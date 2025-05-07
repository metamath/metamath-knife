//! The database outline.
//!
//! This is an analysis pass and should not be invoked directly; it is intended
//! to be instantiated through `Database`.  It is not considered a stable API,
//! although a stable wrapper may be added in `Database`.

use crate::as_str;
use crate::parser::HeadingLevel;
use crate::segment::Comparer;
use crate::segment::SegmentRef;
use crate::segment_set::SegmentSet;
use crate::statement::HeadingDef;
use crate::statement::SegmentId;
use crate::statement::Span;
use crate::statement::StatementAddress;
use crate::statement::StatementIndex;
use crate::statement::Token;
use crate::tree::NodeId;
use crate::tree::Tree;
use crate::Database;
use crate::StatementRef;
use crate::StatementType;
use std::fmt::Display;
use std::fmt::Formatter;
use std::sync::Arc;

#[derive(Debug, Clone)]
/// A node of a database outline
struct OutlineNode {
    /// Name of this outline
    name: Token,
    /// Level of this outline
    level: HeadingLevel,
    /// Statement address
    stmt_address: StatementAddress,
    /// A reference to the parent node
    parent: NodeId,
}

impl OutlineNode {
    /// Build the root node for a database
    fn root_node(segment1: SegmentRef<'_>) -> Self {
        OutlineNode {
            name: (*b"Database").into(),
            level: HeadingLevel::Database,
            stmt_address: StatementAddress::new(segment1.id, 0),
            parent: 0,
        }
    }

    /// Build an outline node, with a generic statement address,
    /// which is specific to a segment
    const fn new(
        name: Token,
        level: HeadingLevel,
        segment_id: SegmentId,
        index: StatementIndex,
    ) -> Self {
        OutlineNode {
            name,
            level,
            stmt_address: StatementAddress::new(segment_id, index),
            parent: 0,
        }
    }

    /// Add this node to the given tree, with the given children, and set their parent id
    fn add_to_tree(self, tree: &mut Tree<OutlineNode>, children: &[NodeId]) -> NodeId {
        let node_id = tree.add_node(self, children);
        for child_node_id in children {
            tree[*child_node_id].parent = node_id;
        }
        node_id
    }

    /// Returns the name of that node, i.e. the heading title or statement label
    fn get_name<'a>(&'a self, database: &'a Database) -> &'a str {
        let sref = database.parse_result().statement(self.stmt_address);
        match self.level {
            HeadingLevel::Statement => as_str(sref.label()),
            HeadingLevel::Database => "Database",
            _ => as_str(&self.name),
        }
    }
}

/// A reference to an outline node
#[derive(Debug, Clone, Copy)]
#[allow(missing_docs)]
pub enum OutlineNodeRef<'a> {
    Chapter {
        database: &'a Database,
        node_id: NodeId,
    },
    Statement {
        database: &'a Database,
        sref: StatementRef<'a>,
    },
}

impl<'a> OutlineNodeRef<'a> {
    /// Creates an `OutlineNodeRef` for the root of this database
    #[allow(clippy::missing_const_for_fn)] // clippy#14091
    #[must_use]
    pub fn root_node(database: &'a Database) -> Self {
        OutlineNodeRef::Chapter {
            database,
            node_id: database.outline_result().root,
        }
    }

    /// Creates an `OutlineNodeRef` for the given statement
    #[must_use]
    pub const fn statement_node(database: &'a Database, sref: StatementRef<'a>) -> Self {
        OutlineNodeRef::Statement { database, sref }
    }

    /// Returns this node's parent, or `None` if this is the root node
    #[inline]
    #[must_use]
    pub fn parent(self) -> Option<OutlineNodeRef<'a>> {
        match self {
            OutlineNodeRef::Chapter { database, node_id } => {
                let node = &database.outline_result().tree[node_id];
                if node.level == HeadingLevel::Database {
                    None
                } else {
                    Some(OutlineNodeRef::Chapter {
                        database,
                        node_id: node.parent,
                    })
                }
            }
            OutlineNodeRef::Statement { database, sref } => {
                let outline = database.outline_result();
                Some(OutlineNodeRef::Chapter {
                    database,
                    node_id: outline.statement_node_inside(sref.address(), outline.root, database),
                })
            }
        }
    }

    /// returns the first child node of this node, if any
    #[must_use]
    pub fn first_child(self) -> Option<OutlineNodeRef<'a>> {
        match self {
            OutlineNodeRef::Chapter { database, node_id } => {
                let node = &database.outline_result().tree[node_id];
                if let Some(sref) = OutlineNodeRef::next_assertion(database, node.stmt_address) {
                    // return statement following this chapter heading, if any
                    Some(OutlineNodeRef::Statement { database, sref })
                } else {
                    // otherwise, return the first child chapter
                    Some(OutlineNodeRef::Chapter {
                        database,
                        node_id: database.outline_result().tree.first_child(node_id)?,
                    })
                }
            }
            OutlineNodeRef::Statement { .. } => None,
        }
    }

    /// Returns the next statement or chapter, in depth-first traversal order
    #[must_use]
    pub fn next(self) -> Option<OutlineNodeRef<'a>> {
        // First attempt to find a child, since we are depth-first
        self.first_child().or_else(|| self.next_after_children())
    }

    /// Returns the next statement or chapter, in depth-first traversal order
    /// but never diving into this node's children
    fn next_after_children(self) -> Option<OutlineNodeRef<'a>> {
        match self {
            // In a chapter, the next node is the next chapter
            OutlineNodeRef::Chapter { database, node_id } => database
                .outline_result()
                .tree
                .next_sibling(node_id)
                .map_or_else(
                    || self.parent()?.next_after_children(),
                    |node_id| Some(OutlineNodeRef::Chapter { database, node_id }),
                ),
            // In a statement,
            OutlineNodeRef::Statement { database, sref } => {
                let address = sref.address();
                if let Some(sref) = OutlineNodeRef::next_assertion(database, address) {
                    // if there are more statements after this one, return the next one
                    Some(OutlineNodeRef::Statement { database, sref })
                } else {
                    // else, if there are no more statements after this one
                    let outline = database.outline_result();
                    let parent_node_id =
                        outline.statement_node_inside(address, outline.root, database);
                    match outline.tree.first_child(parent_node_id) {
                        // Return the first chapter child if any
                        Some(node_id) => Some(OutlineNodeRef::Chapter { database, node_id }),
                        // Else return the parent's next sibling
                        None => self.parent()?.next_after_children(),
                    }
                }
            }
        }
    }

    /// returns the next assertion in the database, until a heading comment or the end of the database is met
    fn next_assertion(
        database: &'a Database,
        mut stmt_address: StatementAddress,
    ) -> Option<StatementRef<'a>> {
        loop {
            stmt_address = StatementAddress::new(stmt_address.segment_id, stmt_address.index + 1);
            let sref = database.parse_result().statement(stmt_address);
            match sref.statement_type() {
                StatementType::Provable | StatementType::Axiom => break,
                StatementType::HeadingComment(_) | StatementType::Eof => return None,
                _ => {}
            }
        }
        Some(database.parse_result().statement(stmt_address))
    }
}

/// An iterator over the children of an outline node, both statements and other chapters.
/// See [`OutlineNodeRef::children_iter`]
#[derive(Debug)]
enum OutlineChildrenIterInner<'a> {
    Statement {
        iter: ChapterStatementIter<'a>,
        node_id: NodeId,
    },
    Children {
        database: &'a Database,
        iter: crate::tree::SiblingIter<'a, OutlineNode>,
    },
    Done,
}

/// An iterator over the children of an outline node, both statements and other chapters.
/// See [`OutlineNodeRef::children_iter`]
#[derive(Debug)]
#[must_use]
pub struct OutlineChildrenIter<'a>(OutlineChildrenIterInner<'a>);

impl<'a> Iterator for OutlineChildrenIter<'a> {
    type Item = OutlineNodeRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0 {
                // We first iterate over the statements within the chapter,
                OutlineChildrenIterInner::Statement {
                    ref mut iter,
                    node_id,
                } => match iter.next() {
                    Some(node) => return Some(node),
                    None => {
                        self.0 = OutlineChildrenIterInner::Children {
                            database: iter.database,
                            iter: iter.database.outline_result().tree.children_iter(node_id),
                        }
                    }
                },
                // then over the sub-chapters
                OutlineChildrenIterInner::Children {
                    database,
                    ref mut iter,
                } => {
                    return Some(OutlineNodeRef::Chapter {
                        database,
                        node_id: iter.next()?,
                    })
                }
                OutlineChildrenIterInner::Done => return None,
            }
        }
    }
}

impl<'a> OutlineNodeRef<'a> {
    /// Iterator through the children outline nodes
    pub fn children_iter(&self) -> OutlineChildrenIter<'a> {
        OutlineChildrenIter(match *self {
            OutlineNodeRef::Chapter { database, node_id } => OutlineChildrenIterInner::Statement {
                iter: ChapterStatementIter::new(database, node_id),
                node_id,
            },
            OutlineNodeRef::Statement { .. } => OutlineChildrenIterInner::Done,
        })
    }

    /// Returns this node's parent, its parent's parent, etc. until the root (database) node.
    pub fn ancestors_iter(&self) -> OutlineAncestorIter<'a> {
        OutlineAncestorIter::from(*self)
    }

    /// Returns the name of that node, i.e. the heading title or statement label
    #[inline]
    #[must_use]
    pub fn get_name(&self) -> &str {
        match self {
            OutlineNodeRef::Chapter { database, node_id } => {
                database.outline_result().tree[*node_id].get_name(database)
            }
            OutlineNodeRef::Statement { sref, .. } => as_str(sref.label()),
        }
    }

    /// Returns the level of that node
    #[inline]
    #[must_use]
    pub fn get_level(&self) -> HeadingLevel {
        match self {
            OutlineNodeRef::Chapter { database, node_id } => {
                database.outline_result().tree[*node_id].level
            }
            OutlineNodeRef::Statement { .. } => HeadingLevel::Statement,
        }
    }

    /// Returns the name of that node, i.e. the heading title or statement label
    #[inline]
    #[must_use]
    pub const fn get_ref(&self) -> usize {
        match self {
            OutlineNodeRef::Chapter { node_id, .. } => *node_id,
            OutlineNodeRef::Statement { .. } => panic!("No ref is provided for Statement nodes."),
        }
    }

    /// Returns the statement for this node
    #[must_use]
    pub fn get_statement(&self) -> StatementRef<'_> {
        match self {
            OutlineNodeRef::Chapter { database, node_id } => {
                let address = database.outline_result().tree[*node_id].stmt_address;
                database.statement_by_address(address)
            }
            OutlineNodeRef::Statement { sref, .. } => *sref,
        }
    }

    /// Returns the span for this node.
    /// For statements, this is the statement span.
    /// For chapters, this covers the whole chaper, until the next one.
    #[must_use]
    pub fn get_span(&self) -> Span {
        match self {
            OutlineNodeRef::Chapter { database, .. } => {
                let stmt = self.get_statement();
                let start = stmt.span().start;
                let end = if let Some(next_stmt) = self.next_after_children() {
                    next_stmt.get_statement().span().start - 1
                } else {
                    let segment_span = database.parse_result().source_info(stmt.segment.id).span;
                    segment_span.end - segment_span.start
                };
                Span { start, end }
            }
            OutlineNodeRef::Statement { sref, .. } => sref.span_full(),
        }
    }

    // TODO(tirix) Getters for next and previous references in the database order

    // TODO(tirix)
    // /// Returns the chapter number
    // pub fn get_chapter_numbers(&self) -> impl Iterator<Item = usize> + '_ {
    //     vec![0].into_iter()
    // }

    // TODO(tirix): it would be nice to also have a method returning the heading chapter comment,
    // if there is any.
}

impl Display for OutlineNodeRef<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        // TODO(tirix) Complete with chapter numbers
        // fmt.write_str(&self.get_chapter_numbers().map(|i| { i.to_string() }).collect::<Vec<String>>().join("."))?;
        // fmt.write_str(" ")?;
        fmt.write_str(self.get_name())
    }
}

/// An iterator over the parents of a node. See [`OutlineNodeRef::ancestors_iter`]
#[derive(Debug)]
#[must_use]
pub struct OutlineAncestorIter<'a>(Option<OutlineNodeRef<'a>>);

impl<'a> From<OutlineNodeRef<'a>> for OutlineAncestorIter<'a> {
    fn from(node: OutlineNodeRef<'a>) -> Self {
        OutlineAncestorIter(Some(node))
    }
}

impl<'a> Iterator for OutlineAncestorIter<'a> {
    type Item = OutlineNodeRef<'a>;

    fn next(&mut self) -> Option<OutlineNodeRef<'a>> {
        let node = self.0;
        self.0 = node.and_then(OutlineNodeRef::parent);
        node
    }
}

/// This iterator will yield an outline node for each statement encountered, skipping any non-statement (comments, etc.),
/// and stopping with the next chapter comment or at the end of the segment
#[derive(Debug)]
pub struct ChapterStatementIter<'a> {
    database: &'a Database,
    stmt_address: StatementAddress,
}

impl<'a> ChapterStatementIter<'a> {
    fn new(database: &'a Database, node_id: NodeId) -> Self {
        Self {
            database,
            stmt_address: database.outline_result().tree[node_id].stmt_address,
        }
    }
}

impl<'a> Iterator for ChapterStatementIter<'a> {
    type Item = OutlineNodeRef<'a>;

    fn next(&mut self) -> Option<OutlineNodeRef<'a>> {
        let sref = OutlineNodeRef::next_assertion(self.database, self.stmt_address)?;
        self.stmt_address = sref.address();
        Some(OutlineNodeRef::Statement {
            database: self.database,
            sref,
        })
    }
}

/// A structure holding the general outline of the database,
/// with chapters, sections, subsections, etc., down to the statement level.
#[derive(Debug, Clone)]
pub struct Outline {
    tree: Arc<Tree<OutlineNode>>,
    root: NodeId,
}

impl Database {
    /// Returns the outline node with the given internal reference
    #[must_use]
    pub const fn get_outline_node_by_ref(&self, chapter_ref: NodeId) -> OutlineNodeRef<'_> {
        OutlineNodeRef::Chapter {
            database: self,
            node_id: chapter_ref,
        }
    }
}

impl Outline {
    /// Returns the smallest outline node containing the given statement, starting from the given node
    fn statement_node_inside(
        &self,
        stmt_address: StatementAddress,
        node_id: NodeId,
        database: &Database,
    ) -> NodeId {
        let order = &database.parse_result().order;
        let node = &self.tree[node_id];
        if stmt_address == node.stmt_address || !self.tree.has_children(node_id) {
            node_id
        } else {
            let mut last_node_id = node_id;
            for this_node_id in self.tree.children_iter(node_id) {
                let node = &self.tree[this_node_id];
                if order.lt(&stmt_address, &node.stmt_address) {
                    if last_node_id == node_id {
                        return node_id;
                    }
                    return self.statement_node_inside(stmt_address, last_node_id, database);
                }
                last_node_id = this_node_id;
            }
            self.statement_node_inside(stmt_address, last_node_id, database)
        }
    }

    /// Dump the content of this outline to the standard output
    pub(crate) fn dump(&self, database: &Database) {
        let root_node_id = self.root;
        self.print_outline_node(root_node_id, 0, database);
    }

    /// Dump the content of the given node to the standard output
    fn print_outline_node(&self, node_id: NodeId, indent: usize, database: &Database) {
        let node = &self.tree[node_id];
        println!(
            "{:indent$} {:?} {:?}",
            "",
            node.level,
            node.get_name(database),
            indent = indent,
        );
        for child_node_id in self.tree.children_iter(node_id) {
            self.print_outline_node(child_node_id, indent + 1, database);
        }
    }
}

/// Builds the overall outline from the different segments
impl SegmentSet {
    pub(crate) fn build_outline(&self) -> Outline {
        let mut tree: Tree<OutlineNode> = Tree::default();
        let segments = self.segments(..);
        let mut current_node =
            OutlineNode::root_node(segments.clone().next().expect("Parse returned no segment!"));
        let mut node_stack = vec![];
        let mut sibling_stack = vec![];
        for vsr in segments {
            for &HeadingDef {
                ref name,
                index,
                level,
            } in &vsr.segment.outline
            {
                let new_node = OutlineNode::new(name.clone(), level, vsr.id, index);
                while level <= current_node.level {
                    // Next chapter is a higher level, pop from the stack onto the tree
                    let (lowest_node, sibling_idx) = node_stack
                        .pop()
                        .expect("impossible because root node has lowest level");
                    let lowest_node_id = std::mem::replace(&mut current_node, lowest_node)
                        .add_to_tree(&mut tree, &sibling_stack[sibling_idx..]);
                    sibling_stack.truncate(sibling_idx);
                    sibling_stack.push(lowest_node_id);
                }
                // Next chapter is at a lower level, push onto the stack
                node_stack.push((
                    std::mem::replace(&mut current_node, new_node),
                    sibling_stack.len(),
                ));
            }
        }

        // Finally, pop everything from the stack onto the tree
        let mut last_sibling_idx = 0;
        for (node, sibling_idx) in node_stack.into_iter().rev() {
            let node_id = std::mem::replace(&mut current_node, node)
                .add_to_tree(&mut tree, &sibling_stack[sibling_idx..]);
            sibling_stack.truncate(sibling_idx);
            sibling_stack.push(node_id);
            last_sibling_idx = sibling_idx;
        }
        let root = current_node.add_to_tree(
            &mut tree,
            if sibling_stack.len() > last_sibling_idx {
                &sibling_stack[..=last_sibling_idx]
            } else {
                &[]
            },
        );
        tree[root].parent = root;

        Outline {
            tree: Arc::new(tree),
            root,
        }
    }
}
