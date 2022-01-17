//! The database outline.
//!
//! This is an analysis pass and should not be invoked directly; it is intended
//! to be instantiated through `Database`.  It is not considered a stable API,
//! although a stable wrapper may be added in `Database`.

use crate::parser::as_str;
use crate::parser::Comparer;
use crate::parser::HeadingDef;
use crate::parser::HeadingLevel;
use crate::parser::SegmentId;
use crate::parser::SegmentRef;
use crate::parser::StatementAddress;
use crate::parser::StatementIndex;
use crate::parser::Token;
use crate::segment_set::SegmentSet;
use crate::tree::NodeId;
use crate::tree::Tree;
use crate::Database;
use std::cmp::Ordering;
use std::fmt::Display;
use std::fmt::Formatter;
use std::sync::Arc;

#[derive(Debug, Default, Clone)]
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
    fn root_node(segments: &[SegmentRef<'_>]) -> Self {
        OutlineNode {
            name: (*b"Database").into(),
            level: HeadingLevel::Database,
            stmt_address: StatementAddress::new(segments[0].id, 0),
            parent: 0,
        }
    }

    /// Build an outline node, with a generic statement address,
    /// which is specific to a segment
    fn new(name: Token, level: HeadingLevel, segment_id: SegmentId, index: StatementIndex) -> Self {
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

#[derive(Debug)]
/// A reference to an outline node
pub struct OutlineNodeRef<'a> {
    database: &'a Database,
    node_id: NodeId,
}

impl OutlineNodeRef<'_> {
    /// Iterator through the children outline nodes
    pub fn children_iter(&self) -> impl Iterator<Item = OutlineNodeRef<'_>> + '_ {
        self.database
            .outline_result()
            .tree
            .children_iter(self.node_id)
            .map(move |node_id| OutlineNodeRef {
                database: self.database,
                node_id,
            })
    }

    /// Returns this node's parent, its parent's parent, etc. until the root (database) node.
    pub fn ancestors_iter(&self) -> impl Iterator<Item = OutlineNodeRef<'_>> + '_ {
        OutlineAncestorIter::from(self)
    }

    /// Returns the name of that node, i.e. the heading title or statement label
    #[inline]
    #[must_use]
    pub fn get_name(&self) -> &str {
        self.database.outline_result().tree[self.node_id].get_name(self.database)
    }

    /// Returns the level of that node
    #[inline]
    #[must_use]
    pub fn get_level(&self) -> HeadingLevel {
        self.database.outline_result().tree[self.node_id].level
    }

    /// Returns the name of that node, i.e. the heading title or statement label
    #[inline]
    #[must_use]
    pub const fn get_ref(&self) -> usize {
        self.node_id
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

struct OutlineAncestorIter<'a> {
    database: &'a Database,
    tree: &'a Tree<OutlineNode>,
    node_id: NodeId,
    initialized: bool,
}

impl<'a> From<&OutlineNodeRef<'a>> for OutlineAncestorIter<'a> {
    fn from(node: &OutlineNodeRef<'a>) -> Self {
        OutlineAncestorIter {
            database: node.database,
            tree: &node.database.outline_result().tree,
            node_id: node.node_id,
            initialized: false,
        }
    }
}

impl<'a> Iterator for OutlineAncestorIter<'a> {
    type Item = OutlineNodeRef<'a>;

    fn next(&mut self) -> Option<OutlineNodeRef<'a>> {
        if !self.initialized {
            self.initialized = true;
            Some(OutlineNodeRef {
                database: self.database,
                node_id: self.node_id,
            })
        } else {
            let parent_node_id = self.tree[self.node_id].parent;
            if parent_node_id == self.node_id {
                None
            } else {
                self.node_id = parent_node_id;
                Some(OutlineNodeRef {
                    database: self.database,
                    node_id: parent_node_id,
                })
            }
        }
    }
}

/// A structure holding the general outline of the database,
/// with chapters, sections, subsections, etc., down to the statement level.
#[derive(Debug, Default, Clone)]
pub struct Outline {
    tree: Arc<Tree<OutlineNode>>,
    root: NodeId,
}

impl Database {
    /// Returns the outline node with the given internal reference
    #[must_use]
    pub const fn get_outline_node_by_ref(&self, chapter_ref: NodeId) -> OutlineNodeRef<'_> {
        OutlineNodeRef {
            database: self,
            node_id: chapter_ref,
        }
    }
}

impl Outline {
    /// Returns the root outline node (at database level)
    pub(crate) const fn root_node<'a>(&self, database: &'a Database) -> OutlineNodeRef<'a> {
        OutlineNodeRef {
            database,
            node_id: self.root,
        }
    }

    /// Returns the deepest outline node containing the given statement
    pub(crate) fn statement_node<'a>(
        &self,
        sref: StatementAddress,
        database: &'a Database,
    ) -> OutlineNodeRef<'a> {
        OutlineNodeRef {
            database,
            node_id: self.statement_node_inside(sref, self.root, database),
        }
    }

    /// Returns the smallest outline node containing the given statement, starting from the given node
    fn statement_node_inside(
        &self,
        stmt_address: StatementAddress,
        node_id: NodeId,
        database: &Database,
    ) -> NodeId {
        let order = &database.parse_result().order;
        let node = &self.tree[node_id];
        let mut pair = (None, None);
        if stmt_address == node.stmt_address {
            node_id
        } else {
            self.tree
                .children_iter(node_id)
                .take_while(|this_node_id| {
                    pair = (pair.1, Some(*this_node_id));
                    let node = &self.tree[*this_node_id];
                    order.cmp(&stmt_address, &node.stmt_address) != Ordering::Less
                })
                .last();
            if let (Some(last_node_id), _) | (None, Some(last_node_id)) = pair {
                if last_node_id != node_id {
                    self.statement_node_inside(stmt_address, last_node_id, database)
                } else {
                    node_id
                }
            } else {
                node_id
            }
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
    pub(crate) fn build_outline(&self, outline: &mut Outline) {
        let mut tree: Tree<OutlineNode> = Tree::default();
        let segments = self.segments();
        assert!(!segments.is_empty(), "Parse returned no segment!");
        let mut node_stack = vec![OutlineNode::root_node(&segments)];
        let mut sibling_stack = vec![vec![]];
        let mut current_siblings = vec![];
        for vsr in &segments {
            for HeadingDef { name, index, level } in &vsr.segment.outline {
                let new_node = OutlineNode::new(name.clone(), *level, vsr.id, *index);
                while level <= &node_stack.last().unwrap().level {
                    // Next chapter is a higher level, pop from the stack onto the tree
                    let lowest_node = node_stack.pop().unwrap();
                    let lowest_node_id = lowest_node.add_to_tree(&mut tree, &current_siblings);
                    current_siblings = sibling_stack.pop().unwrap();
                    current_siblings.push(lowest_node_id);
                }
                // Next chapter is at a lower level, push onto the stack
                sibling_stack.push(current_siblings);
                node_stack.push(new_node);
                current_siblings = vec![];
            }
        }
        // Finally, pop everything from the stack onto the tree
        for (node, siblings) in node_stack.into_iter().zip(sibling_stack.into_iter()).rev() {
            outline.root = node.add_to_tree(&mut tree, &current_siblings);
            current_siblings = siblings;
            current_siblings.push(outline.root);
        }
        tree[outline.root].parent = outline.root;
        outline.tree = Arc::new(tree);
    }
}
