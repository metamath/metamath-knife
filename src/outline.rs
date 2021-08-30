//! The database outline.
//!
//! This is an analysis pass and should not be invoked directly; it is intended
//! to be instantiated through `Database`.  It is not considered a stable API,
//! although a stable wrapper may be added in `Database`.

use crate::parser::as_str;
use crate::parser::copy_token;
use crate::parser::Token;
use crate::parser::HeadingLevel;
use crate::parser::HeadingDef;
use crate::parser::SegmentId;
use crate::parser::SegmentRef;
use crate::parser::StatementAddress;
use crate::segment_set::SegmentSet;
use std::sync::Arc;

#[derive(Debug,Default,Clone)]
/// A node of a database outline
pub struct OutlineNode {
    /// Name of this outline
    pub name: Token,
    /// Level of this outline
    pub level: HeadingLevel,
    /// Statement address
    pub stmt_address: StatementAddress,
    /// A list of children subsections
    pub children: Vec<Arc<OutlineNode>>,
}

impl OutlineNode {
    /// Build the root node for a database
    fn root_node(segments: &Vec<SegmentRef>) -> Self {
        OutlineNode {
            name: copy_token("Database".as_bytes()),
            level: HeadingLevel::Database,
            stmt_address: StatementAddress::new(segments[0].id, 0),
            children: vec![],
        }
    }

    /// Build an outline node, with a generic statement address, from a HeadingDef, which is specific to a segment
    fn from_heading_def(heading: &HeadingDef, segment_id: SegmentId) -> Self {
        OutlineNode {
            name: heading.name.clone(),
            level: heading.level,
            stmt_address: StatementAddress::new(segment_id, heading.index),
            children: vec![],
        }
    }

    /// Add a child to this node, or to the correct sub-node
    fn add_child(&mut self, child: Self) {
        assert!(child.level > self.level, "Cannot add subsection of higher level!");
        match self.children.last_mut() {
            None => {
                // this is our first child
                self.children.push(Arc::new(child));
            },
            Some(last_child) => {
                // Append to our last child
                if child.level > last_child.level {
                    Arc::make_mut(last_child).add_child(child);
                } else {
                    self.children.push(Arc::new(child));
                }
            },
        }
    }
    
    /// Returns the name of that node, i.e. the heading title
    pub fn get_name(&self) -> &str {
        as_str(&self.name)
    }
    
    // TODO - it would be nice to also have a method returning the heading chapter comment, if there is any.
}

/// Builds the overall outline from the different segments
pub fn build_outline<'a>(node: &mut OutlineNode, sset: &'a Arc<SegmentSet>) {
    let segments = sset.segments();
    assert!(segments.len() > 0,"Parse returned no segment!");
    *node = OutlineNode::root_node(&segments);

    for vsr in segments.iter() {
        for heading in &vsr.segment.outline {
            let new_node = OutlineNode::from_heading_def(heading, vsr.id);
            node.add_child(new_node);
        }
    }
}