//! A Tree implementation to be used for `Formula`
//!
use core::ops::Index;

pub type NodeId = usize;

struct TreeNode<TreeItem> {
    item: TreeItem,
    first_child: NodeId,
    next_sibling: NodeId,
}

/// A tree implementation, hopefully efficient for representing formulas
#[derive(Default)]
pub struct Tree<TreeItem> {
    nodes: Vec<TreeNode<TreeItem>>,
}

impl<TreeItem: Copy> Tree<TreeItem> {
    /// Create a new node with the given item and children (previously added to the tree)
    /// This way of constructing the tree forces to use a bottom-up approach, 
    /// where the leafs are added first, followed by the branch nodes.
    /// The root node is added last, and is therefore not at a fixed index.
    pub fn add_node(&mut self, item: TreeItem, children: &[NodeId]) -> NodeId {
        let mut new_node = TreeNode {
            item,
            first_child: 0,
            next_sibling: 0,
        };
        let mut pointer = &mut new_node.first_child;
        for child_index in children {
            *pointer = *child_index;
            pointer = &mut self.nodes[*child_index-1].next_sibling;
            assert!(*pointer == 0, "Children added to a node shall not be chained yet!");
        }
        self.nodes.push(new_node);
        self.nodes.len()
    }

    /// iterator through the children of the given node
    pub fn children_iter(&self, node_id: NodeId) -> SiblingIter<TreeItem> {
        assert!(node_id > 0, "Cannot iterate null node!");
        assert!(node_id <= self.nodes.len(), "Cannot iterate outside of tree!");
        let node = &self.nodes[node_id-1];
        SiblingIter {
            tree: self,
            current_id: node.first_child,
        }
    }

    /// iterator through the children of the given node
    pub fn nth_child(&self, node_id: NodeId, index: usize) -> Option<NodeId> {
        let mut iter = self.children_iter(node_id);
        let mut nth_node_id = node_id;
        for _ in 0..index {
            nth_node_id = iter.next()?;
        }
        Some(nth_node_id)
    }
    
    /// returns whether the given node has children or not
    pub fn has_children(&self, node_id: NodeId) -> bool {
        self.nodes[node_id-1].first_child != 0
    }

    /// Debug only, dumps the internal structure of the tree.
    pub fn dump<'a, D>(&'a self, display: D) where D: Fn(&'a TreeItem) -> &str {
        for node in &self.nodes {
            println!("  - {:?} fc={}, ns={}", display(&node.item), node.first_child, node.next_sibling);
        }
    }
}

impl<TreeItem> Index<NodeId> for Tree<TreeItem> {
    type Output = TreeItem;

    fn index(&self, node_id: NodeId) -> &Self::Output {
        &self.nodes[node_id-1].item
    }
}

// TODO: remove and avoid cloning trees
impl <TreeItem: Clone> Clone for TreeNode<TreeItem> {
    fn clone(&self) -> Self { 
        TreeNode { item: self.item.clone(), first_child: self.first_child, next_sibling: self.next_sibling }
    }
}

// TODO: remove and avoid cloning trees
impl<TreeItem: Clone> Clone for Tree<TreeItem> {
    fn clone(&self) -> Self {
        Tree { nodes: self.nodes.clone() }
    }
}

/// An iterator through sibling nodes
pub struct SiblingIter<'a, TreeItem> {
    tree: &'a Tree<TreeItem>,
    current_id: NodeId,
}

impl<TreeItem> Iterator for SiblingIter<'_, TreeItem> {
    type Item = NodeId;

    fn next(&mut self) -> Option<Self::Item> {
        match self.current_id {
            0 => None, // end of the iteration
            _ => {
                let current_id = self.current_id;
                self.current_id = self.tree.nodes[current_id-1].next_sibling;
                Some(current_id)
            },
        }
    }
}