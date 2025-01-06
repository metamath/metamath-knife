//! A Tree implementation to be used for `Formula`
//!
use core::ops::Index;
use core::ops::IndexMut;

pub(crate) type NodeId = usize;

#[derive(Debug)]
struct TreeNode<TreeItem> {
    item: TreeItem,
    first_child: NodeId,
    next_sibling: NodeId,
}

/// A tree implementation, hopefully efficient for representing formulas
#[derive(Debug)]
pub(crate) struct Tree<TreeItem> {
    nodes: Vec<TreeNode<TreeItem>>,
}

impl<TreeItem> Default for Tree<TreeItem> {
    fn default() -> Self {
        Self { nodes: vec![] }
    }
}

impl<TreeItem> Tree<TreeItem> {
    /// Create a new node with the given item and children (previously added to the tree)
    /// This way of constructing the tree forces to use a bottom-up approach,
    /// where the leafs are added first, followed by the branch nodes.
    /// The root node is added last, and is therefore not at a fixed index.
    pub(crate) fn add_node(&mut self, item: TreeItem, children: &[NodeId]) -> NodeId {
        let mut new_node = TreeNode {
            item,
            first_child: 0,
            next_sibling: 0,
        };
        let mut pointer = &mut new_node.first_child;
        for child_index in children {
            *pointer = *child_index;
            pointer = &mut self.nodes[*child_index - 1].next_sibling;
            assert!(
                *pointer == 0,
                "Children added to a node shall not be chained yet!"
            );
        }
        self.nodes.push(new_node);
        self.nodes.len()
    }

    /// Checked accessor to a tree node
    #[inline]
    fn node(&self, node_id: NodeId) -> &'_ TreeNode<TreeItem> {
        assert!(node_id > 0, "Cannot index null node!");
        assert!(node_id <= self.nodes.len(), "Cannot index outside of tree!");
        &self.nodes[node_id - 1]
    }

    /// Checked mutable accessor to a tree node
    #[inline]
    fn node_mut(&mut self, node_id: NodeId) -> &'_ mut TreeNode<TreeItem> {
        assert!(node_id > 0, "Cannot index null node!");
        assert!(node_id <= self.nodes.len(), "Cannot index outside of tree!");
        &mut self.nodes[node_id - 1]
    }

    /// iterator through the children of the given node
    pub(crate) fn children_iter(&self, node_id: NodeId) -> SiblingIter<'_, TreeItem> {
        SiblingIter {
            tree: self,
            current_id: self.first_child(node_id),
        }
    }

    /// returns the next sibling node id, or `None` if this is the last sibling.
    /// This executes in O(1)
    pub(crate) fn next_sibling(&self, node_id: NodeId) -> Option<NodeId> {
        match self.node(node_id).next_sibling {
            0 => None,
            node_id => Some(node_id),
        }
    }

    /// returns the first child node, if any
    pub(crate) fn first_child(&self, node_id: NodeId) -> Option<NodeId> {
        match self.node(node_id).first_child {
            0 => None,
            node_id => Some(node_id),
        }
    }

    /// returns the child node with the given index among children nodes
    /// Indices starts with 0, so querying index 0 will return the first child node, if any.
    /// This executes in O(n)
    pub(crate) fn nth_child(&self, node_id: NodeId, index: usize) -> Option<NodeId> {
        self.children_iter(node_id).nth(index)
    }

    /// returns whether the given node has children or not
    pub(crate) fn has_children(&self, node_id: NodeId) -> bool {
        self.node(node_id).first_child != 0
    }

    /// Debug only, dumps the internal structure of the tree.
    pub(crate) fn dump<'a, D>(&'a self, display: D)
    where
        D: Fn(&'a TreeItem) -> &'a str,
    {
        for node in &self.nodes {
            println!(
                "  - {:?} fc={}, ns={}",
                display(&node.item),
                node.first_child,
                node.next_sibling
            );
        }
    }

    /// Returns an iterator over all the nodes in the tree (in postorder)
    pub(crate) fn node_iter(&self) -> NodeIter<'_, TreeItem> {
        NodeIter(self.nodes.iter())
    }
}

impl<TreeItem> Index<NodeId> for Tree<TreeItem> {
    type Output = TreeItem;

    fn index(&self, node_id: NodeId) -> &Self::Output {
        &self.node(node_id).item
    }
}

impl<TreeItem> IndexMut<NodeId> for Tree<TreeItem> {
    fn index_mut(&mut self, node_id: NodeId) -> &mut Self::Output {
        &mut self.node_mut(node_id).item
    }
}

// TODO(tirix): remove and avoid cloning trees
impl<TreeItem: Clone> Clone for TreeNode<TreeItem> {
    fn clone(&self) -> Self {
        TreeNode {
            item: self.item.clone(),
            first_child: self.first_child,
            next_sibling: self.next_sibling,
        }
    }
}

// TODO(tirix): remove and avoid cloning trees
impl<TreeItem: Clone> Clone for Tree<TreeItem> {
    fn clone(&self) -> Self {
        Tree {
            nodes: self.nodes.clone(),
        }
    }
}

/// An iterator through sibling nodes
#[derive(Debug)]
pub(crate) struct SiblingIter<'a, TreeItem> {
    tree: &'a Tree<TreeItem>,
    current_id: Option<NodeId>,
}

impl<TreeItem> Iterator for SiblingIter<'_, TreeItem> {
    type Item = NodeId;

    fn next(&mut self) -> Option<Self::Item> {
        let current_id = self.current_id;
        std::mem::replace(&mut self.current_id, self.tree.next_sibling(current_id?))
    }
}

/// An iterator through all nodes
#[derive(Debug)]
pub(crate) struct NodeIter<'a, TreeItem>(std::slice::Iter<'a, TreeNode<TreeItem>>);

impl<'a, TreeItem> Iterator for NodeIter<'a, TreeItem> {
    type Item = &'a TreeItem;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|node| &node.item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<TreeItem> ExactSizeIterator for NodeIter<'_, TreeItem> {
    fn len(&self) -> usize {
        self.0.len()
    }
}
