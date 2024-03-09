use super::node::{Node, OptNode};
use std::marker::PhantomData;

/// An AVL tree is a self-balancing binary search tree that maintains the
/// balance factor of each node between -1 and +1.
///
/// The `AvlTree` struct represents an AVL tree with keys of type `K` and
/// values of type `V`. The keys must implement the `Ord` trait for comparison.
///
/// The tree automatically rebalances itself after insertions and deletions to
/// ensure logarithmic time complexity for search, insertion, and deletion
/// operations.
///
/// # Type Parameters
///
/// - `K`: The type of the keys in the AVL tree. It must implement the `Ord` trait.
/// - `V`: The type of the values associated with the keys in the AVL tree.
///
/// # Fields
///
/// - `root`: The root node of the AVL tree, wrapped in an `OptNode` type alias.
/// - `len`: The number of key-value pairs stored in the AVL tree.
/// - `_marker`: A `PhantomData` marker used to express ownership and lifetime
///    relationships between the `AvlTree` and the `Node` instances.
pub struct AvlTree<K: Ord, V> {
    root: OptNode<K, V>,
    len: usize,
    _marker: PhantomData<Box<Node<K, V>>>,
}

