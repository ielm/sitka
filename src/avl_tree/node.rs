// This is an attempt at an implementation for an AVL tree:
//
// ```rust
// struct AvlTree<K, V> {
//     height: usize,
//     root: Option<Box<Node<K, V, height>>>
// }
//
// struct Node<K, V, height: usize> {
//     key: K,
//     val: V,
//     parent: Option<(NonNull<Node<K, V, height + 1>>, u16)>
//     left: Option<(NonNull<Node<K, V, height - 1>>, u16)>
//     right: Option<(NonNull<Node<K, V, height - 1>>, u16)>
//     height: usize
// }
// ```
//
// This implementation of an AVL Tree borrows heavily from the rust
// alloc::collections::btree implementation, but contains significant differences.
// In particular, this AVL Tree does not store arrays of keys and values,
// instead preferring that each node contains a single value.
//
// TODO(@ielm)
//   [  ] - Node should be renamed to InternalNode
//   [  ] - Create a LeadNode variant
//   [  ] - Make InternalNode & NodeLeaf private
//   [  ] - Create a public NodeRef

#![allow(dead_code)]
#![allow(clippy::option_map_unit_fn)]

use std::cmp::Ordering;
use std::ptr::NonNull;

/// `OptNode` is a type alias for `Option<NonNull<Node<K, V>>>`.
///
/// It represents an optional reference to a `Node` in the AVL tree, where `None`
/// indicates the absence of a node, and `Some(NonNull<Node<K, V>>)` represents
/// a non-null pointer to a `Node` instance.
///
/// The `NonNull` wrapper ensures that the pointer is always non-null.
///
/// # Type Parameters
///
/// - `K`: The type of the keys in the AVL tree. It must implement the `Ord` trait.
/// - `V`: The type of the values associated with the keys in the AVL tree.
pub type OptNode<K, V> = Option<NonNull<Node<K, V>>>;

/// `Node` represents a node in the AVL tree.
///
/// Each node contains a key of type `K`, a value of type `V`, and references to
/// its parent node, left child, and right child. The node also stores its height,
/// which is used to maintain the balance of the AVL tree.
///
/// # Type Parameters
///
/// - `K`: The type of the key stored in the node. It must implement the `Ord` trait
///   for comparison.
/// - `V`: The type of the value associated with the key in the node.
///
/// # Fields
///
/// - `key`: The key stored in the node, of type `K`.
/// - `value`: The value associated with the key, of type `V`.
/// - `parent`: An optional reference to the parent node, represented by `OptNode<K, V>`.
/// - `left`: An optional reference to the left child node, represented by `OptNode<K, V>`.
/// - `right`: An optional reference to the right child node, represented by `OptNode<K, V>`.
/// - `height`: The height of the node, used for maintaining the balance of the AVL tree.
///   It is of type `i32`.
#[derive(Debug)]
pub struct Node<K: Ord, V> {
    key: K,
    value: V,
    parent: OptNode<K, V>,
    left: OptNode<K, V>,
    right: OptNode<K, V>,
    height: isize,
}

impl<K: Ord, V> Node<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Node {
            key,
            value,
            parent: None,
            left: None,
            right: None,
            height: 1,
        }
    }

    #[inline]
    pub fn get_value(node: OptNode<K, V>) -> Option<V> {
        if node.is_none() {
            None
        } else {
            Some(
                node.as_ref()
                    .map(|n| unsafe { std::ptr::read(&(*n.as_ptr()).value) })
                    .unwrap(),
            )
        }
    }

    #[inline]
    pub fn get_mut_value(node: OptNode<K, V>) -> Option<&'static mut V> {
        unsafe { node.map(|n| &mut (*n.as_ptr()).value) }
    }

    #[inline]
    pub fn set_value(node: OptNode<K, V>, value: V) {
        node.as_ref()
            .map(|n| unsafe { (*n.as_ptr()).value = value });
    }

    #[inline]
    pub fn get_key(node: OptNode<K, V>) -> Option<K> {
        if node.is_none() {
            None
        } else {
            Some(
                node.as_ref()
                    .map(|n| unsafe { std::ptr::read(&(*n.as_ptr()).key) })
                    .unwrap(),
            )
        }
    }

    #[inline]
    pub fn get_parent(node: OptNode<K, V>) -> OptNode<K, V> {
        node.as_ref().and_then(|n| unsafe { (*n.as_ptr()).parent })
    }

    #[inline]
    pub fn set_parent(child: OptNode<K, V>, parent: OptNode<K, V>) {
        if parent.is_none() {
            Node::set_parent(child, None);
        } else {
            let ordering = Node::order(parent, child);

            if let Some(o) = ordering {
                match o {
                    Ordering::Less => Node::set_right(parent, child),
                    Ordering::Greater => Node::set_left(parent, child),
                    Ordering::Equal => {
                        // Duplicate keys are not allowed.
                        // TODO(@ielm) - handle error here?
                    }
                }
            }
        }
    }

    #[inline]
    pub fn get_left(node: OptNode<K, V>) -> OptNode<K, V> {
        node.as_ref().and_then(|n| unsafe { (*n.as_ptr()).left })
    }

    #[inline]
    pub fn set_left(node: OptNode<K, V>, left: OptNode<K, V>) {
        node.as_ref().map(|n| unsafe { (*n.as_ptr()).left = left });
        left.as_ref()
            .map(|l| unsafe { (*l.as_ptr()).parent = node });
    }

    #[inline]
    pub fn get_right(node: OptNode<K, V>) -> OptNode<K, V> {
        node.as_ref().and_then(|n| unsafe { (*n.as_ptr()).right })
    }

    #[inline]
    pub fn set_right(node: OptNode<K, V>, right: OptNode<K, V>) {
        node.as_ref()
            .map(|n| unsafe { (*n.as_ptr()).right = right });
        right
            .as_ref()
            .map(|r| unsafe { (*r.as_ptr()).parent = node });
    }

    #[inline]
    pub fn boxed(node: OptNode<K, V>) -> Option<Box<Node<K, V>>> {
        node.map(|n| unsafe { Box::from_raw(n.as_ptr()) })
    }

    #[inline]
    pub fn order(n1: OptNode<K, V>, n2: OptNode<K, V>) -> Option<Ordering> {
        let n1_key = n1.as_ref().map(|n| unsafe { &(n.as_ref()).key });
        let n2_key = n2.as_ref().map(|n| unsafe { &(n.as_ref()).key });
        n1_key.and_then(|n1k| n2_key.map(|n2k| n1k.cmp(n2k)))
    }

    #[inline]
    pub fn compare_key(node: OptNode<K, V>, k: &K) -> Option<Ordering> {
        node.as_ref().map(|n| unsafe { (*n.as_ptr()).key.cmp(k) })
    }

    /// Unlink child FROM parent
    #[inline]
    pub fn unlink(child: OptNode<K, V>, parent: OptNode<K, V>) {
        let ordering = Node::order(parent, child);

        if let Some(o) = ordering {
            match o {
                Ordering::Less => {
                    Node::set_right(parent, None);
                    Node::set_parent(child, None);
                }
                Ordering::Greater => {
                    Node::set_left(parent, None);
                    Node::set_parent(child, None);
                }
                Ordering::Equal => {
                    // Duplicate keys are not allowed
                    // TODO(@ielm) - Handle error here?
                }
            }
        }
    }

    #[inline]
    pub fn get_height(node: OptNode<K, V>) -> isize {
        if node.is_none() {
            0
        } else {
            node.as_ref()
                .map(|n| unsafe { (*n.as_ptr()).height })
                .unwrap()
        }
    }

    #[inline]
    pub fn set_height(node: OptNode<K, V>, height: isize) {
        node.as_ref()
            .map_or_else(|| {}, |n| unsafe { (*n.as_ptr()).height = height })
    }

    #[inline]
    pub fn update_height(node: OptNode<K, V>) {
        let height = std::cmp::max(
            Node::get_height(Node::get_left(node)),
            Node::get_height(Node::get_right(node)),
        ) + 1;

        Node::set_height(node, height);
    }
}
