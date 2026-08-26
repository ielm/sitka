//! # sitka
//!
//! A collection of nonlinear data structures for Rust.
//!
//! Sitka currently ships a single structure: an [`AvlTree`](avl_tree::tree::AvlTree),
//! a self-balancing binary search tree backed by raw pointers, with a design
//! borrowed in part from the standard library's B-tree implementation.
//!
//! This crate is pre-release and experimental; APIs may change (or vanish)
//! without notice, and the unsafe internals have not yet been audited.
//!
//! ## Example
//!
//! ```
//! use sitka::avl_tree::tree::AvlTree;
//!
//! let mut tree = AvlTree::new();
//! tree.insert(2, "two");
//! tree.insert(1, "one");
//! tree.insert(3, "three");
//!
//! assert_eq!(tree.get(&2), Some("two"));
//! assert!(tree.contains(&1));
//! assert_eq!(tree.len(), 3);
//! ```

pub mod avl_tree;
