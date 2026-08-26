# sitka

Nonlinear data structures for Rust.

## Status

**Pre-release, v0.0.1** — under active development. APIs are experimental and
may change without notice. The tree internals are pointer-based and use
`unsafe`; a safety audit is on the roadmap but has not happened yet, so treat
this crate as a work in progress rather than production-ready.

## What's included

- **AVL tree** (`sitka::avl_tree::tree::AvlTree`) — a self-balancing binary
  search tree with insert, lookup, removal, min/max popping, and in-order
  iteration. The implementation borrows ideas from the standard library's
  B-tree design, but stores a single key-value pair per node.

## Example

```rust
use sitka::avl_tree::tree::AvlTree;

let mut tree = AvlTree::new();
tree.insert(2, "two");
tree.insert(1, "one");
tree.insert(3, "three");

assert_eq!(tree.get(&2), Some("two"));
assert!(tree.contains(&1));
assert_eq!(tree.len(), 3);

assert_eq!(tree.remove(&1), Some("one"));
assert!(!tree.contains(&1));
```

## Roadmap

- More tree structures (red-black, B-tree variants, tries)
- Richer iterator support (range queries, entry API)
- Safety audit of the unsafe pointer internals (including non-`Copy` key/value
  handling in the by-value accessors)

## License

MIT
