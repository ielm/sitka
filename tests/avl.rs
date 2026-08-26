//! Integration tests for the public `AvlTree` API.
//!
//! Keys and values are deliberately restricted to `Copy` types: several
//! accessors (`get`, `pop_min`, `pop_max`) return values by bitwise copy of
//! the stored data, which is only sound for `Copy` types in the current
//! pre-release implementation.

use sitka::avl_tree::tree::AvlTree;

/// Simple deterministic pseudorandom sequence (LCG), no dev-dependencies.
fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state
}

#[test]
fn new_tree_is_empty() {
    let tree: AvlTree<i32, i32> = AvlTree::new();
    assert!(tree.is_empty());
    assert_eq!(tree.len(), 0);
    assert!(!tree.contains(&1));
    assert_eq!(tree.get(&1), None);
}

#[test]
fn insert_and_get() {
    let mut tree = AvlTree::new();
    tree.insert(2, 20);
    tree.insert(1, 10);
    tree.insert(3, 30);

    assert_eq!(tree.get(&1), Some(10));
    assert_eq!(tree.get(&2), Some(20));
    assert_eq!(tree.get(&3), Some(30));
    assert_eq!(tree.get(&4), None);
    assert_eq!(tree.len(), 3);
    assert!(!tree.is_empty());
}

#[test]
fn insert_existing_key_updates_value() {
    let mut tree = AvlTree::new();
    tree.insert(1, 10);
    tree.insert(1, 99);
    assert_eq!(tree.get(&1), Some(99));
    assert_eq!(tree.len(), 1);
}

#[test]
fn contains_reports_membership() {
    let mut tree = AvlTree::new();
    for i in 0..20 {
        tree.insert(i, i);
    }
    for i in 0..20 {
        assert!(tree.contains(&i));
    }
    assert!(!tree.contains(&20));
    assert!(!tree.contains(&-1));
}

#[test]
fn ascending_inserts_force_rebalances() {
    // Sequential inserts degenerate to a linked list without rotations.
    let mut tree = AvlTree::new();
    for i in 0..100 {
        tree.insert(i, i * 2);
        assert!(tree.is_balanced(), "unbalanced after inserting {i}");
    }
    assert_eq!(tree.len(), 100);
    for i in 0..100 {
        assert_eq!(tree.get(&i), Some(i * 2), "wrong value for key {i}");
    }
}

#[test]
fn descending_inserts_force_rebalances() {
    let mut tree = AvlTree::new();
    for i in (0..100).rev() {
        tree.insert(i, i * 3);
        assert!(tree.is_balanced(), "unbalanced after inserting {i}");
    }
    assert_eq!(tree.len(), 100);
    for i in 0..100 {
        assert_eq!(tree.get(&i), Some(i * 3), "wrong value for key {i}");
    }
}

#[test]
fn insertion_order_independence() {
    let ascending: Vec<i64> = (0..80).collect();
    let descending: Vec<i64> = (0..80).rev().collect();
    let mut shuffled: Vec<i64> = Vec::new();
    // Deterministic shuffle of 0..80.
    let mut seed = 0xC0FFEE_u64;
    let mut pool = ascending.clone();
    while !pool.is_empty() {
        let idx = (lcg(&mut seed) as usize) % pool.len();
        shuffled.push(pool.swap_remove(idx));
    }

    for order in [&ascending, &descending, &shuffled] {
        let mut tree = AvlTree::new();
        for &k in order {
            tree.insert(k, k + 1000);
        }
        assert_eq!(tree.len(), 80);
        assert!(tree.is_balanced());
        for k in 0..80 {
            assert_eq!(tree.get(&k), Some(k + 1000));
            assert!(tree.contains(&k));
        }
        // In-order iteration must be sorted regardless of insertion order.
        let keys: Vec<i64> = tree.iter().map(|(k, _)| *k).collect();
        assert_eq!(keys, ascending);
    }
}

#[test]
fn remove_leaf_and_missing() {
    let mut tree = AvlTree::new();
    tree.insert(2, 20);
    tree.insert(1, 10);
    tree.insert(3, 30);

    assert_eq!(tree.remove(&1), Some(10));
    assert!(!tree.contains(&1));
    assert_eq!(tree.len(), 2);

    // Removing a missing key is a no-op.
    assert_eq!(tree.remove(&42), None);
    assert_eq!(tree.len(), 2);

    assert_eq!(tree.remove(&2), Some(20));
    assert_eq!(tree.remove(&3), Some(30));
    assert!(tree.is_empty());
    assert_eq!(tree.remove(&3), None);
}

#[test]
fn remove_every_key_from_random_tree() {
    let mut seed = 42_u64;
    let mut keys: Vec<u64> = (0..90).map(|_| lcg(&mut seed) >> 40).collect();
    keys.sort();
    keys.dedup();

    let mut tree = AvlTree::new();
    for &k in &keys {
        tree.insert(k, k);
    }
    assert!(tree.is_balanced());

    // Tear the tree down in pseudorandom order, checking integrity throughout.
    let mut remaining = keys.clone();
    while !remaining.is_empty() {
        let idx = (lcg(&mut seed) as usize) % remaining.len();
        let victim = remaining.swap_remove(idx);
        assert_eq!(tree.remove(&victim), Some(victim));
        assert!(!tree.contains(&victim));
        for &k in &remaining {
            assert!(tree.contains(&k), "key {k} lost after removing {victim}");
        }
        assert!(tree.is_balanced(), "unbalanced after removing {victim}");
        assert_eq!(tree.len() as usize, remaining.len());
    }
    assert!(tree.is_empty());
}

#[test]
fn pop_min_and_pop_max() {
    let mut tree = AvlTree::new();
    for k in [5, 1, 9, 3, 7, 2, 8] {
        tree.insert(k, k * 10);
    }
    assert_eq!(tree.pop_min(), Some((1, 10)));
    assert_eq!(tree.pop_max(), Some((9, 90)));
    assert_eq!(tree.pop_min(), Some((2, 20)));
    assert_eq!(tree.pop_max(), Some((8, 80)));
    assert_eq!(tree.len(), 3);
    assert!(tree.is_balanced());

    let mut empty: AvlTree<i32, i32> = AvlTree::new();
    assert_eq!(empty.pop_min(), None);
    assert_eq!(empty.pop_max(), None);
}

#[test]
fn iter_is_in_order() {
    let mut tree = AvlTree::new();
    for k in [5, 3, 8, 1, 4, 7, 9, 2, 6, 0] {
        tree.insert(k, k * 2);
    }
    let pairs: Vec<(i32, i32)> = tree.iter().map(|(k, v)| (*k, *v)).collect();
    let expected: Vec<(i32, i32)> = (0..10).map(|k| (k, k * 2)).collect();
    assert_eq!(pairs, expected);
}

#[test]
fn clear_empties_the_tree() {
    let mut tree = AvlTree::new();
    for i in 0..50 {
        tree.insert(i, i);
    }
    tree.clear();
    assert!(tree.is_empty());
    assert_eq!(tree.len(), 0);
    assert_eq!(tree.get(&25), None);
    // The tree remains usable after clearing.
    tree.insert(1, 1);
    assert_eq!(tree.get(&1), Some(1));
}

#[test]
fn from_iterator_and_into_iterator() {
    let tree: AvlTree<i32, i32> = (0..60).map(|k| (k, k + 1)).collect();
    assert_eq!(tree.len(), 60);
    assert!(tree.is_balanced());

    let pairs: Vec<(i32, i32)> = tree.into_iter().collect();
    let expected: Vec<(i32, i32)> = (0..60).map(|k| (k, k + 1)).collect();
    assert_eq!(pairs, expected);
}
