use super::constants::BALANCE_THRESHOLD;
use super::node::{Node, OptNode};
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::marker::PhantomData;
use std::ptr::NonNull;

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
    len: isize,
    _marker: PhantomData<Box<Node<K, V>>>,
}

impl<K: Ord, V> AvlTree<K, V> {
    fn _insert_kv(&mut self, k: K, v: V) {
        if self.root.is_none() {
            let node = Box::new(Node::new(k, v));
            let node_ptr = NonNull::new(Box::into_raw(node));
            self.len += 1;
            self.root = node_ptr;
            return;
        }

        let mut node_stack = vec![self.root];

        'outer: loop {
            let child = node_stack.pop();

            match child {
                None => break 'outer,
                Some(curr) => match Node::compare_key(curr, &k) {
                    None => break 'outer,
                    Some(Ordering::Less) => {
                        let right = Node::get_right(curr);
                        if right.is_some() {
                            node_stack.push(right);
                            continue 'outer;
                        }

                        self.len += 1;
                        let right_box = Box::new(Node::new(k, v));
                        let right = NonNull::new(Box::into_raw(right_box));
                        Node::set_right(curr, right);

                        // Rebalance
                        self._update_heights(self.root);
                        self._try_rebalance(right);

                        break 'outer;
                    }
                    Some(Ordering::Greater) => {
                        let left = Node::get_left(curr);
                        if left.is_some() {
                            node_stack.push(left);
                            continue 'outer;
                        }

                        self.len += 1;
                        let left_box = Box::new(Node::new(k, v));
                        let left = NonNull::new(Box::into_raw(left_box));
                        Node::set_left(curr, left);

                        // Rebalance
                        self._update_heights(self.root);
                        self._try_rebalance(left);

                        break 'outer;
                    }
                    Some(Ordering::Equal) => {
                        Node::set_value(curr, v);
                        break 'outer;
                    }
                },
            }
        }
    }

    /// Binary search to retrieve a node given a key
    fn _get_node(&self, k: &K) -> OptNode<K, V> {
        let mut node = self.root;

        loop {
            match Node::compare_key(node, k) {
                None => break None,
                Some(Ordering::Less) => {
                    node = Node::get_right(node);
                    continue;
                }
                Some(Ordering::Greater) => {
                    node = Node::get_left(node);
                    continue;
                }
                Some(Ordering::Equal) => break node,
            }
        }
    }

    fn _get_mut_value(&mut self, k: &K) -> Option<&'static mut V> {
        let node = self._get_node(k);
        Node::get_mut_value(node)
    }

    fn _find_max_child(&self, node: OptNode<K, V>) -> OptNode<K, V> {
        let mut current = node;
        loop {
            let right = Node::get_right(current);
            if right.is_some() {
                current = right;
                continue;
            }
            break current;
        }
    }

    fn _find_min_child(&self, node: OptNode<K, V>) -> OptNode<K, V> {
        let mut current = node;
        loop {
            let left = Node::get_left(current);
            if left.is_some() {
                current = left;
                continue;
            }
            break current;
        }
    }

    /// Removes a node with the given key from the AVL tree and returns the removed node.
    ///
    /// # Arguments
    ///
    /// * `k` - The key of the node to be removed.
    ///
    /// # Returns
    ///
    /// * `OptNode<K, V>` - The removed node wrapped in an `Option`, or `None` if the node was not found.
    fn _remove_node(&mut self, k: &K) -> OptNode<K, V> {
        // Get the node with the given key
        let target = self._get_node(k);

        match target {
            None => None,
            node @ Some(_) => {
                // Decrement the length of the tree
                self.len -= 1;

                // Get the parent, left child, and right child of the node
                let parent = Node::get_parent(node);
                let left = Node::get_left(node);
                let right = Node::get_right(node);

                // Determine the replacement node and whether to update its parent
                let (replacement, update_parent) = match (left.is_some(), right.is_some()) {
                    // If both left and right children exist
                    (true, true) => {
                        // Find the maximum node in the left subtree
                        let l_max = self._find_max_child(left);
                        // Unlink the maximum node from its parent
                        Node::unlink(l_max, Node::get_parent(l_max));
                        // Set the right child of the maximum node to the right child of the current node
                        Node::set_right(l_max, right);
                        // If the maximum node is not the direct left child, set its left child to the left child of the current node
                        if !l_max.eq(&left) {
                            Node::set_left(l_max, left);
                        }
                        // Return the maximum node as the replacement and indicate to update its parent
                        (l_max, true)
                    }

                    // If only the left child exists
                    (true, false) => {
                        // Find the maximum node in the left subtree
                        let l_max = self._find_max_child(left);
                        // Unlink the maximum node from its parent
                        Node::unlink(l_max, Node::get_parent(l_max));
                        // If the maximum node is not the direct left child, set its left child to the left child of the current node
                        if !l_max.eq(&left) {
                            Node::set_left(l_max, left);
                        }
                        // Return the maximum node as the replacement and indicate to update its parent
                        (l_max, true)
                    }

                    // If the left child is absent and the right child exists,
                    // use the right child as the replacement node and indicate to update its parent
                    (false, true) => (right, true),

                    // If both left and right children are absent
                    (false, false) => {
                        if parent.is_some() {
                            // Unlink the current node from its parent
                            Node::unlink(node, parent);
                            // Update the heights of the nodes starting from the parent
                            self._update_heights(parent);
                            // Try to rebalance the tree starting from the parent
                            self._try_rebalance(parent);
                        } else {
                            // If the current node has no parent, it means it was the root node
                            // Set the root of the tree to None
                            self.root = None;
                        }
                        // Return the removed node
                        return node;
                    }
                };

                if update_parent {
                    if parent.is_some() {
                        // Set the parent of the replacement node to the parent of the current node
                        Node::set_parent(replacement, parent);
                    } else {
                        // If the current node had no parent, it means it was the root node
                        // Set the root of the tree to the replacement node
                        self.root = replacement;
                        // Set the parent of the replacement node to None
                        Node::set_parent(replacement, None);
                    }
                    // Update the heights of the nodes starting from the replacement node
                    self._update_heights(replacement);
                    // Try to rebalance the tree starting from the replacement node
                    self._try_rebalance(replacement);
                }

                // Return the removed node
                node
            }
        }
    }

    fn _pop_max(&mut self) -> OptNode<K, V> {
        let max = self._find_max_child(self.root);
        self._remove_node(&Node::get_key(max).unwrap())
    }

    fn _pop_max_boxed(&mut self) -> Option<Box<Node<K, V>>> {
        Node::boxed(self._pop_max())
    }

    fn _pop_min(&mut self) -> OptNode<K, V> {
        let min = self._find_min_child(self.root);
        self._remove_node(&Node::get_key(min).unwrap())
    }

    fn _pop_min_boxed(&mut self) -> Option<Box<Node<K, V>>> {
        Node::boxed(self._pop_min())
    }

    /// Rotate right on node `y`
    ///
    ///       y                x
    ///      / \             /   \
    ///     x  T4           z     y
    ///    / \      -->    / \   / \
    ///   z  T3           T1 T2 T3 T4
    ///  / \
    /// T1 T2
    ///
    fn _rotate_right(&mut self, y: OptNode<K, V>) {
        let y_parent = Node::get_parent(y);
        let x = Node::get_left(y);
        let t3 = Node::get_right(x);

        Node::set_parent(t3, y);
        Node::set_parent(y, x);
        Node::set_parent(x, y_parent);

        if y_parent.is_none() {
            self.root = x;
        }

        Node::update_height(y);
        Node::update_height(x);
        self._update_upper_nodes(x);
    }

    /// Rotate left on node `x`
    ///      x                y
    ///     / \             /   \
    ///    T1  y           x     z
    ///       / \    -->  / \   / \
    ///      T2  z       T1 T2 T3 T4
    ///         / \
    ///        T3 T4
    ///
    fn _rotate_left(&mut self, x: OptNode<K, V>) {
        let x_parent = Node::get_parent(x);
        let y = Node::get_right(x);
        let t2 = Node::get_left(y);

        Node::set_parent(t2, x);
        Node::set_parent(x, y);
        Node::set_parent(y, x_parent);

        if x_parent.is_none() {
            self.root = y;
        }

        Node::update_height(x);
        Node::update_height(y);
        self._update_upper_nodes(y);
    }

    fn _get_balance_factor(&self, node: OptNode<K, V>) -> isize {
        if node.is_none() {
            0
        } else {
            Node::get_height(Node::get_left(node)) - Node::get_height(Node::get_right(node))
        }
    }

    /// BFS traversal to check if the tree is balanced
    fn _is_balanced(&self) -> bool {
        let mut queue = VecDeque::new();
        queue.push_back(self.root);

        loop {
            match queue.pop_front() {
                None => break true,
                Some(node) => {
                    if self._get_balance_factor(node).abs() > BALANCE_THRESHOLD {
                        break false;
                    }

                    let children = vec![Node::get_left(node), Node::get_right(node)];
                    children.into_iter().for_each(|n| {
                        if n.is_some() {
                            queue.push_back(n);
                        }
                    });
                    continue;
                }
            }
        }
    }

    fn _try_rebalance(&mut self, node: OptNode<K, V>) {
        let unbalanced = self._get_unbalanced_node(node);
        if unbalanced.is_some() {
            self._rebalance(unbalanced);
        }
    }

    fn _rebalance(&mut self, node: OptNode<K, V>) {
        let bf = self._get_balance_factor(node);

        // If the balance factor is greater than 1, then the tree is left-heavy
        if bf > 1 {
            let left = Node::get_left(node);
            let left_bf = self._get_balance_factor(left);

            // If the left child is right-heavy, then rotate left on it
            if left_bf < 0 {
                self._rotate_left(left);
            }

            self._rotate_right(node);

        // If the balance factor is less than -1, then the tree is right-heavy
        } else if bf < -1 {
            let right = Node::get_right(node);
            let right_bf = self._get_balance_factor(right);

            // If the right child is left-heavy, then rotate right on it
            if right_bf > 0 {
                self._rotate_right(right);
            }

            self._rotate_left(node);
        }
    }

    /// Find the first unbalanced node from the bottom up
    fn _get_unbalanced_node(&mut self, node: OptNode<K, V>) -> OptNode<K, V> {
        let mut current = node;
        loop {
            let parent = Node::get_parent(current);
            let bf = self._get_balance_factor(current);
            if bf.abs() > 1 {
                break current;
            }
            if parent.is_some() {
                current = parent;
                continue;
            }
            break None;
        }
    }

    /// DFS traversal to update the heights of the nodes
    fn _update_heights(&mut self, node: OptNode<K, V>) {
        let mut node_stack = vec![node];
        let mut updated = HashMap::<OptNode<K, V>, isize>::new();

        // Update heights of lower nodes
        'outer: loop {
            let child = node_stack.pop();

            match child {
                None => {
                    if node_stack.is_empty() {
                        break 'outer;
                    }
                    continue 'outer;
                }
                Some(curr) => {
                    let children: Vec<OptNode<K, V>> =
                        vec![Node::get_left(curr), Node::get_right(curr)]
                            .into_iter()
                            .filter(|n| n.is_some())
                            .collect();

                    let no_node = curr.is_none();
                    let no_children = children.is_empty();
                    let empty_stack = node_stack.is_empty();

                    if no_node && no_children && empty_stack {
                        break 'outer;
                    }
                    if no_node && !no_children && empty_stack {
                        break 'outer;
                    }
                    if no_node && no_children && !empty_stack {
                        continue 'outer;
                    }
                    // NOTE - Is it possible to have a None node with children?
                    if no_node && !no_children && !empty_stack {
                        children.into_iter().for_each(|n| node_stack.push(n));
                        continue 'outer;
                    }
                    if !no_node && no_children && empty_stack {
                        Node::set_height(curr, 1);
                        break 'outer;
                    }
                    if !no_node && no_children && !empty_stack {
                        Node::set_height(curr, 1);
                        updated.insert(curr, 1);
                        continue 'outer;
                    }

                    let not_seen: Vec<OptNode<K, V>> = children
                        .iter()
                        .copied()
                        .filter(|n| !updated.contains_key(n))
                        .collect();

                    if not_seen.is_empty() {
                        let height =
                            (*children.iter().flat_map(|n| updated.get(n)).max().unwrap()) + 1;
                        Node::set_height(curr, height);
                        updated.insert(curr, height);
                        continue 'outer;
                    }
                    node_stack.push(curr);
                    not_seen.into_iter().for_each(|n| node_stack.push(n));
                    continue 'outer;
                }
            }
        }

        // Update heights of upper nodes
        self._update_upper_nodes(node);
    }

    fn _update_upper_nodes(&mut self, node: OptNode<K, V>) {
        let mut current = node;
        loop {
            let parent = Node::get_parent(current);
            if parent.is_none() {
                break;
            }

            let new_height = std::cmp::max(
                Node::get_height(Node::get_left(parent)),
                Node::get_height(Node::get_right(parent)),
            ) + 1;

            if new_height == Node::get_height(parent) {
                break;
            }

            Node::set_height(parent, new_height);
            current = Node::get_parent(parent);
            continue;
        }
    }
}
