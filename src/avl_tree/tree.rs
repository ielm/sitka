use super::constants::BALANCE_THRESHOLD;
use super::node::{Node, OptNode};
use std::cmp::Ordering;
use std::collections::{HashSet, VecDeque};
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
    pub fn new() -> Self {
        AvlTree {
            root: None,
            len: 0,
            _marker: PhantomData,
        }
    }

    pub fn insert(&mut self, k: K, v: V) {
        self._insert_kv(k, v);
    }

    pub fn get(&self, k: &K) -> Option<V> {
        self._get_node(k).and_then(|n| Node::get_value(Some(n)))
    }

    pub fn get_mut(&mut self, k: &K) -> Option<&'static mut V> {
        self._get_mut_value(k)
    }

    pub fn remove(&mut self, k: &K) -> Option<V> {
        self._remove_node(k).and_then(|n| Node::get_value(Some(n)))
    }

    pub fn contains(&self, k: &K) -> bool {
        self._get_node(k).is_some()
    }

    pub fn peek_root(&self) -> Option<(K, V)> {
        self.root.map(|n| unsafe {
            let node = Box::from_raw(n.as_ptr());
            (node.key, node.value)
        })
    }

    pub fn pop_max(&mut self) -> Option<(K, V)> {
        self._pop_max().map(|n| unsafe {
            let node = Box::from_raw(n.as_ptr());
            (node.key, node.value)
        })
    }

    pub fn pop_max_boxed(&mut self) -> Option<Box<Node<K, V>>> {
        self._pop_max_boxed()
    }

    pub fn pop_min(&mut self) -> Option<(K, V)> {
        self._pop_min().map(|n| unsafe {
            let node = Box::from_raw(n.as_ptr());
            (node.key, node.value)
        })
    }

    pub fn pop_min_boxed(&mut self) -> Option<Box<Node<K, V>>> {
        self._pop_min_boxed()
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            next_nodes: vec![self.root],
            seen: HashSet::new(),
            next_back_nodes: vec![self.root],
            seen_back: HashSet::new(),
            _marker: PhantomData,
        }
    }

    pub fn len(&self) -> isize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn is_balanced(&self) -> bool {
        self._is_balanced()
    }

    pub fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<K: Ord, V> Default for AvlTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord, V> Drop for AvlTree<K, V> {
    fn drop(&mut self) {
        struct DropGuard<'a, K: Ord, V>(&'a mut AvlTree<K, V>);
        impl<'a, K: Ord, V> Drop for DropGuard<'a, K, V> {
            fn drop(&mut self) {
                self.0.clear();
            }
        }

        while let Some(b) = self._pop_min_boxed() {
            let guard = DropGuard(self);
            drop(b);
            std::mem::forget(guard);
        }
    }
}

impl<K: Ord, V> AvlTree<K, V> {
    /// Inserts a key-value pair into the AVL tree.
    ///
    /// This function serves as a wrapper to call the recursive `_insert_kv_recursive`
    /// function with the root node of the tree.
    ///
    /// If the key already exists in the tree, the corresponding value is updated.
    /// If the key does not exist, a new node is created and inserted into the tree.
    /// The tree is then rebalanced to maintain the AVL property.
    ///
    /// # Arguments
    ///
    /// * `k` - The key to be inserted.
    /// * `v` - The value associated with the key.
    fn _insert_kv(&mut self, k: K, v: V) {
        self._insert_kv_recursive(self.root, k, v);
    }

    /// Recursively inserts a key-value pair into the AVL tree.
    ///
    /// This function recursively traverses the tree to find the appropriate position
    /// for inserting the new key-value pair. If the key already exists in the tree,
    /// the corresponding value is updated. If the key does not exist, a new node is
    /// created and inserted into the tree. The tree is then rebalanced to maintain
    /// the AVL property.
    ///
    /// # Arguments
    ///
    /// * `node` - The current node being visited during the recursive traversal.
    /// * `k` - The key to be inserted.
    /// * `v` - The value associated with the key.
    fn _insert_kv_recursive(&mut self, node: OptNode<K, V>, k: K, v: V) {
        match node {
            None => {
                // If the current node is None, create a new node and insert it
                let new_node = Box::new(Node::new(k, v));
                let new_node_ptr = NonNull::new(Box::into_raw(new_node));
                self.len += 1;
                self.root = new_node_ptr;
            }
            Some(curr) => match Node::compare_key(Some(curr), &k) {
                None => {}
                Some(Ordering::Less) => {
                    // If the key is greater than the current node's key,
                    // recursively insert into the right subtree
                    let right = Node::get_right(Some(curr));
                    if right.is_none() {
                        // If the right child is None, insert a new node as the right child
                        self.len += 1;
                        let right_box = Box::new(Node::new(k, v));
                        let right = NonNull::new(Box::into_raw(right_box));
                        Node::set_right(Some(curr), right);
                        Node::set_parent(right, Some(curr));
                        AvlTree::_update_heights(Some(curr));
                        self._try_rebalance(right);
                    } else {
                        self._insert_kv_recursive(right, k, v);
                    }
                }
                Some(Ordering::Greater) => {
                    // If the key is less than the current node's key,
                    // recursively insert into the left subtree
                    let left = Node::get_left(Some(curr));
                    if left.is_none() {
                        // If the left child is None, insert a new node as the left child
                        self.len += 1;
                        let left_box = Box::new(Node::new(k, v));
                        let left = NonNull::new(Box::into_raw(left_box));
                        Node::set_left(Some(curr), left);
                        Node::set_parent(left, Some(curr));
                        AvlTree::_update_heights(Some(curr));
                        self._try_rebalance(left);
                    } else {
                        self._insert_kv_recursive(left, k, v);
                    }
                }
                Some(Ordering::Equal) => {
                    // If the key already exists, update its value
                    Node::set_value(Some(curr), v);
                }
            },
        }
    }

    /// Binary search to retrieve a node given a key
    ///
    /// This function performs a binary search on the AVL tree to find the node
    /// that contains the specified key. It starts at the root node and traverses
    /// down the tree by comparing the keys at each node.
    ///
    /// # Arguments
    ///
    /// * `k` - The key to search for in the tree.
    ///
    /// # Returns
    ///
    /// * `OptNode<K, V>` - An optional node that contains the specified key.
    ///                     Returns `Some(node)` if the key is found, or `None`
    ///                     if the key is not present in the tree.
    fn _get_node(&self, k: &K) -> OptNode<K, V> {
        // Start the search at the root node
        let mut node = self.root;

        // Traverse the tree until the key is found or the search ends
        loop {
            // Compare the key of the current node with the search key
            match Node::compare_key(node, k) {
                // If the current node is None, the key is not found
                None => break None,
                // If the search key is greater than the current node's key
                // move to the right child
                Some(Ordering::Less) => {
                    node = Node::get_right(node);
                    continue;
                }
                // If the search key is less than the current node's key,
                // move to the left child
                Some(Ordering::Greater) => {
                    node = Node::get_left(node);
                    continue;
                }

                // If the search key is equal to the current node's key,
                // the key has been found. Break the loop and return the node
                Some(Ordering::Equal) => break node,
            }
        }
    }

    /// Retrieves a mutable reference to the value associated with the given key.
    ///
    /// This function searches for the node with the specified key and returns a mutable
    /// reference to its associated value if found.
    ///
    /// # Arguments
    ///
    /// * `k` - The key to search for in the tree.
    ///
    /// # Returns
    ///
    /// * `Option<&'static mut V>` - An optional mutable reference to the value associated with the key.
    ///                              Returns `Some(&mut value)` if the key is found, or `None` if the key
    ///                              is not present in the tree.
    fn _get_mut_value(&mut self, k: &K) -> Option<&'static mut V> {
        // Search for the node with the given key
        let node = self._get_node(k);
        // Retrieve a mutable reference to the value of the node
        Node::get_mut_value(node)
    }

    /// Finds the maximum child node starting from the given node.
    ///
    /// This function traverses the right subtree starting from the given node to find
    /// the node with the maximum key value.
    ///
    /// # Arguments
    ///
    /// * `node` - The starting node for the search.
    ///
    /// # Returns
    ///
    /// * `OptNode<K, V>` - An optional node representing the maximum child node.
    ///                     Returns `Some(node)` if a maximum child is found, or `None`
    ///                     if the given node is `None`.
    fn _find_max_child(&self, node: OptNode<K, V>) -> OptNode<K, V> {
        // Start the search at the given node
        let mut current = node;
        // Traverse the right subtree until the rightmost node is found
        loop {
            // Get the right child of the current node
            let right = Node::get_right(current);
            if right.is_some() {
                // If the right child exists, update current to the right child
                current = right;
                continue;
            }
            // If the right child is None, the current node is the maximum
            break current;
        }
    }

    /// Finds the minimum child node starting from the given node.
    ///
    /// This function traverses the left subtree starting from the given node to find
    /// the node with the minimum key value.
    ///
    /// # Arguments
    ///
    /// * `node` - The starting node for the search.
    ///
    /// # Returns
    ///
    /// * `OptNode<K, V>` - An optional node representing the minimum child node.
    ///                     Returns `Some(node)` if a minimum child is found, or `None`
    ///                     if the given node is `None`.
    fn _find_min_child(&self, node: OptNode<K, V>) -> OptNode<K, V> {
        // Start the search at the given node
        let mut current = node;
        // Traverse the left subtree until the leftmost node is found
        loop {
            // Get the left child of the current node
            let left = Node::get_left(current);
            if left.is_some() {
                // If the left child exists, update current to the left child
                current = left;
                continue;
            }
            // If the left child is None, the current node is the minimum
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
                            AvlTree::_update_heights(parent);
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
                    AvlTree::_update_heights(replacement);
                    // Try to rebalance the tree starting from the replacement node
                    self._try_rebalance(replacement);
                }

                // Return the removed node
                node
            }
        }
    }

    /// Removes and returns the node with the maximum key from the AVL tree.
    ///
    /// This function finds the node with the maximum key in the tree, removes it
    /// from the tree, and returns the removed node.
    ///
    /// # Returns
    ///
    /// * `OptNode<K, V>` - An optional node representing the removed maximum node.
    ///                     Returns `Some(node)` if the maximum node is found and removed,
    ///                     or `None` if the tree is empty.
    fn _pop_max(&mut self) -> OptNode<K, V> {
        // Find the node with the maximum key in the tree
        let max = self._find_max_child(self.root);
        // Remove the maximum node from the tree and return it
        self._remove_node(&Node::get_key(max).unwrap())
    }

    /// Removes and returns the node with the maximum key from the AVL tree as a boxed node.
    ///
    /// This function finds the node with the maximum key in the tree, removes it
    /// from the tree, and returns the removed node as a boxed node.
    ///
    /// # Returns
    ///
    /// * `Option<Box<Node<K, V>>>` - An optional boxed node representing the removed maximum node.
    ///                               Returns `Some(boxed_node)` if the maximum node is found and removed,
    ///                               or `None` if the tree is empty.
    fn _pop_max_boxed(&mut self) -> Option<Box<Node<K, V>>> {
        // Call _pop_max() to remove and return the maximum node
        // Convert the returned optional node to a boxed node using Node::boxed()
        Node::boxed(self._pop_max())
    }

    /// Removes and returns the node with the minimum key from the AVL tree.
    ///
    /// This function finds the node with the minimum key in the tree, removes it
    /// from the tree, and returns the removed node.
    ///
    /// # Returns
    ///
    /// * `OptNode<K, V>` - An optional node representing the removed minimum node.
    ///                     Returns `Some(node)` if the minimum node is found and removed,
    ///                     or `None` if the tree is empty.
    fn _pop_min(&mut self) -> OptNode<K, V> {
        // Find the node with the minimum key in the tree
        let min = self._find_min_child(self.root);
        // Remove the minimum node from the tree and return it
        self._remove_node(&Node::get_key(min).unwrap())
    }

    /// Removes and returns the node with the minimum key from the AVL tree as a boxed node.
    ///
    /// This function finds the node with the minimum key in the tree, removes it
    /// from the tree, and returns the removed node as a boxed node.
    ///
    /// # Returns
    ///
    /// * `Option<Box<Node<K, V>>>` - An optional boxed node representing the removed minimum node.
    ///                               Returns `Some(boxed_node)` if the minimum node is found and removed,
    ///                               or `None` if the tree is empty.
    fn _pop_min_boxed(&mut self) -> Option<Box<Node<K, V>>> {
        // Call _pop_min() to remove and return the minimum node
        // Convert the returned optional node to a boxed node using Node::boxed()
        Node::boxed(self._pop_min())
    }

    /// Performs a right rotation on the subtree rooted at node `y`.
    ///
    /// The right rotation operation is used to rebalance the AVL tree when the left subtree
    /// of a node becomes too heavy. It rotates the subtree rooted at `y` to the right, making
    /// `x` the new root of the subtree.
    ///
    /// The rotation is performed as follows:
    ///
    ///       y                x
    ///      / \             /   \
    ///     x  T4           z     y
    ///    / \      -->    / \   / \
    ///   z  T3           T1 T2 T3 T4
    ///  / \
    /// T1 T2
    ///
    /// # Arguments
    ///
    /// * `y` - The root node of the subtree to be rotated.
    fn _rotate_right(&mut self, y: OptNode<K, V>) {
        // Get the parent of node y
        let y_parent = Node::get_parent(y);
        // Get the left child of node y (node x)
        let x = Node::get_left(y);
        // Get the right child of node x (node T3)
        let t3 = Node::get_right(x);

        // Update the parent-child relationships
        Node::set_parent(t3, y); // Set y as the parent of T3
        Node::set_parent(y, x); // Set x as the parent of y
        Node::set_parent(x, y_parent); // Set the parent of y as the parent of x

        // If y was the root of the tree, update the root to x
        if y_parent.is_none() {
            self.root = x;
        }

        // Update the heights of the affected nodes
        Node::update_height(y);
        Node::update_height(x);
        // Update the heights of the nodes above x
        AvlTree::_update_upper_nodes(x);
    }

    /// Performs a left rotation on the subtree rooted at node `x`.
    ///
    /// The left rotation operation is used to rebalance the AVL tree when the right
    /// subtree of a node becomes too heavy. It rotates the subtree rooted at `x` to
    /// the left, making`y` the new root of the subtree.
    ///
    /// The rotation is performed as follows:
    ///
    ///      x                  y
    ///     / \               /   \
    ///    T1  y             x     z
    ///       / \    -->    / \   / \
    ///      T2  z         T1 T2 T3 T4
    ///         / \
    ///        T3 T4
    ///
    /// # Arguments
    ///
    /// * `x` - The root node of the subtree to be rotated.
    fn _rotate_left(&mut self, x: OptNode<K, V>) {
        // Get the parent of node x
        let x_parent = Node::get_parent(x);
        // Get the right child of node x (node y)
        let y = Node::get_right(x);
        // Get the left child of node y (node T2)
        let t2 = Node::get_left(y);

        // Update the parent-child relationships
        Node::set_parent(t2, x); // Set x as the parent of T2
        Node::set_parent(x, y); // Set y as the parent of x
        Node::set_parent(y, x_parent); // Set the parent of x as the parent of y

        // If x was the root of the tree, update the root to y
        if x_parent.is_none() {
            self.root = y;
        }

        // Update the heights of the affected nodes
        Node::update_height(x);
        Node::update_height(y);
        // Update the heights of the nodes above y
        AvlTree::_update_upper_nodes(y);
    }

    /// Calculates the balance factor of a node.
    ///
    /// The balance factor is the difference between the heights of the left and right
    /// subtrees. It indicates whether the tree is balanced or not. A balance factor
    /// of 0, 1, or -1 is considered balanced.
    ///
    /// # Arguments
    ///
    /// * `node` - The node for which to calculate the balance factor.
    ///
    /// # Returns
    ///
    /// The balance factor of the node.
    fn _get_balance_factor(&self, node: OptNode<K, V>) -> isize {
        if node.is_none() {
            0
        } else {
            Node::get_height(Node::get_left(node)) - Node::get_height(Node::get_right(node))
        }
    }

    /// Checks if the AVL tree is balanced using Breadth-First Search (BFS) traversal.
    ///
    /// The tree is considered balanced if the absolute value of the balance factor
    /// of each node is less than or equal to 1.
    ///
    /// # Returns
    ///
    /// `true` if the tree is balanced, `false` otherwise.
    fn _is_balanced(&self) -> bool {
        let mut queue = VecDeque::new();
        queue.push_back(self.root);

        loop {
            match queue.pop_front() {
                None => break true,
                Some(node) => {
                    // Check if the balance factor of the current node exceeds the balance threshold
                    if self._get_balance_factor(node).abs() > BALANCE_THRESHOLD {
                        break false;
                    }

                    // Enqueue the left and right children of the current node if they exist
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

    /// Attempts to rebalance the AVL tree starting from the given node.
    ///
    /// It finds the first unbalanced node from the bottom up and rebalances the tree if an unbalanced node is found.
    ///
    /// # Arguments
    ///
    /// * `node` - The node from which to start the rebalancing process.
    fn _try_rebalance(&mut self, node: OptNode<K, V>) {
        let unbalanced = self._get_unbalanced_node(node);
        if unbalanced.is_some() {
            self._rebalance(unbalanced);
        }
    }

    /// Rebalances the AVL tree at the given unbalanced node.
    ///
    /// It performs the necessary rotations based on the balance factor and the balance factors of the child nodes.
    ///
    /// # Arguments
    ///
    /// * `node` - The unbalanced node at which to perform the rebalancing.
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

    /// Finds the first unbalanced node from the bottom up.
    ///
    /// This function traverses the tree from the given node upwards until it finds a
    /// node with a balance factor greater than 1 or reaches the root.
    ///
    /// # Arguments
    ///
    /// * `node` - The node from which to start the search for an unbalanced node.
    ///
    /// # Returns
    ///
    /// The first unbalanced node encountered, or `None` if no unbalanced node is found.
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

    /// Recursively updates the heights of the nodes in the AVL tree.
    ///
    /// This function updates the heights of the nodes starting from the given node and
    /// propagating the changes upwards to the root.
    ///
    /// # Arguments
    ///
    /// * `node` - The node from which to start updating the heights.
    fn _update_heights(node: OptNode<K, V>) -> isize {
        match node {
            None => 0,
            Some(curr) => {
                let left_height = AvlTree::_update_heights(Node::get_left(Some(curr)));
                let right_height = AvlTree::_update_heights(Node::get_right(Some(curr)));
                let new_height = std::cmp::max(left_height, right_height) + 1;
                Node::set_height(Some(curr), new_height);
                AvlTree::_update_upper_nodes(Some(curr));
                new_height
            }
        }
    }

    /// Recursively updates the heights of the nodes above the given node.
    ///
    /// This function traverses upwards from the given node and updates the heights of
    /// the parent nodes until the root is reached or the height remains unchanged.
    ///
    /// # Arguments
    ///
    /// * `node` - The node from which to start updating the heights of the upper nodes.
    fn _update_upper_nodes(node: OptNode<K, V>) {
        if let Some(curr) = node {
            let parent = Node::get_parent(Some(curr));
            if let Some(p) = parent {
                let new_height = std::cmp::max(
                    Node::get_height(Node::get_left(Some(p))),
                    Node::get_height(Node::get_right(Some(p))),
                ) + 1;
                if new_height != Node::get_height(Some(p)) {
                    Node::set_height(Some(p), new_height);
                    AvlTree::_update_upper_nodes(Node::get_parent(Some(p)));
                }
            }
        }
    }
}

impl<K: Ord, V> IntoIterator for AvlTree<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for AvlTree<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut tree = AvlTree::new();
        for (k, v) in iter {
            tree.insert(k, v);
        }
        tree
    }
}

unsafe impl<K: Ord + Send, V: Send> Send for AvlTree<K, V> {}

unsafe impl<K: Ord + Sync, V: Sync> Sync for AvlTree<K, V> {}

pub struct IntoIter<K: Ord, V>(AvlTree<K, V>);

impl<K: Ord, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0._pop_min().map(|n| Node::into_element(Some(n)))
    }
}

impl<K: Ord, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0._pop_max().map(|n| Node::into_element(Some(n)))
    }
}

impl<K: Ord, V> Drop for IntoIter<K, V> {
    fn drop(&mut self) {
        struct DropGuard<'a, K: Ord, V>(&'a mut IntoIter<K, V>);

        impl<'a, K: Ord, V> Drop for DropGuard<'a, K, V> {
            fn drop(&mut self) {
                for _ in self.0.by_ref() {}
            }
        }

        while let Some(d) = self.next() {
            let guard = DropGuard(self);
            drop(d);
            std::mem::forget(guard);
        }
    }
}

pub struct Iter<'a, K: Ord, V> {
    next_nodes: Vec<OptNode<K, V>>,
    seen: HashSet<NonNull<Node<K, V>>>,
    next_back_nodes: Vec<OptNode<K, V>>,
    seen_back: HashSet<NonNull<Node<K, V>>>,
    _marker: PhantomData<&'a Node<K, V>>,
}

impl<'a, K: Ord, V> Iter<'a, K, V> {
    fn next_ascending(&mut self) -> OptNode<K, V> {
        while let Some(node) = self.next_nodes.pop() {
            let left = node
                .as_ref()
                .and_then(|n| Node::get_left(Some(*n)))
                .filter(|n| !self.seen.contains(n));
            let right = node
                .as_ref()
                .and_then(|n| Node::get_right(Some(*n)))
                .filter(|n| !self.seen.contains(n));

            if left.is_some() && right.is_some() {
                self.next_nodes.push(node);
                self.next_nodes.push(left);
            } else if left.is_some() {
                self.next_nodes.push(node);
            } else {
                if right.is_some() {
                    self.next_nodes.push(right);
                    if let Some(n) = node {
                        self.seen.insert(n);
                    }
                    return node;
                }
                if let Some(n) = node {
                    self.seen.insert(n);
                }
                return node;
            }
        }
        None
    }

    fn next_descending(&mut self) -> OptNode<K, V> {
        while let Some(node) = self.next_back_nodes.pop() {
            let left = node
                .as_ref()
                .and_then(|n| Node::get_left(Some(*n)))
                .filter(|n| !self.seen_back.contains(n));
            let right = node
                .as_ref()
                .and_then(|n| Node::get_right(Some(*n)))
                .filter(|n| !self.seen_back.contains(n));

            if left.is_some() && right.is_some() {
                self.next_back_nodes.push(node);
                self.next_back_nodes.push(right);
            } else {
                if left.is_some() {
                    self.next_back_nodes.push(left);
                    if let Some(n) = node {
                        self.seen_back.insert(n);
                    }
                    return node;
                }
                if right.is_some() {
                    self.next_back_nodes.push(node);
                    self.next_back_nodes.push(right);
                } else {
                    if let Some(n) = node {
                        self.seen.insert(n);
                    }
                    return node;
                }
            }
        }
        None
    }
}

impl<'a, K: Ord, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.next_ascending()
            .as_ref()
            .map(|n| unsafe { (&(*n.as_ptr()).key, &(*n.as_ptr()).value) })
    }
}

impl<'a, K: Ord, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_descending()
            .as_ref()
            .map(|n| unsafe { (&(*n.as_ptr()).key, &(*n.as_ptr()).value) })
    }
}
