//based on work
//Copyright (c) 2015 Alexis Beingessner

#![feature(nll)]
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};
use std::ptr;

#[derive(Debug)]
pub struct List<T> {
    head: Link<T>,
    count: usize,
    tail: *mut Node<T>,
}

type Link<T> = Option<Box<Node<T>>>;

#[derive(Debug)]
pub struct Node<T> {
    elem: T,
    next: Link<T>,
}

pub struct IntoIter<T>(List<T>);

pub struct Iter<'a, T: 'a> {
    next: Option<&'a Node<T>>,
}

pub struct IterMut<'a, T: 'a> {
    next: Option<&'a mut Node<T>>,
}

impl<T> Node<T> {
    /// Create a new node on the heap.
    pub fn new_boxed(elem: T) -> Box<Self> {
        Box::new(Node {
            elem: elem,
            next: None,
        })
    }
}

impl<T> Deref for Node<T> {
    type Target = T;

    /// Get a reference to the item held by this node.
    fn deref(&self) -> &T {
        &self.elem
    }
}

impl<T> DerefMut for Node<T> {
    /// Get a mutable reference to the item held by this node.
    fn deref_mut(&mut self) -> &mut T {
        &mut self.elem
    }
}

impl<T> List<T> {
    /// Create a new empty list.
    pub fn new() -> Self {
        List {
            head: None,
            count: 0,
            tail: ptr::null_mut(),
        }
    }

    /// Get the current count of nodes in the list.
    pub fn count(&self) -> usize {
        self.count
    }

    /// Push a node to the front of the list
    pub fn push_front(&mut self, mut new_head: Box<Node<T>>) {
        if self.tail.is_null() {
            let raw_tail: *mut _ = &mut *new_head;
            self.tail = raw_tail;
        }
        std::mem::swap(&mut new_head.next, &mut self.head);
        self.head = Some(new_head);
        self.count = self.count + 1;
    }

    /// Push a node to the back of the list
    pub fn push_back(&mut self, mut new_tail: Box<Node<T>>) {
        let raw_tail: *mut _ = &mut *new_tail;

        if !self.tail.is_null() {
            unsafe {
                (*self.tail).next = Some(new_tail);
            }
        } else {
            self.head = Some(new_tail);
        }

        self.tail = raw_tail;
        self.count = self.count + 1;
    }

    /// Pop a node from the front of the list, if there is one.
    pub fn pop_front(&mut self) -> Option<Box<Node<T>>> {
        self.head.take().map(|mut head| {
            std::mem::swap(&mut self.head, &mut head.next);

            if self.head.is_none() {
                self.tail = ptr::null_mut();
                self.count = 0;
            } else if self.count > 0 {
                self.count = self.count - 1;
            }

            head
        })
    }

    /// Pop's elements from the front of the list while the given function, `func` returns true.
    ///
    /// # Arguments
    /// * `func` - A function that is given a reference to the item the front node holds. If the
    /// func returns true then the front node is popped and returned, otherwise None is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use xnor_llist::Node;
    /// use xnor_llist::List;
    /// use std::iter::FromIterator;
    ///
    /// let mut l = List::from_iter(vec![1,2,3,4]);
    ///
    /// while let Some(node) = l.pop_front_while(|i| *i < 3) {
    ///     println!("{}", **node)
    /// }
    ///
    /// let mut it = l.iter();
    /// assert_eq!(it.next(), Some(&3));
    /// assert_eq!(it.next(), Some(&4));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn pop_front_while<F>(&mut self, func: F) -> Option<Box<Node<T>>>
    where
        F: Fn(&T) -> bool,
    {
        match self.peek_front() {
            None => None,
            Some(ref node) => {
                if func(node.deref().deref()) {
                    self.pop_front()
                } else {
                    None
                }
            }
        }
    }

    /// Get a reference to the item held by the node at the front of the list, if there is one.
    pub fn peek_front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    /// Get a mutable reference to the item held by the node at the front of the list, if there is one.
    pub fn peek_front_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }

    /// Insert new node
    ///
    /// # Arguments
    /// * `new_node` - The node to insert.
    /// * `func` - a function indicating where to insert.
    ///
    /// # Remarks
    ///
    /// The function takes 2 references, your `new_node`'s value is always the first and a node in
    /// the list is the second. When the function evaluates to `true` the `new_node` is placed before
    /// the second node in the function.
    ///
    /// # Examples
    ///
    /// insert reverse sorted
    ///
    /// ```
    /// use xnor_llist::Node;
    /// use xnor_llist::List;
    ///
    /// let mut l = List::new();
    /// l.push_front(Node::new_boxed(2));
    /// l.push_front(Node::new_boxed(4));
    /// l.insert(Node::new_boxed(3), |new_value, node_value| new_value > node_value);
    ///
    /// let mut it = l.iter();
    /// assert_eq!(it.next(), Some(&4));
    /// assert_eq!(it.next(), Some(&3));
    /// assert_eq!(it.next(), Some(&2));
    /// assert_eq!(it.next(), None);
    /// ```
    ///
    pub fn insert<F>(&mut self, mut new_node: Box<Node<T>>, func: F)
    where
        F: Fn(&T, &T) -> bool,
    {
        let mut cur = &mut self.head;
        while let &mut Some(ref mut node) = cur {
            if func(&new_node, node) {
                std::mem::swap(&mut new_node.elem, &mut node.elem);
                std::mem::swap(&mut new_node.next, &mut node.next);
                if self.tail == &mut **node as *mut _ {
                    self.tail = &mut *new_node as *mut _;
                }
                node.next = Some(new_node);
                self.count = self.count + 1;
                return;
            }
            cur = &mut node.next;
        }
        self.push_back(new_node);
    }

    /// Split the list into 2 lists.
    ///
    /// # Arguments
    /// * `func` - a function indicating where to split.
    ///
    /// # Remarks
    ///
    /// The function gets a reference to a node's value and the first time the function returns
    /// true the list is split before that node.
    ///
    /// If the function always returns false then the return is an empty list.
    /// If the function always returns true then the new list contains all of the old list and the
    /// old list is empty.
    ///
    /// # Example
    ///
    /// split at the 8
    /// ```
    /// use xnor_llist::Node;
    /// use xnor_llist::List;
    /// use std::iter::FromIterator;
    ///
    /// let mut l = List::from_iter(vec![2,0,8,4]);
    /// let s = l.split(|v| v == &8);
    ///
    /// let mut it = l.iter();
    /// assert_eq!(it.next(), Some(&2));
    /// assert_eq!(it.next(), Some(&0));
    /// assert_eq!(it.next(), None);
    ///
    /// let mut it = s.iter();
    /// assert_eq!(it.next(), Some(&8));
    /// assert_eq!(it.next(), Some(&4));
    /// assert_eq!(it.next(), None);
    ///
    /// ```
    pub fn split<F>(&mut self, func: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        let mut list = List::new();
        //the case where we split before the first node
        if let &mut Some(ref mut node) = &mut self.head {
            if func(node.deref().deref()) {
                std::mem::swap(&mut self.head, &mut list.head);
                list.tail = self.tail;
                self.tail = ptr::null_mut();
                list.count = self.count;
                self.count = 0;
                return list;
            }
        }
        let mut cur = &mut self.head;
        let mut count = 0;
        while let &mut Some(ref mut node) = cur {
            count = count + 1;
            if let &mut Some(ref mut next) = &mut node.next {
                if func(next.deref().deref()) {
                    std::mem::swap(&mut list.head, &mut node.next);
                    list.tail = self.tail;
                    self.tail = &mut **node as *mut _;
                    list.count = self.count - count;
                    self.count = count;
                    return list;
                }
            }
            cur = &mut node.next;
        }
        list
    }

    /// Add the contents of another list to the end of this list.
    ///
    /// # Remarks
    ///
    /// This is can be done without iteration, it is fast.
    ///
    /// # Example
    ///
    /// ```
    /// use xnor_llist::Node;
    /// use xnor_llist::List;
    /// use std::iter::FromIterator;
    ///
    /// let mut l = List::from_iter(vec![2,0]);
    /// let mut o = List::from_iter(vec![8,4]);
    ///
    /// l.append(o);
    /// let mut it = l.iter();
    /// assert_eq!(it.next(), Some(&2));
    /// assert_eq!(it.next(), Some(&0));
    /// assert_eq!(it.next(), Some(&8));
    /// assert_eq!(it.next(), Some(&4));
    /// assert_eq!(it.next(), None);
    pub fn append(&mut self, mut other: Self) {
        //if self's tail is null then just replace self with other
        if self.tail.is_null() {
            std::mem::swap(&mut self.head, &mut other.head);
            self.tail = other.tail;
        } else if !other.tail.is_null() {
            //if other's tail not null then append
            let mut link = None;
            std::mem::swap(&mut link, &mut other.head);
            unsafe {
                (*self.tail).next = link;
            }
            self.tail = other.tail;
        }
        other.tail = ptr::null_mut();
        self.count = self.count + other.count;
    }

    /// Add the contents of another list to the front of this list.
    ///
    /// # Remarks
    ///
    /// This is can be done without iteration, it is fast.
    ///
    /// # Example
    ///
    /// ```
    /// use xnor_llist::Node;
    /// use xnor_llist::List;
    /// use std::iter::FromIterator;
    ///
    /// let mut l = List::from_iter(vec![2,0]);
    /// let mut o = List::from_iter(vec![8,4]);
    ///
    /// l.prepend(o);
    /// let mut it = l.iter();
    /// assert_eq!(it.next(), Some(&8));
    /// assert_eq!(it.next(), Some(&4));
    /// assert_eq!(it.next(), Some(&2));
    /// assert_eq!(it.next(), Some(&0));
    /// assert_eq!(it.next(), None);
    pub fn prepend(&mut self, mut other: Self) {
        //simply swap our head/tail with other and then append
        std::mem::swap(&mut self.head, &mut other.head);
        std::mem::swap(&mut self.tail, &mut other.tail);
        self.append(other);
    }

    /// Convert the list into an iterator.
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    /// Get an iterator to references of items in the list.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_ref().map(|node| &**node),
        }
    }

    /// Get an iterator to mutable references of items in the list.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            next: self.head.as_mut().map(|node| &mut **node),
        }
    }
}

impl<T> Drop for List<T> {
    /// Drop the contents of the list
    fn drop(&mut self) {
        let mut cur_link = self.head.take();
        while let Some(mut boxed_node) = cur_link {
            cur_link = boxed_node.next.take();
        }
    }
}

impl<T: PartialOrd> List<T> {
    /// Insert sorted.
    ///
    /// # Remarks
    ///
    /// Assumes the list is sorted, the new_node will be inserted before the first node that's
    /// value is greater than or equal to the inserted node's value.
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// use xnor_llist::Node;
    /// use xnor_llist::List;
    /// use std::iter::FromIterator;
    ///
    /// let mut l = List::from_iter(vec![0,1,3,-1]);
    /// l.insert_sorted(Node::new_boxed(2));
    ///
    /// let mut it = l.iter();
    /// assert_eq!(it.next(), Some(&0));
    /// assert_eq!(it.next(), Some(&1));
    /// assert_eq!(it.next(), Some(&2));
    /// assert_eq!(it.next(), Some(&3));
    /// assert_eq!(it.next(), Some(&-1));
    /// assert_eq!(it.next(), None);
    ///
    /// ```
    pub fn insert_sorted(&mut self, new_node: Box<Node<T>>) {
        self.insert(new_node, |a, b| a.lt(&b));
    }

    /// Sort a list.
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// use xnor_llist::Node;
    /// use xnor_llist::List;
    /// use std::iter::FromIterator;
    ///
    /// let mut l = List::from_iter(vec![0,1,3,-1]);
    /// l.sort();
    ///
    /// let mut it = l.iter();
    /// assert_eq!(it.next(), Some(&-1));
    /// assert_eq!(it.next(), Some(&0));
    /// assert_eq!(it.next(), Some(&1));
    /// assert_eq!(it.next(), Some(&3));
    /// assert_eq!(it.next(), None);
    ///
    /// ```
    pub fn sort(&mut self) {
        let mut other = List::new();
        //simply swap our head/tail with other and then append
        std::mem::swap(&mut self.head, &mut other.head);
        std::mem::swap(&mut self.tail, &mut other.tail);
        std::mem::swap(&mut self.count, &mut other.count);
        for n in other.into_iter() {
            self.insert_sorted(n);
        }
    }
}

/// Create a List<T> from anything that implements IntoIterator<Item=T>
///
/// # Remarks
///
/// This allocates boxed Nodes.
///
impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut l = List::new();
        for i in iter {
            l.push_back(Node::new_boxed(i));
        }
        l
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = Box<Node<T>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_ref().map(|node| &**node);
            &node.elem
        })
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_mut().map(|node| &mut **node);
            &mut node.elem
        })
    }
}

unsafe impl<T> Send for List<T> where T: Send {}

impl<T> Default for List<T>
where
    T: Default,
{
    fn default() -> Self {
        List::new()
    }
}

impl<T> Default for Box<Node<T>>
where
    T: Default,
{
    fn default() -> Self {
        Node::new_boxed(Default::default())
    }
}

#[cfg(test)]
mod test {
    use super::List;
    use super::Node;
    use std::iter::FromIterator;
    use std::ops::Deref;
    use std::sync::atomic::{AtomicUsize, Ordering, ATOMIC_USIZE_INIT};
    use std::thread;

    #[test]
    fn basics() {
        let mut list = List::new();
        assert_eq!(list.count(), 0);

        // Check empty list behaves right
        assert!(list.pop_front().is_none());
        assert_eq!(list.count(), 0);

        // Populate list
        list.push_back(Node::new_boxed(1));
        list.push_back(Node::new_boxed(2));
        list.push_back(Node::new_boxed(3));
        assert_eq!(list.count(), 3);

        // Check normal removal
        assert_eq!(list.pop_front().unwrap().deref().deref(), &1);
        assert_eq!(list.pop_front().unwrap().deref().deref(), &2);

        // Push some more just to make sure nothing's corrupted
        list.push_back(Node::new_boxed(4));
        list.push_back(Node::new_boxed(5));
        assert_eq!(list.count(), 3);

        // Check normal removal
        assert_eq!(list.pop_front().unwrap().deref().deref(), &3);
        assert_eq!(list.pop_front().unwrap().deref().deref(), &4);
        assert_eq!(list.count(), 1);

        // Check exhaustion
        assert_eq!(list.pop_front().unwrap().deref().deref(), &5);
        assert!(list.pop_front().is_none());
        assert_eq!(list.count(), 0);
        assert!(list.pop_front().is_none());
        assert_eq!(list.count(), 0);

        // Check the exhaustion case fixed the pointer right
        list.push_back(Node::new_boxed(6));
        list.push_back(Node::new_boxed(7));
        assert_eq!(list.count(), 2);

        // Check normal removal
        assert_eq!(list.pop_front().unwrap().deref().deref(), &6);
        assert_eq!(list.pop_front().unwrap().deref().deref(), &7);
        assert!(list.pop_front().is_none());
        assert_eq!(list.count(), 0);

        // check push_front
        list.push_front(Node::new_boxed(1));
        assert_eq!(list.peek_front().unwrap().deref().deref(), &1);
        list.push_front(Node::new_boxed(2));
        assert_eq!(list.peek_front().unwrap().deref().deref(), &2);
        assert_eq!(list.count(), 2);

        //check insert
        //add before 1
        list.insert(Node::new_boxed(4), |_, x| x == &1);
        list.insert(Node::new_boxed(5), |_, x| x == &1);
        assert_eq!(list.count(), 4);
        //should be 2, 4, 5, 1
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&1));
        }
        assert_eq!(list.count(), 4);

        //push front
        list.insert(Node::new_boxed(6), |_, x| x == &2);
        assert_eq!(list.count(), 5);

        //should be 6, 2, 4, 5, 1
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&1));
        }

        //push back
        list.insert(Node::new_boxed(7), |_, _| false);
        //should be 6, 2, 4, 5, 1, 7
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&1));
            assert_eq!(iter.next(), Some(&7));
        }
        assert_eq!(list.count(), 6);
    }

    #[test]
    fn node() {
        let mut n = Node::new_boxed(1);
        assert_eq!(1, **n);
        **n = 3;
        assert_eq!(3, **n);
    }

    #[test]
    fn pop_then_push() {
        let mut list = List::from_iter(vec![2, 3, 4]);
        assert_eq!(list.iter().count(), 3);
        assert_eq!(list.count(), 3);

        let mut node = list.pop_front().unwrap();
        assert_eq!(list.count(), 2);
        **node = 23;
        list.push_back(node);
        assert_eq!(list.iter().count(), 3);
        assert_eq!(list.count(), 3);

        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&23));
        assert_eq!(list.count(), 3);
    }

    #[test]
    fn peek_front_mut() {
        let mut list = List::from_iter(vec![2, 3, 4]);
        assert_eq!(list.iter().count(), 3);

        //modify the first item
        {
            let x = list.peek_front_mut();
            assert!(x.is_some());
            let r = x.unwrap();
            *r = 23;
        }
        assert_eq!(list.iter().count(), 3);
        assert_eq!(list.count(), 3);

        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&23));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&4));
    }

    #[test]
    fn from_iter() {
        let list = List::from_iter(vec![2, 3, 4]);
        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn split_at_front() {
        let mut list = List::from_iter(vec![2, 3, 4]);

        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), None);
        assert_eq!(list.count(), 3);

        let mut s = list.split(|v| v == &2);
        assert_eq!(list.count(), 0);
        assert_eq!(s.count(), 3);

        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), None);
        }

        //make sure that the back pointer is correct
        {
            list.push_back(Node::new_boxed(7));
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&7));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 1);

        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(s.count(), 3);

        {
            s.push_back(Node::new_boxed(8));
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(s.count(), 4);
    }

    #[test]
    fn split() {
        let mut list = List::from_iter(vec![2, 3, 4]);
        assert_eq!(list.count(), 3);

        let mut s = list.split(|v| v == &3);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 1);
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(s.count(), 2);

        //make sure that the back pointer is correct
        list.push_back(Node::new_boxed(8));
        s.push_back(Node::new_boxed(2084));
        assert_eq!(list.count(), 2);
        assert_eq!(s.count(), 3);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn split_last() {
        let mut list = List::from_iter(vec![2, 3, 4]);
        let mut s = list.split(|v| v == &4);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 2);
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(s.count(), 1);

        //make sure that the back pointer is correct
        list.push_back(Node::new_boxed(8));
        s.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 3);
        assert_eq!(s.count(), 2);
    }

    #[test]
    fn split_end() {
        let mut list = List::from_iter(vec![2, 3, 4]);
        let mut s = list.split(|_| false);
        assert_eq!(list.count(), 3);
        assert_eq!(s.count(), 0);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), None);
        }

        //make sure that the back pointer is correct
        list.push_back(Node::new_boxed(8));
        s.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 4);
        assert_eq!(s.count(), 1);
    }

    #[test]
    fn into_iter() {
        let mut list = List::new();
        list.push_back(Node::new_boxed(1));
        list.push_back(Node::new_boxed(2));
        list.push_back(Node::new_boxed(3));

        let mut iter = list.into_iter();
        assert_eq!(iter.next().unwrap().deref().deref(), &1);
        assert_eq!(iter.next().unwrap().deref().deref(), &2);
        assert_eq!(iter.next().unwrap().deref().deref(), &3);
        assert!(iter.next().is_none());
        assert!(iter.next().is_none());
    }

    #[test]
    fn iter() {
        let mut list = List::new();
        list.push_back(Node::new_boxed(1));
        list.push_back(Node::new_boxed(2));
        list.push_back(Node::new_boxed(3));

        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut list = List::new();
        list.push_back(Node::new_boxed(1));
        list.push_back(Node::new_boxed(2));
        list.push_back(Node::new_boxed(3));

        let mut iter = list.iter_mut();
        assert_eq!(iter.next(), Some(&mut 1));
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn append_empty() {
        let mut list = List::from_iter(vec![2, 3, 4]);

        //append empty
        let a = List::new();
        assert_eq!(a.count(), 0);
        assert_eq!(list.count(), 3);
        list.append(a);
        assert_eq!(list.count(), 3);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }

        //assert push back
        list.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 4);
    }

    #[test]
    fn append_to_empty() {
        let mut list = List::new();

        //append empty
        let a = List::from_iter(vec![2, 3, 4]);
        assert_eq!(list.count(), 0);
        assert_eq!(a.count(), 3);
        list.append(a);
        assert_eq!(list.count(), 3);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }

        //assert push back
        list.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 4);
    }

    #[test]
    fn append() {
        let mut list = List::from_iter(vec![2, 3]);
        let a = List::from_iter(vec![5, 6]);
        assert_eq!(list.count(), 2);
        assert_eq!(a.count(), 2);
        list.append(a);
        assert_eq!(list.count(), 4);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), None);
        }

        //assert push back
        list.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 5);
    }

    #[test]
    fn prepend() {
        let mut list = List::from_iter(vec![2, 3]);
        let a = List::from_iter(vec![5, 6]);
        assert_eq!(list.count(), 2);
        assert_eq!(a.count(), 2);
        list.prepend(a);
        assert_eq!(list.count(), 4);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), None);
        }

        //assert push back
        list.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 5);
    }

    #[test]
    fn prepend_empty() {
        let mut list = List::from_iter(vec![2, 3]);
        let a = List::new();
        assert_eq!(list.count(), 2);
        assert_eq!(a.count(), 0);
        list.prepend(a);
        assert_eq!(list.count(), 2);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), None);
        }

        //assert push back
        list.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 3);
    }

    #[test]
    fn prepend_to_empty() {
        let mut list = List::new();
        let a = List::from_iter(vec![2, 3]);
        assert_eq!(list.count(), 0);
        assert_eq!(a.count(), 2);
        list.prepend(a);
        assert_eq!(list.count(), 2);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), None);
        }

        //assert push back
        list.push_back(Node::new_boxed(2084));
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&2084));
            assert_eq!(iter.next(), None);
        }
        assert_eq!(list.count(), 3);
    }
    // copied/edited from crossbeam's arc_cell test
    #[test]
    fn drops() {
        static DROPS: AtomicUsize = ATOMIC_USIZE_INIT;

        struct Foo;

        impl Drop for Foo {
            fn drop(&mut self) {
                DROPS.fetch_add(1, Ordering::SeqCst);
            }
        }

        assert_eq!(DROPS.load(Ordering::SeqCst), 0);

        let mut l = List::new();
        for _ in 1..11 {
            let n = Node::new_boxed(Foo);
            l.push_front(n);
        }
        assert_eq!(DROPS.load(Ordering::SeqCst), 0);

        {
            let mut n = l.pop_front();
            assert!(n.is_some());

            //push one back
            n = l.pop_front();
            assert!(n.is_some());
            l.push_front(n.unwrap())
        }
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);
        assert_eq!(l.iter().count(), 9);
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);

        drop(l);
        assert_eq!(DROPS.load(Ordering::SeqCst), 10);

        {
            let _ = Node::new_boxed(Foo);
        }
        assert_eq!(DROPS.load(Ordering::SeqCst), 11);
    }

    #[test]
    fn insert_sorted() {
        let mut l = List::new();
        l.insert_sorted(Node::new_boxed(2));
        l.insert_sorted(Node::new_boxed(0));
        l.insert_sorted(Node::new_boxed(8));
        l.insert_sorted(Node::new_boxed(4));
        assert_eq!(l.count(), 4);

        {
            let mut iter = l.iter();
            assert_eq!(iter.next(), Some(&0));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }

        //make sure back still works though
        l.push_back(Node::new_boxed(-20));
        assert_eq!(l.count(), 5);

        {
            let mut iter = l.iter();
            assert_eq!(iter.next(), Some(&0));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), Some(&-20));
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn sort() {
        let mut l = List::new();
        assert_eq!(l.iter().next(), None);
        assert_eq!(l.count(), 0);
        l.sort();
        assert_eq!(l.iter().next(), None);
        assert_eq!(l.count(), 0);

        l.push_back(Node::new_boxed(2));
        l.push_back(Node::new_boxed(0));
        l.push_back(Node::new_boxed(8));
        l.push_back(Node::new_boxed(4));
        l.push_back(Node::new_boxed(4));
        l.push_back(Node::new_boxed(-20));
        l.push_back(Node::new_boxed(-2));
        assert_eq!(l.count(), 7);

        l.sort();
        assert_eq!(l.count(), 7);
        {
            let mut iter = l.iter();
            assert_eq!(iter.next(), Some(&-20));
            assert_eq!(iter.next(), Some(&-2));
            assert_eq!(iter.next(), Some(&0));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }

        //insert before 0
        l.insert(Node::new_boxed(5), |_, y| y == &0);
        l.push_back(Node::new_boxed(-31));
        l.push_front(Node::new_boxed(6));
        assert_eq!(l.count(), 10);
        {
            let mut iter = l.iter();
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&-20));
            assert_eq!(iter.next(), Some(&-2));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&0));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), Some(&-31));
            assert_eq!(iter.next(), None);
        }

        l.sort();
        assert_eq!(l.count(), 10);
        {
            let mut iter = l.iter();
            assert_eq!(iter.next(), Some(&-31));
            assert_eq!(iter.next(), Some(&-20));
            assert_eq!(iter.next(), Some(&-2));
            assert_eq!(iter.next(), Some(&0));
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&6));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn can_thread() {
        let n = Node::new_boxed(23);
        let mut l = List::new();
        l.push_back(n);

        let c = Node::new_boxed(35);
        let child = thread::spawn(move || {
            l.push_back(c);
            let x = Node::new_boxed(45);
            l.push_front(x);

            let mut it = l.iter();
            assert_eq!(it.next(), Some(&45));
            assert_eq!(it.next(), Some(&23));
            assert_eq!(it.next(), Some(&35));
            assert_eq!(it.next(), None);
        });

        if let Err(e) = child.join() {
            panic!(e);
        }
    }

    #[test]
    fn pop_front_while() {
        let mut l = List::from_iter(vec![1, 2, 3, 4]);
        assert_eq!(l.count(), 4);

        //grab nothing
        assert!(l.pop_front_while(|_| false).is_none());
        assert!(l.pop_front_while(|_| false).is_none());
        assert_eq!(l.count(), 4);

        //grab all
        assert_eq!(**l.pop_front_while(|_| true).unwrap(), 1);
        assert_eq!(**l.pop_front_while(|_| true).unwrap(), 2);
        assert_eq!(**l.pop_front_while(|_| true).unwrap(), 3);
        assert_eq!(**l.pop_front_while(|_| true).unwrap(), 4);
        assert!(l.pop_front_while(|_| true).is_none());
        assert!(l.pop_front_while(|_| true).is_none());
        assert_eq!(l.count(), 0);

        //mid way
        l = List::from_iter(vec![1, 2, 3, 4]);
        assert_eq!(l.count(), 4);
        assert_eq!(**l.pop_front_while(|v| *v < 3).unwrap(), 1);
        assert_eq!(**l.pop_front_while(|v| *v < 3).unwrap(), 2);
        assert!(l.pop_front_while(|v| *v < 3).is_none());
        assert!(l.pop_front_while(|v| *v < 3).is_none());
        assert_eq!(l.count(), 2);

        assert!(l.pop_front_while(|_| false).is_none());
        assert_eq!(l.count(), 2);
        assert!(l.pop_front_while(|_| true).is_some());
        assert!(l.pop_front_while(|_| true).is_some());
        assert_eq!(l.count(), 0);
        assert!(l.pop_front_while(|_| true).is_none());
        assert_eq!(l.count(), 0);
    }

    #[test]
    fn default() {
        let mut l: List<usize> = Default::default();
        l.push_front(Default::default());
        assert_eq!(l.count(), 1);
        assert_eq!(l.peek_front().unwrap(), &0usize);

        l.push_front(Default::default());
        assert_eq!(l.count(), 2);
        assert_eq!(l.pop_front().unwrap().deref().deref(), &0usize);
        assert_eq!(l.pop_front().unwrap().deref().deref(), &0usize);
        assert!(l.pop_front().is_none());
    }
}
