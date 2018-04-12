//based on work
//Copyright (c) 2015 Alexis Beingessner
#![feature(nll)]
use std::ops::Deref;
use std::ptr;
use std::iter::FromIterator;

pub struct List<T> {
    head: Link<T>,
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
    pub fn new_boxed(elem: T) -> Box<Self> {
        Box::new(Node {
            elem: elem,
            next: None,
        })
    }
}

impl<T> Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.elem
    }
}

impl<T> List<T> {
    pub fn new() -> Self {
        List {
            head: None,
            tail: ptr::null_mut(),
        }
    }

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
                return;
            }
            cur = &mut node.next;
        }
        self.push_back(new_node);
    }

    pub fn split<F>(&mut self, func: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        let mut list = List::new();
        if let &mut Some(ref mut node) = &mut self.head {
            if func(node.deref().deref()) {
                std::mem::swap(&mut self.head, &mut list.head);
                list.tail = self.tail;
                self.tail = ptr::null_mut();
                return list;
            }
        }
        let mut cur = &mut self.head;
        while let &mut Some(ref mut node) = cur {
            if let &mut Some(ref mut next) = &mut node.next {
                if func(next.deref().deref()) {
                    std::mem::swap(&mut list.head, &mut node.next);
                    list.tail = self.tail;
                    self.tail = &mut **node as *mut _;
                    return list;
                }
            }
            cur = &mut node.next;
        }
        list
    }

    pub fn push_front(&mut self, mut new_head: Box<Node<T>>) {
        if self.tail.is_null() {
            let raw_tail: *mut _ = &mut *new_head;
            self.tail = raw_tail;
        }
        std::mem::swap(&mut new_head.next, &mut self.head);
        self.head = Some(new_head);
    }

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
    }

    pub fn pop_front(&mut self) -> Option<Box<Node<T>>> {
        self.head.take().map(|mut head| {
            std::mem::swap(&mut self.head, &mut head.next);

            if self.head.is_none() {
                self.tail = ptr::null_mut();
            }

            head
        })
    }

    pub fn peek_front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn peek_front_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_ref().map(|node| &**node),
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            next: self.head.as_mut().map(|node| &mut **node),
        }
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut cur_link = self.head.take();
        while let Some(mut boxed_node) = cur_link {
            cur_link = boxed_node.next.take();
        }
    }
}

/// Create a List<T> from anything that implements IntoIterator<Item=T>
///
/// Note:
/// This does allocate boxed nodes.
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

#[cfg(test)]
mod test {
    use super::List;
    use super::Node;
    use std::ops::Deref;
    use std::iter::FromIterator;

    #[test]
    fn basics() {
        let mut list = List::new();

        // Check empty list behaves right
        assert!(list.pop_front().is_none());

        // Populate list
        list.push_back(Node::new_boxed(1));
        list.push_back(Node::new_boxed(2));
        list.push_back(Node::new_boxed(3));

        // Check normal removal
        assert_eq!(list.pop_front().unwrap().deref().deref(), &1);
        assert_eq!(list.pop_front().unwrap().deref().deref(), &2);

        // Push some more just to make sure nothing's corrupted
        list.push_back(Node::new_boxed(4));
        list.push_back(Node::new_boxed(5));

        // Check normal removal
        assert_eq!(list.pop_front().unwrap().deref().deref(), &3);
        assert_eq!(list.pop_front().unwrap().deref().deref(), &4);

        // Check exhaustion
        assert_eq!(list.pop_front().unwrap().deref().deref(), &5);
        assert!(list.pop_front().is_none());
        assert!(list.pop_front().is_none());

        // Check the exhaustion case fixed the pointer right
        list.push_back(Node::new_boxed(6));
        list.push_back(Node::new_boxed(7));

        // Check normal removal
        assert_eq!(list.pop_front().unwrap().deref().deref(), &6);
        assert_eq!(list.pop_front().unwrap().deref().deref(), &7);
        assert!(list.pop_front().is_none());

        // check push_front
        list.push_front(Node::new_boxed(1));
        assert_eq!(list.peek_front().unwrap().deref().deref(), &1);
        list.push_front(Node::new_boxed(2));
        assert_eq!(list.peek_front().unwrap().deref().deref(), &2);

        //check insert
        //add before 1
        list.insert(Node::new_boxed(4), |_, x| x == &1);
        list.insert(Node::new_boxed(5), |_, x| x == &1);
        //should be 2, 4, 5, 1
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&5));
            assert_eq!(iter.next(), Some(&1));
        }

        //push front
        list.insert(Node::new_boxed(6), |_, x| x == &2);

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

        let mut s = list.split(|v| v == &2);

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

        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }

        {
            s.push_back(Node::new_boxed(8));
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), Some(&8));
            assert_eq!(iter.next(), None);
        }
    }

    #[test]
    fn split() {
        let mut list = List::from_iter(vec![2, 3, 4]);

        let mut s = list.split(|v| v == &3);
        {
            let mut iter = list.iter();
            assert_eq!(iter.next(), Some(&2));
            assert_eq!(iter.next(), None);
        }
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&3));
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }

        //make sure that the back pointer is correct
        list.push_back(Node::new_boxed(8));
        s.push_back(Node::new_boxed(2084));
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
        {
            let mut iter = s.iter();
            assert_eq!(iter.next(), Some(&4));
            assert_eq!(iter.next(), None);
        }

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
    }

    #[test]
    fn split_end() {
        let mut list = List::from_iter(vec![2, 3, 4]);
        let mut s = list.split(|_| false);
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
}
