//based on work
//Copyright (c) 2015 Alexis Beingessner

use std::ptr;
use std::ops::Deref;

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

    pub fn push(&mut self, mut new_tail: Box<Node<T>>) {
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

    pub fn pop(&mut self) -> Option<Box<Node<T>>> {
        self.head.take().map(|mut head| {
            std::mem::swap(&mut self.head, &mut head.next);

            if self.head.is_none() {
                self.tail = ptr::null_mut();
            }

            head
        })
    }

    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
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

impl<T> Iterator for IntoIter<T> {
    type Item = Box<Node<T>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
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

    #[test]
    fn basics() {
        let mut list = List::new();

        // Check empty list behaves right
        assert!(list.pop().is_none());

        // Populate list
        list.push(Node::new_boxed(1));
        list.push(Node::new_boxed(2));
        list.push(Node::new_boxed(3));

        // Check normal removal
        assert_eq!(list.pop().unwrap().deref().deref(), &1);
        assert_eq!(list.pop().unwrap().deref().deref(), &2);

        // Push some more just to make sure nothing's corrupted
        list.push(Node::new_boxed(4));
        list.push(Node::new_boxed(5));

        // Check normal removal
        assert_eq!(list.pop().unwrap().deref().deref(), &3);
        assert_eq!(list.pop().unwrap().deref().deref(), &4);

        // Check exhaustion
        assert_eq!(list.pop().unwrap().deref().deref(), &5);
        assert!(list.pop().is_none());
        assert!(list.pop().is_none());

        // Check the exhaustion case fixed the pointer right
        list.push(Node::new_boxed(6));
        list.push(Node::new_boxed(7));

        // Check normal removal
        assert_eq!(list.pop().unwrap().deref().deref(), &6);
        assert_eq!(list.pop().unwrap().deref().deref(), &7);
        assert!(list.pop().is_none());
    }

    #[test]
    fn into_iter() {
        let mut list = List::new();
        list.push(Node::new_boxed(1));
        list.push(Node::new_boxed(2));
        list.push(Node::new_boxed(3));

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
        list.push(Node::new_boxed(1));
        list.push(Node::new_boxed(2));
        list.push(Node::new_boxed(3));

        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut list = List::new();
        list.push(Node::new_boxed(1));
        list.push(Node::new_boxed(2));
        list.push(Node::new_boxed(3));

        let mut iter = list.iter_mut();
        assert_eq!(iter.next(), Some(&mut 1));
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 3));
        assert_eq!(iter.next(), None);
    }
}
