use std::boxed::Box;
use std::ops::Deref;
use std::iter::IntoIterator;
use std::iter::Iterator;
use std::iter::FromIterator;

#[derive(Debug)]
enum Link<T> {
    None,
    Some(Box<Node<T>>)
}

impl<T> Default for Link<T> {
    fn default() -> Self { Link::None }
}

#[derive(Debug)]
pub struct Node<T> {
    next: Link<T>,
    value: T
}

pub struct List<T> {
    head: Link<T>,
    length: usize
}

impl<T> Node<T> {
    /// Create a new boxed node.
    pub fn new_boxed(v: T) -> Box<Self> {
        Box::new(Node { next: Link::default(), value: v })
    }
}

impl<T> Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.value
    }
}

/// A Linked List implementation where the Nodes are pre-allocated and boxed.
impl<T> List<T> {
    /// Create a new list.
    pub fn new() -> Self {
        List { head: Link::default(), length: 0 }
    }

    /// Push a Node onto the front of the list.
    pub fn push_front(&mut self, mut node: Box<Node<T>>) -> () {
        std::mem::swap(&mut node.next, &mut self.head);
        self.head = Link::Some(node);
        self.length = self.length + 1;
    }
    
    /// Pop a Node off the front of the list.
    pub fn pop_front(&mut self) -> Option<Box<Node<T>>> {
        let mut ret = Link::None;
        std::mem::swap(&mut ret, &mut self.head);
        match ret {
            Link::Some(mut node) => {
                self.length = self.length - 1;
                std::mem::swap(&mut node.next, &mut self.head);
                Some(node)
            },
            Link::None => None
        }
    }

    /// Get the length of the list.
    pub fn length(&self) -> usize {
        self.length
    }

    /// Create an iterator over references to times in the nodes of the list.
    pub fn iter(&self) -> ListIterator<T> {
        (&self).into_iter()
    }
}

/// Create a List<T> from anything that implements IntoIterator<Item=T>
/// 
/// Note:
/// This does allocate boxed nodes and the items will appear in the reverse order that they appear
/// in the iterator.
///
impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let mut l = List::new();
        for i in iter {
            l.push_front(Node::new_boxed(i));
        }
        l
    }
}

pub struct ListIterator<'a, T: 'a> 
{
    cur: &'a Link<T>,
    length: usize
}

impl<T: Copy> Iterator for List<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        match self.pop_front() {
            Some(node) => Some(*node.deref().deref()),
            None => None
        }
    }
}

impl <'a, T> Iterator for ListIterator<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        if let &Link::Some(ref node) = self.cur {
            self.cur = &node.next;
            self.length = self.length - 1;
            Some(&node.deref().deref())
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = ListIterator<'a, T>;

    fn into_iter(self) -> ListIterator<'a, T> {
        ListIterator { cur: &self.head, length: self.length }
    }
}

unsafe impl <T> Send for Node<T> where T: Send {}


#[cfg(test)]
mod tests {
    use std::thread;
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering, ATOMIC_USIZE_INIT};

    #[test]
    fn can_push() {
        let mut len: usize = 0;
        let n = Node::new_boxed(23);

        assert_eq!(n.value, 23);
        let mut l = List::new();
        assert_eq!(l.length(), len);

        l.push_front(n);
        len = len + 1;
        assert_eq!(l.length(), len);

        let n = Node::new_boxed(345);
        assert_eq!(n.value, 345);
        l.push_front(n);
        len = len + 1;
        assert_eq!(l.length(), len);

        let c = Node::new_boxed(35);
        let child = thread::spawn(move || {
            assert_eq!(l.length(), len);

            l.push_front(c);
            len = len + 1;
            assert_eq!(l.length(), len);

            let x = Node::new_boxed(45);
            l.push_front(x);
            len = len + 1;
            assert_eq!(l.length(), len);
        });

        if let Err(e) = child.join() {
            panic!(e);
        }
    }

    #[test]
    fn can_thread() {
        let mut len: usize = 0;
        let n = Node::new_boxed(23);

        assert_eq!(n.value, 23);
        let mut l = List::new();
        assert_eq!(l.length(), len);

        let c = Node::new_boxed(35);
        let child = thread::spawn(move || {
            assert_eq!(l.length(), len);

            l.push_front(c);
            len = len + 1;
            assert_eq!(l.length(), len);

            let x = Node::new_boxed(45);
            l.push_front(x);
            len = len + 1;
            assert_eq!(l.length(), len);
        });

        if let Err(e) = child.join() {
            panic!(e);
        }
    }

    #[test]
    fn can_deref() {
        let x = Node::new_boxed(634);
        assert_eq!(x.value, 634);
        assert_eq!(&634, x.deref().deref());
        assert_eq!(&634, &**x);
        assert_eq!(634, **x);
    }

    #[test]
    fn can_pop() {
        let mut l = List::new();
        assert_eq!(l.length(), 0);

        for i in 1..11 {
            let x = Node::new_boxed(i);
            l.push_front(x);
            assert_eq!(l.length(), i);
        }

        for i in (1..11).rev() {
            assert_eq!(l.length(), i);
            let mut n = l.pop_front();
            assert!(n.is_some());
            assert_eq!(n.unwrap().value, i);
        }

        assert_eq!(l.length(), 0);
        let n = l.pop_front();
        assert!(n.is_none());

        l.push_front(Node::new_boxed(42));
        assert_eq!(l.length(), 1);
        l.push_front(Node::new_boxed(2084));
        assert_eq!(l.length(), 2);

        let mut n = l.pop_front();
        assert!(n.is_some());
        assert_eq!(n.unwrap().value, 2084);
        assert_eq!(l.length(), 1);

        n = l.pop_front();
        assert!(n.is_some());
        assert_eq!(n.unwrap().value, 42);
        assert_eq!(l.length(), 0);
        assert!(l.pop_front().is_none());
    }

    #[test]
    fn can_iterate_consuming() {
        let mut l = List::new();
        assert_eq!(l.length(), 0);

        for i in 0..11 {
            let x = Node::new_boxed(i);
            assert_eq!(l.length(), i);
            l.push_front(x);
        }

        for (n, i) in l.zip((0..11).rev()) {
            assert_eq!(n, i);
        }
    }

    #[test]
    fn can_iterate_ref() {
        let mut l = List::new();
        assert_eq!(l.length(), 0);

        for i in 0..11 {
            let x = Node::new_boxed(i);
            assert_eq!(l.length(), i);
            l.push_front(x);
        }
        assert_eq!(l.length(), 11);

        let mut i = 11;
        for n in &l {
            i = i - 1;
            assert_eq!(n, &i);
        }
        assert_eq!(l.length(), 11);

        i = 11;
        for n in l.iter() {
            i = i - 1;
            assert_eq!(n, &i);
        }
        assert_eq!(l.length(), 11);
    }

    #[test]
    fn iter_has_size() {
        let mut l = List::new();
        assert_eq!(l.length(), 0);

        for i in 0..11 {
            let x = Node::new_boxed(i);
            assert_eq!(l.length(), i);
            l.push_front(x);
        }
        assert_eq!(l.length(), 11);

        let it = (&l).into_iter();
        assert_eq!(it.count(), 11);

        let it = (&l).into_iter();
        assert_eq!(it.last(), Some(&0));
    }

    #[test]
    fn can_peek() {
        let mut l = List::new();
        assert_eq!(l.length(), 0);

        for i in 0..11 {
            let x = Node::new_boxed(i);
            assert_eq!(l.length(), i);
            l.push_front(x);
        }

        let mut it = (&l).into_iter().peekable();
        assert_eq!(it.peek(), Some(&&10));

        assert_eq!((&l).into_iter().skip_while(|n| **n > 3).count(), 4);
    }

    #[test]
    fn from_iter() {
        let l = List::from_iter((0..10).rev());
        assert_eq!(l.length(), 10);

        for (i, item) in (0..10).zip(l.iter()) {
            assert_eq!(&i, item);
        }
        assert_eq!(l.length(), 10);

        for (i, item) in (0..10).zip(l.into_iter()) {
            assert_eq!(i, item);
        }

        let mut l = List::from_iter(vec![0,4,7]);
        let mut m = l.pop_front();
        assert!(m.is_some());
        assert_eq!(m.unwrap().deref().deref(), &7);

        m = l.pop_front();
        assert_eq!(m.unwrap().deref().deref(), &4);

        m = l.pop_front();
        assert_eq!(m.unwrap().deref().deref(), &0);
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
        for i in 1..11 {
            let n = Node::new_boxed(Foo);
            l.push_front(n);
            assert_eq!(l.length(), i);
        }
        assert_eq!(DROPS.load(Ordering::SeqCst), 0);

        {
            let n = l.pop_front();
            assert!(n.is_some());
        }
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);
        assert_eq!((&l).into_iter().count(), 9);
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);

        drop(l);
        assert_eq!(DROPS.load(Ordering::SeqCst), 10);

        {
            let _ = Node::new_boxed(Foo);
        }
        assert_eq!(DROPS.load(Ordering::SeqCst), 11);
    }
}
