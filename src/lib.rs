use std::boxed::Box;
use std::ops::Deref;

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
    head: Link<T>
}

impl<T> Node<T> {
    fn new(v: T) -> Box<Self> {
        Box::new(Node { next: Link::default(), value: v })
    }
}

impl<T> Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: Link::default() }
    }

    pub fn push_front(&mut self, mut node: Box<Node<T>>) -> () {
        std::mem::swap(&mut node.next, &mut self.head);
        self.head = Link::Some(node);
    }
    
    pub fn pop_front(&mut self) -> Option<Box<Node<T>>> {
        let mut ret = Link::None;
        std::mem::swap(&mut ret, &mut self.head);
        match ret {
            Link::Some(mut node) => {
                std::mem::swap(&mut node.next, &mut self.head);
                Some(node)
            },
            Link::None => None
        }
    }

    pub fn length(&self) -> usize {
        let mut cur = &self.head;
        let mut cnt: usize = 0;
        while let &Link::Some(ref node) = cur {
            cur = &node.next;
            cnt += 1;
        }
        cnt
    }
}

unsafe impl <T> Send for Node<T> where T: Send {}


#[cfg(test)]
mod tests {
    use std::thread;
    use super::*;

    #[test]
    fn can_push() {
        let mut len: usize = 0;
        let n = Node::new(23);

        assert_eq!(n.value, 23);
        let mut l = List::new();
        assert_eq!(l.length(), len);

        l.push_front(n);
        len = len + 1;
        assert_eq!(l.length(), len);

        let n = Node::new(345);
        assert_eq!(n.value, 345);
        l.push_front(n);
        len = len + 1;
        assert_eq!(l.length(), len);

        let c = Node::new(35);
        let child = thread::spawn(move || {
            assert_eq!(l.length(), len);

            l.push_front(c);
            len = len + 1;
            assert_eq!(l.length(), len);

            let x = Node::new(45);
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
        let n = Node::new(23);

        assert_eq!(n.value, 23);
        let mut l = List::new();
        assert_eq!(l.length(), len);

        let c = Node::new(35);
        let child = thread::spawn(move || {
            assert_eq!(l.length(), len);

            l.push_front(c);
            len = len + 1;
            assert_eq!(l.length(), len);

            let x = Node::new(45);
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
        let x = Node::new(634);
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
            let x = Node::new(i);
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

        l.push_front(Node::new(42));
        assert_eq!(l.length(), 1);
        l.push_front(Node::new(2084));
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
}
