use std::cell::RefCell;
use std::sync::Arc;
use std::thread;

pub enum Link<T> {
    None,
    Some(Arc<Node<T>>)
}

impl<T> Clone for Link<T> {
    fn clone(&self) -> Self {
        match self {
            &Link::None => Link::None,
            &Link::Some(ref item) => Link::Some(item.clone())
        }
    }
}

pub struct Node<T> {
    next: RefCell<Link<T>>,
    value: T
}

pub struct List<T> {
    head: Link<T>
}

impl<T> Node<T> {
    fn new(v: T) -> Arc<Self> {
        Arc::new(Node { next: RefCell::new(Link::None), value: v })
    }
}

unsafe impl <T> Sync for Node<T> where T: Sync {}

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: Link::None }
    }

    pub fn push_front(&mut self, node: Arc<Node<T>>) -> () {
        *node.next.borrow_mut() = self.head.clone();
        self.head = Link::Some(node);
    }

    pub fn length(&self) -> usize {
        let mut cur = self.head.clone();
        let mut cnt: usize = 0;
        while let Link::Some(node) = cur {
            cur = node.next.borrow().clone();
            cnt += 1;
        }

        cnt
    }
}


#[cfg(test)]

mod tests {
    use super::*;

    #[test]
    fn it_builds() {
        let mut n = Node::new(23);
        let mut l = List::new();
        l.push_front(n);
        assert_eq!(l.length(), 1);

        n = Node::new(345);
        l.push_front(n);
        assert_eq!(l.length(), 2);

        let mut c = Node::new(35);
        let child = thread::spawn(move || {
            assert_eq!(l.length(), 2);
            l.push_front(c);
            assert_eq!(l.length(), 3);
            let mut x = Node::new(45);
            l.push_front(x);
            assert_eq!(l.length(), 4);
        });
        child.join();
    }
}
