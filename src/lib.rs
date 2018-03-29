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

//XXX LOOK INTO THIS!!!
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

        /*
        let n = Node::new(1);
        let cl = n.clone(); //ERROR

        l.push_front(n);
        len = len + 1;
        assert_eq!(l.length(), len);

        l.push_front(cl);
        len = len + 1;
        assert_eq!(l.length(), len);
        */

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
}
