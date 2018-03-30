use std::boxed::Box;

pub enum Link<T> {
    None,
    Some(Box<Node<T>>)
}

impl<T> Default for Link<T> {
    fn default() -> Self { Link::None }
}

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

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: Link::default() }
    }

    pub fn push_front(&mut self, mut node: Box<Node<T>>) -> () {
        std::mem::swap(&mut node.next, &mut self.head);
        self.head = Link::Some(node);
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

//XXX LOOK INTO THIS!!!
unsafe impl <T> Sync for Node<T> where T: Sync {}


#[cfg(test)]
use std::thread;

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
