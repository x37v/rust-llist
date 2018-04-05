extern crate llist;

use llist::Node;
use llist::List;
use std::ops::Deref;

#[test]
fn can() {
    let n = Node::new_boxed(634);
    assert_eq!(&634, n.deref().deref());
    assert_eq!(&634, &**n);
    assert_eq!(634, **n);

    let mut l = List::new();
    assert_eq!(l.length(), 0);

    l.push_front(n);
    assert_eq!(l.length(), 1);
}
