extern crate xnor_llist;

use xnor_llist::Node;
use xnor_llist::List;
use std::ops::Deref;

#[test]
fn can() {
    let n = Node::new_boxed(634);
    assert_eq!(&634, n.deref().deref());
    assert_eq!(&634, &**n);
    assert_eq!(634, **n);

    let mut l = List::new();
    l.push_front(n);

    assert_eq!(l.iter().count(), 1);
}
