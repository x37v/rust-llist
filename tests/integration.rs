extern crate xnor_llist;

use xnor_llist::Node;
use xnor_llist::List;
use std::ops::Deref;

#[test]
fn can() {
    let mut n = Node::new_boxed(634);
    assert_eq!(&634, n.deref().deref());
    assert_eq!(&634, &**n);
    assert_eq!(634, **n);

    **n = 23;

    let mut l = List::new();
    l.push_front(n);

    assert_eq!(l.iter().count(), 1);
    assert_eq!(l.peek_front(), Some(&23));
}
