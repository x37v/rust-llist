# xnor_llist

I wanted a linked list where the nodes were pre-allocated so that I can control allocation.
The eventual use of this will be to allocate nodes in one thread, send them to another and append them to a list in that other thread.

## Acknowledgments

Based on examples Copyright (c) 2015 Alexis Beingessner, [Learning Rust With Entirely Too Many Linked Lists](http://cglab.ca/~abeinges/blah/too-many-lists/book/) [github](https://github.com/rust-unofficial/too-many-lists)

## [Thanks for the help:](https://users.rust-lang.org/t/yet-another-linked-list-insert/16783)

  * [Vitaly Davidovich](https://users.rust-lang.org/u/vitalyd)
  * [Ivan Nejgebauer](https://users.rust-lang.org/u/inejge)
