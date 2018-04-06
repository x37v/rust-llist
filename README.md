# llist

I wanted a linked list where the nodes were pre-allocated so that I can control allocation.
The eventual use of this will be to allocate nodes in one thread, send them to another and append them to a list in that other thread.

A work in progress still.
