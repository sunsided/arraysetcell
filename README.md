# ArraySetCell

A fixed-capacity, vector-like array with interior mutability and no ordering guarantees.

⚠️ This crate uses a lot of unsafe code to get around initialization and reassignment concerns.
The behavior is not rigidly tested yet and some edge cases may cause undefined behavior. Use at your own risk.

```rust
use std::cell::Cell;
use arraysetcell::ArraySetCell;

fn it_works() {
    let mut array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    assert_eq!(array.capacity(), 3);
    assert_eq!(array.len(), 2);

    array.push(10);
    assert_eq!(array.len(), 3);

    array.retain(|x| *x < 10);
    assert_eq!(array.len(), 2);

    let result = array.filter_mut(|x| if *x > 2 { Some(*x) } else { None });
    assert_eq!(result, Some(3));

    let mut iter = array.into_iter();
    assert_eq!(iter.size_hint(), (2, Some(2)));
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.next(), Some(3));
    assert_eq!(iter.next(), None);
}
```
