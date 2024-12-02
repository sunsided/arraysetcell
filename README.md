# ArraySetCell

[![Crates.io](https://img.shields.io/crates/v/arraysetcell)](https://crates.io/crates/arraysetcell)
[![Crates.io](https://img.shields.io/crates/l/arraysetcell)](https://crates.io/crates/arraysetcell)
[![GitHub Workflow Status](https://img.shields.io/github/actions/workflow/status/sunsided/arraysetcell/rust.yml)](https://github.com/sunsided/arraysetcell/actions/workflows/rust.yml)
[![Safety Dance][safety-image]][safety-link]
[![docs.rs](https://img.shields.io/docsrs/arraysetcell)](https://docs.rs/arraysetcell/)
[![codecov](https://codecov.io/gh/sunsided/arraysetcell/graph/badge.svg?token=5VG5X1KZ8C)](https://codecov.io/gh/sunsided/arraysetcell)

A fixed-capacity, vector-like array with interior mutability and no ordering guarantees.

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

[safety-image]: https://img.shields.io/badge/unsafe-yes-yellow.svg

[safety-link]: https://github.com/rust-secure-code/safety-dance/
