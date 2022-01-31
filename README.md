# linotype

[![Lib.rs](https://img.shields.io/badge/Lib.rs-*-84f)](https://lib.rs/crates/linotype)
[![Crates.io](https://img.shields.io/crates/v/linotype)](https://crates.io/crates/linotype)
[![Docs.rs](https://docs.rs/linotype/badge.svg)](https://docs.rs/linotype)

![Rust 1.56](https://img.shields.io/static/v1?logo=Rust&label=&message=1.56&color=grey)
[![CI](https://github.com/Tamschi/linotype/workflows/CI/badge.svg?branch=develop)](https://github.com/Tamschi/linotype/actions?query=workflow%3ACI+branch%3Adevelop)
![Crates.io - License](https://img.shields.io/crates/l/linotype/0.0.1)

[![GitHub](https://img.shields.io/static/v1?logo=GitHub&label=&message=%20&color=grey)](https://github.com/Tamschi/linotype)
[![open issues](https://img.shields.io/github/issues-raw/Tamschi/linotype)](https://github.com/Tamschi/linotype/issues)
[![open pull requests](https://img.shields.io/github/issues-pr-raw/Tamschi/linotype)](https://github.com/Tamschi/linotype/pulls)
[![good first issues](https://img.shields.io/github/issues-raw/Tamschi/linotype/good%20first%20issue?label=good+first+issues)](https://github.com/Tamschi/linotype/contribute)

[![crev reviews](https://web.crev.dev/rust-reviews/badge/crev_count/linotype.svg)](https://web.crev.dev/rust-reviews/crate/linotype/)
[![Zulip Chat](https://img.shields.io/endpoint?label=chat&url=https%3A%2F%2Fiteration-square-automation.schichler.dev%2F.netlify%2Ffunctions%2Fstream_subscribers_shield%3Fstream%3Dproject%252Flinotype)](https://iteration-square.schichler.dev/#narrow/stream/project.2Flinotype)

A keyed sequence reprojector that can optionally pin its values.

It can act as list state reconciliator for data-driven GUIs.

More generally speaking, this library can be used to manage item-associated state of a changing sequence.

## Audience

This crate is optimised for flexible use (requiring only [`Eq`](https://doc.rust-lang.org/stable/std/cmp/trait.Eq.html) for keys, with automatic key cache and flexible lifetimes) and relatively low entry counts.

If you're looking to reconcile associated states for a list with many items,
especially with large changes to the list between reprojections, a different
approach may be more appropriate.

## Installation

Please use [cargo-edit](https://crates.io/crates/cargo-edit) to always add the latest version of this library:

```cmd
cargo add linotype --features std
```

## Features

(See [documentation](https://docs.rs/linotype/0.0.1/#features) for more details.)

### `"std"`

Avoids aborting the process if the drop implementation of a key or value inside a pinning [`OwnedProjection`] panics.

## Example

```rust
use linotype::OwnedProjection;

// This is tricky to write as closure except directly as parameter.
// See the `higher-order-closure` crate in the dependencies for a workaround.
fn selector<'a>(item: &'a mut &'static str) -> &'a str {
  item
}

let mut counter = (0..).into_iter();
let mut factory = move |_item: &mut _, _k: &_| {
  counter.next().unwrap()
};

// Inferred to store `String` keys (`K`) and `{integer}` values (`V`).
let mut linotype = OwnedProjection::new();
let mut reproject = |iter: &[&'static str]| linotype
  .reproject_by_with(
    iter.into_iter().copied(), // : IntoIter<Item = T>, here: T = &'static str
    selector,                 // : FnMut(&mut T) -> &Q,
    &mut factory,            // : FnMut(&mut T, &K) -> V,
  )
  .map(|(_item, value)| *value)
  .collect::<Vec<_>>();   // Left-over values are dropped here. Their slots are recycled.

assert_eq!(reproject(&["a", "b", "c"]), vec![0, 1, 2]);
assert_eq!(reproject(&["a", "b", "c", "d"]), vec![0, 1, 2, 3]);
assert_eq!(reproject(&["a", "b", "c"]), vec![0, 1, 2]);
assert_eq!(reproject(&["a", "b", "c", "d"]), vec![0, 1, 2, 4]);
assert_eq!(reproject(&["e", "c", "b", "a"]), vec![5, 2, 1, 0]);

// Reprojection methods for fallible closures and per-item closures are also available.
```

## License

Licensed under either of

- Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license
   ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

See [CONTRIBUTING](CONTRIBUTING.md) for more information.

## [Code of Conduct](CODE_OF_CONDUCT.md)

## [Changelog](CHANGELOG.md)

## Versioning

`linotype` strictly follows [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html) with the following exceptions:

- The minor version will not reset to 0 on major version changes (except for v1).  
Consider it the global feature level.
- The patch version will not reset to 0 on major or minor version changes (except for v0.1 and v1).  
Consider it the global patch level.

This includes the Rust version requirement specified above.  
Earlier Rust versions may be compatible, but this can change with minor or patch releases.

Which versions are affected by features and patches can be determined from the respective headings in [CHANGELOG.md](CHANGELOG.md).

Note that dependencies of this crate may have a more lenient MSRV policy!
Please use `cargo +nightly update -Z minimal-versions` in your automation if you don't generate Cargo.lock manually (or as necessary) and require support for a compiler older than current stable.
