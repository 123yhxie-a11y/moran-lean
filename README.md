# Spectral Moran Salem sets in Lean

This project formalizes the main existence theorem for homogeneous Moran sets
with spectral Cantor–Moran measures and prescribed Fourier and Hausdorff dimensions.

## Scope

The proof source is `BanLat/Moran.lean`. Its final declarations are:

- `Moran.exists_moran_measure`: for every real `s` with `0 < s ≤ 1`, there is a
  homogeneous Moran construction whose measure is spectral, whose Fourier
  dimension is `s`, and whose carrier has Hausdorff dimension `s`.
- `Moran.exists_salem_moran_set`: for every such `s`, there is a homogeneous
  Moran Salem set of Hausdorff dimension `s`.

The formal development reorganizes intermediate arguments. It does not claim
that every numbered result of the accompanying manuscript has been formalized
at its original level of generality.

## Reproduce the verification

Install the Lean toolchain manager [elan](https://github.com/leanprover/elan),
then open a terminal in this directory and run:

```sh
lake exe cache get
lake build
```

The root module `BanLat.lean` imports `BanLat.Moran`, so the default build
includes the complete proof file. To build that module explicitly, run:

```sh
lake build BanLat.Moran
```

An internet connection is needed for the initial toolchain and dependency
downloads. Keep the supplied version files together:

- `lean-toolchain`: Lean `v4.32.1`.
- `lakefile.toml`: project configuration and Mathlib dependency.
- `lake-manifest.json`: exact dependency revisions; Mathlib is pinned to
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.

The Lake package name remains `banLat`; the GitHub repository may have any name.
The proof file imports only Mathlib and does not require other BanLat modules.

## License

This distribution retains the Apache License 2.0 from the source project.
See `LICENSE`.
