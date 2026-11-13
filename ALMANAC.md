# Superpermutation Almanac submission

The same layout as Jay Pantone's batch (commit `882721e` of
[jaypantone/2026-10-superpermutation-asymptotics](https://github.com/jaypantone/2026-10-superpermutation-asymptotics)).
His released proof in `lean/` is unchanged; `lean/Asym37/` is new (see README.md). The files at the root are:

- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`, which make the root a Lake project that reads
  `lean/` as a library. Mathlib is pinned to the same commit as his release.
- `AlmanacDefs.lean`, `AlmanacStatement.lean` and `AlmanacChallenge.lean`, the Almanac's scaffold files
  (version 5). The judge writes its own copies over them. `AlmanacChallenge.lean` is a placeholder containing
  `sorry`; nothing imports it.
- `AlmanacAdapter.lean`, which proves the statement from `CoefficientTwoPrecision.Asym37.explicit_error_37`,
  using his lemmas that `Covers` is the Almanac's `IsSuperpermutation` and that the Almanac's `fact` is
  `Nat.factorial`.
- `AlmanacSolution.lean`, which states the batch: `explicit_error_37 : AlmanacAdapter.ExplicitError37`, a custom
  statement: for every `n >= 5920 * 352^3 * 6^37`, `|S(n) - F3(n) - 2(n-4)!| <= 306 (n-4)! n^(-1/37)`.

The record in `verification/almanac/` has the statements that NanoDa printed. The build, the axioms, Lean's
`leanchecker --fresh` and NanoDa (the toolchain's `nanoda_bin`, only `propext`, `Classical.choice` and
`Quot.sound` permitted) are described in README.md.
