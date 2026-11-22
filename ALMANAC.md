# Superpermutation Almanac submission

The same layout as Jay Pantone's batch (commit `882721e` of
[jaypantone/2026-10-superpermutation-asymptotics](https://github.com/jaypantone/2026-10-superpermutation-asymptotics)).
His released proof is in `lean/`; three of his files are changed (README.md lists them). `lean/Asym35/`,
`lean/Asym33/` and `lean/Asym29/` hold counts of my earlier batches, `lean/Asym25/` the aligned repairs and the
degree of the tied envelopes, and `lean/Asym22/` has the transversal
design in place of his control grid (with copies of his grid-dependent files in `lean/Asym22/TD/`), the collision
equations in local positions, which are new, and the chain for the new threshold. The files at the root are:

- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`, which make the root a Lake project that reads
  `lean/` as a library. Mathlib is pinned to the same commit as his release.
- `AlmanacDefs.lean`, `AlmanacStatement.lean` and `AlmanacChallenge.lean`, the Almanac's scaffold files
  (version 5). The judge writes its own copies over them. `AlmanacChallenge.lean` is a placeholder containing
  `sorry`; nothing imports it.
- `AlmanacAdapter.lean`, which proves the statement from `CoefficientTwoPrecision.Asym22.explicit_error_log20`,
  using his lemmas that `Covers` is the Almanac's `IsSuperpermutation` and that the Almanac's `fact` is
  `Nat.factorial`.
- `AlmanacSolution.lean`, which states the batch: `explicit_error_log20 : AlmanacAdapter.ExplicitErrorLog20`, a custom
  statement: for every `n >= 2904 * 10400^2 * 6^20 * 4^2`,
  `|S(n) - F3(n) - 2(n-4)!| <= 214 (n-4)! (ln n)^(1/10) n^(-1/20)`.

The record in `verification/almanac/` has the statements that NanoDa printed. The build, the axioms, Lean's
`leanchecker --fresh` and NanoDa (the toolchain's `nanoda_bin`, only `propext`, `Classical.choice` and
`Quot.sound` permitted) are described in README.md.
