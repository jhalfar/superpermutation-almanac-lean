# Results

This repository holds my Lean batches for the [Superpermutation Almanac](https://superpermutations.com). Each batch is
one commit that replaces the files of the one before. Every batch listed on the Almanac has a tag with its batch id, so
`git checkout L-0020` gives the files of that proof. The table shows each result as it stands on the Almanac.

| Result | Almanac | Tag | Commit | Check | Build (time / peak memory) |
|---|---|---|---|---|---|
| S(6) ≥ 872 | [b/37](https://superpermutations.com/b/37) | [`L-0018`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0018) | [`7b7b96d`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/7b7b96d) | kernel | 1229 s / 10.1 GB |
| S(7) ≥ 5,898 (superseded) | [b/43](https://superpermutations.com/b/43) | [`L-0023`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0023) | [`5cc0ac3`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/5cc0ac3) | kernel | 3153 s / 17.6 GB |
| S(7) ≥ 5,899 | [b/40](https://superpermutations.com/b/40) | [`L-0020`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0020) | [`a09f9ef`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/a09f9ef) | native_decide, 12 searches | 876 s / 19.8 GB (native_decide re-run 288 s) |
| S(7) ≥ 5,899, kernel only | – | – | [`0734844`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/0734844) | kernel only | – |
| S(7) ≥ 5,900 | – | – | [`956ad6c`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/956ad6c) | native_decide, 89 searches | – |
| S(8) ≥ 46,134 | [b/39](https://superpermutations.com/b/39) | [`L-0017`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0017) | [`7e6664d`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/7e6664d) | native_decide, 3 searches | 3471 s / 8.2 GB (native_decide re-run 3022 s) |
| S(12) ≥ 522,622,401 (superseded) | [b/46](https://superpermutations.com/b/46) | [`L-0025`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0025) | [`7ed009a`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/7ed009a) | kernel | 2226 s / 9.7 GB |
| S(13) ≥ 6,746,627,048 (superseded) | [b/47](https://superpermutations.com/b/47) | [`L-0025`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0025) | [`7ed009a`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/7ed009a) | kernel | 2226 s / 9.7 GB |
| S(n) ≤ n!+(n-1)!+(n-2)!+(0+ε)(n-3)!, large n | [b/35](https://superpermutations.com/b/35) | [`L-0016`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0016) | [`af99e83`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/af99e83) | kernel | 251 s / 3.8 GB |
| S(n) ≤ n!+(n-1)!+(n-2)!+(8+ε)(n-4)!, large n | [b/36](https://superpermutations.com/b/36) | [`L-0016`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0016) | [`af99e83`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/af99e83) | kernel | 251 s / 3.8 GB |
| Error after 2(n-4)!: at most 306 (n-4)! n^(-1/37) | [b/48](https://superpermutations.com/b/48) | [`L-0026`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0026) | [`ad9477f`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/ad9477f) | kernel, statement reviewed | 679 s / 5.1 GB |
| Error after 2(n-4)!: at most 148 (n-4)! (ln n)^(3/32) n^(-1/32) | [b/49](https://superpermutations.com/b/49) | [`L-0031`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0031) | [`dd5dec1`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/dd5dec1) | kernel, statement reviewed | 648 s / 5.2 GB |
| Error after 2(n-4)!: at most 183 (n-4)! (ln n)^(3/29) n^(-1/29) | [b/50](https://superpermutations.com/b/50) | [`L-0032`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0032) | [`8ab3685`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/8ab3685) | kernel, statement reviewed | 647 s / 5.5 GB |
| Error after 2(n-4)!: at most 214 (n-4)! (ln n)^(1/10) n^(-1/20) | [b/51](https://superpermutations.com/b/51) | [`L-0033`](https://github.com/jhalfar/superpermutation-almanac-lean/tree/L-0033) | [`4392df9`](https://github.com/jhalfar/superpermutation-almanac-lean/commit/4392df9) | kernel, statement reviewed | 598 s / 5.8 GB |

Notes.

- "Superseded" is the Almanac's label: a stronger bound was listed afterwards.
- Rows without an Almanac link are proofs in this repository that have no Almanac page; the commit holds the files.
- Commit `e5c5a22` (exponent 1/28) I did not submit. It has no tag.
- My earlier Lean proofs, the general lower bound and the 1771/3456 upper bound among them, are in
  [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations/tree/cc5c763bd5854317b20dadb138990802656e6f03/proofs/lean).
