# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83`, the second (a lower bound for 8 symbols) is commit `7e6664d`, the
third (872 for 6 symbols, checked by the kernel) is commit `7b7b96d`, the fourth (5,899 for 7 symbols with
`native_decide`) is commit `a09f9ef`, the fifth (5,898 for 7 symbols, checked by the kernel) is commit
`5cc0ac3`, the sixth (12 and 13 symbols from Theorem C) is commit `7ed009a`, the seventh (the error after
$`2(n-4)!`$ with exponent 1/37) is commit `ad9477f` and the eighth (5,900 for 7 symbols with `native_decide`) is
commit `956ad6c`. This commit holds the ninth.

## This batch: 5,899 for 7 symbols, checked by the kernel

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one result:

| statement | meaning |
|---|---|
| `Almanac.LowerBoundAt 7 5899` | every superpermutation on 7 symbols has length at least 5,899 |

The bound and its proof are those of my fourth batch: the model of standard configurations, the accounting at
cost 134 and twelve finite searches (F0 to F5 for sequences of rows, FR for rings, and the five profile searches
FF0 to FF4). In the fourth batch `native_decide` evaluated the twelve searches. Here the kernel evaluates all of
them (`decide +kernel`), so `AlmanacSubmission.lower_seven` depends only on `propext`, `Classical.choice` and
`Quot.sound`.

The kernel is far slower than compiled code: `native_decide` does the search F0 in about 95 seconds, and the
kernel needs about 1,400 CPU-hours for it. So I could not just hand the searches to the kernel as they are. The
new directory [`Cert/`](Cert/) holds what it evaluates instead:

| part | what | files in `Cert/` |
|---|---|---|
| engines | the searches of `K16Search.lean` (F0 to F5) and `PSearch.lean` (FR, FF) written for the kernel: the marks are one number, the successors of a word and the blocks of their rows come from one record per word, every loop is `Nat.rec`, and the potentials are natural numbers shifted by $`2^{18}`$; a search can skip the prefixes of a list | `KEngine`, `KEngineN`, `OkN`, `PEngine`, `ChildN` |
| soundness | if the kernel search does not find, the statement of the written proof holds: `kstmt16_of_searchC` (F0 to F5, through `KStmt16` of `K16Sound.lean`) and `pstmt_of_psearchC` (FR, FF, `PS.PStmt`); the engine with natural potentials is the same search (`goNat_eq`); and a search cut at a list of prefixes, with every prefix of the list searched on its own, is the whole search (`goC_cut`, `pgoC_cut`) | `KComplete`, `KEquiv`, `Cut`, `PComplete`, `PStmtC`, `PCut`, `Assemble`, `AssembleN` |
| tables | the word records and the rule records as numbers; the kernel checks that they are what the definitions of `PSearch.lean` and `KSearch.lean` give (every word, every rule record of each search, the ring tables, the caps) | `W`, `WO`, `R_F0` .. `R_F5`, `RingT`, `Cap0`, `WDefs`, `RDefs`, `WC/`, `WOC/`, `RC/`, `RingC/`, `WSpec`, `RSpec`, `RingSpec`, `Cap`, `WCheck` |
| evaluated lemmas | each search cut into 595,177 lemmas of at most 20,000 visited prefixes (26,000 for one profile): a lemma for a subtree (`g...`), a lemma for a part of the tree above together with the list of the subtrees below it (`x...`), and the top (`top`); a prefix is named by its path from the prefix above it | `F0/` .. `F5/`, `FR/`, `FF0/` .. `FF4/`: `S*` the names, `M*` the lemmas (50 per module), `Comb` puts them together |
| assembly | the six caps, the ring cap and the five profiles, and the theorem `covers_lower_bound_7_kernel` | `F0Final` .. `F5Final`, `FRFinal`, `FFFinal`, `Final5899` |

C copies of the searches chose the cutting: they count the visited prefixes below every prefix. Nothing about
the cutting has to be trusted. A lemma names its prefix and its list, and if a name were wrong the kernel would
refuse that lemma.

[`LowerLinks.lean`](LowerLinks.lean) holds the linking lemma, as in the fourth batch: the covering predicate of
the proof (`SuperpermutationBounds.Covers` from Jay Pantone's `Challenge.lean`) is `Almanac.IsSuperpermutation`
over `List (Fin 7)`, and the template statement then follows from
`SuperpermLowerBounds.covers_lower_bound_7_kernel`. The other files are those of the fourth batch, without the
six `native_decide` files, `LowerBounds/PFinalK16.lean`, `K6/` and `tools/`.

## Cost

Nearly all of the work is in the 11,909 modules `Cert/*/M*.lean`. I measured the kernel's cost per visited
prefix on real modules, one Lean process each (Windows, Lean 4.35.0, beside other jobs at idle priority). For
F0, F1, F4 and FR this is the wall time of one whole module of 50 lemmas, for F2 the CPU time of a file of 10
lemmas:

| search | visited prefixes | modules | kernel time per visit (measured on) | memory of one process | CPU-hours |
|---|---|---|---|---|---|
| F0 | 4,120,526,064 | 5,340 | 1.19 ms (`Cert.F0.M100`, 783,357 visits: 930 s) | 2.5 GB | 1,362 |
| F1 | 1,508,386,528 | 1,966 | 1.39 ms (`Cert.F1.M100`, 763,938 visits: 1,060 s) | 3.2 GB | 582 |
| F2, F3 | 345,729,607 and 175,518,625 | 449 and 229 | 2.10 ms on F2 (10 lemmas, 131,204 visits: 275 s) | 4.6 GB | about 300 |
| F4, F5 | 1,073,801 and 67,906 | 2 and 1 | 3.0 ms (both built in full; `Cert.F4.M0`, 790,681 visits: 2,375 s) | 5.8 GB | 1 |
| FR | 2,825,190,014 | 3,707 | 0.50 ms (`Cert.FR.M100`, 781,251 visits: 390 s) | 1.5 GB | 392 |
| FF0 .. FF4 | 5,403,847 | 215 | as FR | | about 1 |

In all that is about 2,600 CPU-hours: about 85 hours with 32 processes at once, or 14 days with 8. A module of
50 lemmas takes 6 to 40 minutes. The kernel frees its memory after each lemma, so a process needs 1.5 to 6 GB,
depending on the search and on its largest lemma.

The rest is small. The table checks take about two CPU-hours. The modules after the evaluated ones (the `Comb`
modules, the assembly and `AlmanacSolution`) take about 35 minutes together. The largest of them is
`Cert.F0.Comb`: 15 minutes and about 15 GB in one process. This batch is meant to be built by hand.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`.

`lake build` starts every module that is ready at once, and there are 11,909 evaluated modules. So build them
first with [`build_parts.sh`](build_parts.sh), which gives Lake `N` of them at a time:

```
lake exe cache get
sh build_parts.sh 8          # 8 Lean processes at a time: up to 48 GB of memory
lake build AlmanacSolution   # the table checks, the assembly and the theorem
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_seven\n' > Axioms.lean
lake env lean Axioms.lean
```

Choose `N` as the free memory divided by 6 GB, and at most the number of cores. A run that is stopped can be
started again with the same command: Lake keeps the modules that are done. The names of F0 are 14 modules that
build one after another (half a minute to two and a half minutes each) before the first module of F0 can
start; FR has 10 of them, about 25 seconds each.

The evaluated modules do not depend on each other (a module `M*` imports only the names of its search), so any
set of them can be built anywhere and in any order:

* `sh build_parts.sh N K I` on machine `I` (`I` from 0 to `K - 1`) builds every `K`-th module from the `I`-th on.
  `K` machines with `I = 0, ..., K - 1` build all of them.
* `sh build_parts.sh N -f LIST` builds the modules named in the file `LIST`, one per line, as `Cert.F0.M12`.
  `find Cert -name 'M*.lean' | sort` lists all of them.

To put the results together, copy the directories `.lake/build/lib/lean/Cert/` and `.lake/build/ir/Cert/` of
every machine into one checkout, and run `lake build AlmanacSolution` there. The files of different machines
overlap only in the modules that every machine builds first, and those are the same. Lake takes the modules
that are already built and builds only the rest. All machines need the same commit, the same Lean and the same
Mathlib. I tried this on one machine only: I deleted the build files of F5 and copied them back, and I copied
them into a copy of the project at another path. Both times Lake took the copied modules and built none of them
again.

Besides the table above, I measured these:

| step | result |
|---|---|
| F5 and the profile FF0 built in full (lemmas, `Comb`, F5's rule records and `capF5`) | F5: 3 minutes for its module, 10 s for `capF5`; FF0: 6 modules of 8 s to 4 minutes |
| everything else, with the 595,177 evaluated lemmas replaced by assumptions (a test copy) | all of it compiles up to `AlmanacSolution`; `lower_seven` then depends on exactly those 595,177 assumptions and the three axioms |
| 50 modules of 10 lemmas of F0 (4,225,802 visits), 5 at a time beside other jobs | 40 minutes on 5 CPUs, at most 2.5 GB each |
| `lake env leanchecker --fresh` on one module of 10 lemmas of F0 | 266 s, 3.7 GB |

## Sources and licences

The project includes Lean files from [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations)
(commit `64ab6a7`), from the Hunter-Raudvere library
[superpermutations-hunter](https://github.com/urdvr/superpermutations-hunter) (commit `d452221`) and from Jay
Pantone's [superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80) (commit `c8fb7ff`), all
under the Apache License 2.0, and from Xiaolong Liu's
[superpermutations-preimage-chain-lower-bounds](https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds)
(commit `8474c74`), under CC BY 4.0. The licence texts are in [`licenses/`](licenses/). Each changed file says
at its top what changed. The fixes for Lean 4.35.0 follow the compatibility changes in Pantone's release "A
polynomial error estimate for superpermutation length". [`NOTICE`](NOTICE) has the details, and
[`SOURCES.tsv`](SOURCES.tsv) gives the SHA-256 of the original of every copied file. `AlmanacDefs.lean`,
`AlmanacStatement.lean` and `AlmanacChallenge.lean` are the Almanac's files, unchanged.
