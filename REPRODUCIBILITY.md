# Reproducibility

## Exact finite replay

```powershell
python research\verify_matroid_boolean_antichains.py
```

The script independently constructs flat lattices from rank oracles and
checks the literal Boolean-antichain identity, both inverse maps, weighted
basis evaluations, all rank-tight interval consumers, the closed Boolean,
partition, and uniform formulas, and the negative boundaries.  It compares
the global `2^k` height-gap criterion against the literal `4^k` meet-map
definition on the non-graded pentagon, modular diamond, lattice products, and
every candidate family in the registered matroid examples.  It also replays
the exact product convolution, the unrestricted uniform formula on five
parameter pairs, and the finite-projective-plane formula on the Fano plane. Examples
include uniform, binary, Fano, connected graphic, disconnected graphic,
looped, and parallel matroids.  It also replays the universal size-two Möbius
formula and the Bell-square partition-lattice formula.
The full distributive classification is replayed on antichain, chain, and
branched posets, while the direct-sum formula is replayed on all subspace
lattices over `F_2` through dimension three.

## Kernel-only formalization

```powershell
python scripts\verify_lean_target.py BooleanAntichainsKernel.PublicationRoot lean4/BooleanAntichainsKernel/PublicationAxiomAudit.lean
python scripts\verify_lean_target.py BooleanAntichainsKernel.AtomicPaperClaimBindings lean4/BooleanAntichainsKernel/AtomicPaperClaimAxiomAudit.lean
```

The first command builds the exact publication root and then runs Lean with
`--trust=0` over the forty-one publication declarations. The second audits the
forty-nine atomic paper bindings. Both commands reject project axioms, proof
escapes, duplicate endpoint lines, and any axiom beyond `propext`,
`Classical.choice`, and `Quot.sound`.

`THEOREM_MAP.md` records the paper-facing grouping, while
`lean4/formal-contract.json` gives the machine-readable mapping for all 105
formal, scope, and proof/restatement occurrences. The conditional
`ProofEngineGraphInterface` is an orchestration interface only and is not
imported by `PublicationRoot`.

## Paper

```powershell
.\paper\build.ps1
```

This builds the public English manuscript from `paper/matroid_boolean_antichains.tex`
and `paper/references.bib`. The released PDF is also available under the stable
paper Concept DOI below.

## Public source

The canonical public repository is
[`crabsatellite/matroid-boolean-antichains`](https://github.com/crabsatellite/matroid-boolean-antichains).
It contains the manuscript source, Lean~4 development, theorem map, exact
verification entry point, and finite regression script. The stable paper
Concept DOI is `10.5281/zenodo.22168871`.

The complete Cayley dependency is adapted from
[Brockian/Cayley.lean at the pinned source commit](https://github.com/primaryhosting/brockian-mathematics/blob/313243c3c37ad150109cb057a062a72d73b4c260/Brockian/Cayley.lean),
Copyright (c) 2026 Christopher Brock, MIT License. Its source blob is
`111a5bdcd71501e5a207ed3a6fef7c26a64e6a3d`. The full license appears in
each of the six cache modules: CayleyForestReachability, CayleyForestCut,
CayleyForestCount, CayleyTreeParents, CayleyParentGraphs and CayleyFormula.
The rooted-forest proof route and actual SimpleGraph.IsTree statement are
retained. Adaptations are bounded imports, cache partitioning, current
`push Not` syntax and the explicit natural-number `Nat.nsmul_eq_mul`
identity. Each cache was locally kernel-checked; the complete consumer is
also audited through the publication root.

CompleteGraphTreeSupport, CompleteTreeCarriers and CompleteGraphCayley
prove the exact transport to the manuscript's original-edge spanning-tree
carrier before the value is used in PartitionStirlingCayley.

The audit parser now recognizes ordinary Lean identifiers ending in
apostrophes and rejects unsupported or duplicate endpoint lines. The
primed Cayley endpoint was tested by a real trust-zero audit; negative
parser tests confirmed rejection before any Lean command executes.
