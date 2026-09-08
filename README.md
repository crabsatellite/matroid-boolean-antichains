# Boolean Antichains in Finite Lattices: Product Formulas and Matroid Applications

This repository contains the paper and its Lean formalization. The paper is
available at [SSRN](https://doi.org/10.2139/ssrn.7378778) and in its
[Zenodo archive](https://doi.org/10.5281/zenodo.22168871).
It develops product formulas and matroid correspondences for the enumeration
of Boolean antichains, addressing questions in Garber--Goltermann--Horiatakis--Koenig--Gottesman,
*Counting Boolean antichains*, arXiv:2608.27126v1.

## Exact target

Classify and count Boolean antichains of every size in the lattice of flats of
a finite matroid.  Resolve the source paper's expected graphic bijection
without silently assuming connectivity, simplicity, or the absence of
parallel edges.

This answers Remark 4.5 of Garber--Goltermann--Horiatakis--Koenig--Gottesman
and the geometric/distributive/modular-lattice construction part of their
Question 6.1. The separate Tamari-recursion and lattice-congruence questions
in Question 6.1 are outside this paper's scope.

## Results

Maximum Boolean antichains are identified with bases of the simplification.
Retaining parallel-class multiplicities gives an exact decomposition of the
multivariate basis generating polynomial.  The construction is local to flat
intervals and matroid minors, and rank-tight Boolean antichains are classified
by contraction bases.  The source paper's graphic expectation follows as a
spanning-forest theorem, specializing to spanning trees for connected simple
graphs.

For an arbitrary size, the global height-gap theorem gives an exact `2^k`
certificate and finite enumerator in every finite lattice.  The enumerator
obeys an explicit positive convolution under lattice products and matroid
direct sums.  In geometric lattices the height gaps are rank gaps and the
face-rank profiles are strictly increasing integral polymatroids.  Uniform
matroids have an explicit all-size constrained block-partition formula;
rank-three matroids and all finite projective planes have complete
distributions.

The paper also classifies every two-element Boolean antichain in every finite
lattice, every Boolean antichain in every finite distributive lattice, and
every Boolean antichain in every finite subspace lattice.

## Evidence boundary

Finite enumeration is regression evidence only.  The general results have
complete human proofs in the manuscript and premise-free kernel-only Lean
producers.  The publication root, atomic declaration audit and reviewed formal
contract pass.  Proof Engine v2.5.27 records thirteen earned edges, fourteen
reachable claims and `target_closed=true`.

The exact regression entry point is
`research/verify_matroid_boolean_antichains.py`.

## Public artifacts

The paper's preferred scholarly citation is
[SSRN 7378778](https://doi.org/10.2139/ssrn.7378778). The first public
version was deposited on Zenodo on 30 August 2026; use the stable
[Concept DOI](https://doi.org/10.5281/zenodo.22168871) for the archive and its versions.

The current paper, Lean~4 source, theorem map, verification instructions, and
finite regression scripts are published at
[`crabsatellite/matroid-boolean-antichains`](https://github.com/crabsatellite/matroid-boolean-antichains).
The public paper record retains the same Concept DOI across versions. Earlier
versions remain immutable historical records; the Concept DOI is the stable
outward-facing archive link.
