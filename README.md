# Boolean Antichains in Finite Lattices: A Height-Gap Classification with Matroid Applications

This is the canonical internal project for the geometric-lattice extension
suggested in Garber--Goltermann--Horiatakis--Koenig--Gottesman,
*Counting Boolean antichains*, arXiv:2608.27126v1.

## Exact target

Classify and count Boolean antichains of every size in the lattice of flats of
a finite matroid.  Resolve the source paper's expected graphic bijection
without silently assuming connectivity, simplicity, or the absence of
parallel edges.

## Candidate strengthening

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

The first public version was deposited on Zenodo on 30 August 2026.  Cite the
stable Concept DOI
[`10.5281/zenodo.22168871`](https://doi.org/10.5281/zenodo.22168871).

The current paper, Lean~4 source, theorem map, verification instructions, and
finite regression scripts are published at
[`crabsatellite/matroid-boolean-antichains`](https://github.com/crabsatellite/matroid-boolean-antichains).
The public paper record retains the same Concept DOI across versions. Earlier
versions remain immutable historical records; the Concept DOI is the stable
outward-facing citation.
