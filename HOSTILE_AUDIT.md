# Hostile mathematical audit — 30 August 2026

This audit treats the manuscript as a human proof.  Finite replay does not
prove a uniform matroid theorem, while absent formalization does not itself
make the human argument false.

## Literal definition and rank carrier

- The manuscript uses the source definition: the meet map from subsets of
  the antichain is an anti-isomorphism onto the generated span, with the empty
  meet equal to the ambient top.
- For `r` Boolean generators, a Boolean maximal chain has exactly `r` strict
  steps.  In a rank-`r` flat lattice these steps exhaust the entire rank
  budget, forcing bottom rank zero and unit rank jumps.
- Rank zero identifies the loop flat, not the empty set when loops exist.

Result: full-height rigidity passes, including the rank-one case.

## Maximum-antichain bijection

- The Boolean atoms are `meet_(j != i) H_j`, whereas the given antichain
  consists of the Boolean coatoms.  The proof does not confuse these two
  families.
- Full-height rigidity makes those atoms rank-one ambient flats.  Their join
  is the ambient top, so they are a basis of the simplification.
- In the reverse direction, matroid submodularity proves
  `cl(B_S) meet cl(B_T)=cl(B_(S intersect T))`; mere injectivity of the join
  map would not have been enough.
- Atoms and coatoms recover one another, so the maps are inverse rather than
  only surjective constructions.

Result: the maximum bijection passes.

## Parallel classes and weights

- A basis contains no loop and at most one representative from each parallel
  class.
- A simplified basis permits every independent choice of one representative
  from each of its rank-one flats.  Expanding the product of class-linear
  forms therefore counts each original basis exactly once.
- The two-parallel-pairs example has one flat-lattice antichain but four
  original bases, proving that simplification and weights are necessary.

Result: the multivariate basis-polynomial identity passes.

## Intervals and rank-tightness

- For flats `X<=Y`, the manuscript uses the literal minor `(M|Y)/X`; its
  ground set is `Y-X`, and the rank formula directly identifies its flats
  with the interval.
- A size-`k` Boolean antichain is maximum in its bottom interval exactly when
  the bottom has rank `r-k`.  This is the rank-tight condition, not a claim
  about every size-`k` antichain.
- The two disjoint rank-two flats of `U(3,4)` give an exact non-tight
  counterexample and retire the unrestricted contraction-basis route.

Result: the interval and rank-tight classification passes with a sharp scope.

## Global height-gap classification

- For every ordered tuple, the atom join `U(S)` lies below the complementary
  coatom meet `V(S)`; this comparability is literal and does not use
  modularity.
- In every finite lattice, longest-chain height strictly increases under
  strict order.  Comparable elements with equal height are therefore equal,
  so vanishing reconstruction gaps gives `U(S)=V(S)` for every subset `S`.
- The `V` description proves all meet identities and the `U` description
  proves all join identities.  Atomic strictness prevents collisions between
  distinct subset faces, so no separate injectivity premise is hidden.
- A top or repeated tuple entry forces an atom to equal the bottom.  Hence the
  symmetric-group action on admissible ordered tuples is free and division by
  `k!` is exact.
- The resulting face-rank function is submodular by the ambient matroid rank
  inequality and is strictly increasing because the face map is an order
  embedding.  Rank-tightness is exactly the profile `rho(S)=|S|`.
- The direct verifier compares this criterion with the literal meet-map
  definition on the non-graded pentagon, the modular diamond, their products,
  and every candidate family in all registered matroid examples.
  It also records counterexamples to complement-only and three-local
  shortcuts.

Result: the global criterion and complete finite enumerator pass.

## Lattice products and low-rank geometries

- A top-preserving homomorphism from `B_k` is uniquely determined by its
  active Boolean atoms and a labelled embedding on them.  This proves the
  binomial homomorphism transform without assuming injectivity.
- A pair of coordinate homomorphisms into `L x K` is injective exactly when
  their active sets cover `[k]`.  Grouping pairs by the two active-set sizes
  gives the displayed positive factorial coefficient.
- Direct replay agrees for Boolean, non-distributive modular, nonmodular, and
  non-graded product examples.
- In rank three, sizes zero through three are supplied by the trivial,
  universal-pair, and maximum-basis theorems.  The projective-plane formula
  counts only line pairs, nonincident point-line pairs, and noncollinear point
  triples, so it does not assume Desarguesian coordinatization.

Result: the product convolution and complete finite-projective-plane
distribution pass.

## The complete size-two layer

- For two proper elements, join equal to the top already forces
  incomparability and four distinct meet-map images; no distributivity or
  semimodularity is silently assumed.
- `ell(Y)^2` counts ordered pairs whose join is at most `Y`.  Möbius inversion
  therefore counts pairs with join exactly the top.
- Exactly `2|L|-1` of those pairs have a top coordinate, with `(top,top)`
  included only once in the union.  Every remaining unordered pair is counted
  twice.
- In `Pi_n`, the lower interval below a partition is the product over its
  blocks, and `mu(pi,top)=(-1)^(b-1)(b-1)!`; the logarithm follows from the
  labelled exponential formula with block weight `Bell_m^2`.

Result: the universal Möbius formula and the partition-lattice EGF pass.

## All finite distributive lattices

- In `J(P)`, proper ideals correspond exactly to nonempty order filters under
  complementation.
- Finite distributivity proves the full meet-map identity from pairwise top
  joins; the argument does not assume that every antichain is Boolean.
- Pairwise top joins of ideals translate exactly to pairwise disjoint
  complement filters, so unordered Boolean antichains are independent sets in
  the filter-intersection graph.
- Direct replay agrees on antichain posets through five elements, chain posets
  through five elements, and a three-element branched poset.

Result: the all-size distributive-lattice classification passes.

## All finite subspace lattices

- The bottom `X` is recovered as the intersection of the coatoms, and each
  Boolean atom gives a nonzero quotient subspace `A_i/X`.
- The Boolean meet of one atom with the join of all other atoms is the bottom;
  this proves an internal direct sum, not merely pairwise-zero intersection.
- Conversely, all partial sums of a direct-sum decomposition preserve sums
  and intersections and therefore form a Boolean sublattice.
- For fixed dimensions, `GL_d(q)` acts transitively on ordered decompositions
  with block-diagonal stabilizer `product GL_(d_i)(q)`.  Division by `k!` is
  valid even when dimensions repeat because every unordered set of `k`
  distinct summands has exactly `k!` orderings.
- Exact replay matches every size over `F_2` through dimension three.

Result: the Gaussian/direct-sum formula for all finite subspace lattices
passes.

## Closed family formulas

- In the free matroid, every corank-`k` flat leaves a free rank-`k`
  contraction with one basis, giving `binom(n,k)`.
- In `Pi_n`, a corank-`k` flat has `k+1` partition blocks.  After contraction,
  each pair of blocks gives one parallel class, so the simplification is
  exactly `K_(k+1)` and Cayley gives `(k+1)^(k-1)`.
- In `U_(r,n)`, the `k=1` contraction is rank one and all remaining elements
  are parallel.  The separate formula for `k=1` is therefore essential.
- For the unrestricted uniform formula, the Boolean atoms differ from the
  bottom by disjoint nonempty blocks.  The full block union must reach rank
  `r`, while deletion of any one block must remain below rank `r`; these are
  exactly the displayed size constraints.  The multinomial factor chooses
  ordered blocks and the free `k!` quotient forgets their labels.
- For a disconnected graph, matroid bases are spanning forests and the
  maximum antichain size is `|V|-c(G)`; the manuscript does not call these
  objects spanning trees.

Result: the Boolean, partition, uniform, and graphic specializations pass.

## Publication boundary

The manuscript does not claim that the existence of a basis-generated
Boolean sublattice is new.  It claims the inverse maximum-antichain
classification, weighted basis decomposition, minor-local theorem, and
rank-tight enumerations, the global height-gap classification, and the lattice
product convolution.  It does not
claim:

- a compact Tutte-polynomial evaluation of the full rank-profile enumerator;
- that a dated literature search is a permanent novelty guarantee.

The completed Lean~4 development now supplies premise-free publication-root
producers for every formally mapped result. The publication and atomic roots,
the 105-occurrence paper correspondence contract, and the unconditional Proof
Engine interface are separately signed and accept only `propext`,
`Classical.choice`, and `Quot.sound`. The conditional claim-graph interface is
not imported by the publication root.

**Verdict:** PASS for the human proof and the paper-to-kernel correspondence.
Independent specialist review remains a separate external gate.
