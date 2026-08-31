# Manuscript theorem map

Canonical manuscript: `paper/matroid_boolean_antichains.tex`.

## Human-proof and finite-regression baseline

The following table records the baseline evidence, not kernel proof status.

| Manuscript result | Mathematical status | Machine boundary |
|---|---|---|
| `lem:full-height` | human proof complete | finite ranked-flat examples replayed |
| `lem:basis-span` | human proof complete | exact meet/join identities replayed on uniform, binary, and graphic matroids |
| `thm:global-gap` | human proof complete | the `2^k` height-gap criterion is replayed against the literal `4^k` meet-map definition on non-graded `N_5`, modular `M_3`, products, and every size in seven uniform, binary, and graphic examples |
| `thm:product` | human proof complete | the positive convolution is replayed on `B_1 x B_1`, `B_2 x B_1`, `N_5 x B_1`, and `M_3 x B_1` |
| `cor:rank-profile` | human proof complete | strictness and rank-tight profile consumers are checked through the global criterion |
| `thm:uniform-all` | human proof complete | every size replayed for `U(2,4)`, `U(3,4)`, `U(3,5)`, `U(4,5)`, and `U(4,6)` |
| `thm:size-two` | human proof complete | Möbius formula replayed on every finite example |
| `thm:distributive` | human proof complete | antichain, chain, and V-poset ideal lattices replayed through five elements |
| `thm:main` | human proof complete | inverse maps replayed on seven matroids, including loops and parallels |
| `thm:weighted` | human proof complete | exact integer-weight evaluations replayed |
| `thm:interval` | human proof complete | every interval of the finite examples replayed through the rank-tight consumer |
| `cor:rank-tight` | human proof complete | every size in the finite examples replayed |
| `cor:boolean-lattice` | human proof complete | `n<=5` replayed against Stirling numbers |
| `cor:partition-lattice` | human proof complete | `n<=4` replayed by direct flat-lattice enumeration |
| `cor:partition-pairs` | human proof complete | direct enumeration through `n=4`; Bell-square formula replayed through `n=7` |
| `thm:subspace` | human proof complete | every size replayed over `F_2` through dimension three |
| `cor:uniform-tight` | human proof complete | the displayed formula replayed for three parameter pairs |
| `cor:graphic` | human proof complete | connected and disconnected graphic examples replayed |
| Equation `eq:projective-count` | human proof complete | product simplification checked algebraically; no projective-geometry enumerator registered |
| Equation `eq:projective-plane-all` | human proof complete | the incidence formula is replayed on the Fano plane, giving `(1,15,49,28)` |

All twenty named theorem-map rows now have premise-free Lean producers. The
Python replay remains regression evidence only. Proof Engine is closed by the
kernel-only publication root, atomic declaration audit and reviewed formal
contract. Individual Lean producers and their literal-correspondence
boundaries are listed below.

## Kernel-only Lean map

Canonical Lean root: `lean4/BooleanAntichainsKernel/PublicationRoot.lean`.
Every row has a publication-root producer. The partition-pairs formula is
stated and proved for the same explicit range `n >= 1` in TeX and Lean.

| Manuscript result | Lean declaration(s) | Kernel-only status |
|---|---|---|
| `lem:full-height` | `manuscript_lem_full_height` | kernel-only producer complete: unordered bottom, all maximal chains, atom and coatom grades |
| `lem:basis-span` | `manuscript_lem_basis_span` | kernel-only producer complete on the paper's rank-one-flat simplified-basis carrier; representatives, rank submodularity, meet/join identities and injectivity consumed |
| `thm:global-gap` | `manuscript_thm_global_gap` | kernel-only producer complete: literal natural height gaps, both indicator products, exact unordered count with proved factorial fibers, zero layer, and vanishing above height |
| `thm:product` | `manuscript_thm_product`; `manuscript_thm_product_transform` | kernel-only producer complete: actual top-only hom/embedding carriers, active-set restriction/extension bijection, product embedding/cover-data bijection, covering-set multiplicities, eta multiplicativity and the literal positive factorial convolution |
| `cor:rank-profile` | `manuscript_cor_rank_profile` | kernel-only producer complete: literal unordered profile is natural-valued, normalized, strictly increasing and submodular; rank-tight iff every face has cardinality rank |
| `thm:uniform-all` | `manuscript_thm_uniform_all`; `manuscript_thm_uniform_all_structure` | kernel-only producer complete: actual block bijection and within-block permutation fibres, exact remaining-ground coefficient, natural admissible-profile and bottom-size sums, rational division with proved divisibility/nonzero guards, zero/singleton layers and both kernel-derived U(3,4)/U(4,5) distributions |
| `thm:size-two` | `manuscript_thm_size_two` | kernel-only producer complete: structural equivalence and Möbius count in a single root |
| `thm:distributive` | `manuscript_thm_distributive` | kernel-only producer complete: size-preserving literal complement bijection, actual SimpleGraph of intersecting nonempty order filters, and polynomial equality on literal antichain/independent-set sums |
| `thm:main` | `manuscript_thm_main` | kernel-only producer complete: actual erase/meet and erase/join maps, both inverse laws, cardinal equality, actual simplification matroid and standard rank-subset Tutte evaluation at (1,1) |
| `thm:weighted` | `manuscript_thm_weighted` | kernel-only producer complete: actual basis/class-choice partition, arbitrary-semiring product expansion, symbolic multivariate polynomial, all-one count, and literal minimal-nonbottom span atoms |
| `thm:interval` | `manuscript_thm_interval` | kernel-only producer complete: actual `(M|Y)/X`, proved contraction rank, inverse `F\\X` / `S union X` flat maps, size `rank(Y)-rank(X)`, Boolean/atom transport, and exact `A\\X` polynomial factors |
| `cor:rank-tight` | `manuscript_cor_rank_tight` | kernel-only producer complete: literal common-meet partition, fixed-bottom interval/contraction bijections to actual simplification-matroid bases, exact integer-corank sum and empty layers above rank |
| `cor:boolean-lattice` | `manuscript_cor_boolean_lattice`; `manuscript_cor_boolean_lattice_tight` | kernel-only producer complete: literal rank-tight and non-rank-tight subtypes, binomial count via actual free contractions, total Stirling count via the paper's B1 product recurrence and actual lattice isomorphism, and complementary subtraction |
| `cor:partition-lattice` | `manuscript_cor_partition_lattice`; retained structure and contraction roots | kernel-only producer complete: literal partition/flat and contraction/simplification transports, full parallel fibres, actual Stirling insertion count, locally replayed complete Cayley proof, exact displayed rank-tight range and the actual maximum-antichain Cayley count |
| `cor:partition-pairs` | `manuscript_cor_partition_pairs`; retained `manuscript_cor_partition_pairs_structure` | kernel-only producer complete for the paper's explicit `n >= 1` range: literal lower-interval product, actual Bell counts, actual partition Möbius values, Bell-square formal power series and logarithm, exponential-formula bridge, exact pair formula and all seven listed values |
| `thm:subspace` | `manuscript_thm_subspace`; retained `manuscript_thm_subspace_correspondence` and `manuscript_thm_subspace_direct_sum_count` | kernel-only producer complete: literal unordered quotient correspondence, dimensions, actual GL action/stabilizer and rational D(d,k); independent-frame/span bijection, annihilator/codimension transport and Gaussian count; exact k..n total, zero layer, kernel-derived F_2^3 distribution and top-layer projective product specialization |
| `cor:uniform-tight` | `manuscript_cor_uniform_tight` | kernel-only producer complete: actual uniform matroid and contractions, corank-flat/r-subset bijection, rank-one simplification exception, singleton parallel classes for rank at least two, exact binomial normalization, all three displayed branches and above-rank empty layers |
| `cor:graphic` | `manuscript_cor_graphic`; six retained graphic foundation/weight roots | kernel-only producer complete: actual simplification matroid equality on all independent sets, literal maximum-antichain/spanning-forest bijection and span-atom edge map, exact size, original simple-graph forests, native connected spanning trees, complete parallel-edge fibres and original-variable spanning-forest polynomial |
| Equation `eq:projective-count` | `manuscript_eq_projective_count` | kernel-only producer complete: actual projective-subspace lattice and unordered independent projective-point carrier; exact atom/line and inverse coatom maps; vector-frame/nonzero-scalar bijection, actual k-factorial labelling fibres and literal rational product |
| Equation `eq:projective-plane-all` | `manuscript_eq_projective_plane_all`; retained `manuscript_eq_projective_plane_structure` | kernel-only producer complete: arbitrary finite incidence-plane matroid, literal flat sets and rank-three bases; actual proper-pair line-line/point-line bijection with both orientations, earned two-factorial fibres, unique-line triple fibres, full c0/c1/c2/c3 distribution and higher vanishing; no Desarguesian premise |

### Current verification boundary

`lean4/BooleanAntichainsKernel/PublicationAxiomAudit.lean` audits forty-one implemented
declarations in the current publication root. The signed receipt policy is
`.paper-infrastructure/lean-publication-verification.json`; its receipt
is `output/lean-publication-receipt.json`. It attests those forty-one
declarations and the exact bound source inventory. The declaration count is
not the complete-row count: several are retained clauses of a shared theorem.
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.

`lean4/BooleanAntichainsKernel/AtomicPaperClaimAxiomAudit.lean` separately
audits forty-nine unique atomic bindings extracted from the protected
definition/equation/theorem/corollary environments. Its signed policy is
`.paper-infrastructure/lean-atomic-claims-verification.json`, with receipt
`output/lean-atomic-claims-receipt.json`.

The reviewed formal contract contains 105 occurrences: 49 formal
declarations, one scope-only formalization-status sentence and 55
restatement/proof relations. Its final signed policy is
`.paper-infrastructure/formal-contract-verification.json`, with receipt
`output/formal-contract-verification-receipt.json`. It binds complete
declaration signatures, proof-term tokens, per-root project axioms, TeX
coverage, premise traces and relation sets.

Proof Engine v2.5.27 now records thirteen earned hyperedges, thirteen exact
bindings, thirteen scope/strength reviews and thirteen sealed machine checks.
All fourteen claims, including `CLAIM-MATROID-BA-TARGET`, are reachable;
`frontier_edge_ids` is empty and `target_closed=true`. The premise-free
outputs are audited in `ProofEngineInterface.lean`. The separate
`ProofEngineGraphInterface.lean` declares only the typed upstream claim inputs
required by the claim graph; those conditional wrappers are not imported by
the publication root and do not broaden its three-axiom trust boundary.

Before kernel execution, use verification-only mode. If missing or stale, use
the same infrastructure's explicit run-or-reuse mode and exclusive lease.
No reference gate or finite Python replay is an input to a Lean producer.

All twenty map rows now have complete theorem producers (`lem:full-height`,
`lem:basis-span`, `thm:global-gap`, `thm:size-two`, `thm:main`,
`cor:rank-profile`, `thm:distributive`, `thm:weighted`, `thm:interval`, `cor:rank-tight`, `thm:product`, `cor:boolean-lattice`, `cor:uniform-tight`, `thm:uniform-all`, `thm:subspace`, `eq:projective-count`, `eq:projective-plane-all`, `cor:graphic`, `cor:partition-lattice`, `cor:partition-pairs`). This count does not by itself certify the final
formal-contract correspondence; that broader correspondence is certified by
the separate 105-occurrence contract and its signed receipt above.

The rank-tight boundary is now proved: `HasCorank` uses integer subtraction,
with a proved additive equivalent; `k > rank(M)` gives an empty index layer.
The `IsRankTight C` predicate on existing Boolean antichains is explicitly
proved equivalent to that integer condition using the rank/size bound.

The product boundary preserves the source: top-preserving homomorphisms are not required to
preserve the ambient bottom. Their active atoms are defined relative to
`f(empty)`, and this carrier is preserved in the checked decomposition.
The product-map injectivity/active-cover equivalence is consumed by an actual
bijection. Complementing the second active set counts its covering partners;
grouping both sets by size and dividing by the proved factorial fibres gives
the displayed coefficient. The convolution is an equality in the rationals
between the cast of the actual unordered count and the literal factorial
ratios, with exactly `0 <= a,b <= k` and `k <= a+b`.

The Boolean rank-tight clause is now checked on literal Boolean antichains
in `Finset (Fin n)`. Its predicate uses the cardinality of the actual common
meet. The free-matroid flat order isomorphism transports this very meet and
its rank, and the contraction/corank proof is consumed.

The total Stirling count now consumes the manuscript's product-with-`B_1`
recurrence, including the actual subset-lattice product isomorphism, initial
layers, active-cover specialization and factorial normalization. An explicit
finite-ground order-isomorphism also aligns the instances used by the total
count and rank-tight subtypes. The non-rank-tight carrier is the literal
complementary subtype, and its subtraction formula is proved.

The uniform rank-tight root now consumes actual uniform closure, flats,
contractions, r-subset bases, the corank subset bijection and the checked
basis/class-choice decomposition. Rank-one contractions use their unique
simplified basis, whereas rank at least two uses proved singleton parallel
classes. The displayed binomial coefficient product is derived from these
counts; neither a uniform minor nor a simplified count is assumed.

The all-size uniform structural root now consumes the literal bottom
`f(empty)` and differences `f({i}) \\ f(empty)`, pairwise disjoint/nonempty
blocks, proper-face ordinary unions, both inverse laws and the proved
k-factorial fibres. The full union is only required to reach rank r; it is
not forced to equal E, so unused ground elements are retained. The exact
profile inequalities and their converse construction are checked.

The complete uniform root now consumes numbered-block/injection bijections
and the actual within-block factorial fibres. Their descending-factorial
count earns the unused-element factorial. Actual bottom/profile decomposition
then yields the displayed sum. Profiles retain natural-number variables;
the bounded encoding is proved equivalent and used for kernel evaluation only.
Divisibility and nonzero factorial proofs connect both natural divisions to
the literal rational fractions. The two displayed distributions consume this
formula, with five independently checked finite computations and the proved
zero/singleton layers; no external Python replay is an input.

The subspace correspondence root now consumes the actual quotient map and
its inverse-image map. The sigma index is the literal common intersection;
the unordered summands are the images of the actual erase/meet atoms, and
inverse coatoms are inverse images of erase/join sums. Internal direct sums
use the bijectivity of the canonical direct-sum map. Nonzero summands, their
dimension sum, k<=d<=n and the free k-factorial labelling fibres are proved.
Equal summand dimensions do not introduce extra permutation denominators.

The direct-sum-count root now consumes the actual GL action on each indexed
summand, componentwise extension and restriction, the complete product-GL
stabilizer isomorphism, and orbit-stabilizer. Positive profiles have actual
coordinate decompositions transported into V, so no nonempty-orbit premise
is left as an external input. A basis-induced group isomorphism connects
Aut(V) with matrix GL, whose cardinality product and g_0=1 are checked.
Positive dimension profiles are partitioned by the actual summand dimensions,
and the rational D(d,k) formula consumes the k-factorial fibres and nonzero
group cardinalities.

The full subspace root now also consumes the independent-frame/span bijection
and the actual number of bases in each dimension-d subspace. The explicit
Gaussian product ratio is proved to equal that carrier's cardinality; the
annihilator/coannihilator equivalence transports this result to the actual
codimension-d carrier. Grouping the quotient sum and removing dimensions
below k gives the literal displayed k..n formula. The F_2^3 distribution
consumes a proved bounded encoding of the natural profiles and pure kernel
reduction of rational arithmetic, with no external computation certificate.
At k=n, the unique profile consists entirely of ones and yields the exact
projective product, including rational subtraction and the original n!.

The projective-count root now consumes the actual projective-subspace lattice
order isomorphism and a bijection to unordered independent projective points.
Their one-dimensional subspaces are exactly the transported erase/meet atoms;
the inverse uses the actual erase/join coatom subspaces. A full independent
frame spans V; conversely, every summand in a full-size internal decomposition
has dimension one. Actual vector frames are bijective to projective frames
and one nonzero scalar per position, proving the (q-1)^r factor. Actual
labelling fibres prove r!, and the resulting basis count is consumed by
the displayed antichain count with rational subtraction and nonzero guards.
The equation is therefore not just a relabelled submodule count.

The full general-plane root now uses arbitrary finite incidence planes,
without any field or Desarguesian premise. The independent-set augmentation
axiom is proved from unique lines and a point outside a line. The resulting
actual matroid has rank three and precisely the noncollinear three-point
bases. Its actual closures prove that its flats are exactly the empty set,
singletons, incidence lines and all points, with the original incidence order.
Their enumeration proves c0=1 and c1=2N+1. Singleton parallel classes allow
the existing maximum-antichain theorem to reduce c3 to actual noncollinear
triples. Each collinear triple lies on exactly one line, so a literal triple
partition gives c3=choose(N,3)-N*choose(q+1,3). All sizes above three vanish.

The size-two layer now consumes an actual bijection from distinct ordered
line pairs and both orientations of nonincident point-line pairs onto all
proper top-join pairs. The actual incidence counts give N(N-1)+2Nq^2;
the generic Boolean-pair correspondence and earned two-factorial fibre give
choose(N,2)+Nq^2. The full four-entry distribution and all higher zero layers
are collected in the named plane root, on the actual matroid flat carrier.

The graphic carrier root now retains the original Graph edge labels and
uses exactly Graph.vertexSet, including isolated vertices. The endpoint map
is proved to recognize original links, diagonal loops and same-endpoint
classes. Forests are defined by absence of actual labelled multigraph cycles;
one-edge loops and two-edge parallel cycles are explicitly constructed.
Cycle lifts and projections preserve their vertex order and endpoint-edge
sequence. They prove the exact equivalence with loop exclusion, injectivity
on selected edge labels and acyclicity of the simple support. A genuine
forest-edge/support-edge bijection proves the edge count, and finite actual
vertex sets imply finite forests even when the ambient edge type is infinite.
The second graphic root now also consumes the original labelled-walk
reachability/component transport. Actual vertex and edge partitions over
components, together with each component's proved tree edge count, give
|F|+c(F)=|V|. The component quotient map and this identity supply a connecting
edge in the larger forest; insertion of that original edge proves the full
forest augmentation axiom. The actual cycle matroid is constructed on the
original edge ground set. Its bases are proved equivalent to labelled
forests preserving all original reachable pairs. The rank identity is first
proved without subtraction, r(M(G))+c(G)=|V(G)|, then in the displayed form.
Only the actual vertex and edge sets must be finite; the ambient label types
are not assumed finite.

The third graphic root now consumes the literal componentwise spanning-tree
characterization. Original components are actual sets of original vertex
labels. Native edge restriction and vertex induction build each selected
component subgraph. Label-preserving walk maps and restrictions prove cycle
and reachability transport in both directions. A spanning forest is defined
by one nonempty connected acyclic labelled subgraph on each full original
component, and this is proved equivalent to the component-spanning condition.
Cycle-matroid bases and these spanning forests are bijective on the identical
finite original edge sets. The forest family is finite from the actual edge
ground alone, and its cardinality and common edge size are proved.

The fourth graphic root now consumes the actual matroid closure and IsFlat
connectivity characterization. Actual bases of edge subsets preserve their
reachable pairs, and the rank/component identity is proved for those subsets.
Empty and singleton labelled walks identify the matroid loop flat with all
original graph loops. A nonloop singleton closure minus that loop flat is
exactly the complete same-endpoint original-edge class. Every actual rank-one
flat has a proved nonloop representative; these flats are bijective to the
actual simple edges, and inverse class membership recovers the full original
endpoint fibre. This is a ground/class identification, not yet a claim that
the full simplification matroid structure or the graph corollary is closed.

The fifth graphic root consumes the finite-ground transports: the native
restriction to the actual matroid ground is lattice-isomorphic to the
original literal flat sets, with exact closure, rank, maximum antichain and
actual span-atom transport. The basis bijection restores original labels
and preserves each finite-set product. Full nonloop classes, not only class
sizes or chosen representatives, are transported back. Only the actual
ground is assumed finite; no finiteness of the ambient label type is added.

The original spanning-forest polynomial is defined directly as the sum of
original-edge monomials. Its kernel-checked expansion now indexes actual
maximum Boolean antichains and their actual span atoms. Those atoms inject
into the actual simple edges, with a proved inverse-flat membership rule.
Each edge factor is the sum of all original variables in its complete
endpoint fibre. The arbitrary-commutative-semiring identity, symbolic
polynomial and maximum-family size are consumed by the publication root.
The weighted result is now connected to the actual spanning-forest
bijection by the full graphic root below.

The sixth graphic root realizes the simple support as a native graph on
the identical original vertex set, with endpoint-pair edge labels. Actual
link identities prove that it has no loops or parallel edges. Its literal
labelled forests are exactly acyclic subsets of the simple-support edges.
Reachability transport induces an identity-on-vertices component bijection
and equality of component counts, retaining isolates. Its native cycle
matroid has precisely those independent sets; its bases are the existing
one-tree-per-original-component spanning forests. These statements do not
by themselves identify that matroid with the rank-one-flat simplification;
that exact identification is consumed by the full graphic root below.

The complete graphic root now proves the exact representative/endpoints
transport for every rank-one-flat family. Equality of whole support graphs
identifies every independent set, giving equality of the actual
representative-comap simplification and the native simplified-graph cycle
matroid after the proved ground bijection. The corresponding finite-basis
and forest maps are composed with the main theorem. Both inverse laws are
checked, and the output finite edge set is exactly the set of actual
span-atom edges already used in the weighted polynomial.

For simple graphs the original-edge/endpoint-pair equivalence transports
forests back to their original labels. For connected graphs, the native
edge restriction retains all original vertices and is a spanning tree
exactly when its original edge set is a spanning forest. The restriction
map preserves complete edge/vertex label sequences and cyclehood. Its
forest/tree bijection is the identity on finite original edge sets.
The full graphic root consumes all these clauses and the symbolic and
arbitrary-semiring parallel-class expansions.

The partition structural root now consumes the actual native finite
nonempty-block partition carrier. Its same-block setoid has exactly those
blocks as classes; both inverse laws and refinement order are proved.
The native intersection-block meet is retained, and the join is proved to
be the least common coarsening. The complete labelled graph retains the
original vertices and unordered distinct-vertex edge labels.

Block-internal complete edges form actual matroid flats, and original
labelled reachability is exactly same-block membership. This gives the
literal partition/complete-flat lattice isomorphism and its inverse.
Components biject to actual quotient classes and actual finite blocks.
The additive rank-plus-block identity is proved before subtraction;
positive vertex types give corank k exactly when there are k+1 blocks.
Boolean antichains, their actual common meets and integer rank-tightness
are transported. The existing rank-tight theorem is consumed as a sum
over actual (k+1)-block partitions with actual contraction-simplification
bases as coefficients. No Stirling or Cayley coefficient is yet supplied.

The contraction root now consumes the literal quotient/block
correspondence. Every coarse block is exactly the union of its grouped
original fine blocks, and the block bijection proves relative-rank
preservation. The already checked interval minor is transported to the
actual contraction by the literal difference/union maps. Its flat lattice
is rank-preservingly isomorphic to the complete graph on the actual
original blocks. An explicit unordered-edge map tests membership in every
flat and the actual contraction ground.

This flat transport is consumed at the independent-set level to prove
equality of the actual simplification matroid with the complete-block
cycle matroid after its proved ground equivalence. Each nonloop parallel
class is the complete fibre of one original block pair, and all these
fibres are proved nonempty. Actual finite bases biject to actual
complete-graph spanning trees, preserving the finite edge map. The
rank-tight sum now has those literal tree cardinalities as coefficients.
The numerical evaluations are now consumed by the complete partition root
described below. A bounded scan of the other research projects found only
unrelated Cayley-graph and prime-root-count filenames, which were not
imported.

The actual unordered partition/Stirling count is now proved from an
insertion/deletion bijection: the new point is either a singleton or joins
one marked original block. Its two block-count changes and all zero
boundaries are checked. A literal vertex relabelling transports the
Option/Fin-successor recurrence, yielding the standard Stirling sequence
and the exact corank-flat count.

A subsequent public-source search located a complete MIT-licensed Cayley
proof by Christopher Brock, pinned at commit
`313243c3c37ad150109cb057a062a72d73b4c260`, source blob
`111a5bdcd71501e5a207ed3a6fef7c26a64e6a3d`.
Its entire rooted-forest counting argument and actual SimpleGraph.IsTree
endpoint were locally replayed in six kernel-checked cache partitions.
The copyright/license and source URL are preserved in each partition.
No external verification label was accepted as proof.

The native original-edge spanning trees are proved equivalent to those
actual simple-graph trees, with both edge maps exact; vertex relabelling
is also a proved tree equivalence. The Cayley value is therefore consumed
on the original block vertices. The complete root now proves
S(n,k+1)(k+1)^(k-1) for exactly 1<=k<=n-1 and n^(n-2) for the actual
maximum-antichain family. The maximum/rank-tight equivalence preserves
the same finite family.

The partition-pairs row is now kernel closed. A literal lower-interval order
isomorphism gives the product over the actual blocks. Marking and removing a
block proves the Bell recurrence on the real partition carrier. The partition
Möbius value is obtained from the incidence-algebra recurrence, and the
Bell-square weighted sum is grouped by actual ordered block profiles. The
power-series logarithm and exponential formula then prove the displayed
coefficient identity. Independent kernel reductions yield exactly
`0,0,3,45,620,9750,183680` for `n=1,...,7`.

The partition-pairs display now explicitly states `n>=1`. This is the exact
Lean premise and excludes the false `n=0` boundary, where the left side is
zero but the displayed right side would be `(0-2+1)/2=-1/2`.

Paper Infrastructure introduced the mandatory language gate at v6.0.0 and
is currently v6.1.0. Its mandatory
bilingual gate now binds a structurally identical 184-unit Chinese review
source and a visually inspected 17-page PDF. The final formal contract binds
105 manuscript occurrences and the positive-`n` premise trace. Submission
preflight, build, postflight, artifact and bilingual-post gates all pass.

The completed local English revision is a visually inspected 14-page PDF; its
only intended visible changes from public v1 are the explicit positive-`n`
range and the completed formalization statement. The public Zenodo v1 record
has not been replaced or updated by this local formalization task.
