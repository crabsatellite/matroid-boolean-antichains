# Kernel-only formalization (in progress)

Canonical manuscript: `../paper/matroid_boolean_antichains.tex`.
Canonical result map: `../THEOREM_MAP.md`.
The full paper remains **OPEN**. The current publication root audits thirty-three
implemented declarations, including seventeen complete theorem producers; this is
not an all-paper completeness claim.

Toolchain: Lean `v4.32.0-rc1`. Mathlib is pinned in `lake-manifest.json` and
`lakefile.toml`; only checked mathlib and this project's Lean source are imported.
The local Lake library uses `--trust=0` and treats warnings as errors.

## Implemented foundations

- `Core.lean`, `GlobalEnumerator.lean`: reconstructed faces, structural criterion,
  and the actual unordered `Finset` carrier with a proved factorial enumeration.
- `HeightGapEndpoints.lean`: the literal natural height differences and both
  products of indicators, the zero layer, and the above-height vanishing clause.
- `Pairs.lean`, `MobiusFormula.lean`: the four pair faces, Möbius inversion,
  and exact removal of the `2|L|-1` pairs having a top coordinate.
- `Distributive.lean`, `FilterIntersectionGraph.lean`, `DistributivePolynomial.lean`:
  complement bijection to disjoint nonempty upper sets; actual intersection
  `SimpleGraph`, independent vertex sets, and ordinary polynomial equality.
- `MatroidFlats.lean`, `MatroidRank.lean`: actual `Matroid.IsFlat` lattice,
  finite natural rank, strict rank increase, submodularity and cover increments.
- `FullHeight.lean`, `FullHeightChains.lean`, `UnorderedFullHeight.lean`:
  full-height rigidity including maximal chains and exact unordered transport.
- `SimplifiedBasis.lean`, `BasisSpan.lean`: choose genuine nonloop representatives,
  prove they form a mathlib matroid basis, and consume the paper's submodularity
  proof of the Boolean join/meet identities.
- `AtomCoatomReconstruction.lean`, `MaximumBijection.lean`: literal unordered
  Phi/Psi maps, both inverse laws, and equality of maximum-antichain and
  simplified-basis cardinalities.
- `MatroidSimplification.lean`, `SimplificationBases.lean`, `TuttePolynomial.lean`:
  an actual mathlib simplification matroid on rank-one flats, identification of
  its actual bases with the paper carrier, and the standard rank-subset Tutte
  polynomial evaluated at (1,1). No Tutte value is assumed or defined as a count.
- `RankProfiles.lean`: literal natural-valued unordered face ranks, normalized
  strict integral polymatroid structure, and both directions of rank-tightness.
- `ParallelClasses.lean`, `BasisChoices.lean`, `BasisChoiceBijection.lean`,
  `BasisWeightExpansion.lean`, `SpanAtoms.lean`, `WeightedTheorem.lean`: the
  actual partition of bases by nonloop parallel-class choices, symbolic product
  expansion, count specialization, and identification of the literal span atoms.
- `MinorRank.lean`, `FlatIntervalMinor.lean`, `LatticeTransport.lean`,
  `IntervalTheorem.lean`: contraction rank from actual bases, the actual
  restriction/contraction flat-lattice isomorphism, full Boolean/atom transport,
  and the interval-weighted theorem with `A \\ X` factors and exact interval rank.
- `UpperIntervalAntichains.lean`, `RankTightFibers.lean`, `RankTightEnumeration.lean`:
  literal common-meet fibers, interval/contraction basis bijections, the corank
  sum, and its empty layers above rank. Integer and natural rank-tight
  formulations are connected only after proving the necessary rank/size bound.
- `TopBooleanHom.lean`, `ActiveAtoms.lean`, `ActiveHomDecomposition.lean`,
  `HomEnumeration.lean`: actual top-preserving (not ambient-bottom-preserving)
  homomorphisms and embeddings, coatom transport, the exact active-set
  decomposition, label-count transport and eta multiplicativity.
- `ProductEmbeddingData.lean`, `CoverPairCounting.lean`,
  `ProductLabelledCounting.lean`, `ProductCoverCoefficient.lean`,
  `ProductConvolution.lean`: actual covering-active-data bijection, cardinal
  grouping by both active-set sizes, exact factorial normalization, and the
  positive product convolution on actual unordered Boolean antichains.
- `FreeMatroid.lean`, `BooleanTightFree.lean`, `BooleanTight.lean`: actual
  free-matroid flats and contractions, unique bases after simplification,
  corank-flat/complement-subset bijection, and binomial rank-tight count on
  the literal subset-lattice carrier with proved common-meet/rank transport.
- `BooleanBaseCounts.lean`, `BooleanProductRecurrence.lean`,
  `BooleanStirling.lean`, `BooleanStirlingTransport.lean`,
  `BooleanEnumeration.lean`: actual B0/B1 boundary counts, the paper's product
  recurrence and subset-lattice product isomorphism, the proved Stirling total
  count, coherent finite-ground transport, and the complementary non-rank-tight
  subtype count. The full Boolean-lattice corollary is consumed in the root.
- `UniformMatroid.lean`: actual cardinal-independence matroid construction,
  proved finite augmentation, r-subset basis characterization and ground rank.
- `UniformFlats.lean`, `UniformMinorBases.lean`: literal closure, proper
  flats and rank, actual contraction identity, and the r-subset basis
  bijection and binomial basis counts on the remaining ground.
- `SimplifiedBasisCounts.lean`, `UniformSimplification.lean`:
  rank-one simplified-basis uniqueness, singleton parallel classes in
  uniform rank at least two, and actual basis/class-choice counting.
- `UniformCorank.lean`, `UniformRankTight.lean`: positive-corank flats as
  actual (r-k)-subsets, the zero layer, and all displayed rank-tight branches
  with the exact binomial normalization and above-rank vanishing.
  The full uniform rank-tight corollary is consumed; the all-size theorem is open.
- `SingletonAntichains.lean`, `UniformSingletonCounting.lean`: actual
  one-atom embedding/proper-element correspondence and the proper-flat
  subset-size sum for the singleton layer.
- `UniformBlockFaces.lean`, `UniformBlockEmbedding.lean`,
  `EmbeddingBlockExtraction.lean`, `UniformEmbeddingBlocks.lean`,
  `UniformBlockBijection.lean`: literal bottom and atom-difference blocks,
  ordinary proper faces, both inverse maps, and the earned k-factorial
  quotient. Unused ground elements are permitted.
- `UniformBlockProfiles.lean`: face-cardinality sums, exact coatom subtraction,
  all displayed arithmetic constraints and their converse block construction.
- `SizedDisjointBlocks.lean`, `SizedBlockCoefficients.lean`: actual
  within-block enumerations, injection bijection, factorial fibres and exact
  fixed-size disjoint-block coefficient, including unused ground elements.
- `UniformProfileIndex.lean`, `UniformProfileAssembly.lean`,
  `UniformAllFormula.lean`: natural admissible-profile carriers, actual
  bottom/profile partition, weighted bottom-size sum and full formula.
- `UniformComputableFormula.lean`, the five `UniformNumeric*` value files,
  `UniformNumericDistributions.lean`, `UniformRationalFormula.lean`:
  proved bounded-code transport, independent kernel computations, both
  displayed distributions, and explicit divisibility/nonzero-denominator
  transport to the paper's rational formula. The full uniform theorem is consumed.
- `TopEmbeddingTransport.lean`, `BottomEmbeddingIntervals.lean`,
  `SubspaceQuotientEmbedding.lean`: actual bottom fibres, quotient images
  and inverse images, with the original common coatom meet preserved.
- `InternalSumEmbedding.lean`, `InternalSumAtoms.lean`,
  `SubspaceDecomposition.lean`, `SubspaceDimensions.lean`: canonical
  internal direct-sum maps, Boolean atoms and subcollection sums, the labelled
  quotient correspondence, positive dimensions, dimension sum and codimension bounds.
- `UnorderedInternalData.lean`, `BottomAntichainBasics.lean`,
  `UnorderedInternalBijection.lean`, `AntichainBottomFibres.lean`,
  `SubspaceAntichainFibres.lean`, `SubspaceUnorderedCorrespondence.lean`:
  actual unordered summand sets, exact erase/meet and erase/join maps, and
  the full unordered quotient correspondence with literal map/comap formulas.
- `InternalOrderingCount.lean`: earned k-factorial fibres of actual
  distinct nonzero summands, also when their dimensions coincide.
- `InternalLinearAction.lean`, `InternalBlockLinearEquiv.lean`,
  `InternalProfileTransitivity.lean`, `InternalStabilizer.lean`:
  actual GL action and dimension preservation, component extensions,
  transitivity and the genuine product-GL stabilizer with inverse group maps.
- `InternalProfileExistence.lean`, `LinearAutomorphismCard.lean`,
  `InternalOrbitCount.lean`, `InternalDimensionProfiles.lean`,
  `SubspaceDirectSumFormula.lean`: actual positive-profile representatives,
  the basis-induced matrix GL group isomorphism and cardinality product,
  orbit-stabilizer count, positive-profile partition and rational D(d,k).
- `SubspaceFrames.lean`, `GaussianSubspaceCount.lean`: actual independent
  frames, their unique spans, basis fibres, the explicit Gaussian product
  ratio, and exact annihilator/coannihilator transport to codimension.
- `SubspaceGaussianFormula.lean`: Gaussian grouping of the actual quotient
  sum with the proved lower limit k.
- `SubspaceComputableFormula.lean`, `SubspaceF23Values.lean`,
  `SubspaceTopProduct.lean`, `SubspaceCompletion.lean`: exact bounded-profile
  encoding, kernel-reduced F_2^3 values, actual antichain distribution, and
  the unique all-one profile yielding the top-layer product. Rational values
  use `decide +kernel`, not a native execution escape.
- `ProjectiveLattice.lean`, `ProjectiveFrames.lean`: actual projective subspace
  and point carriers, atom-preserving lattice transport, and the vector-frame
  bijection with one nonzero scalar per projective point.
- `ProjectiveInternal.lean`, `ProjectiveIndependentSets.lean`: full-length
  independent frames, one-dimensional internal summands, actual unordered
  projective bases, and the forced zero bottom of maximum antichains.
- `ProjectiveBasisCounting.lean`, `ProjectiveEnumeration.lean`: earned scalar
  and labelling multiplicities, literal rational product, and actual inverse
  atom/coatom maps between projective bases and projective antichains.
- `IncidencePlane.lean`, `PlaneIndependence.lean`, `IncidencePlaneMatroid.lean`:
  arbitrary incidence-plane axioms, the proved independence augmentation,
  actual rank-three matroid, and noncollinear-three-point basis characterization.
- `IncidencePlaneClosure.lean`, `IncidencePlaneFlats.lean`,
  `IncidencePlaneFlatCounting.lean`: actual point/line closures, literal flat
  sets and incidence order, flat enumeration, and zero/singleton layers.
- `IncidencePlaneMaximum.lean`, `IncidencePlaneTriples.lean`: singleton
  parallel classes, consumption of the maximum-antichain theorem, unique-line
  fibres for collinear triples, the exact c3 formula and above-three vanishing.
- `IncidencePlaneJoins.lean`, `IncidencePlanePairData.lean`,
  `IncidencePlanePairBijection.lean`, `IncidencePlanePairCounting.lean`:
  literal top-join classification, actual ordered line and nonincident
  point-line cases, both orientations, and the earned pair normalization.
- `IncidencePlaneEnumeration.lean`: complete arbitrary-plane distribution
  and every higher empty layer, with no field or Desarguesian restriction.
- `MultigraphEnds.lean`, `MultigraphWalks.lean`, `MultigraphShortCycles.lean`:
  original Graph edge identities, actual vertices, labelled walks/cycles,
  one-edge loops, two-edge parallel cycles and the literal forest predicate.
- `MultigraphSupport.lean`, `MultigraphCycleLift.lean`,
  `MultigraphForestSupport.lean`: exact simple support, original incidence
  and isolated vertices, cycle lift/projection, and the proved forest
  equivalence retaining loop/parallel restrictions.
- `MultigraphForestEdges.lean`: actual forest-edge/support-edge bijection,
  edge count, and finiteness from the actual vertex set.
- `MultigraphReachability.lean`, `SimpleGraphComponentPartition.lean`,
  `ForestComponentCount.lean`: original labelled reachability and component
  bijection, exact vertex/edge component partitions, and |F|+c(F)=|V|.
- `GraphComponentMonotonicity.lean`, `MultigraphForestInsert.lean`:
  actual component quotient maps, existence of a connecting original edge,
  insertion across components and the forest augmentation axiom.
- `CycleMatroid.lean`, `CycleMatroidComponents.lean`: actual cycle matroid on
  the original edge ground, component-spanning basis characterization and
  the subtraction-free/displayed rank formulas.
- `MultigraphWalkLabels.lean`, `MultigraphSubgraphWalks.lean`,
  `MultigraphComponentPoints.lean`, `MultigraphClosedWalks.lean`: original
  label sequences, native subgraph walk/cycle transport, actual component
  vertex sets, and label-preserving restriction to closed component sets.
- `MultigraphSpanningForest.lean`, `CycleMatroidForests.lean`: the literal
  native tree-in-each-component definition, its proved equivalence with
  component spanning, actual finite original-edge-set base/forest bijection,
  cardinality and common edge size.
- `MultigraphConnectedInsert.lean`, `CycleMatroidSubsetBasis.lean`,
  `CycleMatroidClosure.lean`: exact connected insertion behavior, actual
  subset basis/rank producers and original endpoint-walk closure/flat criteria.
- `CycleMatroidLoops.lean`, `CycleMatroidParallel.lean`,
  `CycleMatroidRankOne.lean`, `GraphicSimplificationGround.lean`: actual
  loop flat, full original parallel classes, proved nonloop representatives
  and rank-one-flat/simple-edge ground bijection with exact inverse fibres.
  The full simplification matroid structure and final antichain/weight
  consumers are completed in the publication root.

## Verification

Run from the project parent of `lean4`:

```powershell
python .paper-infrastructure/paper_infrastructure.py --project . verification-receipt-verify --policy .paper-infrastructure/lean-publication-verification.json
```

If and only if the receipt is missing or stale, use the same runner's
`verification-receipt-run` command with the same `--policy`, an executing
`--agent-id`, `--agent-runtime`, and actual `--thread-id`. It rechecks the receipt
inside the exclusive lease, runs only the incremental target and axiom audit,
and signs the exact input/HEAD/command/output contract. Never bypass or break
its execution lease.

The audit accepts only `propext`, `Classical.choice`, and `Quot.sound`.
A valid publication-root receipt covers all forty-one registered root
declarations. The atomic receipt separately covers forty-nine unique claim
bindings, and the final formal-contract receipt covers the reviewed
manuscript correspondence.

The installed infrastructure is v6.1.0. The 184-unit bilingual review, the
105-occurrence atomic formal contract, submission preflight, build, postflight
and artifact gates all pass. Kernel receipts still certify only their exact
named Lean contracts; the correspondence receipt and publication gates supply
the broader manuscript evidence.

## Closure status

All twenty theorem-map rows are closed. The graphic carrier preserves original
edge labels, loops, parallels and isolated vertices; both partition rows retain
their corank conditions, Stirling/Cayley and Bell-series coefficients. Every
protected manuscript claim has an atomic binding or reviewed relation, and all
publication-root axioms have been audited.

`ProofEngineInterface.lean` packages the thirteen premise-free graph outputs.
`ProofEngineGraphInterface.lean` and `ProofEngineGraphProof.lean` form a
separate typed conditional layer for Proof Engine: every wrapper consumes
exactly its declared upstream claim axioms, while the publication root imports
neither graph file. The generated Proof Engine status has thirteen earned
edges and `target_closed=true`.
