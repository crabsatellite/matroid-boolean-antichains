import BooleanAntichainsKernel.Distributive
import BooleanAntichainsKernel.UnorderedFullHeight
import BooleanAntichainsKernel.BasisSpan
import BooleanAntichainsKernel.HeightGapEndpoints
import BooleanAntichainsKernel.SimplificationBases
import BooleanAntichainsKernel.RankProfiles
import BooleanAntichainsKernel.DistributivePolynomial
import BooleanAntichainsKernel.WeightedTheorem
import BooleanAntichainsKernel.IntervalTheorem
import BooleanAntichainsKernel.RankTightEnumeration
import BooleanAntichainsKernel.ProductConvolution
import BooleanAntichainsKernel.BooleanEnumeration
import BooleanAntichainsKernel.UniformRankTight
import BooleanAntichainsKernel.UniformSingletonCounting
import BooleanAntichainsKernel.UniformBlockBijection
import BooleanAntichainsKernel.UniformBlockProfiles
import BooleanAntichainsKernel.UniformRationalFormula
import BooleanAntichainsKernel.UniformNumericDistributions
import BooleanAntichainsKernel.SubspaceUnorderedCorrespondence
import BooleanAntichainsKernel.InternalOrderingCount
import BooleanAntichainsKernel.SubspaceDirectSumFormula
import BooleanAntichainsKernel.SubspaceCompletion
import BooleanAntichainsKernel.ProjectiveEnumeration
import BooleanAntichainsKernel.IncidencePlaneTriples
import BooleanAntichainsKernel.IncidencePlaneEnumeration
import BooleanAntichainsKernel.MultigraphForestEdges
import BooleanAntichainsKernel.CycleMatroidComponents
import BooleanAntichainsKernel.CycleMatroidForests
import BooleanAntichainsKernel.GraphicSimplificationGround
import BooleanAntichainsKernel.GraphicSpanEdges
import BooleanAntichainsKernel.GraphicSimplifiedComponents
import BooleanAntichainsKernel.GraphicConnected
import BooleanAntichainsKernel.PartitionAntichains
import BooleanAntichainsKernel.PartitionContractionBases
import BooleanAntichainsKernel.PartitionStirlingCayley
import BooleanAntichainsKernel.PartitionBellSquareSeries
import BooleanAntichainsKernel.PartitionPairsInitial67

/-!
The publication root imports premise-free producers for all twenty rows of
`../THEOREM_MAP.md`.  Atomic manuscript occurrence bindings and their
correspondence contract are maintained separately.
-/

namespace BooleanAntichainsKernel

open scoped Classical

theorem manuscript_lem_full_height {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] [GradeMinOrder ℕ L]
    {r : ℕ} (C : BooleanAntichain r L) (hr : grade ℕ (⊤ : L) = r) :
    C.1.inf id = ⊥ ∧
    (∀ c : Set (antichainSpan C.1), IsMaxChain (· ≤ ·) c →
      IsMaxChain (· ≤ ·) (Subtype.val '' c : Set L)) ∧
    (∀ i : C.1, grade ℕ (antichainMeetFace C.1 {i}) = 1) ∧
    (∀ i : C.1, grade ℕ i.1 = r - 1) :=
  unordered_full_height_rigidity C hr

theorem manuscript_lem_basis_span {α : Type*} [Fintype α]
    (M : Matroid α) (A : Finset (MatroidFlat M)) (hA : IsSimplifiedBasis M A) :
    (∀ S T : Finset A,
      S.sup Subtype.val ⊔ T.sup Subtype.val = (S ∪ T).sup Subtype.val ∧
      S.sup Subtype.val ⊓ T.sup Subtype.val = (S ∩ T).sup Subtype.val) ∧
    Function.Injective (fun S : Finset A ↦ S.sup (Subtype.val : A → MatroidFlat M)) :=
  simplified_basis_span A hA

theorem manuscript_thm_global_gap_criterion {L : Type*} [Fintype L]
    [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
    {k : ℕ} (H : Fin k → L) :
    IsBooleanTuple H ↔
      ReconstructedAtomsRise H ∧ ReconstructionGapsVanish H :=
  global_height_gap_criterion H

theorem manuscript_thm_global_gap_enumerator {L : Type*} [Fintype L]
    [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
    {k : ℕ} :
    Fintype.card (BooleanAntichain k L) =
      (∑ H : Fin k → L, globalCriterionIndicator H) / k.factorial :=
  global_height_gap_enumerator

/-- The whole displayed global theorem, including both boundary clauses. -/
theorem manuscript_thm_global_gap {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] (k : ℕ) :
    (∀ H : Fin k → L, IsBooleanTuple H ↔
      (∀ i, latticeHeight (commonMeet H) < latticeHeight (reconstructedAtom H i)) ∧
      (∀ S : Finset (Fin k), reconstructionGap H S = 0)) ∧
    Fintype.card (BooleanAntichain k L) =
      (∑ H : Fin k → L, literalCriterionIndicator H) / k.factorial ∧
    Fintype.card (BooleanAntichain 0 L) = 1 ∧
    (latticeHeight (⊤ : L) < k → Fintype.card (BooleanAntichain k L) = 0) :=
  ⟨literal_height_gap_criterion, literal_height_gap_enumerator k,
    booleanAntichain_count_zero, booleanAntichain_count_above_height k⟩

theorem manuscript_thm_size_two_structural {L : Type*}
    [Lattice L] [OrderTop L] (F G : L) :
    IsBooleanTuple (pairTuple F G) ↔ F ≠ ⊤ ∧ G ≠ ⊤ ∧ F ⊔ G = ⊤ :=
  pair_isBoolean_iff F G

theorem manuscript_thm_size_two_mobius {L : Type*} [Fintype L]
    [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
    [DecidableLE L] [DecidableLT L] :
    (Fintype.card (BooleanAntichain 2 L) : ℤ) =
      (mobiusPairSum (L := L) - 2 * (Fintype.card L : ℤ) + 1) / 2 :=
  mobius_formula_pairs

/-- The whole pair theorem, with the structural and Möbius clauses together. -/
theorem manuscript_thm_size_two {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] [DecidableLE L] [DecidableLT L] :
    (∀ F G : L, IsBooleanTuple (pairTuple F G) ↔ F ≠ ⊤ ∧ G ≠ ⊤ ∧ F ⊔ G = ⊤) ∧
    (Fintype.card (BooleanAntichain 2 L) : ℤ) =
      (mobiusPairSum (L := L) - 2 * (Fintype.card L : ℤ) + 1) / 2 :=
  ⟨pair_isBoolean_iff, mobius_formula_pairs⟩

/-- The maximum-antichain theorem, including the literal maps, both inverse
laws, and the standard Tutte evaluation on the actual simplification matroid. -/
theorem manuscript_thm_main {α : Type*} [Fintype α] (M : Matroid α) :
    (∀ C : MaximumBooleanAntichain M, (maximumAntichainToBasis C).1 = antichainAtoms C.1) ∧
    (∀ A : SimplifiedBasis M, (simplifiedBasisToAntichain A).1 = basisCoatoms A.1) ∧
    Function.LeftInverse (simplifiedBasisToAntichain (M := M)) maximumAntichainToBasis ∧
    Function.RightInverse (simplifiedBasisToAntichain (M := M)) maximumAntichainToBasis ∧
    Fintype.card (MaximumBooleanAntichain M) = Fintype.card (SimplifiedBasis M) ∧
    (Fintype.card (SimplifiedBasis M) : ℤ) =
      MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℤ))
        (matroidTuttePolynomial (simplificationOnFlats M)) := by
  refine ⟨fun _ ↦ rfl, fun _ ↦ rfl, maximumAntichainEquivSimplifiedBasis.left_inv,
    maximumAntichainEquivSimplifiedBasis.right_inv,
    maximumAntichain_count_eq_simplifiedBases, ?_⟩
  rw [simplifiedBasis_count_eq_actualMatroidBases,
    matroidTutte_at_one_eq_number_of_bases]

theorem manuscript_cor_rank_profile {α : Type*} [Fintype α] (M : Matroid α)
    {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    antichainRankProfile C ∅ = 0 ∧ StrictMono (antichainRankProfile C) ∧
    (∀ S T : Finset C.1,
      antichainRankProfile C (S ∩ T) + antichainRankProfile C (S ∪ T) ≤
        antichainRankProfile C S + antichainRankProfile C T) ∧
    (IsRankTight C ↔ ∀ S : Finset C.1, antichainRankProfile C S = S.card) :=
  antichain_rank_profile C

noncomputable def manuscript_thm_distributive_bijection {P : Type*}
    [PartialOrder P] [Fintype P] {k : ℕ} :
    BooleanAntichain k (LowerSet P) ≃ DisjointFilterFamily k P :=
  distributiveAntichainEquivDisjointFilters

theorem manuscript_thm_distributive_independence {P : Type*}
    [PartialOrder P] [Fintype P] {k : ℕ} :
    Fintype.card (BooleanAntichain k (LowerSet P)) =
      filterIntersectionIndependenceCoeff (P := P) k :=
  distributive_independence_coefficient

/-- The full distributive theorem: the size-preserving complement bijections
and the literal intersection-graph independence polynomial identity. -/
theorem manuscript_thm_distributive (P : Type*) [PartialOrder P] [Fintype P] :
    (∀ k : ℕ, Function.Bijective
      (fun C : BooleanAntichain k (LowerSet P) ↦
        (distributiveAntichainEquivDisjointFilters C : DisjointFilterFamily k P))) ∧
    (∀ (k : ℕ) (C : BooleanAntichain k (LowerSet P)),
      (distributiveAntichainEquivDisjointFilters C).1 = lowerFinsetToUpperFinset C.1) ∧
    booleanAntichainPolynomial (LowerSet P) = graphIndependencePolynomial (filterIntersectionGraph P) :=
  ⟨fun _ ↦ distributiveAntichainEquivDisjointFilters.bijective, fun _ _ ↦ rfl,
    distributive_polynomial_identity P⟩

/-- The full parallel-class decomposition: symbolic polynomial and exact
unweighted count, with the actual span atoms and classes `A \ cl_M(∅)`. -/
theorem manuscript_thm_weighted {α : Type*} [Fintype α] (M : Matroid α) :
    matroidBasisPolynomial M =
      (∑ C : MaximumBooleanAntichain M,
        ∏ A ∈ spanAtomFinset C.1, ∑ e ∈ parallelClassElements A,
          (MvPolynomial.X e : MvPolynomial α ℤ)) ∧
    Fintype.card (MatroidBases M) =
      ∑ C : MaximumBooleanAntichain M,
        ∏ A ∈ spanAtomFinset C.1, (parallelClassElements A).card :=
  ⟨weighted_basis_polynomial M, weighted_basis_count M⟩

/-- The full interval theorem with the actual minor `(M|Y)/X`, the actual
interval carrier, and the literal class factors `A \ X`. -/
theorem manuscript_thm_interval {α : Type*} [Fintype α] (M : Matroid α)
    (X Y : MatroidFlat M) [Fact (X ≤ Y)] :
    Function.Bijective (intervalAntichainEquivBasis X Y) ∧
    matroidBasisPolynomial (flatIntervalMinor X Y) =
      ∑ C : IntervalBooleanAntichain X Y,
        ∏ A ∈ spanAtomFinset C.1, ∑ e ∈ (A.1.1 \ X.1).toFinset,
          (MvPolynomial.X e : MvPolynomial α ℤ) :=
  ⟨(intervalAntichainEquivBasis X Y).bijective, interval_weighted_basis_polynomial X Y⟩

/-- The literal bottom partition and the full corank sum of `cor:rank-tight`.
The integer corank condition retains the empty layers above matroid rank. -/
theorem manuscript_cor_rank_tight {α : Type*} [Fintype α] (M : Matroid α) (k : ℕ) :
    (∀ C : RankTightAntichain M k, (rankTightEquivBottomFibers C).1.1 = C.1.1.inf id) ∧
    (∀ (X : MatroidFlat M) (hX : HasCorank M k X),
      Function.Bijective (bottomFiberEquivActualContractionBases k X hX)) ∧
    Fintype.card (RankTightAntichain M k) =
      (∑ X ∈ Finset.univ.filter (fun X : MatroidFlat M ↦
        (MatroidFlat.rank X : ℤ) = (MatroidFlat.rank (⊤ : MatroidFlat M) : ℤ) - (k : ℤ)),
        Fintype.card (MatroidBases (simplificationOnFlats (M.contract X.1)))) ∧
    (MatroidFlat.rank (⊤ : MatroidFlat M) < k → Fintype.card (RankTightAntichain M k) = 0) := by
  refine ⟨rankTightEquivBottomFibers_index,
    fun X hX ↦ (bottomFiberEquivActualContractionBases k X hX).bijective,
    ?_, rankTight_count_above_rank M k⟩
  have hfilter : Finset.univ.filter (HasCorank M k) =
      Finset.univ.filter (fun X : MatroidFlat M ↦
        (MatroidFlat.rank X : ℤ) = (MatroidFlat.rank (⊤ : MatroidFlat M) : ℤ) - (k : ℤ)) := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, HasCorank]
  rw [← hfilter]
  exact rankTight_count_actual_simplification M k

/-- The transform clause of the product theorem, retained as a named consumer. -/
theorem manuscript_thm_product_transform {L K : Type*}
    [Fintype L] [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
    [Fintype K] [DecidableEq K] [Lattice K] [OrderBot K] [OrderTop K] (k : ℕ) :
    etaCount k (L × K) = etaCount k L * etaCount k K := etaCount_product k

/-- Both displayed equations of the full lattice-product theorem. The
convolution consumes the actual active-cover bijection and exact factorial
normalization; no product count is introduced as a premise. -/
theorem manuscript_thm_product {L K : Type*}
    [Fintype L] [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
    [Fintype K] [DecidableEq K] [Lattice K] [OrderBot K] [OrderTop K] (k : ℕ) :
    etaCount k (L × K) = etaCount k L * etaCount k K ∧
    (Fintype.card (BooleanAntichain k (L × K)) : ℚ) =
      ∑ a ∈ Finset.range (k + 1),
        ∑ b ∈ (Finset.range (k + 1)).filter (fun b ↦ k ≤ a + b),
          ((a.factorial : ℚ) * (b.factorial : ℚ) /
            ((k - a).factorial * (k - b).factorial * (a + b - k).factorial : ℚ)) *
            (Fintype.card (BooleanAntichain a L) : ℚ) *
            (Fintype.card (BooleanAntichain b K) : ℚ) :=
  ⟨etaCount_product k, productAntichain_count_convolution k⟩

/-- The rank-tight clause retained as a named consumer. -/
theorem manuscript_cor_boolean_lattice_tight (n k : ℕ) :
    Fintype.card (BooleanLatticeRankTightAntichain (Fin n) k) = n.choose k := by
  simpa using booleanLattice_rankTight_count (α := Fin n) k

/-- The full Boolean-lattice corollary, with the cited total count now proved
from the paper's product recurrence and the actual complementary subtype. -/
theorem manuscript_cor_boolean_lattice (n k : ℕ) :
    Fintype.card (BooleanLatticeRankTightAntichain (Fin n) k) = n.choose k ∧
    Fintype.card (BooleanAntichain k (Finset (Fin n))) = Nat.stirlingSecond (n + 1) (k + 1) ∧
    Fintype.card (BooleanLatticeNonRankTightAntichain (Fin n) k) =
      Nat.stirlingSecond (n + 1) (k + 1) - n.choose k :=
  booleanLattice_enumeration n k

/-- All displayed uniform rank-tight branches, plus the above-rank empty
layers, on the actual uniform matroid over Fin n. -/
theorem manuscript_cor_uniform_tight (n r : ℕ) (hr2 : 2 ≤ r) (hrn : r ≤ n) :
    Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) 0) = 1 ∧
    Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) 1) =
      n.choose (r - 1) ∧
    (∀ k : ℕ, 2 ≤ k → k ≤ r →
      Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) k) =
        n.choose r * r.choose k) ∧
    (∀ k : ℕ, r < k →
      Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) k) = 0) :=
  uniform_rankTight_enumeration n r hr2 hrn

/-- Structural and boundary clauses retained as named consumers. The full
formula and numeric distributions are collected in manuscript_thm_uniform_all. -/
theorem manuscript_thm_uniform_all_structure (n r : ℕ) (hr : 1 ≤ r ∧ r ≤ n) :
    Fintype.card (BooleanAntichain 0 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) = 1 ∧
    Fintype.card (BooleanAntichain 1 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
      (∑ b ∈ Finset.range r, n.choose b) ∧
    (∀ k : ℕ, 2 ≤ k → k ≤ r →
      Function.Bijective
        (fun D : UniformBlockData (Set.univ : Set (Fin n)) r k ↦ D.toEmbedding) ∧
      Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
        Fintype.card (UniformBlockData (Set.univ : Set (Fin n)) r k) / k.factorial ∧
      ∀ D : UniformBlockData (Set.univ : Set (Fin n)) r k,
        UniformProfileValid n r k D.bottom.card (fun i ↦ (D.blocks i).card)) := by
  have hrE : r ≤ (Set.univ : Set (Fin n)).ncard := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using hr.2
  refine ⟨booleanAntichain_count_zero, uniform_singleton_count n r hr.2, ?_⟩
  intro k hk _hkr
  refine ⟨(uniformBlocksEquivTopEmbedding hrE hk).bijective, uniformAntichain_count_blocks hrE hk, ?_⟩
  intro D
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using D.profile_valid

/-- The complete all-size uniform theorem: both boundary layers, the
literal rational block coefficient under the paper's ranges, and both
displayed numerical distributions. -/
theorem manuscript_thm_uniform_all :
    (∀ r n : ℕ, 1 ≤ r → r ≤ n →
      Fintype.card (BooleanAntichain 0 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) = 1 ∧
      Fintype.card (BooleanAntichain 1 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
        (∑ b ∈ Finset.range r, n.choose b) ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ r →
        (Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) : ℚ) =
          (1 / (k.factorial : ℚ)) *
            ∑ b ∈ Finset.range r, (n.choose b : ℚ) *
              ∑ p : UniformAdmissibleProfile n r k b,
                ((n - b).factorial : ℚ) /
                  (((n - b - ∑ i, p.1 i).factorial : ℚ) * ∏ i, ((p.1 i).factorial : ℚ))) ∧
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3)))) =
      [1, 11, 27, 4] ∧
    List.ofFn (fun k : Fin 5 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4)))) =
      [1, 26, 150, 50, 5] := by
  refine ⟨?_, uniform34_distribution, uniform45_distribution⟩
  intro r n _hr1 hrn
  refine ⟨booleanAntichain_count_zero, uniform_singleton_count n r hrn, ?_⟩
  intro k hk _hkr
  exact uniform_all_size_formula_rational n r k hrn hk

/-- The literal unordered correspondence and its dimension/factorial
contracts, retained as a named consumer of the full subspace root below. -/
theorem manuscript_thm_subspace_correspondence (K : Type*) [Field K] [Fintype K] (n k : ℕ) :
    Function.Bijective
      (subspaceUnorderedSigmaEquiv (R := K) (V := Fin n → K) k).symm ∧
    (∀ C : BooleanAntichain k (Submodule K (Fin n → K)),
      ((subspaceUnorderedSigmaEquiv k).symm C).1 = C.1.inf id ∧
      ((subspaceUnorderedSigmaEquiv k).symm C).2.1 =
        (antichainAtoms C.1).image (fun A ↦ A.map (C.1.inf id).mkQ)) ∧
    (∀ (X : Submodule K (Fin n → K))
      (D : UnorderedInternalDecomposition K ((Fin n → K) ⧸ X) k),
      k ≤ Module.finrank K ((Fin n → K) ⧸ X) ∧
      Module.finrank K ((Fin n → K) ⧸ X) ≤ n ∧
      (subspaceUnorderedSigmaEquiv k ⟨X, D⟩).1 =
        D.1.image (fun U ↦ ((D.1.erase U).sup id).comap X.mkQ)) ∧
    Fintype.card (BooleanAntichain k (Submodule K (Fin n → K))) =
      (∑ X : Submodule K (Fin n → K),
        Fintype.card (UnorderedInternalDecomposition K ((Fin n → K) ⧸ X) k)) ∧
    (∀ X : Submodule K (Fin n → K),
      Fintype.card (OrderedInternalDecomposition K ((Fin n → K) ⧸ X) k) =
        Fintype.card (UnorderedInternalDecomposition K ((Fin n → K) ⧸ X) k) * k.factorial) ∧
    Fintype.card (BooleanAntichain 0 (Submodule K (Fin n → K))) = 1 := by
  refine ⟨(subspaceUnorderedSigmaEquiv (R := K) (V := Fin n → K) k).symm.bijective,
    ?_, ?_, subspace_count_by_unordered_quotients k, ?_, booleanAntichain_count_zero⟩
  · intro C
    exact ⟨subspaceUnorderedSigmaEquiv_symm_index C, subspaceUnorderedSigmaEquiv_atoms C⟩
  · intro X D
    have hd := standardSubspace_unordered_codimension_bounds n k X D
    exact ⟨hd.1, hd.2, subspaceUnorderedSigmaEquiv_coatom_formula X D⟩
  · intro X
    exact orderedInternal_count_eq_unordered_mul_factorial

/-- The actual GL/orbit/stabilizer calculation and the direct-sum
coefficient in the subspace proof, retained as a named consumer below. -/
theorem manuscript_thm_subspace_direct_sum_count (K : Type*) [Field K] [Fintype K] :
    (∀ d : ℕ, generalLinearCard K d =
      ∏ i : Fin d, ((Fintype.card K) ^ d - (Fintype.card K) ^ i.1)) ∧
    generalLinearCard K 0 = 1 ∧
    (∀ d k : ℕ, 1 ≤ k → k ≤ d →
      (Fintype.card (UnorderedInternalDecomposition K (Fin d → K) k) : ℚ) =
        (1 / (k.factorial : ℚ)) *
          ∑ p : PositiveDimensionProfile d k,
            (generalLinearCard K d : ℚ) / ∏ i, (generalLinearCard K (p.1 i) : ℚ)) ∧
    (∀ n k : ℕ, 1 ≤ k →
      (Fintype.card (BooleanAntichain k (Submodule K (Fin n → K))) : ℚ) =
        ∑ X : Submodule K (Fin n → K),
          directSumProfileCount K (Module.finrank K ((Fin n → K) ⧸ X)) k) := by
  refine ⟨generalLinearCard_product K, generalLinearCard_zero K, ?_, ?_⟩
  · intro d k _hk _hkd
    exact standardInternal_count_by_dimensions K d k
  · intro n k _hk
    exact subspace_count_by_directSumProfiles (K := K) (V := Fin n → K) k

/-- The full subspace theorem: literal inverse quotient/summand maps,
dimension bounds, GL/profile coefficient, Gaussian total, zero layer,
top-layer product specialization and the displayed binary example.
The separately stated projective-geometry carrier theorem remains separate. -/
theorem manuscript_thm_subspace :
    (∀ (K : Type*) [Field K] [Fintype K] (n k : ℕ),
      Function.Bijective
        (subspaceUnorderedSigmaEquiv (R := K) (V := Fin n → K) k).symm ∧
      (∀ C : BooleanAntichain k (Submodule K (Fin n → K)),
        ((subspaceUnorderedSigmaEquiv k).symm C).1 = C.1.inf id ∧
        ((subspaceUnorderedSigmaEquiv k).symm C).2.1 =
          (antichainAtoms C.1).image (fun A ↦ A.map (C.1.inf id).mkQ)) ∧
      (∀ (X : Submodule K (Fin n → K))
        (D : UnorderedInternalDecomposition K ((Fin n → K) ⧸ X) k),
        k ≤ Module.finrank K ((Fin n → K) ⧸ X) ∧
        Module.finrank K ((Fin n → K) ⧸ X) ≤ n ∧
        (subspaceUnorderedSigmaEquiv k ⟨X, D⟩).1 =
          D.1.image (fun U ↦ ((D.1.erase U).sup id).comap X.mkQ)) ∧
      (1 ≤ k → (Fintype.card (BooleanAntichain k (Submodule K (Fin n → K))) : ℚ) =
        ∑ d ∈ Finset.Icc k n,
          gaussianCoefficient (Fintype.card K) n d * directSumProfileCount K d k) ∧
      Fintype.card (BooleanAntichain 0 (Submodule K (Fin n → K))) = 1) ∧
    (∀ (K : Type*) [Field K] [Fintype K],
      (∀ d : ℕ, generalLinearCard K d =
        ∏ i : Fin d, ((Fintype.card K) ^ d - (Fintype.card K) ^ i.1)) ∧
      generalLinearCard K 0 = 1 ∧
      ∀ d k : ℕ, 1 ≤ k → k ≤ d →
        (Fintype.card (UnorderedInternalDecomposition K (Fin d → K) k) : ℚ) =
          (1 / (k.factorial : ℚ)) *
            ∑ p : PositiveDimensionProfile d k,
              (generalLinearCard K d : ℚ) / ∏ i, (generalLinearCard K (p.1 i) : ℚ)) ∧
    (∀ (K : Type*) [Field K] [Fintype K] (n : ℕ), 1 ≤ n →
      (Fintype.card (BooleanAntichain n (Submodule K (Fin n → K))) : ℚ) =
        (1 / (n.factorial : ℚ)) * ∏ i : Fin n,
          (((Fintype.card K : ℚ) ^ n - (Fintype.card K : ℚ) ^ i.1) /
            ((Fintype.card K : ℚ) - 1))) ∧
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (Submodule (ZMod 2) (Fin 3 → ZMod 2)))) = [1, 15, 49, 28] := by
  refine ⟨?_, ?_, ?_, subspaceF23_distribution⟩
  · intro K _ _ n k
    have h := manuscript_thm_subspace_correspondence K n k
    exact ⟨h.1, h.2.1, h.2.2.1, standardSubspace_all_size_formula K n k,
      booleanAntichain_count_zero⟩
  · intro K _ _
    have h := manuscript_thm_subspace_direct_sum_count K
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro K _ _ n hn
    exact standardSubspace_top_product K n hn

/-- The projective-count equation on actual projective subspaces and
actual unordered independent projective points. The point/scalar and
labelling fibres are consumed by the two displayed cardinality equalities. -/
theorem manuscript_eq_projective_count (K : Type*) [Field K] [Fintype K]
    (r : ℕ) (hr : 1 ≤ r) :
    Function.Bijective (projectiveAntichainEquivBasis (K := K) (V := Fin r → K) (k := r)
      (by simp only [Module.finrank_fin_fun])) ∧
    (∀ C : BooleanAntichain r (Projectivization.Subspace K (Fin r → K)),
      (projectiveAntichainEquivBasis (by simp only [Module.finrank_fin_fun]) C).1.image
        Projectivization.submodule =
          mapFamily projectiveSubspaceOrderIso (antichainAtoms C.1)) ∧
    (∀ B : ProjectiveIndependentSet K (Fin r → K) r,
      ((projectiveAntichainEquivBasis (by simp only [Module.finrank_fin_fun])).symm B).1 =
        mapFamily projectiveSubspaceOrderIso.symm
          (basisCoatoms (B.1.image Projectivization.submodule))) ∧
    (Fintype.card (ProjectiveIndependentSet K (Fin r → K) r) : ℚ) =
      (1 / (r.factorial : ℚ)) * ∏ i : Fin r,
        (((Fintype.card K : ℚ) ^ r - (Fintype.card K : ℚ) ^ i.1) /
          ((Fintype.card K : ℚ) - 1)) ∧
    (Fintype.card (BooleanAntichain r (Projectivization.Subspace K (Fin r → K))) : ℚ) =
      (1 / (r.factorial : ℚ)) * ∏ i : Fin r,
        (((Fintype.card K : ℚ) ^ r - (Fintype.card K : ℚ) ^ i.1) /
          ((Fintype.card K : ℚ) - 1)) := by
  have hd : r = Module.finrank K (Fin r → K) := by simp only [Module.finrank_fin_fun]
  exact ⟨(projectiveAntichainEquivBasis hd).bijective,
    projectiveAntichainEquivBasis_atoms hd, projectiveAntichainEquivBasis_coatoms hd,
    standardProjectiveBasis_product K r hr, standardProjectiveAntichain_product K r hr⟩

/-- Incidence-only foundations and retained zero, singleton and maximum
clauses. The full general-plane equation is collected in the root below. -/
theorem manuscript_eq_projective_plane_structure
    (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L] :
    (∀ F : Set P, (incidencePlaneMatroid P L).IsFlat F ↔
      F = ∅ ∨ (∃ p : P, F = {p}) ∨ (∃ l : L, F = planeLineSet l) ∨ F = Set.univ) ∧
    matroidRank (incidencePlaneMatroid P L) (incidencePlaneMatroid P L).E = 3 ∧
    (∀ B : Set P, (incidencePlaneMatroid P L).IsBase B ↔
      B.ncard = 3 ∧ ¬ PlaneCollinear L B) ∧
    (∀ (p : P) (l : L), incidencePlanePointFlat (L := L) p ≤ incidencePlaneLineFlat (P := P) l ↔ p ∈ l) ∧
    Fintype.card (BooleanAntichain 0 (MatroidFlat (incidencePlaneMatroid P L))) = 1 ∧
    Fintype.card (BooleanAntichain 1 (MatroidFlat (incidencePlaneMatroid P L))) =
      2 * (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1) + 1 ∧
    Fintype.card (BooleanAntichain 3 (MatroidFlat (incidencePlaneMatroid P L))) =
      (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1).choose 3 -
        (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1) *
          (Configuration.ProjectivePlane.order P L + 1).choose 3 ∧
    (∀ k : ℕ, 3 < k →
      Fintype.card (BooleanAntichain k (MatroidFlat (incidencePlaneMatroid P L))) = 0) := by
  exact ⟨incidencePlaneMatroid_isFlat_iff, incidencePlaneMatroid_rank,
    incidencePlaneMatroid_isBase_iff, incidencePlanePointFlat_le_lineFlat,
    incidencePlane_zero_count, incidencePlane_singleton_count, incidencePlane_three_count,
    incidencePlane_count_above_three⟩

/-- The complete general projective-plane equation, on the actual
incidence matroid and its actual flat sets, including non-Desarguesian
planes. All point/line counts and all higher empty layers are explicit. -/
theorem manuscript_eq_projective_plane_all
    (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L] :
    let q := Configuration.ProjectivePlane.order P L
    let N := q ^ 2 + q + 1
    (Fintype.card P = N ∧ Fintype.card L = N) ∧
    (∀ F : Set P, (incidencePlaneMatroid P L).IsFlat F ↔
      F = ∅ ∨ (∃ p : P, F = {p}) ∨ (∃ l : L, F = planeLineSet l) ∨ F = Set.univ) ∧
    matroidRank (incidencePlaneMatroid P L) (incidencePlaneMatroid P L).E = 3 ∧
    (∀ B : Set P, (incidencePlaneMatroid P L).IsBase B ↔
      B.ncard = 3 ∧ ¬ PlaneCollinear L B) ∧
    (∀ (p : P) (l : L), incidencePlanePointFlat (L := L) p ≤ incidencePlaneLineFlat (P := P) l ↔ p ∈ l) ∧
    Function.Bijective (planeJoinPairEquiv (P := P) (L := L)) ∧
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (incidencePlaneMatroid P L)))) =
        [1, 2 * N + 1, N.choose 2 + N * q ^ 2, N.choose 3 - N * (q + 1).choose 3] ∧
    (∀ k : ℕ, 3 < k →
      Fintype.card (BooleanAntichain k (MatroidFlat (incidencePlaneMatroid P L))) = 0) := by
  dsimp only
  exact ⟨⟨plane_card_points, plane_card_lines⟩, incidencePlaneMatroid_isFlat_iff,
    incidencePlaneMatroid_rank, incidencePlaneMatroid_isBase_iff, incidencePlanePointFlat_le_lineFlat,
    (planeJoinPairEquiv (P := P) (L := L)).bijective, incidencePlane_distribution,
    incidencePlane_count_above_three⟩

/-- Literal multigraph/forest carrier foundations for the graphic
corollary. No cycle-matroid, basis, component-rank or weighted closure is
claimed by this partial root. -/
theorem manuscript_cor_graphic_carriers {α β : Type*} (G : Graph α β) (F : Set β) :
    (∀ (e : G.edgeSet) (x y : G.vertexSet),
      graphEdgeEnds G e = s(x, y) ↔ G.IsLink e.1 x.1 y.1) ∧
    (∀ e : G.edgeSet, (graphEdgeEnds G e).IsDiag ↔ ∃ x : α, G.IsLoopAt e.1 x) ∧
    (∀ e f : G.edgeSet, graphEdgeEnds G e = graphEdgeEnds G f ↔
      ∃ x y : α, G.IsLink e.1 x y ∧ G.IsLink f.1 x y) ∧
    (∀ x y : G.vertexSet, (graphSimplification G).Adj x y ↔ x ≠ y ∧ G.Adj x.1 y.1) ∧
    (GraphEdgeForest G F ↔ F ⊆ G.edgeSet ∧
      (∀ e ∈ F, ∀ x : α, ¬G.IsLoopAt e x) ∧
      Set.InjOn (graphEdgeEnds G) {e : G.edgeSet | e.1 ∈ F} ∧ (graphSupport G F).IsAcyclic) ∧
    (∀ hF : GraphEdgeForest G F, Function.Bijective (forestEdgesEquivSupport hF) ∧
      F.ncard = Nat.card (graphSupport G F).edgeSet) ∧
    (∀ (_ : Finite G.vertexSet), GraphEdgeForest G F → F.Finite) := by
  refine ⟨graphEdgeEnds_eq_iff, graphEdgeEnds_isDiag_iff G, graphEdgeEnds_eq_iff_same_link G,
    graphSimplification_adj G, graphEdgeForest_iff_support, ?_, ?_⟩
  · intro hF
    exact ⟨(forestEdgesEquivSupport hF).bijective, forest_edge_ncard hF⟩
  · intro hV hF
    letI := hV
    exact hF.finite

/-- Checked cycle-matroid and original component producers for the
graphic corollary, retained alongside the literal spanning-tree bridge
below. Simplification and the antichain/weight consumers remain separate. -/
theorem manuscript_cor_graphic_cycle_matroid {α β : Type*} (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    (∀ (F : Set β) (x y : G.vertexSet),
      GraphReachable G F x y ↔ (graphSupport G F).Reachable x y) ∧
    (∀ F : Set β, graphComponentCount G F = Nat.card (graphSupport G F).ConnectedComponent) ∧
    (∀ F : Set β, GraphEdgeForest G F → F.ncard + graphComponentCount G F = G.vertexSet.ncard) ∧
    (cycleMatroid G).E = G.edgeSet ∧
    (∀ F : Set β, (cycleMatroid G).Indep F ↔ GraphEdgeForest G F) ∧
    (∀ B : Set β, (cycleMatroid G).IsBase B ↔ GraphEdgeForest G B ∧
      ∀ x y : G.vertexSet, GraphReachable G B x y ↔ GraphReachable G G.edgeSet x y) ∧
    matroidRank (cycleMatroid G) (cycleMatroid G).E + graphConnectedComponentCount G = G.vertexSet.ncard ∧
    matroidRank (cycleMatroid G) (cycleMatroid G).E =
      G.vertexSet.ncard - graphConnectedComponentCount G := by
  exact ⟨graphReachable_iff_support G, graphComponentCount_eq_support G,
    fun _ hF ↦ graphForest_component_count hF, cycleMatroid_ground G,
    cycleMatroid_indep_iff G, cycleMatroid_isBase_iff_spans_components G,
    cycleMatroid_rank_add_components G, cycleMatroid_rank G⟩

/-- The paper's actual componentwise spanning forests are identified
with cycle-matroid bases on the same original edge sets. This remains a
partial graphic root until simplification and antichain/weight consumers. -/
theorem manuscript_cor_graphic_spanning_forests {α β : Type*} (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    (∀ F : Set β, (cycleMatroid G).IsBase F ↔ F ⊆ G.edgeSet ∧
      ∀ c : GraphWalkComponent G G.edgeSet,
        LabelledGraphTree ((G.restrict F).induce (graphComponentPoints G c))) ∧
    Function.Bijective (cycleMatroidBasesEquivSpanningForests G) ∧
    (∀ B : MatroidBases (cycleMatroid G), (cycleMatroidBasesEquivSpanningForests G B).1 = B.1) ∧
    (∀ F : GraphSpanningForests G, ((cycleMatroidBasesEquivSpanningForests G).symm F).1 = F.1) ∧
    Nat.card (MatroidBases (cycleMatroid G)) = Fintype.card (GraphSpanningForests G) ∧
    (∀ F : GraphSpanningForests G, F.1.card = G.vertexSet.ncard - graphConnectedComponentCount G) := by
  exact ⟨cycleMatroid_isBase_iff_spanningForest G,
    (cycleMatroidBasesEquivSpanningForests G).bijective,
    cycleMatroidBasesEquivSpanningForests_val G, cycleMatroidBasesEquivSpanningForests_symm_val G,
    cycleMatroid_spanningForest_count G, graphSpanningForest_card G⟩

/-- Actual closure, loops, parallel classes and simplification ground
for the graphic corollary. The simplification matroid structure and the
maximum-antichain/weighted endpoint consumers are not asserted here. -/
theorem manuscript_cor_graphic_simplification_ground {α β : Type*} (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    (∀ X : Set β, X ⊆ G.edgeSet → (cycleMatroid G).closure X =
      {e : β | ∃ x y : G.vertexSet, G.IsLink e x.1 y.1 ∧ GraphReachable G X x y}) ∧
    (∀ X : Set β, X ⊆ G.edgeSet →
      matroidRank (cycleMatroid G) X + graphComponentCount G X = G.vertexSet.ncard) ∧
    (∀ e : β, (cycleMatroid G).IsLoop e ↔ ∃ x : α, G.IsLoopAt e x) ∧
    (∀ e : G.edgeSet, (cycleMatroid G).IsNonloop e.1 →
      (cycleMatroid G).closure {e.1} \ (cycleMatroid G).loops =
        {f : β | ∃ x y : α, G.IsLink e.1 x y ∧ G.IsLink f x y}) ∧
    Function.Bijective (cycleRankOneEquivSimpleEdges G) ∧
    (∀ (t : (graphSimplification G).edgeSet) (f : G.edgeSet),
      f.1 ∈ ((cycleRankOneEquivSimpleEdges G).symm t).1.1 \ (cycleMatroid G).loops ↔
        graphEdgeEnds G f = t.1) := by
  exact ⟨cycleMatroid_closure_eq G, cycleMatroid_rank_set_add_components G,
    cycleMatroid_isLoop_iff G, cycleMatroid_parallelClass_eq G,
    (cycleRankOneEquivSimpleEdges G).bijective, cycleRankOneEquivSimpleEdges_symm_class G⟩


section GraphicFiniteGround

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

/-- The original-variable weighted and size clauses of the graphic
corollary. The remaining forest-bijection/simplicity/connectedness clauses
are not asserted by this partial root. -/
theorem manuscript_cor_graphic_weights {α β : Type*} (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    (∀ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G)),
      C.1.card = G.vertexSet.ncard - graphConnectedComponentCount G) ∧
    (∀ (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G))) (A : MatroidFlat (cycleMatroid G)),
      A ∈ spanAtomFinset C.1 → MatroidFlat.rank A = 1) ∧
    (∀ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G)), Function.Injective (graphSpanAtomEdge G C)) ∧
    (∀ (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G))) (t : (graphSimplification G).edgeSet),
      t ∈ graphMaximumSpanEdges G C ↔
        ((cycleRankOneEquivSimpleEdges G).symm t).1 ∈ spanAtomFinset C.1) ∧
    (∀ (t : (graphSimplification G).edgeSet) (e : β),
      e ∈ graphParallelEdgeClass G t ↔
        ∃ x y : G.vertexSet, t.1 = s(x, y) ∧ G.IsLink e x.1 y.1) ∧
    (∀ (R : Type*) [CommSemiring R] (x : β → R),
      (∑ F : GraphSpanningForests G, ∏ e ∈ F.1, x e) =
        ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
            (MatroidFlat (cycleMatroid G)),
          ∏ t ∈ graphMaximumSpanEdges G C, ∑ e ∈ graphParallelEdgeClass G t, x e) ∧
    graphSpanningForestPolynomial G =
      ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
          (MatroidFlat (cycleMatroid G)),
        ∏ t ∈ graphMaximumSpanEdges G C, ∑ e ∈ graphParallelEdgeClass G t,
          (MvPolynomial.X e : MvPolynomial β ℤ) := by
  refine ⟨graphMaximumAntichain_card G, graphMaximumAntichain_spanAtom_rank G,
    graphSpanAtomEdge_injective G, graphMaximumSpanEdges_mem G,
    graphParallelEdgeClass_mem G, ?_, graphic_spanningForestPolynomial_parallel_edge_expansion G⟩
  intro R _ x
  exact graphic_weighted_parallel_edge_expansion G x

end GraphicFiniteGround

/-- Native simplified graph and its actual cycle matroid, on unchanged
original vertices. The identification with the rank-one-flat simplification
matroid and the maximum-antichain bijection remain separate obligations. -/
theorem manuscript_cor_graphic_simplified_graph {α β : Type*} (G : Graph α β)
    [Finite G.vertexSet] :
    (graphSimplifiedGraph G).vertexSet = G.vertexSet ∧
    (graphSimplifiedGraph G).edgeSet = (graphSimplification G).edgeSet ∧
    (∀ (q : Sym2 G.vertexSet) (x y : G.vertexSet),
      (graphSimplifiedGraph G).IsLink q x.1 y.1 ↔
        q = s(x, y) ∧ (graphSimplification G).Adj x y) ∧
    (∀ T : Set (Sym2 G.vertexSet),
      (cycleMatroid (graphSimplifiedGraph G)).Indep T ↔
        T ⊆ (graphSimplification G).edgeSet ∧ (SimpleGraph.fromEdgeSet T).IsAcyclic) ∧
    (∀ x y : G.vertexSet,
      GraphReachable (graphSimplifiedGraph G) (graphSimplifiedGraph G).edgeSet x y ↔
        GraphReachable G G.edgeSet x y) ∧
    Function.Bijective (graphSimplifiedComponentsEquiv G) ∧
    graphConnectedComponentCount (graphSimplifiedGraph G) = graphConnectedComponentCount G ∧
    (∀ T : Set (Sym2 G.vertexSet),
      GraphSpanningForest (graphSimplifiedGraph G) T ↔
        T ⊆ (graphSimplification G).edgeSet ∧ (SimpleGraph.fromEdgeSet T).IsAcyclic ∧
          ∀ x y : G.vertexSet,
            (SimpleGraph.fromEdgeSet T).Reachable x y ↔ (graphSimplification G).Reachable x y) ∧
    (∀ T : Set (Sym2 G.vertexSet),
      (cycleMatroid (graphSimplifiedGraph G)).IsBase T ↔
        GraphSpanningForest (graphSimplifiedGraph G) T) := by
  exact ⟨graphSimplifiedGraph_vertexSet G, graphSimplifiedGraph_edgeSet G,
    graphSimplifiedGraph_isLink G, graphSimplifiedGraph_cycleMatroid_indep G,
    graphSimplifiedGraph_reachable_original G, (graphSimplifiedComponentsEquiv G).bijective,
    graphSimplifiedGraph_component_count G, graphSimplifiedGraph_spanningForest_iff G,
    cycleMatroid_isBase_iff_spanningForest (graphSimplifiedGraph G)⟩


section GraphicComplete

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

/-- The full spanning-forest corollary: exact simplification matroid,
literal antichain/forest map, size, simple and connected specializations,
and the original-variable parallel-class polynomial. -/
theorem manuscript_cor_graphic {α β : Type*} (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    simplificationOnFlats ((cycleMatroid G).restrictSubtype (cycleMatroid G).E) =
      (cycleMatroid (graphSimplifiedGraph G)).comap (graphicGroundSimpleLabel G) ∧
    matroidRank (cycleMatroid G) (cycleMatroid G).E =
      G.vertexSet.ncard - graphConnectedComponentCount G ∧
    Function.Bijective (graphicMaximumAntichainEquivForests G) ∧
    (∀ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G)),
      (graphicMaximumAntichainEquivForests G C).1 =
        (graphMaximumSpanEdges G C).map (Function.Embedding.subtype _)) ∧
    (∀ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G)),
      C.1.card = G.vertexSet.ncard - graphConnectedComponentCount G) ∧
    Fintype.card (BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) = Fintype.card (GraphSpanningForests (graphSimplifiedGraph G)) ∧
    (∀ hs : GraphIsSimple G, Function.Bijective (graphicSimpleMaximumAntichainEquivForests G hs)) ∧
    (∀ (hs : GraphIsSimple G) (hc : GraphIsConnected G),
      Function.Bijective (graphicConnectedMaximumAntichainEquivTrees G hs hc)) ∧
    (∀ (_ : GraphIsConnected G) (F : Set β),
      GraphSpanningForest G F ↔ F ⊆ G.edgeSet ∧ LabelledGraphTree (G.restrict F)) ∧
    (∀ (t : (graphSimplification G).edgeSet) (e : β),
      e ∈ graphParallelEdgeClass G t ↔
        ∃ x y : G.vertexSet, t.1 = s(x, y) ∧ G.IsLink e x.1 y.1) ∧
    (∀ (R : Type*) [CommSemiring R] (x : β → R),
      (∑ F : GraphSpanningForests G, ∏ e ∈ F.1, x e) =
        ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
            (MatroidFlat (cycleMatroid G)),
          ∏ t ∈ graphMaximumSpanEdges G C, ∑ e ∈ graphParallelEdgeClass G t, x e) ∧
    graphSpanningForestPolynomial G =
      ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
          (MatroidFlat (cycleMatroid G)),
        ∏ t ∈ graphMaximumSpanEdges G C, ∑ e ∈ graphParallelEdgeClass G t,
          (MvPolynomial.X e : MvPolynomial β ℤ) := by
  refine ⟨graphic_simplification_eq_comap G, cycleMatroid_rank G,
    (graphicMaximumAntichainEquivForests G).bijective,
    graphicMaximumAntichainEquivForests_val G, graphMaximumAntichain_card G,
    graphicMaximumAntichain_count G, ?_, ?_, ?_, graphParallelEdgeClass_mem G,
    ?_, graphic_spanningForestPolynomial_parallel_edge_expansion G⟩
  · intro hs
    exact (graphicSimpleMaximumAntichainEquivForests G hs).bijective
  · intro hs hc
    exact (graphicConnectedMaximumAntichainEquivTrees G hs hc).bijective
  · intro hc F
    exact graphSpanningForest_iff_spanningTree hc
  · intro R _ x
    exact graphic_weighted_parallel_edge_expansion G x

end GraphicComplete


section PartitionStructure

open scoped Matroid

/-- Literal partition/complete-flat carriers, corank, and the consumed
rank-tight sum. No Stirling or Cayley coefficient evaluation is asserted
by this partial root. -/
theorem manuscript_cor_partition_lattice_structure (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    Function.Bijective (finitePartitionCompleteFlatOrderIso (α := α)) ∧
    (∀ (P : Finpartition (Finset.univ : Finset α)) (x y : α),
      s(x, y) ∈ (finitePartitionCompleteFlatOrderIso P).1 ↔
        x ≠ y ∧ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B) ∧
    (∀ (F : MatroidFlat (cycleMatroid (completeLabelledGraph α))) (x y : α),
      (∃ B ∈ (finitePartitionCompleteFlatOrderIso.symm F).parts, x ∈ B ∧ y ∈ B) ↔
        GraphReachable (completeLabelledGraph α) F.1 (completeGraphVertex x) (completeGraphVertex y)) ∧
    (∀ P : Finpartition (Finset.univ : Finset α), Function.Bijective (partitionFlatComponentsEquivBlocks P)) ∧
    (∀ P : Finpartition (Finset.univ : Finset α),
      MatroidFlat.rank (finitePartitionCompleteFlatOrderIso P) + P.parts.card = Fintype.card α) ∧
    (∀ (k : ℕ) (P : Finpartition (Finset.univ : Finset α)),
      HasCorank (cycleMatroid (completeLabelledGraph α)) k (finitePartitionCompleteFlatOrderIso P) ↔
        P.parts.card = k + 1) ∧
    (∀ k : ℕ, Function.Bijective (partitionAntichainEquiv (α := α) k)) ∧
    (∀ (k : ℕ) (C : BooleanAntichain k (Finpartition (Finset.univ : Finset α))),
      (partitionAntichainEquiv k C).1.inf id = finitePartitionCompleteFlatOrderIso (C.1.inf id)) ∧
    (∀ (k : ℕ) (C : BooleanAntichain k (Finpartition (Finset.univ : Finset α))),
      IsPartitionRankTight C ↔ (C.1.inf id).parts.card = k + 1) ∧
    (∀ k : ℕ, Fintype.card (PartitionRankTightAntichain α k) =
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // P.parts.card = k + 1},
        Fintype.card (MatroidBases (simplificationOnFlats
          ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P.1).1)))) := by
  exact ⟨finitePartitionCompleteFlatOrderIso.bijective,
    finitePartitionCompleteFlatOrderIso_mem_pair, finitePartitionCompleteFlatOrderIso_symm_blocks,
    fun P ↦ (partitionFlatComponentsEquivBlocks P).bijective, partitionFlat_rank_add_blocks,
    partitionFlat_hasCorank_iff, fun k ↦ (partitionAntichainEquiv k).bijective,
    partitionAntichainEquiv_meet, fun _ C ↦ partitionRankTight_block_iff C,
    partitionRankTight_count_by_blocks⟩


/-- The contraction step of the partition-lattice proof, including the
literal block unions, original-edge fibres, actual matroid equality and
actual spanning-tree coefficients. Their numerical evaluations remain open. -/
theorem manuscript_cor_partition_lattice_contraction (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    (∀ P : Finpartition (Finset.univ : Finset α), Function.Bijective (partitionCoarseningOrderIso P)) ∧
    (∀ (P : Finpartition (Finset.univ : Finset α)) (Q : Set.Ici P) (D : Q.1.parts),
      (partitionCoarseningBlockEquiv P Q D).1.biUnion (fun B : P.parts ↦ B.1) = D.1) ∧
    (∀ P : Finpartition (Finset.univ : Finset α), Function.Bijective (partitionContractionFlatOrderIso P)) ∧
    (∀ (P : Finpartition (Finset.univ : Finset α))
        (F : MatroidFlat ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P).1)),
      MatroidFlat.rank (partitionContractionFlatOrderIso P F) = MatroidFlat.rank F) ∧
    (∀ (P : Finpartition (Finset.univ : Finset α))
        (F : MatroidFlat ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P).1))
        (q : Sym2 α),
      q ∈ F.1 ↔ partitionBlockEdgeMap P q ∈ (partitionContractionFlatOrderIso P F).1) ∧
    (∀ P : Finpartition (Finset.univ : Finset α),
      simplificationOnFlats ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P).1) =
        (cycleMatroid (completeLabelledGraph P.parts)).comap (partitionSimplificationLabel P)) ∧
    (∀ (P : Finpartition (Finset.univ : Finset α))
        (F : RankOneFlat ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P).1)),
      F.1.1 \ ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P).1).loops =
        {q : Sym2 α | partitionBlockEdgeMap P q = partitionSimplificationLabel P F}) ∧
    (∀ (P : Finpartition (Finset.univ : Finset α)) (t : (completeLabelledGraph P.parts).edgeSet),
      (((partitionSimplificationEdgeEquiv P).symm t).1.1 \
        ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P).1).loops).Nonempty) ∧
    (∀ P : Finpartition (Finset.univ : Finset α), Function.Bijective (partitionContractionBasesEquivTrees P)) ∧
    (∀ (P : Finpartition (Finset.univ : Finset α))
        (I : MatroidBases (simplificationOnFlats
          ((cycleMatroid (completeLabelledGraph α)) ／ (finitePartitionCompleteFlatOrderIso P).1))),
      (partitionContractionBasesEquivTrees P I).1 =
        I.1.map ⟨partitionSimplificationLabel P, partitionSimplificationLabel_injective P⟩) ∧
    (∀ k : ℕ, Fintype.card (PartitionRankTightAntichain α k) =
      ∑ Q : {Q : Finpartition (Finset.univ : Finset α) // Q.parts.card = k + 1},
        Fintype.card (GraphSpanningTrees (completeLabelledGraph Q.1.parts))) := by
  exact ⟨fun P ↦ (partitionCoarseningOrderIso P).bijective, partitionCoarseningBlockEquiv_union,
    fun P ↦ (partitionContractionFlatOrderIso P).bijective, partitionContractionFlatOrderIso_rank,
    partitionContractionFlatOrderIso_mem, partition_simplification_eq_comap, partition_simplification_class,
    partition_simplification_class_nonempty, fun P ↦ (partitionContractionBasesEquivTrees P).bijective,
    fun P I ↦ partitionContractionBasesEquivTrees_val P I, partitionRankTight_count_complete_trees⟩


/-- The complete partition-lattice corollary, with the paper's exact
rank-tight range and the maximum-layer Cayley value. Both numerical
factors are derived from actual finite-object counts and kernel proofs. -/
theorem manuscript_cor_partition_lattice (n : ℕ) :
    (∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
      Fintype.card (PartitionRankTightAntichain (Fin n) k) =
        Nat.stirlingSecond n (k + 1) * (k + 1) ^ (k - 1)) ∧
    (2 ≤ n →
      Fintype.card (BooleanAntichain (n - 1) (Finpartition (Finset.univ : Finset (Fin n)))) =
        n ^ (n - 2)) := by
  constructor
  · intro k hk hkn
    exact partition_rank_tight_formula n k hk hkn
  · intro hn
    exact partition_fin_maximum_count n (by omega)

end PartitionStructure


section PartitionPairsStructure

/-- All finite-lattice and formal-series clauses of the partition-pairs
proof. The remaining exponential-formula bridge is not asserted here. -/
theorem manuscript_cor_partition_pairs_structure (n : ℕ) (hn : 0 < n) :
    letI : LocallyFiniteOrder (Finpartition (Finset.univ : Finset (Fin n))) :=
      Fintype.toLocallyFiniteOrder
    (∀ P : Finpartition (Finset.univ : Finset (Fin n)),
      Function.Bijective (partitionLowerIntervalOrderIso P)) ∧
    (∀ P : Finpartition (Finset.univ : Finset (Fin n)),
      (Finset.Iic P).card = ∏ B : P.parts, Nat.bell B.1.card) ∧
    (∀ P : Finpartition (Finset.univ : Finset (Fin n)),
      IncidenceAlgebra.mu ℤ P (⊤ : Finpartition (Finset.univ : Finset (Fin n))) =
        (-1 : ℤ) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial) ∧
    Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) = Nat.bell n ∧
    mobiusPairSum (L := Finpartition (Finset.univ : Finset (Fin n))) =
      partitionBellSquareMobiusSum n ∧
    (Fintype.card
        (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) : ℤ) =
      (partitionBellSquareMobiusSum n - 2 * (Nat.bell n : ℤ) + 1) / 2 ∧
    (∀ m : ℕ, PowerSeries.coeff m bellSquareEGF =
      if m = 0 then 0 else (Nat.bell m : ℚ) ^ 2 / m.factorial) ∧
    (∀ m : ℕ, PowerSeries.coeff m bellSquareLogSeries =
      ∑ b ∈ Finset.range (m + 1),
        (if b = 0 then 0 else ((-1 : ℚ) ^ (b + 1) / b)) *
          PowerSeries.coeff m (bellSquareEGF ^ b)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨fun P ↦ (partitionLowerIntervalOrderIso P).bijective,
    lowerIntervalCard_partition, finitePartition_mu_top_formula,
    by simpa only [Fintype.card_fin] using finitePartition_card_bell (α := Fin n),
    partition_mobiusPairSum_eq n hn, partition_pairs_mobius_formula n hn,
    bellSquareEGF_coeff, bellSquareLogSeries_coeff⟩


/-- The complete positive-n partition-pairs corollary: actual formal
series, exact logarithmic coefficient, actual pair family and all listed
initial values. -/
theorem manuscript_cor_partition_pairs :
    (∀ n : ℕ, 0 < n →
      (Fintype.card
        (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) : ℚ) =
        (1 / 2 : ℚ) * ((n.factorial : ℚ) *
          PowerSeries.coeff n bellSquareLogSeries - 2 * (Nat.bell n : ℚ) + 1)) ∧
    (∀ n : ℕ, (n.factorial : ℚ) * PowerSeries.coeff n bellSquareLogSeries =
      partitionBellSquareMobiusSumQ n) ∧
    List.ofFn (fun i : Fin 7 ↦ Fintype.card
      (BooleanAntichain 2
        (Finpartition (Finset.univ : Finset (Fin (i.1 + 1)))))) =
      [0, 0, 3, 45, 620, 9750, 183680] := by
  exact ⟨partition_pairs_log_formula, partition_exponential_formula,
    partitionPairCount_initial⟩

end PartitionPairsStructure

end BooleanAntichainsKernel
