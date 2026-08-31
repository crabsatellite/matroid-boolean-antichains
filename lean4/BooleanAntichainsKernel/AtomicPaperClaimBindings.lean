import BooleanAntichainsKernel.PublicationRoot

/-!
# Atomic manuscript-claim bindings

Each declaration below is the unique kernel declaration bound to one formal
claim marker in `paper/matroid_boolean_antichains.tex`.  Composite publication
roots are projected here so that a declaration signature exposes exactly the
carrier, range, hypotheses, and conclusion of its atomic manuscript claim.
-/

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

set_option linter.defProp false

theorem atomic_def_boolean_atoms {L : Type*} [Lattice L] [OrderBot L] [OrderTop L]
    {k : ℕ} (H : Fin k → L) (i : Fin k) :
    reconstructedAtom H i = (Finset.univ.erase i).inf H := by
  rfl

noncomputable def atomic_lem_full_height := @manuscript_lem_full_height

noncomputable def atomic_lem_basis_span := @manuscript_lem_basis_span

theorem atomic_def_reconstruction_gap {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] {k : ℕ}
    (H : Fin k → L) (S : Finset (Fin k)) :
    reconstructionGap H S =
      latticeHeight (meetFace H S) - latticeHeight (joinFace H S) := by
  rfl

noncomputable def atomic_thm_global_gap_criterion := @manuscript_thm_global_gap_criterion

noncomputable def atomic_eq_global_enumerator := @manuscript_thm_global_gap_enumerator

theorem atomic_thm_global_boundaries {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] (k : ℕ) :
    Fintype.card (BooleanAntichain 0 L) = 1 ∧
    (latticeHeight (⊤ : L) < k → Fintype.card (BooleanAntichain k L) = 0) := by
  exact ⟨booleanAntichain_count_zero, booleanAntichain_count_above_height k⟩

theorem atomic_def_hom_transform {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] (k : ℕ) :
    etaCount k L =
      ∑ a ∈ Finset.range (k + 1), k.choose a *
        (a.factorial * Fintype.card (BooleanAntichain a L)) := by
  rfl

noncomputable def atomic_eq_product_transform := @manuscript_thm_product_transform

noncomputable def atomic_eq_product_convolution := @productAntichain_count_convolution

theorem atomic_def_rank_profile {α : Type*} [Fintype α] {M : Matroid α}
    {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) (S : Finset C.1) :
    antichainRankProfile C S =
      MatroidFlat.rank (antichainMeetFace C.1 S) - MatroidFlat.rank (C.1.inf id) := by
  rfl

theorem atomic_cor_rank_profile_polymatroid {α : Type*} [Fintype α]
    (M : Matroid α) {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    antichainRankProfile C ∅ = 0 ∧ StrictMono (antichainRankProfile C) ∧
    (∀ S T : Finset C.1,
      antichainRankProfile C (S ∩ T) + antichainRankProfile C (S ∪ T) ≤
        antichainRankProfile C S + antichainRankProfile C T) := by
  have h := manuscript_cor_rank_profile M C
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem atomic_cor_rank_profile_tight {α : Type*} [Fintype α]
    (M : Matroid α) {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    IsRankTight C ↔ ∀ S : Finset C.1, antichainRankProfile C S = S.card := by
  exact (manuscript_cor_rank_profile M C).2.2.2

theorem atomic_thm_uniform_base_layers (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    Fintype.card
        (BooleanAntichain 0 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) = 1 ∧
    Fintype.card
        (BooleanAntichain 1 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
      ∑ b ∈ Finset.range r, n.choose b := by
  have h := manuscript_thm_uniform_all_structure n r ⟨hr1, hrn⟩
  exact ⟨h.1, h.2.1⟩

theorem atomic_eq_uniform_all (n r k : ℕ) (_hr1 : 1 ≤ r) (hrn : r ≤ n)
    (hk2 : 2 ≤ k) (_hkr : k ≤ r) :
    (Fintype.card
      (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) : ℚ) =
      (1 / (k.factorial : ℚ)) *
        ∑ b ∈ Finset.range r, (n.choose b : ℚ) *
          ∑ p : UniformAdmissibleProfile n r k b,
            ((n - b).factorial : ℚ) /
              (((n - b - ∑ i, p.1 i).factorial : ℚ) *
                ∏ i, ((p.1 i).factorial : ℚ)) := by
  exact uniform_all_size_formula_rational n r k hrn hk2

theorem atomic_thm_uniform_distributions :
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3)))) =
        [1, 11, 27, 4] ∧
    List.ofFn (fun k : Fin 5 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4)))) =
        [1, 26, 150, 50, 5] := by
  exact ⟨uniform34_distribution, uniform45_distribution⟩

noncomputable def atomic_thm_size_two_structural := @manuscript_thm_size_two_structural

noncomputable def atomic_eq_size_two_mobius := @manuscript_thm_size_two_mobius

noncomputable def atomic_thm_distributive_bijection :=
  @manuscript_thm_distributive_bijection

noncomputable def atomic_eq_distributive_polynomial := @distributive_polynomial_identity

theorem atomic_thm_main_bijection {α : Type*} [Fintype α] (M : Matroid α) :
    (∀ C : MaximumBooleanAntichain M,
      (maximumAntichainToBasis C).1 = antichainAtoms C.1) ∧
    (∀ A : SimplifiedBasis M,
      (simplifiedBasisToAntichain A).1 = basisCoatoms A.1) ∧
    Function.LeftInverse (simplifiedBasisToAntichain (M := M)) maximumAntichainToBasis ∧
    Function.RightInverse (simplifiedBasisToAntichain (M := M)) maximumAntichainToBasis := by
  have h := manuscript_thm_main M
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem atomic_eq_main_count {α : Type*} [Fintype α] (M : Matroid α) :
    Fintype.card (MaximumBooleanAntichain M) = Fintype.card (SimplifiedBasis M) ∧
    (Fintype.card (SimplifiedBasis M) : ℤ) =
      MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℤ))
        (matroidTuttePolynomial (simplificationOnFlats M)) := by
  have h := manuscript_thm_main M
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

noncomputable def atomic_eq_weighted_polynomial := @weighted_basis_polynomial

noncomputable def atomic_eq_weighted_count := @weighted_basis_count

theorem atomic_thm_interval_bijection {α : Type*} [Fintype α]
    (M : Matroid α) (X Y : MatroidFlat M) [Fact (X ≤ Y)] :
    Function.Bijective (intervalAntichainEquivBasis X Y) := by
  exact (intervalAntichainEquivBasis X Y).bijective

noncomputable def atomic_eq_interval_weighted := @interval_weighted_basis_polynomial

theorem atomic_def_rank_tight {α : Type*} [Fintype α] {M : Matroid α}
    {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    IsRankTight C ↔
      MatroidFlat.rank (C.1.inf id) = MatroidFlat.rank (⊤ : MatroidFlat M) - k := by
  rfl

theorem atomic_def_rank_tight_equivalent {α : Type*} [Fintype α] {M : Matroid α}
    {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    IsRankTight C ↔ HasCorank M k (C.1.inf id) := by
  exact (hasCorank_bottom_iff_rankTight C).symm

noncomputable def atomic_cor_rank_tight_partition {α : Type*} [Fintype α]
    (M : Matroid α) (k : ℕ) := rankTightEquivBottomFibers (M := M) (k := k)

theorem atomic_eq_rank_tight_count {α : Type*} [Fintype α]
    (M : Matroid α) (k : ℕ) :
    Fintype.card (RankTightAntichain M k) =
      ∑ X ∈ Finset.univ.filter (fun X : MatroidFlat M ↦
        (MatroidFlat.rank X : ℤ) =
          (MatroidFlat.rank (⊤ : MatroidFlat M) : ℤ) - (k : ℤ)),
        Fintype.card (MatroidBases (simplificationOnFlats (M.contract X.1))) := by
  exact (manuscript_cor_rank_tight M k).2.2.1

theorem atomic_cor_rank_tight_fiber {α : Type*} [Fintype α]
    (M : Matroid α) (k : ℕ) (X : MatroidFlat M) (hX : HasCorank M k X) :
    Function.Bijective (bottomFiberEquivActualContractionBases k X hX) := by
  exact (bottomFiberEquivActualContractionBases k X hX).bijective

noncomputable def atomic_eq_boolean_tight := @manuscript_cor_boolean_lattice_tight

noncomputable def atomic_cor_boolean_total := @booleanLattice_count_stirling

noncomputable def atomic_eq_boolean_nontight := @booleanLattice_nonRankTight_count

noncomputable def atomic_eq_partition_tight := @partition_rank_tight_formula

noncomputable def atomic_cor_partition_maximum := @partition_fin_maximum_count

noncomputable def atomic_cor_uniform_tight := @manuscript_cor_uniform_tight

theorem atomic_def_bell_square_egf (m : ℕ) :
    PowerSeries.coeff m bellSquareEGF =
      if m = 0 then 0 else (Nat.bell m : ℚ) ^ 2 / m.factorial := by
  rw [bellSquareEGF_coeff]
  rfl

noncomputable def atomic_eq_partition_pairs := @partition_pairs_log_formula

noncomputable def atomic_cor_partition_pairs_initial := partitionPairCount_initial

theorem atomic_def_direct_sum_count (K : Type*) [Field K] [Fintype K]
    (d k : ℕ) :
    directSumProfileCount K d k =
      (1 / (k.factorial : ℚ)) *
        ∑ p : PositiveDimensionProfile d k,
          (generalLinearCard K d : ℚ) /
            ∏ i, (generalLinearCard K (p.1 i) : ℚ) := by
  rfl

theorem atomic_thm_subspace_correspondence
    (K : Type*) [Field K] [Fintype K] (n k : ℕ) :
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
        D.1.image (fun U ↦ ((D.1.erase U).sup id).comap X.mkQ)) := by
  have h := manuscript_thm_subspace_correspondence K n k
  exact ⟨h.1, h.2.1, h.2.2.1⟩

noncomputable def atomic_eq_subspace_count := @standardSubspace_all_size_formula

theorem atomic_thm_subspace_zero_layer
    (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    Fintype.card (BooleanAntichain 0 (Submodule K (Fin n → K))) = 1 := by
  exact booleanAntichain_count_zero

noncomputable def atomic_cor_graphic_simplified_forests :=
  @graphicMaximumAntichainEquivForests

theorem atomic_cor_graphic_size_specializations {α β : Type*} (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    (∀ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G)),
      C.1.card = G.vertexSet.ncard - graphConnectedComponentCount G) ∧
    (∀ hs : GraphIsSimple G,
      Function.Bijective (graphicSimpleMaximumAntichainEquivForests G hs)) ∧
    (∀ (hs : GraphIsSimple G) (hc : GraphIsConnected G),
      Function.Bijective (graphicConnectedMaximumAntichainEquivTrees G hs hc)) := by
  exact ⟨graphMaximumAntichain_card G,
    fun hs ↦ (graphicSimpleMaximumAntichainEquivForests G hs).bijective,
    fun hs hc ↦ (graphicConnectedMaximumAntichainEquivTrees G hs hc).bijective⟩

noncomputable def atomic_cor_graphic_weighted :=
  @graphic_spanningForestPolynomial_parallel_edge_expansion

noncomputable def atomic_eq_projective_plane_all := @manuscript_eq_projective_plane_all

noncomputable def atomic_eq_projective_count := @manuscript_eq_projective_count

end BooleanAntichainsKernel
