import BooleanAntichainsKernel.SimplificationBases

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {M : Matroid α} {N : Matroid β}
variable (e : MatroidFlat M ≃o MatroidFlat N)
variable (hr : ∀ F : MatroidFlat M, MatroidFlat.rank (e F) = MatroidFlat.rank F)

noncomputable def rankOneFlatEquivOfOrderIso : RankOneFlat M ≃ RankOneFlat N :=
  Equiv.subtypeEquiv e.toEquiv (fun F ↦ by
    change MatroidFlat.rank F = 1 ↔ MatroidFlat.rank (e F) = 1
    rw [hr])

theorem rankOneFlatEquivOfOrderIso_val (F : RankOneFlat M) :
    (rankOneFlatEquivOfOrderIso e hr F).1 = e F.1 := rfl

theorem rankOneFlatEquivOfOrderIso_sup (I : Finset (RankOneFlat M)) :
    (I.map (rankOneFlatEquivOfOrderIso e hr).toEmbedding).sup
        (Subtype.val : RankOneFlat N → MatroidFlat N) =
      e (I.sup (Subtype.val : RankOneFlat M → MatroidFlat M)) := by
  rw [Finset.sup_map]
  change I.sup (fun F ↦ e F.1) = _
  exact (map_finset_sup e I (Subtype.val : RankOneFlat M → MatroidFlat M)).symm

theorem matroid_indep_finset_iff_rank {γ : Type*} [Fintype γ] (A : Matroid γ) (I : Finset γ) :
    A.Indep (I : Set γ) ↔ matroidRank A (I : Set γ) = I.card := by
  constructor
  · intro h
    simpa only [Set.ncard_coe_finset] using matroidRank_indep h
  · intro h
    apply (Matroid.indep_iff_eRk_eq_encard_of_finite I.finite_toSet).mpr
    rw [← coe_matroidRank, h]
    simp

section TargetFinite

variable [Fintype β]

/-- The target's existing rank-one representative, after the exact flat
transport. No literature output or extra matroid premise is introduced. -/
noncomputable def flatIsoRepresentativeMap (F : RankOneFlat M) : β :=
  rankOneRepresentative (rankOneFlatEquivOfOrderIso e hr F)

theorem flatIsoRepresentativeMap_injective : Function.Injective (flatIsoRepresentativeMap e hr) :=
  rankOneRepresentative_injective.comp (rankOneFlatEquivOfOrderIso e hr).injective

theorem flatIsoRepresentativeMap_mem_ground (F : RankOneFlat M) :
    flatIsoRepresentativeMap e hr F ∈ N.E :=
  rankOneRepresentative_mem_ground _

end TargetFinite

section Finite

variable [Fintype α] [Fintype β]

theorem simplificationFlatIso_finset_rank (I : Finset (RankOneFlat M)) :
    matroidRank (simplificationOnFlats N)
        (↑(I.map (rankOneFlatEquivOfOrderIso e hr).toEmbedding) : Set (RankOneFlat N)) =
      matroidRank (simplificationOnFlats M) (I : Set (RankOneFlat M)) := by
  rw [simplificationOnFlats_finset_rank, simplificationOnFlats_finset_rank,
    rankOneFlatEquivOfOrderIso_sup e hr]
  exact hr _

theorem simplificationFlatIso_finset_indep (I : Finset (RankOneFlat M)) :
    (simplificationOnFlats N).Indep (↑(I.map (rankOneFlatEquivOfOrderIso e hr).toEmbedding) : Set (RankOneFlat N)) ↔
      (simplificationOnFlats M).Indep (I : Set (RankOneFlat M)) := by
  rw [matroid_indep_finset_iff_rank, matroid_indep_finset_iff_rank, Finset.card_map,
    simplificationFlatIso_finset_rank e hr]

theorem simplificationFlatIso_indep (X : Set (RankOneFlat M)) :
    (simplificationOnFlats M).Indep X ↔
      (simplificationOnFlats N).Indep (rankOneFlatEquivOfOrderIso e hr '' X) := by
  have h := simplificationFlatIso_finset_indep e hr X.toFinset
  simpa only [Finset.coe_map, Equiv.coe_toEmbedding, Set.coe_toFinset] using h.symm

/-- Equality of actual simplification matroids after the proved
rank-preserving flat transport. Every independent set is checked. -/
theorem simplificationFlatIso_eq_comap :
    simplificationOnFlats M = N.comap (flatIsoRepresentativeMap e hr) := by
  apply Matroid.ext_indep
  · rw [simplificationOnFlats_ground, Matroid.comap_ground_eq]
    ext F
    exact iff_of_true (Set.mem_univ F) (flatIsoRepresentativeMap_mem_ground e hr F)
  · intro X _hX
    rw [Matroid.comap_indep_iff]
    have h := simplificationFlatIso_indep e hr X
    change (simplificationOnFlats M).Indep X ↔
      N.Indep (rankOneRepresentative '' (rankOneFlatEquivOfOrderIso e hr '' X)) ∧
        Set.InjOn (rankOneRepresentative (M := N)) (rankOneFlatEquivOfOrderIso e hr '' X) at h
    rw [Set.image_image] at h
    have hi : Set.InjOn (rankOneRepresentative (M := N)) (rankOneFlatEquivOfOrderIso e hr '' X) :=
      rankOneRepresentative_injective.injOn
    have h' : (simplificationOnFlats M).Indep X ↔
        N.Indep (flatIsoRepresentativeMap e hr '' X) := by
      simpa only [hi, and_true, flatIsoRepresentativeMap] using h
    exact h'.trans (and_iff_left (flatIsoRepresentativeMap_injective e hr).injOn).symm

end Finite

end BooleanAntichainsKernel
