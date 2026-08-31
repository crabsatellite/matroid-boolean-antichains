import BooleanAntichainsKernel.UnorderedFullHeight
import BooleanAntichainsKernel.MatroidRank

/-! The normalized integral polymatroid rank profile of Corollary 3.3. -/

namespace BooleanAntichainsKernel

open Finset

variable {α : Type*} [Fintype α] {M : Matroid α}

noncomputable def tupleRankProfile {k : ℕ} (H : Fin k → MatroidFlat M)
    (S : Finset (Fin k)) : ℕ :=
  MatroidFlat.rank (meetFace H S) - MatroidFlat.rank (commonMeet H)

def IsRankTightTuple {k : ℕ} (H : Fin k → MatroidFlat M) : Prop :=
  MatroidFlat.rank (commonMeet H) = MatroidFlat.rank (⊤ : MatroidFlat M) - k

lemma rank_commonMeet_le_face {k : ℕ} (H : Fin k → MatroidFlat M) (S : Finset (Fin k)) :
    MatroidFlat.rank (commonMeet H) ≤ MatroidFlat.rank (meetFace H S) :=
  MatroidFlat.rank_mono (Finset.inf_mono Finset.sdiff_subset)

omit [Fintype α] in
@[simp] lemma tupleRankProfile_empty {k : ℕ} (H : Fin k → MatroidFlat M) :
    tupleRankProfile H ∅ = 0 := by simp [tupleRankProfile]

lemma tupleRankProfile_strictMono {k : ℕ} {H : Fin k → MatroidFlat M}
    (hH : IsBooleanTuple H) : StrictMono (tupleRankProfile H) := by
  intro S T hST
  have hstrict := MatroidFlat.rank_strictMono (boolean_meetFace_strictMono hH hST)
  have hS := rank_commonMeet_le_face H S
  have hT := rank_commonMeet_le_face H T
  unfold tupleRankProfile
  omega

lemma tupleRankProfile_submod {k : ℕ} {H : Fin k → MatroidFlat M}
    (hH : IsBooleanTuple H) (S T : Finset (Fin k)) :
    tupleRankProfile H (S ∩ T) + tupleRankProfile H (S ∪ T) ≤
      tupleRankProfile H S + tupleRankProfile H T := by
  have hm := MatroidFlat.rank_submod (meetFace H S) (meetFace H T)
  rw [← meetFace_inter, ← hH.2] at hm
  have hS := rank_commonMeet_le_face H S
  have hT := rank_commonMeet_le_face H T
  have hI := rank_commonMeet_le_face H (S ∩ T)
  have hU := rank_commonMeet_le_face H (S ∪ T)
  unfold tupleRankProfile
  omega

theorem tuple_rankTight_iff_card_profile {k : ℕ} {H : Fin k → MatroidFlat M}
    (hH : IsBooleanTuple H) :
    IsRankTightTuple H ↔ ∀ S : Finset (Fin k), tupleRankProfile H S = S.card := by
  have hbound := boolean_face_rank_bounds hH MatroidFlat.rank MatroidFlat.rank_strictMono Finset.univ
  simp only [meetFace_univ, Finset.card_univ, Fintype.card_fin] at hbound
  constructor
  · intro htight S
    have hface := boolean_face_rank_bounds hH MatroidFlat.rank MatroidFlat.rank_strictMono S
    have hcard : S.card ≤ k := by simpa using Finset.card_le_card (Finset.subset_univ S)
    unfold IsRankTightTuple at htight
    unfold tupleRankProfile
    omega
  · intro hprof
    have hall := hprof Finset.univ
    simp only [tupleRankProfile, meetFace_univ, Finset.card_univ, Fintype.card_fin] at hall
    have hle : MatroidFlat.rank (commonMeet H) ≤ MatroidFlat.rank (⊤ : MatroidFlat M) :=
      MatroidFlat.rank_mono le_top
    unfold IsRankTightTuple
    omega

/-- The paper's literal profile on subfamilies of the unordered antichain. -/
noncomputable def antichainRankProfile {k : ℕ} (C : BooleanAntichain k (MatroidFlat M))
    (S : Finset C.1) : ℕ :=
  MatroidFlat.rank (antichainMeetFace C.1 S) - MatroidFlat.rank (C.1.inf id)

def IsRankTight {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) : Prop :=
  MatroidFlat.rank (C.1.inf id) = MatroidFlat.rank (⊤ : MatroidFlat M) - k

lemma rankProfile_enumeration {k : ℕ} (C : BooleanAntichain k (MatroidFlat M))
    (e : Fin k ≃ C.1) (S : Finset (Fin k)) :
    antichainRankProfile C (e.finsetCongr S) = tupleRankProfile (fun i ↦ (e i).1) S := by
  unfold antichainRankProfile tupleRankProfile
  rw [antichainMeetFace_map_equiv, ← enumeration_commonMeet C.1 e]

/-- Corollary 3.3 on the actual unordered family, including both directions
of the rank-tight characterization. The codomain `ℕ` records integrality. -/
theorem antichain_rank_profile {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    antichainRankProfile C ∅ = 0 ∧
    StrictMono (antichainRankProfile C) ∧
    (∀ S T : Finset C.1,
      antichainRankProfile C (S ∩ T) + antichainRankProfile C (S ∪ T) ≤
        antichainRankProfile C S + antichainRankProfile C T) ∧
    (IsRankTight C ↔ ∀ S : Finset C.1, antichainRankProfile C S = S.card) := by
  let e := canonicalEnumeration C
  let H : Fin k → MatroidFlat M := fun i ↦ (e i).1
  let E := e.finsetCongr
  have hH : IsBooleanTuple H := (isBooleanTuple_iff_antichain_of_equiv C.1 e).mpr C.2.2
  have htransport (S : Finset C.1) : antichainRankProfile C S = tupleRankProfile H (E.symm S) := by
    rw [← rankProfile_enumeration C e, Equiv.apply_symm_apply]
  have hcard (S : Finset C.1) : (E.symm S).card = S.card := Finset.card_map _
  have hUnion (S T : Finset C.1) : E.symm (S ∪ T) = E.symm S ∪ E.symm T := Finset.map_union S T
  have hInter (S T : Finset C.1) : E.symm (S ∩ T) = E.symm S ∩ E.symm T := Finset.map_inter S T
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htransport]
    change tupleRankProfile H (Finset.map e.symm.toEmbedding ∅) = 0
    simp
  · intro S T hST
    rw [htransport, htransport]
    apply tupleRankProfile_strictMono hH
    exact (Finset.mapEmbedding e.symm.toEmbedding).strictMono hST
  · intro S T
    rw [htransport, htransport, htransport, htransport, hInter, hUnion]
    exact tupleRankProfile_submod hH _ _
  · have htight : IsRankTight C ↔ IsRankTightTuple H := by
      unfold IsRankTight IsRankTightTuple
      rw [enumeration_commonMeet C.1 e]
    rw [htight, tuple_rankTight_iff_card_profile hH]
    constructor
    · intro hall S
      rw [htransport, hall, hcard]
    · intro hall S
      have h := hall (E S)
      rw [rankProfile_enumeration C e] at h
      have hcES : (E S).card = S.card := Finset.card_map _
      exact h.trans hcES

end BooleanAntichainsKernel
