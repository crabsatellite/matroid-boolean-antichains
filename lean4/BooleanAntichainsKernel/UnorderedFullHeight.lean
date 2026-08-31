import BooleanAntichainsKernel.FullHeightChains
import BooleanAntichainsKernel.GlobalEnumerator
import Mathlib.Order.Hom.Set

namespace BooleanAntichainsKernel

open Finset

variable {L : Type*} [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]

/-- The paper's unordered span: all meets of subfamilies, including the empty
meet.  Complementing the index family leaves this range unchanged. -/
def antichainSpan (C : Finset L) : Set L := Set.range (antichainMeetFace C)

omit [OrderBot L] in
lemma enumeration_commonMeet {r : ℕ} (C : Finset L) (e : Fin r ≃ C) :
    commonMeet (fun i ↦ (e i).1) = C.inf id := by
  have hcarrier := orderedCarrier_of_equiv C e
  calc
    commonMeet (fun i ↦ (e i).1) =
        (Finset.univ.image (fun i ↦ (e i).1)).inf id :=
      (Finset.inf_image (Finset.univ : Finset (Fin r)) (fun i ↦ (e i).1) id).symm
    _ = C.inf id := congrArg (fun S : Finset L ↦ S.inf id) hcarrier

omit [OrderBot L] in
lemma enumeration_span {r : ℕ} (C : Finset L) (e : Fin r ≃ C) :
    Set.range (meetFace (fun i ↦ (e i).1)) = antichainSpan C := by
  ext x
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨e.finsetCongr S, antichainMeetFace_map_equiv C e S⟩
  · rintro ⟨S, rfl⟩
    refine ⟨e.finsetCongr.symm S, ?_⟩
    rw [← antichainMeetFace_map_equiv C e, Equiv.apply_symm_apply]

/-- All conclusions of Lemma 2.1 for the actual unordered antichain carrier. -/
theorem unordered_full_height_rigidity [GradeMinOrder ℕ L] {r : ℕ}
    (C : BooleanAntichain r L) (hr : grade ℕ (⊤ : L) = r) :
    C.1.inf id = ⊥ ∧
    (∀ c : Set (antichainSpan C.1), IsMaxChain (· ≤ ·) c →
      IsMaxChain (· ≤ ·) (Subtype.val '' c : Set L)) ∧
    (∀ i : C.1, grade ℕ (antichainMeetFace C.1 {i}) = 1) ∧
    (∀ i : C.1, grade ℕ i.1 = r - 1) := by
  let e : Fin r ≃ C.1 := canonicalEnumeration C
  let H : Fin r → L := fun i ↦ (e i).1
  have hH : IsBooleanTuple H := (isBooleanTuple_iff_antichain_of_equiv C.1 e).mpr C.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← enumeration_commonMeet C.1 e]
    exact full_height_commonMeet_eq_bot hH hr
  · intro c hc
    let E : BooleanSpan H ≃o antichainSpan C.1 :=
      OrderIso.setCongr _ _ (enumeration_span C.1 e)
    have hd := hc.image E.symm
    have hm := full_height_span_maxChain hH hr hd
    have hval : (Subtype.val '' (E.symm '' c) : Set L) = Subtype.val '' c := by
      rw [Set.image_image]
      apply Set.image_congr
      intro y _
      rfl
    rwa [hval] at hm
  · intro i
    have hi : e.finsetCongr {e.symm i} = {i} := by
      simp [Equiv.finsetCongr_apply]
    have ht := antichainMeetFace_map_equiv C.1 e ({e.symm i} : Finset (Fin r))
    rw [hi] at ht
    rw [ht, ← reconstructedAtom_eq_meetFace_singleton]
    exact full_height_atom_grade hH hr (e.symm i)
  · intro i
    have hv : H (e.symm i) = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
    rw [← hv]
    exact full_height_coatom_grade hH hr (e.symm i)

end BooleanAntichainsKernel
