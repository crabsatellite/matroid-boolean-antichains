import BooleanAntichainsKernel.FullHeight
import Mathlib.Data.Set.Finite.Lemmas

namespace BooleanAntichainsKernel

open Finset

variable {L : Type*} [Lattice L] [OrderBot L] [OrderTop L] [GradeMinOrder ℕ L]

/-- Every maximal chain of Boolean faces is a maximal chain of the ambient
ranked lattice when the Boolean span has full height (Lemma 2.1). -/
theorem full_height_maxChain_image {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r)
    {c : Set (Finset (Fin r))} (hc : IsMaxChain (· ≤ ·) c) :
    IsMaxChain (· ≤ ·) (meetFace H '' c) := by
  classical
  let f := meetFace H
  have hf : StrictMono f := boolean_meetFace_strictMono hH
  refine ⟨hf.monotone.isChain_image hc.1, ?_⟩
  intro t ht hct
  apply Set.Subset.antisymm hct
  intro x hxt
  let below : Set (Finset (Fin r)) := {A | A ∈ c ∧ f A ≤ x}
  let above : Set (Finset (Fin r)) := {B | B ∈ c ∧ x ≤ f B}
  have below_ne : below.Nonempty := by
    refine ⟨∅, hc.bot_mem, ?_⟩
    change meetFace H ∅ ≤ x
    rw [meetFace_empty, full_height_commonMeet_eq_bot hH hr]
    exact bot_le
  have above_ne : above.Nonempty := by
    refine ⟨Finset.univ, hc.top_mem, ?_⟩
    change x ≤ meetFace H Finset.univ
    rw [meetFace_univ]
    exact le_top
  obtain ⟨A, hA, hAmax⟩ := Set.exists_max_image below Finset.card (Set.toFinite _) below_ne
  obtain ⟨B, hB, hBmin⟩ := Set.exists_min_image above Finset.card (Set.toFinite _) above_ne
  have hAc : A ∈ c := hA.1
  have hBc : B ∈ c := hB.1
  have hAx : f A ≤ x := hA.2
  have hxB : x ≤ f B := hB.2
  by_cases heA : f A = x
  · exact ⟨A, hAc, heA⟩
  by_cases heB : f B = x
  · exact ⟨B, hBc, heB⟩
  have hAx' : f A < x := lt_of_le_of_ne hAx heA
  have hxB' : x < f B := lt_of_le_of_ne hxB (Ne.symm heB)
  have lower_bound : ∀ W ∈ c, f W ≤ x → W ≤ A := by
    intro W hWc hWx
    by_contra hnot
    have hAW := (hc.1.total hWc hAc).resolve_left hnot
    have hstrict : A < W := lt_of_le_not_ge hAW hnot
    exact (Finset.card_lt_card hstrict).not_ge (hAmax W ⟨hWc, hWx⟩)
  have upper_bound : ∀ W ∈ c, x ≤ f W → B ≤ W := by
    intro W hWc hxW
    by_contra hnot
    have hWB := (hc.1.total hBc hWc).resolve_left hnot
    have hstrict : W < B := lt_of_le_not_ge hWB hnot
    exact (Finset.card_lt_card hstrict).not_ge (hBmin W ⟨hWc, hxW⟩)
  have hAB : A < B := by
    apply lt_of_le_of_ne ((boolean_meetFace_le_iff hH).mp (hAx.trans hxB))
    intro heq
    exact (hAx'.trans hxB').ne (congrArg f heq)
  have hcover : A ⋖ B := by
    refine ⟨hAB, ?_⟩
    intro Z hAZ hZB
    have hinsert : IsChain (· ≤ ·) (insert Z c) := hc.1.insert (by
      intro W hWc _
      have hWt : f W ∈ t := hct ⟨W, hWc, rfl⟩
      rcases ht.total hWt hxt with hWx | hxW
      · exact Or.inr ((lower_bound W hWc hWx).trans hAZ.le)
      · exact Or.inl (hZB.le.trans (upper_bound W hWc hxW)))
    have heq : c = insert Z c := hc.2 hinsert (Set.subset_insert Z c)
    have hZc : Z ∈ c := heq.symm ▸ Set.mem_insert Z c
    have hZt : f Z ∈ t := hct ⟨Z, hZc, rfl⟩
    rcases ht.total hZt hxt with hZx | hxZ
    · exact hAZ.not_ge (lower_bound Z hZc hZx)
    · exact hZB.not_ge (upper_bound Z hZc hxZ)
  exact ((full_height_cover hH hr hcover).2 hAx' hxB').elim

/-- The literal Boolean span as a subtype of the ambient lattice. -/
abbrev BooleanSpan {r : ℕ} (H : Fin r → L) := Set.range (meetFace H)

omit [OrderBot L] [GradeMinOrder ℕ L] in
noncomputable def booleanFaceOrderIso {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) : Finset (Fin r) ≃o BooleanSpan H :=
  { Equiv.ofInjective (meetFace H) hH.1 with
    map_rel_iff' := fun {_ _} ↦ boolean_meetFace_le_iff hH }

/-- The maximal-chain conclusion, stated on chains in the literal Boolean
span rather than merely on an indexed list of faces. -/
theorem full_height_span_maxChain {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r)
    {c : Set (BooleanSpan H)} (hc : IsMaxChain (· ≤ ·) c) :
    IsMaxChain (· ≤ ·) (Subtype.val '' c : Set L) := by
  let e := booleanFaceOrderIso hH
  have hd : IsMaxChain (· ≤ ·) (e.symm '' c) := hc.image e.symm
  have hm := full_height_maxChain_image hH hr hd
  have himage : meetFace H '' (e.symm '' c) = (Subtype.val '' c : Set L) := by
    rw [Set.image_image]
    apply Set.image_congr
    intro y _
    exact congrArg Subtype.val (e.apply_symm_apply y)
  rwa [himage] at hm

/-- Full-height rigidity, with all four conclusions exposed. -/
theorem full_height_rigidity {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r) :
    commonMeet H = ⊥ ∧
    (∀ c : Set (BooleanSpan H), IsMaxChain (· ≤ ·) c →
      IsMaxChain (· ≤ ·) (Subtype.val '' c : Set L)) ∧
    (∀ i, grade ℕ (reconstructedAtom H i) = 1) ∧
    (∀ i, grade ℕ (H i) = r - 1) :=
  ⟨full_height_commonMeet_eq_bot hH hr,
    fun _ hc ↦ full_height_span_maxChain hH hr hc,
    full_height_atom_grade hH hr, full_height_coatom_grade hH hr⟩

end BooleanAntichainsKernel
