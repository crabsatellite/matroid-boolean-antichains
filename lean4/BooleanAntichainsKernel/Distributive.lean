import BooleanAntichainsKernel.MobiusFormula
import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Boolean antichains in distributive lattices
-/

namespace BooleanAntichainsKernel

open Finset

section Distributive

variable {L : Type*} [DistribLattice L] [OrderTop L]

lemma inf_sup_inf_eq_inf_inter {ι : Type*} [DecidableEq ι]
    (H : ι → L) (A B : Finset ι)
    (hpair : ∀ i ∈ A, ∀ j ∈ B, i ≠ j → H i ⊔ H j = ⊤) :
    A.inf H ⊔ B.inf H = (A ∩ B).inf H := by
  apply le_antisymm
  · apply sup_le
    · exact Finset.inf_mono Finset.inter_subset_left
    · exact Finset.inf_mono Finset.inter_subset_right
  · rw [Finset.inf_sup_distrib_right]
    apply Finset.le_inf
    intro i hiA
    rw [Finset.inf_sup_distrib_left]
    apply Finset.le_inf
    intro j hjB
    by_cases hij : i = j
    · subst j
      simpa using Finset.inf_le (f := H) (Finset.mem_inter.mpr ⟨hiA, hjB⟩)
    · rw [hpair i hiA j hjB hij]
      exact le_top

lemma pairwise_top_join_meetFace_union {k : ℕ} (H : Fin k → L)
    (hpair : ∀ i j, i ≠ j → H i ⊔ H j = ⊤)
    (S T : Finset (Fin k)) :
    meetFace H (S ∪ T) = meetFace H S ⊔ meetFace H T := by
  rw [meetFace, Finset.sdiff_union_distrib]
  symm
  apply inf_sup_inf_eq_inf_inter
  intro i hi j hj hij
  exact hpair i j hij

lemma pairwise_top_join_face_sup_entry {k : ℕ} (H : Fin k → L)
    (hpair : ∀ i j, i ≠ j → H i ⊔ H j = ⊤)
    {S : Finset (Fin k)} {i : Fin k} (hiS : i ∈ S) :
    meetFace H S ⊔ H i = ⊤ := by
  have h := inf_sup_inf_eq_inf_inter H (Finset.univ \ S) {i} (by
    intro j hj l hl hji
    have hli : l = i := Finset.mem_singleton.mp hl
    subst l
    exact hpair j i hji)
  have hinter : (Finset.univ \ S) ∩ ({i} : Finset (Fin k)) = ∅ := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨hjS, rfl⟩
    exact hjS hiS
  simpa [meetFace, hinter] using h

/-- The structural classification underlying `thm:distributive`. -/
theorem distributive_isBoolean_iff_pairwise_top {k : ℕ} (H : Fin k → L) :
    IsBooleanTuple H ↔
      (∀ i, H i ≠ ⊤) ∧ (∀ i j, i ≠ j → H i ⊔ H j = ⊤) := by
  constructor
  · intro hH
    refine ⟨booleanTuple_entry_ne_top hH, ?_⟩
    intro i j hij
    have hu : Finset.univ.erase i ∪ Finset.univ.erase j =
        (Finset.univ : Finset (Fin k)) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true,
        iff_true]
      by_cases hxi : x = i
      · exact Or.inr (fun hxj ↦ hij (hxi.symm.trans hxj))
      · exact Or.inl hxi
    have hj := hH.2 (Finset.univ.erase i) (Finset.univ.erase j)
    rw [hu, meetFace_univ, meetFace_complement_singleton,
      meetFace_complement_singleton] at hj
    exact hj.symm
  · rintro ⟨hproper, hpair⟩
    constructor
    · intro S T hST
      apply Finset.Subset.antisymm
      · intro i hiS
        by_contra hiT
        have hTi : meetFace H T ≤ H i := by
          apply Finset.inf_le
          simp [hiT]
        have hSi : meetFace H S ≤ H i := hST.trans_le hTi
        have htop : meetFace H S ⊔ H i = ⊤ :=
          pairwise_top_join_face_sup_entry H hpair hiS
        apply hproper i
        rw [← htop, sup_eq_right.mpr hSi]
      · intro i hiT
        by_contra hiS
        have hSi : meetFace H S ≤ H i := by
          apply Finset.inf_le
          simp [hiS]
        have hTi : meetFace H T ≤ H i := hST.symm.trans_le hSi
        have htop : meetFace H T ⊔ H i = ⊤ :=
          pairwise_top_join_face_sup_entry H hpair hiT
        apply hproper i
        rw [← htop, sup_eq_right.mpr hTi]
    · exact pairwise_top_join_meetFace_union H hpair

end Distributive

section DistributiveFinsets

variable {L : Type*} [Fintype L] [DecidableEq L]
variable [DistribLattice L] [OrderBot L] [OrderTop L]

omit [Fintype L] [OrderBot L] in
/-- Intrinsic finite-set form of the distributive classification. -/
theorem distributive_isBooleanAntichain_iff (C : Finset L) :
    IsBooleanAntichain C ↔
      (∀ x ∈ C, x ≠ ⊤) ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → x ⊔ y = ⊤) := by
  let e : Fin C.card ≃ C := (Finset.equivFin C).symm
  let H : Fin C.card → L := fun i ↦ ((e i : C) : L)
  rw [← isBooleanTuple_iff_antichain_of_equiv C e,
    distributive_isBoolean_iff_pairwise_top]
  constructor
  · rintro ⟨hproper, hpair⟩
    constructor
    · intro x hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      have hix : H i = x := congrArg Subtype.val hi
      rw [← hix]
      exact hproper i
    · intro x hx y hy hxy
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨y, hy⟩
      have hij : i ≠ j := by
        intro hij
        apply hxy
        exact congrArg Subtype.val (hi.symm.trans (hij ▸ hj))
      have hix : H i = x := congrArg Subtype.val hi
      have hjy : H j = y := congrArg Subtype.val hj
      rw [← hix, ← hjy]
      exact hpair i j hij
  · rintro ⟨hproper, hpair⟩
    constructor
    · intro i
      exact hproper (H i) (e i).2
    · intro i j hij
      apply hpair (H i) (e i).2 (H j) (e j).2
      intro hvals
      apply hij
      apply e.injective
      exact Subtype.ext hvals

end DistributiveFinsets

section OrderIdeals

variable {P : Type*} [PartialOrder P]

lemma lowerSet_compl_nonempty_iff_ne_top (I : LowerSet P) :
    ((I.compl : UpperSet P) : Set P).Nonempty ↔ I ≠ ⊤ := by
  rw [UpperSet.coe_nonempty]
  constructor
  · intro h htop
    apply h
    rw [htop, LowerSet.compl_top]
  · intro h hcompl
    apply h
    have hc := congrArg UpperSet.compl hcompl
    simpa using hc

lemma lowerSet_compl_disjoint_iff_sup_eq_top (I J : LowerSet P) :
    Disjoint (((I.compl : UpperSet P) : Set P))
      (((J.compl : UpperSet P) : Set P)) ↔ I ⊔ J = ⊤ := by
  rw [Set.disjoint_iff_inter_eq_empty]
  constructor
  · intro h
    apply SetLike.ext
    intro x
    change x ∈ (I : Set P) ∪ (J : Set P) ↔ True
    simp only [Set.mem_union, iff_true]
    by_contra hx
    push Not at hx
    have hxI : x ∈ ((I.compl : UpperSet P) : Set P) := by simpa using hx.1
    have hxJ : x ∈ ((J.compl : UpperSet P) : Set P) := by simpa using hx.2
    have : x ∈ (((I.compl : UpperSet P) : Set P) ∩
        ((J.compl : UpperSet P) : Set P)) := ⟨hxI, hxJ⟩
    rw [h] at this
    exact this
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases hx with ⟨hxI, hxJ⟩
    have hxTop : x ∈ (⊤ : LowerSet P) := by simp
    rw [← h] at hxTop
    rcases hxTop with hxTop | hxTop
    · exact hxI hxTop
    · exact hxJ hxTop

/-- The ordered form of the bijection in `thm:distributive`: complements are
nonempty pairwise-disjoint order filters. -/
theorem orderIdeal_isBoolean_iff_disjoint_filters {k : ℕ}
    (H : Fin k → LowerSet P) :
    IsBooleanTuple H ↔
      (∀ i, (((H i).compl : UpperSet P) : Set P).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint ((((H i).compl : UpperSet P) : Set P))
        ((((H j).compl : UpperSet P) : Set P))) := by
  rw [distributive_isBoolean_iff_pairwise_top]
  constructor
  · rintro ⟨hproper, hpair⟩
    exact ⟨fun i ↦ (lowerSet_compl_nonempty_iff_ne_top (H i)).mpr (hproper i),
      fun i j hij ↦ (lowerSet_compl_disjoint_iff_sup_eq_top (H i) (H j)).mpr
        (hpair i j hij)⟩
  · rintro ⟨hne, hdisj⟩
    exact ⟨fun i ↦ (lowerSet_compl_nonempty_iff_ne_top (H i)).mp (hne i),
      fun i j hij ↦ (lowerSet_compl_disjoint_iff_sup_eq_top (H i) (H j)).mp
        (hdisj i j hij)⟩

noncomputable instance : DecidableEq (LowerSet P) := Classical.decEq _

noncomputable instance : DecidableEq (UpperSet P) := Classical.decEq _

noncomputable instance [Fintype P] : Fintype (LowerSet P) :=
  Fintype.ofInjective (fun I : LowerSet P ↦ (I : Set P)) SetLike.coe_injective

noncomputable instance [Fintype P] : Fintype (UpperSet P) :=
  Fintype.ofInjective (fun F : UpperSet P ↦ (F : Set P)) SetLike.coe_injective

abbrev DisjointFilterFamily (k : ℕ) (P : Type*) [PartialOrder P] :=
  {C : Finset (UpperSet P) //
    C.card = k ∧
    (∀ F ∈ C, ((F : UpperSet P) : Set P).Nonempty) ∧
    (∀ F ∈ C, ∀ G ∈ C, F ≠ G →
      Disjoint ((F : UpperSet P) : Set P) ((G : UpperSet P) : Set P))}

noncomputable instance [Fintype P] {k : ℕ} :
    Fintype (DisjointFilterFamily k P) := by
  classical
  exact Subtype.fintype _

noncomputable def lowerFinsetToUpperFinset :
    Finset (LowerSet P) ≃ Finset (UpperSet P) :=
  upperSetIsoLowerSet.symm.toEquiv.finsetCongr

/-- The literal unordered complement bijection in `thm:distributive`. -/
noncomputable def distributiveAntichainEquivDisjointFilters [Fintype P] {k : ℕ} :
    BooleanAntichain k (LowerSet P) ≃ DisjointFilterFamily k P where
  toFun C := ⟨lowerFinsetToUpperFinset C.1, by
    have hC := (distributive_isBooleanAntichain_iff C.1).mp C.2.2
    refine ⟨by simpa [lowerFinsetToUpperFinset, Equiv.finsetCongr_apply] using C.2.1,
      ?_, ?_⟩
    · intro F hF
      rw [lowerFinsetToUpperFinset, Equiv.finsetCongr_apply] at hF
      rcases Finset.mem_map.mp hF with ⟨I, hI, rfl⟩
      exact (lowerSet_compl_nonempty_iff_ne_top I).mpr (hC.1 I hI)
    · intro F hF G hG hFG
      rw [lowerFinsetToUpperFinset, Equiv.finsetCongr_apply] at hF hG
      rcases Finset.mem_map.mp hF with ⟨I, hI, rfl⟩
      rcases Finset.mem_map.mp hG with ⟨J, hJ, rfl⟩
      apply (lowerSet_compl_disjoint_iff_sup_eq_top I J).mpr
      apply hC.2 I hI J hJ
      intro hIJ
      apply hFG
      simp [hIJ]⟩
  invFun C := ⟨lowerFinsetToUpperFinset.symm C.1, by
    have hC := C.2
    refine ⟨by simpa [lowerFinsetToUpperFinset, Equiv.finsetCongr_apply] using C.2.1, ?_⟩
    apply (distributive_isBooleanAntichain_iff _).mpr
    constructor
    · intro I hI
      have hmap : I.compl ∈ C.1 := by
        have hI' : I ∈ C.1.map upperSetIsoLowerSet.toEquiv.toEmbedding := by
          simpa [lowerFinsetToUpperFinset, Equiv.finsetCongr_apply] using hI
        have hm := Finset.mem_map_equiv.mp hI'
        simpa [upperSetIsoLowerSet] using hm
      exact (lowerSet_compl_nonempty_iff_ne_top I).mp (hC.2.1 I.compl hmap)
    · intro I hI J hJ hIJ
      have hmapI : I.compl ∈ C.1 := by
        have hI' : I ∈ C.1.map upperSetIsoLowerSet.toEquiv.toEmbedding := by
          simpa [lowerFinsetToUpperFinset, Equiv.finsetCongr_apply] using hI
        have hm := Finset.mem_map_equiv.mp hI'
        simpa [upperSetIsoLowerSet] using hm
      have hmapJ : J.compl ∈ C.1 := by
        have hJ' : J ∈ C.1.map upperSetIsoLowerSet.toEquiv.toEmbedding := by
          simpa [lowerFinsetToUpperFinset, Equiv.finsetCongr_apply] using hJ
        have hm := Finset.mem_map_equiv.mp hJ'
        simpa [upperSetIsoLowerSet] using hm
      apply (lowerSet_compl_disjoint_iff_sup_eq_top I J).mp
      apply hC.2.2 I.compl hmapI J.compl hmapJ
      intro hc
      apply hIJ
      have := congrArg UpperSet.compl hc
      simpa using this⟩
  left_inv C := by
    apply Subtype.ext
    exact lowerFinsetToUpperFinset.symm_apply_apply C.1
  right_inv C := by
    apply Subtype.ext
    exact lowerFinsetToUpperFinset.apply_symm_apply C.1

/-- The `t^k` coefficient of the independence polynomial of the intersection
graph on nonempty order filters.  An independent vertex set is literally a
pairwise-disjoint family, so this is the graph-semantic coefficient. -/
noncomputable def filterIntersectionIndependenceCoeff [Fintype P] (k : ℕ) : ℕ :=
  Fintype.card (DisjointFilterFamily k P)

/-- Coefficientwise count for `eq:distributive-independence`; the literal graph
and polynomial identification is consumed in `DistributivePolynomial.lean`. -/
theorem distributive_independence_coefficient [Fintype P] {k : ℕ} :
    Fintype.card (BooleanAntichain k (LowerSet P)) =
      filterIntersectionIndependenceCoeff (P := P) k := by
  exact Fintype.card_congr distributiveAntichainEquivDisjointFilters

end OrderIdeals

end BooleanAntichainsKernel
