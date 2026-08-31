import BooleanAntichainsKernel.SpanAtoms

/-! Exact transport of Boolean antichains and their atoms along a lattice
order isomorphism. The interval theorem consumes this transport. -/

namespace BooleanAntichainsKernel

open Finset

variable {L K : Type*} [Lattice L] [OrderTop L] [Lattice K] [OrderTop K]

lemma orderIso_meetFace (e : L ≃o K) {k : ℕ} (H : Fin k → L) (S : Finset (Fin k)) :
    meetFace (fun i ↦ e (H i)) S = e (meetFace H S) :=
  (map_finset_inf e (Finset.univ \ S) H).symm

lemma isBooleanTuple_orderIso (e : L ≃o K) {k : ℕ} (H : Fin k → L) :
    IsBooleanTuple (fun i ↦ e (H i)) ↔ IsBooleanTuple H := by
  constructor
  · intro h
    constructor
    · intro S T hST
      apply h.1
      rw [orderIso_meetFace, orderIso_meetFace, hST]
    · intro S T
      apply e.injective
      have hj := h.2 S T
      simpa only [orderIso_meetFace, map_sup] using hj
  · intro h
    constructor
    · intro S T hST
      apply h.1
      apply e.injective
      simpa only [orderIso_meetFace] using hST
    · intro S T
      rw [orderIso_meetFace, orderIso_meetFace, orderIso_meetFace, h.2, map_sup]

variable [DecidableEq L] [DecidableEq K]

def mapFamily (e : L ≃o K) (C : Finset L) : Finset K := e.toEquiv.finsetCongr C

omit [OrderTop L] [OrderTop K] [DecidableEq L] [DecidableEq K] in
lemma mapFamily_card (e : L ≃o K) (C : Finset L) : (mapFamily e C).card = C.card :=
  Finset.card_map _

omit [OrderTop L] [OrderTop K] in
lemma mapFamily_orderedCarrier (e : L ≃o K) {k : ℕ} (H : Fin k → L) :
    mapFamily e (orderedCarrier H) = orderedCarrier (fun i ↦ e (H i)) := by
  unfold mapFamily orderedCarrier
  rw [Equiv.finsetCongr_apply, Finset.map_eq_image, Finset.image_image]
  rfl

lemma isBooleanAntichain_mapFamily (e : L ≃o K) (C : Finset L) (hC : IsBooleanAntichain C) :
    IsBooleanAntichain (mapFamily e C) := by
  let f : Fin C.card ≃ C := (Finset.equivFin C).symm
  let H : Fin C.card → L := fun i ↦ (f i).1
  have hH : IsBooleanTuple H := (isBooleanTuple_iff_antichain_of_equiv C f).mpr hC
  have hm := orderedCarrier_isBoolean ((isBooleanTuple_orderIso e H).mpr hH)
  have hc : orderedCarrier H = C := orderedCarrier_of_equiv C f
  have hmap : orderedCarrier (fun i ↦ e (H i)) = mapFamily e C :=
    (mapFamily_orderedCarrier e H).symm.trans (congrArg (mapFamily e) hc)
  exact hmap ▸ hm

lemma mapFamily_erase_inf (e : L ≃o K) (C : Finset L) (a : L) :
    ((mapFamily e C).erase (e a)).inf id = e ((C.erase a).inf id) := by
  have hm : (mapFamily e C).erase (e a) = (C.erase a).map e.toEquiv.toEmbedding :=
    (Finset.map_erase e.toEquiv.toEmbedding C a).symm
  rw [hm, Finset.inf_map]
  exact (map_finset_inf e (C.erase a) id).symm

lemma antichainAtoms_mapFamily (e : L ≃o K) (C : Finset L) :
    antichainAtoms (mapFamily e C) = mapFamily e (antichainAtoms C) := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, hyz⟩
    rcases Finset.mem_map.mp hy with ⟨a, ha, rfl⟩
    change ((mapFamily e C).erase (e a)).inf id = z at hyz
    rw [mapFamily_erase_inf e C a] at hyz
    exact Finset.mem_map.mpr ⟨(C.erase a).inf id,
      Finset.mem_image.mpr ⟨a, ha, rfl⟩, hyz⟩
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨a, ha, haz⟩
    rcases Finset.mem_image.mp ha with ⟨b, hb, hba⟩
    refine Finset.mem_image.mpr ⟨e b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    rw [mapFamily_erase_inf, hba]
    exact haz

lemma spanAtomFinset_mapFamily [Fintype L] [Fintype K] (e : L ≃o K)
    (C : Finset L) (hC : IsBooleanAntichain C) :
    spanAtomFinset (mapFamily e C) = mapFamily e (spanAtomFinset C) := by
  rw [spanAtomFinset_eq_antichainAtoms _ (isBooleanAntichain_mapFamily e C hC),
    spanAtomFinset_eq_antichainAtoms C hC, antichainAtoms_mapFamily]

variable [OrderBot L] [OrderBot K]

def booleanAntichainOrderIsoEquiv (e : L ≃o K) (k : ℕ) :
    BooleanAntichain k L ≃ BooleanAntichain k K where
  toFun C := ⟨mapFamily e C.1, (mapFamily_card e C.1).trans C.2.1,
    isBooleanAntichain_mapFamily e C.1 C.2.2⟩
  invFun D := ⟨mapFamily e.symm D.1, (mapFamily_card e.symm D.1).trans D.2.1,
    isBooleanAntichain_mapFamily e.symm D.1 D.2.2⟩
  left_inv C := Subtype.ext (e.toEquiv.finsetCongr.symm_apply_apply C.1)
  right_inv D := Subtype.ext (e.toEquiv.finsetCongr.apply_symm_apply D.1)

@[simp] lemma booleanAntichainOrderIsoEquiv_val (e : L ≃o K) (k : ℕ)
    (C : BooleanAntichain k L) : (booleanAntichainOrderIsoEquiv e k C).1 = mapFamily e C.1 := rfl

omit [Lattice K] [OrderTop K] [DecidableEq K] [OrderBot K] in
/-- Change only the size certificate along a proved numerical equality. -/
def booleanAntichainSizeEquiv {k l : ℕ} (hkl : k = l) : BooleanAntichain k L ≃ BooleanAntichain l L where
  toFun C := ⟨C.1, C.2.1.trans hkl, C.2.2⟩
  invFun D := ⟨D.1, D.2.1.trans hkl.symm, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end BooleanAntichainsKernel
