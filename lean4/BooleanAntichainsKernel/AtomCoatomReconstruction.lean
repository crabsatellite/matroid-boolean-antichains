import BooleanAntichainsKernel.GlobalEnumerator
import BooleanAntichainsKernel.FullHeight

/-! The two literal inverse constructions in the proof of `thm:main`. -/

namespace BooleanAntichainsKernel

open Finset

variable {L : Type*} [Lattice L] [OrderBot L] [OrderTop L]

/-- The paper's coatom constructed by joining every atom except itself. -/
def coatomTuple {r : ℕ} (A : Fin r → L) (i : Fin r) : L :=
  (Finset.univ.erase i).sup A

lemma coatom_inf_eq_sup_complement {r : ℕ} (A : Fin r → L)
    (htop : Finset.univ.sup A = ⊤)
    (hmeet : ∀ S T : Finset (Fin r), S.sup A ⊓ T.sup A = (S ∩ T).sup A)
    (D : Finset (Fin r)) :
    D.inf (coatomTuple A) = (Finset.univ \ D).sup A := by
  induction D using Finset.induction_on with
  | empty => simp [htop]
  | @insert i D hi ih =>
    rw [Finset.inf_insert, ih, coatomTuple, hmeet]
    congr 1
    ext j
    simp

lemma coatom_meetFace {r : ℕ} (A : Fin r → L)
    (htop : Finset.univ.sup A = ⊤)
    (hmeet : ∀ S T : Finset (Fin r), S.sup A ⊓ T.sup A = (S ∩ T).sup A)
    (S : Finset (Fin r)) : meetFace (coatomTuple A) S = S.sup A := by
  rw [meetFace, coatom_inf_eq_sup_complement A htop hmeet,
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)]

lemma coatomTuple_isBoolean {r : ℕ} (A : Fin r → L)
    (htop : Finset.univ.sup A = ⊤)
    (hmeet : ∀ S T : Finset (Fin r), S.sup A ⊓ T.sup A = (S ∩ T).sup A)
    (hinj : Function.Injective (fun S : Finset (Fin r) ↦ S.sup A)) :
    IsBooleanTuple (coatomTuple A) := by
  constructor
  · intro S T hST
    apply hinj
    simpa only [coatom_meetFace A htop hmeet] using hST
  · intro S T
    simp only [coatom_meetFace A htop hmeet, Finset.sup_union]

lemma reconstructedAtom_coatomTuple {r : ℕ} (A : Fin r → L)
    (htop : Finset.univ.sup A = ⊤)
    (hmeet : ∀ S T : Finset (Fin r), S.sup A ⊓ T.sup A = (S ∩ T).sup A) :
    reconstructedAtom (coatomTuple A) = A := by
  funext i
  rw [reconstructedAtom_eq_meetFace_singleton, coatom_meetFace A htop hmeet,
    Finset.sup_singleton]

omit [OrderBot L] in
lemma reconstructedAtom_injective {r : ℕ} {H : Fin r → L} (hH : IsBooleanTuple H) :
    Function.Injective (reconstructedAtom H) := by
  intro i j hij
  rw [reconstructedAtom_eq_meetFace_singleton, reconstructedAtom_eq_meetFace_singleton] at hij
  have hs : ({i} : Finset (Fin r)) = {j} := hH.1 hij
  exact Finset.mem_singleton.mp (hs ▸ Finset.mem_singleton_self i)

lemma coatomTuple_reconstructedAtom {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hbot : commonMeet H = ⊥) :
    coatomTuple (reconstructedAtom H) = H := by
  funext i
  have hface := (joinFace_eq_meetFace_of_boolean hH (Finset.univ.erase i)).trans
    (meetFace_complement_singleton H i)
  simpa only [joinFace, hbot, bot_sup_eq, coatomTuple] using hface

lemma reconstructedAtoms_sup_top {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hbot : commonMeet H = ⊥) :
    Finset.univ.sup (reconstructedAtom H) = ⊤ := by
  have hface := joinFace_eq_meetFace_of_boolean hH Finset.univ
  simpa only [joinFace, hbot, bot_sup_eq, meetFace_univ] using hface

variable [DecidableEq L]

/-- The literal unordered map Phi, using the meet after deleting one member. -/
def antichainAtoms (C : Finset L) : Finset L :=
  C.image fun H ↦ (C.erase H).inf id

/-- The literal unordered map Psi, using the join after deleting one atom. -/
def basisCoatoms (A : Finset L) : Finset L :=
  A.image fun F ↦ (A.erase F).sup id

omit [OrderBot L] in
lemma antichainAtoms_orderedCarrier {r : ℕ} (H : Fin r → L)
    (hinj : Function.Injective H) :
    antichainAtoms (orderedCarrier H) = orderedCarrier (reconstructedAtom H) := by
  unfold antichainAtoms orderedCarrier
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  change ((Finset.univ.image H).erase (H i)).inf id = (Finset.univ.erase i).inf H
  rw [← Finset.image_erase hinj, Finset.inf_image]
  rfl

omit [OrderTop L] in
lemma basisCoatoms_orderedCarrier {r : ℕ} (A : Fin r → L)
    (hinj : Function.Injective A) :
    basisCoatoms (orderedCarrier A) = orderedCarrier (coatomTuple A) := by
  unfold basisCoatoms orderedCarrier
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  change ((Finset.univ.image A).erase (A i)).sup id = (Finset.univ.erase i).sup A
  rw [← Finset.image_erase hinj, Finset.sup_image]
  rfl

end BooleanAntichainsKernel
