import BooleanAntichainsKernel.TopBooleanHom

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {L : Type*} [Lattice L] [OrderTop L]

lemma oneAtomSet_cases (S : Finset (Fin 1)) : S = ∅ ∨ S = univ :=
  S.eq_empty_or_nonempty.imp_right Finset.Nonempty.eq_univ

def oneAtomTopHom (x : L) : TopBooleanHom (Fin 1) L :=
  ⟨fun S ↦ if S = ∅ then x else ⊤, by
    refine ⟨?_, ?_, ?_⟩
    · intro S T
      rcases oneAtomSet_cases S with rfl | rfl <;>
        rcases oneAtomSet_cases T with rfl | rfl <;> simp
    · intro S T
      rcases oneAtomSet_cases S with rfl | rfl <;>
        rcases oneAtomSet_cases T with rfl | rfl <;> simp
    · simp⟩

lemma oneAtomTopHom_injective (x : L) (hx : x ≠ ⊤) : Function.Injective (oneAtomTopHom x).1 := by
  intro S T hST
  rcases oneAtomSet_cases S with rfl | rfl <;> rcases oneAtomSet_cases T with rfl | rfl
  · rfl
  · exact (hx (by simpa [oneAtomTopHom] using hST)).elim
  · exact (hx (by simpa [oneAtomTopHom] using hST.symm)).elim
  · rfl

def oneAtomEmbeddingOfProper (x : {x : L // x ≠ ⊤}) : TopBooleanEmbedding (Fin 1) L :=
  ⟨oneAtomTopHom x.1, oneAtomTopHom_injective x.1 x.2⟩

/-- The sole coatom is the very chosen proper element, not merely an
equinumerous parameter. This is the singleton-antichain construction. -/
lemma oneAtomTopHom_coatom (x : L) (i : Fin 1) : topHomCoatoms (oneAtomTopHom x) i = x := by
  have hU : (univ : Finset (Fin 1)) = {i} := (Finset.singleton_eq_univ i).symm
  change (if (univ.erase i : Finset (Fin 1)) = ∅ then x else ⊤) = x
  rw [hU, Finset.erase_singleton, if_pos rfl]

lemma topBooleanEmbedding_face_ne_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : TopBooleanEmbedding ι L) (S : Finset ι) (hS : S ≠ univ) : f.1.1 S ≠ ⊤ := by
  intro h
  exact hS (f.2 (h.trans f.1.2.2.2.symm))

def oneAtomEmbeddingEquivProper : TopBooleanEmbedding (Fin 1) L ≃ {x : L // x ≠ ⊤} where
  toFun f := ⟨f.1.1 ∅, topBooleanEmbedding_face_ne_top f ∅
    (Ne.symm Finset.univ_nonempty.ne_empty)⟩
  invFun := oneAtomEmbeddingOfProper
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext S
    rcases oneAtomSet_cases S with rfl | rfl
    · simp [oneAtomEmbeddingOfProper, oneAtomTopHom]
    · change (if (univ : Finset (Fin 1)) = ∅ then f.1.1 ∅ else ⊤) = f.1.1 univ
      rw [if_neg Finset.univ_nonempty.ne_empty, f.1.2.2.2]
  right_inv x := by
    apply Subtype.ext
    simp [oneAtomEmbeddingOfProper, oneAtomTopHom]

variable [Fintype L] [DecidableEq L] [OrderBot L]

/-- Every proper lattice element contributes exactly one actual size-one
Boolean antichain; the factorial bridge has value 1 here. -/
theorem singletonAntichain_count :
    Fintype.card (BooleanAntichain 1 L) = Fintype.card {x : L // x ≠ ⊤} := by
  have h := Fintype.card_congr (oneAtomEmbeddingEquivProper (L := L))
  simpa [topBooleanEmbedding_count] using h

end BooleanAntichainsKernel
