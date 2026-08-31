import BooleanAntichainsKernel.TopBooleanHom
import BooleanAntichainsKernel.HeightGapEndpoints

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The source and target Boolean lattices retain their full subset carriers. -/
theorem booleanEmbedding_size_le_dimension {n k : ℕ}
    (f : TopBooleanEmbedding (Fin k) (Finset (Fin n))) : k ≤ n := by
  have hc := Fintype.card_le_of_injective f.1.1 f.2
  simp only [Fintype.card_finset, Fintype.card_fin] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc

theorem booleanLattice_count_above_dimension (n k : ℕ) (hk : n < k) :
    Fintype.card (BooleanAntichain k (Finset (Fin n))) = 0 := by
  have hempty : IsEmpty (TopBooleanEmbedding (Fin k) (Finset (Fin n))) :=
    ⟨fun f ↦ hk.not_ge (booleanEmbedding_size_le_dimension f)⟩
  have hc := Fintype.card_eq_zero_iff.mpr hempty
  rw [topBooleanEmbedding_count] at hc
  exact (Nat.mul_eq_zero.mp hc).resolve_right (Nat.factorial_ne_zero k)

def booleanOneIdentityEmbedding : TopBooleanEmbedding (Fin 1) (Finset (Fin 1)) :=
  ⟨⟨id, ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, rfl⟩⟩, Function.injective_id⟩

lemma booleanOneEmbedding_eq_identity
    (f : TopBooleanEmbedding (Fin 1) (Finset (Fin 1))) :
    f = booleanOneIdentityEmbedding := by
  have he : f.1.1 ∅ = ∅ := by
    by_contra hne
    have ht : f.1.1 ∅ = Finset.univ := (Finset.nonempty_iff_ne_empty.mpr hne).eq_univ
    have hc : (∅ : Finset (Fin 1)) = Finset.univ := f.2 (ht.trans f.1.2.2.2.symm)
    exact Finset.univ_nonempty.ne_empty hc.symm
  apply Subtype.ext
  apply Subtype.ext
  funext S
  change f.1.1 S = S
  rcases S.eq_empty_or_nonempty with hS | hS
  · simpa [hS] using he
  · rw [hS.eq_univ]
    exact f.1.2.2.2

theorem booleanOne_count_one :
    Fintype.card (BooleanAntichain 1 (Finset (Fin 1))) = 1 := by
  have hc : Fintype.card (TopBooleanEmbedding (Fin 1) (Finset (Fin 1))) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨booleanOneIdentityEmbedding, booleanOneEmbedding_eq_identity⟩
  simpa [topBooleanEmbedding_count] using hc

theorem booleanOne_count (k : ℕ) :
    Fintype.card (BooleanAntichain k (Finset (Fin 1))) = if k ≤ 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · simpa using (booleanAntichain_count_zero (L := Finset (Fin 1)))
  · simpa using booleanOne_count_one
  · rw [booleanLattice_count_above_dimension 1 (k + 2) (by omega), if_neg (by omega)]

theorem booleanZero_count_succ (k : ℕ) :
    Fintype.card (BooleanAntichain (k + 1) (Finset (Fin 0))) = 0 :=
  booleanLattice_count_above_dimension 0 (k + 1) (by omega)

end BooleanAntichainsKernel
