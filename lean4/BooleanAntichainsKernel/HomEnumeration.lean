import BooleanAntichainsKernel.ActiveHomDecomposition
import Mathlib.Data.Finset.Powerset

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι κ L : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Lattice L] [OrderTop L]

def reindexTopBooleanHom (e : ι ≃ κ) (f : TopBooleanHom ι L) : TopBooleanHom κ L :=
  ⟨fun S ↦ f.1 (e.symm.finsetCongr S), by
    refine ⟨?_, ?_, ?_⟩
    · intro S T
      dsimp only
      simp only [Equiv.finsetCongr_apply, Finset.map_union, f.2.1]
    · intro S T
      dsimp only
      simp only [Equiv.finsetCongr_apply, Finset.map_inter, f.2.2.1]
    · dsimp only
      simp only [Equiv.finsetCongr_apply, Finset.map_univ_equiv, f.2.2.2]⟩

def reindexTopBooleanEmbedding (e : ι ≃ κ) (f : TopBooleanEmbedding ι L) :
    TopBooleanEmbedding κ L :=
  ⟨reindexTopBooleanHom e f.1, fun _S _T hST ↦ e.symm.finsetCongr.injective (f.2 hST)⟩

/-- A genuine label equivalence transports embeddings; no label count is
substituted for the carrier until this equivalence is consumed. -/
def topBooleanEmbeddingDomainEquiv (e : ι ≃ κ) :
    TopBooleanEmbedding ι L ≃ TopBooleanEmbedding κ L where
  toFun := reindexTopBooleanEmbedding e
  invFun := reindexTopBooleanEmbedding e.symm
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext S
    exact congrArg f.1.1 (e.finsetCongr.symm_apply_apply S)
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext S
    exact congrArg f.1.1 (e.finsetCongr.apply_symm_apply S)

variable [Fintype L] [DecidableEq L] [OrderBot L]

theorem topBooleanEmbedding_count_general :
    Fintype.card (TopBooleanEmbedding ι L) =
      (Fintype.card ι).factorial * Fintype.card (BooleanAntichain (Fintype.card ι) L) := by
  rw [Fintype.card_congr (topBooleanEmbeddingDomainEquiv (L := L) (Fintype.equivFin ι)),
    topBooleanEmbedding_count, Nat.mul_comm]

lemma sum_finsets_by_card (k : ℕ) (w : ℕ → ℕ) :
    (∑ S : Finset (Fin k), w S.card) =
      ∑ a ∈ Finset.range (k + 1), (k.choose a) * w a := by
  let U : Finset (Finset (Fin k)) := Finset.univ
  have hmap : ∀ S ∈ U, S.card ∈ Finset.range (k + 1) := by
    intro S _
    apply Finset.mem_range.mpr
    have hc : S.card ≤ k := by simpa using Finset.card_le_card (Finset.subset_univ S)
    omega
  calc
    _ = ∑ a ∈ Finset.range (k + 1), ∑ S ∈ U.filter (fun S ↦ S.card = a), w S.card :=
      (Finset.sum_fiberwise_of_maps_to (s := U) (t := Finset.range (k + 1))
        (g := Finset.card) hmap (fun S ↦ w S.card)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have hsets : U.filter (fun S ↦ S.card = a) = (Finset.univ : Finset (Fin k)).powersetCard a := by
        ext S
        simp [U, Finset.mem_powersetCard]
      calc
        _ = ∑ _S ∈ U.filter (fun S ↦ S.card = a), w a := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [(Finset.mem_filter.mp hS).2]
        _ = (U.filter (fun S ↦ S.card = a)).card * w a := by simp
        _ = (k.choose a) * w a := by rw [hsets, Finset.card_powersetCard]; simp

/-- The paper's binomial transform `eta_k(L)`. -/
noncomputable def etaCount (k : ℕ) (L : Type*) [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] : ℕ :=
  ∑ a ∈ Finset.range (k + 1), (k.choose a) *
    (a.factorial * Fintype.card (BooleanAntichain a L))

/-- The active-set decomposition earns the interpretation of the displayed
binomial transform as the number of all top-preserving homomorphisms. -/
theorem topBooleanHom_count_eq_eta (k : ℕ) :
    Fintype.card (TopBooleanHom (Fin k) L) = etaCount k L := by
  calc
    _ = Fintype.card (ActiveHomData (Fin k) L) :=
      (Fintype.card_congr activeHomDecompositionEquiv).symm
    _ = ∑ A : Finset (Fin k), Fintype.card (TopBooleanEmbedding A L) := Fintype.card_sigma
    _ = ∑ A : Finset (Fin k), A.card.factorial * Fintype.card (BooleanAntichain A.card L) := by
      apply Finset.sum_congr rfl
      intro A _
      simpa using topBooleanEmbedding_count_general (ι := A) (L := L)
    _ = etaCount k L := sum_finsets_by_card k (fun a ↦ a.factorial * Fintype.card (BooleanAntichain a L))

variable {K : Type*} [Lattice K] [OrderTop K]

def fstTopBooleanHom (f : TopBooleanHom ι (L × K)) : TopBooleanHom ι L :=
  ⟨fun S ↦ (f.1 S).1, by
    refine ⟨?_, ?_, ?_⟩
    · intro S T
      exact congrArg Prod.fst (f.2.1 S T)
    · intro S T
      exact congrArg Prod.fst (f.2.2.1 S T)
    · exact congrArg Prod.fst f.2.2.2⟩

def sndTopBooleanHom (f : TopBooleanHom ι (L × K)) : TopBooleanHom ι K :=
  ⟨fun S ↦ (f.1 S).2, by
    refine ⟨?_, ?_, ?_⟩
    · intro S T
      exact congrArg Prod.snd (f.2.1 S T)
    · intro S T
      exact congrArg Prod.snd (f.2.2.1 S T)
    · exact congrArg Prod.snd f.2.2.2⟩

def topBooleanHomProductEquiv :
    TopBooleanHom ι (L × K) ≃ TopBooleanHom ι L × TopBooleanHom ι K where
  toFun f := (fstTopBooleanHom f, sndTopBooleanHom f)
  invFun fg := prodTopBooleanHom fg.1 fg.2
  left_inv f := by apply Subtype.ext; rfl
  right_inv fg := by
    rcases fg with ⟨f, g⟩
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- Equation `eq:product-transform`; the positive coefficient convolution
still needs its separate active-cover multiplicity calculation. -/
theorem etaCount_product [Fintype K] [DecidableEq K] [OrderBot K] (k : ℕ) :
    etaCount k (L × K) = etaCount k L * etaCount k K := by
  calc
    _ = Fintype.card (TopBooleanHom (Fin k) (L × K)) := (topBooleanHom_count_eq_eta k).symm
    _ = Fintype.card (TopBooleanHom (Fin k) L) * Fintype.card (TopBooleanHom (Fin k) K) :=
      (Fintype.card_congr topBooleanHomProductEquiv).trans (Fintype.card_prod _ _)
    _ = etaCount k L * etaCount k K := by rw [topBooleanHom_count_eq_eta, topBooleanHom_count_eq_eta]

end BooleanAntichainsKernel
