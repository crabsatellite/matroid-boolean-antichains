import BooleanAntichainsKernel.HomEnumeration

/-! Product embeddings are exactly pairs of active embeddings whose label
sets cover the entire Boolean ground, as in the proof of `thm:product`. -/

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι L K : Type*} [Fintype ι] [DecidableEq ι]
variable [Lattice L] [OrderTop L] [Lattice K] [OrderTop K]

abbrev CoveredHomPairs (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L K : Type*) [Lattice L] [OrderTop L] [Lattice K] [OrderTop K] :=
  {p : TopBooleanHom ι L × TopBooleanHom ι K // activeAtoms p.1 ∪ activeAtoms p.2 = Finset.univ}

abbrev CoveredActivePairs (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L K : Type*) [Lattice L] [OrderTop L] [Lattice K] [OrderTop K] :=
  {p : ActiveHomData ι L × ActiveHomData ι K // p.1.1 ∪ p.2.1 = Finset.univ}

noncomputable def productEmbeddingEquivCoveredHomPairs :
    TopBooleanEmbedding ι (L × K) ≃ CoveredHomPairs ι L K :=
  (topBooleanHomProductEquiv (ι := ι) (L := L) (K := K)).subtypeEquiv (fun f ↦ by
    exact prodTopBooleanHom_injective_iff (fstTopBooleanHom f) (sndTopBooleanHom f))

noncomputable def coveredActivePairsEquivHomPairs : CoveredActivePairs ι L K ≃ CoveredHomPairs ι L K :=
  ((activeHomDecompositionEquiv (ι := ι) (L := L)).prodCongr
    (activeHomDecompositionEquiv (ι := ι) (L := K))).subtypeEquiv (fun p ↦ by
      rcases p with ⟨⟨A, f⟩, ⟨B, g⟩⟩
      change A ∪ B = Finset.univ ↔
        activeAtoms (extendActiveEmbedding A f) ∪ activeAtoms (extendActiveEmbedding B g) = Finset.univ
      rw [activeAtoms_extend, activeAtoms_extend])

noncomputable def coveredActivePairsEquivProductEmbedding :
    CoveredActivePairs ι L K ≃ TopBooleanEmbedding ι (L × K) :=
  coveredActivePairsEquivHomPairs.trans productEmbeddingEquivCoveredHomPairs.symm

abbrev CoverEmbeddingSigma (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L K : Type*) [Lattice L] [OrderTop L] [Lattice K] [OrderTop K] :=
  Σ A : Finset ι, Σ B : Finset ι,
    {_p : TopBooleanEmbedding A L × TopBooleanEmbedding B K // A ∪ B = Finset.univ}

def coveredActivePairsEquivSigma : CoveredActivePairs ι L K ≃ CoverEmbeddingSigma ι L K where
  toFun p := ⟨p.1.1.1, p.1.2.1, ⟨(p.1.1.2, p.1.2.2), p.2⟩⟩
  invFun p := ⟨(⟨p.1, p.2.2.1.1⟩, ⟨p.2.1, p.2.2.1.2⟩), p.2.2.2⟩
  left_inv p := by rcases p with ⟨⟨⟨A, f⟩, ⟨B, g⟩⟩, h⟩; rfl
  right_inv p := by rcases p with ⟨A, B, ⟨⟨f, g⟩, h⟩⟩; rfl

lemma card_fixed_proposition_subtype {T : Type*} [Fintype T] (p : Prop) [Decidable p] :
    Fintype.card {_x : T // p} = if p then Fintype.card T else 0 := by
  rw [Fintype.card_subtype]
  by_cases hp : p <;> simp [hp]

variable [Fintype L] [Fintype K]

/-- Exact product-embedding cardinality before grouping active sets by size. -/
theorem productEmbedding_count_cover :
    Fintype.card (TopBooleanEmbedding ι (L × K)) =
      ∑ A : Finset ι, ∑ B : Finset ι,
        if A ∪ B = Finset.univ then
          Fintype.card (TopBooleanEmbedding A L) * Fintype.card (TopBooleanEmbedding B K)
        else 0 := by
  calc
    _ = Fintype.card (CoveredActivePairs ι L K) :=
      (Fintype.card_congr coveredActivePairsEquivProductEmbedding).symm
    _ = Fintype.card (CoverEmbeddingSigma ι L K) := Fintype.card_congr coveredActivePairsEquivSigma
    _ = _ := by
      simp only [Fintype.card_sigma, card_fixed_proposition_subtype, Fintype.card_prod]

end BooleanAntichainsKernel
