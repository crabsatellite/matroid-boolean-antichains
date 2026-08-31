import BooleanAntichainsKernel.TopBooleanHom

namespace BooleanAntichainsKernel

open scoped Classical

variable {ι L K : Type*} [Fintype ι] [DecidableEq ι]
variable [Lattice L] [OrderTop L] [Lattice K] [OrderTop K]

def mapTopBooleanHom (e : L ≃o K) (f : TopBooleanHom ι L) : TopBooleanHom ι K :=
  ⟨fun S ↦ e (f.1 S), by
    refine ⟨?_, ?_, ?_⟩
    · intro S T
      change e (f.1 (S ∪ T)) = e (f.1 S) ⊔ e (f.1 T)
      rw [f.2.1, e.map_sup]
    · intro S T
      change e (f.1 (S ∩ T)) = e (f.1 S) ⊓ e (f.1 T)
      rw [f.2.2.1, e.map_inf]
    · change e (f.1 Finset.univ) = ⊤
      rw [f.2.2.2, e.map_top]⟩

def mapTopBooleanEmbedding (e : L ≃o K) (f : TopBooleanEmbedding ι L) :
    TopBooleanEmbedding ι K :=
  ⟨mapTopBooleanHom e f.1, e.injective.comp f.2⟩

@[simp] theorem mapTopBooleanEmbedding_apply (e : L ≃o K) (f : TopBooleanEmbedding ι L)
    (S : Finset ι) : (mapTopBooleanEmbedding e f).1.1 S = e (f.1.1 S) := rfl

/-- Transport every image by the actual lattice order isomorphism. -/
def topBooleanEmbeddingCodomainEquiv (e : L ≃o K) :
    TopBooleanEmbedding ι L ≃ TopBooleanEmbedding ι K where
  toFun := mapTopBooleanEmbedding e
  invFun := mapTopBooleanEmbedding e.symm
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext S
    exact e.symm_apply_apply (f.1.1 S)
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext S
    exact e.apply_symm_apply (f.1.1 S)

abbrev TopBooleanEmbeddingAtBottom (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L : Type*) [Lattice L] [OrderTop L] (X : L) :=
  {f : TopBooleanEmbedding ι L // f.1.1 ∅ = X}

abbrev BottomTopBooleanEmbedding (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L : Type*) [Lattice L] [OrderTop L] [OrderBot L] :=
  TopBooleanEmbeddingAtBottom ι L ⊥

noncomputable instance [Fintype L] (X : L) : Fintype (TopBooleanEmbeddingAtBottom ι L X) :=
  Subtype.fintype _

variable [OrderBot L] [OrderBot K]

def bottomTopBooleanEmbeddingCodomainEquiv (e : L ≃o K) :
    BottomTopBooleanEmbedding ι L ≃ BottomTopBooleanEmbedding ι K :=
  (topBooleanEmbeddingCodomainEquiv (ι := ι) e).subtypeEquiv (fun f ↦ by
    change f.1.1 ∅ = ⊥ ↔ e (f.1.1 ∅) = ⊥
    rw [← e.map_bot, e.injective.eq_iff])

end BooleanAntichainsKernel
