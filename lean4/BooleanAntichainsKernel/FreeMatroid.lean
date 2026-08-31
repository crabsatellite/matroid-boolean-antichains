import BooleanAntichainsKernel.BasisChoices
import BooleanAntichainsKernel.MinorRank
import BooleanAntichainsKernel.SimplificationBases
import BooleanAntichainsKernel.LatticeTransport

/-! Literal free-matroid objects in the proof of cor:boolean-lattice. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical Matroid

variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem freeOn_isFlat_iff (E X : Set α) :
    (Matroid.freeOn E).IsFlat X ↔ X ⊆ E := by
  rw [Matroid.isFlat_iff_closure_eq, Matroid.freeOn_closure_eq, Set.inter_eq_left]

/-- The Boolean lattice is literally the flat lattice of the free matroid.
The forward map takes the actual flat's elements; the inverse retains them. -/
noncomputable def freeOnUnivFlatOrderIsoFinset :
    MatroidFlat (Matroid.freeOn (Set.univ : Set α)) ≃o Finset α where
  toFun F := F.1.toFinset
  invFun S := ⟨(S : Set α), (freeOn_isFlat_iff _ _).mpr (Set.subset_univ _)⟩
  left_inv F := Subtype.ext (Set.coe_toFinset F.1)
  right_inv S := by simp
  map_rel_iff' := by
    intro F G
    change F.1.toFinset ⊆ G.1.toFinset ↔ F.1 ⊆ G.1
    simp only [Set.toFinset_subset_toFinset]

theorem freeOn_flat_rank (E : Set α) (F : MatroidFlat (Matroid.freeOn E)) :
    MatroidFlat.rank F = F.1.ncard :=
  matroidRank_indep (Matroid.freeOn_indep F.2.subset_ground)

theorem freeOn_top_rank (E : Set α) :
    MatroidFlat.rank (⊤ : MatroidFlat (Matroid.freeOn E)) = E.ncard :=
  freeOn_flat_rank E ⊤

omit [Fintype α] in
/-- Contracting the actual subset removes exactly those free elements. -/
theorem freeOn_contract_eq (E X : Set α) (hX : X ⊆ E) :
    (Matroid.freeOn E) ／ X = Matroid.freeOn (E \ X) := by
  apply Matroid.eq_freeOn_iff.mpr
  refine ⟨rfl, ?_⟩
  apply (Matroid.freeOn_indep hX).contract_indep_iff.mpr
  exact ⟨Set.disjoint_sdiff_left, Matroid.freeOn_indep (Set.union_subset Set.sdiff_subset hX)⟩

noncomputable def freeOnBase (E : Set α) : MatroidBases (Matroid.freeOn E) :=
  ⟨E.toFinset, Matroid.freeOn_isBase_iff.mpr (Set.coe_toFinset E)⟩

/-- Every simplified basis is the family of classes of the genuine unique
ground-set basis. This proves uniqueness after simplification as well. -/
theorem freeOn_simplifiedBasis_eq (E : Set α) (A : SimplifiedBasis (Matroid.freeOn E)) :
    A = basisToSimplifiedBasis (freeOnBase E) := by
  have hchoice : ∀ F : A.1, ∃ e, e ∈ parallelClassElements F.1 :=
    fun F ↦ parallelClassElements_nonempty (A.2.1 F.1 F.2)
  choose f hf using hchoice
  let g : BasisClassChoice A := fun F ↦ ⟨f F, hf F⟩
  have hset : (chosenBasisElements A g : Set α) = E :=
    Matroid.freeOn_isBase_iff.mp (chosenBasisElements_isBase A g)
  have hfin : chosenBasisElements A g = E.toFinset := by
    apply Finset.coe_injective
    simpa using hset
  apply Subtype.ext
  change A.1 = basisClassSet (M := Matroid.freeOn E) E.toFinset
  rw [← chosenBasisElements_classes A g, hfin]

theorem freeOn_simplifiedBasis_count (E : Set α) :
    Fintype.card (SimplifiedBasis (Matroid.freeOn E)) = 1 :=
  Fintype.card_eq_one_iff.mpr
    ⟨basisToSimplifiedBasis (freeOnBase E), freeOn_simplifiedBasis_eq E⟩

theorem freeOn_actual_simplification_basis_count (E : Set α) :
    Fintype.card (MatroidBases (simplificationOnFlats (Matroid.freeOn E))) = 1 := by
  rw [← simplifiedBasis_count_eq_actualMatroidBases, freeOn_simplifiedBasis_count]

theorem freeOn_contraction_simplifiedBasis_count (E X : Set α) (hX : X ⊆ E) :
    Fintype.card (SimplifiedBasis ((Matroid.freeOn E) ／ X)) = 1 := by
  rw [freeOn_contract_eq E X hX, freeOn_simplifiedBasis_count]

end BooleanAntichainsKernel
