import BooleanAntichainsKernel.CompleteGraphSetoidEdges
import BooleanAntichainsKernel.FinitePartitionLattice

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*}

section Setoids

variable [Finite α]

/-- Recover the same-block equivalence from a literal complete-graph flat,
using the original vertices and labelled walks. -/
def completeFlatSetoid (F : MatroidFlat (cycleMatroid (completeLabelledGraph α))) : Setoid α where
  r x y := GraphReachable (completeLabelledGraph α) F.1 (completeGraphVertex x) (completeGraphVertex y)
  iseqv := ⟨
    fun x ↦ (graphReachable_equivalence (completeLabelledGraph α) F.1).refl (completeGraphVertex x),
    fun {_ _} h ↦ (graphReachable_equivalence (completeLabelledGraph α) F.1).symm h,
    fun {_ _ _} h h' ↦ (graphReachable_equivalence (completeLabelledGraph α) F.1).trans h h'⟩

theorem completeFlat_pair_mem (F : MatroidFlat (cycleMatroid (completeLabelledGraph α))) (x y : α) :
    s(x, y) ∈ F.1 ↔ x ≠ y ∧ completeFlatSetoid F x y := by
  constructor
  · intro h
    have hne : x ≠ y := F.2.subset_ground h
    refine ⟨hne, ?_⟩
    change GraphReachable (completeLabelledGraph α) F.1 (completeGraphVertex x) (completeGraphVertex y)
    exact ⟨LabelledGraphWalk.cons (G := completeLabelledGraph α)
      (x := completeGraphVertex x) (y := completeGraphVertex y) (z := completeGraphVertex y)
      ⟨s(x, y), hne⟩ h ⟨rfl, hne⟩ (.nil (completeGraphVertex y))⟩
  · rintro ⟨hne, hrel⟩
    exact ((cycleMatroid_isFlat_iff_reach_closed (completeLabelledGraph α) F.1).mp F.2).2
      ⟨s(x, y), hne⟩ (completeGraphVertex x) (completeGraphVertex y) ⟨rfl, hne⟩ hrel

theorem completeFlatSetoid_setoidFlat (s : Setoid α) :
    completeFlatSetoid (completeSetoidFlat s) = s := by
  apply Setoid.ext
  intro x y
  exact completeSetoid_reachable_iff s (completeGraphVertex x) (completeGraphVertex y)

theorem completeSetoidFlat_flatSetoid (F : MatroidFlat (cycleMatroid (completeLabelledGraph α))) :
    completeSetoidFlat (completeFlatSetoid F) = F := by
  apply Subtype.ext
  ext q
  induction q using Sym2.inductionOn with
  | _ x y =>
    exact (completeSetoidEdges_mem_pair (completeFlatSetoid F) x y).trans (completeFlat_pair_mem F x y).symm

theorem completeSetoidFlat_le_iff (s t : Setoid α) :
    completeSetoidFlat s ≤ completeSetoidFlat t ↔ s ≤ t := by
  constructor
  · intro h x y hxy
    by_cases hEq : x = y
    · subst y
      exact t.refl' x
    · have he : s(x, y) ∈ completeSetoidEdges s := (completeSetoidEdges_mem_pair s x y).mpr ⟨hEq, hxy⟩
      exact ((completeSetoidEdges_mem_pair t x y).mp (h he)).2
  · intro h
    change completeSetoidEdges s ⊆ completeSetoidEdges t
    intro q
    induction q using Sym2.inductionOn with
    | _ x y =>
      intro hq
      have hxy := (completeSetoidEdges_mem_pair s x y).mp hq
      exact (completeSetoidEdges_mem_pair t x y).mpr ⟨hxy.1, h hxy.2⟩

def setoidCompleteFlatOrderIso : Setoid α ≃o MatroidFlat (cycleMatroid (completeLabelledGraph α)) where
  toFun := completeSetoidFlat
  invFun := completeFlatSetoid
  left_inv := completeFlatSetoid_setoidFlat
  right_inv := completeSetoidFlat_flatSetoid
  map_rel_iff' := completeSetoidFlat_le_iff _ _

end Setoids

section FinitePartitions

variable [Fintype α] [DecidableEq α]

/-- The paper's literal partition lattice and the literal flat lattice
of the complete-graph cycle matroid. No carrier replacement is left unpaid. -/
noncomputable def finitePartitionCompleteFlatOrderIso :
    Finpartition (Finset.univ : Finset α) ≃o MatroidFlat (cycleMatroid (completeLabelledGraph α)) :=
  finitePartitionSetoidOrderIso.trans setoidCompleteFlatOrderIso

theorem finitePartitionCompleteFlatOrderIso_mem_pair
    (P : Finpartition (Finset.univ : Finset α)) (x y : α) :
    s(x, y) ∈ (finitePartitionCompleteFlatOrderIso P).1 ↔
      x ≠ y ∧ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B := by
  change s(x, y) ∈ completeSetoidEdges (finitePartitionSetoid P) ↔ _
  rw [completeSetoidEdges_mem_pair, finitePartitionSetoid_same_block]

theorem finitePartitionCompleteFlatOrderIso_symm_relation
    (F : MatroidFlat (cycleMatroid (completeLabelledGraph α))) :
    finitePartitionSetoid (finitePartitionCompleteFlatOrderIso.symm F) = completeFlatSetoid F :=
  finitePartitionSetoid_ofSetoid (completeFlatSetoid F)

theorem finitePartitionCompleteFlatOrderIso_symm_blocks
    (F : MatroidFlat (cycleMatroid (completeLabelledGraph α))) (x y : α) :
    (∃ B ∈ (finitePartitionCompleteFlatOrderIso.symm F).parts, x ∈ B ∧ y ∈ B) ↔
      GraphReachable (completeLabelledGraph α) F.1 (completeGraphVertex x) (completeGraphVertex y) := by
  rw [← finitePartitionSetoid_same_block, finitePartitionCompleteFlatOrderIso_symm_relation]
  rfl

end FinitePartitions

end BooleanAntichainsKernel
