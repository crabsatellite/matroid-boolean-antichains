import BooleanAntichainsKernel.CompleteLabelledGraph
import BooleanAntichainsKernel.CycleMatroidClosure
import Mathlib.Data.Setoid.Basic

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*}

/-- Exactly the complete-graph edges internal to a block of the given
equivalence relation. Diagonal pairs remain excluded. -/
def completeSetoidEdges (s : Setoid α) : Set (Sym2 α) :=
  (completeLabelledGraph α).edgeSet ∩
    Sym2.fromRel (r := s.r) ⟨fun _ _ h ↦ s.symm' h⟩

theorem completeSetoidEdges_mem_pair (s : Setoid α) (x y : α) :
    s(x, y) ∈ completeSetoidEdges s ↔ x ≠ y ∧ s x y := Iff.rfl

theorem completeSetoidEdges_subset_ground (s : Setoid α) :
    completeSetoidEdges s ⊆ (completeLabelledGraph α).edgeSet := Set.inter_subset_left

theorem completeSetoidEdges_link (s : Setoid α) {q : Sym2 α} {x y : α}
    (h : (completeLabelledGraph α).IsLink q x y) :
    q ∈ completeSetoidEdges s ↔ s x y := by
  rw [h.1, completeSetoidEdges_mem_pair]
  exact and_iff_right h.2

theorem completeSetoid_walk_rel (s : Setoid α) {x y : (completeLabelledGraph α).vertexSet}
    (p : LabelledGraphWalk (completeLabelledGraph α) (completeSetoidEdges s) x y) :
    s x.1 y.1 := by
  induction p with
  | nil x => exact s.refl' x.1
  | cons e he h p ih => exact s.trans' ((completeSetoidEdges_link s h).mp he) ih

/-- Equality of blocks is equivalent to actual labelled reachability.
Related distinct vertices have their literal complete-graph edge. -/
theorem completeSetoid_reachable_iff (s : Setoid α) (x y : (completeLabelledGraph α).vertexSet) :
    GraphReachable (completeLabelledGraph α) (completeSetoidEdges s) x y ↔ s x.1 y.1 := by
  constructor
  · rintro ⟨p⟩
    exact completeSetoid_walk_rel s p
  · intro hrel
    by_cases hxy : x = y
    · subst y
      exact ⟨LabelledGraphWalk.nil (G := completeLabelledGraph α) x⟩
    · have hne : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
      let e : (completeLabelledGraph α).edgeSet := ⟨s(x.1, y.1), hne⟩
      have he : e.1 ∈ completeSetoidEdges s :=
        (completeSetoidEdges_mem_pair s x.1 y.1).mpr ⟨hne, hrel⟩
      exact ⟨LabelledGraphWalk.cons (G := completeLabelledGraph α) (x := x) (y := y) (z := y)
        e he ⟨rfl, hne⟩ (.nil y)⟩

variable [Finite α]

theorem completeSetoidEdges_isFlat (s : Setoid α) :
    (cycleMatroid (completeLabelledGraph α)).IsFlat (completeSetoidEdges s) := by
  apply (cycleMatroid_isFlat_iff_reach_closed (completeLabelledGraph α) _).mpr
  refine ⟨completeSetoidEdges_subset_ground s, ?_⟩
  intro e x y hlink hreach
  exact (completeSetoidEdges_link s hlink).mpr ((completeSetoid_reachable_iff s x y).mp hreach)

def completeSetoidFlat (s : Setoid α) : MatroidFlat (cycleMatroid (completeLabelledGraph α)) :=
  ⟨completeSetoidEdges s, completeSetoidEdges_isFlat s⟩

theorem completeSetoidFlat_val (s : Setoid α) : (completeSetoidFlat s).1 = completeSetoidEdges s := rfl

end BooleanAntichainsKernel
