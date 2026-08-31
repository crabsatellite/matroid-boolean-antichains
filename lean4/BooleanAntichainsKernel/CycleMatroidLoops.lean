import BooleanAntichainsKernel.CycleMatroidClosure
import Mathlib.Combinatorics.Matroid.Loop

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

theorem graphReachable_empty_iff (G : Graph α β) (x y : G.vertexSet) :
    GraphReachable G ∅ x y ↔ x = y := by
  rw [graphReachable_iff_support, graphSupport_empty, SimpleGraph.reachable_bot]

/-- A walk using one original edge either stays at its vertex or has
exactly that edge's endpoints. Repeated traversals do not introduce a new relation. -/
theorem graphReachable_singleton_iff (G : Graph α β) (e : G.edgeSet) (x y : G.vertexSet) :
    GraphReachable G {e.1} x y ↔ x = y ∨ G.IsLink e.1 x.1 y.1 := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Or.inl rfl
    | @cons x y z f hf h p ih =>
      have hfe : f.1 = e.1 := Set.mem_singleton_iff.mp hf
      have h' : G.IsLink e.1 x.1 y.1 := hfe ▸ h
      rcases ih with hyz | htail
      · exact Or.inr (by simpa only [hyz] using h')
      · exact Or.inl (Subtype.ext (h'.symm.right_unique htail))
  · rintro (rfl | h)
    · exact ⟨LabelledGraphWalk.nil x⟩
    · exact ⟨LabelledGraphWalk.cons e (by simp) h (.nil y)⟩

variable (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

/-- Matroid loops are exactly the original graph loops, on original edge
labels, including when the graph has loops at several different vertices. -/
theorem cycleMatroid_isLoop_iff (e : β) :
    (cycleMatroid G).IsLoop e ↔ ∃ x : α, G.IsLoopAt e x := by
  change e ∈ (cycleMatroid G).closure ∅ ↔ _
  rw [cycleMatroid_closure_eq G ∅ (Set.empty_subset _)]
  constructor
  · rintro ⟨x, y, hlink, hxy⟩
    have h := (graphReachable_empty_iff G x y).mp hxy
    subst y
    exact ⟨x.1, hlink⟩
  · rintro ⟨x, hx⟩
    let xx : G.vertexSet := ⟨x, hx.vertex_mem⟩
    exact ⟨xx, xx, hx, ⟨LabelledGraphWalk.nil xx⟩⟩

theorem cycleMatroid_loops_eq :
    (cycleMatroid G).loops = {e : β | ∃ x : α, G.IsLoopAt e x} := by
  ext e
  exact cycleMatroid_isLoop_iff G e

theorem cycleMatroid_isNonloop_ends_iff (e : G.edgeSet) :
    (cycleMatroid G).IsNonloop e.1 ↔ ¬(graphEdgeEnds G e).IsDiag := by
  rw [← Matroid.not_isLoop_iff (M := cycleMatroid G) (e := e.1) e.2,
    cycleMatroid_isLoop_iff G e.1, ← graphEdgeEnds_isDiag_iff G e]

end BooleanAntichainsKernel
