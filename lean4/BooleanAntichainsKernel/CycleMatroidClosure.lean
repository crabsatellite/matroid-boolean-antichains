import BooleanAntichainsKernel.CycleMatroidSubsetBasis
import BooleanAntichainsKernel.MultigraphConnectedInsert

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

theorem cycleMatroid_mem_closure_forest_iff {I : Set β} (hI : GraphEdgeForest G I)
    (e : G.edgeSet) {x y : G.vertexSet} (hlink : G.IsLink e.1 x.1 y.1) :
    e.1 ∈ (cycleMatroid G).closure I ↔ GraphReachable G I x y := by
  have hMI := (cycleMatroid_indep_iff G I).mpr hI
  constructor
  · intro hc
    by_contra hn
    have hins := (cycleMatroid_indep_iff G (insert e.1 I)).mpr (graphEdgeForest_insert hI e hlink hn)
    have heI := (hMI.mem_closure_iff'.mp hc).2 hins
    exact hn ⟨LabelledGraphWalk.cons e heI hlink (.nil y)⟩
  · intro hxy
    apply hMI.mem_closure_iff'.mpr
    refine ⟨e.2, ?_⟩
    intro hins
    by_contra heI
    exact graphEdgeForest_insert_not_connected ((cycleMatroid_indep_iff G _).mp hins) heI hlink hxy

/-- The actual cycle-matroid closure recognizes precisely original
endpoints already joined by an original labelled walk in X. -/
theorem cycleMatroid_mem_closure_iff (X : Set β) (hX : X ⊆ G.edgeSet)
    (e : G.edgeSet) {x y : G.vertexSet} (hlink : G.IsLink e.1 x.1 y.1) :
    e.1 ∈ (cycleMatroid G).closure X ↔ GraphReachable G X x y := by
  obtain ⟨I, hI⟩ := (cycleMatroid G).exists_isBasis X hX
  have hs := cycleMatroid_isBasis_reachability G hI
  rw [← hI.closure_eq_closure, cycleMatroid_mem_closure_forest_iff G hs.1 e hlink]
  exact hs.2.2 x y

theorem cycleMatroid_closure_eq (X : Set β) (hX : X ⊆ G.edgeSet) :
    (cycleMatroid G).closure X =
      {e : β | ∃ x y : G.vertexSet, G.IsLink e x.1 y.1 ∧ GraphReachable G X x y} := by
  ext e
  constructor
  · intro hc
    have he : e ∈ G.edgeSet := (cycleMatroid G).closure_subset_ground X hc
    let ee : G.edgeSet := ⟨e, he⟩
    let uv := (graphEdgeEndpoints G ee).1
    have hlink : G.IsLink ee.1 uv.1.1 uv.2.1 := (graphEdgeEndpoints G ee).2
    exact ⟨uv.1, uv.2, hlink, (cycleMatroid_mem_closure_iff G X hX ee hlink).mp hc⟩
  · rintro ⟨x, y, hlink, hxy⟩
    exact (cycleMatroid_mem_closure_iff G X hX ⟨e, hlink.edge_mem⟩ (x := x) (y := y) hlink).mpr hxy

/-- A flat contains every original edge whose endpoints its own edges
connect. This is an iff for mathlib's actual IsFlat predicate. -/
theorem cycleMatroid_isFlat_iff_reach_closed (X : Set β) :
    (cycleMatroid G).IsFlat X ↔ X ⊆ G.edgeSet ∧
      ∀ (e : G.edgeSet) (x y : G.vertexSet), G.IsLink e.1 x.1 y.1 →
        GraphReachable G X x y → e.1 ∈ X := by
  constructor
  · intro hX
    refine ⟨hX.subset_ground, ?_⟩
    intro e x y hlink hxy
    have hc := (cycleMatroid_mem_closure_iff G X hX.subset_ground e hlink).mpr hxy
    rwa [hX.closure] at hc
  · rintro ⟨hX, hclosed⟩
    apply Matroid.isFlat_iff_closure_eq.mpr
    apply Set.Subset.antisymm ?_ ((cycleMatroid G).subset_closure X hX)
    intro e hc
    rw [cycleMatroid_closure_eq G X hX] at hc
    obtain ⟨x, y, hlink, hxy⟩ := hc
    exact hclosed ⟨e, hlink.edge_mem⟩ x y hlink hxy

end BooleanAntichainsKernel
