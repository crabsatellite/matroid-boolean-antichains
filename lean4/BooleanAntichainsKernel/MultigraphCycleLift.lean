import BooleanAntichainsKernel.MultigraphSupport
import BooleanAntichainsKernel.MultigraphWalks
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {G : Graph α β} {F : Set β}

noncomputable def graphSupportEdge {x y : G.vertexSet} (h : (graphSupport G F).Adj x y) :
    {e : G.edgeSet // e.1 ∈ F ∧ G.IsLink e.1 x.1 y.1} := by
  let hex := ((graphSupport_adj G F x y).mp h).2
  let e := hex.choose
  have he : e ∈ F ∧ G.IsLink e x.1 y.1 := hex.choose_spec
  exact ⟨⟨e, he.2.edge_mem⟩, he⟩

theorem graphSupportEdge_ends {x y : G.vertexSet} (h : (graphSupport G F).Adj x y) :
    graphEdgeEnds G (graphSupportEdge h).1 = s(x, y) :=
  graphEdgeEnds_eq _ (graphSupportEdge h).2.2

/-- Lift a support walk by actual edges in the selected original edge set. -/
noncomputable def graphSupportWalkLift {x y : G.vertexSet} :
    (graphSupport G F).Walk x y → LabelledGraphWalk G F x y
  | .nil => .nil x
  | .cons h p => .cons (graphSupportEdge h).1 (graphSupportEdge h).2.1
      (graphSupportEdge h).2.2 (graphSupportWalkLift p)

theorem graphSupportWalkLift_support {x y : G.vertexSet} (p : (graphSupport G F).Walk x y) :
    (graphSupportWalkLift p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [graphSupportWalkLift, LabelledGraphWalk.support_cons,
      SimpleGraph.Walk.support_cons, ih]

/-- Every projected edge is exactly the corresponding simple-walk edge. -/
theorem graphSupportWalkLift_edges {x y : G.vertexSet} (p : (graphSupport G F).Walk x y) :
    (graphSupportWalkLift p).edges.map (graphEdgeEnds G) = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [graphSupportWalkLift, LabelledGraphWalk.edges_cons,
      SimpleGraph.Walk.edges_cons, List.map_cons, graphSupportEdge_ends, ih]

theorem graphSupportWalkLift_isCycle {x : G.vertexSet} {p : (graphSupport G F).Walk x x}
    (hp : p.IsCycle) : (graphSupportWalkLift p).IsCycle := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.Nodup.of_map (graphEdgeEnds G)
    rw [graphSupportWalkLift_edges]
    exact hp.isTrail.edges_nodup
  · intro he
    have hz : p.edges = [] := by
      rw [← graphSupportWalkLift_edges p, he, List.map_nil]
    exact hp.not_nil (SimpleGraph.Walk.edges_eq_nil.mp hz)
  · rw [graphSupportWalkLift_support]
    exact hp.support_nodup

theorem GraphEdgeForest.support_isAcyclic (hF : GraphEdgeForest G F) :
    (graphSupport G F).IsAcyclic := by
  intro x p hp
  exact hF.2 x (graphSupportWalkLift p) (graphSupportWalkLift_isCycle hp)

end BooleanAntichainsKernel
