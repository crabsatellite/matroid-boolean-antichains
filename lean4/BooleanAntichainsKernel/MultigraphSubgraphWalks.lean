import BooleanAntichainsKernel.MultigraphWalkLabels
import BooleanAntichainsKernel.MultigraphReachability
import Mathlib.Combinatorics.Graph.Delete

namespace BooleanAntichainsKernel

variable {α β : Type*} {G H : Graph α β} {F : Set β}

def subgraphVertexMap (hHG : H ≤ G) (x : H.vertexSet) : G.vertexSet :=
  ⟨x.1, hHG.vertexSet_mono x.2⟩

def subgraphEdgeMap (hHG : H ≤ G) (e : H.edgeSet) : G.edgeSet :=
  ⟨e.1, hHG.edgeSet_mono e.2⟩

/-- Inclusion of a genuine subgraph changes only membership proofs;
every original vertex and edge label is preserved. -/
def LabelledGraphWalk.mapSubgraph (hHG : H ≤ G) {x y : H.vertexSet} :
    LabelledGraphWalk H F x y →
      LabelledGraphWalk G F (subgraphVertexMap hHG x) (subgraphVertexMap hHG y)
  | .nil x => .nil (subgraphVertexMap hHG x)
  | @LabelledGraphWalk.cons _ _ _ _ x y z e he h p =>
    .cons (y := subgraphVertexMap hHG y) (subgraphEdgeMap hHG e) he
      (hHG.isLink_mono h) (p.mapSubgraph hHG)

theorem LabelledGraphWalk.mapSubgraph_edgeLabels (hHG : H ≤ G) {x y : H.vertexSet}
    (p : LabelledGraphWalk H F x y) : (p.mapSubgraph hHG).edgeLabels = p.edgeLabels := by
  induction p with
  | nil => rfl
  | cons e he h p ih => simp only [LabelledGraphWalk.mapSubgraph,
      LabelledGraphWalk.edgeLabels_cons, subgraphEdgeMap, ih]

theorem LabelledGraphWalk.mapSubgraph_vertexLabels (hHG : H ≤ G) {x y : H.vertexSet}
    (p : LabelledGraphWalk H F x y) : (p.mapSubgraph hHG).vertexLabels = p.vertexLabels := by
  induction p with
  | nil => rfl
  | @cons x y z e he h p ih =>
    change x.1 :: (p.mapSubgraph hHG).vertexLabels = x.1 :: p.vertexLabels
    exact congrArg (List.cons x.1) ih

theorem LabelledGraphWalk.mapSubgraph_isCycle (hHG : H ≤ G) {x : H.vertexSet}
    (p : LabelledGraphWalk H F x x) : (p.mapSubgraph hHG).IsCycle ↔ p.IsCycle := by
  rw [(p.mapSubgraph hHG).isCycle_iff_originalLabels, p.isCycle_iff_originalLabels,
    p.mapSubgraph_edgeLabels hHG, p.mapSubgraph_vertexLabels hHG]

theorem graphReachable_map_subgraph (hHG : H ≤ G) {x y : H.vertexSet}
    (h : GraphReachable H F x y) :
    GraphReachable G F (subgraphVertexMap hHG x) (subgraphVertexMap hHG y) := by
  obtain ⟨p⟩ := h
  exact ⟨p.mapSubgraph hHG⟩

theorem graphEdgeForest_of_subgraph (hHG : H ≤ G) (hF : GraphEdgeForest G F)
    (hFH : F ⊆ H.edgeSet) : GraphEdgeForest H F := by
  refine ⟨hFH, ?_⟩
  intro x p hp
  exact hF.2 (subgraphVertexMap hHG x) (p.mapSubgraph hHG) ((p.mapSubgraph_isCycle hHG).mpr hp)

end BooleanAntichainsKernel
