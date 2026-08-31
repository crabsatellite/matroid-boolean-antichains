import BooleanAntichainsKernel.SimpleGraphComponentPartition
import BooleanAntichainsKernel.MultigraphReachability

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {V : Type*} [Fintype V]

theorem simpleForest_component_tree_count (H : SimpleGraph V) (hH : H.IsAcyclic)
    (c : H.ConnectedComponent) : Fintype.card c.toSimpleGraph.edgeSet + 1 = Fintype.card c := by
  simpa only [SimpleGraph.edgeFinset_card] using (hH.isTree_connectedComponent c).card_edgeFinset

/-- Sum the proved tree identity over the disjoint actual components.
Isolated vertices contribute one component and zero edges. -/
theorem simpleForest_component_count (H : SimpleGraph V) (hH : H.IsAcyclic) :
    Fintype.card H.edgeSet + Fintype.card H.ConnectedComponent = Fintype.card V := by
  calc
    _ = (∑ c : H.ConnectedComponent, Fintype.card c.toSimpleGraph.edgeSet) +
        (∑ _c : H.ConnectedComponent, 1) := by
      rw [simpleGraph_edge_count_components]
      simp
    _ = ∑ c : H.ConnectedComponent, (Fintype.card c.toSimpleGraph.edgeSet + 1) :=
      Finset.sum_add_distrib.symm
    _ = ∑ c : H.ConnectedComponent, Fintype.card c :=
      Finset.sum_congr rfl (fun c _ ↦ simpleForest_component_tree_count H hH c)
    _ = _ := (simpleGraph_vertex_count_components H).symm

omit [Fintype V] in
theorem simpleForest_component_count_nat [Finite V] (H : SimpleGraph V) (hH : H.IsAcyclic) :
    Nat.card H.edgeSet + Nat.card H.ConnectedComponent = Nat.card V := by
  letI : Fintype V := Fintype.ofFinite V
  simpa only [Nat.card_eq_fintype_card] using simpleForest_component_count H hH

variable {α β : Type*} {G : Graph α β} {F : Set β}

/-- The original labelled forest edge count and original walk-component
count, transported through both exact carrier bijections. -/
theorem graphForest_component_count [Finite G.vertexSet] (hF : GraphEdgeForest G F) :
    F.ncard + graphComponentCount G F = G.vertexSet.ncard := by
  rw [forest_edge_ncard hF, graphComponentCount_eq_support]
  exact simpleForest_component_count_nat (graphSupport G F) hF.support_isAcyclic

theorem graphForest_size_eq [Finite G.vertexSet] (hF : GraphEdgeForest G F) :
    F.ncard = G.vertexSet.ncard - graphComponentCount G F :=
  Nat.eq_sub_of_add_eq (graphForest_component_count hF)

theorem graphForest_size_le [Finite G.vertexSet] (hF : GraphEdgeForest G F) :
    F.ncard ≤ G.vertexSet.ncard := by
  have h := graphForest_component_count hF
  omega

end BooleanAntichainsKernel
