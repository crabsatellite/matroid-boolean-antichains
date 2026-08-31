import BooleanAntichainsKernel.MultigraphCycleLift
import BooleanAntichainsKernel.MultigraphShortCycles

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {G : Graph α β} {F : Set β}

theorem graphSupportAdj_of_link
    (hNL : ∀ e ∈ F, ∀ x : α, ¬G.IsLoopAt e x)
    (e : G.edgeSet) (he : e.1 ∈ F) {x y : G.vertexSet} (h : G.IsLink e.1 x.1 y.1) :
    (graphSupport G F).Adj x y := by
  apply (graphSupport_adj G F x y).mpr
  refine ⟨?_, e.1, he, h⟩
  intro hxy
  subst y
  exact hNL e.1 he x.1 h

/-- Project the original labelled walk, using the proved absence of loops
to obtain each genuine simple-graph adjacency. -/
noncomputable def graphWalkToSupport
    (hNL : ∀ e ∈ F, ∀ x : α, ¬G.IsLoopAt e x) {x y : G.vertexSet} :
    LabelledGraphWalk G F x y → (graphSupport G F).Walk x y
  | .nil _ => .nil
  | .cons e he h p => .cons (graphSupportAdj_of_link hNL e he h) (graphWalkToSupport hNL p)

theorem graphWalkToSupport_support
    (hNL : ∀ e ∈ F, ∀ x : α, ¬G.IsLoopAt e x) {x y : G.vertexSet}
    (p : LabelledGraphWalk G F x y) : (graphWalkToSupport hNL p).support = p.support := by
  induction p with
  | nil => rfl
  | cons e he h p ih => simp only [graphWalkToSupport, LabelledGraphWalk.support_cons,
      SimpleGraph.Walk.support_cons, ih]

theorem graphWalkToSupport_edges
    (hNL : ∀ e ∈ F, ∀ x : α, ¬G.IsLoopAt e x) {x y : G.vertexSet}
    (p : LabelledGraphWalk G F x y) :
    (graphWalkToSupport hNL p).edges = p.edges.map (graphEdgeEnds G) := by
  induction p with
  | nil => rfl
  | cons e he h p ih => simp only [graphWalkToSupport, LabelledGraphWalk.edges_cons,
      SimpleGraph.Walk.edges_cons, List.map_cons, graphEdgeEnds_eq e h, ih]

/-- Injectivity on actual edge labels, not merely an equal cardinality,
preserves the trail condition under projection of a labelled cycle. -/
theorem graphWalkToSupport_isCycle
    (hNL : ∀ e ∈ F, ∀ x : α, ¬G.IsLoopAt e x)
    (hInj : Set.InjOn (graphEdgeEnds G) {e : G.edgeSet | e.1 ∈ F})
    {x : G.vertexSet} (p : LabelledGraphWalk G F x x) (hp : p.IsCycle) :
    (graphWalkToSupport hNL p).IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [graphWalkToSupport_edges]
    exact List.Nodup.map_on (fun e he f hf h ↦ hInj (p.edges_mem e he) (p.edges_mem f hf) h) hp.1
  · intro h
    have he := congrArg SimpleGraph.Walk.edges h
    rw [graphWalkToSupport_edges, SimpleGraph.Walk.edges_nil] at he
    exact hp.2.1 (List.map_eq_nil_iff.mp he)
  · rw [graphWalkToSupport_support]
    exact hp.2.2

/-- Exact transport of the literal no-labelled-cycle forest predicate.
Loops, parallel-edge repetitions, edge identity and isolated vertices all
remain explicit; this equivalence precedes use of simple-graph forest API. -/
theorem graphEdgeForest_iff_support :
    GraphEdgeForest G F ↔ F ⊆ G.edgeSet ∧
      (∀ e ∈ F, ∀ x : α, ¬G.IsLoopAt e x) ∧
      Set.InjOn (graphEdgeEnds G) {e : G.edgeSet | e.1 ∈ F} ∧
      (graphSupport G F).IsAcyclic := by
  constructor
  · intro hF
    exact ⟨hF.1, fun _ he x ↦ hF.no_loops he x, hF.ends_injOn, hF.support_isAcyclic⟩
  · rintro ⟨hground, hNL, hInj, hacyc⟩
    refine ⟨hground, ?_⟩
    intro x p hp
    exact hacyc (graphWalkToSupport hNL p) (graphWalkToSupport_isCycle hNL hInj p hp)

end BooleanAntichainsKernel
