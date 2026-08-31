import BooleanAntichainsKernel.MultigraphWalks

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {G : Graph α β} {F : Set β}

def graphLoopWalk (e : G.edgeSet) (he : e.1 ∈ F) (x : G.vertexSet)
    (h : G.IsLink e.1 x.1 x.1) : LabelledGraphWalk G F x x :=
  .cons e he h (.nil x)

theorem graphLoopWalk_isCycle (e : G.edgeSet) (he : e.1 ∈ F) (x : G.vertexSet)
    (h : G.IsLink e.1 x.1 x.1) : (graphLoopWalk e he x h).IsCycle := by
  simp [graphLoopWalk, LabelledGraphWalk.IsCycle, LabelledGraphWalk.edges, LabelledGraphWalk.support]

def graphParallelWalk (e f : G.edgeSet) (he : e.1 ∈ F) (hf : f.1 ∈ F)
    (x y : G.vertexSet) (hE : G.IsLink e.1 x.1 y.1) (hF : G.IsLink f.1 x.1 y.1) :
    LabelledGraphWalk G F x x :=
  .cons e he hE (.cons f hf hF.symm (.nil x))

theorem graphParallelWalk_isCycle (e f : G.edgeSet) (he : e.1 ∈ F) (hf : f.1 ∈ F)
    (x y : G.vertexSet) (hE : G.IsLink e.1 x.1 y.1) (hF : G.IsLink f.1 x.1 y.1)
    (hef : e ≠ f) (hxy : x ≠ y) : (graphParallelWalk e f he hf x y hE hF).IsCycle := by
  simp [graphParallelWalk, LabelledGraphWalk.IsCycle, LabelledGraphWalk.edges,
    LabelledGraphWalk.support, hef, Ne.symm hxy]

/-- A one-edge labelled cycle forbids every actual loop in a forest. -/
theorem GraphEdgeForest.no_loops (hF : GraphEdgeForest G F) {e : β} (he : e ∈ F)
    (x : α) : ¬G.IsLoopAt e x := by
  intro hx
  let ee : G.edgeSet := ⟨e, hx.edge_mem⟩
  let xx : G.vertexSet := ⟨x, hx.vertex_mem⟩
  have hl : G.IsLink ee.1 xx.1 xx.1 := hx
  exact hF.2 xx (graphLoopWalk ee he xx hl) (graphLoopWalk_isCycle ee he xx hl)

theorem GraphEdgeForest.link_ne (hF : GraphEdgeForest G F) {e : β} (he : e ∈ F)
    {x y : α} (h : G.IsLink e x y) : x ≠ y := by
  intro hxy
  subst y
  exact hF.no_loops he x h

/-- Two distinct original edges with the same endpoints form a two-edge
labelled cycle. Thus each endpoint class contributes at most one forest edge. -/
theorem GraphEdgeForest.unique_edge (hI : GraphEdgeForest G F)
    {e f : β} (he : e ∈ F) (hf : f ∈ F) {x y : α}
    (hE : G.IsLink e x y) (hF : G.IsLink f x y) : e = f := by
  by_contra hef
  let ee : G.edgeSet := ⟨e, hE.edge_mem⟩
  let ff : G.edgeSet := ⟨f, hF.edge_mem⟩
  let xx : G.vertexSet := ⟨x, hE.left_mem⟩
  let yy : G.vertexSet := ⟨y, hE.right_mem⟩
  have hEE : ee ≠ ff := fun h ↦ hef (congrArg Subtype.val h)
  have hXY : xx ≠ yy := fun h ↦ hI.link_ne he hE (congrArg Subtype.val h)
  exact hI.2 xx (graphParallelWalk ee ff he hf xx yy hE hF)
    (graphParallelWalk_isCycle ee ff he hf xx yy hE hF hEE hXY)

theorem GraphEdgeForest.ends_injOn (hF : GraphEdgeForest G F) :
    Set.InjOn (graphEdgeEnds G) {e : G.edgeSet | e.1 ∈ F} := by
  intro e he f hf h
  obtain ⟨x, y, hE, hF'⟩ := (graphEdgeEnds_eq_iff_same_link G e f).mp h
  exact Subtype.ext (hF.unique_edge he hf hE hF')

end BooleanAntichainsKernel
