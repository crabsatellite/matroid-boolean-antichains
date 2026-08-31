import BooleanAntichainsKernel.MultigraphForestEdges

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- Reachability is defined by the original edge-labelled walks. -/
def GraphReachable (G : Graph α β) (F : Set β) (x y : G.vertexSet) : Prop :=
  Nonempty (LabelledGraphWalk G F x y)

theorem LabelledGraphWalk.support_reachable {G : Graph α β} {F : Set β}
    {x y : G.vertexSet} (p : LabelledGraphWalk G F x y) : (graphSupport G F).Reachable x y := by
  induction p with
  | nil x => exact SimpleGraph.Reachable.refl x
  | @cons x y z e he h p ih =>
    by_cases hxy : x = y
    · subst y
      exact ih
    · have ha := (graphSupport_adj G F x y).mpr ⟨hxy, e.1, he, h⟩
      exact ha.reachable.trans ih

/-- Loop steps may be stationary, but they do not change reachable pairs.
No absence-of-loops premise is used in this transport. -/
theorem graphReachable_iff_support (G : Graph α β) (F : Set β) (x y : G.vertexSet) :
    GraphReachable G F x y ↔ (graphSupport G F).Reachable x y := by
  constructor
  · rintro ⟨p⟩
    exact p.support_reachable
  · rintro ⟨p⟩
    exact ⟨graphSupportWalkLift p⟩

theorem graphReachable_equivalence (G : Graph α β) (F : Set β) :
    Equivalence (GraphReachable G F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨LabelledGraphWalk.nil x⟩
  · intro x y h
    exact (graphReachable_iff_support G F y x).mpr ((graphReachable_iff_support G F x y).mp h).symm
  · intro x y z hxy hyz
    obtain ⟨p⟩ := hxy
    obtain ⟨q⟩ := hyz
    exact ⟨p.append q⟩

theorem graphReachable_mono (G : Graph α β) {F H : Set β} (hFH : F ⊆ H)
    {x y : G.vertexSet} (h : GraphReachable G F x y) : GraphReachable G H x y := by
  obtain ⟨p⟩ := h
  exact ⟨p.mono hFH⟩

/-- Components are classes under original labelled-walk reachability. -/
def GraphWalkComponent (G : Graph α β) (F : Set β) := Quot (GraphReachable G F)

def graphWalkComponentMk (G : Graph α β) (F : Set β) (x : G.vertexSet) : GraphWalkComponent G F :=
  Quot.mk (GraphReachable G F) x

noncomputable def graphWalkComponentEquivSupport (G : Graph α β) (F : Set β) :
    GraphWalkComponent G F ≃ (graphSupport G F).ConnectedComponent :=
  Quot.congrRight (graphReachable_iff_support G F)

theorem graphWalkComponentEquivSupport_mk (G : Graph α β) (F : Set β) (x : G.vertexSet) :
    graphWalkComponentEquivSupport G F (graphWalkComponentMk G F x) =
      (graphSupport G F).connectedComponentMk x := rfl

instance (G : Graph α β) (F : Set β) [Finite G.vertexSet] : Finite (GraphWalkComponent G F) :=
  Quot.finite _

noncomputable def graphComponentCount (G : Graph α β) (F : Set β) : ℕ :=
  Nat.card (GraphWalkComponent G F)

theorem graphComponentCount_eq_support (G : Graph α β) (F : Set β) :
    graphComponentCount G F = Nat.card (graphSupport G F).ConnectedComponent :=
  Nat.card_congr (graphWalkComponentEquivSupport G F)

/-- The paper's c(G), retaining isolated vertices and all original edges. -/
noncomputable def graphConnectedComponentCount (G : Graph α β) : ℕ :=
  graphComponentCount G G.edgeSet

theorem graphConnectedComponentCount_eq_simplification (G : Graph α β) :
    graphConnectedComponentCount G = Nat.card (graphSimplification G).ConnectedComponent :=
  graphComponentCount_eq_support G G.edgeSet

end BooleanAntichainsKernel
