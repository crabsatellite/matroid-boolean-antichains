import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum

namespace BooleanAntichainsKernel

open scoped Classical

variable {V : Type*}

/-- Actual vertices partitioned by their actual connected-component class. -/
def simpleGraphVertexComponentsEquiv (H : SimpleGraph V) :
    (Σ c : H.ConnectedComponent, c) ≃ V := Equiv.sigmaFiberEquiv H.connectedComponentMk

def simpleComponentEdgeMap (H : SimpleGraph V)
    (a : Σ c : H.ConnectedComponent, c.toSimpleGraph.edgeSet) : H.edgeSet :=
  a.1.toSimpleGraph_hom.mapEdgeSet a.2

theorem simpleComponentEdgeMap_val (H : SimpleGraph V) (c : H.ConnectedComponent)
    (e : c.toSimpleGraph.edgeSet) :
    (simpleComponentEdgeMap H ⟨c, e⟩).1 = e.1.map (fun x : c ↦ (x : V)) := rfl

/-- An original edge cannot belong to two components: any one of its
actual endpoints is a common vertex of those components. -/
theorem simpleComponentEdgeMap_component_unique (H : SimpleGraph V)
    {c d : H.ConnectedComponent} (e : c.toSimpleGraph.edgeSet) (f : d.toSimpleGraph.edgeSet)
    (h : simpleComponentEdgeMap H ⟨c, e⟩ = simpleComponentEdgeMap H ⟨d, f⟩) : c = d := by
  have hex : ∃ x : c, x ∈ e.1 := Sym2.ind (fun x _y ↦ ⟨x, by simp⟩) e.1
  obtain ⟨x, hx⟩ := hex
  have hedges : e.1.map (fun x : c ↦ (x : V)) = f.1.map (fun y : d ↦ (y : V)) :=
    congrArg (fun q : H.edgeSet ↦ q.1) h
  have hxm : (x : V) ∈ f.1.map (fun y : d ↦ (y : V)) :=
    hedges ▸ Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, _hy, hyx⟩ := Sym2.mem_map.mp hxm
  have hyx' : (y : V) = (x : V) := hyx
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex x.2 (hyx' ▸ y.2)

theorem simpleComponentEdgeMap_injective (H : SimpleGraph V) :
    Function.Injective (simpleComponentEdgeMap H) := by
  rintro ⟨c, e⟩ ⟨d, f⟩ h
  have hcd := simpleComponentEdgeMap_component_unique H e f h
  subst d
  have hef : e = f := SimpleGraph.Hom.mapEdgeSet.injective c.toSimpleGraph_hom
    Subtype.val_injective h
  subst f
  rfl

theorem simpleComponentEdgeMap_surjective (H : SimpleGraph V) :
    Function.Surjective (simpleComponentEdgeMap H) := by
  rintro ⟨e, he⟩
  revert he
  refine Sym2.ind (fun u v he ↦ ?_) e
  have huv : H.Adj u v := he
  let c := H.connectedComponentMk u
  let uu : c := ⟨u, rfl⟩
  let vv : c := ⟨v, SimpleGraph.ConnectedComponent.sound huv.reachable.symm⟩
  let ee : c.toSimpleGraph.edgeSet := ⟨s(uu, vv), huv⟩
  exact ⟨⟨c, ee⟩, rfl⟩

/-- The disjoint component decomposition of actual unordered endpoint
edges, with no count presumed for any component. -/
noncomputable def simpleGraphEdgeComponentsEquiv (H : SimpleGraph V) :
    (Σ c : H.ConnectedComponent, c.toSimpleGraph.edgeSet) ≃ H.edgeSet :=
  Equiv.ofBijective (simpleComponentEdgeMap H)
    ⟨simpleComponentEdgeMap_injective H, simpleComponentEdgeMap_surjective H⟩

variable [Fintype V]

theorem simpleGraph_vertex_count_components (H : SimpleGraph V) :
    Fintype.card V = ∑ c : H.ConnectedComponent, Fintype.card c := by
  rw [← Fintype.card_congr (simpleGraphVertexComponentsEquiv H), Fintype.card_sigma]

theorem simpleGraph_edge_count_components (H : SimpleGraph V) :
    Fintype.card H.edgeSet = ∑ c : H.ConnectedComponent, Fintype.card c.toSimpleGraph.edgeSet := by
  rw [← Fintype.card_congr (simpleGraphEdgeComponentsEquiv H), Fintype.card_sigma]

end BooleanAntichainsKernel
