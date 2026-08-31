import BooleanAntichainsKernel.GraphicSimpleForests
import BooleanAntichainsKernel.MultigraphSpanningTrees

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β)

theorem graphIsConnected_component_eq (hG : GraphIsConnected G)
    (c d : GraphWalkComponent G G.edgeSet) : c = d :=
  Quot.inductionOn c (fun x ↦ Quot.inductionOn d (fun y ↦ Quot.sound (hG.2 x y)))

theorem graphIsConnected_component_count (hG : GraphIsConnected G) :
    graphConnectedComponentCount G = 1 := by
  letI : Subsingleton (GraphWalkComponent G G.edgeSet) := ⟨graphIsConnected_component_eq G hG⟩
  letI : Nonempty (GraphWalkComponent G G.edgeSet) :=
    hG.1.map (graphWalkComponentMk G G.edgeSet)
  exact Nat.card_unique

variable [Finite G.vertexSet] [Finite G.edgeSet]

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

/-- The connected simple-graph clause on native original-edge spanning
trees. The final map from forests to trees is the identity on edge sets. -/
noncomputable def graphicConnectedMaximumAntichainEquivTrees
    (hs : GraphIsSimple G) (hc : GraphIsConnected G) :
    BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G)) ≃ GraphSpanningTrees G :=
  (graphicSimpleMaximumAntichainEquivForests G hs).trans (graphSpanningForestsEquivTrees G hc)

theorem graphicConnectedMaximumAntichain_count (hs : GraphIsSimple G) (hc : GraphIsConnected G) :
    Fintype.card (BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) = Fintype.card (GraphSpanningTrees G) :=
  Fintype.card_congr (graphicConnectedMaximumAntichainEquivTrees G hs hc)

theorem graphicConnectedMaximumAntichain_card (hc : GraphIsConnected G)
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) : C.1.card = G.vertexSet.ncard - 1 := by
  rw [graphMaximumAntichain_card G C, graphIsConnected_component_count G hc]

end BooleanAntichainsKernel
