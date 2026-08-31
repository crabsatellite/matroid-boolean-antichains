import BooleanAntichainsKernel.MultigraphSpanningForest
import BooleanAntichainsKernel.TuttePolynomial
import Mathlib.Data.Finset.Powerset

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- Actual unordered finite sets of original edge labels satisfying the
paper's componentwise spanning-tree condition. -/
abbrev GraphSpanningForests (G : Graph α β) :=
  {F : Finset β // GraphSpanningForest G (F : Set β)}

noncomputable instance (G : Graph α β) [Finite G.edgeSet] : Fintype (GraphSpanningForests G) := by
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  let U := G.edgeSet.toFinset
  let encode : GraphSpanningForests G → U.powerset := fun F ↦
    ⟨F.1, Finset.mem_powerset.mpr (fun e he ↦ Set.mem_toFinset.mpr (F.2.1 he))⟩
  exact Fintype.ofInjective encode (fun F H h ↦
    Subtype.ext (congrArg (fun S : U.powerset ↦ S.1) h))

/-- The map is the identity on the finite original edge set in both
directions; only the proved base/forest certificate changes. -/
noncomputable def cycleMatroidBasesEquivSpanningForests (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    MatroidBases (cycleMatroid G) ≃ GraphSpanningForests G where
  toFun B := ⟨B.1, (cycleMatroid_isBase_iff_spanningForest G (B.1 : Set β)).mp B.2⟩
  invFun F := ⟨F.1, (cycleMatroid_isBase_iff_spanningForest G (F.1 : Set β)).mpr F.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cycleMatroidBasesEquivSpanningForests_val (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] (B : MatroidBases (cycleMatroid G)) :
    (cycleMatroidBasesEquivSpanningForests G B).1 = B.1 := rfl

theorem cycleMatroidBasesEquivSpanningForests_symm_val (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] (F : GraphSpanningForests G) :
    ((cycleMatroidBasesEquivSpanningForests G).symm F).1 = F.1 := rfl

theorem cycleMatroid_spanningForest_count (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    Nat.card (MatroidBases (cycleMatroid G)) = Fintype.card (GraphSpanningForests G) := by
  calc
    _ = Nat.card (GraphSpanningForests G) := Nat.card_congr (cycleMatroidBasesEquivSpanningForests G)
    _ = _ := Nat.card_eq_fintype_card

theorem graphSpanningForest_card (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]
    (F : GraphSpanningForests G) : F.1.card = G.vertexSet.ncard - graphConnectedComponentCount G := by
  have hbase := (cycleMatroid_isBase_iff_spanningForest G (F.1 : Set β)).mpr F.2
  simpa only [Set.ncard_coe_finset] using cycleMatroid_base_card G hbase

end BooleanAntichainsKernel
