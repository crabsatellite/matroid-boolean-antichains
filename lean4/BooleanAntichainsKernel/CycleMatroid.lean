import BooleanAntichainsKernel.MultigraphForestInsert
import BooleanAntichainsKernel.MatroidRank
import Mathlib.Combinatorics.Matroid.IndepAxioms

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- The cycle matroid on the graph's original edge labels and original
edge ground set. Independence is the literal absence of labelled cycles;
all finite matroid axioms are supplied by proved forest producers. -/
noncomputable def cycleMatroid (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet] : Matroid β :=
  (IndepMatroid.ofFinite (Set.toFinite G.edgeSet) (GraphEdgeForest G)
    (graphEdgeForest_empty G)
    (fun {_I _J} hJ hIJ ↦ hJ.mono hIJ)
    (fun {_I _J} hI hJ hcard ↦ graphEdgeForest_augment hI hJ hcard)
    (fun {_I} hI ↦ hI.1)).matroid

variable (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

@[simp] theorem cycleMatroid_ground : (cycleMatroid G).E = G.edgeSet := rfl

@[simp] theorem cycleMatroid_indep_iff (I : Set β) :
    (cycleMatroid G).Indep I ↔ GraphEdgeForest G I := Iff.rfl

instance cycleMatroid_finite : (cycleMatroid G).Finite := ⟨Set.toFinite G.edgeSet⟩

theorem cycleMatroid_isBase_iff_maximalForest (B : Set β) :
    (cycleMatroid G).IsBase B ↔ Maximal (GraphEdgeForest G) B := by
  rw [Matroid.isBase_iff_maximal_indep]
  rfl

theorem cycleMatroid_indep_finite {I : Set β} (hI : (cycleMatroid G).Indep I) : I.Finite :=
  ((cycleMatroid_indep_iff G I).mp hI).finite

theorem cycleMatroid_indep_card_le {I : Set β} (hI : (cycleMatroid G).Indep I) :
    I.ncard ≤ G.vertexSet.ncard := graphForest_size_le ((cycleMatroid_indep_iff G I).mp hI)

end BooleanAntichainsKernel
