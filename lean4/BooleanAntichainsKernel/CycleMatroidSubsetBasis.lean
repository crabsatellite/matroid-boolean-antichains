import BooleanAntichainsKernel.CycleMatroidComponents

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

/-- An actual matroid basis of X is an original labelled forest with
exactly the same reachable pairs as X, including isolated vertices. -/
theorem cycleMatroid_isBasis_reachability {I X : Set β} (hI : (cycleMatroid G).IsBasis I X) :
    GraphEdgeForest G I ∧ I ⊆ X ∧ ∀ x y : G.vertexSet,
      GraphReachable G I x y ↔ GraphReachable G X x y := by
  have hforest := (cycleMatroid_indep_iff G I).mp hI.indep
  have hEdges : ∀ e ∈ X, ∀ x y : G.vertexSet, G.IsLink e x.1 y.1 → GraphReachable G I x y := by
    intro e he x y hlink
    by_contra hn
    have heG : e ∈ G.edgeSet := hI.subset_ground he
    have hins := graphEdgeForest_insert hforest ⟨e, heG⟩ (x := x) (y := y) hlink hn
    have heq := hI.eq_of_subset_indep ((cycleMatroid_indep_iff G _).mpr hins)
      (Set.subset_insert e I) (Set.insert_subset he hI.subset)
    have heI : e ∈ I := heq.symm ▸ Set.mem_insert e I
    exact hn ⟨LabelledGraphWalk.cons ⟨e, heG⟩ heI hlink (.nil y)⟩
  refine ⟨hforest, hI.subset, ?_⟩
  intro x y
  exact ⟨graphReachable_mono G hI.subset, graphReachable_le_of_edges hEdges x y⟩

theorem cycleMatroid_isBasis_component_count {I X : Set β} (hI : (cycleMatroid G).IsBasis I X) :
    graphComponentCount G I = graphComponentCount G X := by
  change Nat.card (Quot (GraphReachable G I)) = Nat.card (Quot (GraphReachable G X))
  exact Nat.card_congr (Quot.congrRight (cycleMatroid_isBasis_reachability G hI).2.2)

/-- The same actual-basis argument gives the rank of every edge subset,
with the ambient original vertices retained when counting components. -/
theorem cycleMatroid_rank_set_add_components (X : Set β) (hX : X ⊆ G.edgeSet) :
    matroidRank (cycleMatroid G) X + graphComponentCount G X = G.vertexSet.ncard := by
  obtain ⟨I, hI⟩ := (cycleMatroid G).exists_isBasis X hX
  have hforest := (cycleMatroid_isBasis_reachability G hI).1
  have hr : matroidRank (cycleMatroid G) X = I.ncard := by
    change ((cycleMatroid G).eRk X).toNat = I.ncard
    rw [hI.eRk_eq_encard]
    rfl
  have hcount := graphForest_component_count hforest
  rw [cycleMatroid_isBasis_component_count G hI] at hcount
  rw [hr]
  exact hcount

theorem cycleMatroid_rank_set (X : Set β) (hX : X ⊆ G.edgeSet) :
    matroidRank (cycleMatroid G) X = G.vertexSet.ncard - graphComponentCount G X :=
  Nat.eq_sub_of_add_eq (cycleMatroid_rank_set_add_components G X hX)

end BooleanAntichainsKernel
