import BooleanAntichainsKernel.MultigraphForestInsert

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {G : Graph α β} {I : Set β} {e : β}

theorem graphReachable_of_same_link {x y u v : G.vertexSet}
    (hlink : G.IsLink e x.1 y.1) (hxy : GraphReachable G I x y)
    (huv : G.IsLink e u.1 v.1) : GraphReachable G I u v := by
  rcases hlink.eq_and_eq_or_eq_and_eq huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
  · have hxu' : x = u := Subtype.ext hxu
    have hyv' : y = v := Subtype.ext hyv
    simpa only [hxu', hyv'] using hxy
  · have hxv' : x = v := Subtype.ext hxv
    have hyu' : y = u := Subtype.ext hyu
    have hyx := (graphReachable_equivalence G I).symm hxy
    simpa only [hxv', hyu'] using hyx

/-- Inserting an edge whose endpoints are already reachable does not
change any original labelled-walk connected component. -/
theorem graphReachable_insert_iff {x y : G.vertexSet} (hlink : G.IsLink e x.1 y.1)
    (hxy : GraphReachable G I x y) (u v : G.vertexSet) :
    GraphReachable G (insert e I) u v ↔ GraphReachable G I u v := by
  constructor
  · intro h
    apply graphReachable_le_of_edges ?_ u v h
    intro f hf a b hfl
    rcases hf with rfl | hf
    · exact graphReachable_of_same_link hlink hxy hfl
    · exact ⟨LabelledGraphWalk.cons ⟨f, hfl.edge_mem⟩ hf hfl (.nil b)⟩
  · exact graphReachable_mono G (Set.subset_insert e I)

theorem graphComponentCount_insert_of_reachable {x y : G.vertexSet}
    (hlink : G.IsLink e x.1 y.1) (hxy : GraphReachable G I x y) :
    graphComponentCount G (insert e I) = graphComponentCount G I := by
  change Nat.card (Quot (GraphReachable G (insert e I))) = Nat.card (Quot (GraphReachable G I))
  exact Nat.card_congr (Quot.congrRight (graphReachable_insert_iff hlink hxy))

/-- A new forest edge must connect distinct old components. Otherwise
the proved forest edge/component equations differ by exactly one edge. -/
theorem graphEdgeForest_insert_not_connected [Finite G.vertexSet]
    (hIns : GraphEdgeForest G (insert e I)) (heI : e ∉ I) {x y : G.vertexSet}
    (hlink : G.IsLink e x.1 y.1) : ¬GraphReachable G I x y := by
  intro hxy
  have hI := hIns.mono (Set.subset_insert e I)
  have hiCount := graphForest_component_count hI
  have hInsCount := graphForest_component_count hIns
  rw [Set.ncard_insert_of_notMem heI hI.finite,
    graphComponentCount_insert_of_reachable hlink hxy] at hInsCount
  omega

theorem graphEdgeForest_insert_iff [Finite G.vertexSet] (hI : GraphEdgeForest G I)
    (e : G.edgeSet) {x y : G.vertexSet} (hlink : G.IsLink e.1 x.1 y.1) :
    GraphEdgeForest G (insert e.1 I) ↔ e.1 ∈ I ∨ ¬GraphReachable G I x y := by
  constructor
  · intro h
    by_cases he : e.1 ∈ I
    · exact Or.inl he
    · exact Or.inr (graphEdgeForest_insert_not_connected h he hlink)
  · rintro (he | hn)
    · simpa only [Set.insert_eq_of_mem he] using hI
    · exact graphEdgeForest_insert hI e hlink hn

end BooleanAntichainsKernel
