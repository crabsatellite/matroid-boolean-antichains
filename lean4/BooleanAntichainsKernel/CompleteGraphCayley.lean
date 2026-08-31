import BooleanAntichainsKernel.CompleteTreeCarriers
import BooleanAntichainsKernel.CayleyFormula

namespace BooleanAntichainsKernel

open scoped Classical

/-- Cayley's count on the manuscript's original-edge spanning-tree
carrier. The licensed full rooted-forest proof is locally replayed in
CayleyFormula; both carrier transports here are proved equivalences. -/
theorem completeGraph_spanningTree_count {α : Type*} [Fintype α] [Nonempty α] :
    Fintype.card (GraphSpanningTrees (completeLabelledGraph α)) =
      (Fintype.card α) ^ (Fintype.card α - 2) := by
  calc
    _ = Nat.card {G : SimpleGraph α // G.IsTree} := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr (completeTreeEquivSimpleTree (α := α))
    _ = Nat.card {G : SimpleGraph (Fin (Fintype.card α)) // G.IsTree} :=
      Nat.card_congr (simpleTreeRelabelEquiv (Fintype.equivFin α))
    _ = _ := by
      rw [Nat.card_eq_fintype_card]
      exact Brockian.Cayley.cayley_formula (Fintype.card α)
        (show 1 ≤ Fintype.card α from Fintype.card_pos)

theorem completeFin_spanningTree_count (n : ℕ) (hn : 0 < n) :
    Fintype.card (GraphSpanningTrees (completeLabelledGraph (Fin n))) = n ^ (n - 2) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin] using completeGraph_spanningTree_count (α := Fin n)

end BooleanAntichainsKernel
