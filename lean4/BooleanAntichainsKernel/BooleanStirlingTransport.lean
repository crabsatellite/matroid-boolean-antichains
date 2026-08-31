import BooleanAntichainsKernel.BooleanStirling

namespace BooleanAntichainsKernel

open scoped Classical

/-- An arbitrary actual finite ground set is transported by a full subset
lattice order isomorphism. This also keeps the decidable-equality instances
in the total count coherent with those in the rank-tight subtypes. -/
theorem booleanLattice_count_stirling_general {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card (BooleanAntichain k (Finset α)) =
      Nat.stirlingSecond (Fintype.card α + 1) (k + 1) := by
  calc
    _ = Fintype.card (BooleanAntichain k (Finset (Fin (Fintype.card α)))) :=
      Fintype.card_congr
        (booleanAntichainOrderIsoEquiv (finsetGroundOrderIso (Fintype.equivFin α)) k)
    _ = _ := booleanLattice_count_stirling (Fintype.card α) k

end BooleanAntichainsKernel
