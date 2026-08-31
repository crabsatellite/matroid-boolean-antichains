import BooleanAntichainsKernel.BooleanTightFree

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α : Type*} [Fintype α]

/-- The literal rank-tight condition in the subset lattice: the common meet
has cardinality n-k. The carrier already consists of size-k Boolean antichains. -/
abbrev BooleanLatticeRankTightAntichain (α : Type*) [Fintype α] (k : ℕ) :=
  {C : BooleanAntichain k (Finset α) // (C.1.inf id).card = Fintype.card α - k}

noncomputable instance (k : ℕ) : Fintype (BooleanLatticeRankTightAntichain α k) :=
  Subtype.fintype _

lemma mapFamily_inf {L K : Type*} [Lattice L] [OrderTop L] [Lattice K] [OrderTop K]
    [DecidableEq L] [DecidableEq K] (e : L ≃o K) (C : Finset L) :
    (mapFamily e C).inf id = e (C.inf id) := by
  unfold mapFamily
  rw [Equiv.finsetCongr_apply, Finset.inf_map]
  exact (map_finset_inf e C id).symm

/-- Transport the actual common meet, not just the cardinality of the family. -/
theorem freeOn_antichainBottom_card (k : ℕ)
    (C : BooleanAntichain k (MatroidFlat (Matroid.freeOn (Set.univ : Set α)))) :
    ((booleanAntichainOrderIsoEquiv freeOnUnivFlatOrderIsoFinset k C).1.inf id).card =
      MatroidFlat.rank (C.1.inf id) := by
  rw [booleanAntichainOrderIsoEquiv_val, mapFamily_inf]
  change (C.1.inf id).1.toFinset.card = MatroidFlat.rank (C.1.inf id)
  rw [freeOn_flat_rank, Set.ncard_eq_toFinset_card']

noncomputable def freeOnRankTightEquivBoolean (k : ℕ) :
    RankTightAntichain (Matroid.freeOn (Set.univ : Set α)) k ≃
      BooleanLatticeRankTightAntichain α k :=
  (booleanAntichainOrderIsoEquiv freeOnUnivFlatOrderIsoFinset k).subtypeEquiv (fun C ↦ by
    change IsRankTight C ↔
      ((booleanAntichainOrderIsoEquiv freeOnUnivFlatOrderIsoFinset k C).1.inf id).card =
        Fintype.card α - k
    rw [freeOn_antichainBottom_card]
    unfold IsRankTight
    rw [freeOn_top_rank]
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card])

/-- Equation eq:boolean-tight on the actual subset-lattice carrier, proved
through free-matroid contractions and the corank complement bijection. -/
theorem booleanLattice_rankTight_count (k : ℕ) :
    Fintype.card (BooleanLatticeRankTightAntichain α k) = (Fintype.card α).choose k := by
  rw [← Fintype.card_congr (freeOnRankTightEquivBoolean k), freeOn_rankTight_count]

end BooleanAntichainsKernel
