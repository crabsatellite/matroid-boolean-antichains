import BooleanAntichainsKernel.UniformNumeric34Pairs
import BooleanAntichainsKernel.UniformNumeric34Top
import BooleanAntichainsKernel.UniformNumeric45Pairs
import BooleanAntichainsKernel.UniformNumeric45Triples
import BooleanAntichainsKernel.UniformNumeric45Top
import BooleanAntichainsKernel.HeightGapEndpoints
import Mathlib.Data.List.OfFn

namespace BooleanAntichainsKernel

/-- The displayed U(3,4) distribution, on actual Boolean-antichain counts. -/
theorem uniform34_distribution :
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3)))) =
      [1, 11, 27, 4] := by
  have h2 := (uniform_count_eq_bounded 4 3 2 (by decide) (by decide)).trans uniform34_pairs_value
  have h3 := (uniform_count_eq_bounded 4 3 3 (by decide) (by decide)).trans uniform34_top_value
  change
    [Fintype.card (BooleanAntichain 0 (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3))),
     Fintype.card (BooleanAntichain 1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3))),
     Fintype.card (BooleanAntichain 2 (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3))),
     Fintype.card (BooleanAntichain 3 (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3)))] =
      [1, 11, 27, 4]
  rw [booleanAntichain_count_zero, uniform_singleton_count 4 3 (by decide), h2, h3]
  decide

/-- The displayed U(4,5) distribution, with every entry kernel-derived. -/
theorem uniform45_distribution :
    List.ofFn (fun k : Fin 5 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4)))) =
      [1, 26, 150, 50, 5] := by
  have h2 := (uniform_count_eq_bounded 5 4 2 (by decide) (by decide)).trans uniform45_pairs_value
  have h3 := (uniform_count_eq_bounded 5 4 3 (by decide) (by decide)).trans uniform45_triples_value
  have h4 := (uniform_count_eq_bounded 5 4 4 (by decide) (by decide)).trans uniform45_top_value
  change
    [Fintype.card (BooleanAntichain 0 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4))),
     Fintype.card (BooleanAntichain 1 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4))),
     Fintype.card (BooleanAntichain 2 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4))),
     Fintype.card (BooleanAntichain 3 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4))),
     Fintype.card (BooleanAntichain 4 (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4)))] =
      [1, 26, 150, 50, 5]
  rw [booleanAntichain_count_zero, uniform_singleton_count 5 4 (by decide), h2, h3, h4]
  decide

end BooleanAntichainsKernel
