import BooleanAntichainsKernel.IncidencePlanePairCounting
import BooleanAntichainsKernel.IncidencePlaneTriples
import Mathlib.Data.List.OfFn

namespace BooleanAntichainsKernel

open scoped Classical

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
variable [Fintype P] [Fintype L]

/-- The displayed complete distribution on the original incidence-plane
matroid's flat lattice, with q the actual plane order. -/
theorem incidencePlane_distribution :
    let q := Configuration.ProjectivePlane.order P L
    let N := q ^ 2 + q + 1
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (incidencePlaneMatroid P L)))) =
        [1, 2 * N + 1, N.choose 2 + N * q ^ 2, N.choose 3 - N * (q + 1).choose 3] := by
  dsimp only
  change
    [Fintype.card (BooleanAntichain 0 (MatroidFlat (incidencePlaneMatroid P L))),
     Fintype.card (BooleanAntichain 1 (MatroidFlat (incidencePlaneMatroid P L))),
     Fintype.card (BooleanAntichain 2 (MatroidFlat (incidencePlaneMatroid P L))),
     Fintype.card (BooleanAntichain 3 (MatroidFlat (incidencePlaneMatroid P L)))] = _
  rw [incidencePlane_zero_count, incidencePlane_singleton_count, incidencePlane_two_count,
    incidencePlane_three_count]

/-- The source's all-size enumeration, including every higher empty layer;
there is no coordinatization or Desarguesian assumption. -/
theorem incidencePlane_enumeration :
    let q := Configuration.ProjectivePlane.order P L
    let N := q ^ 2 + q + 1
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (incidencePlaneMatroid P L)))) =
        [1, 2 * N + 1, N.choose 2 + N * q ^ 2, N.choose 3 - N * (q + 1).choose 3] ∧
    ∀ k : ℕ, 3 < k → Fintype.card (BooleanAntichain k (MatroidFlat (incidencePlaneMatroid P L))) = 0 :=
  ⟨incidencePlane_distribution, incidencePlane_count_above_three⟩

end BooleanAntichainsKernel
