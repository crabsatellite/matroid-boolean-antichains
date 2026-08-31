import BooleanAntichainsKernel.FlatIntervalMinor
import BooleanAntichainsKernel.LatticeTransport
import BooleanAntichainsKernel.WeightedTheorem

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α] {M : Matroid α}
variable (X Y : MatroidFlat M) [Fact (X ≤ Y)]

abbrev IntervalBooleanAntichain :=
  BooleanAntichain (MatroidFlat.rank Y - MatroidFlat.rank X) (FlatInterval X Y)

/-- The size certificate uses the proved contraction rank identity; the
underlying finite set is sent through the literal `F ↦ F \ X` map. -/
noncomputable def intervalAntichainEquivMinorMaximum :
    IntervalBooleanAntichain X Y ≃ MaximumBooleanAntichain (flatIntervalMinor X Y) :=
  (booleanAntichainSizeEquiv (L := FlatInterval X Y)
    (flatIntervalMinor_total_rank X Y Fact.out).symm).trans
    (booleanAntichainOrderIsoEquiv (flatIntervalMinorOrderIso X Y Fact.out)
      (MatroidFlat.rank (⊤ : MatroidFlat (flatIntervalMinor X Y))))

@[simp] lemma intervalAntichainEquivMinorMaximum_val (C : IntervalBooleanAntichain X Y) :
    (intervalAntichainEquivMinorMaximum X Y C).1 =
      mapFamily (flatIntervalMinorOrderIso X Y Fact.out) C.1 := rfl

/-- The natural bijection in `thm:interval`, consuming the maximum theorem. -/
noncomputable def intervalAntichainEquivBasis :
    IntervalBooleanAntichain X Y ≃ SimplifiedBasis (flatIntervalMinor X Y) :=
  (intervalAntichainEquivMinorMaximum X Y).trans maximumAntichainEquivSimplifiedBasis

lemma interval_parallelClassElements (F : FlatInterval X Y) :
    parallelClassElements ((flatIntervalMinorOrderIso X Y Fact.out) F) =
      (F.1.1 \ X.1).toFinset := by
  ext e
  change e ∈ (((flatIntervalToMinor X Y F).1 \ (flatIntervalMinor X Y).closure ∅).toFinset) ↔
    e ∈ (F.1.1 \ X.1).toFinset
  simp only [Set.mem_toFinset]
  exact Iff.of_eq (congrArg (fun S : Set α ↦ e ∈ S) (flatInterval_minor_class X Y Fact.out F))

/-- Equation `eq:interval-weighted`, with literal interval atoms and the
paper's `A \ X` linear factors. -/
theorem interval_weighted_basis_polynomial :
    matroidBasisPolynomial (flatIntervalMinor X Y) =
      ∑ C : IntervalBooleanAntichain X Y,
        ∏ A ∈ spanAtomFinset C.1, ∑ e ∈ (A.1.1 \ X.1).toFinset,
          (MvPolynomial.X e : MvPolynomial α ℤ) := by
  rw [weighted_basis_polynomial]
  let E := intervalAntichainEquivMinorMaximum X Y
  calc
    _ = ∑ C : IntervalBooleanAntichain X Y,
        ∏ A ∈ spanAtomFinset (E C).1, ∑ e ∈ parallelClassElements A,
          (MvPolynomial.X e : MvPolynomial α ℤ) :=
      (E.sum_comp (fun D : MaximumBooleanAntichain (flatIntervalMinor X Y) ↦
        ∏ A ∈ spanAtomFinset D.1, ∑ e ∈ parallelClassElements A,
          (MvPolynomial.X e : MvPolynomial α ℤ))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C _
      dsimp only [E]
      rw [intervalAntichainEquivMinorMaximum_val,
        spanAtomFinset_mapFamily _ C.1 C.2.2, mapFamily,
        Equiv.finsetCongr_apply, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro A _
      change (∑ e ∈ parallelClassElements ((flatIntervalMinorOrderIso X Y Fact.out) A),
        (MvPolynomial.X e : MvPolynomial α ℤ)) = _
      rw [interval_parallelClassElements X Y A]

end BooleanAntichainsKernel
