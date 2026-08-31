import BooleanAntichainsKernel.InternalOrbitCount
import BooleanAntichainsKernel.InternalOrderingCount

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The exact ordered positive compositions in the paper's direct-sum count. -/
abbrev PositiveDimensionProfile (d k : ℕ) :=
  {p : Fin k → ℕ // (∀ i, 1 ≤ p i) ∧ (∑ i, p i) = d}

lemma positiveDimensionProfile_le {d k : ℕ} (p : PositiveDimensionProfile d k) (i : Fin k) :
    p.1 i ≤ d :=
  (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_eq p.2.2

def positiveDimensionCode {d k : ℕ} (p : PositiveDimensionProfile d k) : Fin k → Fin (d + 1) :=
  fun i ↦ ⟨p.1 i, Nat.lt_succ_of_le (positiveDimensionProfile_le p i)⟩

lemma positiveDimensionCode_injective {d k : ℕ} :
    Function.Injective (positiveDimensionCode (d := d) (k := k)) := by
  intro p q h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance (d k : ℕ) : Fintype (PositiveDimensionProfile d k) :=
  Fintype.ofInjective positiveDimensionCode positiveDimensionCode_injective

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {k : ℕ}

noncomputable def internalDimensionProfile (D : OrderedInternalDecomposition K V k) :
    PositiveDimensionProfile (Module.finrank K V) k :=
  ⟨fun i ↦ Module.finrank K (D.1 i), D.summand_finrank_ge_one, D.finrank_eq_sum.symm⟩

noncomputable def internalProfileSigmaEquiv :
    (Σ p : PositiveDimensionProfile (Module.finrank K V) k, SizedInternalDecomposition K V p.1) ≃
      OrderedInternalDecomposition K V k := by
  refine Equiv.ofBijective (fun x ↦ x.2.1) ⟨?_, ?_⟩
  · rintro ⟨p, D⟩ ⟨q, E⟩ h
    have hpq : p = q := by
      apply Subtype.ext
      funext i
      exact (D.2 i).symm.trans
        ((congrArg (fun A : OrderedInternalDecomposition K V k ↦ Module.finrank K (A.1 i)) h).trans (E.2 i))
    cases hpq
    have hDE : D = E := Subtype.ext h
    cases hDE
    rfl
  · intro D
    exact ⟨⟨internalDimensionProfile D, ⟨D, fun _ ↦ rfl⟩⟩, rfl⟩

variable [Fintype K] [Fintype V]

theorem orderedInternal_count_by_dimensions :
    Fintype.card (OrderedInternalDecomposition K V k) =
      ∑ p : PositiveDimensionProfile (Module.finrank K V) k,
        generalLinearCard K (Module.finrank K V) / ∏ i, generalLinearCard K (p.1 i) := by
  rw [← Fintype.card_congr (internalProfileSigmaEquiv (K := K) (V := V) (k := k)),
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  exact sizedInternal_count_of_profile p.1 p.2.1 p.2.2

theorem orderedInternal_count_by_dimensions_rational :
    (Fintype.card (OrderedInternalDecomposition K V k) : ℚ) =
      ∑ p : PositiveDimensionProfile (Module.finrank K V) k,
        (generalLinearCard K (Module.finrank K V) : ℚ) / ∏ i, (generalLinearCard K (p.1 i) : ℚ) := by
  rw [← Fintype.card_congr (internalProfileSigmaEquiv (K := K) (V := V) (k := k)),
    Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact sizedInternal_count_of_profile_rational p.1 p.2.1 p.2.2

/-- The paper's D_{d,k}(q), with g_d the actual finite-field GL cardinality. -/
noncomputable def directSumProfileCount (K : Type*) [Field K] [Fintype K] (d k : ℕ) : ℚ :=
  (1 / (k.factorial : ℚ)) *
    ∑ p : PositiveDimensionProfile d k,
      (generalLinearCard K d : ℚ) / ∏ i, (generalLinearCard K (p.1 i) : ℚ)

theorem unorderedInternal_count_by_dimensions :
    (Fintype.card (UnorderedInternalDecomposition K V k) : ℚ) =
      directSumProfileCount K (Module.finrank K V) k := by
  unfold directSumProfileCount
  conv_rhs => rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))).mpr
  calc
    _ = (Fintype.card (OrderedInternalDecomposition K V k) : ℚ) := by
      exact_mod_cast (orderedInternal_count_eq_unordered_mul_factorial (R := K) (V := V) (k := k)).symm
    _ = _ := orderedInternal_count_by_dimensions_rational

end BooleanAntichainsKernel
