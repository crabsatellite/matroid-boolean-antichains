import BooleanAntichainsKernel.OrderedPartitionInverse
import BooleanAntichainsKernel.BellSquarePowerProfiles
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp

namespace BooleanAntichainsKernel

open scoped Classical

def profiledBlocksFromSigma {n b : ℕ}
    (t : Σ p : PositiveBlockProfile n b,
      SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) :
    ProfiledOrderedBlocks n b :=
  ⟨(t.1.1, t.2.1), t.1.2.1, t.1.2.2,
    t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩

theorem profiledBlocksFromSigma_injective {n b : ℕ} :
    Function.Injective (profiledBlocksFromSigma :
      (Σ p : PositiveBlockProfile n b,
        SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) →
          ProfiledOrderedBlocks n b) := by
  rintro ⟨p, B⟩ ⟨q, C⟩ h
  have hpval : p.1 = q.1 := congrArg (fun t : ProfiledOrderedBlocks n b ↦ t.1.1) h
  have hp : p = q := Subtype.ext hpval
  subst q
  have hBval : B.1 = C.1 := congrArg (fun t : ProfiledOrderedBlocks n b ↦ t.1.2) h
  have hB : B = C := Subtype.ext hBval
  subst C
  rfl

theorem profiledBlocksFromSigma_surjective {n b : ℕ} :
    Function.Surjective (profiledBlocksFromSigma :
      (Σ p : PositiveBlockProfile n b,
        SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) →
          ProfiledOrderedBlocks n b) := by
  intro t
  exact ⟨⟨⟨t.1.1, t.2.1, t.2.2.1⟩,
    ⟨t.1.2, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩⟩, rfl⟩

noncomputable def profiledBlocksSigmaEquiv (n b : ℕ) :
    (Σ p : PositiveBlockProfile n b,
      SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) ≃
        ProfiledOrderedBlocks n b :=
  Equiv.ofBijective profiledBlocksFromSigma
    ⟨profiledBlocksFromSigma_injective, profiledBlocksFromSigma_surjective⟩

noncomputable def orderedPartitionEquivSigmaBlocks (n b : ℕ) :
    OrderedFinitePartition n b ≃
      (Σ p : PositiveBlockProfile n b,
        SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) :=
  (orderedPartitionEquivProfiledBlocks n b).trans (profiledBlocksSigmaEquiv n b).symm

def partitionBellSquareWeight {n b : ℕ} (P : PartitionsWithBlocks (Fin n) b) : ℚ :=
  ∏ B : P.1.parts, (Nat.bell B.1.card : ℚ) ^ 2

noncomputable def partitionBellSquareWeightedCount (n b : ℕ) : ℚ :=
  ∑ P : PartitionsWithBlocks (Fin n) b, partitionBellSquareWeight P

noncomputable def partitionBlockEnumeration {n b : ℕ}
    (P : PartitionsWithBlocks (Fin n) b) : Fin b ≃ P.1.parts :=
  (Finset.equivFinOfCardEq P.2).symm

theorem orderedPartition_weight_sum (n b : ℕ) :
    (∑ t : OrderedFinitePartition n b, partitionBellSquareWeight t.1) =
      (b.factorial : ℚ) * partitionBellSquareWeightedCount n b := by
  unfold partitionBellSquareWeightedCount
  change (∑ t : (Σ P : PartitionsWithBlocks (Fin n) b, Fin b ≃ P.1.parts),
    partitionBellSquareWeight t.1) = _
  calc
    _ = ∑ P : PartitionsWithBlocks (Fin n) b,
        ∑ _e : Fin b ≃ P.1.parts, partitionBellSquareWeight P :=
      Fintype.sum_sigma'
        (fun (P : PartitionsWithBlocks (Fin n) b) (_e : Fin b ≃ P.1.parts) ↦
          partitionBellSquareWeight P)
    _ = ∑ P : PartitionsWithBlocks (Fin n) b,
        (b.factorial : ℚ) * partitionBellSquareWeight P := by
      apply Finset.sum_congr rfl
      intro P _hP
      calc
        (∑ _e : Fin b ≃ P.1.parts, partitionBellSquareWeight P) =
            (Fintype.card (Fin b ≃ P.1.parts) : ℚ) * partitionBellSquareWeight P := by
          simp
        _ = _ := by
          rw [Fintype.card_equiv (partitionBlockEnumeration P), Fintype.card_fin]
    _ = _ := by rw [← Finset.mul_sum]

theorem orderedPartition_profile_weight_sum (n b : ℕ) :
    (∑ t : OrderedFinitePartition n b, partitionBellSquareWeight t.1) =
      ∑ p : PositiveBlockProfile n b,
        (Fintype.card
          (SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) : ℚ) *
            ∏ i : Fin b, (Nat.bell (p.1 i) : ℚ) ^ 2 := by
  calc
    _ = ∑ t : ProfiledOrderedBlocks n b,
        ∏ i : Fin b, (Nat.bell (t.1.1 i) : ℚ) ^ 2 := by
      have h := (orderedPartitionEquivProfiledBlocks n b).sum_comp
        (fun t : ProfiledOrderedBlocks n b ↦
          ∏ i : Fin b, (Nat.bell (t.1.1 i) : ℚ) ^ 2)
      calc
        _ = ∑ t : OrderedFinitePartition n b,
            ∏ i : Fin b, (Nat.bell ((orderedPartitionToProfiledBlocks t).1.1 i) : ℚ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact (orderedPartition_weight t).symm
        _ = _ := h
    _ = ∑ t : (Σ p : PositiveBlockProfile n b,
        SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1),
        ∏ i : Fin b, (Nat.bell (t.1.1 i) : ℚ) ^ 2 := by
      exact (profiledBlocksSigmaEquiv n b).sum_comp
        (fun t : ProfiledOrderedBlocks n b ↦
          ∏ i : Fin b, (Nat.bell (t.1.1 i) : ℚ) ^ 2) |>.symm
    _ = _ := by
      calc
        _ = ∑ p : PositiveBlockProfile n b,
            ∑ _B : SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1,
              ∏ i : Fin b, (Nat.bell (p.1 i) : ℚ) ^ 2 :=
          Fintype.sum_sigma' _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p _hp
          simp

theorem positiveProfile_scaled_term {n b : ℕ} (p : PositiveBlockProfile n b) :
    (n.factorial : ℚ) * positiveProfilePowerTerm p =
      (Fintype.card
        (SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) : ℚ) *
          ∏ i : Fin b, (Nat.bell (p.1 i) : ℚ) ^ 2 := by
  have hs := sizedDisjointBlocks_mul_factorials
    (A := (Finset.univ : Finset (Fin n))) (p := p.1)
  rw [p.2.1, Finset.card_univ, Fintype.card_fin, Nat.descFactorial_self] at hs
  have hsQ :
      (Fintype.card
        (SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) : ℚ) *
          (∏ i : Fin b, ((p.1 i).factorial : ℚ)) = n.factorial := by
    exact_mod_cast hs
  have hprod : positiveProfilePowerTerm p =
      (∏ i : Fin b, (Nat.bell (p.1 i) : ℚ) ^ 2) /
        ∏ i : Fin b, ((p.1 i).factorial : ℚ) := by
    rw [positiveProfilePowerTerm, Finset.prod_div_distrib]
  rw [hprod, ← hsQ]
  have hne : (∏ i : Fin b, ((p.1 i).factorial : ℚ)) ≠ 0 := by
    positivity
  field_simp

/-- The exact labelled exponential-formula bridge for one fixed block
count. Both factorials are earned from actual fibres. -/
theorem bellSquareEGF_coeff_pow_partition (n b : ℕ) :
    (n.factorial : ℚ) * PowerSeries.coeff n (bellSquareEGF ^ b) =
      (b.factorial : ℚ) * partitionBellSquareWeightedCount n b := by
  rw [bellSquareEGF_coeff_pow_profiles, Finset.mul_sum]
  calc
    _ = ∑ p : PositiveBlockProfile n b,
        (Fintype.card
          (SizedDisjointBlocks (Finset.univ : Finset (Fin n)) p.1) : ℚ) *
            ∏ i : Fin b, (Nat.bell (p.1 i) : ℚ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact positiveProfile_scaled_term p
    _ = ∑ t : OrderedFinitePartition n b, partitionBellSquareWeight t.1 :=
      (orderedPartition_profile_weight_sum n b).symm
    _ = _ := orderedPartition_weight_sum n b

end BooleanAntichainsKernel
