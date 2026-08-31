import BooleanAntichainsKernel.Pairs
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Möbius formula for Boolean pairs
-/

namespace BooleanAntichainsKernel

open Finset

section MobiusPair

variable {L : Type*} [Fintype L] [DecidableEq L]
variable [Lattice L] [OrderBot L] [OrderTop L] [DecidableLE L] [DecidableLT L]

local instance finiteLocallyFiniteOrder : LocallyFiniteOrder L :=
  Fintype.toLocallyFiniteOrder

def lowerIntervalCard (Y : L) : ℕ := (Finset.Iic Y).card

def orderedJoinCount (Y : L) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : L × L => p.1 ⊔ p.2 = Y).card

def properTopJoinPairs : Finset (L × L) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p : L × L =>
    p.1 ≠ ⊤ ∧ p.2 ≠ ⊤ ∧ p.1 ⊔ p.2 = ⊤

def properTopJoinCount : ℕ := #(properTopJoinPairs (L := L))

def topCoordinatePairs : Finset (L × L) :=
  ({⊤} ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ {⊤})

omit [DecidableLE L] [DecidableLT L] in
def pairFunctionEquiv : (L × L) ≃ (Fin 2 → L) where
  toFun p := pairTuple p.1 p.2
  invFun H := (H 0, H 1)
  left_inv p := by simp
  right_inv H := by
    funext i
    fin_cases i <;> simp

abbrev ProperTopJoinPair :=
  {p : L × L // p.1 ≠ ⊤ ∧ p.2 ≠ ⊤ ∧ p.1 ⊔ p.2 = ⊤}

noncomputable instance : Fintype (ProperTopJoinPair (L := L)) := by
  classical
  exact Subtype.fintype _

omit [DecidableLE L] [DecidableLT L] in
def properTopJoinPairEquivOrderedBoolean :
    ProperTopJoinPair (L := L) ≃ OrderedBooleanTuple 2 L where
  toFun p := ⟨pairTuple p.1.1 p.1.2, (pair_isBoolean_iff _ _).mpr p.2⟩
  invFun H := ⟨(H.1 0, H.1 1), by
    apply (pair_isBoolean_iff (H.1 0) (H.1 1)).mp
    have heq : pairTuple (H.1 0) (H.1 1) = H.1 := by
      funext i
      fin_cases i <;> simp
    exact heq.symm ▸ H.2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv H := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp

omit [DecidableLE L] [DecidableLT L] in
lemma properTopJoinCount_eq_card_orderedBoolean :
    properTopJoinCount (L := L) = Fintype.card (OrderedBooleanTuple 2 L) := by
  classical
  rw [← Fintype.card_congr properTopJoinPairEquivOrderedBoolean]
  rw [Fintype.card_subtype]
  rfl

omit [OrderBot L] [DecidableLE L] [DecidableLT L] in
lemma topCoordinatePairs_card_add_one :
    #(topCoordinatePairs (L := L)) + 1 = 2 * Fintype.card L := by
  have hinter :
      (({⊤} ×ˢ (Finset.univ : Finset L)) ∩
        ((Finset.univ : Finset L) ×ˢ {⊤})) = {((⊤ : L), (⊤ : L))} := by
    ext p
    simp [Prod.ext_iff]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂.symm⟩
  rw [topCoordinatePairs, Finset.card_union]
  rw [hinter]
  simp
  have hpos : 0 < Fintype.card L := Fintype.card_pos_iff.mpr ⟨⊤⟩
  omega

omit [OrderBot L] [DecidableLE L] [DecidableLT L] in
lemma topJoinPairs_eq_proper_union_topCoordinate :
    ((Finset.univ ×ˢ Finset.univ).filter fun p : L × L => p.1 ⊔ p.2 = ⊤) =
      properTopJoinPairs (L := L) ∪ topCoordinatePairs (L := L) := by
  ext p
  simp only [properTopJoinPairs, topCoordinatePairs, Finset.mem_filter,
    Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_singleton]
  constructor
  · intro hsup
    by_cases h₁ : p.1 = ⊤
    · exact Or.inr (Or.inl ⟨h₁, trivial⟩)
    by_cases h₂ : p.2 = ⊤
    · exact Or.inr (Or.inr h₂)
    exact Or.inl ⟨h₁, h₂, hsup⟩
  · rintro (h | h)
    · exact h.2.2
    · rcases h with h | h
      · simp [h]
      · simp [h]

omit [OrderBot L] [DecidableLE L] [DecidableLT L] in
lemma properTopJoinPairs_disjoint_topCoordinate :
    Disjoint (properTopJoinPairs (L := L)) (topCoordinatePairs (L := L)) := by
  rw [Finset.disjoint_left]
  intro p hp htop
  simp only [properTopJoinPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and] at hp
  simp only [topCoordinatePairs, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_univ, and_true, true_and] at htop
  rcases htop with h | h
  · exact hp.1 h
  · exact hp.2.1 h

omit [OrderBot L] [DecidableLE L] [DecidableLT L] in
lemma orderedJoinCount_top_add_one :
    orderedJoinCount (⊤ : L) + 1 =
      properTopJoinCount (L := L) + 2 * Fintype.card L := by
  rw [orderedJoinCount, topJoinPairs_eq_proper_union_topCoordinate,
    Finset.card_union_of_disjoint properTopJoinPairs_disjoint_topCoordinate,
    properTopJoinCount, Nat.add_assoc, topCoordinatePairs_card_add_one]

omit [OrderTop L] in
lemma lowerIntervalCard_sq_eq_sum_orderedJoinCount (Y : L) :
    lowerIntervalCard Y ^ 2 = ∑ X ∈ Finset.Iic Y, orderedJoinCount X := by
  classical
  have hmap : ∀ p ∈ (Finset.Iic Y ×ˢ Finset.Iic Y), p.1 ⊔ p.2 ∈ Finset.Iic Y := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_Iic] at hp ⊢
    exact sup_le hp.1 hp.2
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := Finset.Iic Y ×ˢ Finset.Iic Y) (t := Finset.Iic Y)
    (f := fun p : L × L ↦ p.1 ⊔ p.2) hmap
  calc
    lowerIntervalCard Y ^ 2 = #(Finset.Iic Y ×ˢ Finset.Iic Y) := by
      simp [lowerIntervalCard, pow_two]
    _ = ∑ X ∈ Finset.Iic Y,
        #((Finset.Iic Y ×ˢ Finset.Iic Y).filter fun p : L × L ↦ p.1 ⊔ p.2 = X) :=
      hfiber
    _ = ∑ X ∈ Finset.Iic Y, orderedJoinCount X := by
      apply Finset.sum_congr rfl
      intro X hXY
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Iic,
        Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · intro hp
        have hsupY : p.1 ⊔ p.2 ≤ Y := hp ▸ Finset.mem_Iic.mp hXY
        exact ⟨⟨le_sup_left.trans hsupY, le_sup_right.trans hsupY⟩, hp⟩

def mobiusPairSum : ℤ :=
  ∑ X ∈ Finset.Iic (⊤ : L),
    IncidenceAlgebra.mu ℤ X ⊤ * (lowerIntervalCard X : ℤ) ^ 2

theorem orderedJoinCount_top_eq_mobiusPairSum :
    (orderedJoinCount (⊤ : L) : ℤ) = mobiusPairSum (L := L) := by
  let f : L → ℤ := fun X ↦ orderedJoinCount X
  let g : L → ℤ := fun X ↦ (lowerIntervalCard X : ℤ) ^ 2
  have hconv : ∀ Y, g Y = ∑ X ∈ Finset.Iic Y, f X := by
    intro Y
    dsimp [f, g]
    exact_mod_cast lowerIntervalCard_sq_eq_sum_orderedJoinCount Y
  have hinv := IncidenceAlgebra.moebius_inversion_bot f g hconv (⊤ : L)
  simpa [f, g, mobiusPairSum] using hinv

omit [DecidableLE L] [DecidableLT L] in
lemma properTopJoinCount_eq_two_mul_booleanPairCount :
    properTopJoinCount (L := L) = 2 * Fintype.card (BooleanAntichain 2 L) := by
  rw [properTopJoinCount_eq_card_orderedBoolean, card_orderedBooleanTuple]
  norm_num [Nat.factorial, Nat.mul_comm]

/-- The integer form of manuscript `eq:size-two-mobius`, before division by two. -/
theorem mobius_formula_pairs_doubled :
    2 * (Fintype.card (BooleanAntichain 2 L) : ℤ) =
      mobiusPairSum (L := L) - 2 * (Fintype.card L : ℤ) + 1 := by
  have hcount :
      (orderedJoinCount (⊤ : L) : ℤ) + 1 =
        (properTopJoinCount (L := L) : ℤ) + 2 * (Fintype.card L : ℤ) := by
    exact_mod_cast orderedJoinCount_top_add_one (L := L)
  have hproper :
      (properTopJoinCount (L := L) : ℤ) =
        2 * (Fintype.card (BooleanAntichain 2 L) : ℤ) := by
    exact_mod_cast properTopJoinCount_eq_two_mul_booleanPairCount (L := L)
  rw [orderedJoinCount_top_eq_mobiusPairSum] at hcount
  omega

/-- The displayed Möbius formula in `thm:size-two`. -/
theorem mobius_formula_pairs :
    (Fintype.card (BooleanAntichain 2 L) : ℤ) =
      (mobiusPairSum (L := L) - 2 * (Fintype.card L : ℤ) + 1) / 2 := by
  rw [← mobius_formula_pairs_doubled (L := L)]
  norm_num

end MobiusPair

end BooleanAntichainsKernel
