import BooleanAntichainsKernel.Distributive
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {P : Type*} [PartialOrder P] [Fintype P]

abbrev NonemptyFilter (P : Type*) [PartialOrder P] :=
  {F : UpperSet P // (F : Set P).Nonempty}

noncomputable instance : Fintype (NonemptyFilter P) := Subtype.fintype _

/-- The actual intersection graph from `thm:distributive`: its vertices are
nonempty upper sets, and distinct vertices are adjacent iff they intersect. -/
def filterIntersectionGraph (P : Type*) [PartialOrder P] : SimpleGraph (NonemptyFilter P) where
  Adj F G := F ≠ G ∧ ((F.1 : Set P) ∩ (G.1 : Set P)).Nonempty
  symm := by
    constructor
    intro F G h
    exact ⟨h.1.symm, by simpa only [Set.inter_comm] using h.2⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

noncomputable def underlyingFilterFamily (B : Finset (NonemptyFilter P)) : Finset (UpperSet P) :=
  B.image Subtype.val

omit [Fintype P] in
lemma underlyingFilterFamily_card (B : Finset (NonemptyFilter P)) :
    (underlyingFilterFamily B).card = B.card :=
  Finset.card_image_of_injective B Subtype.val_injective

omit [Fintype P] in
lemma underlyingFilterFamily_nonempty (B : Finset (NonemptyFilter P)) :
    ∀ F ∈ underlyingFilterFamily B, (F : Set P).Nonempty := by
  intro F hF
  rcases Finset.mem_image.mp hF with ⟨q, _, rfl⟩
  exact q.2

omit [Fintype P] in
lemma filterGraph_independent_iff_disjoint (B : Finset (NonemptyFilter P)) :
    (filterIntersectionGraph P).IsIndepSet (B : Set (NonemptyFilter P)) ↔
      ∀ F ∈ underlyingFilterFamily B, ∀ G ∈ underlyingFilterFamily B, F ≠ G →
        Disjoint (F : Set P) (G : Set P) := by
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h F hF G hG hFG
    rcases Finset.mem_image.mp hF with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hG with ⟨r, hr, rfl⟩
    apply Set.disjoint_iff_inter_eq_empty.mpr
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hinter
    have hqr : q ≠ r := fun heq ↦ hFG (congrArg Subtype.val heq)
    exact h hq hr hqr ⟨hqr, hinter⟩
  · intro h q hq r hr hqr hadj
    have hdisj := h q.1 (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      r.1 (Finset.mem_image.mpr ⟨r, hr, rfl⟩) (fun heq ↦ hqr (Subtype.ext heq))
    exact (Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hdisj)) hadj.2

abbrev GraphIndependentFamily {V : Type*} (G : SimpleGraph V) (k : ℕ) :=
  {B : Finset V // B.card = k ∧ G.IsIndepSet (B : Set V)}

noncomputable instance {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ} :
    Fintype (GraphIndependentFamily G k) := Subtype.fintype _

noncomputable def liftFilterFamily (C : Finset (UpperSet P)) : Finset (NonemptyFilter P) :=
  Finset.univ.filter fun F ↦ F.1 ∈ C

lemma underlyingFilterFamily_lift (C : Finset (UpperSet P))
    (hC : ∀ F ∈ C, (F : Set P).Nonempty) : underlyingFilterFamily (liftFilterFamily C) = C := by
  ext F
  constructor
  · intro hF
    rcases Finset.mem_image.mp hF with ⟨q, hq, rfl⟩
    exact (Finset.mem_filter.mp hq).2
  · intro hF
    exact Finset.mem_image.mpr ⟨⟨F, hC F hF⟩,
      Finset.mem_filter.mpr ⟨mem_univ _, hF⟩, rfl⟩

lemma lift_underlyingFilterFamily (B : Finset (NonemptyFilter P)) :
    liftFilterFamily (underlyingFilterFamily B) = B := by
  ext q
  simp only [liftFilterFamily, underlyingFilterFamily, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, heq⟩
    exact (Subtype.ext heq : p = q) ▸ hp
  · intro hq
    exact ⟨q, hq, rfl⟩

noncomputable def disjointFiltersEquivGraphIndependent (k : ℕ) :
    DisjointFilterFamily k P ≃ GraphIndependentFamily (filterIntersectionGraph P) k where
  toFun C := ⟨liftFilterFamily C.1, by
    refine ⟨?_, ?_⟩
    · rw [← underlyingFilterFamily_card, underlyingFilterFamily_lift C.1 C.2.2.1]
      exact C.2.1
    · rw [filterGraph_independent_iff_disjoint, underlyingFilterFamily_lift C.1 C.2.2.1]
      exact C.2.2.2⟩
  invFun B := ⟨underlyingFilterFamily B.1, by
    exact ⟨(underlyingFilterFamily_card B.1).trans B.2.1,
      underlyingFilterFamily_nonempty B.1, (filterGraph_independent_iff_disjoint B.1).mp B.2.2⟩⟩
  left_inv C := Subtype.ext (underlyingFilterFamily_lift C.1 C.2.2.1)
  right_inv B := Subtype.ext (lift_underlyingFilterFamily B.1)

noncomputable def booleanAntichainEquivGraphIndependent (k : ℕ) :
    BooleanAntichain k (LowerSet P) ≃ GraphIndependentFamily (filterIntersectionGraph P) k :=
  distributiveAntichainEquivDisjointFilters.trans (disjointFiltersEquivGraphIndependent k)

theorem distributive_count_eq_graph_independent (k : ℕ) :
    Fintype.card (BooleanAntichain k (LowerSet P)) =
      Fintype.card (GraphIndependentFamily (filterIntersectionGraph P) k) :=
  Fintype.card_congr (booleanAntichainEquivGraphIndependent k)

end BooleanAntichainsKernel
