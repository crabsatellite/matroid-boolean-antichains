import BooleanAntichainsKernel.SimplifiedBasis
import Mathlib.Data.Fintype.EquivFin

namespace BooleanAntichainsKernel

open Set Finset

variable {α : Type*} [Fintype α] {M : Matroid α}

/-- Lemma 2.2, with the paper's indexed rank-one flats.  The intersection
proof below uses the displayed submodularity inequality, not an alternative
independence-closure identity. -/
theorem indexed_simplified_basis_span {r : ℕ} (A : Fin r → MatroidFlat M)
    (hAinj : Function.Injective A) (hrank : ∀ i, MatroidFlat.rank (A i) = 1)
    (htop : Finset.univ.sup A = ⊤)
    (hr : MatroidFlat.rank (⊤ : MatroidFlat M) = r) :
    (∀ S T : Finset (Fin r),
      S.sup A ⊔ T.sup A = (S ∪ T).sup A ∧
      S.sup A ⊓ T.sup A = (S ∩ T).sup A) ∧
    Function.Injective (fun S : Finset (Fin r) ↦ S.sup A) ∧
    (∀ S : Finset (Fin r), MatroidFlat.rank (S.sup A) = S.card) := by
  classical
  choose e _heMem _heNonloop he using fun i ↦ rank_one_flat_has_representative (A i) (hrank i)
  have hb : M.IsBase (Set.range e) := rank_one_representatives_isBase A hAinj e he htop hr
  have hfaces : ∀ S : Finset (Fin r), MatroidFlat.rank (S.sup A) = S.card :=
    representative_face_rank A hAinj e he hb
  have hmeet (S T : Finset (Fin r)) : S.sup A ⊓ T.sup A = (S ∩ T).sup A := by
    have hle : (S ∩ T).sup A ≤ S.sup A ⊓ T.sup A :=
      le_inf (Finset.sup_mono Finset.inter_subset_left) (Finset.sup_mono Finset.inter_subset_right)
    have hsub := MatroidFlat.rank_submod (S.sup A) (T.sup A)
    rw [← Finset.sup_union, hfaces (S ∪ T), hfaces S, hfaces T] at hsub
    have hcard := Finset.card_union_add_card_inter S T
    have hl := MatroidFlat.rank_mono hle
    rw [hfaces (S ∩ T)] at hl
    have hrankEq : MatroidFlat.rank ((S ∩ T).sup A) = MatroidFlat.rank (S.sup A ⊓ T.sup A) := by
      rw [hfaces (S ∩ T)]
      omega
    exact (MatroidFlat.eq_of_le_of_rank_eq hle hrankEq).symm
  refine ⟨fun S T ↦ ⟨Finset.sup_union.symm, hmeet S T⟩, ?_, hfaces⟩
  intro S T hST
  change S.sup A = T.sup A at hST
  have hI : (S ∩ T).sup A = S.sup A := by rw [← hmeet, hST, inf_idem]
  have hI' : (S ∩ T).sup A = T.sup A := hI.trans hST
  have hcardS : (S ∩ T).card = S.card := by
    rw [← hfaces (S ∩ T), ← hfaces S, hI]
  have hcardT : (S ∩ T).card = T.card := by
    rw [← hfaces (S ∩ T), ← hfaces T, hI']
  exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcardS.ge).symm.trans
    (Finset.eq_of_subset_of_card_le Finset.inter_subset_right hcardT.ge)

/-- The same producer on the literal elements of an unordered simplified
basis.  The `Fin r` transport is supplied and consumed here. -/
theorem simplified_basis_span (A : Finset (MatroidFlat M)) (hA : IsSimplifiedBasis M A) :
    (∀ S T : Finset A,
      S.sup Subtype.val ⊔ T.sup Subtype.val = (S ∪ T).sup Subtype.val ∧
      S.sup Subtype.val ⊓ T.sup Subtype.val = (S ∩ T).sup Subtype.val) ∧
    Function.Injective (fun S : Finset A ↦ S.sup (Subtype.val : A → MatroidFlat M)) := by
  classical
  let e : Fin A.card ≃ A := (Finset.equivFin A).symm
  let f : Fin A.card → MatroidFlat M := fun i ↦ (e i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hftop : Finset.univ.sup f = ⊤ := by
    have huniv : (Finset.univ : Finset (Fin A.card)).image f = A := by
      ext F
      constructor
      · intro hF
        rcases Finset.mem_image.mp hF with ⟨i, _, rfl⟩
        exact (e i).2
      · intro hF
        obtain ⟨i, hi⟩ := e.surjective ⟨F, hF⟩
        exact Finset.mem_image.mpr ⟨i, mem_univ i, congrArg Subtype.val hi⟩
    calc
      Finset.univ.sup f = (Finset.univ.image f).sup id :=
        (Finset.sup_image (Finset.univ : Finset (Fin A.card)) f id).symm
      _ = ⊤ := by rw [huniv]; exact hA.2.2
  have hindexed := indexed_simplified_basis_span f hf
    (fun i ↦ hA.1 (f i) (e i).2) hftop hA.2.1.symm
  let E := e.finsetCongr
  have hsup (S : Finset (Fin A.card)) : (E S).sup Subtype.val = S.sup f := by
    exact Finset.sup_map S e.toEmbedding Subtype.val
  have htransport (S : Finset A) : S.sup Subtype.val = (E.symm S).sup f := by
    rw [← hsup, E.apply_symm_apply]
  have hUnion (S T : Finset A) : E.symm (S ∪ T) = E.symm S ∪ E.symm T := by
    exact Finset.map_union S T
  have hInter (S T : Finset A) : E.symm (S ∩ T) = E.symm S ∩ E.symm T := by
    exact Finset.map_inter S T
  constructor
  · intro S T
    rw [htransport S, htransport T, htransport (S ∪ T), htransport (S ∩ T),
      hUnion, hInter]
    exact hindexed.1 _ _
  · intro S T hST
    apply E.symm.injective
    apply hindexed.2.1
    change (E.symm S).sup f = (E.symm T).sup f
    change S.sup Subtype.val = T.sup Subtype.val at hST
    rw [← htransport, ← htransport, hST]

end BooleanAntichainsKernel
