import BooleanAntichainsKernel.PartitionFlatRank

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α]

local notation "M" => cycleMatroid (completeLabelledGraph α)

theorem completeMatroid_loops_empty : (M).loops = ∅ := by
  ext q
  change (M).IsLoop q ↔ False
  rw [cycleMatroid_isLoop_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact completeLabelledGraph_no_loops q x hx
  · intro h
    exact h.elim

theorem completeMatroid_singleton_closure (e : (completeLabelledGraph α).edgeSet) :
    (M).closure {e.1} = {e.1} := by
  have hclass := cycleMatroid_parallelClass_eq (completeLabelledGraph α) e
    (GraphIsSimple.edge_nonloop (completeLabelledGraph α) completeLabelledGraph_simple e)
  rw [completeMatroid_loops_empty, Set.sdiff_empty] at hclass
  ext q
  constructor
  · intro hq
    rw [hclass] at hq
    obtain ⟨x, y, he, hq⟩ := hq
    exact Set.mem_singleton_iff.mpr (completeLabelledGraph_unique_edge hq he)
  · intro hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact (M).mem_closure_self e.1 e.2

/-- On the actual complete graph each rank-one flat is a singleton of its
original edge label; no parallel-class multiplicity is discarded. -/
theorem completeRankOneFlat_singleton (F : RankOneFlat M) :
    F.1.1 = {rankOneRepresentative F} :=
  (rankOneRepresentative_spec F).2.2.symm.trans
    (completeMatroid_singleton_closure ⟨rankOneRepresentative F, rankOneRepresentative_mem_ground F⟩)

noncomputable def completeRankOneRepresentative (F : RankOneFlat M) :
    (completeLabelledGraph α).edgeSet :=
  ⟨rankOneRepresentative F, rankOneRepresentative_mem_ground F⟩

theorem completeRankOneRepresentative_injective :
    Function.Injective (completeRankOneRepresentative (α := α)) := by
  intro F H h
  exact rankOneRepresentative_injective (congrArg (fun e : (completeLabelledGraph α).edgeSet ↦ e.1) h)

theorem completeRankOneRepresentative_surjective :
    Function.Surjective (completeRankOneRepresentative (α := α)) := by
  intro e
  let F : RankOneFlat M := ⟨elementFlat M e.1,
    elementFlat_rank_one (GraphIsSimple.edge_nonloop (completeLabelledGraph α) completeLabelledGraph_simple e)⟩
  have hF : F.1.1 = {e.1} := completeMatroid_singleton_closure e
  have hrep := (rankOneRepresentative_spec F).1
  rw [hF] at hrep
  exact ⟨F, Subtype.ext (Set.mem_singleton_iff.mp hrep)⟩

noncomputable def completeRankOneRepresentativeEquiv :
    RankOneFlat M ≃ (completeLabelledGraph α).edgeSet :=
  Equiv.ofBijective completeRankOneRepresentative
    ⟨completeRankOneRepresentative_injective, completeRankOneRepresentative_surjective⟩

theorem completeRankOneRepresentativeEquiv_val (F : RankOneFlat M) :
    (completeRankOneRepresentativeEquiv F).1 = rankOneRepresentative F := rfl

theorem completeRankOneRepresentativeEquiv_singleton (F : RankOneFlat M) :
    F.1.1 = {(completeRankOneRepresentativeEquiv F).1} :=
  completeRankOneFlat_singleton F

end BooleanAntichainsKernel
