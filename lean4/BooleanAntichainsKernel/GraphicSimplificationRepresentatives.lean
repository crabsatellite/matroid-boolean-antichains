import BooleanAntichainsKernel.GraphicWeights
import BooleanAntichainsKernel.GraphicSimplifiedComponents

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

attribute [local instance] cycleMatroidGroundFintype

local notation "N" => Matroid.restrictSubtype (cycleMatroid G) (Matroid.E (cycleMatroid G))

noncomputable def graphicGroundRankOneEquiv :
    RankOneFlat N ≃ (graphSimplification G).edgeSet :=
  (matroidGroundRankOneEquiv (cycleMatroid G)).trans (cycleRankOneEquivSimpleEdges G)

/-- The existing simplification representative, with its original edge
label restored. This makes no new choice of representative. -/
noncomputable def graphicGroundRepresentative (A : RankOneFlat N) : G.edgeSet :=
  ⟨(rankOneRepresentative A).1, (rankOneRepresentative A).2⟩

noncomputable def graphicGroundOriginalLabel (A : RankOneFlat N) : β :=
  (graphicGroundRepresentative G A).1

noncomputable def graphicGroundSimpleLabel (A : RankOneFlat N) : Sym2 G.vertexSet :=
  (graphicGroundRankOneEquiv G A).1

theorem graphicGroundRepresentative_injective :
    Function.Injective (graphicGroundRepresentative G) := by
  intro A B h
  apply rankOneRepresentative_injective
  exact Subtype.ext (congrArg (fun e : G.edgeSet ↦ e.1) h)

theorem graphicGroundOriginalLabel_injective :
    Function.Injective (graphicGroundOriginalLabel G) :=
  Subtype.val_injective.comp (graphicGroundRepresentative_injective G)

theorem graphicGroundSimpleLabel_injective :
    Function.Injective (graphicGroundSimpleLabel G) :=
  Subtype.val_injective.comp (graphicGroundRankOneEquiv G).injective

theorem graphicGroundRepresentative_in_class (A : RankOneFlat N) :
    (graphicGroundRepresentative G A).1 ∈
      (matroidGroundRankOneEquiv (cycleMatroid G) A).1.1 \ (cycleMatroid G).loops := by
  change (rankOneRepresentative A).1 ∈
    (matroidGroundFlatOrderIso (cycleMatroid G) A.1).1 \ (cycleMatroid G).loops
  rw [← matroidGround_parallelClassSet]
  exact ⟨rankOneRepresentative A,
    ⟨(rankOneRepresentative_spec A).1, (rankOneRepresentative_spec A).2.1.not_isLoop⟩, rfl⟩

/-- The original representative has exactly the endpoints of its simple
edge. This proved equality is consumed by all later graph transports. -/
theorem graphicGroundRepresentative_ends (A : RankOneFlat N) :
    graphEdgeEnds G (graphicGroundRepresentative G A) = graphicGroundSimpleLabel G A :=
  (cycleRankOneSimpleEdge_class_member G (matroidGroundRankOneEquiv (cycleMatroid G) A)
    (graphicGroundRepresentative G A)).mp (graphicGroundRepresentative_in_class G A)

theorem graphicGroundSimpleLabel_range :
    Set.range (graphicGroundSimpleLabel G) = (graphSimplifiedGraph G).edgeSet := by
  ext q
  constructor
  · rintro ⟨A, rfl⟩
    exact (graphicGroundRankOneEquiv G A).2
  · intro hq
    obtain ⟨A, hA⟩ := (graphicGroundRankOneEquiv G).surjective ⟨q, hq⟩
    exact ⟨A, congrArg (fun e : (graphSimplification G).edgeSet ↦ e.1) hA⟩

theorem graphicGroundOriginalLabel_image_ground (X : Set (RankOneFlat N)) :
    graphicGroundOriginalLabel G '' X ⊆ G.edgeSet := by
  rintro e ⟨A, _hA, rfl⟩
  exact (graphicGroundRepresentative G A).2

theorem graphicGroundSimpleLabel_image_ground (X : Set (RankOneFlat N)) :
    graphicGroundSimpleLabel G '' X ⊆ (graphSimplifiedGraph G).edgeSet := by
  rintro e ⟨A, _hA, rfl⟩
  exact (graphicGroundRankOneEquiv G A).2

/-- Exact equality of the whole support, on all original vertices, for
every family of rank-one flats. It is not only an edge-count identity. -/
theorem graphicGroundRepresentative_support (X : Set (RankOneFlat N)) :
    graphSupport G (graphicGroundOriginalLabel G '' X) =
      SimpleGraph.fromEdgeSet (graphicGroundSimpleLabel G '' X) := by
  unfold graphSupport
  congr 1
  ext q
  constructor
  · rintro ⟨e, ⟨A, hA, hAe⟩, heq⟩
    have hrep : graphicGroundRepresentative G A = e := Subtype.ext hAe
    exact ⟨A, hA, (graphicGroundRepresentative_ends G A).symm.trans
      ((congrArg (graphEdgeEnds G) hrep).trans heq)⟩
  · rintro ⟨A, hA, hAq⟩
    exact ⟨graphicGroundRepresentative G A, ⟨A, hA, rfl⟩,
      (graphicGroundRepresentative_ends G A).trans hAq⟩

end BooleanAntichainsKernel
