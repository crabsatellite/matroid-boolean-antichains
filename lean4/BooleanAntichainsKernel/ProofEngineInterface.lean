import BooleanAntichainsKernel.AtomicPaperClaimBindings

/-!
# Proof Engine semantic interfaces

These proposition-valued structures expose the exact machine outputs for the
thirteen claim-graph edges.  Every inhabitant below is constructed from the
premise-free publication or atomic roots; no graph claim is reintroduced as a
Lean axiom.
-/

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

universe u v

set_option linter.defProp false

structure ProofEngineFullHeightOutput : Prop where
  theorem_value : ∀ {L : Type u} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] [GradeMinOrder ℕ L]
    {r : ℕ} (C : BooleanAntichain r L) (_hr : grade ℕ (⊤ : L) = r),
    C.1.inf id = ⊥ ∧
    (∀ c : Set (antichainSpan C.1), IsMaxChain (· ≤ ·) c →
      IsMaxChain (· ≤ ·) (Subtype.val '' c : Set L)) ∧
    (∀ i : C.1, grade ℕ (antichainMeetFace C.1 {i}) = 1) ∧
    (∀ i : C.1, grade ℕ i.1 = r - 1)

noncomputable def proofEngineFullHeight : ProofEngineFullHeightOutput :=
  ⟨@manuscript_lem_full_height⟩

structure ProofEngineMaximumBijectionOutput : Prop where
  theorem_value : ∀ {α : Type u} [Fintype α] (M : Matroid α),
    (∀ C : MaximumBooleanAntichain M,
      (maximumAntichainToBasis C).1 = antichainAtoms C.1) ∧
    (∀ A : SimplifiedBasis M,
      (simplifiedBasisToAntichain A).1 = basisCoatoms A.1) ∧
    Function.LeftInverse (simplifiedBasisToAntichain (M := M)) maximumAntichainToBasis ∧
    Function.RightInverse (simplifiedBasisToAntichain (M := M)) maximumAntichainToBasis

noncomputable def proofEngineMaximumBijection : ProofEngineMaximumBijectionOutput :=
  ⟨@atomic_thm_main_bijection⟩

structure ProofEngineWeightedOutput : Prop where
  theorem_value : ∀ {α : Type u} [Fintype α] (M : Matroid α),
    matroidBasisPolynomial M =
      ∑ C : MaximumBooleanAntichain M,
        ∏ A ∈ spanAtomFinset C.1, ∑ e ∈ parallelClassElements A,
          (MvPolynomial.X e : MvPolynomial α ℤ)

noncomputable def proofEngineWeighted : ProofEngineWeightedOutput :=
  ⟨@weighted_basis_polynomial⟩

structure ProofEngineIntervalOutput : Prop where
  interval : ∀ {α : Type u} [Fintype α] (M : Matroid α)
    (X Y : MatroidFlat M) [Fact (X ≤ Y)],
    Function.Bijective (intervalAntichainEquivBasis X Y) ∧
    matroidBasisPolynomial (flatIntervalMinor X Y) =
      ∑ C : IntervalBooleanAntichain X Y,
        ∏ A ∈ spanAtomFinset C.1, ∑ e ∈ (A.1.1 \ X.1).toFinset,
          (MvPolynomial.X e : MvPolynomial α ℤ)
  rank_tight : ∀ {α : Type u} [Fintype α] (M : Matroid α) (k : ℕ),
    (∀ C : RankTightAntichain M k,
      (rankTightEquivBottomFibers C).1.1 = C.1.1.inf id) ∧
    (∀ (X : MatroidFlat M) (hX : HasCorank M k X),
      Function.Bijective (bottomFiberEquivActualContractionBases k X hX)) ∧
    Fintype.card (RankTightAntichain M k) =
      (∑ X ∈ Finset.univ.filter (fun X : MatroidFlat M ↦
        (MatroidFlat.rank X : ℤ) =
          (MatroidFlat.rank (⊤ : MatroidFlat M) : ℤ) - (k : ℤ)),
        Fintype.card (MatroidBases (simplificationOnFlats (M.contract X.1)))) ∧
    (MatroidFlat.rank (⊤ : MatroidFlat M) < k →
      Fintype.card (RankTightAntichain M k) = 0)

noncomputable def proofEngineInterval : ProofEngineIntervalOutput :=
  ⟨@manuscript_thm_interval, @manuscript_cor_rank_tight⟩

structure ProofEngineClosedFamiliesOutput : Prop where
  boolean_lattice : ∀ n k : ℕ,
    Fintype.card (BooleanLatticeRankTightAntichain (Fin n) k) = n.choose k ∧
    Fintype.card (BooleanAntichain k (Finset (Fin n))) =
      Nat.stirlingSecond (n + 1) (k + 1) ∧
    Fintype.card (BooleanLatticeNonRankTightAntichain (Fin n) k) =
      Nat.stirlingSecond (n + 1) (k + 1) - n.choose k
  partition_lattice : ∀ n : ℕ,
    (∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
      Fintype.card (PartitionRankTightAntichain (Fin n) k) =
        Nat.stirlingSecond n (k + 1) * (k + 1) ^ (k - 1)) ∧
    (2 ≤ n →
      Fintype.card
        (BooleanAntichain (n - 1) (Finpartition (Finset.univ : Finset (Fin n)))) =
          n ^ (n - 2))
  uniform_tight : ∀ n r : ℕ, 2 ≤ r → r ≤ n →
    Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) 0) = 1 ∧
    Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) 1) =
      n.choose (r - 1) ∧
    (∀ k : ℕ, 2 ≤ k → k ≤ r →
      Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) k) =
        n.choose r * r.choose k) ∧
    (∀ k : ℕ, r < k →
      Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) k) = 0)
  graphic : ∀ {α : Type u} {β : Type v} (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet],
    Function.Bijective (graphicMaximumAntichainEquivForests G) ∧
    (∀ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
        (MatroidFlat (cycleMatroid G)),
      C.1.card = G.vertexSet.ncard - graphConnectedComponentCount G) ∧
    (∀ hs : GraphIsSimple G,
      Function.Bijective (graphicSimpleMaximumAntichainEquivForests G hs)) ∧
    (∀ (hs : GraphIsSimple G) (hc : GraphIsConnected G),
      Function.Bijective (graphicConnectedMaximumAntichainEquivTrees G hs hc))
  projective_geometry : ∀ (K : Type u) [Field K] [Fintype K]
    (r : ℕ), 1 ≤ r →
    (Fintype.card
      (BooleanAntichain r (Projectivization.Subspace K (Fin r → K))) : ℚ) =
      (1 / (r.factorial : ℚ)) * ∏ i : Fin r,
        (((Fintype.card K : ℚ) ^ r - (Fintype.card K : ℚ) ^ i.1) /
          ((Fintype.card K : ℚ) - 1))

noncomputable def proofEngineClosedFamilies : ProofEngineClosedFamiliesOutput := by
  refine ⟨@manuscript_cor_boolean_lattice, manuscript_cor_partition_lattice,
    manuscript_cor_uniform_tight, ?_, ?_⟩
  · intro α β G _ _
    exact ⟨graphicMaximumAntichainEquivForests_bijective G,
      graphMaximumAntichain_card G,
      fun hs ↦ (graphicSimpleMaximumAntichainEquivForests G hs).bijective,
      fun hs hc ↦ (graphicConnectedMaximumAntichainEquivTrees G hs hc).bijective⟩
  · intro K _ _ r hr
    exact (manuscript_eq_projective_count K r hr).2.2.2.2

structure ProofEngineSizeTwoOutput : Prop where
  finite_lattice : ∀ {L : Type u} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] [DecidableLE L] [DecidableLT L],
    (∀ F G : L,
      IsBooleanTuple (pairTuple F G) ↔ F ≠ ⊤ ∧ G ≠ ⊤ ∧ F ⊔ G = ⊤) ∧
    (Fintype.card (BooleanAntichain 2 L) : ℤ) =
      (mobiusPairSum (L := L) - 2 * (Fintype.card L : ℤ) + 1) / 2
  partition_lattice :
    (∀ n : ℕ, 0 < n →
      (Fintype.card
        (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) : ℚ) =
        (1 / 2 : ℚ) * ((n.factorial : ℚ) *
          PowerSeries.coeff n bellSquareLogSeries - 2 * (Nat.bell n : ℚ) + 1)) ∧
    (∀ n : ℕ, (n.factorial : ℚ) * PowerSeries.coeff n bellSquareLogSeries =
      partitionBellSquareMobiusSumQ n) ∧
    List.ofFn (fun i : Fin 7 ↦ Fintype.card
      (BooleanAntichain 2
        (Finpartition (Finset.univ : Finset (Fin (i.1 + 1)))))) =
      [0, 0, 3, 45, 620, 9750, 183680]

noncomputable def proofEngineSizeTwo : ProofEngineSizeTwoOutput :=
  ⟨@manuscript_thm_size_two, manuscript_cor_partition_pairs⟩

structure ProofEngineDistributiveOutput : Prop where
  theorem_value : ∀ (P : Type u) [PartialOrder P] [Fintype P],
    (∀ k : ℕ, Function.Bijective
      (fun C : BooleanAntichain k (LowerSet P) ↦
        (distributiveAntichainEquivDisjointFilters C : DisjointFilterFamily k P))) ∧
    (∀ (k : ℕ) (C : BooleanAntichain k (LowerSet P)),
      (distributiveAntichainEquivDisjointFilters C).1 = lowerFinsetToUpperFinset C.1) ∧
    booleanAntichainPolynomial (LowerSet P) =
      graphIndependencePolynomial (filterIntersectionGraph P)

noncomputable def proofEngineDistributive : ProofEngineDistributiveOutput :=
  ⟨manuscript_thm_distributive⟩

structure ProofEngineSubspaceOutput : Prop where
  correspondence : ∀ (K : Type u) [Field K] [Fintype K] (n k : ℕ),
    Function.Bijective
      (subspaceUnorderedSigmaEquiv (R := K) (V := Fin n → K) k).symm ∧
    (∀ C : BooleanAntichain k (Submodule K (Fin n → K)),
      ((subspaceUnorderedSigmaEquiv k).symm C).1 = C.1.inf id ∧
      ((subspaceUnorderedSigmaEquiv k).symm C).2.1 =
        (antichainAtoms C.1).image (fun A ↦ A.map (C.1.inf id).mkQ)) ∧
    (∀ (X : Submodule K (Fin n → K))
      (D : UnorderedInternalDecomposition K ((Fin n → K) ⧸ X) k),
      k ≤ Module.finrank K ((Fin n → K) ⧸ X) ∧
      Module.finrank K ((Fin n → K) ⧸ X) ≤ n ∧
      (subspaceUnorderedSigmaEquiv k ⟨X, D⟩).1 =
        D.1.image (fun U ↦ ((D.1.erase U).sup id).comap X.mkQ))
  direct_sum_count : ∀ (K : Type u) [Field K] [Fintype K],
    (∀ d : ℕ, generalLinearCard K d =
      ∏ i : Fin d, ((Fintype.card K) ^ d - (Fintype.card K) ^ i.1)) ∧
    generalLinearCard K 0 = 1 ∧
    (∀ d k : ℕ, 1 ≤ k → k ≤ d →
      (Fintype.card (UnorderedInternalDecomposition K (Fin d → K) k) : ℚ) =
        (1 / (k.factorial : ℚ)) *
          ∑ p : PositiveDimensionProfile d k,
            (generalLinearCard K d : ℚ) /
              ∏ i, (generalLinearCard K (p.1 i) : ℚ)) ∧
    (∀ n k : ℕ, 1 ≤ k →
      (Fintype.card (BooleanAntichain k (Submodule K (Fin n → K))) : ℚ) =
        ∑ X : Submodule K (Fin n → K),
          directSumProfileCount K (Module.finrank K ((Fin n → K) ⧸ X)) k)
  all_size : ∀ (K : Type u) [Field K] [Fintype K] (n k : ℕ), 1 ≤ k →
    (Fintype.card (BooleanAntichain k (Submodule K (Fin n → K))) : ℚ) =
      ∑ d ∈ Finset.Icc k n,
        gaussianCoefficient (Fintype.card K) n d * directSumProfileCount K d k
  zero_layer : ∀ (K : Type u) [Field K] [Fintype K] (n : ℕ),
    Fintype.card (BooleanAntichain 0 (Submodule K (Fin n → K))) = 1

noncomputable def proofEngineSubspace : ProofEngineSubspaceOutput :=
  ⟨@atomic_thm_subspace_correspondence,
    @manuscript_thm_subspace_direct_sum_count,
    @standardSubspace_all_size_formula,
    @atomic_thm_subspace_zero_layer⟩

structure ProofEngineGlobalOutput : Prop where
  criterion : ∀ {L : Type u} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] {k : ℕ} (H : Fin k → L),
    IsBooleanTuple H ↔ ReconstructedAtomsRise H ∧ ReconstructionGapsVanish H
  enumerator : ∀ {L : Type u} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] {k : ℕ},
    Fintype.card (BooleanAntichain k L) =
      (∑ H : Fin k → L, globalCriterionIndicator H) / k.factorial
  boundaries : ∀ {L : Type u} [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] (k : ℕ),
    Fintype.card (BooleanAntichain 0 L) = 1 ∧
    (latticeHeight (⊤ : L) < k → Fintype.card (BooleanAntichain k L) = 0)
  rank_profile : ∀ {α : Type u} [Fintype α] (M : Matroid α)
    {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)),
    antichainRankProfile C ∅ = 0 ∧ StrictMono (antichainRankProfile C) ∧
    (∀ S T : Finset C.1,
      antichainRankProfile C (S ∩ T) + antichainRankProfile C (S ∪ T) ≤
        antichainRankProfile C S + antichainRankProfile C T) ∧
    (IsRankTight C ↔ ∀ S : Finset C.1, antichainRankProfile C S = S.card)

noncomputable def proofEngineGlobal : ProofEngineGlobalOutput :=
  ⟨@manuscript_thm_global_gap_criterion,
    @manuscript_thm_global_gap_enumerator,
    @atomic_thm_global_boundaries,
    @manuscript_cor_rank_profile⟩

structure ProofEngineUniformAllOutput : Prop where
  theorem_value :
    (∀ r n : ℕ, 1 ≤ r → r ≤ n →
      Fintype.card
        (BooleanAntichain 0 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) = 1 ∧
      Fintype.card
        (BooleanAntichain 1 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
          (∑ b ∈ Finset.range r, n.choose b) ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ r →
        (Fintype.card
          (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) : ℚ) =
          (1 / (k.factorial : ℚ)) *
            ∑ b ∈ Finset.range r, (n.choose b : ℚ) *
              ∑ p : UniformAdmissibleProfile n r k b,
                ((n - b).factorial : ℚ) /
                  (((n - b - ∑ i, p.1 i).factorial : ℚ) *
                    ∏ i, ((p.1 i).factorial : ℚ))) ∧
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1
        (MatroidFlat (uniformOn (Set.univ : Set (Fin 4)) 3)))) = [1, 11, 27, 4] ∧
    List.ofFn (fun k : Fin 5 ↦ Fintype.card
      (BooleanAntichain k.1
        (MatroidFlat (uniformOn (Set.univ : Set (Fin 5)) 4)))) = [1, 26, 150, 50, 5]

noncomputable def proofEngineUniformAll : ProofEngineUniformAllOutput :=
  ⟨manuscript_thm_uniform_all⟩

structure ProofEngineProductOutput : Prop where
  theorem_value : ∀ {L K : Type u}
    [Fintype L] [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
    [Fintype K] [DecidableEq K] [Lattice K] [OrderBot K] [OrderTop K] (k : ℕ),
    etaCount k (L × K) = etaCount k L * etaCount k K ∧
    (Fintype.card (BooleanAntichain k (L × K)) : ℚ) =
      ∑ a ∈ Finset.range (k + 1),
        ∑ b ∈ (Finset.range (k + 1)).filter (fun b ↦ k ≤ a + b),
          ((a.factorial : ℚ) * (b.factorial : ℚ) /
            ((k - a).factorial * (k - b).factorial * (a + b - k).factorial : ℚ)) *
            (Fintype.card (BooleanAntichain a L) : ℚ) *
            (Fintype.card (BooleanAntichain b K) : ℚ)

noncomputable def proofEngineProduct : ProofEngineProductOutput :=
  ⟨@manuscript_thm_product⟩

structure ProofEngineProjectivePlaneOutput : Prop where
  theorem_value : ∀ (P : Type u) (L : Type v) [Membership P L]
    [Configuration.ProjectivePlane P L] [Fintype P] [Fintype L],
    let q := Configuration.ProjectivePlane.order P L
    let N := q ^ 2 + q + 1
    (Fintype.card P = N ∧ Fintype.card L = N) ∧
    (∀ F : Set P, (incidencePlaneMatroid P L).IsFlat F ↔
      F = ∅ ∨ (∃ p : P, F = {p}) ∨ (∃ l : L, F = planeLineSet l) ∨ F = Set.univ) ∧
    matroidRank (incidencePlaneMatroid P L) (incidencePlaneMatroid P L).E = 3 ∧
    (∀ B : Set P, (incidencePlaneMatroid P L).IsBase B ↔
      B.ncard = 3 ∧ ¬ PlaneCollinear L B) ∧
    (∀ (p : P) (l : L),
      incidencePlanePointFlat (L := L) p ≤ incidencePlaneLineFlat (P := P) l ↔ p ∈ l) ∧
    Function.Bijective (planeJoinPairEquiv (P := P) (L := L)) ∧
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (MatroidFlat (incidencePlaneMatroid P L)))) =
        [1, 2 * N + 1, N.choose 2 + N * q ^ 2, N.choose 3 - N * (q + 1).choose 3] ∧
    (∀ k : ℕ, 3 < k →
      Fintype.card (BooleanAntichain k (MatroidFlat (incidencePlaneMatroid P L))) = 0)

noncomputable def proofEngineProjectivePlane : ProofEngineProjectivePlaneOutput :=
  ⟨@manuscript_eq_projective_plane_all⟩

structure ProofEngineTargetOutput : Prop where
  full_height : ProofEngineFullHeightOutput.{u}
  maximum_bijection : ProofEngineMaximumBijectionOutput.{u}
  weighted : ProofEngineWeightedOutput.{u}
  interval : ProofEngineIntervalOutput.{u}
  closed_families : ProofEngineClosedFamiliesOutput.{u, v}
  size_two : ProofEngineSizeTwoOutput.{u}
  distributive : ProofEngineDistributiveOutput.{u}
  subspace : ProofEngineSubspaceOutput.{u}
  global : ProofEngineGlobalOutput.{u}
  uniform_all : ProofEngineUniformAllOutput
  product : ProofEngineProductOutput.{u}
  projective_plane : ProofEngineProjectivePlaneOutput.{u, v}

noncomputable def proofEngineTarget : ProofEngineTargetOutput.{u, v} :=
  ⟨proofEngineFullHeight, proofEngineMaximumBijection, proofEngineWeighted,
    proofEngineInterval, proofEngineClosedFamilies, proofEngineSizeTwo,
    proofEngineDistributive, proofEngineSubspace, proofEngineGlobal,
    proofEngineUniformAll, proofEngineProduct, proofEngineProjectivePlane⟩

end BooleanAntichainsKernel
