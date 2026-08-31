import BooleanAntichainsKernel.ProofEngineGraphInterface

namespace BooleanAntichainsKernel

universe u v

set_option linter.defProp false

noncomputable def proofEngineFullHeightEdge : ProofEngineFullHeightEdgeOutput.{u} :=
  ⟨graphClaimSource, proofEngineFullHeight⟩

noncomputable def proofEngineMaximumBijectionEdge :
    ProofEngineMaximumBijectionEdgeOutput.{u} :=
  ⟨graphClaimFullHeight, proofEngineMaximumBijection⟩

noncomputable def proofEngineWeightedEdge : ProofEngineWeightedEdgeOutput.{u} :=
  ⟨graphClaimMaximumBijection, proofEngineWeighted⟩

noncomputable def proofEngineIntervalEdge : ProofEngineIntervalEdgeOutput.{u} :=
  ⟨graphClaimMaximumBijection, proofEngineInterval⟩

noncomputable def proofEngineClosedFamiliesEdge :
    ProofEngineClosedFamiliesEdgeOutput.{u, v} :=
  ⟨graphClaimInterval, proofEngineClosedFamilies⟩

noncomputable def proofEngineSizeTwoEdge : ProofEngineSizeTwoEdgeOutput.{u} :=
  ⟨graphClaimSource, proofEngineSizeTwo⟩

noncomputable def proofEngineDistributiveEdge : ProofEngineDistributiveEdgeOutput.{u} :=
  ⟨graphClaimSource, proofEngineDistributive⟩

noncomputable def proofEngineSubspaceEdge : ProofEngineSubspaceEdgeOutput.{u} :=
  ⟨graphClaimSource, proofEngineSubspace⟩

noncomputable def proofEngineGlobalEdge : ProofEngineGlobalEdgeOutput.{u} :=
  ⟨graphClaimSource, proofEngineGlobal⟩

noncomputable def proofEngineUniformAllEdge : ProofEngineUniformAllEdgeOutput.{u} :=
  ⟨graphClaimGlobal, proofEngineUniformAll⟩

noncomputable def proofEngineProductEdge : ProofEngineProductEdgeOutput.{u} :=
  ⟨graphClaimGlobal, proofEngineProduct⟩

noncomputable def proofEngineProjectivePlaneEdge :
    ProofEngineProjectivePlaneEdgeOutput.{u, v} :=
  ⟨graphClaimGlobal, graphClaimSizeTwo, graphClaimMaximumBijection,
    proofEngineProjectivePlane⟩

noncomputable def proofEngineAssemblyEdge : ProofEngineAssemblyEdgeOutput.{u, v} :=
  ⟨graphClaimWeighted, graphClaimInterval, graphClaimClosedFamilies,
    graphClaimSizeTwo, graphClaimDistributive, graphClaimSubspace,
    graphClaimGlobal, graphClaimUniformAll, graphClaimProduct,
    graphClaimProjectivePlane, proofEngineTarget⟩

end BooleanAntichainsKernel
