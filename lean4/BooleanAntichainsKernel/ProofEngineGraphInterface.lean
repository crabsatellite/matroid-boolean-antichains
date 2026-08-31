import BooleanAntichainsKernel.ProofEngineInterface

/-! Typed claim inputs and exact edge bundles used only by Proof Engine probes. -/

namespace BooleanAntichainsKernel

universe u v

structure ProofEngineSourceInput : Prop where
  source_registered : True

axiom graphClaimSource : ProofEngineSourceInput
axiom graphClaimFullHeight : ProofEngineFullHeightOutput.{u}
axiom graphClaimMaximumBijection : ProofEngineMaximumBijectionOutput.{u}
axiom graphClaimWeighted : ProofEngineWeightedOutput.{u}
axiom graphClaimInterval : ProofEngineIntervalOutput.{u}
axiom graphClaimClosedFamilies : ProofEngineClosedFamiliesOutput.{u, v}
axiom graphClaimSizeTwo : ProofEngineSizeTwoOutput.{u}
axiom graphClaimDistributive : ProofEngineDistributiveOutput.{u}
axiom graphClaimSubspace : ProofEngineSubspaceOutput.{u}
axiom graphClaimGlobal : ProofEngineGlobalOutput.{u}
axiom graphClaimUniformAll : ProofEngineUniformAllOutput
axiom graphClaimProduct : ProofEngineProductOutput.{u}
axiom graphClaimProjectivePlane : ProofEngineProjectivePlaneOutput.{u, v}

structure ProofEngineFullHeightEdgeOutput : Prop where
  source : ProofEngineSourceInput
  result : ProofEngineFullHeightOutput.{u}

structure ProofEngineMaximumBijectionEdgeOutput : Prop where
  full_height : ProofEngineFullHeightOutput.{u}
  result : ProofEngineMaximumBijectionOutput.{u}

structure ProofEngineWeightedEdgeOutput : Prop where
  maximum_bijection : ProofEngineMaximumBijectionOutput.{u}
  result : ProofEngineWeightedOutput.{u}

structure ProofEngineIntervalEdgeOutput : Prop where
  maximum_bijection : ProofEngineMaximumBijectionOutput.{u}
  result : ProofEngineIntervalOutput.{u}

structure ProofEngineClosedFamiliesEdgeOutput : Prop where
  interval : ProofEngineIntervalOutput.{u}
  result : ProofEngineClosedFamiliesOutput.{u, v}

structure ProofEngineSizeTwoEdgeOutput : Prop where
  source : ProofEngineSourceInput
  result : ProofEngineSizeTwoOutput.{u}

structure ProofEngineDistributiveEdgeOutput : Prop where
  source : ProofEngineSourceInput
  result : ProofEngineDistributiveOutput.{u}

structure ProofEngineSubspaceEdgeOutput : Prop where
  source : ProofEngineSourceInput
  result : ProofEngineSubspaceOutput.{u}

structure ProofEngineGlobalEdgeOutput : Prop where
  source : ProofEngineSourceInput
  result : ProofEngineGlobalOutput.{u}

structure ProofEngineUniformAllEdgeOutput : Prop where
  global : ProofEngineGlobalOutput.{u}
  result : ProofEngineUniformAllOutput

structure ProofEngineProductEdgeOutput : Prop where
  global : ProofEngineGlobalOutput.{u}
  result : ProofEngineProductOutput.{u}

structure ProofEngineProjectivePlaneEdgeOutput : Prop where
  global : ProofEngineGlobalOutput.{u}
  size_two : ProofEngineSizeTwoOutput.{u}
  maximum_bijection : ProofEngineMaximumBijectionOutput.{u}
  result : ProofEngineProjectivePlaneOutput.{u, v}

structure ProofEngineAssemblyEdgeOutput : Prop where
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
  result : ProofEngineTargetOutput.{u, v}

end BooleanAntichainsKernel
