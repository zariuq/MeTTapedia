import Mettapedia.Languages.MeTTa.RuntimeExec

/-!
# Elaborated MeTTa-Core Base

Common infrastructure for the elaborated MeTTa-Core layer.

This file contains only the neutral base notions shared by proof-facing and
runtime-facing elaborated fragments:

- region classification
- shared artifact carrier
- runtime lowering target
- overlap classification
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The first explicit region split for elaborated MeTTa-Core. -/
inductive ElaboratedRegion where
  | pureKernelRegion
  | runtimeExecRegion
  | oracleRegion
  | metaRegion
deriving DecidableEq, Repr

/-- Shared artifact substrate used by both proof and runtime views. -/
structure SharedArtifact where
  pattern : Pattern

/-- Backend-neutral runtime kernel classes for elaborated MeTTa-Core.

These are the semantic classes we currently want the runtime side to expose,
independently of any particular witness dialect.
-/
inductive RuntimeKernelClass where
  | ruleExec
  | query
  | spaceEffect
  | oracle
  | metaPhase
deriving DecidableEq, Repr

def RuntimeKernelClass.name : RuntimeKernelClass → String
  | .ruleExec => "rule-exec"
  | .query => "query"
  | .spaceEffect => "space-effect"
  | .oracle => "oracle"
  | .metaPhase => "meta"

/-- First neutral resource classification below the runtime kernel classes.

The default MeTTa runtime story is still "one atomspace", but this leaves room
for generalized resources such as solver handles or map-like stores without
redefining the kernel classes themselves.
-/
inductive RuntimeResourceClass where
  | defaultAtomSpace
  | namedAtomSpace
  | mapResource
  | queueResource
  | solverResource
  | externalResource
deriving DecidableEq, Repr

def RuntimeResourceClass.name : RuntimeResourceClass → String
  | .defaultAtomSpace => "default-atomspace"
  | .namedAtomSpace => "named-atomspace"
  | .mapResource => "map-resource"
  | .queueResource => "queue-resource"
  | .solverResource => "solver-resource"
  | .externalResource => "external-resource"

/-- Runtime-side lowering target. This is intentionally smaller than "all
runtime semantics": it only records the current theoremic seams. -/
inductive RuntimeLowering where
  | exec (surface : MeTTaRuntimeExecSurface)
  | query (surface : MeTTaRuntimeQuerySurface)
  | spaceEffect (surface : MeTTaRuntimeExecSurface)
  | auditOnly

def RuntimeLowering.backendName : RuntimeLowering → String
  | RuntimeLowering.exec surface => surface.backendName
  | RuntimeLowering.query surface => surface.backendName
  | RuntimeLowering.spaceEffect surface => surface.backendName
  | RuntimeLowering.auditOnly => "audit-only"

def RuntimeLowering.kernelClass : RuntimeLowering → RuntimeKernelClass
  | RuntimeLowering.exec _ => .ruleExec
  | RuntimeLowering.query _ => .query
  | RuntimeLowering.spaceEffect _ => .spaceEffect
  | RuntimeLowering.auditOnly => .metaPhase

/-- Neutral packaging of a runtime target below elaboration and above concrete
backend theorems. This is the object we want surface elaboration to classify
into, before dialect-specific details are considered.
-/
structure RuntimeKernelTarget where
  kernelClass : RuntimeKernelClass
  resourceClass : RuntimeResourceClass
  lowering : RuntimeLowering

def RuntimeKernelTarget.backendName (t : RuntimeKernelTarget) : String :=
  RuntimeLowering.backendName t.lowering

/-- Current overlap classification between the proof side and the runtime side.

`artifactOnly` is the present honest overlap for the currently certified proof
fragments: they share a MeTTa artifact, but they do not yet lower through the
direct `R_exec₀` source-rule bridge.

`directExec` is reserved for future fragments that genuinely elaborate to both a
trusted proof target and the current theoremic runtime execution seam. -/
inductive OverlapClass where
  | artifactOnly
  | directExec (surface : MeTTaRuntimeExecSurface)

def OverlapClass.name : OverlapClass → String
  | .artifactOnly => "artifact-only"
  | .directExec surface => surface.backendName

end Mettapedia.Languages.MeTTa.ElaboratedCore
