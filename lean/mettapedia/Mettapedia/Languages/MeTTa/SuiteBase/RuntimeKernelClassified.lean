import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import MeTTailCore

/-!
# Runtime-Kernel Classified Fragments

Internal classified-fragment layer for the MeTTa runtime-boundary package.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open MeTTailCore.MeTTaIL.EffectSafety

/-! ## 1. Effect-class bridge

Assigns a conservative `EffectClass` to each `RuntimeKernelClass` based on
the current proved MORK/MM2 seams:

- `ruleExec`: eval/evalc are pure structural rewrites
- `query`: match &self, get-atoms are read-only lookups
- `spaceEffect`: add-atom, remove-atom mutate workspace state
- `oracle`: grounded/FFI calls are side-effecting I/O
- `metaPhase`: meta-reflection is structural
-/
def RuntimeKernelClass.effectClass : RuntimeKernelClass → EffectClass
  | .ruleExec    => .pureStructural
  | .query       => .readOnlyLookup
  | .spaceEffect => .writesState
  | .oracle      => .oracleIO
  | .metaPhase   => .pureStructural

def RuntimeKernelTarget.effectClass (t : RuntimeKernelTarget) : EffectClass :=
  t.kernelClass.effectClass

end Mettapedia.Languages.MeTTa.ElaboratedCore

namespace Mettapedia.Languages.MeTTa.RuntimeKernel

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec
open MeTTailCore.MeTTaIL.EffectSafety

/-! ## 2. Classified fragment

Pairs a kernel class with its proved effect class, resource class, and backend
name. This is the object that ElaboratedCore can target through backend-neutral
classes without importing scheduler internals.
-/
structure ClassifiedFragment where
  kernelClass : RuntimeKernelClass
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
deriving Repr, DecidableEq

/-! ## 3. Current MORK/MM2-backed classified fragments -/

/-- PeTTa eval/evalc rewrite steps over the default atomspace. -/
def execFragment : ClassifiedFragment where
  kernelClass := .ruleExec
  effectClass := .pureStructural
  resourceClass := .defaultAtomSpace
  backendName := "MORK/MM2"

/-- match &self, get-atoms &self queries over the default atomspace. -/
def queryFragment : ClassifiedFragment where
  kernelClass := .query
  effectClass := .readOnlyLookup
  resourceClass := .defaultAtomSpace
  backendName := "MORK/MM2"

/-- add-atom, remove-atom mutations over the default atomspace. -/
def spaceEffectFragment : ClassifiedFragment where
  kernelClass := .spaceEffect
  effectClass := .writesState
  resourceClass := .defaultAtomSpace
  backendName := "MORK/MM2"

/-- Z3-backed oracle interactions over the solver resource. -/
def solverOracleFragment : ClassifiedFragment where
  kernelClass := .oracle
  effectClass := .oracleIO
  resourceClass := .solverResource
  backendName := "MORK/MM2"

/-- ACT-backed external lookups over the external resource. -/
def externalOracleFragment : ClassifiedFragment where
  kernelClass := .oracle
  effectClass := .oracleIO
  resourceClass := .externalResource
  backendName := "MORK/MM2"

end Mettapedia.Languages.MeTTa.RuntimeKernel
