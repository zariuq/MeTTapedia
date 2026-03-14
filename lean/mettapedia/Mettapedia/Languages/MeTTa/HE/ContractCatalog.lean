import Mettapedia.Languages.MeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.HE.LookupPlan

/-!
# HE Contract Catalog

Semantic catalog for the HE execution-contract surface.
-/

namespace Mettapedia.Languages.MeTTa.HE.ExecutionContract

open Mettapedia.Languages.MeTTa.ExecutionContract
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety

private def heEqQueryTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_scalar"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
  , "Mettapedia.Languages.MeTTa.HE.LookupPlan.heEqQueryFamily_negatesHas_notResult"
  ]

private def heControlKernelTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
  ]

-- Planned conformance theorems (not yet proven in Conformance.lean).
-- These names document which witnesses are needed; the theorems themselves
-- will be added once the switch/assert/case/unify EvalSpec constructors
-- have full conformance witnesses.
private def heSwitchControlTheoremRefs : List String :=
  heControlKernelTheoremRefs ++
  [ "Mettapedia.Languages.MeTTa.HE.Conformance.extension_switch_minimal_first_match"       -- planned
  , "Mettapedia.Languages.MeTTa.HE.Conformance.extension_switch_no_match_empty"             -- planned
  , "Mettapedia.Languages.MeTTa.HE.Conformance.extension_switch_internal_first_match"       -- planned
  ]

private def heAssertControlTheoremRefs : List String :=
  heControlKernelTheoremRefs ++
  [ "Mettapedia.Languages.MeTTa.HE.Conformance.extension_assert_true"                      -- planned
  , "Mettapedia.Languages.MeTTa.HE.Conformance.extension_assert_false_error"                -- planned
  ]

private def heCaseControlTheoremRefs : List String :=
  heControlKernelTheoremRefs ++
  [ "Mettapedia.Languages.MeTTa.HE.Conformance.extension_case_first_match"                 -- planned
  , "Mettapedia.Languages.MeTTa.HE.Conformance.extension_switch_minimal_first_match"        -- planned
  ]

private def heUnifyControlTheoremRefs : List String :=
  heControlKernelTheoremRefs ++
  [ "Mettapedia.Languages.MeTTa.HE.Conformance.minimal_unify_match_then_branch"             -- planned
  , "Mettapedia.Languages.MeTTa.HE.Conformance.minimal_unify_match_substitutes_success"     -- planned
  , "Mettapedia.Languages.MeTTa.HE.Conformance.minimal_unify_no_match_else_branch"          -- planned
  ]

/-- First HE execution-contract entry: the derived `eqQuery` lookup family. -/
def heEqQueryLookupContract : LookupQueryContract where
  head := "eqQuery"
  surfaceHead := none
  arity := 2
  lookupFamily := Mettapedia.Languages.MeTTa.HE.LookupPlan.heEqQueryFamily
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.scalar, .outcomeSet]
  sourceRuleCompilable := false
  queryCompilable := true
  spaceEffectCompilable := false
  builtinDemand := none
  theoremRefs := heEqQueryTheoremRefs

def heEqQueryEntry : ExecutionContractEntry :=
  .lookupQuery heEqQueryLookupContract

/--
HE `mettaCall` control forms are explicit control lanes, not lookup or
grounded-builtin lanes.

Why control:
- `switch`, `assert`, and `case` sequence nested evaluation and branch/continuation
  structure in `Interpreter.lean` / `HELanguageDef.lean`
- these forms are part of the live HE runtime surface already, so exporting
  them as control contracts lets later Rust work consume the same authority
  instead of rediscovering their control semantics ad hoc

Why conservatively `writes_state`:
- like the existing PeTTa control contracts, these forms may sequence nested
  runtime actions and should not pretend to be memo-safe or pure at the
  execution-lane boundary
- this is a conservative runtime contract, not a claim that the control forms
  themselves mutate the atomspace directly in every execution
-/
def heSwitchContract : ControlBuiltinContract where
  head := "switch"
  minArity := 2
  maxArity := some 2
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := heSwitchControlTheoremRefs

def heSwitchEntry : ExecutionContractEntry :=
  .controlBuiltin heSwitchContract

def heSwitchMinimalContract : ControlBuiltinContract where
  head := "switch-minimal"
  minArity := 2
  maxArity := some 2
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := heSwitchControlTheoremRefs

def heSwitchMinimalEntry : ExecutionContractEntry :=
  .controlBuiltin heSwitchMinimalContract

def heSwitchInternalContract : ControlBuiltinContract where
  head := "switch-internal"
  minArity := 2
  maxArity := some 2
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := heSwitchControlTheoremRefs

def heSwitchInternalEntry : ExecutionContractEntry :=
  .controlBuiltin heSwitchInternalContract

def heAssertContract : ControlBuiltinContract where
  head := "assert"
  minArity := 1
  maxArity := some 1
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := heAssertControlTheoremRefs

def heAssertEntry : ExecutionContractEntry :=
  .controlBuiltin heAssertContract

def heCaseContract : ControlBuiltinContract where
  head := "case"
  minArity := 2
  maxArity := some 2
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := heCaseControlTheoremRefs

def heCaseEntry : ExecutionContractEntry :=
  .controlBuiltin heCaseContract

/--
HE `unify` is a minimal-instruction control lane.

Why control:
- `MC_Unify_Match` / `MC_Unify_NoMatch` branch on a local structural match and
  then continue by evaluating either the substituted success body or the failure
  body
- this is closer to explicit branch/control behavior than to a lookup family or
  grounded builtin

Why conservatively `writes_state`:
- the shared control-builtin schema and Rust validator currently require HE
  control lanes to use the same conservative effect envelope as the existing
  `switch` / `assert` / `case` batch
- this is a runtime-boundary contract, not a claim that `unify` mutates the
  atomspace in every execution -/
def heUnifyContract : ControlBuiltinContract where
  head := "unify"
  minArity := 4
  maxArity := some 4
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := heUnifyControlTheoremRefs

def heUnifyEntry : ExecutionContractEntry :=
  .controlBuiltin heUnifyContract

def heControlEntries : List ExecutionContractEntry :=
  [ heSwitchEntry
  , heSwitchMinimalEntry
  , heSwitchInternalEntry
  , heAssertEntry
  , heCaseEntry
  , heUnifyEntry
  ]

/--
Current honest HE execution-contract surface.

This intentionally exports only the lanes whose semantic ownership is already
clear in the HE formalization:
- `eqQuery` as the derived lookup family
- `switch` / `switch-minimal` / `switch-internal` / `assert` / `case` as
  explicit `mettaCall` control rules

It intentionally does **not** inherit the shared `coreIntrinsicEntries`
wholesale.

Why not:
- `if` is classified in `OpProfile.lean` as `preludeEqAndType`, not as a live
  HE intrinsic lane
- arithmetic/comparison heads currently live under `MC_Grounded`, which needs
  an HE-specific grounded contract batch rather than pretending the shared MM2
  intrinsic catalog already applies
- `match` / `unify` / `superpose` / `collapse` are minimal-instruction lanes,
  not intrinsic builtins; this batch now includes `unify` because its branch
  semantics are already explicit and conformance-tested

Positive example:
- later Rust work can consume this catalog without rediscovering HE's control
  semantics ad hoc

Negative example:
- the artifact should not overclaim that HE already exports the entire shared
  intrinsic catalog just because those rows exist for other dialects. -/
def heExecutionEntries : List ExecutionContractEntry :=
  [heEqQueryEntry] ++ heControlEntries

def heExecutionContractArtifact : ExecutionContractArtifact where
  dialect := "he"
  entries := heExecutionEntries

theorem heEqQuery_effectClass :
    heEqQueryLookupContract.effectClass = .readOnlyLookup := rfl

theorem heEqQuery_resource :
    heEqQueryLookupContract.resourceClass = .defaultAtomSpace := rfl

theorem heEqQuery_backend :
    heEqQueryLookupContract.backendName = "MORK/MM2" := rfl

theorem heEqQuery_noFalseNegatives :
    heEqQueryLookupContract.noFalseNegatives = true := rfl

theorem heEqQuery_exactResult :
    heEqQueryLookupContract.exactResult = false := rfl

theorem heEqQuery_stratifiedNegationSafe :
    heEqQueryLookupContract.stratifiedNegationSafe = true := rfl

theorem heEqQuery_scalarMemo :
    heEqQueryLookupContract.effectClass.supportsMemoShape .scalar = true := by
  simpa [heEqQueryLookupContract] using query_memo_scalar

theorem heEqQuery_outcomeSetMemo :
    heEqQueryLookupContract.effectClass.supportsMemoShape .outcomeSet = true := by
  simpa [heEqQueryLookupContract] using query_memo_outcomeSet

theorem heSwitch_control_effectClass :
    heSwitchContract.effectClass = .writesState := rfl

theorem heAssert_control_effectClass :
    heAssertContract.effectClass = .writesState := rfl

theorem heCase_control_effectClass :
    heCaseContract.effectClass = .writesState := rfl

theorem heUnify_control_effectClass :
    heUnifyContract.effectClass = .writesState := rfl

end Mettapedia.Languages.MeTTa.HE.ExecutionContract
