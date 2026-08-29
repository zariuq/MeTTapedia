import Mettapedia.Languages.MeTTa.DialectProfile
import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.HE.HEPremises
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness

/-!
# MeTTa Runtime Specification Profile

First draft of an auditable `R_spec` layer for the MeTTa family.

This file is intentionally small.  It does not define execution semantics and
it does not try to identify all dialects with one shared core machine.  It only
records the runtime-facing semantic features that should be obvious to reviewers
inspecting `HE`, `PeTTa`, `Pure`, and the legacy state-machine slice.

The intended reading is:

- `R_exec` may be implemented by an MM2/MORK-like substrate
- `R_spec` remains recognizably MeTTa
- IntrinsicPure `A/B/C1` stays separate and untouched
- future maps `HE -> R_spec`, `PeTTa -> R_spec`, and then `R_spec -> C*`
  should target this profile rather than redefining the kernel
-/

namespace Mettapedia.Languages.MeTTa.RuntimeSpec

open Mettapedia.Languages.MeTTa.DialectProfile
open Mettapedia.Languages.MeTTa.CoreProfile
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Whether variable bindings are an explicit semantic object. -/
inductive BindingsMode where
  | none
  | explicit
  deriving DecidableEq, Repr

/-- Whether branching is represented explicitly in the semantic interface. -/
inductive BranchingMode where
  | single
  | explicitAlternatives
  deriving DecidableEq, Repr

/-- How the runtime interface exposes the space/context side of MeTTa execution. -/
inductive ContextMode where
  | none
  | explicitSpace
  | explicitStateAndSpace
  deriving DecidableEq, Repr

/-- How the runtime interface exposes native/grounded execution hooks. -/
inductive NativeHookMode where
  | none
  | groundedDispatch
  | oracleLayer
  deriving DecidableEq, Repr

/-- Whether collapse/superpose-style collection control is explicit. -/
inductive CollectionControlMode where
  | none
  | collapseSuperpose
  deriving DecidableEq, Repr

/-- Minimal first-draft runtime spec for a MeTTa dialect.

The carrier names are intentionally strings in the first draft.  This keeps the
profile auditable without prematurely fixing the exact theorem boundary between
runtime relations living in different files.
-/
structure MeTTaRuntimeSpec where
  dialect : MeTTaDialectProfile
  stateCarrier : String
  resultCarrier : String
  bindingsMode : BindingsMode
  branchingMode : BranchingMode
  contextMode : ContextMode
  nativeHookMode : NativeHookMode
  collectionControl : CollectionControlMode

/-- Lightweight audit predicate: the named sort appears in the chosen `LanguageDef`. -/
def languageHasTypeNamed (lang : LanguageDef) (ty : String) : Prop :=
  LanguageDef.hasTypeNamed lang ty

instance languageHasTypeNamedDecidable
    (lang : LanguageDef) (ty : String) : Decidable (languageHasTypeNamed lang ty) := by
  unfold languageHasTypeNamed
  infer_instance

/-- Lightweight audit predicate: the premise program exports a relation of this name. -/
def premiseProgramHasRelationNamed
    (prog : Mettapedia.OSLF.MeTTaIL.PremiseDatalog.PremiseProgram)
    (relName : String) : Prop :=
  relName ∈
    (Mettapedia.OSLF.MeTTaIL.PremiseDatalog.PremiseProgram.relations prog).map
      Mettapedia.OSLF.MeTTaIL.PremiseDatalog.RelDecl.name

instance premiseProgramHasRelationNamedDecidable
    (prog : Mettapedia.OSLF.MeTTaIL.PremiseDatalog.PremiseProgram)
    (relName : String) : Decidable (premiseProgramHasRelationNamed prog relName) := by
  unfold premiseProgramHasRelationNamed
  infer_instance

/-- Runtime-facing kernel profile.  Pure is intentionally degenerate here:
there is no ambient atomspace or bindings store. -/
def pureRuntimeSpec : MeTTaRuntimeSpec where
  dialect := pureDialectProfile
  stateCarrier := "PureTm 0"
  resultCarrier := "PureTm 0"
  bindingsMode := .none
  branchingMode := .single
  contextMode := .none
  nativeHookMode := .none
  collectionControl := .none

/-- Runtime-facing HE profile.

This records the recognizably MeTTa runtime features already explicit in the HE
formalization: `State`, `ResultSet`, explicit bindings, explicit space, and
grounded dispatch.
-/
def heRuntimeSpec : MeTTaRuntimeSpec where
  dialect := heDialectProfile
  stateCarrier := "State"
  resultCarrier := "ResultSet"
  bindingsMode := .explicit
  branchingMode := .explicitAlternatives
  contextMode := .explicitStateAndSpace
  nativeHookMode := .groundedDispatch
  collectionControl := .collapseSuperpose

/-- Runtime-facing PeTTa profile.

PeTTa's semantic carrier is the program/space object `PeTTaSpace`.  The richest
currently formalized MeTTa-facing result carrier is `EvalResult` from
`MeTTaEval.lean`, which already exposes values paired with bindings.  Grounded
oracles live in a separate extension layer and are therefore not treated as part
of the base PeTTa runtime spec in this first draft.
-/
def pettaRuntimeSpec : MeTTaRuntimeSpec where
  dialect := pettaDialectProfile
  stateCarrier := "PeTTaSpace"
  resultCarrier := "EvalResult"
  bindingsMode := .explicit
  branchingMode := .explicitAlternatives
  contextMode := .explicitSpace
  nativeHookMode := .none
  collectionControl := .collapseSuperpose

/-- Runtime-facing legacy full/core profile. -/
def fullLegacyRuntimeSpec : MeTTaRuntimeSpec where
  dialect := fullLegacyDialectProfile
  stateCarrier := "State"
  resultCarrier := "Atom"
  bindingsMode := .none
  branchingMode := .single
  contextMode := .explicitStateAndSpace
  nativeHookMode := .groundedDispatch
  collectionControl := .none

/-- First-draft runtime inventory. -/
def runtimeSpecs : List MeTTaRuntimeSpec :=
  [pureRuntimeSpec, heRuntimeSpec, pettaRuntimeSpec, fullLegacyRuntimeSpec]

/-- Lookup by dialect name. -/
def findRuntimeSpec (name : String) : Option MeTTaRuntimeSpec :=
  runtimeSpecs.find? (fun s => s.dialect.name == name)

@[simp] theorem pureRuntimeSpec_dialect :
    pureRuntimeSpec.dialect = pureDialectProfile := rfl

@[simp] theorem pureRuntimeSpec_bindings :
    pureRuntimeSpec.bindingsMode = .none := rfl

@[simp] theorem heRuntimeSpec_dialect :
    heRuntimeSpec.dialect = heDialectProfile := rfl

@[simp] theorem heRuntimeSpec_stateCarrier :
    heRuntimeSpec.stateCarrier = "State" := rfl

@[simp] theorem heRuntimeSpec_resultCarrier :
    heRuntimeSpec.resultCarrier = "ResultSet" := rfl

@[simp] theorem heRuntimeSpec_native :
    heRuntimeSpec.nativeHookMode = .groundedDispatch := rfl

@[simp] theorem pettaRuntimeSpec_dialect :
    pettaRuntimeSpec.dialect = pettaDialectProfile := rfl

@[simp] theorem pettaRuntimeSpec_stateCarrier :
    pettaRuntimeSpec.stateCarrier = "PeTTaSpace" := rfl

@[simp] theorem pettaRuntimeSpec_resultCarrier :
    pettaRuntimeSpec.resultCarrier = "EvalResult" := rfl

@[simp] theorem pettaRuntimeSpec_native :
    pettaRuntimeSpec.nativeHookMode = .none := rfl

@[simp] theorem fullLegacyRuntimeSpec_dialect :
    fullLegacyRuntimeSpec.dialect = fullLegacyDialectProfile := rfl

/-! ## HE Facts -/

/-- `heRuntimeSpec` is anchored in the fixed HE core profile and its exported
language/premise objects. -/
theorem heRuntimeSpec_profile_fact :
    heRuntimeSpec.dialect.referenceCoreProfile? = some heProfile ∧
    heProfile.lang = Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE ∧
    heProfile.premises = Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises := by
  simp [heRuntimeSpec, heDialectProfile, heProfile]

/-- The HE runtime profile explicitly exposes both `State` and `Space` in the
exported language definition. -/
theorem heRuntimeSpec_state_context_fact :
    heRuntimeSpec.contextMode = .explicitStateAndSpace ∧
    languageHasTypeNamed Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE "State" ∧
    languageHasTypeNamed Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE "Space" := by
  native_decide

/-- HE's result carrier is concretely a list of `(Atom × Bindings)` pairs, so
bindings and explicit alternatives are part of the formal semantic interface. -/
theorem heRuntimeSpec_result_bindings_fact :
    heRuntimeSpec.bindingsMode = .explicit ∧
    heRuntimeSpec.branchingMode = .explicitAlternatives ∧
    Mettapedia.Languages.MeTTa.HE.ResultSet =
      List (Mettapedia.Languages.MeTTa.HE.ResultPair) := by
  simp [heRuntimeSpec, Mettapedia.Languages.MeTTa.HE.ResultSet]

/-- HE's native hook classification is justified by the exported
`groundedCallResult` premise relation and the interpreter's explicit
`GroundedDispatch` parameter. -/
theorem heRuntimeSpec_native_hook_fact :
    heRuntimeSpec.nativeHookMode = .groundedDispatch ∧
    premiseProgramHasRelationNamed Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises
      "groundedCallResult" := by
  decide

/-- HE exposes `superpose`/`collapse` style control through explicit premise
relations rather than hiding them in an opaque backend. -/
theorem heRuntimeSpec_collection_control_fact :
    heRuntimeSpec.collectionControl = .collapseSuperpose ∧
    premiseProgramHasRelationNamed Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises
      "parseSuperpose" ∧
    premiseProgramHasRelationNamed Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises
      "isSuperpose_empty" ∧
    premiseProgramHasRelationNamed Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises
      "collapseBind" := by
  decide

/-! ## PeTTa Facts -/

/-- `pettaRuntimeSpec` is anchored in the fixed PeTTa dialect profile, while the
lowered `LanguageDef` artifact source remains program-parametric. -/
theorem pettaRuntimeSpec_dialect_fact :
    pettaRuntimeSpec.dialect = pettaDialectProfile ∧
    pettaRuntimeSpec.dialect.artifactBoundary = .programParametric ∧
    pettaRuntimeSpec.dialect.artifactLanguageSource? = some "pettaSpaceToLangDef" := by
  simp [pettaRuntimeSpec, pettaDialectProfile]

/-- The PeTTa runtime state is explicitly a `PeTTaSpace`, and every concrete
space lowers to a `LanguageDef` named `PeTTaSpace`. -/
theorem pettaRuntimeSpec_state_artifact_fact :
    pettaRuntimeSpec.stateCarrier = "PeTTaSpace" ∧
    ∀ s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace,
      (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s).name = "PeTTaSpace" := by
  refine ⟨rfl, ?_⟩
  intro s
  rfl

/-- PeTTa's richest current MeTTa-facing result carrier is `EvalResult`, which
threads explicit bindings through a list of alternatives. -/
theorem pettaRuntimeSpec_result_bindings_fact :
    pettaRuntimeSpec.bindingsMode = .explicit ∧
    pettaRuntimeSpec.branchingMode = .explicitAlternatives ∧
    Mettapedia.Languages.MeTTa.PeTTa.EvalResult =
      List (Pattern × Mettapedia.OSLF.MeTTaIL.Match.Bindings) := by
  simp [pettaRuntimeSpec, Mettapedia.Languages.MeTTa.PeTTa.EvalResult]

/-- PeTTa's base runtime profile is explicitly space-indexed: `(match &self ...)`
is interpreted directly against `s.spaceMatch`. -/
theorem pettaRuntimeSpec_context_fact :
    pettaRuntimeSpec.contextMode = .explicitSpace ∧
    ∀ (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) (pat tmpl : Pattern),
      Mettapedia.Languages.MeTTa.PeTTa.PeTTaEval s
        (.apply "match" [.apply "&self" [], pat, tmpl])
        (s.spaceMatch pat tmpl) := by
  refine ⟨rfl, ?_⟩
  intro s pat tmpl
  exact Mettapedia.Languages.MeTTa.PeTTa.petta_eval_spaceQuery_correct s pat tmpl

/-- PeTTa exposes `superpose`/`collapse` through the semantic interface in both the
type-free and binding-threaded relations. -/
theorem pettaRuntimeSpec_collection_control_fact :
    pettaRuntimeSpec.collectionControl = .collapseSuperpose ∧
    (∀ (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) (alts : List Pattern),
      Mettapedia.Languages.MeTTa.PeTTa.PeTTaEval s
        (.apply "superpose" [.collection .vec alts none]) alts) ∧
    (∀ (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) (p ty : Pattern)
        (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
        (results : Mettapedia.Languages.MeTTa.PeTTa.EvalResult),
      Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval s p ty bindings results →
      Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval s (.apply "collapse" [p]) ty bindings
        [(.collection .vec (results.map Prod.fst) none, bindings)]) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro s alts
    exact Mettapedia.Languages.MeTTa.PeTTa.PeTTaEval.superpose alts
  · intro s p ty bindings results h
    exact Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval.collapse p ty bindings results h

/- The absence of a native-hook mode in the first PeTTa runtime spec remains
an explicit regularization choice. The current formalization has pure,
binding-threaded, LP, and artifact layers, but no single dedicated base-runtime
hook analogous to HE's `groundedCallResult`. -/

end Mettapedia.Languages.MeTTa.RuntimeSpec
