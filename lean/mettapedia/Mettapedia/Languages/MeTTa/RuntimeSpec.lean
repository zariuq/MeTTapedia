import Mettapedia.Languages.MeTTa.DialectProfile
import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.HE.HEPremises
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness

/-!
# MeTTa Runtime Spec Surface

First draft of an auditable `R_spec` layer for the MeTTa family.

This file is intentionally small.  It does not define execution semantics and
it does not try to identify all dialects with one shared core machine.  It only
records the runtime-facing semantic features that should be obvious to reviewers
inspecting `HE`, `PeTTa`, `Pure`, and the legacy state-machine slice.

The intended reading is:

- `R_exec` may be implemented by an MM2/MORK-like substrate
- `R_spec` remains recognizably MeTTa
- PureKernel `A/B/C1` stays separate and untouched
- future maps `HE -> R_spec`, `PeTTa -> R_spec`, and then `R_spec -> C*`
  should target this surface rather than redefining the kernel
-/

namespace Mettapedia.Languages.MeTTa.RuntimeSpec

open Mettapedia.Languages.MeTTa.DialectProfile
open Mettapedia.Languages.MeTTa.CoreProfile
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Whether variable bindings are an explicit semantic object. -/
inductive BindingsSurface where
  | none
  | explicit
  deriving DecidableEq, Repr

/-- Whether branching is represented explicitly in the semantic surface. -/
inductive BranchingSurface where
  | single
  | explicitAlternatives
  deriving DecidableEq, Repr

/-- How the runtime surface exposes the space/context side of MeTTa execution. -/
inductive ContextSurface where
  | none
  | explicitSpace
  | explicitStateAndSpace
  deriving DecidableEq, Repr

/-- How the runtime surface exposes native/grounded execution hooks. -/
inductive NativeHookSurface where
  | none
  | groundedDispatch
  | oracleLayer
  deriving DecidableEq, Repr

/-- Whether collapse/superpose-style collection control is explicit. -/
inductive CollectionControlSurface where
  | none
  | collapseSuperpose
  deriving DecidableEq, Repr

/-- Minimal first-draft runtime spec for a MeTTa dialect.

The carrier names are intentionally strings in the first draft.  This keeps the
surface auditable without prematurely fixing the exact theorem boundary between
runtime relations living in different files.
-/
structure MeTTaRuntimeSpec where
  dialect : MeTTaDialectProfile
  stateCarrier : String
  resultCarrier : String
  bindingsSurface : BindingsSurface
  branchingSurface : BranchingSurface
  contextSurface : ContextSurface
  nativeHookSurface : NativeHookSurface
  collectionControl : CollectionControlSurface

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

/-- Runtime-facing kernel surface.  Pure is intentionally degenerate here:
there is no ambient atomspace or bindings store. -/
def pureRuntimeSpec : MeTTaRuntimeSpec where
  dialect := pureDialectProfile
  stateCarrier := "PureTm 0"
  resultCarrier := "PureTm 0"
  bindingsSurface := .none
  branchingSurface := .single
  contextSurface := .none
  nativeHookSurface := .none
  collectionControl := .none

/-- Runtime-facing HE surface.

This records the recognizably MeTTa runtime features already explicit in the HE
formalization: `State`, `ResultSet`, explicit bindings, explicit space, and
grounded dispatch.
-/
def heRuntimeSpec : MeTTaRuntimeSpec where
  dialect := heDialectProfile
  stateCarrier := "State"
  resultCarrier := "ResultSet"
  bindingsSurface := .explicit
  branchingSurface := .explicitAlternatives
  contextSurface := .explicitStateAndSpace
  nativeHookSurface := .groundedDispatch
  collectionControl := .collapseSuperpose

/-- Runtime-facing PeTTa surface.

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
  bindingsSurface := .explicit
  branchingSurface := .explicitAlternatives
  contextSurface := .explicitSpace
  nativeHookSurface := .none
  collectionControl := .collapseSuperpose

/-- Runtime-facing legacy full/core surface. -/
def fullLegacyRuntimeSpec : MeTTaRuntimeSpec where
  dialect := fullLegacyDialectProfile
  stateCarrier := "State"
  resultCarrier := "Atom"
  bindingsSurface := .none
  branchingSurface := .single
  contextSurface := .explicitStateAndSpace
  nativeHookSurface := .groundedDispatch
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
    pureRuntimeSpec.bindingsSurface = .none := rfl

@[simp] theorem heRuntimeSpec_dialect :
    heRuntimeSpec.dialect = heDialectProfile := rfl

@[simp] theorem heRuntimeSpec_stateCarrier :
    heRuntimeSpec.stateCarrier = "State" := rfl

@[simp] theorem heRuntimeSpec_resultCarrier :
    heRuntimeSpec.resultCarrier = "ResultSet" := rfl

@[simp] theorem heRuntimeSpec_native :
    heRuntimeSpec.nativeHookSurface = .groundedDispatch := rfl

@[simp] theorem pettaRuntimeSpec_dialect :
    pettaRuntimeSpec.dialect = pettaDialectProfile := rfl

@[simp] theorem pettaRuntimeSpec_stateCarrier :
    pettaRuntimeSpec.stateCarrier = "PeTTaSpace" := rfl

@[simp] theorem pettaRuntimeSpec_resultCarrier :
    pettaRuntimeSpec.resultCarrier = "EvalResult" := rfl

@[simp] theorem pettaRuntimeSpec_native :
    pettaRuntimeSpec.nativeHookSurface = .none := rfl

@[simp] theorem fullLegacyRuntimeSpec_dialect :
    fullLegacyRuntimeSpec.dialect = fullLegacyDialectProfile := rfl

/-! ## HE Fact Surface -/

/-- `heRuntimeSpec` is anchored in the fixed HE core profile and its exported
language/premise objects. -/
theorem heRuntimeSpec_profile_fact :
    heRuntimeSpec.dialect.referenceCoreProfile? = some heProfile ∧
    heProfile.lang = Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE ∧
    heProfile.premises = Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises := by
  simp [heRuntimeSpec, heDialectProfile, heProfile]

/-- The HE runtime surface explicitly exposes both `State` and `Space` in the
exported language definition. -/
theorem heRuntimeSpec_state_context_fact :
    heRuntimeSpec.contextSurface = .explicitStateAndSpace ∧
    languageHasTypeNamed Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE "State" ∧
    languageHasTypeNamed Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE "Space" := by
  native_decide

/-- HE's result carrier is concretely a list of `(Atom × Bindings)` pairs, so
bindings and explicit alternatives are part of the formal semantic surface. -/
theorem heRuntimeSpec_result_bindings_fact :
    heRuntimeSpec.bindingsSurface = .explicit ∧
    heRuntimeSpec.branchingSurface = .explicitAlternatives ∧
    Mettapedia.Languages.MeTTa.HE.ResultSet =
      List (Mettapedia.Languages.MeTTa.HE.ResultPair) := by
  simp [heRuntimeSpec, Mettapedia.Languages.MeTTa.HE.ResultSet]

/-- HE's native hook classification is justified by the exported
`groundedCallResult` premise relation and the interpreter's explicit
`GroundedDispatch` parameter. -/
theorem heRuntimeSpec_native_hook_fact :
    heRuntimeSpec.nativeHookSurface = .groundedDispatch ∧
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

/-! ## PeTTa Fact Surface -/

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
    pettaRuntimeSpec.bindingsSurface = .explicit ∧
    pettaRuntimeSpec.branchingSurface = .explicitAlternatives ∧
    Mettapedia.Languages.MeTTa.PeTTa.EvalResult =
      List (Pattern × Mettapedia.OSLF.MeTTaIL.Match.Bindings) := by
  simp [pettaRuntimeSpec, Mettapedia.Languages.MeTTa.PeTTa.EvalResult]

/-- PeTTa's base runtime surface is explicitly space-indexed: `(match &self ...)`
is interpreted directly against `s.spaceMatch`. -/
theorem pettaRuntimeSpec_context_fact :
    pettaRuntimeSpec.contextSurface = .explicitSpace ∧
    ∀ (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) (pat tmpl : Pattern),
      Mettapedia.Languages.MeTTa.PeTTa.PeTTaEval s
        (.apply "match" [.apply "&self" [], pat, tmpl])
        (s.spaceMatch pat tmpl) := by
  refine ⟨rfl, ?_⟩
  intro s pat tmpl
  exact Mettapedia.Languages.MeTTa.PeTTa.petta_eval_spaceQuery_correct s pat tmpl

/-- PeTTa exposes `superpose`/`collapse` at the semantic surface in both the
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

/- The absence of a native-hook surface in the first PeTTa runtime spec remains
an explicit regularization choice. The current formalization has pure,
binding-threaded, LP, and artifact layers, but no single dedicated base-runtime
hook analogous to HE's `groundedCallResult`. -/

end Mettapedia.Languages.MeTTa.RuntimeSpec
