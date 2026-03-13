import Mettapedia.Languages.MeTTa.InductiveKernelExtension
import Mettapedia.Languages.MeTTa.PureCheckingExtensions

/-!
# General Ordinary-Family Kernel Design Memo

This file is a design memo for the next real `PureKernel` implementation step.
It is intentionally **not** imported by the trusted umbrella path.

The purpose is to make one thing explicit before implementation resumes:

- ordinary families must enter `PureKernel` through a **general mechanism**,
- `Unit`, `Bool`, and `Nat` must arise as instances of that mechanism,
- and `Unit` is the first proving ground for the implementation.

The memo is code-adjacent on purpose: it names the objects, obligations, and
phase order in Lean terms, but it does not pretend the mechanism is already
implemented.
-/

namespace Mettapedia.Languages.MeTTa

/-- What route the next kernel extension is allowed to take. -/
inductive OrdinaryFamilyKernelRoute where
  | declarationEnvWithSymbolicRefs
  | familySpecificBuiltinsRejected
deriving DecidableEq, Repr

/-- The design choice for the next implementation pass. -/
def chosenOrdinaryFamilyKernelRoute : OrdinaryFamilyKernelRoute :=
  .declarationEnvWithSymbolicRefs

/-- Generic references into the future ordinary-family declaration environment.

The key idea is that the kernel should not gain `NatRec`, `BoolRec`, etc.
Instead, the term language should refer to declarations through generic
symbols whose meaning is supplied by the ordinary-family environment.
-/
structure OrdinaryFamilyRefs where
  familyName : String
  ctorName : Option String := none
  recursorName : Option String := none
deriving DecidableEq, Repr

/-- Memo-level classification tags for the existing generic term route.

These are not proposed new `PureTm` constructors. They classify how ordinary
families will use the already-live generic symbolic head route:
- family/constructor/recursor names as ordinary `PureTm.const` heads,
- ordinary `app` for instantiation and elimination.
-/
inductive OrdinaryFamilyTermForm where
  | familyConst
  | ctorConst
  | recursorConst
  | motiveApp
  | ctorApp
  | recursorApp
deriving DecidableEq, Repr

/-- The declaration environment shape needed by the next implementation pass. -/
structure OrdinaryFamilyDeclarationEnv where
  declarations : List OrdinaryFamilyDeclaration
  familyNamesDistinct : declarations.Pairwise (fun a b => a.familyName ≠ b.familyName)
deriving Repr

/-- The kernel needs one explicit naming discipline for declared family items.

The immediate goal is not to settle parser syntax. It is to say what kind of
references the trusted term language may carry once ordinary families are
admitted through a declaration environment.
-/
inductive OrdinaryFamilyRefForm where
  | familyRefByName
  | ctorRefByQualifiedName
  | recursorRefByQualifiedName
deriving DecidableEq, Repr

/-- The current design choice for kernel references into the declaration
environment.

We choose symbolic names first because:

- the surrounding spec/interface layers already speak in names,
- `Unit` as the pilot does not need de Bruijn-style declaration indices to test
  the mechanism,
- and bridge/paper/debugging work stays legible while the mechanism is being
  stabilized.

If we later want a compiled/indexed internal form, it should come after the
symbolic route is correct, not instead of it.
-/
def chosenOrdinaryFamilyRefForm : OrdinaryFamilyRefForm :=
  .familyRefByName

/-- Generic references carried by the future declaration metadata.

These references are generic on purpose:
- no `Nat.rec`,
- no `Bool.true`,
- no `Unit.unit` baked into the AST shape.

Instead, declaration metadata and lowering will carry these references, and
typing/reduction will consult the declaration environment to interpret the
already-existing generic kernel heads.
-/
inductive KernelOrdinaryFamilyRef where
  | family (familyName : String)
  | ctor (familyName ctorName : String)
  | recursor (familyName recursorName : String)
deriving DecidableEq, Repr

/-- Memo-level classification tags over the existing generic kernel route.

These tags describe how the declaration mechanism uses the current
`PureTm.const` + `app` route. They are not a request to reopen `Syntax.lean`.
-/
inductive PlannedOrdinaryFamilyKernelForm where
  | declConst (ref : KernelOrdinaryFamilyRef)
  | declElim (recursorRef : KernelOrdinaryFamilyRef)
deriving DecidableEq, Repr

/-- Files that must move in lockstep once the declaration-driven general
mechanism starts landing.

This checklist intentionally avoids reopening `PureKernel/Syntax.lean` unless a
later theorem forces it. The recovered kernel already has the generic symbolic
route it needs: `PureTm.const`, `app`, `HasTypeDecl`, and `RedDecl`. -/
def ordinaryFamilyKernelTouchSet : List String :=
  [ "Mettapedia/Languages/MeTTa/InductiveKernelExtension.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationEnv.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationSemantics.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationPilotScaffold.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/PatternBridge.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/CoreEmbedding.lean"
  , "Mettapedia/Languages/MeTTa/PureCertificateFragment.lean"
  , "Mettapedia/Languages/MeTTa/PureCheckingService.lean"
  , "Mettapedia/Languages/MeTTa/PureNormalizationService.lean"
  , "Mettapedia/Languages/MeTTa/PureCanonicalEvaluation.lean" ]

/-- The minimal declaration/kernel files that must change for the `Unit` pilot
itself.

The intent is to realize `Unit` through the declaration-driven extension layer,
not through ad hoc kernel syntax growth. -/
def unitPilotKernelTouchSet : List String :=
  [ "Mettapedia/Languages/MeTTa/InductiveKernelExtension.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationEnv.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationSemantics.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationPilotScaffold.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/PatternBridge.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/CoreEmbedding.lean"
  , "Mettapedia/Languages/MeTTa/PureCertificateFragment.lean" ]

/-- The first implementation proving ground.

`Unit` is the pilot because it has:
- zero parameters,
- zero indices,
- one nullary constructor,
- the smallest nontrivial recursor story.
-/
def ordinaryFamilyPilot : OrdinaryFamilyDeclaration :=
  unitKernelExtension.declaration

/-- The order in which the first concrete instances should land. -/
def ordinaryFamilyPilotOrder : List OrdinaryFamilyDeclaration :=
  [ unitKernelExtension.declaration
  , boolKernelExtension.declaration
  , natKernelExtension.declaration ]

/-- The declaration environment responsibilities that typing/reduction must
share.

This is the central representation checkpoint before implementation:
- family/constructor/recursor heads lower through ordinary `const` names,
- typing must validate those names against the declaration environment,
- reduction must consult the same environment for recursor computation,
- and no new trusted kernel syntax should be introduced unless a later theorem
  genuinely forces it.
-/
structure OrdinaryFamilyKernelEnvironmentContract where
  declarationEnv : OrdinaryFamilyDeclarationEnv
  referenceForm : OrdinaryFamilyRefForm
  termForms : List PlannedOrdinaryFamilyKernelForm
  typingConsultsEnv : Bool
  reductionConsultsEnv : Bool
  generatedRecursorsComeFromDeclarations : Bool
deriving Repr

/-- The implementation-ready environment contract for the next pass. -/
def ordinaryFamilyKernelEnvironmentContract : OrdinaryFamilyKernelEnvironmentContract :=
  { declarationEnv :=
      { declarations := ordinaryFamilyPilotOrder
        familyNamesDistinct := by
          native_decide }
    referenceForm := chosenOrdinaryFamilyRefForm
    termForms :=
      [ .declConst (.family "Unit")
      , .declConst (.ctor "Unit" "unit")
      , .declConst (.recursor "Unit" "Unit.rec")
      , .declElim (.recursor "Unit" "Unit.rec") ]
    typingConsultsEnv := true
    reductionConsultsEnv := true
    generatedRecursorsComeFromDeclarations := true }

/-- The exact kind of success criterion we want from the first pass. -/
structure OrdinaryFamilyPilotSuccess where
  route : OrdinaryFamilyKernelRoute
  pilotFamily : String
  noFamilySpecificAstGrowth : Bool
  generatedRecursorComesFromDeclaration : Bool
  checkingBoundaryStillAuthoritative : Bool
  subjectReductionReestablished : Bool
  canonicalizationUpdated : Bool
  bridgeQuotingUpdated : Bool
deriving Repr

/-- File-by-file obligations for the first `Unit` pilot.

This is meant to prevent the common “we implemented the constructor but forgot
the bridge/theory side” failure mode.
-/
structure UnitPilotTouchPoint where
  file : String
  obligation : String
deriving DecidableEq, Repr

def unitPilotTouchPoints : List UnitPilotTouchPoint :=
  [ { file := "Mettapedia/Languages/MeTTa/InductiveKernelExtension.lean"
      obligation := "repair the typed family declaration layer into a binder-aware generic declaration object, without inventing another record family" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/DeclarationEnv.lean"
      obligation := "make the declaration environment extension route explicit enough to support monotonicity from prefix envs to fuller envs" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/DeclarationSemantics.lean"
      obligation := "prove typing/reduction/conversion monotonicity for declaration-env extension, then use it to let prefix-typed pilot facts feed full-env obligations" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/DeclarationPilotScaffold.lean"
      obligation := "make the prefix/signature layer lower cleanly into the operational environment facts instead of duplicating pilot-local proofs" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/PatternBridge.lean"
      obligation := "quote declaration-driven Unit family/constructor/recursor constants honestly into shared artifacts" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/CoreEmbedding.lean"
      obligation := "re-establish the Pure-to-profile bridge facts for the declaration-driven Unit recursor computation rule once the generic declaration lowering is real" }
  , { file := "Mettapedia/Languages/MeTTa/PureCertificateFragment.lean"
      obligation := "extend the restricted certificate lane only after the declaration-driven Unit instance is live and quotes correctly" } ]

/-- The target success profile for the first `Unit` implementation pass. -/
def unitPilotSuccessTarget : OrdinaryFamilyPilotSuccess :=
  { route := chosenOrdinaryFamilyKernelRoute
    pilotFamily := "Unit"
    noFamilySpecificAstGrowth := true
    generatedRecursorComesFromDeclaration := true
    checkingBoundaryStillAuthoritative := true
    subjectReductionReestablished := true
    canonicalizationUpdated := true
    bridgeQuotingUpdated := true }

/-- The implementation phase order that keeps the project at the right layer. -/
def ordinaryFamilyPhaseOrder : List String :=
  [ "freeze the current Pure checking/canonicalization waist"
  , "repair the typed family declaration layer into a binder-aware generic declaration object"
  , "prove declaration-env extension monotonicity for HasTypeDecl and the declaration-aware reduction/conversion relations"
  , "lower a generic family declaration to closed declaration specs"
  , "prove the lowering yields prefix-well-formed signatures and then operational env well-formedness"
  , "realize Unit as the first actual instance of the generic declaration object"
  , "add the first generated iota rule and prove its preservation boundary"
  , "re-establish quotation, profile, and certificate bridges"
  , "land Bool, then Nat"
  , "only then stage structural fixpoints above the family mechanism" ]

theorem chosenOrdinaryFamilyKernelRoute_is_general :
    chosenOrdinaryFamilyKernelRoute = .declarationEnvWithSymbolicRefs := rfl

theorem chosenOrdinaryFamilyRefForm_is_symbolic :
    chosenOrdinaryFamilyRefForm = .familyRefByName := rfl

theorem ordinaryFamilyKernelEnvironmentContract_typingConsultsEnv :
    ordinaryFamilyKernelEnvironmentContract.typingConsultsEnv = true := rfl

theorem ordinaryFamilyKernelEnvironmentContract_reductionConsultsEnv :
    ordinaryFamilyKernelEnvironmentContract.reductionConsultsEnv = true := rfl

theorem ordinaryFamilyKernelEnvironmentContract_generatesRecursorsFromDeclarations :
    ordinaryFamilyKernelEnvironmentContract.generatedRecursorsComeFromDeclarations = true := rfl

theorem ordinaryFamilyPilot_is_unit :
    ordinaryFamilyPilot.familyName = "Unit" := by
  rfl

theorem ordinaryFamilyPilotOrder_head_is_unit :
    ordinaryFamilyPilotOrder.head? = some ordinaryFamilyPilot := by
  rfl

theorem unitPilotSuccessTarget_rejects_familySpecificAstGrowth :
    unitPilotSuccessTarget.noFamilySpecificAstGrowth = true := rfl

theorem unitPilotSuccessTarget_requires_generatedRecursorFromDeclaration :
    unitPilotSuccessTarget.generatedRecursorComesFromDeclaration = true := rfl

theorem unitPilotKernelTouchSet_head_is_inductiveKernelExtension :
    unitPilotKernelTouchSet.head? =
      some "Mettapedia/Languages/MeTTa/InductiveKernelExtension.lean" := by
  rfl

theorem unitPilotTouchPoints_head_is_inductiveKernelExtension :
    unitPilotTouchPoints.head?.map UnitPilotTouchPoint.file =
      some "Mettapedia/Languages/MeTTa/InductiveKernelExtension.lean" := by
  rfl

theorem ordinaryFamilyPhaseOrder_starts_with_waist_freeze :
    ordinaryFamilyPhaseOrder.head? = some "freeze the current Pure checking/canonicalization waist" := by
  rfl

end Mettapedia.Languages.MeTTa
