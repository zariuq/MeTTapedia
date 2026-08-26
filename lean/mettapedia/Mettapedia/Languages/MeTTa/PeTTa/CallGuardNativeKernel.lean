import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT

/-!
# Vanilla PeTTa typed calls as a native operational kernel

This module gives the closed, resolved-declaration fragment of vanilla PeTTa's
typed-call guard a live operational meaning.  It is not a trace checker.  A
successful transition selects an authored arrow-declaration occurrence and
executes the `get-type`/`get-metatype` relations at the call boundary.

The input and output rules follow current mainline PeTTa:

* an `Atom` input remains raw;
* `%Undefined%` and `_` inputs are unchecked after evaluation;
* an ordinary input tries `get-type` first and uses `get-metatype` only when
  that exact `get-type` query has no solution;
* `%Undefined%`, `_`, and `Atom` outputs are unchecked; and
* ordinary outputs use the same soft-cut query order.

Argument evaluation and the called function's own semantics are adjacent
authorities.  This kernel consumes their values but does not pretend to prove
how those values were computed.  The optional boundary article near the end
only names the selected declaration; it replays this native judgment and does
not define it.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT

set_option autoImplicit false

/-! ## Live call-boundary judgments -/

/-- A typed-call configuration after ordinary argument evaluation and after
the called relation has produced one candidate result.  Source arguments stay
visible because the `Atom` input rule must establish that its argument was
passed raw. -/
structure Call where
  function : String
  sourceArguments : List Term
  evaluatedArguments : List Term
  result : Term
deriving DecidableEq, Repr

/-- The ordered vanilla input guard.  The negative first-query premise is the
logical content of Prolog's `*->` fallback. -/
def InputGuard (snapshot : Snapshot)
    (source value expected : Term) : Prop :=
  if expected = atomType then
    value = source
  else if expected = undefinedType then
    True
  else if expected = holeType then
    True
  else
    GetType snapshot value expected ∨
      (¬ GetType snapshot value expected ∧
        GetMetatype snapshot value expected)

instance (snapshot : Snapshot) (source value expected : Term) :
    Decidable (InputGuard snapshot source value expected) := by
  unfold InputGuard
  infer_instance

/-- All three argument lists are consumed in lockstep.  Length mismatch is
ordinary guard failure. -/
def ArgumentsGuard (snapshot : Snapshot) :
    List Term → List Term → List Term → Prop
  | [], [], [] => True
  | source :: sources, value :: values, expected :: expectedTypes =>
      InputGuard snapshot source value expected ∧
        ArgumentsGuard snapshot sources values expectedTypes
  | _, _, _ => False

private def decidableArgumentsGuard (snapshot : Snapshot) :
    (sources values expectedTypes : List Term) →
      Decidable (ArgumentsGuard snapshot sources values expectedTypes)
  | [], [], [] => isTrue trivial
  | source :: sources, value :: values, expected :: expectedTypes =>
      match inferInstanceAs
          (Decidable (InputGuard snapshot source value expected)),
        decidableArgumentsGuard snapshot sources values expectedTypes with
      | isTrue headProof, isTrue tailProof =>
          isTrue ⟨headProof, tailProof⟩
      | isFalse headFailure, _ =>
          isFalse (fun proof => headFailure proof.1)
      | _, isFalse tailFailure =>
          isFalse (fun proof => tailFailure proof.2)
  | [], [], _ :: _ => isFalse (by simp [ArgumentsGuard])
  | [], _ :: _, [] => isFalse (by simp [ArgumentsGuard])
  | [], _ :: _, _ :: _ => isFalse (by simp [ArgumentsGuard])
  | _ :: _, [], [] => isFalse (by simp [ArgumentsGuard])
  | _ :: _, [], _ :: _ => isFalse (by simp [ArgumentsGuard])
  | _ :: _, _ :: _, [] => isFalse (by simp [ArgumentsGuard])

instance (snapshot : Snapshot) (sources values expectedTypes : List Term) :
    Decidable (ArgumentsGuard snapshot sources values expectedTypes) :=
  decidableArgumentsGuard snapshot sources values expectedTypes

/-- Output checking has no raw-argument case. -/
def OutputGuard (snapshot : Snapshot) (value expected : Term) : Prop :=
  if expected = undefinedType then
    True
  else if expected = holeType then
    True
  else if expected = atomType then
    True
  else
    GetType snapshot value expected ∨
      (¬ GetType snapshot value expected ∧
        GetMetatype snapshot value expected)

instance (snapshot : Snapshot) (value expected : Term) :
    Decidable (OutputGuard snapshot value expected) := by
  unfold OutputGuard
  infer_instance

structure Claim where
  snapshot : Snapshot
  call : Call
deriving DecidableEq, Repr

/-- One exact declaration occurrence natively guards one call occurrence. -/
def GuardedBy (declaration : ArrowDeclaration) (claim : Claim) : Prop :=
  claim.snapshot.WellFormed ∧
    declaration ∈ claim.snapshot.declarations ∧
    declaration.function = claim.call.function ∧
    ArgumentsGuard claim.snapshot
      claim.call.sourceArguments
      claim.call.evaluatedArguments
      declaration.inputTypes ∧
    OutputGuard claim.snapshot claim.call.result declaration.outputType

instance (declaration : ArrowDeclaration) (claim : Claim) :
    Decidable (GuardedBy declaration claim) := by
  unfold GuardedBy
  infer_instance

/-- The native call judgment is existential declaration resolution followed
by live guard execution. -/
def GuardedCall (claim : Claim) : Prop :=
  ∃ declaration ∈ claim.snapshot.declarations,
    GuardedBy declaration claim

instance (claim : Claim) : Decidable (GuardedCall claim) := by
  unfold GuardedCall
  infer_instance

def callDecision (claim : Claim) : Bool := decide (GuardedCall claim)

theorem callDecision_correct (claim : Claim) :
    callDecision claim = true ↔ GuardedCall claim := by
  exact decide_eq_true_iff

/-- Closed finite calls support direct decision.  Open and polymorphic calls use
the same judgment relationally rather than being reduced to this interface. -/
def decisionKernel : Checker.DecisionKernel Claim GuardedCall where
  decide := callDecision
  correct := callDecision_correct

/-- The successful declaration fibre in PeTTa's authored order.  This is the
list-valued interface for relational callers that must retain alternative
answers rather than collapse them to `GuardedCall`. -/
def successfulDeclarations (claim : Claim) : List ArrowDeclaration :=
  claim.snapshot.declarations.filter fun declaration =>
    decide (GuardedBy declaration claim)

theorem mem_successfulDeclarations_iff
    (claim : Claim) (declaration : ArrowDeclaration) :
    declaration ∈ successfulDeclarations claim ↔
      declaration ∈ claim.snapshot.declarations ∧
        GuardedBy declaration claim := by
  simp [successfulDeclarations]

/-- Boolean call admission is exactly the nonemptiness projection of the
ordered relational answer fibre. -/
theorem guardedCall_iff_successfulDeclarations_ne_nil (claim : Claim) :
    GuardedCall claim ↔ successfulDeclarations claim ≠ [] := by
  constructor
  · rintro ⟨declaration, member, guarded⟩
    exact List.ne_nil_of_mem
      ((mem_successfulDeclarations_iff claim declaration).mpr
        ⟨member, guarded⟩)
  · intro nonempty
    cases successful : successfulDeclarations claim with
    | nil => exact False.elim (nonempty successful)
    | cons declaration remaining =>
        have memberSuccessful :
            declaration ∈ successfulDeclarations claim := by
          rw [successful]
          simp
        obtain ⟨member, guarded⟩ :=
          (mem_successfulDeclarations_iff claim declaration).mp memberSuccessful
        exact ⟨declaration, member, guarded⟩

theorem callDecision_eq_true_iff_successfulDeclarations_ne_nil
    (claim : Claim) :
    callDecision claim = true ↔ successfulDeclarations claim ≠ [] := by
  rw [callDecision_correct, guardedCall_iff_successfulDeclarations_ne_nil]

/-! ## Operational GSLT and its exact generated NTT -/

inductive Phase where
  | pending
  | accepted (declaration : ArrowDeclaration)
deriving DecidableEq, Repr

structure Machine where
  claim : Claim
  phase : Phase
deriving DecidableEq, Repr

/-- Each successful successor retains the selected unique type-chain branch
and its first source occurrence.  Multiple distinct applicable chains remain
multiple operational successors rather than collapsing into one Boolean
endpoint. -/
def MachineStep (source target : Machine) : Prop :=
  source.phase = .pending ∧
    ∃ declaration ∈ source.claim.snapshot.declarations,
      GuardedBy declaration source.claim ∧
        target = ⟨source.claim, .accepted declaration⟩

instance (source target : Machine) : Decidable (MachineStep source target) := by
  unfold MachineStep
  infer_instance

def callGuardGSLT : GSLT where
  Term := Machine
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := MachineStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def stepDecision : EffectiveStructure.StepDecision callGuardGSLT where
  decideStep source target := decide (MachineStep source target)
  correct := by
    intro source target
    exact decide_eq_true_iff

/-- The NTT generated from the call-guard GSLT recognizes exactly the selected
typed-call successor. -/
theorem decideStep_iff_ntt (source target : Machine) :
    stepDecision.decideStep source target = true ↔
      (gsltOSLF callGuardGSLT).satisfies source
        (exactTargetNativeType callGuardGSLT target).pred := by
  rw [stepDecision.correct, satisfies_exactTargetNativeType_iff_step]

/-- The exact modal type consumed by later native inference composition. -/
abbrev typedCallNTT (claim : Claim) (declaration : ArrowDeclaration) :
    GSLTNativeType callGuardGSLT :=
  exactTargetNativeType callGuardGSLT
    (⟨claim, .accepted declaration⟩ : Machine)

/-- NTT inhabitation is exactly live guarding by the selected declaration,
including its membership in the current revision. -/
theorem satisfies_typedCallNTT_iff
    (claim : Claim) (declaration : ArrowDeclaration) :
    (gsltOSLF callGuardGSLT).satisfies ⟨claim, .pending⟩
        (typedCallNTT claim declaration).pred ↔
      declaration ∈ claim.snapshot.declarations ∧
        GuardedBy declaration claim := by
  rw [satisfies_exactTargetNativeType_iff_step]
  constructor
  · rintro ⟨_, candidate, member, guarded, targetEqual⟩
    cases targetEqual
    exact ⟨member, guarded⟩
  · rintro ⟨member, guarded⟩
    exact ⟨rfl, declaration, member, guarded, rfl⟩

/-- The generated NTT has exactly the ordered list fibre exposed by the native
PeTTa relation.  In particular, alternative distinct type chains remain
available to the surrounding Prolog search in first-authored order. -/
theorem satisfies_typedCallNTT_iff_mem_successfulDeclarations
    (claim : Claim) (declaration : ArrowDeclaration) :
    (gsltOSLF callGuardGSLT).satisfies ⟨claim, .pending⟩
        (typedCallNTT claim declaration).pred ↔
      declaration ∈ successfulDeclarations claim := by
  rw [satisfies_typedCallNTT_iff, mem_successfulDeclarations_iff]

/-! ## Optional external boundary article -/

/-- A boundary article names only the declaration occurrence to replay.  It
does not carry asserted type-query answers. -/
structure BoundaryArticle where
  declaration : ArrowDeclaration
deriving DecidableEq, Repr

def BoundaryArticle.Valid (article : BoundaryArticle) (claim : Claim) : Prop :=
  article.declaration ∈ claim.snapshot.declarations ∧
    GuardedBy article.declaration claim

instance (article : BoundaryArticle) (claim : Claim) :
    Decidable (article.Valid claim) := by
  unfold BoundaryArticle.Valid
  infer_instance

theorem guardedCall_iff_exists_boundary_article (claim : Claim) :
    GuardedCall claim ↔
      ∃ article : BoundaryArticle, article.Valid claim := by
  constructor
  · rintro ⟨declaration, member, guarded⟩
    exact ⟨⟨declaration⟩, member, guarded⟩
  · rintro ⟨⟨declaration⟩, member, guarded⟩
    exact ⟨declaration, member, guarded⟩

inductive AuthorityKind where
  | typedCallBoundary
deriving DecidableEq

def boundaryProofSystem : NativeProofSystem Claim where
  ProofObject := BoundaryArticle
  Judges := fun article claim => article.Valid claim

def boundaryKernel : NativeProofKernel boundaryProofSystem where
  decide claim article := decide (article.Valid claim)
  correct := by
    intro claim article
    exact decide_eq_true_iff

def boundaryFamily : AuthorityFamily AuthorityKind where
  Claim := fun _ => Claim
  Certificate := fun _ => BoundaryArticle
  checker := fun _ => boundaryKernel.toChecker
  Certified := fun _ claim => Nonempty (boundaryProofSystem.ProofFibre claim)
  Meaning := fun _ claim => GuardedCall claim
  projection := fun _ =>
    { authority := boundaryKernel.authority
      project := by
        intro claim certified
        rcases certified with ⟨⟨article, valid⟩⟩
        exact (guardedCall_iff_exists_boundary_article claim).mpr
          ⟨article, valid⟩ }

theorem accepted_boundary_article_produces_native_step
    {claim : Claim} {article : BoundaryArticle}
    (accepted : boundaryKernel.toChecker.check claim article = true) :
    callGuardGSLT.Step
      ⟨claim, .pending⟩
      ⟨claim, .accepted article.declaration⟩ := by
  have valid := (boundaryKernel.correct claim article).mp accepted
  exact ⟨rfl, article.declaration, valid.1, valid.2, rfl⟩

/-! ## Discriminating current-mainline canaries -/

namespace Canary

def declaration : ArrowDeclaration :=
  ⟨10, "f", [atomType], numberType⟩

def snapshot : Snapshot :=
  ⟨7, [declaration], [], ["f"]⟩

def source : Term := .atom "source"
def result : Term := .number "7"

def claim : Claim :=
  ⟨snapshot, ⟨"f", [source], [source], result⟩⟩

theorem direct_call_accepted : callDecision claim = true := by
  decide

/-- `Atom` inputs are raw: substituting a different evaluated value is not a
valid typed call. -/
def changedRawClaim : Claim :=
  { claim with call := { claim.call with evaluatedArguments := [.atom "changed"] } }

theorem changed_raw_atom_rejected : callDecision changedRawClaim = false := by
  decide

/-- The old pinned-PeTTa `Expression` raw-input convention is not silently
accepted as current mainline's `Atom` convention. -/
def oldConventionDeclaration : ArrowDeclaration :=
  ⟨11, "f", [expressionMetaType], numberType⟩

def oldConventionClaim : Claim :=
  ⟨⟨7, [oldConventionDeclaration], [], ["f"]⟩,
    ⟨"f", [source], [source], result⟩⟩

theorem old_expression_raw_convention_rejected :
    callDecision oldConventionClaim = false := by
  decide

/-- When the expected `get-type` query fails, the metatype branch is live. -/
def fallbackDeclaration : ArrowDeclaration :=
  ⟨12, "g", [groundedMetaType], numberType⟩

def fallbackClaim : Claim :=
  ⟨⟨7, [fallbackDeclaration], [], ["g"]⟩,
    ⟨"g", [.number "3"], [.number "3"], result⟩⟩

theorem metatype_fallback_accepted : callDecision fallbackClaim = true := by
  decide

def alternativeDeclaration : ArrowDeclaration :=
  ⟨13, "f", [undefinedType], undefinedType⟩

def overloadedClaim : Claim :=
  { claim with
    snapshot :=
      { snapshot with
        declarations := [declaration, alternativeDeclaration] } }

/-- Applicable distinct type chains retain their first-authored order rather
than being selected by a hidden priority. -/
theorem successful_declarations_retain_authored_order :
    successfulDeclarations overloadedClaim =
      [declaration, alternativeDeclaration] := by
  decide

def duplicateChainClaim : Claim :=
  { claim with
    snapshot :=
      { snapshot with
        declarations := [declaration, { declaration with occurrence := 13 }] } }

/-- The admitted snapshot is downstream of PeTTa's `list_to_set`: presenting
the same semantic type chain twice is rejected rather than inventing a second
operational successor. -/
theorem duplicate_type_chain_rejected :
    callDecision duplicateChainClaim = false := by
  decide

def acceptedTarget : Machine :=
  ⟨claim, .accepted declaration⟩

theorem accepted_successor_has_generated_ntt :
    (gsltOSLF callGuardGSLT).satisfies ⟨claim, .pending⟩
      (exactTargetNativeType callGuardGSLT acceptedTarget).pred := by
  exact (decideStep_iff_ntt ⟨claim, .pending⟩ acceptedTarget).mp (by decide)

end Canary

#print axioms callDecision_correct
#print axioms guardedCall_iff_successfulDeclarations_ne_nil
#print axioms callDecision_eq_true_iff_successfulDeclarations_ne_nil
#print axioms decideStep_iff_ntt
#print axioms satisfies_typedCallNTT_iff
#print axioms satisfies_typedCallNTT_iff_mem_successfulDeclarations
#print axioms guardedCall_iff_exists_boundary_article
#print axioms accepted_boundary_article_produces_native_step
#print axioms Canary.direct_call_accepted
#print axioms Canary.changed_raw_atom_rejected
#print axioms Canary.old_expression_raw_convention_rejected
#print axioms Canary.metatype_fallback_accepted
#print axioms Canary.successful_declarations_retain_authored_order
#print axioms Canary.duplicate_type_chain_rejected
#print axioms Canary.accepted_successor_has_generated_ntt

end Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
