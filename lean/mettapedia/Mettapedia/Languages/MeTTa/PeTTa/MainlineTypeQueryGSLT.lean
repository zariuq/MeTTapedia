import Mettapedia.GSLT.LanguageDef.CertificateGSLTFiniteTraceAuthority
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-!
# Closed mainline PeTTa type queries as an operational GSLT

This module presents the closed, resolved-declaration fragment of the type
queries used by mainline PeTTa.  It follows the clause order of `get-type` and
`get-metatype` rather than the optional `typecheck-v2` or `typecheck-v3`
languages.

The updateable reference baseline for this presentation is
`trueagi-io/PeTTa`, branch `fix/minimal-space-owned-eval-20260827`, commit
`91c27146b129f4d54776362ddb58898568f4665f`.  At that revision the modeled
clauses are `src/metta.pl:180-215` (`get-type`, `space-get-type`, and their
candidate relations) and `src/metta.pl:217-224` (`get-metatype`).  The space
selection used by typed guards is in `src/translator.pl:94-102`.  Moving this
baseline requires rechecking those clauses and rerunning the maintained
cross-runtime fixture gate; the commit records qualification, not a promise
that mainline PeTTa will stop evolving.

The carrier distinguishes Prolog variables, numbers, strings, atoms, and
lists.  Arrow declarations and ordinary type annotations are already resolved
ground occurrences from one atomspace revision.  Polymorphic declaration
matching, open lists, and the theorem connecting these occurrences to PeTTa's
`match` implementation are separate later boundaries.

For a closed term, the relevant mainline behavior is:

* primitive candidates for numbers, strings, booleans, and variables;
* recursively checked function applications;
* elementwise list typing only when no function type applies;
* exact resolved type annotations;
* `%Undefined%` as the `get-type` fallback; and
* structural `get-metatype`, including the registered-function distinction.

The query relation is independently stated as a recursive proposition.  Its
Boolean decision is then used as one operational GSLT step, from which OSLF
generates the exact-target native type.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

set_option autoImplicit false

/-! ## Closed PeTTa values and revisioned declarations -/

inductive Term where
  | variable (name : String)
  | number (lexeme : String)
  | string (value : String)
  | atom (name : String)
  | list (elements : List Term)
deriving Repr

mutual
  private def decEqTerm : (left right : Term) → Decidable (left = right)
    | .variable left, .variable right =>
        if equal : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro same; cases same; exact equal rfl)
    | .number left, .number right =>
        if equal : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro same; cases same; exact equal rfl)
    | .string left, .string right =>
        if equal : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro same; cases same; exact equal rfl)
    | .atom left, .atom right =>
        if equal : left = right then isTrue (by subst right; rfl)
        else isFalse (by intro same; cases same; exact equal rfl)
    | .list left, .list right =>
        match decEqTermList left right with
        | isTrue equal => isTrue (by subst right; rfl)
        | isFalse different =>
            isFalse (by intro same; cases same; exact different rfl)
    | .variable _, .number _ | .variable _, .string _
    | .variable _, .atom _ | .variable _, .list _
    | .number _, .variable _ | .number _, .string _
    | .number _, .atom _ | .number _, .list _
    | .string _, .variable _ | .string _, .number _
    | .string _, .atom _ | .string _, .list _
    | .atom _, .variable _ | .atom _, .number _
    | .atom _, .string _ | .atom _, .list _
    | .list _, .variable _ | .list _, .number _
    | .list _, .string _ | .list _, .atom _ =>
        isFalse Term.noConfusion

  private def decEqTermList :
      (left right : List Term) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun equal => by cases equal)
    | _ :: _, [] => isFalse (fun equal => by cases equal)
    | leftHead :: leftTail, rightHead :: rightTail =>
        match decEqTerm leftHead rightHead, decEqTermList leftTail rightTail with
        | isTrue headEqual, isTrue tailEqual =>
            isTrue (by subst rightHead; subst rightTail; rfl)
        | isFalse headDifferent, _ =>
            isFalse (by intro same; cases same; exact headDifferent rfl)
        | _, isFalse tailDifferent =>
            isFalse (by intro same; cases same; exact tailDifferent rfl)
end

instance : DecidableEq Term := decEqTerm

mutual
  /-- Maximum constructor depth of a closed term. -/
  def Term.height : Term → Nat
    | .variable _ | .number _ | .string _ | .atom _ => 1
    | .list elements => Term.listHeight elements + 1

  def Term.listHeight : List Term → Nat
    | [] => 0
    | head :: tail => max head.height (Term.listHeight tail)
end

def numberType : Term := .atom "Number"
def stringType : Term := .atom "String"
def boolType : Term := .atom "Bool"
def undefinedType : Term := .atom "%Undefined%"
def atomType : Term := .atom "Atom"
def holeType : Term := .atom "_"
def variableMetaType : Term := .atom "Variable"
def groundedMetaType : Term := .atom "Grounded"
def expressionMetaType : Term := .atom "Expression"
def symbolMetaType : Term := .atom "Symbol"

/-- One resolved branch of `(: f (-> A ... R))`.  Mainline PeTTa applies
`list_to_set` to the matching type chains before building its disjunction, so
`occurrence` records the first contributing source occurrence. -/
structure ArrowDeclaration where
  occurrence : Nat
  function : String
  inputTypes : List Term
  outputType : Term
deriving DecidableEq, Repr

def ArrowDeclaration.semanticKey
    (declaration : ArrowDeclaration) : String × List Term × Term :=
  (declaration.function, declaration.inputTypes, declaration.outputType)

/-- One resolved occurrence of an ordinary `(: subject type)` annotation. -/
structure TypeAnnotation where
  occurrence : Nat
  subject : Term
  type : Term
deriving DecidableEq, Repr

/-- The finite read-only environment for one query revision. -/
structure Snapshot where
  revision : Nat
  declarations : List ArrowDeclaration
  annotations : List TypeAnnotation
  registeredFunctions : List String
deriving DecidableEq, Repr

namespace Snapshot

def WellFormed (snapshot : Snapshot) : Prop :=
  (snapshot.declarations.map ArrowDeclaration.occurrence).Nodup ∧
    (snapshot.declarations.map ArrowDeclaration.semanticKey).Nodup ∧
      (snapshot.annotations.map TypeAnnotation.occurrence).Nodup ∧
        snapshot.registeredFunctions.Nodup

instance (snapshot : Snapshot) : Decidable snapshot.WellFormed := by
  unfold WellFormed
  infer_instance

def HasAnnotation (snapshot : Snapshot) (subject type : Term) : Prop :=
  ∃ annotation ∈ snapshot.annotations,
    annotation.subject = subject ∧ annotation.type = type

instance (snapshot : Snapshot) (subject type : Term) :
    Decidable (snapshot.HasAnnotation subject type) := by
  unfold HasAnnotation
  infer_instance

end Snapshot

/-! ## Mainline query judgments -/

/-- Fuel-indexed closed `get-type` meaning.  Recursive calls always inspect
strict subterms.  The public judgment below supplies more fuel than the term's
structural size, so the zero case is reached only after exhausting a malformed
external budget; it retains PeTTa's `%Undefined%` fallback. -/
def GetTypeAtDepth (snapshot : Snapshot) : Nat → Term → Term → Prop
  | 0, _, expected => expected = undefinedType
  | fuel + 1, value, expected =>
      expected = undefinedType ∨
        snapshot.HasAnnotation value expected ∨
        match value with
        | .variable _ => True
        | .number _ => expected = numberType
        | .string _ => expected = stringType
        | .atom "true" => expected = boolType
        | .atom "false" => expected = boolType
        | .atom _ => False
        | .list elements =>
            let functionAt : Term → Prop := fun resultType =>
              match elements with
              | .atom function :: arguments =>
                  ∃ declaration ∈ snapshot.declarations,
                    declaration.function = function ∧
                    declaration.outputType = resultType ∧
                      List.Forall₂
                        (GetTypeAtDepth snapshot fuel)
                        arguments declaration.inputTypes
              | _ => False
            let hasFunction : Prop :=
              match elements with
              | .atom function :: arguments =>
                  ∃ declaration ∈ snapshot.declarations,
                    declaration.function = function ∧
                      List.Forall₂
                        (GetTypeAtDepth snapshot fuel)
                        arguments declaration.inputTypes
              | _ => False
            functionAt expected ∨
              (¬ hasFunction ∧
                match expected with
                | .list expectedElements =>
                    List.Forall₂
                      (GetTypeAtDepth snapshot fuel)
                      elements expectedElements
                | _ => False)

/-- Exact closed, resolved-declaration fragment of mainline `get-type/2`. -/
def GetType (snapshot : Snapshot) (value expected : Term) : Prop :=
  GetTypeAtDepth snapshot (value.height + 1) value expected

private def decidableForall₂ {leftType rightType : Type}
    (relation : leftType → rightType → Prop)
    (decidableRelation : ∀ left right, Decidable (relation left right)) :
    (left : List leftType) → (right : List rightType) →
      Decidable (List.Forall₂ relation left right)
  | [], [] => isTrue .nil
  | [], _ :: _ => isFalse (by intro proof; cases proof)
  | _ :: _, [] => isFalse (by intro proof; cases proof)
  | leftHead :: leftTail, rightHead :: rightTail =>
      match decidableRelation leftHead rightHead,
          decidableForall₂ relation decidableRelation leftTail rightTail with
      | isTrue headProof, isTrue tailProof =>
          isTrue (.cons headProof tailProof)
      | isFalse headFailure, _ =>
          isFalse (by intro proof; cases proof; contradiction)
      | _, isFalse tailFailure =>
          isFalse (by intro proof; cases proof; contradiction)

private def decidableExistsMem {elementType : Type}
    (predicate : elementType → Prop)
    (decidablePredicate : ∀ element, Decidable (predicate element)) :
    (elements : List elementType) →
      Decidable (∃ element ∈ elements, predicate element)
  | [] => isFalse (by simp)
  | head :: tail =>
      match decidablePredicate head,
          decidableExistsMem predicate decidablePredicate tail with
      | isTrue headProof, _ =>
          isTrue ⟨head, by simp, headProof⟩
      | _, isTrue tailProof =>
          isTrue (by
            rcases tailProof with ⟨element, member, proof⟩
            exact ⟨element, by simp [member], proof⟩)
      | isFalse headFailure, isFalse tailFailure =>
          isFalse (by
            rintro ⟨element, member, proof⟩
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact headFailure proof
            · exact tailFailure ⟨element, member, proof⟩)

private def decidableGetTypeAtDepth (snapshot : Snapshot) :
    (fuel : Nat) → (value expected : Term) →
      Decidable (GetTypeAtDepth snapshot fuel value expected)
  | 0, value, expected => by
      simp only [GetTypeAtDepth]
      infer_instance
  | fuel + 1, value, expected => by
      letI (child expectedChild : Term) :
          Decidable (GetTypeAtDepth snapshot fuel child expectedChild) :=
        decidableGetTypeAtDepth snapshot fuel child expectedChild
      letI (children expectedChildren : List Term) :
          Decidable
            (List.Forall₂ (GetTypeAtDepth snapshot fuel)
              children expectedChildren) :=
        decidableForall₂ (GetTypeAtDepth snapshot fuel)
          (fun child expectedChild =>
            decidableGetTypeAtDepth snapshot fuel child expectedChild)
          children expectedChildren
      letI declarationResultDecidable
          (function : String) (arguments : List Term) (resultType : Term) :
          Decidable
            (∃ declaration ∈ snapshot.declarations,
              declaration.function = function ∧
              declaration.outputType = resultType ∧
                List.Forall₂ (GetTypeAtDepth snapshot fuel)
                  arguments declaration.inputTypes) :=
        decidableExistsMem
          (fun declaration =>
            declaration.function = function ∧
            declaration.outputType = resultType ∧
              List.Forall₂ (GetTypeAtDepth snapshot fuel)
                arguments declaration.inputTypes)
          (fun _ => by infer_instance) snapshot.declarations
      letI declarationInputDecidable
          (function : String) (arguments : List Term) :
          Decidable
            (∃ declaration ∈ snapshot.declarations,
              declaration.function = function ∧
                List.Forall₂ (GetTypeAtDepth snapshot fuel)
                  arguments declaration.inputTypes) :=
        decidableExistsMem
          (fun declaration =>
            declaration.function = function ∧
              List.Forall₂ (GetTypeAtDepth snapshot fuel)
                arguments declaration.inputTypes)
          (fun _ => by infer_instance) snapshot.declarations
      simp only [GetTypeAtDepth]
      cases value with
      | «variable» _ => simp only; infer_instance
      | number _ => simp only; infer_instance
      | string _ => simp only; infer_instance
      | atom name =>
          by_cases isTrueName : name = "true"
          · subst name
            simp only
            infer_instance
          · by_cases isFalseName : name = "false"
            · subst name
              simp only
              infer_instance
            · simp only
              infer_instance
      | list elements =>
          cases elements with
          | nil => cases expected <;> simp only <;> infer_instance
          | cons head _ =>
              cases head <;> cases expected <;> simp only <;> infer_instance

instance (snapshot : Snapshot) (value expected : Term) :
    Decidable (GetType snapshot value expected) := by
  unfold GetType
  exact decidableGetTypeAtDepth snapshot (value.height + 1) value expected

/-- Exact closed fragment of mainline `get-metatype/2`. -/
def GetMetatype (snapshot : Snapshot) (value expected : Term) : Prop :=
  match value with
  | .variable _ => expected = variableMetaType
  | .number _ => expected = groundedMetaType
  | .string _ => expected = groundedMetaType
  | .atom "true" => expected = groundedMetaType
  | .atom "false" => expected = groundedMetaType
  | .atom name =>
      if name ∈ snapshot.registeredFunctions then
        expected = groundedMetaType
      else
        expected = symbolMetaType
  | .list _ => expected = expressionMetaType

instance (snapshot : Snapshot) (value expected : Term) :
    Decidable (GetMetatype snapshot value expected) := by
  unfold GetMetatype
  split <;> infer_instance

inductive QueryKind where
  | getType
  | getMetatype
deriving DecidableEq, Repr

structure Query where
  snapshot : Snapshot
  kind : QueryKind
  value : Term
  expected : Term
deriving DecidableEq, Repr

/-- A query is meaningful only at a well-formed revision and according to the
selected mainline relation. -/
def Query.Holds (query : Query) : Prop :=
  query.snapshot.WellFormed ∧
    match query.kind with
    | .getType => GetType query.snapshot query.value query.expected
    | .getMetatype =>
        GetMetatype query.snapshot query.value query.expected

instance (query : Query) : Decidable query.Holds := by
  unfold Query.Holds
  split <;> infer_instance

def queryDecision (query : Query) : Bool := decide query.Holds

theorem queryDecision_correct (query : Query) :
    queryDecision query = true ↔ query.Holds := by
  exact decide_eq_true_iff

def queryKernel :
    Checker.DecisionKernel Query Query.Holds where
  decide := queryDecision
  correct := queryDecision_correct

/-! ## Operational query GSLT and generated native type -/

structure Machine where
  query : Query
  pending : Bool
deriving DecidableEq, Repr

def MachineStep (source target : Machine) : Prop :=
  source.pending = true ∧ source.query.Holds ∧
    target = ⟨source.query, false⟩

instance (source target : Machine) : Decidable (MachineStep source target) := by
  unfold MachineStep
  infer_instance

def queryGSLT : GSLT where
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

def stepDecision : EffectiveStructure.StepDecision queryGSLT where
  decideStep source target := decide (MachineStep source target)
  correct := by
    intro source target
    exact decide_eq_true_iff

/-- The OSLF-generated exact-target NTT accepts exactly one successful
mainline type-query transition. -/
theorem decideStep_iff_ntt (source target : Machine) :
    stepDecision.decideStep source target = true ↔
      (gsltOSLF queryGSLT).satisfies source
        (exactTargetNativeType queryGSLT target).pred := by
  rw [stepDecision.correct, satisfies_exactTargetNativeType_iff_step]

/-! ## Discriminating query canaries -/

namespace Canary

def addDeclaration : ArrowDeclaration :=
  ⟨10, "+", [numberType, numberType], numberType⟩

def snapshot : Snapshot :=
  ⟨7, [addDeclaration], [], ["+"]⟩

def addition : Term :=
  .list [.atom "+", .number "2", .number "3"]

def additionQuery : Query :=
  ⟨snapshot, .getType, addition, numberType⟩

theorem addition_query_accepted : queryDecision additionQuery = true := by
  decide

/-- The result type is derived from the selected arrow declaration and both
recursive argument checks; changing it is rejected. -/
def wrongAdditionQuery : Query :=
  ⟨snapshot, .getType, addition, boolType⟩

theorem wrong_addition_type_rejected :
    queryDecision wrongAdditionQuery = false := by
  decide

/-- When no function type applies, a list receives the elementwise list of
its members' types.  Unknown symbols contribute `%Undefined%`. -/
def structuralQuery : Query :=
  ⟨snapshot, .getType, .list [.atom "a", .string "b"],
    .list [undefinedType, stringType]⟩

theorem structural_query_accepted :
    queryDecision structuralQuery = true := by
  decide

/-- Registered function symbols have grounded metatype. -/
def registeredFunctionQuery : Query :=
  ⟨snapshot, .getMetatype, .atom "+", groundedMetaType⟩

theorem registered_function_metatype_accepted :
    queryDecision registeredFunctionQuery = true := by
  decide

/-- An ordinary symbol does not have grounded metatype. -/
def ordinarySymbolWrongQuery : Query :=
  ⟨snapshot, .getMetatype, .atom "a", groundedMetaType⟩

theorem ordinary_symbol_grounded_rejected :
    queryDecision ordinarySymbolWrongQuery = false := by
  decide

end Canary

#print axioms queryDecision_correct
#print axioms decideStep_iff_ntt
#print axioms Canary.addition_query_accepted
#print axioms Canary.wrong_addition_type_rejected
#print axioms Canary.structural_query_accepted

end Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
