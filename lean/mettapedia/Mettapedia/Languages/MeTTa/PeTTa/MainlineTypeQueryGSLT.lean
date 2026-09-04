import Mettapedia.GSLT.LanguageDef.CertificateGSLTFiniteTraceAuthority
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardReferenceAuthority

/-!
# Closed mainline PeTTa type queries as an operational GSLT

This module presents the closed, resolved-declaration fragment of the type
queries used by mainline PeTTa.  It follows the clause order of `get-type` and
`get-metatype` rather than the optional `typecheck-v2` or `typecheck-v3`
languages.

The updateable reference baseline for this presentation is commit
`91c27146b129f4d54776362ddb58898568f4665f`, retained on the project fork as
branch `fix/minimal-space-owned-eval-20260827` and published by upstream review
ref `refs/pull/219/head`.  The complete navigable clause ledger is
`MainlineCallGuardReferenceAuthority.clauseTable`; in particular, the modeled
query clauses are `src/metta.pl:181-215` (`get-type`, `space-get-type`, and
their candidate relations) and `src/metta.pl:216-223` (`get-metatype`).
Moving this baseline requires rechecking that ledger and rerunning the
maintained cross-runtime fixture gate; the commit records qualification, not a
promise that mainline PeTTa will stop evolving.

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

/-- Whether the subject has any authored type annotation.  This is the exact
fallback discriminator for ordinary atom subjects; primitive and list values
have earlier candidate clauses. -/
def HasAnnotationSubject (snapshot : Snapshot) (subject : Term) : Prop :=
  ∃ annotation ∈ snapshot.annotations, annotation.subject = subject

instance (snapshot : Snapshot) (subject : Term) :
    Decidable (snapshot.HasAnnotationSubject subject) := by
  unfold HasAnnotationSubject
  infer_instance

theorem hasAnnotationSubject_iff_exists_type
    (snapshot : Snapshot) (subject : Term) :
    snapshot.HasAnnotationSubject subject ↔
      ∃ type, snapshot.HasAnnotation subject type := by
  constructor
  · rintro ⟨annotation, member, subjectEqual⟩
    exact ⟨annotation.type, annotation, member, subjectEqual, rfl⟩
  · rintro ⟨_, annotation, member, subjectEqual, _⟩
    exact ⟨annotation, member, subjectEqual⟩

end Snapshot

/-! ## Mainline query judgments -/

/-- Candidate relation for one `get_type_candidate/2` call.  The child relation
is supplied explicitly so the fuel-indexed public query can recurse only on
strict subterms.  Primitive cuts are represented by keeping ordinary
annotations out of the number, string, and Boolean cases. -/
def TypeCandidateUsing (snapshot : Snapshot)
    (childType : Term → Term → Prop) (value expected : Term) : Prop :=
  match value with
  | .variable _ => True
  | .number _ => expected = numberType
  | .string _ => expected = stringType
  | .atom "true" => expected = boolType
  | .atom "false" => expected = boolType
  | .atom name => snapshot.HasAnnotation (.atom name) expected
  | .list elements =>
      let functionAt : Term → Prop := fun resultType =>
        match elements with
        | .atom function :: arguments =>
            ∃ declaration ∈ snapshot.declarations,
              declaration.function = function ∧
              declaration.outputType = resultType ∧
                List.Forall₂ childType arguments declaration.inputTypes
        | _ => False
      let hasFunction : Prop :=
        match elements with
        | .atom function :: arguments =>
            ∃ declaration ∈ snapshot.declarations,
              declaration.function = function ∧
                List.Forall₂ childType arguments declaration.inputTypes
        | _ => False
      functionAt expected ∨
        (¬ hasFunction ∧
          match expected with
          | .list expectedElements =>
              List.Forall₂ childType elements expectedElements
          | _ => False) ∨
        snapshot.HasAnnotation (.list elements) expected

/-- Whether `get_type_candidate/2` has at least one solution.  Closed proper
lists always have an elementwise candidate because each child query itself
falls back when necessary. -/
def HasTypeCandidate (snapshot : Snapshot) : Term → Prop
  | .variable _ | .number _ | .string _ => True
  | .atom "true" | .atom "false" => True
  | .atom name => snapshot.HasAnnotationSubject (.atom name)
  | .list _ => True

instance (snapshot : Snapshot) (value : Term) :
    Decidable (HasTypeCandidate snapshot value) := by
  unfold HasTypeCandidate
  split <;> infer_instance

/-- Fuel-indexed closed `get-type` meaning.  `%Undefined%` is available only
when the candidate relation has no solution, matching the source soft cut.
Recursive calls inspect strict subterms.  The public judgment supplies more
fuel than the term's structural height. -/
def GetTypeAtDepth (snapshot : Snapshot) : Nat → Term → Term → Prop
  | 0, _, expected => expected = undefinedType
  | fuel + 1, value, expected =>
      TypeCandidateUsing snapshot (GetTypeAtDepth snapshot fuel)
          value expected ∨
        (¬ HasTypeCandidate snapshot value ∧ expected = undefinedType)

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
      | «variable» _ =>
          simp only [TypeCandidateUsing, HasTypeCandidate]
          infer_instance
      | number _ =>
          simp only [TypeCandidateUsing, HasTypeCandidate]
          infer_instance
      | string _ =>
          simp only [TypeCandidateUsing, HasTypeCandidate]
          infer_instance
      | atom name =>
          by_cases isTrueName : name = "true"
          · subst name
            simp only [TypeCandidateUsing, HasTypeCandidate]
            infer_instance
          · by_cases isFalseName : name = "false"
            · subst name
              simp only [TypeCandidateUsing, HasTypeCandidate]
              infer_instance
            · simp only [TypeCandidateUsing, HasTypeCandidate]
              infer_instance
      | list elements =>
          cases elements with
          | nil =>
              cases expected <;>
                simp only [TypeCandidateUsing, HasTypeCandidate] <;>
                infer_instance
          | cons head tail =>
              cases head <;> cases expected <;>
                simp only [TypeCandidateUsing, HasTypeCandidate] <;>
                infer_instance

instance (snapshot : Snapshot) (value expected : Term) :
    Decidable (GetType snapshot value expected) := by
  unfold GetType
  exact decidableGetTypeAtDepth snapshot (value.height + 1) value expected

private theorem forall₂_exists_right {leftType rightType : Type}
    (relation : leftType → rightType → Prop)
    (rightExists : ∀ left, ∃ right, relation left right) :
    ∀ lefts, ∃ rights, List.Forall₂ relation lefts rights
  | [] => ⟨[], .nil⟩
  | head :: tail => by
      rcases rightExists head with ⟨rightHead, headRelated⟩
      rcases forall₂_exists_right relation rightExists tail with
        ⟨rightTail, tailRelated⟩
      exact ⟨rightHead :: rightTail, .cons headRelated tailRelated⟩

/-- Every closed, fuel-indexed query has at least one result.  The list case
constructs an elementwise type when no function declaration applies; this is
the reason closed proper lists always have a candidate before the public
fallback is considered. -/
private theorem getTypeAtDepth_exists (snapshot : Snapshot) :
    ∀ fuel value, ∃ expected, GetTypeAtDepth snapshot fuel value expected := by
  intro fuel
  induction fuel with
  | zero =>
      intro value
      exact ⟨undefinedType, rfl⟩
  | succ fuel childExists =>
      intro value
      cases value with
      | «variable» name =>
          exact ⟨undefinedType, Or.inl (by
            simp only [TypeCandidateUsing])⟩
      | number lexeme =>
          exact ⟨numberType, Or.inl rfl⟩
      | string text =>
          exact ⟨stringType, Or.inl rfl⟩
      | atom name =>
          by_cases isTrueName : name = "true"
          · subst name
            exact ⟨boolType, Or.inl rfl⟩
          · by_cases isFalseName : name = "false"
            · subst name
              exact ⟨boolType, Or.inl rfl⟩
            · by_cases annotated :
                  snapshot.HasAnnotationSubject (.atom name)
              · rw [Snapshot.hasAnnotationSubject_iff_exists_type] at annotated
                rcases annotated with ⟨expected, annotation⟩
                refine ⟨expected, Or.inl ?_⟩
                simpa [TypeCandidateUsing, isTrueName, isFalseName] using
                  annotation
              · refine ⟨undefinedType, Or.inr ⟨?_, rfl⟩⟩
                simpa [HasTypeCandidate, isTrueName, isFalseName] using
                  annotated
      | list elements =>
          let functionAt : Term → Prop := fun resultType =>
            match elements with
            | .atom function :: arguments =>
                ∃ declaration ∈ snapshot.declarations,
                  declaration.function = function ∧
                  declaration.outputType = resultType ∧
                    List.Forall₂ (GetTypeAtDepth snapshot fuel)
                      arguments declaration.inputTypes
            | _ => False
          let hasFunction : Prop :=
            match elements with
            | .atom function :: arguments =>
                ∃ declaration ∈ snapshot.declarations,
                  declaration.function = function ∧
                    List.Forall₂ (GetTypeAtDepth snapshot fuel)
                      arguments declaration.inputTypes
            | _ => False
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
          letI : Decidable hasFunction := by
            unfold hasFunction
            split <;> infer_instance
          by_cases functionApplies : hasFunction
          · have outputExists : ∃ expected, functionAt expected := by
              cases elements with
              | nil => simp [hasFunction] at functionApplies
              | cons head arguments =>
                  cases head with
                  | atom function =>
                      change ∃ declaration ∈ snapshot.declarations,
                        declaration.function = function ∧
                          List.Forall₂ (GetTypeAtDepth snapshot fuel)
                            arguments declaration.inputTypes at functionApplies
                      rcases functionApplies with
                        ⟨declaration, member, functionEqual, argumentsTyped⟩
                      exact ⟨declaration.outputType, declaration, member,
                        functionEqual, rfl, argumentsTyped⟩
                  | «variable» name =>
                      simp [hasFunction] at functionApplies
                  | number lexeme =>
                      simp [hasFunction] at functionApplies
                  | string text =>
                      simp [hasFunction] at functionApplies
                  | list nested =>
                      simp [hasFunction] at functionApplies
            rcases outputExists with ⟨expected, outputTyped⟩
            refine ⟨expected, Or.inl ?_⟩
            unfold TypeCandidateUsing
            left
            simpa [functionAt] using outputTyped
          · rcases forall₂_exists_right
                (GetTypeAtDepth snapshot fuel) childExists elements with
              ⟨expectedElements, elementsTyped⟩
            refine ⟨.list expectedElements, Or.inl ?_⟩
            change functionAt (.list expectedElements) ∨
              ((¬ hasFunction ∧
                List.Forall₂ (GetTypeAtDepth snapshot fuel)
                  elements expectedElements) ∨
                snapshot.HasAnnotation (.list elements)
                  (.list expectedElements))
            exact Or.inr (Or.inl ⟨functionApplies, elementsTyped⟩)

/-- The finite discriminator used by the executable decision procedure is
extensionally exact: it holds precisely when the source candidate relation has
some result. -/
theorem hasTypeCandidate_iff_exists_typeCandidate
    (snapshot : Snapshot) (fuel : Nat) (value : Term) :
    HasTypeCandidate snapshot value ↔
      ∃ expected,
        TypeCandidateUsing snapshot (GetTypeAtDepth snapshot fuel)
          value expected := by
  constructor
  · intro hasCandidate
    rcases getTypeAtDepth_exists snapshot (fuel + 1) value with
      ⟨expected, candidateOrFallback⟩
    rcases candidateOrFallback with candidate | ⟨noCandidate, _⟩
    · exact ⟨expected, candidate⟩
    · exact False.elim (noCandidate hasCandidate)
  · rintro ⟨expected, candidate⟩
    cases value with
    | «variable» name => trivial
    | number lexeme => trivial
    | string text => trivial
    | atom name =>
        by_cases isTrueName : name = "true"
        · subst name
          trivial
        · by_cases isFalseName : name = "false"
          · subst name
            trivial
          · simp only [HasTypeCandidate]
            simp only [TypeCandidateUsing] at candidate
            rcases candidate with
              ⟨annotation, member, subjectEqual, typeEqual⟩
            exact ⟨annotation, member, subjectEqual⟩
    | list elements => trivial

/-- Exact soft-cut factorization of one positive-fuel query: either the
candidate relation supplies this result, or no candidate exists and the result
is `%Undefined%`. -/
theorem getTypeAtDepth_candidate_or_fallback
    (snapshot : Snapshot) (fuel : Nat) (value expected : Term) :
    GetTypeAtDepth snapshot (fuel + 1) value expected ↔
      TypeCandidateUsing snapshot (GetTypeAtDepth snapshot fuel)
          value expected ∨
        ((¬ ∃ candidate,
            TypeCandidateUsing snapshot (GetTypeAtDepth snapshot fuel)
              value candidate) ∧ expected = undefinedType) := by
  change
    (TypeCandidateUsing snapshot (GetTypeAtDepth snapshot fuel)
        value expected ∨
      (¬ HasTypeCandidate snapshot value ∧ expected = undefinedType)) ↔ _
  rw [hasTypeCandidate_iff_exists_typeCandidate]

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
  rw [stepDecision.correct]
  exact (satisfies_exactTargetNativeType_iff_step
    queryGSLT source target).symm

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

/-- A later ordinary annotation cannot override the cut in the primitive
number candidate clause. -/
def primitiveCutAnnotation : TypeAnnotation :=
  ⟨20, .number "3", groundedMetaType⟩

def primitiveCutSnapshot : Snapshot :=
  ⟨8, [], [primitiveCutAnnotation], []⟩

def primitiveNumberQuery : Query :=
  ⟨primitiveCutSnapshot, .getType, .number "3", numberType⟩

def primitiveAnnotationOverrideQuery : Query :=
  ⟨primitiveCutSnapshot, .getType, .number "3", groundedMetaType⟩

def primitiveUndefinedQuery : Query :=
  ⟨primitiveCutSnapshot, .getType, .number "3", undefinedType⟩

def unknownAtomFallbackQuery : Query :=
  ⟨primitiveCutSnapshot, .getType, .atom "untyped", undefinedType⟩

theorem primitive_number_query_accepted :
    queryDecision primitiveNumberQuery = true := by
  decide

theorem primitive_annotation_override_rejected :
    queryDecision primitiveAnnotationOverrideQuery = false := by
  decide

theorem primitive_undefined_fallback_rejected :
    queryDecision primitiveUndefinedQuery = false := by
  decide

theorem unknown_atom_fallback_accepted :
    queryDecision unknownAtomFallbackQuery = true := by
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
#print axioms hasTypeCandidate_iff_exists_typeCandidate
#print axioms getTypeAtDepth_candidate_or_fallback
#print axioms Canary.addition_query_accepted
#print axioms Canary.wrong_addition_type_rejected
#print axioms Canary.structural_query_accepted
#print axioms Canary.primitive_number_query_accepted
#print axioms Canary.primitive_annotation_override_rejected
#print axioms Canary.primitive_undefined_fallback_rejected
#print axioms Canary.unknown_atom_fallback_accepted

end Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
