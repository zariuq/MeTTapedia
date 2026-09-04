import Mettapedia.Logic.HOL.Syntax.Term

/-!
# Named elaboration for intrinsically typed higher-order terms

Source languages ordinarily name binders, while the intrinsic HOL syntax uses
typed de Bruijn variables.  This module separates those two roles.  A
`BinderNames` value is a name decoration over one already fixed type context;
changing the decoration does not change that context.

Elaboration is bidirectional only at the outer boundary: `infer` reconstructs
the intrinsic type of a named term, and `check` compares that type with an
explicit expectation.  Failures distinguish scope, constant lookup, function
shape, and type mismatch.  Successful results are intrinsically scoped and
typed by construction.

The central alpha theorem does not implement textual renaming.  Instead,
`Alpha` relates two named terms when corresponding variable occurrences
resolve to the same intrinsic variable under their respective name
decorations.  Alpha-related terms therefore elaborate to exactly the same
intrinsic term.  Shadowing and a capture-shaped negative control show why the
resolution premise is essential.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NamedElaboration

open Mettapedia.Logic.HOL

universe uBase uVarName uConstName uConst uBind

variable {Base : Type uBase} {VarName : Type uVarName}
variable {ConstName : Type uConstName}

/-! ## Names displayed over an intrinsic context -/

/-- One binder name for every entry of an intrinsic type context.  The head
name belongs to de Bruijn index zero. -/
inductive BinderNames (Base : Type uBase) (Name : Type uVarName) :
    Ctx Base -> Type (max uBase uVarName) where
  | nil : BinderNames Base Name []
  | cons {context : Ctx Base} {type : Ty Base}
      (name : Name) (tail : BinderNames Base Name context) :
      BinderNames Base Name (type :: context)

/-- A variable whose type is retained existentially. -/
abbrev SomeVar {Base : Type uBase} (context : Ctx Base) :=
  Sigma fun type => Var context type

namespace BinderNames

variable {Base : Type uBase} {Name : Type uVarName}

/-- Resolve the nearest binder with the requested name.  Repeated names
therefore have ordinary lexical-shadowing behavior. -/
def lookup? [DecidableEq Name] :
    {context : Ctx Base} -> BinderNames Base Name context -> Name ->
      Option (SomeVar context)
  | [], .nil, _ => none
  | _type :: _context, .cons binder tail, name =>
      if binder = name then
        some ⟨_, .vz⟩
      else
        (lookup? tail name).map fun resolved =>
          ⟨resolved.1, .vs resolved.2⟩

@[simp] theorem lookup?_nil [DecidableEq Name] (name : Name) :
    lookup? (BinderNames.nil : BinderNames Base Name []) name = none :=
  rfl

@[simp] theorem lookup?_cons_self [DecidableEq Name]
    {context : Ctx Base} {type : Ty Base}
    (name : Name) (tail : BinderNames Base Name context) :
    lookup? (BinderNames.cons (type := type) name tail) name =
      some ⟨type, .vz⟩ := by
  simp [lookup?]

@[simp] theorem lookup?_cons_of_ne [DecidableEq Name]
    {context : Ctx Base} {type : Ty Base}
    {binder name : Name} (different : binder ≠ name)
    (tail : BinderNames Base Name context) :
    lookup? (BinderNames.cons (type := type) binder tail) name =
      (lookup? tail name).map fun resolved =>
        ⟨resolved.1, .vs resolved.2⟩ := by
  simp [lookup?, different]

end BinderNames

/-! ## Named surface terms and exact failure reasons -/

/-- A named, type-annotated higher-order source term.  Binders carry domain
types; applications and constant occurrences obtain their types from
elaboration. -/
inductive NamedTerm (Base : Type uBase) (VarName : Type uVarName)
    (ConstName : Type uConstName) where
  | variable (name : VarName)
  | constant (name : ConstName)
  | app (function argument : NamedTerm Base VarName ConstName)
  | lam (binder : VarName) (domain : Ty Base)
      (body : NamedTerm Base VarName ConstName)
  | top
  | bottom
  | and (left right : NamedTerm Base VarName ConstName)
  | or (left right : NamedTerm Base VarName ConstName)
  | imp (antecedent consequent : NamedTerm Base VarName ConstName)
  | not (body : NamedTerm Base VarName ConstName)
  | equal (left right : NamedTerm Base VarName ConstName)
  | forallE (binder : VarName) (domain : Ty Base)
      (body : NamedTerm Base VarName ConstName)
  | existsE (binder : VarName) (domain : Ty Base)
      (body : NamedTerm Base VarName ConstName)
deriving Repr, DecidableEq

/-- One intrinsically typed constant with its type hidden existentially. -/
abbrev SomeConst {Base : Type uBase}
    (Const : Ty Base -> Type uConst) := Sigma Const

/-- A functional constant signature.  Occurrence-bearing declaration lists
belong to source artifacts and may be compiled to this semantic lookup only
after their own consistency checks. -/
abbrev Signature {Base : Type uBase} (ConstName : Type uConstName)
    (Const : Ty Base -> Type uConst) :=
  ConstName -> Option (SomeConst Const)

/-- Exact elaboration failures.  None of these constructors is a theoremhood
or semantic-refutation judgment. -/
inductive Error (Base : Type uBase) (VarName : Type uVarName)
    (ConstName : Type uConstName) where
  | unboundVariable (name : VarName)
  | unknownConstant (name : ConstName)
  | expectedFunction (actual : Ty Base)
  | typeMismatch (expected actual : Ty Base)
deriving Repr, DecidableEq

/-- An intrinsic term together with its inferred type. -/
structure SomeTerm {Base : Type uBase} (Const : Ty Base -> Type uConst)
    (context : Ctx Base) where
  type : Ty Base
  term : Term Const context type

/- Lean's `Except` monad does not currently expose these computation rules to
the simplifier through the `Bind` projection.  Naming them keeps concrete
elaboration canaries kernel-reducible rather than sending them through an
external evaluator. -/
@[simp] theorem except_ok_monad_bind {error input output : Type uBind}
    (value : input) (next : input -> Except error output) :
    ((Except.ok value : Except error input) >>= next) = next value :=
  rfl

@[simp] theorem except_error_monad_bind {error input output : Type uBind}
    (failure : error) (next : input -> Except error output) :
    ((Except.error failure : Except error input) >>= next) = .error failure :=
  rfl

/-- Compare an inferred term with one expected type and transport the term
only along the checked type equality. -/
def expectType [DecidableEq Base]
    {VarName : Type uVarName} {ConstName : Type uConstName}
    {Const : Ty Base -> Type uConst} {context : Ctx Base}
    (expected : Ty Base) (inferred : SomeTerm Const context) :
    Except (Error Base VarName ConstName) (Term Const context expected) :=
  if equal : inferred.type = expected then
    .ok (equal ▸ inferred.term)
  else
    .error (.typeMismatch expected inferred.type)

@[simp] theorem expectType_same [DecidableEq Base]
    {VarName : Type uVarName} {ConstName : Type uConstName}
    {Const : Ty Base -> Type uConst} {context : Ctx Base}
    {type : Ty Base} (term : Term Const context type) :
    expectType (VarName := VarName) (ConstName := ConstName)
      type (SomeTerm.mk type term) = .ok term := by
  simp [expectType]

/-! ## Intrinsically typed elaboration -/

/-- Infer an intrinsic type and term from a named source term. -/
def infer [DecidableEq Base] [DecidableEq VarName]
    {Const : Ty Base -> Type uConst}
    (signature : Signature ConstName Const) {context : Ctx Base}
    (names : BinderNames Base VarName context) :
    NamedTerm Base VarName ConstName ->
      Except (Error Base VarName ConstName) (SomeTerm Const context)
  | .variable name =>
      match names.lookup? name with
      | none => .error (.unboundVariable name)
      | some resolved => .ok ⟨resolved.1, .var resolved.2⟩
  | .constant name =>
      match signature name with
      | none => .error (.unknownConstant name)
      | some resolved => .ok ⟨resolved.1, .const resolved.2⟩
  | .app function argument => do
      let inferredFunction <- infer signature names function
      match inferredFunction with
      | ⟨.arr domain codomain, functionTerm⟩ =>
          let inferredArgument <- infer signature names argument
          let argumentTerm <- expectType domain inferredArgument
          .ok ⟨codomain, .app functionTerm argumentTerm⟩
      | ⟨actual, _functionTerm⟩ =>
          .error (.expectedFunction actual)
  | .lam binder domain body => do
      let inferredBody <-
        infer signature (BinderNames.cons (type := domain) binder names) body
      .ok ⟨.arr domain inferredBody.type, .lam inferredBody.term⟩
  | .top => .ok ⟨.prop, .top⟩
  | .bottom => .ok ⟨.prop, .bot⟩
  | .and left right => do
      let inferredLeft <- infer signature names left
      let leftTerm <- expectType .prop inferredLeft
      let inferredRight <- infer signature names right
      let rightTerm <- expectType .prop inferredRight
      .ok ⟨.prop, .and leftTerm rightTerm⟩
  | .or left right => do
      let inferredLeft <- infer signature names left
      let leftTerm <- expectType .prop inferredLeft
      let inferredRight <- infer signature names right
      let rightTerm <- expectType .prop inferredRight
      .ok ⟨.prop, .or leftTerm rightTerm⟩
  | .imp antecedent consequent => do
      let inferredAntecedent <- infer signature names antecedent
      let antecedentTerm <- expectType .prop inferredAntecedent
      let inferredConsequent <- infer signature names consequent
      let consequentTerm <- expectType .prop inferredConsequent
      .ok ⟨.prop, .imp antecedentTerm consequentTerm⟩
  | .not body => do
      let inferredBody <- infer signature names body
      let bodyTerm <- expectType .prop inferredBody
      .ok ⟨.prop, .not bodyTerm⟩
  | .equal left right => do
      let inferredLeft <- infer signature names left
      let inferredRight <- infer signature names right
      let rightTerm <- expectType inferredLeft.type inferredRight
      .ok ⟨.prop, .eq inferredLeft.term rightTerm⟩
  | .forallE binder domain body => do
      let inferredBody <-
        infer signature (BinderNames.cons (type := domain) binder names) body
      let bodyTerm <- expectType .prop inferredBody
      .ok ⟨.prop, .all bodyTerm⟩
  | .existsE binder domain body => do
      let inferredBody <-
        infer signature (BinderNames.cons (type := domain) binder names) body
      let bodyTerm <- expectType .prop inferredBody
      .ok ⟨.prop, .ex bodyTerm⟩
termination_by term => sizeOf term

/-- Check a named source term against one explicit intrinsic type. -/
def check [DecidableEq Base] [DecidableEq VarName]
    {Const : Ty Base -> Type uConst}
    (signature : Signature ConstName Const) {context : Ctx Base}
    (names : BinderNames Base VarName context)
    (term : NamedTerm Base VarName ConstName) (expected : Ty Base) :
    Except (Error Base VarName ConstName) (Term Const context expected) := do
  let inferred <- infer signature names term
  expectType expected inferred

theorem infer_variable_of_lookup [DecidableEq Base] [DecidableEq VarName]
    {Const : Ty Base -> Type uConst}
    (signature : Signature ConstName Const) {context : Ctx Base}
    (names : BinderNames Base VarName context) (name : VarName)
    {type : Ty Base} {intrinsicVar : Var context type}
    (resolved : names.lookup? name = some ⟨type, intrinsicVar⟩) :
    infer signature names (.variable name) =
      .ok ⟨type, .var intrinsicVar⟩ := by
  simp [infer, resolved]

theorem infer_unbound_variable [DecidableEq Base] [DecidableEq VarName]
    {Const : Ty Base -> Type uConst}
    (signature : Signature ConstName Const) {context : Ctx Base}
    (names : BinderNames Base VarName context) (name : VarName)
    (unbound : names.lookup? name = none) :
    infer signature names (.variable name) =
      .error (.unboundVariable name) := by
  simp [infer, unbound]

theorem infer_unknown_constant [DecidableEq Base] [DecidableEq VarName]
    {Const : Ty Base -> Type uConst}
    (signature : Signature ConstName Const) {context : Ctx Base}
    (names : BinderNames Base VarName context) (name : ConstName)
    (unknown : signature name = none) :
    infer signature names (.constant name) =
      .error (.unknownConstant name) := by
  simp [infer, unknown]

/-! ## Alpha equivalence by common intrinsic resolution -/

/-- Two named terms are alpha-related when corresponding variable
occurrences resolve to the same intrinsic variable.  Binder names may differ;
constant identities, operators, and binder types do not. -/
inductive Alpha [DecidableEq VarName] :
    {context : Ctx Base} ->
      BinderNames Base VarName context ->
      BinderNames Base VarName context ->
      NamedTerm Base VarName ConstName ->
      NamedTerm Base VarName ConstName -> Prop where
  | var {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftName rightName : VarName} {type : Ty Base}
      {intrinsicVar : Var context type}
      (leftResolves : leftNames.lookup? leftName = some ⟨type, intrinsicVar⟩)
      (rightResolves : rightNames.lookup? rightName = some ⟨type, intrinsicVar⟩) :
      Alpha leftNames rightNames (.variable leftName) (.variable rightName)
  | constant {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      (name : ConstName) :
      Alpha leftNames rightNames (.constant name) (.constant name)
  | app {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftFunction rightFunction leftArgument rightArgument}
      (functionAlpha : Alpha leftNames rightNames leftFunction rightFunction)
      (argumentAlpha : Alpha leftNames rightNames leftArgument rightArgument) :
      Alpha leftNames rightNames
        (.app leftFunction leftArgument) (.app rightFunction rightArgument)
  | lam {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftBinder rightBinder : VarName} {domain : Ty Base}
      {leftBody rightBody}
      (bodyAlpha : Alpha
        (BinderNames.cons (type := domain) leftBinder leftNames)
        (BinderNames.cons (type := domain) rightBinder rightNames)
        leftBody rightBody) :
      Alpha leftNames rightNames
        (.lam leftBinder domain leftBody) (.lam rightBinder domain rightBody)
  | top {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context} :
      Alpha leftNames rightNames .top .top
  | bottom {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context} :
      Alpha leftNames rightNames .bottom .bottom
  | and {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftFirst rightFirst leftSecond rightSecond}
      (firstAlpha : Alpha leftNames rightNames leftFirst rightFirst)
      (secondAlpha : Alpha leftNames rightNames leftSecond rightSecond) :
      Alpha leftNames rightNames
        (.and leftFirst leftSecond) (.and rightFirst rightSecond)
  | or {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftFirst rightFirst leftSecond rightSecond}
      (firstAlpha : Alpha leftNames rightNames leftFirst rightFirst)
      (secondAlpha : Alpha leftNames rightNames leftSecond rightSecond) :
      Alpha leftNames rightNames
        (.or leftFirst leftSecond) (.or rightFirst rightSecond)
  | imp {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftFirst rightFirst leftSecond rightSecond}
      (firstAlpha : Alpha leftNames rightNames leftFirst rightFirst)
      (secondAlpha : Alpha leftNames rightNames leftSecond rightSecond) :
      Alpha leftNames rightNames
        (.imp leftFirst leftSecond) (.imp rightFirst rightSecond)
  | not {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftBody rightBody}
      (bodyAlpha : Alpha leftNames rightNames leftBody rightBody) :
      Alpha leftNames rightNames (.not leftBody) (.not rightBody)
  | equal {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftFirst rightFirst leftSecond rightSecond}
      (firstAlpha : Alpha leftNames rightNames leftFirst rightFirst)
      (secondAlpha : Alpha leftNames rightNames leftSecond rightSecond) :
      Alpha leftNames rightNames
        (.equal leftFirst leftSecond) (.equal rightFirst rightSecond)
  | forallE {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftBinder rightBinder : VarName} {domain : Ty Base}
      {leftBody rightBody}
      (bodyAlpha : Alpha
        (BinderNames.cons (type := domain) leftBinder leftNames)
        (BinderNames.cons (type := domain) rightBinder rightNames)
        leftBody rightBody) :
      Alpha leftNames rightNames
        (.forallE leftBinder domain leftBody)
        (.forallE rightBinder domain rightBody)
  | existsE {context : Ctx Base}
      {leftNames rightNames : BinderNames Base VarName context}
      {leftBinder rightBinder : VarName} {domain : Ty Base}
      {leftBody rightBody}
      (bodyAlpha : Alpha
        (BinderNames.cons (type := domain) leftBinder leftNames)
        (BinderNames.cons (type := domain) rightBinder rightNames)
        leftBody rightBody) :
      Alpha leftNames rightNames
        (.existsE leftBinder domain leftBody)
        (.existsE rightBinder domain rightBody)

/-- Alpha-related named terms elaborate to exactly the same intrinsic result,
including the same failure if their common structure is ill typed. -/
theorem infer_eq_of_alpha [DecidableEq Base] [DecidableEq VarName]
    {Const : Ty Base -> Type uConst}
    (signature : Signature ConstName Const)
    {context : Ctx Base}
    {leftNames rightNames : BinderNames Base VarName context}
    {left right : NamedTerm Base VarName ConstName}
    (related : Alpha leftNames rightNames left right) :
    infer signature leftNames left = infer signature rightNames right := by
  induction related with
  | var leftResolves rightResolves =>
      simp [infer, leftResolves, rightResolves]
  | constant => simp [infer]
  | app _ _ functionIH argumentIH =>
      simp only [infer, functionIH, argumentIH]
  | lam _ bodyIH =>
      simp only [infer, bodyIH]
  | top => simp [infer]
  | bottom => simp [infer]
  | and _ _ firstIH secondIH =>
      simp only [infer, firstIH, secondIH]
  | or _ _ firstIH secondIH =>
      simp only [infer, firstIH, secondIH]
  | imp _ _ firstIH secondIH =>
      simp only [infer, firstIH, secondIH]
  | not _ bodyIH =>
      simp only [infer, bodyIH]
  | equal _ _ firstIH secondIH =>
      simp only [infer, firstIH, secondIH]
  | forallE _ bodyIH =>
      simp only [infer, bodyIH]
  | existsE _ bodyIH =>
      simp only [infer, bodyIH]

/-- Checking is alpha-invariant for the same reason as inference. -/
theorem check_eq_of_alpha [DecidableEq Base] [DecidableEq VarName]
    {Const : Ty Base -> Type uConst}
    (signature : Signature ConstName Const)
    {context : Ctx Base}
    {leftNames rightNames : BinderNames Base VarName context}
    {left right : NamedTerm Base VarName ConstName}
    (related : Alpha leftNames rightNames left right)
    (expected : Ty Base) :
    check signature leftNames left expected =
      check signature rightNames right expected := by
  simp only [check, infer_eq_of_alpha signature related]

/-! ## Positive and negative canaries -/

namespace Canary

abbrev AtomBase := String
abbrev BinderName := String
abbrev ConstantName := String

def individual : Ty AtomBase := .base "individual"

inductive Constant : Ty AtomBase -> Type where
  | predicate : Constant (.arr individual .prop)

def signature : Signature ConstantName Constant
  | "P" => some ⟨.arr individual .prop, .predicate⟩
  | _ => none

def emptyNames : BinderNames AtomBase BinderName [] := .nil

def identityX : NamedTerm AtomBase BinderName ConstantName :=
  .lam "x" individual (.variable "x")

def identityY : NamedTerm AtomBase BinderName ConstantName :=
  .lam "y" individual (.variable "y")

def identityIntrinsic : Term Constant [] (.arr individual individual) :=
  .lam (.var .vz)

def identityAlpha : Alpha emptyNames emptyNames identityX identityY := by
  apply Alpha.lam
  apply Alpha.var (type := individual) (intrinsicVar := Var.vz)
  · rfl
  · rfl

theorem alpha_identities_elaborate_identically :
    infer signature emptyNames identityX =
        .ok ⟨.arr individual individual, identityIntrinsic⟩ /\
      infer signature emptyNames identityY =
        .ok ⟨.arr individual individual, identityIntrinsic⟩ := by
  constructor
  · simp [infer, identityX, identityIntrinsic, emptyNames]
  · rw [← infer_eq_of_alpha signature identityAlpha]
    simp [infer, identityX, identityIntrinsic, emptyNames]

/-- Nearest-name lookup gives the inner binder, not the shadowed outer one. -/
def shadowed : NamedTerm AtomBase BinderName ConstantName :=
  .lam "x" individual (.lam "x" individual (.variable "x"))

def shadowedIntrinsic :
    Term Constant [] (.arr individual (.arr individual individual)) :=
  .lam (.lam (.var .vz))

theorem shadowing_selects_nearest_binder :
    infer signature emptyNames shadowed =
      .ok ⟨.arr individual (.arr individual individual),
        shadowedIntrinsic⟩ := by
  simp [infer, shadowed, shadowedIntrinsic, emptyNames]

/-- The occurrence of `x` remains tied to the outer binder. -/
def outerReference : NamedTerm AtomBase BinderName ConstantName :=
  .lam "x" individual (.lam "y" individual (.variable "x"))

/-- A capture-shaped textual replacement changes that occurrence to the inner
`y`; it is not alpha-related to `outerReference`. -/
def capturedReference : NamedTerm AtomBase BinderName ConstantName :=
  .lam "y" individual (.lam "y" individual (.variable "y"))

def outerReferenceIntrinsic :
    Term Constant [] (.arr individual (.arr individual individual)) :=
  .lam (.lam (.var (.vs .vz)))

def capturedReferenceIntrinsic :
    Term Constant [] (.arr individual (.arr individual individual)) :=
  .lam (.lam (.var .vz))

theorem capture_shaped_renaming_changes_intrinsic_term :
    infer signature emptyNames outerReference =
        .ok ⟨.arr individual (.arr individual individual),
          outerReferenceIntrinsic⟩ /\
      infer signature emptyNames capturedReference =
        .ok ⟨.arr individual (.arr individual individual),
          capturedReferenceIntrinsic⟩ /\
      outerReferenceIntrinsic ≠ capturedReferenceIntrinsic := by
  constructor
  · simp [infer, outerReference, outerReferenceIntrinsic, emptyNames]
  constructor
  · simp [infer, capturedReference, capturedReferenceIntrinsic, emptyNames]
  · simp [outerReferenceIntrinsic, capturedReferenceIntrinsic]

def propositionIdentity : NamedTerm AtomBase BinderName ConstantName :=
  .forallE "P" .prop
    (.imp (.variable "P") (.variable "P"))

def propositionIdentityIntrinsic : Formula Constant [] :=
  .all (.imp (.var .vz) (.var .vz))

theorem quantified_identity_checks :
    check signature emptyNames propositionIdentity .prop =
      .ok propositionIdentityIntrinsic := by
  simp [check, infer, propositionIdentity, propositionIdentityIntrinsic,
    emptyNames, expectType]

theorem unbound_variable_rejects :
    infer signature emptyNames (.variable "free") =
      .error (.unboundVariable "free") := by
  simp [infer, emptyNames, BinderNames.lookup?]

theorem unknown_constant_rejects :
    infer signature emptyNames (.constant "Q") =
      .error (.unknownConstant "Q") := by
  simp [infer, emptyNames, signature]

theorem proposition_application_rejects :
    infer signature emptyNames (.app .top .top) =
      .error (.expectedFunction (.prop : Ty AtomBase)) := by
  simp [infer, emptyNames]

theorem wrong_argument_type_rejects :
    infer signature emptyNames (.app (.constant "P") .top) =
      .error (.typeMismatch individual .prop) := by
  simp [infer, emptyNames, signature, expectType, individual]

theorem named_elaboration_boundary :
    check signature emptyNames propositionIdentity .prop =
        .ok propositionIdentityIntrinsic /\
      infer signature emptyNames (.variable "free") =
        .error (.unboundVariable "free") /\
      infer signature emptyNames (.app (.constant "P") .top) =
        .error (.typeMismatch individual .prop) /\
      outerReferenceIntrinsic ≠ capturedReferenceIntrinsic := by
  exact ⟨quantified_identity_checks, unbound_variable_rejects,
    wrong_argument_type_rejects,
    capture_shaped_renaming_changes_intrinsic_term.2.2⟩

end Canary

#print axioms infer_eq_of_alpha
#print axioms check_eq_of_alpha
#print axioms Canary.alpha_identities_elaborate_identically
#print axioms Canary.capture_shaped_renaming_changes_intrinsic_term
#print axioms Canary.named_elaboration_boundary

end Mettapedia.Logic.HOL.NamedElaboration
