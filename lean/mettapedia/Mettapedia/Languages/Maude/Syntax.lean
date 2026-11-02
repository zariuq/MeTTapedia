import Mathlib.Data.List.Basic

/-! The first-order, many-sorted IR for the Maude core. Operator identities
are declaration identities, distinct from their source spellings: overloaded
or imported operators must not acquire each other's axioms. This IR contains
neither packed grammar trees nor runtime search continuations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

inductive Term where
  | var (name : String)
  | app (operatorId : String) (arguments : List Term)
  deriving Repr, BEq

structure Attributes where
  associative : Bool := false
  commutative : Bool := false
  identity : Option Term := none
  constructor : Bool := false
  deriving Repr, BEq

structure Operator where
  id : String
  sourceName : String
  arguments : List String
  result : String
  attributes : Attributes := {}
  deriving Repr, BEq

structure Signature where
  sorts : List String
  operators : List Operator
  deriving Repr, BEq

abbrev VariableContext := List (String × String)
abbrev Valuation := String → Term

def Signature.operator? (signature : Signature) (id : String) : Option Operator :=
  signature.operators.find? (fun declaration => declaration.id == id)

def Term.substitute (assignment : Valuation) : Term → Term
  | .var name => assignment name
  | .app id arguments => .app id (arguments.map (Term.substitute assignment))

def Term.variables : Term → List String
  | .var name => [name]
  | .app _ arguments => arguments.flatMap Term.variables

def inferSort? (signature : Signature) (context : VariableContext) : Term → Option String
  | .var name => context.lookup name
  | .app id arguments => do
      let declaration ← signature.operator? id
      let actual ← arguments.mapM (inferSort? signature context)
      if actual == declaration.arguments then some declaration.result else none

/-- Associativity and a two-sided identity require a closed binary operation.
Commutativity alone requires equal argument sorts; the result may differ. -/
def Operator.checkAlgebraShape (declaration : Operator) : Bool :=
  ((!(declaration.attributes.associative || declaration.attributes.identity.isSome)) ||
    declaration.arguments == [declaration.result, declaration.result]) &&
  (!declaration.attributes.commutative || match declaration.arguments with
    | [first, second] => first == second
    | _ => false)

def Signature.check (signature : Signature) : Bool :=
  decide signature.sorts.Nodup && decide (signature.operators.map Operator.id).Nodup &&
  signature.operators.all fun declaration =>
    signature.sorts.contains declaration.result && declaration.arguments.all signature.sorts.contains &&
    declaration.checkAlgebraShape &&
    match declaration.attributes.identity with
    | none => true
    | some unit => unit.variables.isEmpty && inferSort? signature [] unit == some declaration.result &&
        match unit with
        | .app root _ => root != declaration.id
        | .var _ => false

inductive HasSort (signature : Signature) (context : VariableContext) : Term → String → Prop where
  | var {name sort} : context.lookup name = some sort → HasSort signature context (.var name) sort
  | app {declaration : Operator} {arguments : List Term} :
      declaration ∈ signature.operators →
      List.Forall₂ (HasSort signature context) arguments declaration.arguments →
      HasSort signature context (.app declaration.id arguments) declaration.result

theorem HasSort.operator_origin {signature : Signature} {context : VariableContext}
    {term : Term} {sort id : String} {arguments : List Term}
    (typed : HasSort signature context term sort) (shape : term = .app id arguments) :
    ∃ declaration ∈ signature.operators, declaration.id = id ∧ declaration.result = sort := by
  cases typed with
  | var _ => cases shape
  | app member _ => exact ⟨_, member, (Term.app.inj shape).1, rfl⟩

theorem HasSort.operator_arguments {signature : Signature} {context : VariableContext}
    {term : Term} {sort id : String} {arguments : List Term}
    (typed : HasSort signature context term sort) (shape : term = .app id arguments) :
    ∃ declaration ∈ signature.operators, declaration.id = id ∧ declaration.result = sort ∧
      List.Forall₂ (HasSort signature context) arguments declaration.arguments := by
  cases typed with
  | var _ => cases shape
  | app member argumentsTyped =>
      obtain ⟨label, sameArguments⟩ := Term.app.inj shape
      exact ⟨_, member, label, rfl, sameArguments ▸ argumentsTyped⟩

structure Condition where
  left : Term
  right : Term
  deriving Repr, BEq

structure Row where
  name : String
  formals : VariableContext
  conditions : List Condition := []
  left : Term
  right : Term
  deriving Repr, BEq

def sameSort (signature : Signature) (context : VariableContext) (left right : Term) : Bool :=
  match inferSort? signature context left, inferSort? signature context right with
  | some first, some second => first == second
  | _, _ => false

def Row.check (signature : Signature) (row : Row) : Bool :=
  decide (row.formals.map Prod.fst).Nodup && row.formals.all (fun entry => signature.sorts.contains entry.2) &&
  sameSort signature row.formals row.left row.right &&
  row.conditions.all (fun condition => sameSort signature row.formals condition.left condition.right)

def Row.usedContext (row : Row) : VariableContext :=
  let used := row.left.variables ++ row.right.variables ++
    row.conditions.flatMap (fun condition => condition.left.variables ++ condition.right.variables)
  row.formals.filter (fun entry => used.contains entry.1)

/-- This is an execution-profile check, not the definition of the equation
theory: conditional terms may require a stronger binding producer. -/
def Row.inputsBound (row : Row) : Bool :=
  (row.right.variables ++ row.conditions.flatMap (fun condition => condition.left.variables ++ condition.right.variables)).all
    (fun name => row.left.variables.contains name)

structure Theory where
  name : String
  signature : Signature
  equations : List Row := []
  rules : List Row := []
  deriving Repr, BEq

def Theory.check (theory : Theory) : Bool :=
  theory.signature.check && theory.equations.all (Row.check theory.signature) &&
    theory.rules.all (Row.check theory.signature)

def TypedValuation (signature : Signature) (context declarations : VariableContext) (assignment : Valuation) : Prop :=
  ∀ name sort, declarations.lookup name = some sort → HasSort signature context (assignment name) sort

end Mettapedia.Languages.Maude
