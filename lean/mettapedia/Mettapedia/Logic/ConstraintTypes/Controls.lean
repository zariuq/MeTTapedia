import Mettapedia.Logic.ConstraintTypes.CallTyping
import Mettapedia.Logic.ConstraintTypes.OpenTyping
import Mettapedia.Logic.ConstraintTypes.DeclarationTyping
import Mettapedia.Logic.ConstraintTypes.DeterminedMembership
import Mettapedia.Logic.ConstraintTypes.ResidualConstraints

/-!
# Executable controls for symbolic predicate typing

These are finite queries of the general compiler. The type parameters range over
an infinite free constructor algebra; no list of type instances is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.Controls

open SymbolicTypes ConstructorTyping CallTyping

inductive Name where
  | number | string | token | box | same
  deriving DecidableEq

inductive Constructor where
  | list | pair | tagged
  deriving DecidableEq

def typeArity : Constructor → Nat
  | .list | .tagged => 1
  | .pair => 2

inductive Symbol where
  | number (n : Nat)
  | text (s : String)
  | nil | cons | pair | box | token | tag | typeName (name : Name)
  deriving DecidableEq

def valueArity : Symbol → Nat
  | .cons | .pair | .tag => 2
  | .box => 1
  | _ => 0

abbrev TypeCode (X : Type) := Expr X Name Constructor typeArity
abbrev Value := Tree Symbol valueArity

def listOf {X : Type} (element : TypeCode X) : TypeCode X := .app .list (fun _ => element)
def pairOf {X : Type} (left right : TypeCode X) : TypeCode X :=
  .app .pair (fun i => if i.val = 0 then left else right)

def number (n : Nat) : Value := .node (.number n) Fin.elim0
def text (s : String) : Value := .node (.text s) Fin.elim0
def nil : Value := .node .nil Fin.elim0
def cons (head tail : Value) : Value := .node .cons (fun i => if i.val = 0 then head else tail)
def pair (left right : Value) : Value := .node .pair (fun i => if i.val = 0 then left else right)
def boxed (value : Value) : Value := .node .box (fun _ => value)
def token : Value := .node .token Fin.elim0

def table (world : Bool) (symbol : Symbol) : List (Rule Nat Name Constructor typeArity (valueArity symbol)) :=
  match symbol with
  | .number _ => [⟨Fin.elim0, .closed .number⟩]
  | .text _ => [⟨Fin.elim0, .closed .string⟩]
  | .nil => [⟨Fin.elim0, listOf (.parameter 0)⟩]
  | .cons => [⟨fun i => some (if i.val = 0 then .parameter 0 else listOf (.parameter 0)),
      listOf (.parameter 0)⟩]
  | .pair => [⟨fun i => some (.parameter i.val), pairOf (.parameter 0) (.parameter 1)⟩]
  | .box => [⟨fun _ => some (.parameter 0), .closed .box⟩]
  | .token => if world then [⟨Fin.elim0, .closed .token⟩] else []
  | .tag | .typeName _ => []

def system : System Bool Nat Name Constructor Symbol typeArity valueArity :=
  DeterminedMembership.asSystem (fun context _ _ => context) table

theorem polymorphic_nil_number : ConstructorTyping.check system false nil (listOf (.closed .number)) = true := by
  cbv

theorem polymorphic_nil_string : ConstructorTyping.check system false nil (listOf (.closed .string)) = true := by
  cbv

theorem nested_polymorphic_list :
    ConstructorTyping.check system false (cons nil nil) (listOf (listOf (.closed .number))) = true := by cbv

theorem constructor_shared_parameter_rejects_mixed_list :
    ConstructorTyping.check system false (cons (text "bad") nil) (listOf (.closed .number)) = false := by cbv

theorem existential_field_is_solved_without_a_type_enumerator :
    ConstructorTyping.check system false (boxed (cons (number 2) nil)) (.closed .box) = true := by cbv

theorem existential_field_needs_the_general_checker :
    DeterminedMembership.coversFields (⟨fun (_ : Fin 1) => some (.parameter 0), .closed .box⟩ :
      Rule Nat Name Constructor typeArity 1) = false := by cbv

def equalPairFact : DeclarationTyping.Fact Unit Nat Name Constructor Symbol typeArity valueArity where
  pattern := .node .pair (fun _ => .var ())
  type := .closed .same

def declarations : DeclarationTyping.Declarations Bool Unit Nat Name Constructor Symbol typeArity valueArity where
  childContext context _ _ := context
  constructors := table
  facts _ := [equalPairFact]

theorem repeated_pattern_variable_accepts_equal_fields :
    DeclarationTyping.check declarations false (pair (number 2) (number 2)) (.closed .same) = true := by cbv

theorem repeated_pattern_variable_rejects_unequal_fields :
    DeclarationTyping.check declarations false (pair (number 2) (number 3)) (.closed .same) = false := by cbv

def blanketList : DeclarationTyping.Fact Unit Nat Name Constructor Symbol typeArity valueArity where
  pattern := .var ()
  type := listOf (.closed .number)

def nominalDeclarations : DeclarationTyping.Declarations Bool Unit Nat Name Constructor Symbol typeArity valueArity :=
  { declarations with facts := fun _ => [blanketList] }

theorem whole_value_fact_does_not_prove_its_fields :
    DeclarationTyping.check nominalDeclarations false (cons (text "bad") nil) (listOf (.closed .number)) = true ∧
      ConstructorTyping.check system false (text "bad") (.closed .number) = false := by cbv

def tagged {X : Type} (index : TypeCode X) : TypeCode X := .app .tagged (fun _ => index)
def typeName (name : Name) : Value := .node (.typeName name) Fin.elim0
def tag (index payload : Value) : Value := .node .tag (fun i => if i.val = 0 then index else payload)
def tagPattern : OpenTree Nat Symbol valueArity := .node .tag (fun i => .var i.val)
def readTypeName : Value → Option (Closed Name Constructor typeArity)
  | .node (.typeName name) _ => some (.closed name)
  | _ => none

def taggedFact : DeclarationTyping.Fact Nat Nat Name Constructor Symbol typeArity valueArity where
  pattern := tagPattern
  type := tagged (.parameter 0)
  bindings := [⟨0, 0, by decide⟩]
  readType := readTypeName

def taggedDeclarations : DeclarationTyping.Declarations Bool Nat Nat Name Constructor Symbol typeArity valueArity where
  childContext context _ _ := context
  constructors := table
  facts _ := [taggedFact]

theorem tagged_index_is_read_from_the_matched_value (world : Bool) (index : Name) (payload : Value)
    (type : Closed Name Constructor typeArity)
    (typed : DeclarationTyping.HasType taggedDeclarations world (tag (typeName index) payload) type) :
    type = tagged (.closed index) := by
  rcases (DeclarationTyping.hasType_node_iff taggedDeclarations world .tag _ type).1 typed with
    constructorCase | nominalCase
  · obtain ⟨rule, present, _⟩ := constructorCase
    cases present
  · obtain ⟨fact, present, matched, equal, parameters, bound, typeEqual⟩ := nominalCase
    have factEqual : fact = taggedFact := List.mem_singleton.1 present
    subst fact
    let canonical : Nat → Value := fun n => if n = 0 then typeName index else payload
    have canonicalMatch : tagPattern.evaluate canonical = tag (typeName index) payload := rfl
    have field := ValuePatterns.matched_variable_determined tagPattern matched canonical
      (equal.trans canonicalMatch.symm) 0 (by decide)
    have read := bound _ List.mem_cons_self
    change readTypeName (matched 0) = some (parameters 0) at read
    change matched 0 = typeName index at field
    rw [field] at read
    have parameter : parameters 0 = .closed index := (Option.some.inj read).symm
    simpa only [taggedFact, TypeExpr.substitute, tagged, parameter] using typeEqual

theorem matching_indexed_fact_is_accepted :
    DeclarationTyping.check taggedDeclarations false (tag (typeName .number) (number 1))
      (tagged (.closed .number)) = true := by cbv

theorem wrong_indexed_fact_is_rejected :
    DeclarationTyping.check taggedDeclarations false (tag (typeName .number) (number 1))
      (tagged (.closed .string)) = false := by cbv

theorem indexed_fact_does_not_claim_a_payload_type :
    DeclarationTyping.check taggedDeclarations false (tag (typeName .number) (text "payload"))
      (tagged (.closed .number)) = true := by cbv

def openNumberTag : OpenTree Unit Symbol valueArity :=
  .node .tag (fun i => if i.val = 0 then .node (.typeName .number) Fin.elim0 else .var ())

theorem wrong_index_is_impossible_while_payload_is_open (payload : Value) :
    ¬ ResidualConstraints.alternativesModel
      (OpenTyping.compile taggedDeclarations false openNumberTag (tagged (.closed .string) : TypeCode Empty))
      (OpenTyping.model taggedDeclarations (fun _ => payload)) Empty.elim := by
  intro admitted
  have typed := (OpenTyping.compile_correct _ _ _ _ _ _).1 admitted
  have expanded : openNumberTag.evaluate (fun _ => payload) = tag (typeName .number) payload := by
    simp only [openNumberTag, OpenTree.evaluate, tag]
    apply congrArg (Tree.node (arity := valueArity) Symbol.tag)
    funext i
    by_cases zero : i.val = 0 <;> simp [zero, OpenTree.evaluate, typeName]
    apply congrArg (Tree.node (arity := valueArity) (Symbol.typeName .number))
    funext impossible
    exact Fin.elim0 impossible
  rw [expanded, closed_substitute] at typed
  have forced := tagged_index_is_read_from_the_matched_value false .number payload _ typed
  have fields := forced
  simp only [tagged, TypeExpr.app.injEq, heq_eq_eq, true_and] at fields
  have names := congrFun fields ⟨0, by decide⟩
  cases names

def sameTaggedScheme : Declaration Nat Name Constructor Unit typeArity 2 where
  input _ := .inr (tagged (.parameter 0))
  output := .inr (.closed .number)

theorem shared_indices_reject_different_tags :
    entryAccepted (prepare (DeclarationTyping.asSystem taggedDeclarations) (fun _ _ _ => true) false
      (fun i => if i.val = 0 then tag (typeName .number) (number 1) else tag (typeName .string) (number 2))
      [sameTaggedScheme]) = false := by cbv

def sameScheme : Declaration Nat Name Constructor Unit typeArity 2 where
  input _ := .inr (.parameter 0)
  output := .inr (.parameter 0)

def observe (_ : Bool) (_ : Unit) (_ : Value) : Bool := true

theorem shared_parameters_reject_incompatible_arguments :
    entryAccepted (prepare system observe false (fun i => if i.val = 0 then number 1 else text "bad")
      [sameScheme]) = false := by cbv

/-- Nil admits infinitely many List instances. Its input equations must not
commit to List Number before the return value determines List String. -/
def identityScheme : Declaration Nat Name Constructor Unit typeArity 1 where
  input _ := .inr (.parameter 0)
  output := .inr (.parameter 0)

theorem result_selects_a_later_input_compatible_witness :
    resultAccepted system observe false (cons (text "ok") nil)
      (prepare system observe false (fun _ => nil) [identityScheme]) = true := by cbv

def rawScheme : Declaration Nat Name Constructor Unit typeArity 1 where
  input _ := .inl ()
  output := .inl ()

def numberScheme : Declaration Nat Name Constructor Unit typeArity 1 where
  input _ := .inr (.closed .number)
  output := .inr (.closed .number)

theorem mixed_modes_evaluate_once :
    evaluationPlan () [rawScheme.input 0, numberScheme.input 0] = .evaluate := by cbv

theorem literal_raw_mode_holds : evaluationPlan () [rawScheme.input 0] = .hold := by cbv

theorem duplicate_signatures_do_not_repeat_effects :
    (invoke system observe [numberScheme, numberScheme]
      (fun world _ => (.effect "once" (.answer (number 3, world) .done) : Trace (Value × Bool) String String))
      false (fun _ => number 2)).effects = ["once"] := by cbv

def tokenScheme : Declaration Nat Name Constructor Unit typeArity 1 where
  input _ := .inr (.closed .number)
  output := .inr (.closed .token)

theorem live_result_membership_is_not_entry_membership :
    resultAccepted system observe true token (prepare system observe false (fun _ => number 2) [tokenScheme]) = true ∧
      resultAccepted system observe false token
        (prepare system observe false (fun _ => number 2) [tokenScheme]) = false := by cbv

theorem occurs_check_rejects_recursive_type_equation :
    (SymbolicTypes.solve [(TypeExpr.parameter 0, listOf (.parameter 0))] :
      Option (Assignment Nat Name Constructor typeArity)).isSome = false := by cbv

/-- Normalization preserves an undecided predicate request as data. It neither
asserts that the requested type is inhabited nor decides the future world. -/
def pending : ResidualConstraints.Problem Unit Name Constructor String typeArity :=
  ResidualConstraints.atom "later-value" (.parameter ())

theorem pending_request_has_not_become_true : pending.requests.length = 1 := rfl

theorem pending_request_interpreted_in_its_waking_world (world : Bool) :
    ResidualConstraints.Models pending (fun _ _ => world = true) (fun _ => .closed .number) ↔ world = true :=
  ResidualConstraints.models_atom _ _ _ _


def plainDeclarations : DeclarationTyping.Declarations Bool Unit Nat Name Constructor Symbol typeArity valueArity :=
  { declarations with facts := fun _ => [] }

def openList (head : OpenTree Unit Symbol valueArity) : OpenTree Unit Symbol valueArity :=
  .node .cons (fun i => if i.val = 0 then head else .var ())

theorem known_bad_head_fails_with_an_open_tail :
    ScopedConstraints.accept ((OpenTyping.compile plainDeclarations false
      (openList (.node (.text "bad") Fin.elim0)) (listOf (.closed .number)) :
        List (ResidualConstraints.Problem Empty Name Constructor
          (OpenTyping.Request Bool Unit Unit Name Constructor Symbol typeArity valueArity) typeArity)).map
        ResidualConstraints.Problem.equations) = false := by cbv

theorem known_good_head_retains_a_tail_request :
    ((OpenTyping.compile plainDeclarations false
      (openList (.node (.number 2) Fin.elim0)) (listOf (.closed .number)) :
        List (ResidualConstraints.Problem Empty Name Constructor
          (OpenTyping.Request Bool Unit Unit Name Constructor Symbol typeArity valueArity) typeArity)).map
        (fun problem => problem.requests.length)) = [1] := by cbv

theorem ready_request_uses_current_declarations :
    OpenTyping.checkRequest plainDeclarations (fun (_ : Unit) => token) (.member true ()) (.closed .token) = true ∧
      OpenTyping.checkRequest plainDeclarations (fun (_ : Unit) => token) (.member false ()) (.closed .token) = false := by cbv

end Mettapedia.Logic.ConstraintTypes.Controls
