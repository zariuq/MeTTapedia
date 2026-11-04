import Mettapedia.Logic.ConstraintTypes.PatternContracts
import Mettapedia.Logic.ConstraintTypes.Controls

/-!
# Controls for explicit wildcards, proper witnesses and exact indices

Proper membership is the existing declaration judgment. Checking operators add
pointwise list requirements and decoded type indices, without a universal
proper type or additional typing derivations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.PatternControls

open SymbolicTypes ScopedConstraints CheckingPatterns Controls

inductive Kind where
  | value | index

inductive ValueOperator where
  | list | tagged

abbrev Carrier : Kind → Type
  | .value => Value
  | .index => Closed Name Constructor typeArity

abbrev signature : CheckingPatterns.Signature Kind where
  symbol
    | .value => ValueOperator
    | .index => Constructor
  arity := fun {s} op => match s, op with
    | .value, _ => 1
    | .index, op => typeArity op
  argumentSort := fun {s} op i => match s, op, i with
    | .value, .list, _ => .value
    | .value, .tagged, _ => .index
    | .index, _, _ => .index

def elements : Value → Option (List Value)
  | .node .nil _ => some []
  | .node .cons children => (elements (children ⟨1, by decide⟩)).map (children ⟨0, by decide⟩ :: ·)
  | _ => none

def branches : {s : Kind} → (op : signature.symbol s) → Bool → Carrier s →
    List (List (Query op Carrier Bool))
  | .value, .list, context, value => match elements value with
      | none => []
      | some values => [values.map fun child => ⟨⟨0, by decide⟩, context, child⟩]
  | .value, .tagged, context, .node .tag children => match readTypeName (children ⟨0, by decide⟩) with
      | none => []
      | some index => [[⟨⟨0, by decide⟩, context, index⟩]]
  | .value, .tagged, _, _ => []
  | .index, op, context, .app actual children =>
      if same : actual = op then
        [(List.finRange (typeArity op)).map fun i => ⟨i, context, children (same.symm ▸ i)⟩]
      else []
  | .index, _, _, .closed _ => []
  | .index, _, _, .parameter impossible => nomatch impossible

def model : Model signature Carrier Bool Name Constructor typeArity where
  member := fun {s} context subject type => match s, context, subject, type with
    | .value, context, value, type => DeclarationTyping.HasType taggedDeclarations context value type
    | .index, _, index, type => index = type
  branches := branches

def compiler : Compiler model where
  proper := fun {X} [_] {s} context subject type => match s, context, subject, type with
    | .value, context, value, type =>
        ConstructorTyping.compile (DeclarationTyping.asSystem taggedDeclarations) context value type
    | .index, _, index, type => [equation (embedClosed index) type]
  correct := by
    intro X _ s context subject type parameters
    cases s with
    | value =>
        exact (ConstructorTyping.compile_correct _ _ _ _ _).trans
          (DeclarationTyping.asSystem_iff _ _ _ _)
    | index =>
        change alternativesSatisfy [equation (embedClosed subject) type] parameters ↔
          subject = type.substitute parameters
        simp only [alternativesSatisfy, List.mem_singleton, exists_eq_left, satisfies_equation]
        rw [close_embed]

abbrev ValueCheck (P : Type) := Pattern signature P Name Constructor typeArity .value
abbrev IndexCheck (P : Type) := Pattern signature P Name Constructor typeArity .index

def listCheck {P : Type} (element : ValueCheck P) : ValueCheck P := .apply .list (fun _ => element)
def tagCheck {P : Type} (index : IndexCheck P) : ValueCheck P := .apply .tagged (fun _ => index)
def indexList {P : Type} (element : IndexCheck P) : IndexCheck P := .apply .list (fun _ => element)

def check {P : Type} [DecidableEq P] (pattern : ValueCheck P) (value : Value) : Bool :=
  accept ((compile model compiler pattern false value).map close)

theorem check_iff {P : Type} [DecidableEq P] (pattern : ValueCheck P) (value : Value) :
    check pattern value = true ↔ ∃ parameters, Matches model parameters pattern false value := by
  rw [check, accept_closed_iff (.closed .number)]
  constructor
  · rintro ⟨problem,present,solved⟩
    obtain ⟨compiled,compiledMember,rfl⟩ := List.mem_map.1 present
    obtain ⟨parameters,solved⟩ := (satisfies_close _).1 solved
    exact ⟨parameters,(compile_correct _ _ _ _ _ _).1 ⟨compiled,compiledMember,solved⟩⟩
  · rintro ⟨parameters,matched⟩
    obtain ⟨compiled,present,solved⟩ := (compile_correct _ _ _ _ _ _).2 matched
    exact ⟨close compiled,List.mem_map.2 ⟨compiled,present,rfl⟩,(satisfies_close _).2 ⟨parameters,solved⟩⟩

def mixed : Value := cons (number 1) (cons (text "a") nil)

theorem wildcard_list_accepts_mixed_values : check (listCheck (.any : ValueCheck Empty)) mixed = true := by cbv

theorem number_list_rejects_mixed_values :
    check (listCheck (.proper (.closed .number) : ValueCheck Empty)) mixed = false := by cbv

theorem wildcard_still_requires_list_structure :
    check (listCheck (.any : ValueCheck Empty)) (number 1) = false := by cbv

theorem nested_wildcard_preserves_outer_structure :
    check (listCheck (listCheck (.any : ValueCheck Empty))) (cons mixed nil) = true ∧
      check (listCheck (listCheck (.any : ValueCheck Empty))) mixed = false := by cbv

theorem wildcard_is_not_an_existential_element_type :
    check (.proper (listOf (.parameter 0)) : ValueCheck Nat) mixed = false := by cbv

theorem nested_shared_parameter_is_not_a_wildcard :
    check (listCheck (.proper (.parameter 0)) : ValueCheck Nat) mixed = false := by cbv

/-- Known bad structure is impossible under every completion, not just after
choosing one concrete tail. A propagator can therefore reject it immediately. -/
theorem bad_head_cannot_be_repaired_by_any_tail (tail : Value) :
    ¬ Matches model Empty.elim (listCheck (.proper (.closed .number) : ValueCheck Empty)) false
      (cons (text "bad") tail) := by
  intro matched
  obtain ⟨branch,present,checked⟩ := (matches_apply_iff _ _ _ _ _ _).1 matched
  cases tailShape : elements tail with
  | none => simp [model,branches,elements,cons,tailShape] at present
  | some values =>
      have selected : branch = (text "bad" :: values).map
          (fun child => (⟨⟨0,by decide⟩,false,child⟩ :
            Query (sig := signature) (s := Kind.value) ValueOperator.list Carrier Bool)) := by
        simpa [model,branches,elements,cons,tailShape] using present
      subst branch
      let firstQuery : Query (sig := signature) (s := Kind.value) ValueOperator.list Carrier Bool :=
        ⟨⟨0,by decide⟩,false,text "bad"⟩
      have bad := checked firstQuery (by simp [firstQuery])
      have typed : DeclarationTyping.HasType taggedDeclarations false (text "bad") (.closed .number) :=
        (matches_proper_iff _ _ _ _ _).1 bad
      have accepted := (DeclarationTyping.check_iff _ _ _ _).2 typed
      have rejected : DeclarationTyping.check taggedDeclarations false (text "bad") (.closed .number) = false := by cbv
      rw [rejected] at accepted
      cases accepted

def shared : PatternContracts.Declaration signature Nat Name Constructor typeArity .value 2 where
  input _ := ⟨.evaluate, .proper (.parameter 0)⟩
  output := .any

theorem shared_parameter_rejects_number_and_string :
    PatternContracts.entryAccepted (PatternContracts.prepare (valueKind := .value) model compiler false
      (fun i => if i.val = 0 then number 1 else text "a") [shared]) = false := by cbv

theorem repeated_wildcards_do_not_correlate_inputs :
    let unrestricted : PatternContracts.Declaration signature Nat Name Constructor typeArity .value 2 :=
      ⟨fun _ => ⟨.evaluate,.any⟩,.any⟩
    PatternContracts.entryAccepted (PatternContracts.prepare (valueKind := .value) model compiler false
      (fun i => if i.val = 0 then number 1 else text "a") [unrestricted]) = true := by cbv

theorem exact_index_accepts_its_tag :
    check (tagCheck (.proper (.closed .number) : IndexCheck Empty)) (tag (typeName .number) (text "payload")) = true := by cbv

theorem exact_index_rejects_another_tag :
    check (tagCheck (.proper (.closed .string) : IndexCheck Empty)) (tag (typeName .number) (number 1)) = false := by cbv

theorem wildcard_index_does_not_impose_an_exact_tag :
    check (tagCheck (.any : IndexCheck Empty)) (tag (typeName .number) (number 1)) = true ∧
      check (tagCheck (.any : IndexCheck Empty)) (tag (typeName .string) (number 1)) = true := by cbv

theorem compound_index_wildcard_accepts_different_elements :
    accept ((compile model compiler (indexList (.any : IndexCheck Empty)) false
      (listOf (.closed .string))).map close) = true := by cbv

theorem compound_exact_index_remains_exact :
    accept ((compile model compiler (.proper (listOf (.closed .number)) : IndexCheck Empty) false
      (listOf (.closed .string))).map close) = false := by cbv

def numberToAny : PatternContracts.Declaration signature Nat Name Constructor typeArity .value 1 where
  input _ := ⟨.evaluate,.proper (.closed .number)⟩
  output := .any

theorem unrestricted_result_keeps_a_computed_answer :
    PatternContracts.invoke (Carrier := Carrier) (valueKind := Kind.value) model compiler [numberToAny]
      (fun world _ => (.answer (number (2 + 42),world) .done : Trace (Value × Bool) String String))
      false (fun _ => number 2) = .answer (number 44,false) .done := by cbv

theorem explicit_template_is_returned_as_data :
    PatternContracts.invoke (Carrier := Carrier) (valueKind := Kind.value) model compiler [numberToAny]
      (fun world _ => (.answer (pair (number 2) (number 42),world) .done : Trace (Value × Bool) String String))
      false (fun _ => number 2) = .answer (pair (number 2) (number 42),false) .done := by cbv

theorem unrestricted_result_retains_effects_and_faults :
    PatternContracts.invoke (Carrier := Carrier) (valueKind := Kind.value) model compiler [numberToAny]
      (fun world _ => (.effect "ran" (.answer (number 44,world) (.fault "body fault")) :
        Trace (Value × Bool) String String)) false (fun _ => number 2) =
      .effect "ran" (.answer (number 44,false) (.fault "body fault")) := by cbv

end Mettapedia.Logic.ConstraintTypes.PatternControls
