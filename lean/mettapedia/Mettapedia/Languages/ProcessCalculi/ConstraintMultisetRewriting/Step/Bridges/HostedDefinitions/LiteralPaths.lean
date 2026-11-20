import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleBuilder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HeadSeparation

/-!
# Checked literal paths through equation templates

A path descends only through rigid operators and arguments without binders.
Such a selected part survives metavariable assignment. Literal symbols on
these paths certify that two clauses cannot match the same closed call;
paths to slots certify recovery of the complete matching environment.

These are sufficient certificates about actual binding terms. A failed
certificate is not a refusal of the source equation or a completeness claim
about disjointness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.LiteralPaths

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

def atEmpty {X : Type} {declaration : X → MetaArity MSig} {context : Ctx MSig} {sort : Unit}
    (closed : context = []) (term : Term (signature MSig declaration) context sort) :
    Term (signature MSig declaration) [] () := by
  cases sort
  subst closed
  exact term

theorem atEmpty_instantiate {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) {context : Ctx MSig} {sort : Unit}
    (closed : context = []) (term : Term (signature MSig source) context sort) :
    atEmpty closed (instantiate assignment term) = instantiate assignment (atEmpty closed term) := by
  cases sort
  subst closed
  rfl

mutual

def partAt {X : Type} {declaration : X → MetaArity MSig} {context : Ctx MSig} {sort : Unit}
    (term : Term (signature MSig declaration) context sort) (closed : context = []) :
    List Nat → Option (Term (signature MSig declaration) [] ())
  | [] => some (atEmpty closed term)
  | index :: rest =>
      match term with
      | .op (.inl _) arguments => partArgsAt arguments closed index rest
      | _ => none

def partArgsAt {X : Type} {declaration : X → MetaArity MSig}
    {arity : List (List Unit × Unit)} {context : Ctx MSig}
    (arguments : Args (signature MSig declaration) arity context) (closed : context = [])
    (index : Nat) (rest : List Nat) : Option (Term (signature MSig declaration) [] ()) :=
  match arguments with
  | .nil => none
  | .cons (bs := bound) first later =>
      match index with
      | 0 => if empty : bound = [] then partAt first (by subst empty; exact closed) rest else none
      | index + 1 => partArgsAt later closed index rest

end

abbrev part {X : Type} {declaration : X → MetaArity MSig}
    (term : Term (signature MSig declaration) [] ()) (path : List Nat) := partAt term rfl path

mutual

theorem partAt_instantiate {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) :
    ∀ {context : Ctx MSig} {sort : Unit} (term : Term (signature MSig source) context sort)
      (closed : context = []) (path : List Nat) {selected : Term (signature MSig source) [] ()},
      partAt term closed path = some selected →
      partAt (instantiate assignment term) closed path = some (instantiate assignment selected)
  | _, _, term, closed, [], selected, found => by
      simp only [partAt] at found ⊢
      have same : atEmpty closed term = selected := Option.some.inj found
      subst selected
      exact congrArg some (atEmpty_instantiate assignment closed term)
  | _, _, .var _, _, _ :: _, _, found => by cases found
  | _, _, .op (.inr _) _, _, _ :: _, _, found => by cases found
  | _, _, .op (.inl _) arguments, closed, index :: rest, _, found =>
      partArgsAt_instantiate assignment arguments closed index rest found

theorem partArgsAt_instantiate {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) :
    ∀ {arity : List (List Unit × Unit)} {context : Ctx MSig}
      (arguments : Args (signature MSig source) arity context) (closed : context = [])
      (index : Nat) (path : List Nat) {selected : Term (signature MSig source) [] ()},
      partArgsAt arguments closed index path = some selected →
      partArgsAt (instantiateArgs assignment arguments) closed index path =
        some (instantiate assignment selected)
  | _, _, .nil, _, _, _, _, found => by cases found
  | _, _, .cons (bs := bound) first _, closed, 0, path, _, found => by
      by_cases empty : bound = []
      · subst empty
        exact partAt_instantiate assignment first closed path found
      · simp only [partArgsAt, dif_neg empty] at found
        cases found
  | _, _, .cons _ later, closed, index + 1, path, _, found =>
      partArgsAt_instantiate assignment later closed index path found

end

theorem part_instantiate {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) {term selected : Term (signature MSig source) [] ()}
    {path : List Nat} (found : part term path = some selected) :
    part (instantiate assignment term) path = some (instantiate assignment selected) :=
  partAt_instantiate assignment term rfl path found

def symbolAt {X : Type} {declaration : X → MetaArity MSig}
    (term : Term (signature MSig declaration) [] ()) (path : List Nat) : Option String :=
  (part term path).bind literalSymbol

theorem symbolAt_instantiate {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) {term : Term (signature MSig source) [] ()}
    {path : List Nat} {symbol : String} (found : symbolAt term path = some symbol) :
    symbolAt (instantiate assignment term) path = some symbol := by
  obtain ⟨selected, located, named⟩ := Option.bind_eq_some_iff.mp found
  have located' := part_instantiate assignment located
  simp only [symbolAt, located', Option.bind_some]
  exact literalSymbol_instantiate assignment selected named

theorem distinct_symbols {X Y Z : Type} {first : X → MetaArity MSig} {second : Y → MetaArity MSig}
    {target : Z → MetaArity MSig} {left : Term (signature MSig first) [] ()}
    {right : Term (signature MSig second) [] ()} {path : List Nat} {a b : String}
    (one : symbolAt left path = some a) (two : symbolAt right path = some b) (apart : a ≠ b)
    (leftAssignment : Assignment first target) (rightAssignment : Assignment second target) :
    instantiate leftAssignment left ≠ instantiate rightAssignment right := by
  intro same
  have names := congrArg (fun term => symbolAt term path) same
  rw [symbolAt_instantiate leftAssignment one, symbolAt_instantiate rightAssignment two] at names
  exact apart (Option.some.inj names)

def differentAt {X Y : Type} {first : X → MetaArity MSig} {second : Y → MetaArity MSig}
    (left : Term (signature MSig first) [] ()) (right : Term (signature MSig second) [] ())
    (path : List Nat) : Bool :=
  match symbolAt left path, symbolAt right path with
  | some a, some b => decide (a ≠ b)
  | _, _ => false

def separated (paths : List (List Nat)) (first second : ProgramBinders.Equation MSig [] ()) : Bool :=
  paths.any (differentAt first.lhs second.lhs)

theorem differentAt_sound {X Y Z : Type} {first : X → MetaArity MSig} {second : Y → MetaArity MSig}
    {target : Z → MetaArity MSig} {left : Term (signature MSig first) [] ()}
    {right : Term (signature MSig second) [] ()} {path : List Nat}
    (checked : differentAt left right path = true)
    (leftAssignment : Assignment first target) (rightAssignment : Assignment second target) :
    instantiate leftAssignment left ≠ instantiate rightAssignment right := by
  cases one : symbolAt left path with
  | none => simp [differentAt, one] at checked
  | some a =>
      cases two : symbolAt right path with
      | none => simp [differentAt, two] at checked
      | some b =>
          have apart : a ≠ b := of_decide_eq_true (by simpa [differentAt, one, two] using checked)
          exact distinct_symbols one two apart leftAssignment rightAssignment

theorem separated_no_common_call (paths : List (List Nat)) (first second : ProgramBinders.Equation MSig [] ())
    (checked : separated paths first second = true) (call a b : MClosed) :
    ¬ (ProgramBinders.Answers first call a ∧ ProgramBinders.Answers second call b) := by
  obtain ⟨path, _, checkedPath⟩ := List.any_eq_true.mp checked
  rintro ⟨⟨one, firstMatch, _⟩, ⟨two, secondMatch, _⟩⟩
  exact differentAt_sound checkedPath (first.assign one (ProgramBinders.ground MSig))
    (second.assign two (ProgramBinders.ground MSig)) (firstMatch.trans secondMatch.symm)

theorem recover_slot {n : Nat} (template : RuleBuilder.Template n) (index : Fin n) (path : List Nat)
    (located : part template path = some (RuleBuilder.slot index))
    (first second : Fin n → MClosed)
    (same : RuleBuilder.materialize first template = RuleBuilder.materialize second template) :
    first index = second index := by
  have instantiated := (RuleBuilder.include_materialize first template).symm.trans
    ((congrArg (Rigid.includeTerm (ProgramBinders.ground MSig)) same).trans
      (RuleBuilder.include_materialize second template))
  have parts := congrArg (fun term => part term path) instantiated
  rw [part_instantiate (RuleBuilder.values first) located,
    part_instantiate (RuleBuilder.values second) located,
    RuleBuilder.instantiate_slot, RuleBuilder.instantiate_slot] at parts
  exact Rigid.include_injective (ProgramBinders.ground MSig) _ _ (Option.some.inj parts)

theorem determining_paths {n : Nat} (template : RuleBuilder.Template n) (paths : Fin n → List Nat)
    (checked : ∀ index, part template (paths index) = some (RuleBuilder.slot index)) :
    Function.Injective (fun values : Fin n → MClosed => RuleBuilder.materialize values template) := by
  intro first second same
  funext index
  exact recover_slot template index (paths index) (checked index) first second same

def slotIndex {n : Nat} : RuleBuilder.Template n → Option (Fin n)
  | .op (.inr (.mk index)) _ => some index
  | _ => none

theorem slotIndex_sound {n : Nat} : ∀ {template : RuleBuilder.Template n} {index : Fin n},
    slotIndex template = some index → template = RuleBuilder.slot index
  | .var impossible, _, _ => nomatch impossible
  | .op (.inl _) _, _, found => by cases found
  | .op (.inr (.mk actual)) .nil, index, found => by
      have same : actual = index := Option.some.inj found
      subst actual
      rfl

mutual

/-- Find candidate slot positions. The positions are validated independently
by `pathsChecked`; finding one does not itself certify a template. -/
def slotLocations {n : Nat} {context : Ctx MSig} {sort : Unit} :
    Term (signature MSig (RuleBuilder.FoArity n)) context sort → List (Fin n × List Nat)
  | .var _ => []
  | .op (.inr (.mk index)) _ => [(index, [])]
  | .op (.inl _) arguments => argumentLocations 0 arguments

def argumentLocations {n : Nat} {context : Ctx MSig} {arity : List (List Unit × Unit)}
    (index : Nat) : Args (signature MSig (RuleBuilder.FoArity n)) arity context → List (Fin n × List Nat)
  | .nil => []
  | .cons first rest =>
      (slotLocations first).map (fun entry => (entry.1, index :: entry.2)) ++ argumentLocations (index + 1) rest

end

def chosenPath {n : Nat} (template : RuleBuilder.Template n) (index : Fin n) : List Nat :=
  (((slotLocations template).find? (fun entry => decide (entry.1 = index))).map Prod.snd).getD []

def pathChecks {n : Nat} (template : RuleBuilder.Template n) (index : Fin n) (path : List Nat) : Bool :=
  match part template path with
  | none => false
  | some selected => decide (slotIndex selected = some index)

def pathsChecked {n : Nat} (template : RuleBuilder.Template n) : Bool :=
  (List.finRange n).all (fun index => pathChecks template index (chosenPath template index))

theorem pathChecks_sound {n : Nat} {template : RuleBuilder.Template n} {index : Fin n} {path : List Nat}
    (checked : pathChecks template index path = true) : part template path = some (RuleBuilder.slot index) := by
  cases selected : part template path with
  | none => simp [pathChecks, selected] at checked
  | some found =>
      have foundIndex : slotIndex found = some index := of_decide_eq_true (by simpa [pathChecks, selected] using checked)
      exact congrArg some (slotIndex_sound foundIndex)

theorem pathsChecked_determines {n : Nat} {template : RuleBuilder.Template n}
    (checked : pathsChecked template = true) :
    Function.Injective (fun values : Fin n → MClosed => RuleBuilder.materialize values template) := by
  apply determining_paths template (chosenPath template)
  intro index
  exact pathChecks_sound (List.all_eq_true.mp checked index (by simp))

def EquationDeterministic (equation : ProgramBinders.Equation MSig [] ()) : Prop :=
  ∀ call first second, ProgramBinders.Answers equation call first →
    ProgramBinders.Answers equation call second → first = second

theorem equation_deterministic {n : Nat} (left right : RuleBuilder.Template n)
    (checked : pathsChecked left = true) : EquationDeterministic (RuleBuilder.equation left right) := by
  intro call first second one two
  obtain ⟨firstEnvironment, firstInput, firstOutput⟩ := (RuleBuilder.answers_iff left right call first).mp one
  obtain ⟨secondEnvironment, secondInput, secondOutput⟩ := (RuleBuilder.answers_iff left right call second).mp two
  have same := pathsChecked_determines checked (firstInput.trans secondInput.symm)
  subst secondEnvironment
  exact firstOutput.symm.trans secondOutput

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.LiteralPaths
