import Mettapedia.Languages.Megalodon.MathdataTypeFormation

/-!
# Declaration-order source parameters and nested type binders

The source exporter numbers type parameters in application order: source
parameter zero receives the first type argument. The Mathdata/NIK syntax
uses nested type abstractions, so that same parameter has the largest bound
index. The boundary reverses the declared interval and preserves variables
bound inside it or outside it.

The main specialization theorem compares the actual nested-binder operation
with successive removal of source parameter zero. The variable theorem
identifies the latter with lookup in the supplied argument list. Closed plain
arguments are explicit hypotheses; this does not assert correctness of a
parser or of arbitrary open specialization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceTypeParameters

open MathdataKernel

def reverseIndex (count depth index : Nat) : Nat :=
  if depth ≤ index ∧ index < depth + count then
    depth + count - 1 - (index - depth)
  else index

theorem reverseIndex_involutive (count depth index : Nat) :
    reverseIndex count depth (reverseIndex count depth index) = index := by
  unfold reverseIndex
  split
  · split <;> omega
  · rfl

theorem reverseIndex_scope (count depth index : Nat) :
    reverseIndex count depth index < depth + count ↔ index < depth + count := by
  unfold reverseIndex
  split <;> omega

def type (count depth : Nat) : Tp → Tp
  | .var index => .var (reverseIndex count depth index)
  | .prop => .prop
  | .base index => .base index
  | .arr domain codomain => .arr (type count depth domain) (type count depth codomain)
  | .all body => .all (type count (depth + 1) body)

theorem type_involutive (count depth : Nat) (body : Tp) :
    type count depth (type count depth body) = body := by
  induction body generalizing depth with
  | var index => simp [type, reverseIndex_involutive]
  | prop | base => rfl
  | arr domain codomain ihd ihc => simp [type, ihd, ihc]
  | all body ih => simp [type, ih]

theorem type_plainWellFormed (count depth : Nat) (body : Tp) :
    (type count depth body).plainWellFormed (depth + count) =
      body.plainWellFormed (depth + count) := by
  induction body with
  | var index => simp [type, Tp.plainWellFormed, reverseIndex_scope]
  | prop | base | all => rfl
  | arr domain codomain ihd ihc => simp [type, Tp.plainWellFormed, ihd, ihc]

theorem type_zero (depth : Nat) (body : Tp) : type 0 depth body = body := by
  induction body generalizing depth with
  | var index => simp [type, reverseIndex]; omega
  | prop | base => rfl
  | arr domain codomain ihd ihc => simp [type, ihd, ihc]
  | all body ih => simp [type, ih]

theorem type_closed (count depth : Nat) {body : Tp}
    (closed : body.plainWellFormed 0 = true) : type count depth body = body := by
  induction body with
  | var index => simp [Tp.plainWellFormed] at closed
  | prop | base => rfl
  | arr domain codomain ihd ihc =>
      simp only [Tp.plainWellFormed, Bool.and_eq_true] at closed
      simp [type, ihd closed.1, ihc closed.2]
  | all body ih => simp [Tp.plainWellFormed] at closed

private theorem shift_closed (amount : Nat) {body : Tp}
    (closed : body.plainWellFormed 0 = true) : body.shift 0 amount = body := by
  induction body with
  | var index => simp [Tp.plainWellFormed] at closed
  | prop | base => rfl
  | arr domain codomain ihd ihc =>
      simp only [Tp.plainWellFormed, Bool.and_eq_true] at closed
      simp [Tp.shift, ihd closed.1, ihc closed.2]
  | all body ih => simp [Tp.plainWellFormed] at closed

/-- The first source parameter becomes the outermost of the pending binders.
Removing it leaves precisely the same reversal for the remaining parameters. -/
theorem instantiate_outer {count : Nat} {body argument : Tp}
    (formed : body.plainWellFormed (count + 1) = true)
    (closed : argument.plainWellFormed 0 = true) :
    Tp.instantiateAt count argument (type (count + 1) 0 body) =
      type count 0 (Tp.instantiate argument body) := by
  induction body with
  | var index =>
      simp only [Tp.plainWellFormed, decide_eq_true_eq] at formed
      by_cases zero : index = 0
      · subst index
        simp [type, reverseIndex, Tp.instantiate, Tp.instantiateAt,
          shift_closed count closed, Tp.shift_zero, type_closed count 0 closed]
      · have mapped : count - index < count := by omega
        have same : count - 1 - (index - 1) = count - index := by omega
        simp [type, reverseIndex, Tp.instantiate, Tp.instantiateAt, formed,
          zero, mapped, same, show index - 1 < count by omega]
  | prop | base => rfl
  | arr domain codomain ihd ihc =>
      simp only [Tp.plainWellFormed, Bool.and_eq_true] at formed
      simp [type, Tp.instantiate, Tp.instantiateAt, ihd formed.1, ihc formed.2]
  | all body ih => simp [Tp.plainWellFormed] at formed

def bind : Nat → Tp → Tp
  | 0, body => body
  | count + 1, body => .all (bind count body)

def specialize : List Tp → Tp → Option Tp
  | [], body => some body
  | argument :: arguments, .all body => specialize arguments (Tp.instantiate argument body)
  | _ :: _, _ => none

/-- Remove source parameters in their declaration/application order. -/
def instantiateParameters : List Tp → Tp → Tp
  | [], body => body
  | argument :: arguments, body => instantiateParameters arguments (Tp.instantiate argument body)

private theorem instantiateAt_bind (count depth : Nat) (argument body : Tp) :
    Tp.instantiateAt depth argument (bind count body) =
      bind count (Tp.instantiateAt (depth + count) argument body) := by
  induction count generalizing depth with
  | zero => simp [bind]
  | succ count ih => simp [bind, Tp.instantiateAt, ih, Nat.add_comm, Nat.add_left_comm]

/-- Exact computation of arbitrary finite closed type-argument spines. -/
theorem specialize_bind (arguments : List Tp) (body : Tp)
    (formed : body.plainWellFormed arguments.length = true)
    (closed : ∀ argument ∈ arguments, argument.plainWellFormed 0 = true) :
    specialize arguments (bind arguments.length (type arguments.length 0 body)) =
      some (instantiateParameters arguments body) := by
  induction arguments generalizing body with
  | nil => simp [bind, specialize, instantiateParameters, type_zero]
  | cons argument arguments ih =>
      have argument_closed := closed argument (by simp)
      have tail_closed : ∀ value ∈ arguments, value.plainWellFormed 0 = true := by
        intro value member
        exact closed value (by simp [member])
      have next_formed := Tp.plainWellFormed_instantiate formed
        (Tp.plainWellFormed_mono argument_closed (Nat.zero_le arguments.length))
      simp only [List.length_cons, bind, specialize, Tp.instantiate,
        instantiateAt_bind, Nat.zero_add]
      rw [instantiate_outer formed argument_closed]
      exact ih (Tp.instantiate argument body) next_formed tail_closed

theorem instantiateParameters_closed (arguments : List Tp) {body : Tp}
    (closed : body.plainWellFormed 0 = true) : instantiateParameters arguments body = body := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih =>
      rw [instantiateParameters, Tp.instantiate,
        Tp.instantiateAt_eq_of_plain body argument closed (Nat.zero_le 0)]
      exact ih

/-- Source variable zero denotes the first supplied argument, not the last. -/
theorem instantiateParameters_var (arguments : List Tp)
    (closed : ∀ argument ∈ arguments, argument.plainWellFormed 0 = true)
    (index : Nat) (scope : index < arguments.length) :
    instantiateParameters arguments (.var index) = arguments[index] := by
  induction arguments generalizing index with
  | nil => simp at scope
  | cons argument arguments ih =>
      cases index with
      | zero =>
          simp [instantiateParameters, Tp.instantiate, Tp.instantiateAt, Tp.shift_zero,
            instantiateParameters_closed arguments (closed argument (by simp))]
      | succ index =>
          have tail_closed : ∀ value ∈ arguments, value.plainWellFormed 0 = true := by
            intro value member
            exact closed value (by simp [member])
          simpa [instantiateParameters, Tp.instantiate, Tp.instantiateAt] using
            ih tail_closed index (by simpa using scope)

/-- Apply source type arguments, left to right, using the existing term former. -/
def applyTypes : List Tp → Tm → Tm
  | [], function => function
  | argument :: arguments, function => applyTypes arguments (.typeApp function argument)

/-- The actual term checker computes the same finite specialization, including
failure when the function has too few type binders. -/
theorem inferTerm_applyTypes (environment : Environment) (context : List Tp)
    (arguments : List Tp) (function : Tm)
    (closed : ∀ argument ∈ arguments, argument.plainWellFormed 0 = true) :
    inferTerm environment 0 context (applyTypes arguments function) =
      (inferTerm environment 0 context function).bind (specialize arguments) := by
  induction arguments generalizing function with
  | nil => simp [applyTypes, specialize]
  | cons argument arguments ih =>
      have argument_closed := closed argument (by simp)
      have tail_closed : ∀ value ∈ arguments, value.plainWellFormed 0 = true := by
        intro value member
        exact closed value (by simp [member])
      rw [applyTypes, ih _ tail_closed]
      simp only [inferTerm, argument_closed, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
      cases inferred : inferTerm environment 0 context function with
      | none => rfl
      | some value => cases value <;> rfl

/-- A checked polymorphic source function applied to all its type parameters
receives exactly its source-order result type in the existing checker. -/
theorem inferTerm_source_parameters (environment : Environment) (context : List Tp)
    (arguments : List Tp) (function : Tm) (body : Tp)
    (formed : body.plainWellFormed arguments.length = true)
    (closed : ∀ argument ∈ arguments, argument.plainWellFormed 0 = true)
    (checked : inferTerm environment 0 context function =
      some (bind arguments.length (type arguments.length 0 body))) :
    inferTerm environment 0 context (applyTypes arguments function) =
      some (instantiateParameters arguments body) := by
  rw [inferTerm_applyTypes environment context arguments function closed, checked]
  exact specialize_bind arguments body formed closed

theorem checked_two_parameter_function :
    let environment : Environment := { terms :=
      [{ name := "sourceFunction", type := bind 2 (type 2 0 (.arr (.var 0) (.var 1))) }] }
    inferTerm environment 0 [] (applyTypes [.base 0, .prop] (.named "sourceFunction")) =
      some (.arr (.base 0) .prop) := by decide

theorem extra_parameter_rejected :
    let environment : Environment := { terms :=
      [{ name := "sourceFunction", type := bind 2 (type 2 0 (.arr (.var 0) (.var 1))) }] }
    inferTerm environment 0 []
      (applyTypes [.base 0, .prop, .prop] (.named "sourceFunction")) = none := by decide

theorem two_parameters_preserve_order :
    specialize [.base 0, .prop] (bind 2 (type 2 0 (.arr (.var 0) (.var 1)))) =
      some (.arr (.base 0) .prop) := by decide

/-- Omitting the boundary reversal is well scoped but changes the source type. -/
theorem scope_does_not_detect_reversed_meaning :
    (bind 2 (.arr (.var 0) (.var 1))).polyWellFormed 0 = true ∧
      specialize [.base 0, .prop] (bind 2 (.arr (.var 0) (.var 1))) ≠
        some (.arr (.base 0) .prop) := by decide

#print axioms reverseIndex_involutive
#print axioms type_involutive
#print axioms type_plainWellFormed
#print axioms instantiate_outer
#print axioms specialize_bind
#print axioms instantiateParameters_var
#print axioms inferTerm_applyTypes
#print axioms inferTerm_source_parameters
#print axioms checked_two_parameter_function
#print axioms extra_parameter_rejected
#print axioms two_parameters_preserve_order
#print axioms scope_does_not_detect_reversed_meaning

end Mettapedia.Languages.Megalodon.SourceTypeParameters
