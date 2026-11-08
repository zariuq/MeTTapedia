import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

/-!
# Executable admission of closed HE constructor values

The checker reads the actual HE type lookup and stored equations. It accepts
one closed arrow declaration, excludes callable/minimal heads, rejects every
equation that could have that head (including variable-headed equations), and
checks the fields recursively. Its certificate is derived, not supplied:
successful admission implies `CompletedDelivery.Completed`, hence exact
singleton delivery by the existing HE interpreter at sufficient fuel.

This is the closed, single-applicability fragment. Open declaration variables
and first-success selection among several typing paths are not identified
with the interpreter's all-candidate relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorAdmission

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Only equations with a different literal head are harmless to this head.
Unstructured or variable-headed left sides are conservatively rejected. -/
def rowAvoidsHead (head : String) : Atom → Bool
  | .expression [.symbol "=", .expression (.symbol other :: _), _] => head != other
  | .expression [.symbol "=", _, _] => false
  | _ => true

def headAbsent (space : Space) (head : String) : Bool :=
  space.atoms.all (rowAvoidsHead head)

theorem matchAtoms_distinct_heads {head other : String} (different : head ≠ other)
    (args fields : List Atom) (fuel : Nat) :
    matchAtoms (.expression (.symbol head :: args))
      (.expression (.symbol other :: fields)) fuel = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      change (if (args.length + 1 == fields.length + 1) then
        matchAtomsList (.symbol head :: args) (.symbol other :: fields) [Bindings.empty] fuel
        else []).filter (fun b => !b.hasLoop) = []
      split
      · cases fuel with
        | zero => rfl
        | succ fuel =>
            have symbols : matchAtoms (.symbol head) (.symbol other) fuel = [] := by
              cases fuel <;> simp [matchAtoms, getMetaType, different]
            simp [matchAtomsList, symbols, matchAtomsList_nil_acc]
      · rfl

theorem headAbsent_noEquation {space : Space} {head : String}
    (absent : headAbsent space head = true) (args : List Atom) :
    NoEquationMatch space (.expression (.symbol head :: args)) := by
  intro avoid fuel
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result member
  obtain ⟨lhs, rhs, idx, stored, _, matched, _⟩ :=
    queryEquationsAvoiding_matchAtoms_witness member
  have source : .expression [.symbol "=", lhs, rhs] ∈ space.atoms := by
    rw [List.mem_zipIdx_iff_getElem?] at stored
    exact List.mem_of_getElem? stored
  have safe : rowAvoidsHead head (.expression [.symbol "=", lhs, rhs]) = true :=
    (List.all_eq_true.mp absent) _ source
  cases lhs with
  | symbol name => simp [rowAvoidsHead] at safe
  | var name => simp [rowAvoidsHead] at safe
  | grounded value => simp [rowAvoidsHead] at safe
  | expression fields =>
      cases fields with
      | nil => simp [rowAvoidsHead] at safe
      | cons first fields =>
          cases first with
          | var name => simp [rowAvoidsHead] at safe
          | grounded value => simp [rowAvoidsHead] at safe
          | expression values => simp [rowAvoidsHead] at safe
          | symbol other =>
              have different : head ≠ other := by simpa [rowAvoidsHead] using safe
              simp only [freshenEquationAvoiding, renameAtom, renameAtomList] at matched
              rw [matchAtoms_distinct_heads different] at matched
              cases matched

/-- Exactly one accepted typing, and no open rejected typing that could bind
the caller's record instead of being a completed mismatch. -/
def checkOnce (space : Space) (param arg : Atom) : Bool :=
  (getAtomTypes space arg).countP (accepts param) == 1 &&
    (getAtomTypes space arg).all fun type =>
      accepts param type || atomVariables type == []

theorem checkOnce_sound {space : Space} {param arg : Atom}
    (checked : checkOnce space param arg = true) : ArgumentChecked space param arg := by
  simp only [checkOnce, Bool.and_eq_true] at checked
  obtain ⟨once, rejected⟩ := checked
  refine ⟨by simpa using once, ?_⟩
  intro type member failed
  have found := List.all_eq_true.mp rejected type member
  simpa [failed] using found

/-- Field admission is separate from traversal so the induction uses the
already certified child checker, not an assumption about evaluation. -/
def checkFields (space : Space) (child : Atom → Option Atom) :
    List Atom → List Atom → Bool
  | [], [] => true
  | param :: params, arg :: args =>
      checkOnce space param arg &&
      (isLeaf arg || match child arg with
        | none => false
        | some range => param == Atom.undefinedType || param == range) &&
      checkFields space child params args
  | _, _ => false

theorem checkFields_sound {space : Space} {dispatch : GroundedDispatch}
    {child : Atom → Option Atom}
    (sound : ∀ value range, child value = some range → Completed space dispatch value range) :
    ∀ params args, checkFields space child params args = true →
      CompletedArguments space dispatch params args
  | [], [], _ => .nil
  | [], _ :: _, checked => by simp [checkFields] at checked
  | _ :: _, [], checked => by simp [checkFields] at checked
  | param :: params, arg :: args, checked => by
      simp only [checkFields, Bool.and_eq_true] at checked
      obtain ⟨⟨once, value⟩, rest⟩ := checked
      have tail := checkFields_sound sound params args rest
      have first := checkOnce_sound once
      simp only [Bool.or_eq_true] at value
      rcases value with leaf | completed
      · exact .leaf leaf first tail
      · cases found : child arg with
        | none => simp [found] at completed
        | some range =>
            have fits : param = Atom.undefinedType ∨ param = range := by
              simpa [found] using completed
            exact .value (sound arg range found) fits first tail

def checkHead (space : Space) (dispatch : GroundedDispatch) (head : String)
    (params args : List Atom) (range : Atom) : Bool :=
  getAtomTypes space (.symbol head) == [arrowType params range] &&
  atomVariables (arrowType params range) == [] &&
  head != "Empty" && !dispatch.isExecutable (.symbol head) &&
  !minimalInstruction (.expression (.symbol head :: args)) && headAbsent space head

theorem checkHead_sound {space : Space} {dispatch : GroundedDispatch} {head : String}
    {params args : List Atom} {range : Atom}
    (header : checkHead space dispatch head params args range = true)
    (fields : CompletedArguments space dispatch params args) :
    Completed space dispatch (.expression (.symbol head :: args)) range := by
  simp only [checkHead, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at header
  obtain ⟨⟨⟨⟨⟨declared, ground⟩, notEmpty⟩, notExecutable⟩, notInstruction⟩, absent⟩ := header
  exact .typed declared ground notEmpty (by simpa using notExecutable)
    (by simpa using notInstruction)
    (headAbsent_noEquation absent args) fields

/-- A bounded executable checker. Running out of structural fuel declines;
it never manufactures a completed judgment. -/
def check (space : Space) (dispatch : GroundedDispatch) : Nat → Atom → Option Atom
  | 0, _ => none
  | fuel + 1, .expression (.symbol head :: args) =>
      match getAtomTypes space (.symbol head) with
      | [type] =>
          match getFunctionArgTypes type, getFunctionRetType type with
          | some params, some range =>
              if checkHead space dispatch head params args range &&
                  checkFields space (check space dispatch fuel) params args
              then some range else none
          | _, _ => none
      | _ => none
  | _ + 1, _ => none

theorem check_sound (space : Space) (dispatch : GroundedDispatch) :
    ∀ fuel value range, check space dispatch fuel value = some range →
      Completed space dispatch value range := by
  intro fuel
  induction fuel with
  | zero => intro value range accepted; simp [check] at accepted
  | succ fuel ih =>
      intro value range accepted
      cases value with
      | symbol name => simp [check] at accepted
      | var name => simp [check] at accepted
      | grounded value => simp [check] at accepted
      | expression elements =>
          cases elements with
          | nil => simp [check] at accepted
          | cons head args =>
              cases head with
              | var name => simp [check] at accepted
              | grounded value => simp [check] at accepted
              | expression values => simp [check] at accepted
              | symbol name =>
                  unfold check at accepted
                  split at accepted
                  · split at accepted
                    · split at accepted
                      · rename_i params result admitted
                        simp only [Bool.and_eq_true] at admitted
                        obtain ⟨header, fields⟩ := admitted
                        cases Option.some.inj accepted
                        exact checkHead_sound header (checkFields_sound ih _ _ fields)
                      · simp at accepted
                    · simp at accepted
                  · simp at accepted

/-- A successful checked build is a singleton HE normal form. This retains
the incoming bindings and the exact ordered answer, not only set membership. -/
theorem checkedBuild_delivers {space : Space} {dispatch : GroundedDispatch}
    {fuel : Nat} {value range : Atom} (accepted : check space dispatch fuel value = some range) :
    ∃ bound, ∀ extra expected bindings live, accepts expected range = true →
      evalAtom space dispatch value expected bindings (bound + extra) live = [(value, bindings)] :=
  evalAtom_completed_accepted (check_sound space dispatch fuel value range accepted)

/-- Failure of a constructor field's only ground typing is an HE error, not
an empty answer bag. A declined checked build must return to this protocol. -/
theorem rejectedFirstField {space : Space} {dispatch : GroundedDispatch} {head : String}
    {param arg actual range expected : Atom} {params args : List Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType (param :: params) range])
    (notError : head ≠ "Error")
    (types : getAtomTypes space arg = [actual]) (rejected : accepts param actual = false)
    (groundParam : atomVariables param = []) (groundActual : atomVariables actual = [])
    (lengths : args.length = params.length)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch (.expression (.symbol head :: arg :: args)) expected bindings
      (fuel + 3) live =
        [(mkError (.expression (.symbol head :: arg :: args))
          (.badArgType 1 param actual), bindings)] := by
  have failed := checkIfFunctionTypeIsApplicable_argumentRejected
    (head := head) (range := range) (expected := expected)
    types rejected groundParam groundActual lengths bindings fuel
  have interpreted := interpretExpression_rejected (dispatch := dispatch)
    (live := live) declared (isFunctionType_arrowType ..) failed
  rw [HEReturns.evalAtom_expression (HEReturns.isEmptyOrError_call notError _)
    notAtom notExpression, interpreted]
  rfl

namespace Controls

open Mettapedia.Languages.MeTTa.HE.CompletedDelivery.Controls

theorem nested_constructor_admitted :
    check natSpace GroundedDispatch.none 2 (succ (succ zero)) = some nat := by decide

theorem nested_constructor_delivers :
    ∃ bound, ∀ extra expected bindings live, accepts expected nat = true →
      evalAtom natSpace GroundedDispatch.none (succ (succ zero)) expected bindings
        (bound + extra) live = [(succ (succ zero), bindings)] :=
  checkedBuild_delivers nested_constructor_admitted

/-- An equation at another literal head does not invalidate admission. -/
def unrelatedSpace : Space := natSpace.add
  (equation (.expression [.symbol "other", .var "x"]) (.var "x"))

theorem unrelated_equation_admitted :
    check unrelatedSpace GroundedDispatch.none 2 (succ (succ zero)) = some nat := by decide

theorem incomplete_traversal_declines :
    check natSpace GroundedDispatch.none 1 (succ (succ zero)) = none := by decide

theorem wrong_field_declines :
    check natSpace GroundedDispatch.none 1 (succ (.grounded (.int 3))) = none := by decide

theorem wrong_field_is_error (fuel : Nat) (live : List Atom) :
    evalAtom natSpace GroundedDispatch.none (succ (.grounded (.int 3))) Atom.undefinedType
      Bindings.empty (fuel + 3) live =
        [(mkError (succ (.grounded (.int 3)))
          (.badArgType 1 nat (.symbol "Number")), Bindings.empty)] :=
  rejectedFirstField rfl (by decide) rfl (by decide) rfl rfl rfl
    (by decide) (by decide) Bindings.empty fuel live

theorem equation_reopens_admission :
    check rewrittenSpace GroundedDispatch.none 1 (succ zero) = none := by decide

theorem equation_changes_answer :
    ∃ bound, ∀ extra live,
      evalAtom rewrittenSpace GroundedDispatch.none (succ zero) Atom.undefinedType
        Bindings.empty (bound + extra) live = [(zero, Bindings.empty)] :=
  completed_reopens_after_equation.2.2

/-- A variable left side can match the constructor despite having no named head. -/
def wildcardSpace : Space := natSpace.add (equation (.var "x") zero)

theorem wildcard_equation_declines :
    check wildcardSpace GroundedDispatch.none 1 (succ zero) = none := by decide

theorem multiple_typings_decline :
    check twiceZeroSpace GroundedDispatch.none 1 (succ zero) = none := by decide

theorem multiple_typings_change_multiplicity :
    ∃ bound, ∀ extra live,
      evalAtom twiceZeroSpace GroundedDispatch.none (succ zero) Atom.undefinedType
        Bindings.empty (bound + extra) live =
          [(succ zero, Bindings.empty), (succ zero, Bindings.empty)] :=
  argumentChecked_once_required.2

/-- Structural admission is not permission to ignore source fuel. -/
theorem source_fuel_is_observable :
    check natSpace GroundedDispatch.none 1 (succ zero) = some nat ∧
      evalAtom natSpace GroundedDispatch.none (succ zero) Atom.undefinedType
        Bindings.empty 0 [] ≠ [(succ zero, Bindings.empty)] := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorAdmission
