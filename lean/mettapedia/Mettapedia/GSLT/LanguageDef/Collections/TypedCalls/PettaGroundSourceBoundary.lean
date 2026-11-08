import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaPrivateGroundBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns
import Mettapedia.Languages.MeTTa.PeTTa.EagerDFS

/-!
# Actual protected source returns and concrete intrinsic guards

The source body is the existing substitution-bearing Unifying machine, with
its real effects, recursive calls and ordered answer packets. The result
recipe is earned by its syntax checker. A partial finite-value codec connects
the protected source datum to the intrinsic query carrier, and the actual
query/join checks are shown readonly at each returned occurrence.

This is a body/delivery boundary, not a second evaluator or a proof that the
typed Destination overlay and Unifying are the same whole machine. The
native allocator, physical caller-record lowering, classifier authority and
declaration currentness remain separate admission obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaGroundSourceBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Logic.LP (Subst)
open IntrinsicTypeFacts (TypeTerm signature Declaration)
open IndependentTypeOutput (row Path)
open StableGroundTypeQueries (GroundUninterpreted groundSchema)
open PettaPrivateGroundBoundary (entered)

mutual
/-- Ground finite structural source values only. Unknown host objects and
unresolved variables stay unserved; alternate symbolic truth aliases use
the existing structural admission rather than acquiring a false codec. -/
def encodeGround : Atom → Option TypeTerm
  | .var _ => none
  | .symbol name =>
      if EagerDFS.Destination.finiteStructural (.symbol name) then some (.const (.symbol name)) else none
  | .grounded (.int value) => some (.const (.number (toString value)))
  | .grounded (.string value) => some (.const (.string value))
  | .grounded (.bool value) => some (.const (.boolean value))
  | .grounded (.custom _ _) => none
  | .expression children => (encodeGroundList children).map row

def encodeGroundList : List Atom → Option (List TypeTerm)
  | [] => some []
  | first :: rest => do
      let head ← encodeGround first
      let tail ← encodeGroundList rest
      pure (head :: tail)
end

mutual
theorem encoded_source_ground : ∀ (value : Atom) (encoded : TypeTerm),
    encodeGround value = some encoded → MORK.isGroundAtom value = true
  | .var _, _, encoded => by simp [encodeGround] at encoded
  | .symbol _, _, _ => rfl
  | .grounded _, _, _ => rfl
  | .expression children, encoded, computed => by
      obtain ⟨parts, computedParts, _⟩ := Option.map_eq_some_iff.mp computed
      exact encoded_source_list_ground children parts computedParts

theorem encoded_source_list_ground : ∀ (values : List Atom) (encoded : List TypeTerm),
    encodeGroundList values = some encoded → MORK.isGroundAtom.isGroundList values = true
  | [], _, _ => rfl
  | first :: rest, encoded, computed => by
      cases head : encodeGround first with
      | none => simp [encodeGroundList, head] at computed
      | some one =>
          cases tail : encodeGroundList rest with
          | none => simp [encodeGroundList, head, tail] at computed
          | some more =>
              simp only [MORK.isGroundAtom.isGroundList,
                encoded_source_ground first one head, encoded_source_list_ground rest more tail]
              rfl
end

/-- The actual ordered source packets survive the guard, with the caller
record obtained from the input's one concrete refinement. No successful
source run, return value or recursive outcome is built into the analyser. -/
theorem checked_source_delivers_readonly_guards {program : SpaceSemantics.Program}
    (bindings : MORK.Subst) (valid : Unifying.Idempotent bindings) (parameter : String)
    (body : Atom) (inspectionFuel : Nat)
    (recognized : Unifying.checksReturnVariable parameter inspectionFuel body = true)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (representation : TypeTerm)
    (encoded : encodeGround (Unifying.resolve bindings (.var parameter)) = some representation)
    (library : List Declaration) (queryFuel : Nat) (path : Path)
    (caller : Subst signature) (expected rangeExpected : TypeTerm) (typeName : Nat)
    (unbound : caller.applyTerm expected = .var typeName)
    (rangeUnbound : caller.applyTerm rangeExpected = .var typeName)
    (admitted : GroundUninterpreted library representation) (enough : representation.size ≤ queryFuel)
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : Unifying.run program fuel
      { state, control := .evaluate bindings body, input, output, uses := use } =
        .complete after values remaining printed) :
    StableGroundGuardDischarge.check library queryFuel path caller representation expected =
        some [entered caller typeName representation] ∧
    ∃ final answers,
      Relation.ReflTransGen (Unifying.Transition program)
        { state, control := .evaluate bindings body, input, output, uses := use } final ∧
      final.control = .returned answers ∧ final.frames = [] ∧
      final.state = after ∧ final.input = remaining ∧ final.output = printed ∧
      values = List.replicate answers.length (Unifying.resolve bindings (.var parameter)) ∧
      (∀ answer ∈ answers, Unifying.BindingRefines bindings answer.bindings) ∧
      (∀ answer ∈ answers,
        encodeGround (Unifying.resolve answer.bindings answer.value) = some representation) ∧
      (∀ refinements : Unifying.Answer → Subst signature,
        answers.map (fun answer => StableGroundGuardDischarge.check library queryFuel path
          (Subst.comp (refinements answer) (entered caller typeName representation)) representation rangeExpected) =
        answers.map (fun answer => some [Subst.comp (refinements answer) (entered caller typeName representation)])) := by
  have readValue : caller.applyTerm representation = representation :=
    Mettapedia.Logic.LP.ConjunctiveUnification.applyTerm_of_isGround caller
      (StableGroundTypeQueries.admitted_is_ground _ _ admitted)
  have clean : GroundUninterpreted library (caller.applyTerm representation) := by
    rw [readValue]
    exact admitted
  have depth : (caller.applyTerm representation).size ≤ queryFuel := by simpa only [readValue] using enough
  refine ⟨StableGroundGuardDischarge.input_guard_single_refinement library queryFuel path caller
    representation expected typeName unbound clean depth, ?_⟩
  have ground := encoded_source_ground _ _ encoded
  obtain ⟨final, answers, steps, returned, frames, stateEq, inputEq, outputEq, packets, count⟩ :=
    Unifying.completed_protected_return bindings valid parameter body
      (Unifying.checksReturnVariable_sound parameter inspectionFuel body recognized)
      state input output use ground completed
  refine ⟨final, answers, steps, returned, frames, stateEq, inputEq, outputEq, count, ?_, ?_, ?_⟩
  · exact Unifying.reached_answers_refine steps
      (Unifying.evaluation_entry_refines bindings valid state body input output use) answers returned
  · intro answer present
    rw [packets answer present]
    change encodeGround (MORK.applySubst answer.bindings (Unifying.resolve bindings (.var parameter))) = _
    rw [Unifying.applySubst_ground answer.bindings _ ground]
    exact encoded
  · intro refinements
    apply List.map_congr_left
    intro answer _
    exact PettaPrivateGroundBoundary.refined_return_is_readonly library caller (refinements answer)
      typeName representation rangeExpected queryFuel path rangeUnbound clean depth

namespace Controls

theorem source_truth_uses_intrinsic_bool :
    encodeGround (.grounded (.bool true)) = some (.const (.boolean true)) ∧
      encodeGround (.symbol "true") = none := by cbv

theorem unresolved_source_is_not_ground_encoded : encodeGround (.var "x") = none := rfl

theorem opaque_source_is_not_silently_symbol_encoded :
    encodeGround (.grounded (.custom "opaque" "payload")) = none := rfl

theorem structural_source_value_is_encoded :
    encodeGround (.expression [.symbol "raw", .grounded (.int 7)]) =
      some (row [.const (.symbol "raw"), .const (.number "7")]) := by cbv

/-- The actual source run prints 1,1,2 and returns three copies of 7.
Every completed return query still has its one concrete caller outcome. -/
theorem three_source_occurrences_have_three_guard_outcomes :
    ∃ (final : Unifying.Configuration) (answers : List Unifying.Answer),
      final.output = [Unifying.ReturnControls.num 1, Unifying.ReturnControls.num 1,
        Unifying.ReturnControls.num 2] ∧ answers.length = 3 ∧
      answers.map (fun _ => StableGroundGuardDischarge.check [] 1 []
        (entered (Subst.id signature) 0 (.const (.number "7")))
        (.const (.number "7")) (.var 0)) =
      List.replicate 3 (some [entered (Subst.id signature) 0 (.const (.number "7"))]) := by
  obtain ⟨after, completed⟩ := SourceContractReturns.Controls.complete_print_run
  have joined := checked_source_delivers_readonly_guards
    Unifying.ReturnControls.bindings SourceContractReturns.Controls.print_entry_idempotent
    "protected" Unifying.ReturnControls.branchAndPrint 3
    Unifying.ReturnControls.return_recognizer_controls.1 Effects.empty [] [] 0
    (.const (.number "7")) (by cbv) [] 1 [] (Subst.id signature) (.var 0) (.var 0) 0 rfl rfl
    (by trivial) (by decide +kernel) completed
  obtain ⟨_, final, answers, _steps, _returned, _frames, _stateEq, _inputEq, outputEq, count,
    _refined, _encoded, guards⟩ := joined
  have length : answers.length = 3 := by
    have counted := congrArg List.length count
    simpa using counted.symm
  refine ⟨final, answers, outputEq, length, ?_⟩
  have exactGuards := guards (fun _ => Subst.id signature)
  simp only [Subst.comp_id_left] at exactGuards
  rw [exactGuards, List.map_const']
  rw [length]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaGroundSourceBoundary
