import Mettapedia.Machines.TIsa.StoreInstructions.WordTests
import Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms

/-!
# Closed first-order premises need no new bindings

A closed pattern can compare its exact code against an occurrence
value. The ordinal is decoded through the packed store, but the
premise records the occurrence identity. Taking an already read
occurrence is still refused even if every value comparison agrees.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.ClosedMatch

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Derivation (Role Match attempt)
open Derivation.FirstOrderTerms (Bindings extend matcher semantics)

variable {σ : LPSignature} [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem mapped_children {f : σ.functionSymbols} (values : Fin (σ.functionArity f) → GroundTerm σ) :
    (finToList values).map GroundTerm.toTerm = finToList (fun k => (values k).toTerm) := by
  simp [finToList, List.map_map, Function.comp_def]

private theorem collect_closed : ∀ terms : List (GroundTerm σ),
    collectBindingsList (terms.map GroundTerm.toTerm) terms = some []
  | [] => by simp [collectBindingsList]
  | .const atom :: rest => by
    rw [List.map_cons, GroundTerm.toTerm, collectBindingsList, if_pos rfl]
    exact collect_closed rest
  | .app f children :: rest => by
    rw [List.map_cons, GroundTerm.toTerm, collectBindingsList, dif_pos rfl]
    change collectBindingsList (finToList (fun k => (children k).toTerm) ++ rest.map GroundTerm.toTerm)
      (finToList children ++ rest) = some []
    rw [← mapped_children, ← List.map_append]
    exact collect_closed (finToList children ++ rest)
termination_by terms => patternListSize (terms.map GroundTerm.toTerm)
decreasing_by
  all_goals
    simp [patternListSize, GroundTerm.toTerm, Term.size, Fin.sum_univ_def, finToList,
      List.map_append, List.sum_append, List.map_map, Function.comp_def]

variable [DecidableEq σ.vars]

theorem extend_closed (binding : Bindings σ) (consistent : BindingsConsistent binding)
    (expected found : GroundTerm σ) :
    extend binding expected.toTerm found = if expected = found then some binding else none := by
  by_cases same : expected = found
  · subst found
    have collected : collectBindings expected.toTerm expected = some [] := collect_closed [expected]
    have sound := (bindingsConsistent?_eq_true binding).mpr consistent
    simp [extend, collected, sound]
  · rw [if_neg same]
    cases matched : extend binding expected.toTerm found with
    | none => rfl
    | some result =>
      obtain ⟨assignment, denoted⟩ := semantics.extend_inhabited binding expected.toTerm found result matched
      have solved := (semantics.extend_iff binding expected.toTerm found assignment).mp ⟨result, matched, denoted⟩
      have fixed := FirstOrder.ground_fixed assignment expected.toTerm (GroundTerm.toTerm_isGround expected)
      exact (same (GroundTerm.toTerm_injective (fixed.symm.trans solved.2))).elim

theorem attempt_closed (role : Role) (expected : GroundTerm σ)
    (entered : Match (GroundTerm σ) (Bindings σ)) (consistent : BindingsConsistent entered.bindings)
    (candidate : ℕ × GroundTerm σ) :
    attempt matcher role expected.toTerm entered candidate =
      if role.allows entered candidate.1 && decide (expected = candidate.2) then
        some (entered.select role candidate.1 entered.bindings)
      else none := by
  simp only [attempt]
  cases eligible : role.allows entered candidate.1
  · simp
  · simp only [Bool.true_and]
    change (extend entered.bindings expected.toTerm candidate.2).map (entered.select role candidate.1) = _
    rw [extend_closed _ consistent]
    by_cases equal : expected = candidate.2 <;> simp [equal]

/-- In-range lookup, eligibility and encoded equality are sufficient
for the complete source effect of the closed-case MATCH. In
particular the next level is changed only on a success. -/
theorem packed_attempt (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ))
    {memory : PackedOccurrences.Layout} (packed : PackedOccurrences.pack codes st.store = some memory)
    (role : Role) (expected found : GroundTerm σ) (identity level : ℕ) (index dst : P1Source.Reg)
    (consistent : BindingsConsistent (st.levels level).bindings)
    (stored : PackedOccurrences.at? codes memory (st.machine.registers index).toNat = some (identity, found))
    (left right : Word) (expectedCode : codes.encode expected = some left) (foundCode : codes.encode found = some right) :
    executeInstruction matcher st (.transform (.premise role expected.toTerm level index dst)) =
      if role.allows (st.levels level) identity && (left == right) then
        .ok ((st.setLevel (level + 1) ((st.levels level).select role identity (st.levels level).bindings)).write dst 1)
      else .ok (st.write dst 0) := by
  rw [PackedOccurrences.at_exact codes packed] at stored
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, stored, attempt_closed _ _ _ consistent]
  have compare : (left == right) = decide (expected = found) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq, decide_eq_true_eq] using WordTests.code_equality codes expectedCode foundCode
  rw [compare]
  by_cases accepts : (role.allows (st.levels level) identity && decide (expected = found)) = true <;> simp [accepts]

namespace Examples

open RuleSyntax.Controls (atoms)

private def ready : Match (GroundTerm atoms) (Bindings atoms) := ⟨[], [], [7], [], []⟩
private def target : GroundTerm atoms := .const 42

theorem a_second_read_records_the_same_identity :
    (attempt matcher .read target.toTerm ready (7, target)).map Match.read = some [7, 7] := by
  rw [attempt_closed .read target ready (fun _ _ _ placed _ => by cases placed)]
  rfl

theorem a_take_after_a_read_is_refused :
    attempt matcher .take target.toTerm ready (7, target) = none := by
  rw [attempt_closed .take target ready (fun _ _ _ placed _ => by cases placed)]
  rfl

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.ClosedMatch
