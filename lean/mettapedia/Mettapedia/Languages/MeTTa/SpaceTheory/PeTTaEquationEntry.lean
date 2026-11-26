import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution

/-!
# An explicit equation view at PeTTa function entry

PeTTa's ordinary source interpreter is unchanged. For a caller choosing
to observe function entry modulo equations, saturate only the ready request.
A selected ordered alternative list, including its captured bindings, is
an ordinary value of the continuation and is not quotiented. Primitives
and argument evaluation remain at their original source boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT
open PeTTaExecution (programAt programAt_exact theoryAt live_rewrite_iff)

/-- The ordinary saturated entry of a function definition at this
snapshot. A successful empty list is not the refusal to take this step. -/
def select (atoms : List Atom) (ready : Atom) : Option (List Eval.Control) :=
  match ready with
  | .expression (.symbol head :: values) =>
    let program := programAt atoms
    if Eval.ioHead head || StdLib.known head then none
    else if values.length ∈ Eval.arities program head then some (Eval.clauses program head values)
    else none
  | _ => none

theorem select_ready (atoms : List Atom) (head : String) (values : List Atom)
    (ordinary : Eval.ioHead head = false) (nonnative : StdLib.known head = false)
    (saturated : values.length ∈ Eval.arities (programAt atoms) head) :
    select atoms (.expression (.symbol head :: values)) = some (Eval.clauses (programAt atoms) head values) := by
  simp only [select, ordinary, nonnative, Bool.or_false, Bool.false_eq_true,
    if_false, if_pos saturated]

theorem ordinary_entry_exact (atoms : List Atom) (source : Eval.Configuration)
    (bindings : Subst) (head : String) (values : List Atom) (position : Nat)
    (ready : source.control = .arguments bindings (.function head) [] values position)
    (ordinary : Eval.ioHead head = false) (nonnative : StdLib.known head = false)
    (saturated : values.length ∈ Eval.arities (programAt atoms) head)
    (alternatives : List Eval.Control) :
    select atoms (.expression (.symbol head :: values)) = some alternatives ↔
      (theoryAt atoms).Step source { source with control := .sequence alternatives [] } := by
  change _ ↔ (Eval.theory (programAt atoms)).Step source _
  rw [Eval.theory_step_iff]
  simp only [select, ordinary, nonnative, Bool.or_false, Bool.false_eq_true, if_false,
    if_pos saturated, Eval.step, ready, Eval.application_saturated saturated, Option.some.injEq]
  cases source
  simp

def theory (atoms : List Atom) : GSLT :=
  EndpointSaturation.inputTheory (AtomEquations.setoid atoms)
    (fun call alternatives => select atoms call = some alternatives)

/-- An equation-aware entry takes precisely the alternatives of some
ordinary representative. It does not merge or rewrite those alternatives
after selection. -/
theorem entry_exact (atoms : List Atom) (call : Atom) (alternatives : List Eval.Control) :
    (theory atoms).Step (.inl call) (.inr alternatives) ↔
      ∃ representative, AtomEquations.Equivalent atoms call representative ∧
        select atoms representative = some alternatives :=
  EndpointSaturation.input_step_iff (AtomEquations.setoid atoms) _ call alternatives

theorem entered_equality_is_literal (atoms : List Atom) (first second : List Eval.Control) :
    (theory atoms).Equiv (.inr first) (.inr second) ↔ first = second :=
  EndpointSaturation.output_eq_iff (AtomEquations.setoid atoms) _ first second

theorem already_entered_is_final_here (atoms : List Atom) (alternatives : List Eval.Control) :
    (theory atoms).IsNormalForm (.inr alternatives) :=
  EndpointSaturation.output_is_final (AtomEquations.setoid atoms) _ alternatives

private theorem select_call_shape {atoms : List Atom} {ready : Atom} {alternatives : List Eval.Control}
    (selected : select atoms ready = some alternatives) :
    ∃ head values, ready = .expression (.symbol head :: values) ∧
      Eval.ioHead head = false ∧ StdLib.known head = false ∧
      values.length ∈ Eval.arities (programAt atoms) head := by
  cases ready with
  | expression args =>
    cases args with
    | nil => cases selected
    | cons first values =>
      cases first with
      | symbol head =>
        have ordinary : (Eval.ioHead head || StdLib.known head) = false := by
          cases found : Eval.ioHead head || StdLib.known head
          · rfl
          · simp [select, found] at selected
        have saturated : values.length ∈ Eval.arities (programAt atoms) head := by
          by_contra missing
          simp only [select, ordinary, Bool.false_eq_true, if_false, if_neg missing] at selected
          cases selected
        have tests := Bool.or_eq_false_iff.mp ordinary
        exact ⟨head, values, rfl, tests.1, tests.2, saturated⟩
      | _ => cases selected
  | _ => cases selected

/-- At a live source state, entry uses the current definitions of that
state. The ordinary step at the chosen representative has the same store,
frames, and publication history. Only its ready request and then its
ordered alternatives are selected by the equation view. -/
theorem equation_entry_in_live_registry (source : Eval.Configuration) (call : Atom)
    (alternatives : List Eval.Control) (bindings : Subst) (position : Nat) :
    (theory source.state.core).Step (.inl call) (.inr alternatives) ↔
      ∃ head values,
        AtomEquations.Equivalent source.state.core call (.expression (.symbol head :: values)) ∧
        Eval.ioHead head = false ∧ StdLib.known head = false ∧
        values.length ∈ Eval.arities (programAt source.state.core) head ∧
        LiveRegistry.theory.Step
          { source with control := .arguments bindings (.function head) [] values position }
          { source with control := .sequence alternatives [] } := by
  rw [entry_exact]
  constructor
  · rintro ⟨representative, same, selected⟩
    obtain ⟨head, values, rfl, ordinary, nonnative, saturated⟩ := select_call_shape selected
    refine ⟨head, values, same, ordinary, nonnative, saturated, ?_⟩
    let ready : Eval.Configuration :=
      { source with control := .arguments bindings (.function head) [] values position }
    apply (live_rewrite_iff ready _).mpr
    exact (ordinary_entry_exact source.state.core ready bindings head values position
      rfl ordinary nonnative saturated alternatives).mp selected
  · rintro ⟨head, values, same, ordinary, nonnative, saturated, fired⟩
    refine ⟨_, same, ?_⟩
    let ready : Eval.Configuration :=
      { source with control := .arguments bindings (.function head) [] values position }
    exact (ordinary_entry_exact source.state.core ready bindings head values position
      rfl ordinary nonnative saturated alternatives).mpr ((live_rewrite_iff ready _).mp fired)

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)

/-- The selected entry passes through the existing Transform compiler at
its actual representative and snapshot. No equation is imposed on the
captured continuation or the rest of the store. -/
theorem equation_entry_representative_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (source : Eval.Configuration) (call : Atom) (alternatives : List Eval.Control)
    (bindings : Subst) (position : Nat)
    (entry : (theory source.state.core).Step (.inl call) (.inr alternatives)) :
    ∃ head values,
      AtomEquations.Equivalent source.state.core call (.expression (.symbol head :: values)) ∧
      ∀ start : SState O,
        EvalOnTheStep.Shows
          { source with control := .arguments bindings (.function head) [] values position } start →
        ∃ final, (EvalOnTheStep.stepSystem O (programAt source.state.core)).Step start final ∧
          EvalOnTheStep.Shows { source with control := .sequence alternatives [] } final := by
  obtain ⟨head, values, eq, _, _, _, fired⟩ :=
    (equation_entry_in_live_registry source call alternatives bindings position).mp entry
  refine ⟨head, values, eq, ?_⟩
  intro start shown
  exact PeTTaExecution.snapshot_step_on_transform source.state.core shown
    ((live_rewrite_iff _ _).mp fired)

theorem entry_without_equations (atoms : List Atom)
    (noneWritten : ∀ a b, ¬ AtomEquations.Generator atoms a b)
    (call : Atom) (alternatives : List Eval.Control) :
    (theory atoms).Step (.inl call) (.inr alternatives) ↔ select atoms call = some alternatives := by
  rw [entry_exact]
  constructor
  · rintro ⟨representative, equal, selected⟩
    exact ((AtomEquations.without_generators atoms noneWritten _ _).mp equal).symm ▸ selected
  · exact fun selected => ⟨call, .refl _, selected⟩

section Controls

open Mettapedia.Languages.MeTTa.SpaceTheory.Atoms (Content)

private def left : Atom := .symbol "A"
private def right : Atom := .symbol "B"
private def sameDefinition : Atom :=
  (Content.definition (.expression [.symbol "same", .var "x", .var "x"]) (.symbol "OK")).syntax
private def equation : Atom :=
  (Content.equation .indifferent left right []).syntax
private def written : List Atom := [sameDefinition, equation]
private def differentCall : Atom := .expression [.symbol "same", left, right]
private def equalCall : Atom := .expression [.symbol "same", left, left]

theorem different_arguments_have_no_plain_alternatives :
    select written differentCall = some [] := by
  change select written (.expression [.symbol "same", left, right]) = some []
  have saturated : ([left, right] : List Atom).length ∈ Eval.arities (programAt written) "same" := by
    rw [programAt_exact]
    decide +kernel
  have empty : (Eval.clauses (programAt written) "same" [left, right]).length = 0 := by
    rw [programAt_exact]
    decide +kernel
  rw [select_ready written "same" [left, right] (by decide +kernel) (by decide +kernel) saturated,
    List.length_eq_zero_iff.mp empty]

theorem only_the_explicit_equation_entry_gets_the_alternative :
    ∃ alternatives, (theory written).Step (.inl differentCall) (.inr alternatives) ∧
      alternatives.length = 1 := by
  have identified : AtomEquations.Equivalent written left right :=
    AtomEquations.authored ⟨.indifferent, right, [],
      List.mem_cons_of_mem sameDefinition List.mem_cons_self, List.mem_cons_self⟩
  have equal : AtomEquations.Equivalent written differentCall equalCall :=
    AtomEquations.fill_equivalent (.child [.symbol "same", left] .hole [])
      (.symm _ _ identified)
  let alternatives := Eval.clauses (programAt written) "same" [left, left]
  refine ⟨alternatives, (entry_exact _ _ _).mpr ⟨equalCall, equal, ?_⟩, ?_⟩
  · change select written (.expression [.symbol "same", left, left]) = some alternatives
    apply select_ready written "same" [left, left] (by decide +kernel) (by decide +kernel)
    rw [programAt_exact]
    decide +kernel
  · simp only [alternatives, programAt_exact]
    decide +kernel

/-- A single spelling, even one chosen independently of printing,
cannot implement this whole explicit entry view. A completed empty
frontier and a one-alternative frontier are both genuine observations. -/
theorem one_spelling_cannot_select_both_frontiers (representative : Atom) :
    ¬ (∀ alternatives, (theory written).Step (.inl differentCall) (.inr alternatives) ↔
      select written representative = some alternatives) := by
  intro all
  have emptyStep : (theory written).Step (.inl differentCall) (.inr []) :=
    (entry_exact _ _ _).mpr ⟨differentCall, .refl _, different_arguments_have_no_plain_alternatives⟩
  have empty := (all []).mp emptyStep
  obtain ⟨nonempty, admitted, length⟩ := only_the_explicit_equation_entry_gets_the_alternative
  have other := (all nonempty).mp admitted
  have equal := Option.some.inj (other.symm.trans empty)
  simp [equal] at length

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationEntry
