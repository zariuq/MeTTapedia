import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual

/-!
# Freshness at declaration frames speaks only of what the state mentions

`Firing.Fresh` asks that every instantiation of the state's frame and every instantiation of the
rule's unknowns be realized together on the terms the state mentions and on the rule's terms. So
`information_amalgamates` constrains nothing about a name of the frame that the state does not
mention. Both controls are over the signature with one sort and the numbers as constants, at the
frame with one name `m`.

* **A program firing couples a new unknown to an old name the state does not mention**
  (`coupling_admitted`, `coupling_couples`): the program whose one rule tells `x ≐ y`, with no take,
  read, check, made row or collect pattern, fires at the state with no knowledge and no occurrences,
  with `x` opened to a new name and `y` to `m`; the step of the program admits it, and no solution of
  its information sends `m` to `1` and the new name to `2`. That is the coupling the helper step shows
  at the same state (`HelperControl.nameHelper_coupled`).
* **Where the state mentions `m`, that opening is not fresh** (`coupling_not_fresh_when_mentioned`,
  `coupling_refused_when_mentioned`): with the knowledge `m ≐ m` the step refuses the same firing,
  while the helper firing valued `m` still couples its helper to `m` there (`mentionedHelper_coupled`).
  At such a state, by `information_amalgamates`, a fresh firing of a program that takes and reads no
  row adds no relation between its new unknowns and `m` beyond the knowledge and the rule's tells.
* **"The state mentions" is syntactic** (`tautology_flips_coupling`): the knowledge `m ≐ m`, which every
  instantiation solves and the empty knowledge entails, is what turns the admitted coupling firing into
  a refused one. A name counts as mentioned when it is a side of an equation of the knowledge or the
  label of a present row, whatever the equation says. And "fresh" is not "new": the admitted firing
  opens a rule unknown as the old name `m`, which the state does not mention.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
namespace Contextual
namespace CouplingControls

open Interface (Frames)
open Interface.Frames (Frame)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Helpers.Consumer (tiny constant)
open HelperControl (oneName)

/-- The extension by one new name. -/
abbrev newName : Frame tiny := ⟨Unit, fun _ => ([], ())⟩

/-- The rule's own frame: two parameterless unknowns, `x` (`true`) and `y` (`false`). -/
abbrev twoNames : Frame tiny := ⟨Bool, fun _ => ([], ())⟩

/-- A name of a frame, as a term at it. -/
abbrev nameAt (F : Frame tiny) (name : F.Names) : Terms tiny F := observe (generator F.arity name)

/-- **The rule** `x ≐ y`: no take, read, check or made row, and no collect pattern. -/
def tellRule : Rule (Terms tiny) :=
  ⟨twoNames, ⟨[], [], [(nameAt twoNames true, nameAt twoNames false)], [], []⟩, []⟩

/-- The program of that one rule. -/
def program : Program (Terms tiny) := {tellRule}

/-- The state at `m` with the given knowledge and no occurrences. -/
def stateWith (knowledge : EquationStore (Terms tiny oneName)) : State (Terms tiny) ℕ :=
  ⟨oneName, knowledge, ∅, fun _ => nameAt oneName ()⟩

/-- `m ≐ m`: knowledge that mentions `m` and allows every value of it. -/
def mentionsM : EquationStore (Terms tiny oneName) := [(nameAt oneName (), nameAt oneName ())]

/-- **The coupling opening**: `x` to the new name, `y` to the old name `m`. -/
def couplingOpening : Assignment twoNames.arity (extend tiny oneName newName).arity
  | true => generator (extend tiny oneName newName).arity (.inr ())
  | false => generator (extend tiny oneName newName).arity (.inl ())

/-- The firing of the rule with the coupling opening and the empty selection. -/
def coupling : Firing ℕ (declarations tiny) program oneName :=
  ⟨tellRule, Set.mem_singleton tellRule, newName, couplingOpening, ⟨[], [], []⟩, []⟩

/-- The rule's terms are `x` and `y`. -/
theorem rule_terms : tellRule.terms = [nameAt twoNames true, nameAt twoNames false] := rfl

theorem mem_terms_y : nameAt twoNames false ∈ tellRule.terms := by
  rw [rule_terms]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- **A name, acted on by an assignment**, is the assignment's value at it. -/
theorem act_name {F G : Frame tiny} (u : Assignment F.arity G.arity) (name : F.Names) :
    (Frames.contextual tiny).act u (nameAt F name) = observe (u name) := by
  show instantiateObservation u (observe (generator F.arity name)) = observe (u name)
  rw [instantiateObservation_observe, instantiate_generator]

theorem act_x : (Frames.contextual tiny).act couplingOpening (nameAt twoNames true) =
    nameAt (extend tiny oneName newName) (.inr ()) :=
  act_name couplingOpening true

theorem act_y : (Frames.contextual tiny).act couplingOpening (nameAt twoNames false) =
    nameAt (extend tiny oneName newName) (.inl ()) :=
  act_name couplingOpening false

theorem act_m : (Frames.contextual tiny).act (weakenNames tiny oneName newName) (nameAt oneName ()) =
    nameAt (extend tiny oneName newName) (.inl ()) :=
  act_name (F := oneName) (weakenNames tiny oneName newName) ()

/-- The opened tell is in the information, at every state at `m`. -/
theorem tell_mem (knowledge : EquationStore (Terms tiny oneName)) :
    ((Frames.contextual tiny).act couplingOpening (nameAt twoNames true),
      (Frames.contextual tiny).act couplingOpening (nameAt twoNames false)) ∈
      coupling.information (Frames.contextual tiny) (stateWith knowledge) :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- An instantiation of the extended frame from one of the rule's unknowns: `m` to `y`'s value, the
new name to `x`'s. -/
def amalgam {B : Frame tiny} (h : Assignment twoNames.arity B.arity) :
    Assignment (extend tiny oneName newName).arity B.arity
  | .inl () => h false
  | .inr () => h true

/-- A solution of the coupling information: both names to `m`. -/
def bothToM : Assignment (extend tiny oneName newName).arity oneName.arity
  | .inl () => generator oneName.arity ()
  | .inr () => generator oneName.arity ()

/-- **At a state that mentions nothing the coupling opening is fresh.** -/
theorem coupling_fresh : coupling.Fresh (Frames.contextual tiny) (stateWith []) := by
  intro B g h
  refine ⟨amalgam h, ?_, ?_⟩
  · rintro t (mem | mem | ⟨o, mem, -⟩)
    · cases mem
    · cases mem
    · simp [stateWith] at mem
  · intro t mem
    have terms : t ∈ [nameAt twoNames true, nameAt twoNames false] := mem
    rcases List.mem_cons.mp terms with rfl | terms
    · exact (congrArg ((Frames.contextual tiny).act (amalgam h)) act_x).trans
        ((act_name (amalgam h) (.inr ())).trans (act_name h true).symm)
    · rcases List.mem_cons.mp terms with rfl | terms
      · exact (congrArg ((Frames.contextual tiny).act (amalgam h)) act_y).trans
          ((act_name (amalgam h) (.inl ())).trans (act_name h false).symm)
      · cases terms

/-- **The step of the program admits the coupling firing at the state that mentions nothing.** -/
theorem coupling_admitted :
    (step (Frames.contextual tiny) ℕ (declarations tiny) program).Admits (s := stateWith []) coupling := by
  refine (admits_iff (s := stateWith []) coupling).mpr ⟨coupling_fresh,
    ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [coupling, stateWith, Selection.commit]
  · refine ⟨oneName, bothToM, ?_⟩
    intro e mem
    have told : e ∈ [((Frames.contextual tiny).act couplingOpening (nameAt twoNames true),
        (Frames.contextual tiny).act couplingOpening (nameAt twoNames false))] := mem
    rcases List.mem_cons.mp told with rfl | told
    · exact (congrArg ((Frames.contextual tiny).act bothToM) act_x).trans
        ((act_name bothToM (.inr ())).trans ((act_name bothToM (.inl ())).symm.trans
          (congrArg ((Frames.contextual tiny).act bothToM) act_y).symm))
    · cases told
  · intro c mem
    cases mem
  · intro q mem
    cases mem

/-- **The coupling firing couples the new name to `m`**, at every state at `m`: no solution of its
information sends `m` to `1` and the new name to `2`. -/
theorem coupling_couples (knowledge : EquationStore (Terms tiny oneName)) :
    ¬ ∃ (B : Frame tiny) (u : Assignment (extend tiny oneName newName).arity B.arity),
      (Frames.contextual tiny).Models u (coupling.information (Frames.contextual tiny) (stateWith knowledge)) ∧
        u (.inl ()) = constant 1 ∧ u (.inr ()) = constant 2 := by
  rintro ⟨B, u, solved, old, new⟩
  have told := solved _ (tell_mem knowledge)
  change (Frames.contextual tiny).act u ((Frames.contextual tiny).act couplingOpening
      (nameAt twoNames true)) = (Frames.contextual tiny).act u ((Frames.contextual tiny).act
        couplingOpening (nameAt twoNames false)) at told
  rw [act_x, act_y, act_name, act_name] at told
  have same := observe_injective told
  rw [old, new] at same
  simp [constant] at same

/-- **Where the state mentions `m`, the coupling opening is not fresh**: an instantiation sending `m`
to `1` and one sending `y` to `2` are not realized together, since the opening sends `y` to `m`. -/
theorem coupling_not_fresh_when_mentioned :
    ¬ coupling.Fresh (Frames.contextual tiny) (stateWith mentionsM) := by
  intro fresh
  obtain ⟨u, onState, onRule⟩ := fresh oneName (fun _ => constant 1) (fun _ => constant 2)
  have stateSide := onState (nameAt oneName ()) (Or.inl (List.mem_singleton_self _))
  have ruleSide := onRule (nameAt twoNames false) mem_terms_y
  change (Frames.contextual tiny).act u ((Frames.contextual tiny).act
      (weakenNames tiny oneName newName) (nameAt oneName ())) =
    (Frames.contextual tiny).act (fun _ => constant 1) (nameAt oneName ()) at stateSide
  change (Frames.contextual tiny).act u ((Frames.contextual tiny).act couplingOpening
      (nameAt twoNames false)) = (Frames.contextual tiny).act (fun _ => constant 2)
        (nameAt twoNames false) at ruleSide
  have left := (act_name (F := extend tiny oneName newName) u (.inl ())).symm.trans
    ((congrArg ((Frames.contextual tiny).act u) act_m).symm.trans
      (stateSide.trans (act_name (F := oneName) (fun _ => constant 1) ())))
  have right := (act_name (F := extend tiny oneName newName) u (.inl ())).symm.trans
    ((congrArg ((Frames.contextual tiny).act u) act_y).symm.trans
      (ruleSide.trans (act_name (F := twoNames) (fun _ => constant 2) false)))
  have same := observe_injective (left.symm.trans right)
  simp [constant] at same

/-- **The step refuses the coupling firing where the state mentions `m`.** -/
theorem coupling_refused_when_mentioned :
    ¬ (step (Frames.contextual tiny) ℕ (declarations tiny) program).Admits (s := stateWith mentionsM)
      coupling := fun admitted =>
  coupling_not_fresh_when_mentioned ((admits_iff (s := stateWith mentionsM) coupling).mp admitted).1

/-- **A tautology decides the coupling**: the empty knowledge entails `m ≐ m`, so the two knowledges
have the same solutions; yet the coupling firing is admitted with the empty knowledge and refused
with `m ≐ m`. Freshness reads what the state mentions syntactically, not what its knowledge says. -/
theorem tautology_flips_coupling :
    (Frames.contextual tiny).Entails (a := oneName) []
        (fun _ u => (Frames.contextual tiny).Models u mentionsM) ∧
      (step (Frames.contextual tiny) ℕ (declarations tiny) program).Admits (s := stateWith []) coupling ∧
      ¬ (step (Frames.contextual tiny) ℕ (declarations tiny) program).Admits (s := stateWith mentionsM)
        coupling :=
  ⟨fun b _ _ e inside => by
      rw [List.mem_singleton.mp inside]
      exact ((Frames.contextual tiny).equivalence b).refl _,
    coupling_admitted, coupling_refused_when_mentioned⟩

/-! ## The helper step at a state that mentions `m` -/

/-- The helper step's state at `m` with the knowledge `m ≐ m`. -/
abbrev mentioning : Interface.Helpers.State tiny ℕ := ⟨oneName, mentionsM, ∅⟩

/-- Make occurrence `0` and a helper whose value is `m`. -/
def mentionedHelper : Interface.Helpers.Firing mentioning := ⟨0, ([], ()), generator oneName.arity (), []⟩

/-- **The helper firing couples its helper to `m` at a state that mentions `m`**: no solution of its
information sends `m` to `1` and the helper to `2`. -/
theorem mentionedHelper_coupled :
    ¬ ∃ (B : Frame tiny) (u : Assignment (Interface.Helpers.extend oneName ([], ())).arity B.arity),
      (Frames.contextual tiny).Models u mentionedHelper.information ∧ u (.inl ()) = constant 1 ∧
        u (.inr ()) = constant 2 := by
  rintro ⟨B, u, solved, old, new⟩
  have coupled := helper_coupled mentionedHelper u solved
  have helperValue : instantiate u (Interface.Helpers.fresh oneName ([], ())) = u (.inr ()) :=
    instantiate_generator u (.inr ())
  have oldValue : instantiate (Assignment.compose u (Interface.Helpers.incl oneName ([], ())))
      (generator oneName.arity ()) = u (.inl ()) := by
    rw [instantiate_generator]
    exact instantiate_generator u (.inl ())
  have same : u (.inr ()) = u (.inl ()) := helperValue.symm.trans (coupled.trans oldValue)
  rw [old, new] at same
  simp [constant] at same

end CouplingControls
end Contextual

#print axioms Contextual.CouplingControls.coupling_fresh
#print axioms Contextual.CouplingControls.coupling_admitted
#print axioms Contextual.CouplingControls.coupling_couples
#print axioms Contextual.CouplingControls.coupling_not_fresh_when_mentioned
#print axioms Contextual.CouplingControls.coupling_refused_when_mentioned
#print axioms Contextual.CouplingControls.tautology_flips_coupling
#print axioms Contextual.CouplingControls.mentionedHelper_coupled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
