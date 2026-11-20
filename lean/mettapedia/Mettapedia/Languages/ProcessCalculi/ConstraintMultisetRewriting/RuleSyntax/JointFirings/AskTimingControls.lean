import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Knowledge

/-! # Separating and positive controls for ask timing -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTimingControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms action)

abbrev Tm := Terms (Term atoms)
abbrev X := frames action
abbrev E := ext action
def v (n : ℕ) : Term atoms := .var n
def c (n : ℕ) : Term atoms := .const n

def selfRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[], [], [(v 0, c 5)], [.equal (v 0) (c 5)], []⟩, []⟩
def selfProgram : Program Tm := {selfRule}
def emptyState : State Tm ℕ := ⟨PUnit.unit, [], ∅, fun _ => v 0⟩
def selfFiring : Firing ℕ E selfProgram PUnit.unit :=
  ⟨selfRule, Set.mem_singleton _, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, []⟩

theorem self_fresh : selfFiring.Fresh X emptyState := by
  intro b g h
  cases b
  refine ⟨h, ?_, ?_⟩
  · intro term mentioned
    simp [State.Mentions, emptyState] at mentioned
  · intro term _
    change h.applyTerm ((Subst.id atoms).applyTerm term) = h.applyTerm term
    rw [Subst.applyTerm_id]

theorem self_information : selfFiring.information X emptyState = [(v 0, c 5)] := rfl
theorem self_ask_information : selfFiring.askInformation X emptyState = [] := rfl

theorem self_after : selfFiring.Admits X emptyState := by
  refine ⟨⟨self_fresh, by decide, by decide, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact enabled_nil ∅
  · refine ⟨PUnit.unit, (fun _ => c 5), fun equation inside => ?_⟩
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b assignment solves
    refine ⟨?_, ?_⟩
    · intro check member
      obtain rfl := List.mem_singleton.mp member
      exact solves (v 0, c 5) List.mem_cons_self
    · intro query member
      cases member

theorem self_before_refused : ¬ selfFiring.AdmitsBeforeTells X emptyState := by
  intro admitted
  have known : X.Models (a := PUnit.unit) (b := PUnit.unit) (fun _ => c 0)
      (selfFiring.askInformation X emptyState) := by rw [self_ask_information]; exact Interface.Frames.models_nil _
  have check := (admitted.2.2.2 PUnit.unit (fun _ => c 0) known).1
    (.equal (v 0) (c 5)) List.mem_cons_self
  have impossible : c 0 = c 5 := check
  simp [c] at impossible

theorem strict_inclusion : selfFiring.Admits X emptyState ∧
    ¬ selfFiring.AdmitsBeforeTells X emptyState := ⟨self_after, self_before_refused⟩

theorem self_bag_after : (Bag.single selfFiring).Admits X emptyState :=
  (Bag.single_admits_iff X emptyState selfFiring).mpr self_after

theorem self_bag_before_refused : ¬ (Bag.single selfFiring).AdmitsBeforeTells X emptyState := by
  intro before
  exact self_before_refused ((Bag.beforeTells_single X emptyState (Member.ofFiring selfFiring)).mp before)

theorem mutual_matching_only : Knowledge.both.askInformation Examples.X Knowledge.start =
    [(Knowledge.v 2, Knowledge.v 0), (Knowledge.v 3, Knowledge.v 1),
     (Knowledge.v 4, Knowledge.v 0), (Knowledge.v 5, Knowledge.v 1)] := rfl

theorem mutual_before_refused :
    ¬ Knowledge.both.AdmitsBeforeTells Examples.X Knowledge.start := by
  intro admitted
  have known : Examples.X.Models (a := PUnit.unit) (b := PUnit.unit) (fun _ => Examples.c 0)
      (Knowledge.both.askInformation Examples.X Knowledge.start) := by
    rw [mutual_matching_only]
    intro equation inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;> rfl
  have all := admitted.2.2.2 PUnit.unit (fun _ => Examples.c 0) known Knowledge.first List.mem_cons_self
  have bad := all.1 (.equal (Knowledge.v 3) (Examples.c 6)) List.mem_cons_self
  have impossible : Examples.c 0 = Examples.c 6 := bad
  simp [Examples.c] at impossible

theorem a_tell_free_take_is_before :
    Examples.consumeFiring.AdmitsBeforeTells Examples.X Examples.tokenState := by
  exact (Firing.beforeTells_iff_of_no_tells Examples.X Examples.tokenState Examples.consumeFiring rfl).mpr
    Examples.consume_admitted

theorem inconsistent_tells_refused {P : Program Tm} (f : Firing ℕ E P PUnit.unit)
    (both : (v 0, c 5) ∈ f.information X emptyState ∧ (v 0, c 6) ∈ f.information X emptyState) :
    ¬ f.AdmitsBeforeTells X emptyState := by
  intro admitted
  obtain ⟨b, assignment, solves⟩ := admitted.2.2.1
  have five := solves (v 0, c 5) both.1
  have six := solves (v 0, c 6) both.2
  have impossible : c 5 = c 6 := Eq.trans (Eq.symm five) six
  simp [c] at impossible

namespace Inconsistent

def rule : Rule Tm := ⟨PUnit.unit, ⟨[], [], [(v 0, c 5), (v 0, c 6)], [], []⟩, []⟩
def program : Program Tm := {rule}
def firing : Firing ℕ E program PUnit.unit :=
  ⟨rule, Set.mem_singleton _, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, []⟩

theorem after_refused : ¬ firing.Admits X emptyState := by
  intro admitted
  obtain ⟨_, assignment, solves⟩ := admitted.2.2.1
  have five := solves (v 0, c 5) List.mem_cons_self
  have six := solves (v 0, c 6) (List.mem_cons_of_mem _ List.mem_cons_self)
  have impossible : c 5 = c 6 := five.symm.trans six
  simp [c] at impossible

theorem before_refused : ¬ firing.AdmitsBeforeTells X emptyState := by
  exact inconsistent_tells_refused firing ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem bag_refused : ¬ (Bag.single firing).AdmitsBeforeTells X emptyState := by
  intro admitted
  exact before_refused ((Bag.beforeTells_single X emptyState (Member.ofFiring firing)).mp admitted)

end Inconsistent

namespace MatchingOnly

def demandRule : Rule Tm := ⟨PUnit.unit, ⟨[], [v 0], [], [.equal (v 0) (c 5)], []⟩, []⟩
def pinRule : Rule Tm := ⟨PUnit.unit, ⟨[], [c 5], [], [], []⟩, []⟩
def program : Program Tm := {demandRule, pinRule}
def start : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => v 0⟩
def demand : OneMember action ℕ program :=
  ⟨demandRule, Or.inl rfl, (fun n => v (n + 1)), ⟨[], [0], []⟩, []⟩
def pin : OneMember action ℕ program :=
  ⟨pinRule, Or.inr rfl, Subst.id atoms, ⟨[], [0], []⟩, []⟩
def both : Bag ℕ E program PUnit.unit := bagOf action [demand, pin]

theorem fresh : both.Fresh X start := by
  intro b g first second
  cases b
  let assignment : Subst atoms := fun n => if n = 0 then g 0 else first (n - 1)
  refine ⟨assignment, ⟨?_, ?_⟩, ?_⟩
  · intro term mentioned
    obtain (known | known | ⟨o, _, rfl⟩) := mentioned
    · cases known
    · cases known
    · change assignment.applyTerm ((Subst.id atoms).applyTerm (v 0)) = g.applyTerm (v 0)
      simp [assignment, v, Subst.applyTerm, Subst.id]
  · intro term inside
    change term ∈ [v 0, v 0, c 5] at inside
    change assignment.applyTerm (Subst.applyTerm (fun n => v (n + 1)) term) = first.applyTerm term
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> simp [assignment, v, c, Subst.applyTerm]
  · intro term inside
    change term ∈ [c 5] at inside
    obtain rfl := List.mem_singleton.mp inside
    rfl

theorem after : both.Admits X start := by
  refine ⟨⟨fresh, by decide, by decide, ?_⟩, ?_, ?_, ?_⟩
  · intro member inside
    change member ∈ [demand, pin] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp inside
      exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨by decide, by decide, by decide, by decide, fun query inside => by cases inside⟩
  · refine ⟨PUnit.unit, (fun _ => c 5), ?_⟩
    intro equation inside
    change equation ∈ [(v 1, v 0), (c 5, v 0)] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · rfl
    · obtain rfl := List.mem_singleton.mp inside
      rfl
  · intro b assignment solved member inside
    change member ∈ [demand, pin] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · refine ⟨?_, fun query inside => by cases inside⟩
      intro check inside
      obtain rfl := List.mem_singleton.mp inside
      have one := solved (v 1, v 0) List.mem_cons_self
      have two := solved (c 5, v 0) (List.mem_cons_of_mem _ List.mem_cons_self)
      exact one.trans two.symm
    · obtain rfl := List.mem_singleton.mp inside
      refine ⟨?_, ?_⟩
      · intro check inside
        cases inside
      · intro query inside
        cases inside

theorem before : both.AdmitsBeforeTells X start := by
  apply (Bag.beforeTells_iff_of_no_tells X start both ?_).mpr after
  intro member inside
  change member ∈ [demand, pin] at inside
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · obtain rfl := List.mem_singleton.mp inside
    rfl

theorem own_refused : ¬ both.AdmitsOwn X start := by
  intro own
  have solves : X.Models (a := PUnit.unit) (b := PUnit.unit) (fun _ => c 0)
      (demand.firing.information X start) := by
    intro equation inside
    change equation ∈ [(v 1, v 0)] at inside
    obtain rfl := List.mem_singleton.mp inside
    rfl
  have held := (own.2.2.2 demand List.mem_cons_self PUnit.unit (fun _ => c 0) solves).1
    (.equal (v 1) (c 5)) List.mem_cons_self
  have impossible : c 0 = c 5 := held
  simp [c] at impossible

theorem before_is_not_own : both.AdmitsBeforeTells X start ∧ ¬ both.AdmitsOwn X start :=
  ⟨before, own_refused⟩

end MatchingOnly

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTimingControls
