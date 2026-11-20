import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SynchronousUpdate

/-!
# An open input gives two terminal outcomes without takes or tells

Two positive ground rules read different constants against one shared unknown.
Their matching information makes different refinements. Each branch reaches
a different closed set. This separates the general lane from monotone ground
propagation without relying on negation, side effects or a scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOpenControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings
open SetStoreSyntax
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms action)

abbrev Tm := Terms (Term atoms)
abbrev X := frames action
def c (n : ℕ) : Term atoms := .const n
def v : Term atoms := .var 0

def choose (n : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[], [c n], [], [], [c (n + 10)]⟩, []⟩
def program : Program Tm := {choose 5, choose 6}
def source : Finset (Term atoms) := {v}
def target (n : ℕ) : Finset (Term atoms) := {c n, c (n + 10)}

theorem choose_propagates (n : ℕ) : Propagates (choose n) := by
  refine ⟨rfl, rfl, ⟨?_, rfl⟩, ?_, ?_⟩
  · intro check inside
    cases inside
  · simp [varsIn, choose, Term.freeVars, c]
  · simp [varsIn, choose]

theorem program_propagates : ∀ rule ∈ program, Propagates rule := by
  intro rule member
  simp only [program, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl <;> exact choose_propagates _

def chooseFiring (n : ℕ) (which : n = 5 ∨ n = 6) :
    Firing (Term atoms × ℕ) (ext action) program PUnit.unit :=
  ⟨choose n, by rcases which with rfl | rfl <;> simp [program], PUnit.unit, Subst.id atoms,
    ⟨[], [(v, 0)], [(c (n + 10), 1)]⟩, []⟩

theorem choose_information (n : ℕ) (which : n = 5 ∨ n = 6) :
    (chooseFiring n which).information X (SetStore.represent source) = [(c n, v)] := rfl

theorem choose_fresh (n : ℕ) (which : n = 5 ∨ n = 6) :
    (chooseFiring n which).Fresh X (SetStore.represent source) := by
  apply Examples.fresh_of_ground action
  intro term inside assignment
  change term ∈ [c n, c (n + 10)] at inside
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · obtain rfl := List.mem_singleton.mp inside
    rfl

theorem choose_admitted (n : ℕ) (which : n = 5 ∨ n = 6) :
    (chooseFiring n which).Admits X (SetStore.represent source) := by
  refine ⟨⟨choose_fresh n which, by simp [chooseFiring], by simp [chooseFiring], rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨by simp [chooseFiring, Selection.commit], ?_, by simp [chooseFiring, Selection.commit], ?_, ?_⟩
    · intro row inside
      exact inside
    · simp [chooseFiring, Selection.commit, SetStore.represent, source]
    · intro query inside
      cases inside
  · refine ⟨PUnit.unit, (fun _ => c n), ?_⟩
    rw [choose_information]
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro b assignment _
    refine ⟨?_, ?_⟩
    · intro check inside
      cases inside
    · intro query inside
      cases inside

theorem choose_step (timing : SetStore.AskTiming) (n : ℕ) (which : n = 5 ∨ n = 6) :
    SetStore.Step timing program source (target n) := by
  let f := chooseFiring n which
  let bag := Bag.single f
  have yes := choose_admitted n which
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent [(c n, v)]).mpr
    ⟨(fun _ => c n), fun equation member => by obtain rfl := List.mem_singleton.mp member; rfl⟩
  have solved := unifyTotal_sound _ _ accepted
  have value : answer 0 = c n := (solved (c n, v) List.mem_cons_self).symm
  have afterYes : bag.Admits X (SetStore.represent source) := (Bag.single_admits_iff X _ f).mpr yes
  have admitted : SetStore.admitted timing source bag := by
    cases timing with
    | afterTells => exact afterYes
    | beforeTells =>
      apply (Bag.beforeTells_iff_of_no_tells X _ bag ?_).mpr afterYes
      intro member inside
      obtain rfl := List.mem_singleton.mp inside
      rfl
  refine ⟨bag, List.cons_ne_nil _ _, admitted, answer, ?_, ?_, ?_⟩
  · change unifyTotal (Bag.information X (SetStore.represent source) (Bag.single f)) = some answer
    simp only [Bag.single, Bag.information_single]
    exact accepted
  · simp [bag, f, SetStore.setResult, SetStore.update, Bag.single, Bag.selection, Bag.produce,
      Member.ofFiring, Member.firing, chooseFiring, Firing.opened, RuleInstance.map, choose,
      source, target, c, v, Subst.applyTerm, value]
    rfl
  · rintro ⟨names, same⟩
    have member : c n ∈ source.image (UnificationRenaming.rename names) := by
      rw [← same]
      simp [target]
    simp [source, v, c, UnificationRenaming.rename_var] at member

theorem target_ground (n : ℕ) : GroundRows (target n) := by
  intro term member
  simp only [target, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl <;> trivial

theorem target_closed_five : SetStoreClosure.Closed (consequence (P := program)) (target 5) := by
  intro match_ enabled
  obtain ⟨rule, member, pure, assignment, reads, checks⟩ := match_
  simp only [program, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl <;>
    simp [consequence, choose, target, c, Subst.applyTerm] at enabled ⊢

theorem target_closed_six : SetStoreClosure.Closed (consequence (P := program)) (target 6) := by
  intro match_ enabled
  obtain ⟨rule, member, pure, assignment, reads, checks⟩ := match_
  simp only [program, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl <;>
    simp [consequence, choose, target, c, Subst.applyTerm] at enabled ⊢

theorem targets_differ : target 5 ≠ target 6 := by
  intro same
  have member : c 5 ∈ target 6 := same ▸ (by simp [target])
  simp [target, c] at member

theorem positive_open_input_has_two_terminal_outcomes (timing : SetStore.AskTiming) :
    SetStore.Step timing program source (target 5) ∧ SetStore.Step timing program source (target 6) ∧
      target 5 ≠ target 6 ∧
      (∀ later, ¬ SetStore.Step timing program (target 5) later) ∧
      (∀ later, ¬ SetStore.Step timing program (target 6) later) := by
  refine ⟨choose_step timing 5 (Or.inl rfl), choose_step timing 6 (Or.inr rfl), targets_differ,
    closed_ground_terminal program_propagates _ (target_ground 5) target_closed_five,
    closed_ground_terminal program_propagates _ (target_ground 6) target_closed_six⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOpenControls
