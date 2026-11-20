import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Exec

/-!
# A store of linear rules that make no rule is used up

With no ambient program, at a state all of whose held rules are linear (`RState.AllLinear`), in a
code system whose codes make, install and publish no rule (`Codes.MakesNone`): every firing uses a
held occurrence, which is taken, and makes none. So, over any frame action and extensions,

* **`linear_used_up`**: the result of an admitted firing holds strictly fewer rule occurrences, all
  of them linear;
* **`linear_run_bounded`**: a run has at most as many firings as the state holds rule occurrences.

The rules of the present step, as codes, are such a system (`makesNone_ofRules`).

Over first-order atoms, with the rule that takes the fact `12` and makes the fact `22` held once,
linearly, as its own code: its firing is admitted (`UsedUp.once_admitted`), the result holds fewer
rules (`UsedUp.once_used_up`), and admits no firing (`UsedUp.then_stuck`).

Each hypothesis is needed. A persistent occurrence is kept by its own firing
(`RFiring.kept_persistent`), and a code that makes itself again holds the rule again after each
firing (`Exec.loop_reemits`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)

section General

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}

/-- **A code system that makes no rule**: no code makes, installs or publishes a rule. -/
def Codes.MakesNone (codes : Codes Tm C Z) : Prop :=
  ∀ c, (codes.unfold c).makes = [] ∧ (codes.unfold c).installs = [] ∧
    (codes.unfold c).publishes = []

/-- The rules of the present step, as codes, make no rule. -/
theorem makesNone_ofRules (Z : Type uZ) : (ofRules Z : Codes Tm (Rule Tm) Z).MakesNone :=
  fun _ => ⟨rfl, rfl, rfl⟩

/-- **Every held rule is linear.** -/
def RState.AllLinear (s : RState Tm O R C Z) : Prop :=
  ∀ ρ ∈ s.rules, (s.held ρ).mode = Mode.linear

/-- With no ambient program, an available use is a held occurrence. -/
theorem RState.held_of_available {s : RState Tm O R C Z} {u : Use C R}
    (available : s.Available (∅ : Set C) u) : ∃ ρ, u = Use.held ρ ∧ ρ ∈ s.rules := by
  cases u with
  | ambient c => exact absurd available (Set.notMem_empty c)
  | held ρ => exact ⟨ρ, rfl, available⟩

variable (X : Frames Tm Hom) [DecidableEq O] [DecidableEq R] {E : Extensions.{uO, uH, uE} Hom}
  {codes : Codes Tm C Z} {s : RState Tm O R C Z}

/-- **A linear store whose codes make no rule is used up**: an admitted firing leaves strictly fewer
rule occurrences, all of them linear. -/
theorem linear_used_up (f : RFiring O R E codes s) (none : codes.MakesNone) (linear : s.AllLinear)
    (admitted : f.Admits X (∅ : Set C)) :
    (f.result X).rules.card < s.rules.card ∧ (f.result X).AllLinear := by
  have shapes : f.RuleShapes (∅ : Set C) := admitted.1.2.2
  obtain ⟨noMakes, noInstalls, noPublishes⟩ := none (s.codeOf f.use)
  have made : f.madeRules = [] := by
    apply List.length_eq_zero_iff.mp
    have count := shapes.madeLength
    rw [noMakes, noInstalls, noPublishes] at count
    exact count.symm
  obtain ⟨ρ, use, held⟩ := RState.held_of_available shapes.available
  have left : f.left = s.rules.erase ρ := by
    unfold RFiring.left
    rw [use]
    exact if_pos (linear ρ held)
  have rules : (f.result X).rules = f.kept := by
    show f.kept ∪ f.madeRules.toFinset = f.kept
    rw [made, List.toFinset_nil, Finset.union_empty]
  have fewer : (f.result X).rules.card < s.rules.card := by
    rw [rules]
    calc f.kept.card ≤ f.left.card := Finset.card_le_card Finset.sdiff_subset
      _ = (s.rules.erase ρ).card := by rw [left]
      _ < s.rules.card := Finset.card_erase_lt_of_mem held
  refine ⟨fewer, fun ρ₀ inside => ?_⟩
  have missing : ρ₀ ∉ f.madeRules := by
    rw [made]
    exact List.not_mem_nil
  have inKept : ρ₀ ∈ f.kept := by
    rw [← rules]
    exact inside
  rw [f.result_held_other missing]
  exact linear ρ₀ (f.kept_subset inKept)

/-- **So a run has at most as many firings as the state holds rule occurrences.** -/
theorem linear_run_bounded (none : codes.MakesNone) (linear : s.AllLinear)
    (run : (rstep X O R E codes (∅ : Set C)).toStep.Run s) : run.word.length ≤ s.rules.card := by
  induction run with
  | nil s => exact Nat.zero_le _
  | cons f admitted rest ih =>
      obtain ⟨fewer, stillLinear⟩ := linear_used_up X f none linear admitted
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih stillLinear) fewer)

end General

#print axioms makesNone_ofRules
#print axioms RState.held_of_available
#print axioms linear_used_up
#print axioms linear_run_bounded

namespace UsedUp

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- The fact `12` at row `0`, and the rule that takes it and makes the fact `22` held once,
linearly, as its own code. -/
def factState : RState Tm ℕ ℕ (Rule Tm) Unit :=
  ⟨⟨PUnit.unit, [], {0}, fun _ => c 12⟩, {0}, fun _ => ⟨Exec.onceRule, [], .linear, ()⟩⟩

/-- The rule takes the fact and makes row `1`. -/
def onceFiring : RFiring ℕ ℕ E (ofRules Unit) factState :=
  ⟨.held 0, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, [], [], [], [], []⟩

theorem fact_linear : factState.AllLinear := fun _ _ => rfl

/-- **The linear occurrence fires.** -/
theorem once_admitted : onceFiring.Admits X (∅ : Set (Rule Tm)) :=
  (onceFiring.admits_plain X (fun _ _ => rfl) (Spec.plain_ofRule Exec.onceRule) ∅).mpr
    ⟨Exec.once_base_admitted, Finset.mem_singleton_self 0, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- **It is used up**: the result holds fewer rule occurrences. -/
theorem once_used_up : (onceFiring.result X).rules.card < factState.rules.card :=
  (linear_used_up X onceFiring (makesNone_ofRules Unit) fact_linear once_admitted).1

/-- **Then nothing fires**: the result holds no rule. -/
theorem then_stuck (g : RFiring ℕ ℕ E (ofRules Unit) (onceFiring.result X)) :
    ¬ g.Admits X (∅ : Set (Rule Tm)) := by
  have empty : (onceFiring.result X).rules = ∅ := by
    apply Finset.card_eq_zero.mp
    have fewer := once_used_up
    have one : factState.rules.card = 1 := rfl
    omega
  exact stuck_of_no_rules X empty g

#print axioms once_admitted
#print axioms once_used_up
#print axioms then_stuck

end UsedUp

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
