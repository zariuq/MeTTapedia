import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Charge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverFirstOrder

/-!
# Conserved charges of the one-frame instance

* **Place charges** (`placeCharge`): a weight on labels, summed over the present occurrences. They
  are invariant under the transport that renames occurrences keeping labels
  (`placeCharge_invariant`), and under the one-frame transport (`placeCharge_invariant_firstOrder`).
  **Label counts** (`labelCharge`) are the place charge in multisets: the multiset of present labels
  (`labelCharge_potential`).
* **The value flow** (`valueCharge`): in a Henkin model at a point, the multiset of the values of the
  present occurrences. Its totals along a run are the flow of `run_conservation`
  (`valueCharge_totals`), so `run_conservation` is the telescoping of this charge
  (`value_run_balance`).
* **Place invariants** (`place_invariant`, Murata): a weight on values whose taken patterns and
  produced terms carry equal weight at a point, for every rule of a run, is constant along the run at
  every point satisfying its end. The hypothesis is about rules, not firings: the patterns evaluate to
  the selected values at such a point (`models_start_of_last`).

## Controls (`ChargeControls`)

Every occurrence labelled `0`; the transport renames occurrences keeping labels.

* **A fold admitted, charges matching** (`cycle_folds`, `cycle_balanced`): taking `5` and making `6`
  folds back to the start by the exchange of `5` and `6`, and the run takes the label it makes.
* **A fold refused by a charge mismatch** (`grow_refused`): making `6` beside `5` cannot fold back to
  the start, by the count of occurrences alone.
* **Matching charges are not sufficient** (`charges_blind_to_knowledge`): the same occurrences with and
  without the knowledge `X = 1` carry every place charge alike and are not isomorphic.
* **Traced is not conserved** (`length_traced_not_conserved`): the length of a run is a property of
  traces, and no invariant charge takes one per firing and makes nothing, since the cycle folds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport ConservedCharge weightCharge weightCharge_invariant)

universe uT uS uO uV uP uB

section Charges

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **A place charge**: a weight on labels, summed over the present occurrences. -/
abbrev placeCharge {B : Type uB} [AddCommMonoid B] (y : T → B) : ConservedCharge (firstOrder A label).toStep B :=
  weightCharge (firstOrder A label).toStep fun o => y (label o)

/-- **Label counts**: the multiset of the labels of the present occurrences. -/
abbrev labelCharge : ConservedCharge (firstOrder A label).toStep (Multiset T) :=
  placeCharge A label fun t => {t}

theorem labelCharge_potential (C : Configuration T O) :
    (labelCharge A label).potential C = C.present.val.map label :=
  Interface.weightCharge_singleton_potential (firstOrder A label).toStep label C

/-- **Place charges are invariant under renamings that keep labels.** -/
theorem placeCharge_invariant {B : Type uB} [AddCommMonoid B] (y : T → B) :
    (placeCharge A label y).Invariant (renamingTransport A label) :=
  weightCharge_invariant (renamingTransport A label) _ fun i o _ => congrArg y (i.keeps o)

/-- **Place charges are invariant under the one-frame transport.** -/
theorem placeCharge_invariant_firstOrder {B : Type uB} [AddCommMonoid B] (y : T → B) :
    (placeCharge A label y).Invariant (firstOrderTransport A label) :=
  weightCharge_invariant _ _ fun _ _ _ => rfl

variable {A label}

section Models

variable {Val : Type uV} {Pt : PUnit.{1} → Type uP}
  (M : (Frames.ofSubstitution A).HenkinModel Val Pt) (ρ : Pt PUnit.unit)

variable (label) in
/-- **The value charge at a point**: the multiset of the values of the present occurrences. -/
abbrev valueCharge : ConservedCharge (firstOrder A label).toStep (Multiset Val) :=
  placeCharge A label fun t => {M.eval t ρ}

theorem valueCharge_potential (C : Configuration T O) :
    (valueCharge label M ρ).potential C = C.present.val.map fun o => M.eval (label o) ρ :=
  Interface.weightCharge_singleton_potential (firstOrder A label).toStep (fun o => M.eval (label o) ρ) C

theorem valueCharge_taken {C : Configuration T O} {f : Firing T S O} (valid : f.Valid A label C) :
    (valueCharge label M ρ).taken C f = (f.selection.taken : Multiset O).map fun o => M.eval (label o) ρ := by
  show ∑ o ∈ f.selection.taken.toFinset, ({M.eval (label o) ρ} : Multiset Val) = _
  rw [Interface.sum_singleton_eq_map, List.toFinset_val, valid.firing.take_distinct.dedup]

theorem valueCharge_made {C : Configuration T O} {f : Firing T S O} (valid : f.Valid A label C) :
    (valueCharge label M ρ).made C f = (f.selection.made : Multiset O).map fun o => M.eval (label o) ρ := by
  show ∑ o ∈ f.selection.made.toFinset, ({M.eval (label o) ρ} : Multiset Val) = _
  rw [Interface.sum_singleton_eq_map, List.toFinset_val, valid.firing.output_distinct.dedup]

/-- **The totals of the value charge are the flow of `run_conservation`.** -/
theorem valueCharge_totals : ∀ {C : Configuration T O} (r : (firstOrder A label).toStep.Run C),
    ((valueCharge label M ρ).runTaken r, (valueCharge label M ρ).runMade r) =
      Multiplicative.toAdd (r.account fun _ f => flow M label ρ f)
  | _, .nil _ => rfl
  | C, .cons f admitted rest => by
      have valid : f.Valid A label C := admitted
      have later := valueCharge_totals rest
      show ((valueCharge label M ρ).taken C f + (valueCharge label M ρ).runTaken rest,
          (valueCharge label M ρ).made C f + (valueCharge label M ρ).runMade rest) =
        Multiplicative.toAdd (flow M label ρ f * rest.account fun _ f => flow M label ρ f)
      rw [toAdd_mul, ← later, valueCharge_taken M ρ valid, valueCharge_made M ρ valid]
      rfl

/-- **Values are conserved along runs, as the telescoping of the value charge**: the statement of
`run_conservation`, derived from `ConservedCharge.run_balance`. -/
theorem value_run_balance {C : Configuration T O} (r : (firstOrder A label).toStep.Run C) :
    r.last.present.val.map (fun o => M.eval (label o) ρ) +
        (Multiplicative.toAdd (r.account fun _ f => flow M label ρ f)).1 =
      C.present.val.map (fun o => M.eval (label o) ρ) +
        (Multiplicative.toAdd (r.account fun _ f => flow M label ρ f)).2 := by
  have balance := (valueCharge label M ρ).run_balance r
  rw [valueCharge_potential, valueCharge_potential] at balance
  rw [← valueCharge_totals M ρ r]
  exact balance

/-- A point satisfying the knowledge at the end of a run satisfies the knowledge at its start. -/
theorem models_start_of_last : ∀ {C : Configuration T O} (r : (firstOrder A label).toStep.Run C),
    M.Models ρ r.last.equations → M.Models ρ C.equations
  | _, .nil _, known => known
  | C, .cons f _ rest, known => by
      have after : M.Models ρ (f.result label C).equations := models_start_of_last rest known
      rw [Firing.result_equations'] at after
      exact fun e member => after e (List.mem_append_left _ member)

/-- **Place invariants** (Murata): a weight on values for which, at a point, every rule of a run
gives its taken patterns and its produced terms equal weight is constant along the run at that point,
when the point satisfies the knowledge at the end. -/
theorem place_invariant {B : Type uB} [AddCommMonoid B] [IsRightCancelAdd B] (y : Val → B) :
    ∀ {C : Configuration T O} (r : (firstOrder A label).toStep.Run C), M.Models ρ r.last.equations →
      (∀ x ∈ r.word, (x.2.rule.take.map fun p => y (M.eval p ρ)).sum =
        (x.2.rule.produce.map fun p => y (M.eval p ρ)).sum) →
      (placeCharge A label fun t => y (M.eval t ρ)).potential r.last =
        (placeCharge A label fun t => y (M.eval t ρ)).potential C
  | _, .nil _, _, _ => rfl
  | C, .cons f admitted rest, known, semiflow => by
      have valid : f.Valid A label C := admitted
      have atResult : M.Models ρ (f.result label C).equations := models_start_of_last M ρ rest known
      have problem : M.Models ρ (f.selection.problem label f.rule C) := atResult
      unfold Selection.problem at problem
      have takeValues : f.rule.take.map (fun p => M.eval p ρ) =
          f.selection.taken.map (fun o => M.eval (label o) ρ) :=
        models_equations_values M label ρ valid.firing.take_length
          (fun e member => problem e (by simp [member]))
      have produceValues : f.rule.produce.map (fun p => M.eval p ρ) =
          f.selection.made.map (fun o => M.eval (label o) ρ) := by
        rw [← valid.firing.outputs, List.map_map]
        rfl
      have taken : (f.rule.take.map fun p => y (M.eval p ρ)).sum =
          (f.selection.taken.map fun o => y (M.eval (label o) ρ)).sum := by
        have weighed := congrArg (fun l => (l.map y).sum) takeValues
        simpa only [List.map_map, Function.comp_def] using weighed
      have produced : (f.rule.produce.map fun p => y (M.eval p ρ)).sum =
          (f.selection.made.map fun o => y (M.eval (label o) ρ)).sum := by
        have weighed := congrArg (fun l => (l.map y).sum) produceValues
        simpa only [List.map_map, Function.comp_def] using weighed
      have rule : (f.rule.take.map fun p => y (M.eval p ρ)).sum =
          (f.rule.produce.map fun p => y (M.eval p ρ)).sum :=
        semiflow ⟨C, f⟩ (by simp [Interface.Step.Run.word])
      have flux : (placeCharge A label fun t => y (M.eval t ρ)).taken C f =
          (placeCharge A label fun t => y (M.eval t ρ)).made C f := by
        show ∑ o ∈ f.selection.taken.toFinset, y (M.eval (label o) ρ) =
          ∑ o ∈ f.selection.made.toFinset, y (M.eval (label o) ρ)
        rw [List.sum_toFinset _ valid.firing.take_distinct, List.sum_toFinset _ valid.firing.output_distinct,
          ← taken, rule, produced]
      have step := (placeCharge A label fun t => y (M.eval t ρ)).balance f admitted
      rw [flux] at step
      exact (place_invariant y rest known fun x member =>
        semiflow x (by simp [Interface.Step.Run.word, member])).trans (add_right_cancel step)

end Models

end Charges

/-! ## Controls -/

namespace ChargeControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open EscapeControls (blank)

abbrev Control := Firing (Term signature) (Subst signature) ℕ

/-- One occurrence, `5`, and no knowledge. -/
def single : Configuration (Term signature) ℕ := ⟨[], {5}⟩

/-- Takes `5` and makes `6`. -/
def cycle : Control := ⟨⟨[.const 0], [], [], [], [.const 0]⟩, [], ⟨[5], [], [6]⟩⟩

/-- Makes `6` and takes nothing. -/
def grow : Control := ⟨⟨[], [], [], [], [.const 0]⟩, [], ⟨[], [], [6]⟩⟩

theorem cycle_valid : cycle.Valid A blank single := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩, by simp [cycle]⟩,
    by simp [cycle]⟩
  intro equation member
  have same : equation = (.const 0, .const 0) := by
    simpa [Selection.problem, Selection.equations, single, cycle, blank] using member
  subst same
  exact A.equivalence.refl _

theorem grow_valid : grow.Valid A blank single :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, single, grow]⟩,
    by simp [grow]⟩, by simp [grow]⟩

/-- The run of the cycle. -/
abbrev cycleRun : (firstOrder A blank).toStep.Run single := .cons cycle cycle_valid (.nil _)

/-- The run of the growth. -/
abbrev growRun : (firstOrder A blank).toStep.Run single := .cons grow grow_valid (.nil _)

/-- The exchange of `5` and `6` carries the start to the end of the cycle. -/
def cycleFold : (renamingTransport A blank).Iso single (cycle.result blank single) :=
  ⟨Equiv.swap 5 6, fun _ => rfl, ⟨fun σ => ⟨fun _ e member => by
      have same : e = (.const 0, .const 0) := by
        simpa [Firing.result, Selection.result, Selection.problem, Selection.equations, single, cycle,
          blank] using member
      subst same
      exact A.equivalence.refl _, fun _ e member => by
      simp [renameConfiguration, single] at member⟩, by decide⟩⟩

/-- **A fold admitted**: the cycle folds back to its start. -/
theorem cycle_folds : (renamingTransport A blank).Same single cycleRun.last := ⟨cycleFold⟩

/-- **Charges match at the admitted fold**: by the fold law, the cycle takes the label it makes. -/
theorem cycle_balanced :
    (labelCharge A blank).runTaken cycleRun = (labelCharge A blank).runMade cycleRun :=
  ConservedCharge.balanced_of_fold (placeCharge_invariant A blank _) cycleRun cycle_folds

/-- **A fold refused by a charge mismatch**: the growth makes one occurrence and takes none, so it
cannot fold back to its start. -/
theorem grow_refused : ¬ (renamingTransport A blank).Same single growRun.last :=
  ConservedCharge.not_fold_of_unbalanced (placeCharge_invariant A blank fun _ => (1 : ℕ)) growRun
    (by decide)

/-- The same occurrence, knowing `X = 1`. -/
def knowing : Configuration (Term signature) ℕ := ⟨[(.var 0, .const 1)], {5}⟩

/-- **Matching charges are not sufficient to fold**: the two configurations carry every place
charge alike, and are not isomorphic, since only one of them knows `X = 1`. -/
theorem charges_blind_to_knowledge :
    (∀ {B : Type} [AddCommMonoid B] (y : Term signature → B),
      (placeCharge A blank y).potential single = (placeCharge A blank y).potential knowing) ∧
      ¬ (renamingTransport A blank).Same single knowing := by
  refine ⟨fun _ => rfl, ?_⟩
  rintro ⟨i⟩
  have known : A.Models ConstraintMultisetRewriting.Controls.zero knowing.equations :=
    (i.same.1 ConstraintMultisetRewriting.Controls.zero).mp fun _ member => by
      simp [renameConfiguration, single] at member
  have impossible := known (.var 0, .const 1) (by simp [knowing])
  change (Term.const (σ := signature) 0) = .const 1 at impossible
  cases impossible

/-- **Traced is not conserved**: the length of a run is a property of traces, and no charge
invariant under the transport takes one per firing and makes nothing, since the cycle folds. -/
theorem length_traced_not_conserved :
    (∀ {C : Configuration (Term signature) ℕ} {r r' : (firstOrder A blank).toStep.Run C},
      (renamingTransport A blank).TraceEquiv C r r' →
        r.total (fun _ _ => (1 : ℕ)) = r'.total (fun _ _ => (1 : ℕ))) ∧
      ¬ ∃ Q : ConservedCharge (firstOrder A blank).toStep ℕ, Q.Invariant (renamingTransport A blank) ∧
        (∀ C f, Q.taken C f = 1) ∧ (∀ C f, Q.made C f = 0) := by
  refine ⟨fun equivalent => Interface.Step.Run.traceEquiv_total _ (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ => rfl) equivalent, ?_⟩
  rintro ⟨Q, invariant, takesOne, makesNone⟩
  have balanced : Q.taken single cycle + 0 = Q.made single cycle + 0 :=
    ConservedCharge.balanced_of_fold invariant cycleRun cycle_folds
  rw [takesOne, makesNone] at balanced
  exact absurd balanced (by decide)

end ChargeControls

#print axioms labelCharge_potential
#print axioms placeCharge_invariant
#print axioms placeCharge_invariant_firstOrder
#print axioms valueCharge_potential
#print axioms valueCharge_totals
#print axioms value_run_balance
#print axioms models_start_of_last
#print axioms place_invariant
#print axioms ChargeControls.cycle_valid
#print axioms ChargeControls.cycle_folds
#print axioms ChargeControls.cycle_balanced
#print axioms ChargeControls.grow_refused
#print axioms ChargeControls.charges_blind_to_knowledge
#print axioms ChargeControls.length_traced_not_conserved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
