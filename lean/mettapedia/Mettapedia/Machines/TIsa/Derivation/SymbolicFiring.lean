import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderLicence
import Mettapedia.Machines.BoundedDeterministicRun

/-!
# A symbolic firing retains its residual knowledge

Take and read selections and the opened tells give a single equation
problem on the actual occurrence store. The total first-order solver
produces a principal answer or refuses the problem. The guard checker
uses its published all-solutions judgment, not the result of testing
an arbitrary instance of the answer.

This is the evaluator of one selected firing. The snapshot result
retains the opened information, including any remaining unknowns.
An opening and its physical selection are supplied separately by
search; they are not chosen by the unifier.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (Program)
open RuleSyntax.OneFrame (Terms frames ext)
open RuleSyntax.FirstOrderLicence (firingChecks admits_iff_checked unsolvable_refuses)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence (certain certain_eq_matches)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {program : Program (Terms (Term signature))}

abbrev World (signature : LPSignature) (O : Type) := RuleSyntax.State (Terms (Term signature)) O
abbrev act (signature : LPSignature) := frames (FirstOrder.action signature)

/-- Resource and opening evidence belongs to the selection. Equation
consistency and universal checks have not yet been established. -/
structure Selection (before : World signature O) where
  firing : RuleSyntax.Firing O (ext (FirstOrder.action signature)) program before.frame
  shaped : firing.Shapes (act signature) before
  enabled : Enabled (fun _ : O => ()) before.present (firing.selection.commit (T := Unit))

def problem {before : World signature O} (selected : Selection (program := program) before) :=
  selected.firing.information (act signature) before

def Admitted {before : World signature O} (selected : Selection (program := program) before) : Prop :=
  (RuleSyntax.step (act signature) O (ext (FirstOrder.action signature)) program).Admits selected.firing

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def evaluate {before : World signature O} (selected : Selection (program := program) before) :
    Option (Subst signature × World signature O) :=
  match unifyTotal (problem selected) with
  | none => none
  | some answer =>
    if firingChecks answer before selected.firing then
      some (answer, selected.firing.result (act signature) before)
    else none

theorem evaluate_exact {before : World signature O} (selected : Selection (program := program) before)
    (answer : Subst signature) (after : World signature O) :
    evaluate selected = some (answer, after) ↔
      unifyTotal (problem selected) = some answer ∧ Admitted selected ∧
        after = selected.firing.result (act signature) before := by
  cases unified : unifyTotal (problem selected) with
  | none => simp [evaluate, unified]
  | some solved =>
    have describes : Admitted selected ↔ firingChecks solved before selected.firing = true := by
      exact (admits_iff_checked before selected.firing solved unified).trans
        ⟨fun licensed => licensed.2.2, fun guards => ⟨selected.shaped, selected.enabled, guards⟩⟩
    by_cases holds : firingChecks solved before selected.firing = true
    · have admitted := describes.mpr holds
      simp only [evaluate, unified, if_pos holds, Option.some.injEq, Prod.mk.injEq, admitted, true_and]
      exact and_congr_right (fun _ => eq_comm)
    · have denied : ¬Admitted selected := fun accepts => holds (describes.mp accepts)
      simp [evaluate, unified, holds, denied]

theorem refuses_exactly_when_not_admitted {before : World signature O}
    (selected : Selection (program := program) before) : evaluate selected = none ↔ ¬Admitted selected := by
  cases unified : unifyTotal (problem selected) with
  | none =>
    exact ⟨fun _ => unsolvable_refuses before selected.firing unified, fun _ => by simp [evaluate, unified]⟩
  | some solved =>
    have describes : Admitted selected ↔ firingChecks solved before selected.firing = true :=
      (admits_iff_checked before selected.firing solved unified).trans
        ⟨fun licensed => licensed.2.2, fun guards => ⟨selected.shaped, selected.enabled, guards⟩⟩
    rw [describes]
    by_cases holds : firingChecks solved before selected.firing = true <;> simp [evaluate, unified, holds]

theorem principal_result {before after : World signature O} (selected : Selection (program := program) before)
    {answer : Subst signature} (publishes : evaluate selected = some (answer, after)) :
    (FirstOrder.action signature).Principal after.knowledge answer := by
  obtain ⟨computed, _, rfl⟩ := (evaluate_exact selected answer after).mp publishes
  exact FirstOrder.accepted_principal (problem selected) answer computed

def inferSeen {before : World signature O} (selected : Selection (program := program) before)
    (answer : Subst signature) : List (Finset O) :=
  (selected.firing.collectOpened (act signature)).map fun pattern =>
    certain answer
      (selected.firing.row (act signature) before) before.present pattern

private theorem map_eq_claims {A B : Type*} (read : A → B) :
    ∀ {patterns : List A} {claims : List B},
      patterns.length = claims.length →
      (∀ query ∈ patterns.zip claims, read query.1 = query.2) →
      patterns.map read = claims
  | [], [], _, _ => rfl
  | [], _ :: _, width, _ => by cases width
  | _ :: _, [], width, _ => by cases width
  | p :: ps, a :: rest, width, holds => by
    have head : read p = a := holds (p, a) List.mem_cons_self
    have tail := map_eq_claims read (Nat.succ.inj width)
      (fun query found => holds query (List.mem_cons_of_mem _ found))
    exact congrArg₂ List.cons head tail

/-- Every admitted collection claim is forced by the principal
answer. Search need not guess subsets of the occurrence store. The
universal check is still needed to certify that these claims are
unchanged in all residual solutions. -/
theorem inferred_collection_is_the_only_admitted_one {before after : World signature O}
    (selected : Selection (program := program) before) {answer : Subst signature}
    (publishes : evaluate selected = some (answer, after)) : inferSeen selected answer = selected.firing.seen := by
  obtain ⟨solved, admitted, _⟩ := (evaluate_exact selected answer after).mp publishes
  have valid := (FirstOrder.accepted_principal (problem selected) answer solved).sound
  have collects := (admitted.2.2.2 PUnit.unit answer valid).2
  unfold inferSeen
  apply map_eq_claims
  · rw [RuleSyntax.Firing.collectOpened, List.length_map]
    exact selected.shaped.2.2.2.2.2.2
  · intro query paired
    have seen := collects query paired
    rw [RuleSyntax.OneFrame.matchesAt_eq] at seen
    rw [certain_eq_matches]
    exact seen

theorem admitted_has_computed_result {before : World signature O}
    (selected : Selection (program := program) before) (allowed : Admitted selected) :
    ∃ answer, evaluate selected = some (answer, selected.firing.result (act signature) before) := by
  cases computed : evaluate selected with
  | none => exact ((refuses_exactly_when_not_admitted selected).mp computed allowed).elim
  | some publication =>
    obtain ⟨answer, actual⟩ := publication
    have final := ((evaluate_exact selected answer actual).mp computed).2.2
    exact ⟨answer, congrArg (fun world => some (answer, world)) final⟩

/-- Replace the collect claims without changing the rule, its opening,
the equations, or its use of occurrences. -/
def Selection.withSeen {before : World signature O} (selected : Selection (program := program) before)
    (claims : List (Finset O)) (width : selected.firing.rule.collect.length = claims.length) :
    Selection (program := program) before where
  firing := {selected.firing with seen := claims}
  shaped := ⟨selected.shaped.1, selected.shaped.2.1, selected.shaped.2.2.1, selected.shaped.2.2.2.1,
    selected.shaped.2.2.2.2.1, selected.shaped.2.2.2.2.2.1, width⟩
  enabled := selected.enabled

def proposeCollections {before : World signature O} (selected : Selection (program := program) before) :
    Option (Subst signature × Selection (program := program) before) := do
  let answer ← unifyTotal (problem selected)
  let claims := inferSeen selected answer
  pure (answer, selected.withSeen claims (by
    simp [claims, inferSeen, RuleSyntax.Firing.collectOpened]))

theorem proposed_collections_include_every_admitted_choice {before : World signature O}
    (selected : Selection (program := program) before) (claims : List (Finset O))
    (width : selected.firing.rule.collect.length = claims.length)
    (admitted : Admitted (selected.withSeen claims width)) :
    ∃ answer, proposeCollections selected = some (answer, selected.withSeen claims width) := by
  let actual := selected.withSeen claims width
  obtain ⟨answer, found⟩ := admitted_has_computed_result actual admitted
  have answer_exact := (evaluate_exact actual answer _).mp found
  have solved : unifyTotal (problem selected) = some answer := answer_exact.1
  have inferred := inferred_collection_is_the_only_admitted_one actual found
  change inferSeen selected answer = claims at inferred
  refine ⟨answer, ?_⟩
  unfold proposeCollections
  rw [solved]
  simp only [bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and]
  cases inferred
  rfl

theorem proposed_principal_solution {before : World signature O}
    {seed chosen : Selection (program := program) before} {answer : Subst signature}
    (proposal : proposeCollections seed = some (answer, chosen)) :
    unifyTotal (problem chosen) = some answer := by
  unfold proposeCollections at proposal
  cases solved : unifyTotal (problem seed) with
  | none => simp [solved] at proposal
  | some found =>
    simp only [solved, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at proposal
    obtain ⟨rfl, rfl⟩ := proposal
    exact solved

theorem proposed_keeps_selection {before : World signature O}
    {seed chosen : Selection (program := program) before} {answer : Subst signature}
    (proposal : proposeCollections seed = some (answer, chosen)) :
    chosen.firing = {seed.firing with seen := chosen.firing.seen} := by
  unfold proposeCollections at proposal
  cases solved : unifyTotal (problem seed) with
  | none => simp [solved] at proposal
  | some found =>
    simp only [solved, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at proposal
    obtain ⟨rfl, rfl⟩ := proposal
    rfl

/-- Choose the only possible collects and test them with the same
principal answer, without solving the selected equation problem again. -/
def evaluateInferred {before : World signature O} (seed : Selection (program := program) before) :
    Option (Subst signature × Selection (program := program) before) := do
  let (answer, chosen) ← proposeCollections seed
  if firingChecks answer before chosen.firing then some (answer, chosen) else none

theorem evaluateInferred_exact {before : World signature O}
    (seed : Selection (program := program) before) (answer : Subst signature)
    (chosen : Selection (program := program) before) :
    evaluateInferred seed = some (answer, chosen) ↔
      proposeCollections seed = some (answer, chosen) ∧ Admitted chosen := by
  constructor
  · intro evaluated
    unfold evaluateInferred at evaluated
    obtain ⟨⟨solution, candidate⟩, proposed, checked⟩ := Option.bind_eq_some_iff.mp evaluated
    by_cases passes : firingChecks solution before candidate.firing = true
    · simp only [if_pos passes, Option.some.injEq, Prod.mk.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨proposed, (admits_iff_checked before candidate.firing solution
        (proposed_principal_solution proposed)).mpr ⟨candidate.shaped, candidate.enabled, passes⟩⟩
    · simp [passes] at checked
  · rintro ⟨proposed, admitted⟩
    have passes := (admits_iff_checked before chosen.firing answer
      (proposed_principal_solution proposed)).mp admitted
    simp [evaluateInferred, proposed, passes.2.2]

/-- CPS at the same publication boundary as the ground evaluator:
only success has a new world; failure has the original continuation. -/
def evaluateK {R : Type*} {before : World signature O}
    (selected : Selection (program := program) before)
    (win : Subst signature → World signature O → R) (lose : Unit → R) : R :=
  match unifyTotal (problem selected) with
  | none => lose ()
  | some answer =>
    if firingChecks answer before selected.firing then
      win answer (selected.firing.result (act signature) before)
    else lose ()

theorem evaluateK_exact {R : Type*} {before : World signature O}
    (selected : Selection (program := program) before)
    (win : Subst signature → World signature O → R) (lose : Unit → R) :
    evaluateK selected win lose = (evaluate selected).elim (lose ()) (fun result => win result.1 result.2) := by
  unfold evaluateK evaluate
  split
  · rfl
  · split <;> rfl

/-- Defunctionalized phases of testing and publishing a selected
firing. The principal substitution is passed as data between phases.
The unnormalized store is still the one carried into publication. -/
inductive Phase (signature : LPSignature) (O : Type) where
  | resolve
  | test (answer : Subst signature)
  | publish (answer : Subst signature)
  | finished (result : Option (Subst signature × World signature O))

def advance {before : World signature O} (selected : Selection (program := program) before) :
    Phase signature O → Option (Phase signature O)
  | .resolve => some (match unifyTotal (problem selected) with
    | none => .finished none
    | some answer => .test answer)
  | .test answer => some (if firingChecks answer before selected.firing then .publish answer else .finished none)
  | .publish answer => some (.finished (some (answer, selected.firing.result (act signature) before)))
  | .finished _ => none

def remaining {before : World signature O} (selected : Selection (program := program) before) :
    Phase signature O → Option (Subst signature × World signature O)
  | .resolve => evaluate selected
  | .test answer => if firingChecks answer before selected.firing
      then some (answer, selected.firing.result (act signature) before) else none
  | .publish answer => some (answer, selected.firing.result (act signature) before)
  | .finished result => result

theorem advance_preserves {before : World signature O} (selected : Selection (program := program) before)
    {first later : Phase signature O} (moved : advance selected first = some later) :
    remaining selected first = remaining selected later := by
  cases first with
  | resolve =>
    cases solved : unifyTotal (problem selected) with
    | none =>
      obtain rfl := Option.some.inj (by simpa only [advance, solved] using moved)
      simp [remaining, evaluate, solved]
    | some answer =>
      obtain rfl := Option.some.inj (by simpa only [advance, solved] using moved)
      simp [remaining, evaluate, solved]
  | test answer =>
    by_cases holds : firingChecks answer before selected.firing = true
    · obtain rfl := Option.some.inj (by simpa only [advance, if_pos holds] using moved)
      simp [remaining, holds]
    · obtain rfl := Option.some.inj (by simpa only [advance, if_neg holds] using moved)
      simp [remaining, holds]
  | publish answer =>
    obtain rfl := Option.some.inj moved
    rfl
  | finished result => cases moved

abbrev Passes {before : World signature O} (selected : Selection (program := program) before) :=
  Relation.ReflTransGen fun first later => advance selected first = some later

theorem complete_selected_run {before : World signature O} (selected : Selection (program := program) before) :
    BoundedDeterministicRun.run (advance selected) 3 .resolve = .finished (evaluate selected) := by
  cases solved : unifyTotal (problem selected) with
  | none => simp [BoundedDeterministicRun.run, advance, evaluate, solved]
  | some answer =>
    by_cases holds : firingChecks answer before selected.firing = true <;>
      simp [BoundedDeterministicRun.run, advance, evaluate, solved, holds]

theorem selected_run_iff {before : World signature O} (selected : Selection (program := program) before)
    (result : Option (Subst signature × World signature O)) :
    Passes selected .resolve (.finished result) ↔ result = evaluate selected := by
  constructor
  · intro ran
    have invariant {a b : Phase signature O} (steps : Passes selected a b) :
        remaining selected a = remaining selected b := by
      induction steps with
      | refl => rfl
      | tail _ edge ih => exact ih.trans (advance_preserves selected edge)
    exact (invariant ran).symm
  · rintro rfl
    exact (complete_selected_run selected) ▸ BoundedDeterministicRun.run_reachable (advance selected) 3 .resolve

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
