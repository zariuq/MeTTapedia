import Mettapedia.Machines.TIsa.Derivation.SymbolicReopening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OneAfterAnother
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchWords
import Mathlib.Data.List.Forall2

/-!
# Joint information survives freshening a whole population

Each presence in the population has its own local choices, including
when two members used the same rule and the same read ports. Freshening
all members at once preserves the shared incoming assignment and the
individual values at every port, so joint guards are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicJointReopening

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open RuleSyntax.JointFirings (Bag OneMember Realized bagOf)
open RuleSyntax.OneFrame (Terms)
open RuleSyntax.JointFirings.SymmetricMatches (WordResultModel outputWords)
open SymbolicFiring (World act SameInput)
open SymbolicFiring.SameInput (Agree)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {program : RuleSyntax.Program (Terms (Term signature))} {before : World signature O}

private abbrev A := FirstOrder.action signature
abbrev Member (signature : LPSignature) (O : Type) (program : RuleSyntax.Program (Terms (Term signature))) :=
  OneMember (A (signature := signature)) O program
private abbrev bag (members : List (Member signature O program)) := bagOf A members

abbrev Same (before : World signature O) (l r : Member signature O program) :=
  SameInput (before := before) l.firing r.firing

abbrev Paired (before : World signature O) (ξ τ : Subst signature) (l r : Member signature O program) :=
  Same before l r ∧ Agree (before := before) l.firing r.firing ξ τ

omit [DecidableEq O] in
private theorem realize {ξ : Subst signature} {Q : Subst signature → Prop}
    {left right : List (Member signature O program)} (pairs : List.Forall₂ (Same before) left right)
    (available : Realized (act signature) PUnit.unit right Q) :
    ∃ τ, Q τ ∧ List.Forall₂ (fun l r => Same before l r ∧
      ∀ term ∈ l.rule.terms, ξ.applyTerm (l.opening.applyTerm term) =
        τ.applyTerm (r.opening.applyTerm term)) left right := by
  induction pairs generalizing Q with
  | nil =>
    obtain ⟨τ, holds⟩ := available
    exact ⟨τ, holds, .nil⟩
  | @cons l r restL restR same paired ih =>
    have desc := available (ξ.comp l.opening)
    obtain ⟨τ, ⟨holds, localValues⟩, tail⟩ := ih desc
    refine ⟨τ, holds, .cons ⟨same, fun term authored => ?_⟩ tail⟩
    have ruleEq : l.rule = r.rule := same.rule
    have named := localValues term (ruleEq ▸ authored)
    change τ.applyTerm (r.opening.applyTerm term) = (ξ.comp l.opening).applyTerm term at named
    simpa only [Subst.applyTerm_comp] using named.symm

omit [DecidableEq O] in
theorem realize_pairs {left right : List (Member signature O program)}
    (pairs : List.Forall₂ (Same before) left right) (fresh : (bag right).Fresh (act signature) before)
    (ξ : Subst signature) : ∃ τ, (∀ term, before.Mentions term → ξ.applyTerm term = τ.applyTerm term) ∧
      List.Forall₂ (Paired before ξ τ) left right := by
  obtain ⟨τ, keeps, localValues⟩ := realize (ξ := ξ) pairs (fresh PUnit.unit ξ)
  have incoming (term : Term signature) (used : before.Mentions term) :
      ξ.applyTerm term = τ.applyTerm term := by
    have holds := keeps term used
    change τ.applyTerm ((Subst.id signature).applyTerm term) = ξ.applyTerm term at holds
    simpa only [Subst.applyTerm_id] using holds.symm
  exact ⟨τ, incoming, localValues.imp (fun _ _ h => ⟨h.1, incoming, h.2⟩)⟩

omit [DecidableEq O] in
private theorem models_iff_members (members : List (Member signature O program)) (ρ : Subst signature) :
    Unifies ρ ((bag members).information (act signature) before) ↔
      Unifies ρ before.knowledge ∧
        ∀ m ∈ members, Unifies ρ (m.firing.information (act signature) before) := by
  have membersHave (m : Member signature O program) :
      m.firing.information (act signature) before = before.knowledge ++ m.own (act signature) before := by
    exact (RuleSyntax.JointFirings.Member.information_eq (act signature) before m).trans
      (congrArg (fun initial => initial ++ m.own (act signature) before)
        (Interface.Frames.applyStore_id (X := act signature) before.knowledge))
  have bagHas :
      (bag members).information (act signature) before =
        before.knowledge ++ members.flatMap (fun m => m.own (act signature) before) := by
    unfold Bag.information
    exact congrArg (fun initial => initial ++ members.flatMap (fun m => m.own (act signature) before))
      (Interface.Frames.applyStore_id (X := act signature) before.knowledge)
  simp only [bagHas, membersHave, Unifies, List.forall_mem_append, List.forall_mem_flatMap]
  exact ⟨fun ⟨source, each⟩ => ⟨source, fun m inside => ⟨source, each m inside⟩⟩,
    fun ⟨source, each⟩ => ⟨source, fun m inside => (each m inside).2⟩⟩

omit [DecidableEq O] in
theorem pair_of_right {R : Member signature O program → Member signature O program → Prop}
    {left right : List (Member signature O program)} (pairs : List.Forall₂ R left right) :
    ∀ r ∈ right, ∃ l ∈ left, R l r := by
  induction pairs with
  | nil => intro r inside; cases inside
  | @cons l r restL restR related paired ih =>
    intro query inside
    rcases List.mem_cons.mp inside with rfl | later
    · exact ⟨l, List.mem_cons_self, related⟩
    · obtain ⟨other, there, corresponds⟩ := ih query later
      exact ⟨other, List.mem_cons_of_mem _ there, corresponds⟩

private abbrev EnabledEach (members : List (Member signature O program)) :=
  ∀ m ∈ members, Enabled (fun _ : O => ()) before.present (m.selection.commit (T := Unit))

private theorem transport_model {left right : List (Member signature O program)} {ξ τ : Subst signature}
    (pairs : List.Forall₂ (Paired before ξ τ) left right)
    (incoming : ∀ term, before.Mentions term → ξ.applyTerm term = τ.applyTerm term)
    (usable : EnabledEach (before := before) left) (model : Unifies ξ ((bag left).information (act signature) before)) :
    Unifies τ ((bag right).information (act signature) before) := by
  obtain ⟨initial, done⟩ := (models_iff_members (before := before) left ξ).mp model
  apply (models_iff_members (before := before) right τ).mpr
  constructor
  · intro e inside
    have lhs := incoming e.1 (.inl (List.mem_map.mpr ⟨e, inside, rfl⟩))
    have rhs := incoming e.2 (.inr (.inl (List.mem_map.mpr ⟨e, inside, rfl⟩)))
    rw [← lhs, ← rhs]
    exact initial e inside
  · intro r inside
    obtain ⟨l, used, same, values⟩ := pair_of_right pairs r inside
    exact same.model_transport values (usable l used) (done l used)

omit [DecidableEq O] in
private theorem transport_holds {left right : List (Member signature O program)} {ξ τ : Subst signature}
    (pairs : List.Forall₂ (Paired before ξ τ) left right)
    (holds : (bag left).Holds (act signature) before (b := PUnit.unit) ξ) :
    (bag right).Holds (act signature) before (b := PUnit.unit) τ := by
  intro r inside
  obtain ⟨l, used, same, values⟩ := pair_of_right pairs r inside
  exact same.holds_transport values (holds l used)

theorem transport_joint_tests {left right : List (Member signature O program)}
    (pairs : List.Forall₂ (Same before) left right)
    (leftFresh : (bag left).Fresh (act signature) before)
    (rightFresh : (bag right).Fresh (act signature) before)
    (leftEnabled : EnabledEach (before := before) left)
    (rightEnabled : EnabledEach (before := before) right)
    (consistent : (act signature).Solvable ((bag left).information (act signature) before))
    (checked : (act signature).Entails ((bag left).information (act signature) before)
      (fun b σ => (bag left).Holds (act signature) before (b := b) σ)) :
    (act signature).Solvable ((bag right).information (act signature) before) ∧
      (act signature).Entails ((bag right).information (act signature) before)
        (fun b σ => (bag right).Holds (act signature) before (b := b) σ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨point, ξ, model⟩ := consistent
    cases point
    obtain ⟨τ, incoming, alignment⟩ := realize_pairs pairs rightFresh ξ
    exact ⟨PUnit.unit, τ, transport_model alignment incoming leftEnabled model⟩
  · intro point τ model
    cases point
    have flipped : List.Forall₂ (Same before) right left :=
      pairs.flip.imp (fun _ _ equal => equal.symm)
    obtain ⟨ξ, incoming, alignment⟩ := realize_pairs flipped leftFresh τ
    have solved := transport_model alignment incoming rightEnabled model
    have back : List.Forall₂ (Paired before ξ τ) left right :=
      alignment.flip.imp (fun _ _ pair => ⟨pair.1.symm, pair.2.reverse pair.1⟩)
    exact transport_holds back (checked PUnit.unit ξ solved)

theorem admits_joint {left right : List (Member signature O program)}
    (pairs : List.Forall₂ (Same before) left right)
    (admitted : (bag left).Admits (act signature) before)
    (fits : (bag right).Fits (act signature) before)
    (enabled : Enabled (fun _ : O => ()) before.present ((bag right).selection.commit (T := Unit))) :
    (bag right).Admits (act signature) before := by
  have transferred := transport_joint_tests pairs admitted.1.1 fits.1
    (fun _ inside => Bag.enabled_member admitted.2.1 inside) (fun _ inside => Bag.enabled_member enabled inside)
    admitted.2.2.1 admitted.2.2.2
  exact ⟨fits, enabled, transferred⟩

theorem admits_snapshot {left right : List (Member signature O program)}
    (pairs : List.Forall₂ (Same before) left right)
    (admitted : (bag left).AdmitsSnapshot (act signature) before)
    (fits : (bag right).Fits (act signature) before)
    (enabled : EnabledEach (before := before) right) :
    (bag right).AdmitsSnapshot (act signature) before :=
  ⟨fits, enabled, transport_joint_tests pairs admitted.1.1 fits.1 admitted.2.1 enabled
    admitted.2.2.1 admitted.2.2.2⟩

theorem admits_own {left right : List (Member signature O program)}
    (pairs : List.Forall₂ (Same before) left right)
    (admitted : (bag left).AdmitsOwn (act signature) before)
    (fits : (bag right).Fits (act signature) before)
    (enabled : Enabled (fun _ : O => ()) before.present ((bag right).selection.commit (T := Unit))) :
    (bag right).AdmitsOwn (act signature) before := by
  have joint := admits_joint pairs (Bag.admits_of_admitsOwn (act signature) admitted) fits enabled
  refine ⟨fits, enabled, joint.2.2.1, ?_⟩
  intro m inside
  obtain ⟨source, wasPresent, same⟩ := pair_of_right pairs m inside
  have old := Bag.admits_member (act signature) (fun _ _ => ⟨Subst.id signature⟩) admitted (m := source) wasPresent
  have shaped : m.firing.Shapes (act signature) before :=
    ⟨Bag.fresh_member (act signature) (fun _ _ => ⟨Subst.id signature⟩) fits.1 inside,
      (List.nodup_flatMap.mp fits.2.1).1 m inside,
      (List.nodup_flatMap.mp fits.2.2.1).1 m inside, fits.2.2.2 m inside⟩
  have allowed := same.admitted old shaped (Bag.enabled_member enabled inside)
  exact allowed.2.2.2

omit [DecidableEq O] in
private theorem same_outputs {left right : List (Member signature O program)} {ξ τ : Subst signature}
    (pairs : List.Forall₂ (Paired before ξ τ) left right) :
    outputWords left ξ = outputWords right τ := by
  induction pairs with
  | nil => rfl
  | @cons l r restL restR aligned tail ih =>
    let outputs (rule : RuleSyntax.Rule (Terms (Term signature))) : List (Term signature) := rule.body.produce
    have authored : outputs l.rule = outputs r.rule := congrArg outputs aligned.1.rule
    have head :
        (l.firing.opened (act signature)).produce.map ξ.applyTerm =
        (r.firing.opened (act signature)).produce.map τ.applyTerm := by
      change ((outputs l.rule).map l.opening.applyTerm).map ξ.applyTerm =
          ((outputs r.rule).map r.opening.applyTerm).map τ.applyTerm
      rw [List.map_map, List.map_map, ← authored]
      apply List.map_congr_left
      intro term present
      have written : term ∈ l.rule.body.produce := present
      exact aligned.2.localValue term (by simp [RuleSyntax.Rule.terms, written])
    exact congrArg₂ List.cons head ih

private theorem move_result_models {left right : List (Member signature O program)}
    (pairs : List.Forall₂ (Same before) left right)
    (rightFresh : (bag right).Fresh (act signature) before)
    (leftEnabled : EnabledEach (before := before) left)
    (source : Subst signature) (words : List (List (Term signature)))
    (observed : WordResultModel before (bag left) source words) :
    WordResultModel before (bag right) source words := by
  obtain ⟨ξ, solved, caller, outputs⟩ := observed
  obtain ⟨τ, incoming, align⟩ := realize_pairs pairs rightFresh ξ
  refine ⟨τ, transport_model align incoming leftEnabled solved, ?_, outputs.trans (same_outputs align)⟩
  intro term mentioned
  exact (incoming term mentioned).symm.trans (caller term mentioned)

/-- Opening a population differently preserves its ordered sequence of
output words and its joint dependence on incoming unknowns. Repeating
a word is observable; this does not identify it with one copy. -/
theorem result_models {left right : List (Member signature O program)}
    (pairs : List.Forall₂ (Same before) left right)
    (leftFresh : (bag left).Fresh (act signature) before)
    (rightFresh : (bag right).Fresh (act signature) before)
    (leftEnabled : EnabledEach (before := before) left)
    (rightEnabled : EnabledEach (before := before) right)
    (source : Subst signature) (words : List (List (Term signature))) :
    WordResultModel before (bag left) source words ↔ WordResultModel before (bag right) source words :=
  ⟨move_result_models pairs rightFresh leftEnabled source words,
    move_result_models (pairs.flip.imp (fun _ _ aligned => aligned.symm)) leftFresh rightEnabled source words⟩

end Mettapedia.Machines.TIsa.Derivation.SymbolicJointReopening
