import Mettapedia.Machines.TIsa.Derivation.FiniteRenaming
import Mettapedia.Machines.TIsa.Derivation.SymbolicAllocation
import Mettapedia.Machines.TIsa.Derivation.SymbolicJointReopening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FreshResultNames

/-!
# Freshen the whole opened batch with one renaming

Instead of comparing individual solutions at each stage, use joint
realization in both directions for the complete finite family of
opened terms. One renaming then acts on the incoming terms and every
member, and is the identity on what the incoming state mentions.
This is suitable for transporting a serial prefix without renaming
the members independently and accidentally breaking their sharing.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.OpeningRenaming

open Mettapedia.Logic.LP
open MutualInstantiation (permutation_of_mutual_lists)
open UnificationRenaming (rename)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.OneFrame (Terms)
open RuleSyntax.JointFirings (bagOf)
open RuleSyntax.JointFirings.FreshResultNames (align)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open SymbolicFiring (LiveWorld act)
open SymbolicJointReopening (Member Same Paired realize_pairs)

variable {σ : LPSignature} {program : RuleSyntax.Program (Terms (Term σ))}

private theorem visible_mentions (before : LiveWorld σ) (term : Term σ) (observed : term ∈ before.visibleTerms) :
    before.state.Mentions term := by
  unfold LiveWorld.visibleTerms at observed
  rcases List.mem_append.mp observed with known | visible
  · exact (List.mem_append.mp known).elim Or.inl (fun side => Or.inr (Or.inl side))
  · obtain ⟨o, live, eq⟩ := List.mem_map.mp visible
    exact Or.inr (Or.inr ⟨o, before.visible ▸ List.mem_toFinset.mpr live, eq⟩)

private def opened (members : List (Member σ ℕ program)) : List (Term σ) :=
  members.flatMap fun member => member.rule.terms.map member.opening.applyTerm

private theorem opened_agree (before : LiveWorld σ)
    {first second : List (Member σ ℕ program)} {ξ τ : Subst σ}
    (paired : List.Forall₂ (Paired before.state ξ τ) first second) :
    (opened first).map ξ.applyTerm = (opened second).map τ.applyTerm := by
  induction paired with
  | nil => rfl
  | @cons l r laterL laterR aligned tail ih =>
    let terms (rule : RuleSyntax.Rule (Terms (Term σ))) : List (Term σ) := rule.terms
    have common : terms l.rule = terms r.rule := congrArg terms aligned.1.rule
    have head : ((terms l.rule).map l.opening.applyTerm).map ξ.applyTerm =
        ((terms r.rule).map r.opening.applyTerm).map τ.applyTerm := by
      rw [List.map_map, List.map_map, ← common]
      apply List.map_congr_left
      exact aligned.2.localValue
    change _ = _
    simp only [opened, List.flatMap_cons, List.map_append] at *
    exact congrArg₂ List.append head ih

private def transcript (before : LiveWorld σ) (members : List (Member σ ℕ program)) : List (Term σ) :=
  before.visibleTerms ++ opened members

private theorem transfer (before : LiveWorld σ)
    {first second : List (Member σ ℕ program)}
    (related : List.Forall₂ (Same before.state) first second)
    (fresh : (bagOf (FirstOrder.action σ) first).Fresh (act σ) before.state) :
    ∃ forward, (transcript before first).map forward.applyTerm = transcript before second ∧
      (∀ term, before.state.Mentions term → forward.applyTerm term = term) ∧
      List.Forall₂ (Paired before.state (Subst.id σ) forward) second first := by
  obtain ⟨forward, fixed, paired⟩ :=
    realize_pairs (related.flip.imp (fun _ _ pair => pair.symm)) fresh (Subst.id σ)
  have preserves (term : Term σ) (mentioned : before.state.Mentions term) : forward.applyTerm term = term := by
    simpa only [Subst.applyTerm_id] using (fixed term mentioned).symm
  refine ⟨forward, ?_, preserves, paired⟩
  have entry : before.visibleTerms.map forward.applyTerm = before.visibleTerms := by
    conv_rhs => rw [← List.map_id before.visibleTerms]
    apply List.map_congr_left
    intro term observed
    exact preserves term (visible_mentions before term observed)
  have body := (opened_agree before paired).symm
  have identity : (Subst.id σ).applyTerm = id := funext Subst.applyTerm_id
  rw [identity, List.map_id] at body
  change (before.visibleTerms ++ opened first).map forward.applyTerm = before.visibleTerms ++ opened second
  rw [List.map_append, entry, body]

theorem variable_permutation [DecidableEq σ.vars] (before : LiveWorld σ)
    {first second : List (Member σ ℕ program)}
    (related : List.Forall₂ (Same before.state) first second)
    (firstFresh : (bagOf (FirstOrder.action σ) first).Fresh (act σ) before.state)
    (secondFresh : (bagOf (FirstOrder.action σ) second).Fresh (act σ) before.state) :
    ∃ π : Equiv.Perm σ.vars,
      (∀ term, before.state.Mentions term → rename π term = term) ∧
      List.Forall₂ (fun l r => Same before.state l r ∧ ∀ term ∈ l.rule.terms,
        rename π (l.opening.applyTerm term) = r.opening.applyTerm term) first second := by
  obtain ⟨forward, advanced, preserves, pair⟩ := transfer before related firstFresh
  obtain ⟨backward, recovered, _, _⟩ := transfer before (related.flip.imp (fun _ _ same => same.symm)) secondFresh
  obtain ⟨π, same, _⟩ :=
    permutation_of_mutual_lists forward backward (transcript before first) (transcript before second) advanced recovered
  have agree := List.map_inj_left.mp (same.trans advanced.symm)
  refine ⟨π, ?_, ?_⟩
  · intro term observed
    have inside : term ∈ transcript before first := List.mem_append_left _ (before.mentions_mem observed)
    rw [agree term inside]
    exact preserves term observed
  · have pointwise : List.Forall₂ (fun l r => Same before.state l r ∧ ∀ term ∈ l.rule.terms,
        r.opening.applyTerm term = forward.applyTerm (l.opening.applyTerm term)) first second :=
      pair.flip.imp (fun _ _ h => ⟨h.1.symm, fun t mentioned => by
        simpa only [Subst.applyTerm_id] using h.2.localValue t (h.1.rule.symm ▸ mentioned)⟩)
    suffices ∀ {ls rs : List (Member σ ℕ program)}, ls ⊆ first →
        List.Forall₂ (fun l r => Same before.state l r ∧ ∀ term ∈ l.rule.terms,
          r.opening.applyTerm term = forward.applyTerm (l.opening.applyTerm term)) ls rs →
        List.Forall₂ (fun l r => Same before.state l r ∧ ∀ term ∈ l.rule.terms,
          rename π (l.opening.applyTerm term) = r.opening.applyTerm term) ls rs from this (fun _ h => h) pointwise
    intro ls rs included compared
    induction compared with
    | nil => exact .nil
    | @cons l r ls rs head tail ih =>
      have belongs : l ∈ first := included List.mem_cons_self
      refine .cons ⟨head.1, fun term authored => ?_⟩ (ih (fun _ member => included (List.mem_cons_of_mem _ member)))
      have occurs : l.opening.applyTerm term ∈ transcript before first :=
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, belongs, List.mem_map.mpr ⟨term, authored, rfl⟩⟩)
      exact (agree _ occurs).trans (head.2 term authored).symm

private theorem equal_output_widths (before : LiveWorld σ) {left right : List (Member σ ℕ program)}
    (paired : List.Forall₂ (Same before.state) left right)
    (leftWidths : ∀ m ∈ left, m.rule.body.produce.length = m.selection.made.length)
    (rightWidths : ∀ m ∈ right, m.rule.body.produce.length = m.selection.made.length) :
    List.Forall₂ (fun l r => l.selection.made.length = r.selection.made.length) left right := by
  induction paired with
  | nil => exact .nil
  | @cons l r ls rs head tail ih =>
    let arity (rule : RuleSyntax.Rule (Terms (Term σ))) : ℕ := rule.body.produce.length
    have same : arity l.rule = arity r.rule := congrArg arity head.rule
    exact .cons ((leftWidths _ List.mem_cons_self).symm.trans (same.trans (rightWidths _ List.mem_cons_self)))
      (ih (fun m seen => leftWidths m (List.mem_cons_of_mem _ seen))
        (fun m seen => rightWidths m (List.mem_cons_of_mem _ seen)))

private theorem concatenated_width {left right : List (Member σ ℕ program)}
    (same : List.Forall₂ (fun l r => l.selection.made.length = r.selection.made.length) left right) :
    (left.flatMap fun m => m.selection.made).length = (right.flatMap fun m => m.selection.made).length := by
  induction same with
  | nil => rfl
  | @cons l r ls rs width rest ih =>
    simp only [List.flatMap_cons, List.length_append]
    exact congrArg₂ Nat.add width ih

private theorem splits_output_map {left right : List (Member σ ℕ program)} (perm : Equiv.Perm ℕ)
    (aligned : List.Forall₂ (fun l r => l.selection.made.length = r.selection.made.length) left right)
    (entire : (left.flatMap fun m => m.selection.made).map perm = right.flatMap fun m => m.selection.made) :
    List.Forall₂ (fun l r => l.selection.made.map perm = r.selection.made) left right := by
  induction aligned with
  | nil => exact .nil
  | @cons l r ls rs width rest ih =>
    simp only [List.flatMap_cons, List.map_append] at entire
    have leftWidth : (l.selection.made.map perm).length = r.selection.made.length := by
      simpa only [List.length_map] using width
    obtain ⟨head, body⟩ := List.append_inj entire leftWidth
    exact .cons head (ih body)

/-- A separate permutation pairs physical outputs in member and port
order. It fixes every original occurrence, including any used in
several read ports. This is independent of the variable permutation. -/
theorem occurrence_permutation (before : LiveWorld σ)
    {left right : List (Member σ ℕ program)}
    (paired : List.Forall₂ (Same before.state) left right)
    (leftFits : (bagOf (FirstOrder.action σ) left).Fits (act σ) before.state)
    (rightFits : (bagOf (FirstOrder.action σ) right).Fits (act σ) before.state)
    (leftEnabled : Enabled (fun _ : ℕ => ()) before.state.present
      ((bagOf (FirstOrder.action σ) left).selection.commit (T := Unit)))
    (rightEnabled : Enabled (fun _ : ℕ => ()) before.state.present
      ((bagOf (FirstOrder.action σ) right).selection.commit (T := Unit))) :
    ∃ perm : Equiv.Perm ℕ,
      (∀ occurrence ∈ before.state.present, perm occurrence = occurrence) ∧
      List.Forall₂ (fun l r => l.selection.made.map perm = r.selection.made) left right := by
  let leftMade := (bagOf (FirstOrder.action σ) left).selection.made
  let rightMade := (bagOf (FirstOrder.action σ) right).selection.made
  have slots := equal_output_widths before paired
    (fun m here => (leftFits.2.2.2 m here).2.2.1) (fun m here => (rightFits.2.2.2 m here).2.2.1)
  have sized : leftMade.length = rightMade.length := concatenated_width slots
  obtain ⟨perm, maps, fixed⟩ := align before.state.present leftMade rightMade leftFits.2.2.1 rightFits.2.2.1 sized
    (fun _ member present => Finset.disjoint_left.mp leftEnabled.fresh (List.mem_toFinset.mpr member) present)
    (fun _ member present => Finset.disjoint_left.mp rightEnabled.fresh (List.mem_toFinset.mpr member) present)
  exact ⟨perm, fixed, splits_output_map perm slots maps⟩

end Mettapedia.Machines.TIsa.Derivation.OpeningRenaming
