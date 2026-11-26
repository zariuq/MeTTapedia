import Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFiringResults

/-!
# Fresh opening is not a choice of meaning

Freshness lets one realize the same incoming and rule-local values at
another opening. This preserves admission, including universally
quantified guards and collection claims. The result is compared on its
incoming interface and its produced terms, not by equating the freshly
named residual equation stores.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (Program)
open RuleSyntax.OneFrame (Terms ext)
open RuleSyntax.JointFirings.SymmetricMatches
  (presentation models_information_iff row_identity ResultModel resultModel_iff)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {program : Program (Terms (Term signature))} {before : World signature O}

abbrev Firing (before : World signature O) (program : Program (Terms (Term signature))) :=
  RuleSyntax.Firing O (ext (FirstOrder.action signature)) program before.frame

structure SameInput (first second : Firing before program) : Prop where
  rule : first.rule = second.rule
  taken : first.selection.taken = second.selection.taken
  read : first.selection.read = second.selection.read
  seen : first.seen = second.seen

namespace SameInput

variable {first second : Firing before program}

omit [DecidableEq O] in
theorem symm (same : SameInput first second) :
    SameInput second first := ⟨same.rule.symm, same.taken.symm, same.read.symm, same.seen.symm⟩

omit [DecidableEq O] in
theorem presentation_eq (same : SameInput first second) : presentation first = presentation second := by
  let matching (rule : RuleSyntax.Rule (Terms (Term signature))) (taken read : List O) :
      RuleSyntax.JointFirings.SymmetricMatches.Presentation signature O :=
    ⟨rule, (rule.body.take.zip taken : List (Term signature × O)),
      (rule.body.read.zip read : List (Term signature × O))⟩
  change matching first.rule first.selection.taken first.selection.read =
    matching second.rule second.selection.taken second.selection.read
  rw [same.rule, same.taken, same.read]

structure Agree (first second : Firing before program) (left right : Subst signature) : Prop where
  incoming : ∀ term, before.Mentions term → left.applyTerm term = right.applyTerm term
  localValue : ∀ term ∈ first.rule.terms,
    left.applyTerm (first.opening.applyTerm term) = right.applyTerm (second.opening.applyTerm term)

omit [DecidableEq O] in
theorem Agree.reverse {left right : Subst signature} (values : Agree first second left right)
    (same : SameInput first second) : Agree second first right left :=
  ⟨fun term mentioned => (values.incoming term mentioned).symm,
    fun term used => (values.localValue term (same.rule ▸ used)).symm⟩

omit [DecidableEq O] in
private theorem realise (same : SameInput first second)
    (fresh : second.Fresh (act signature) before) (ξ : Subst signature) :
    ∃ τ, Agree first second ξ τ := by
  obtain ⟨τ, incoming, localValues⟩ := fresh PUnit.unit ξ (ξ.comp first.opening)
  refine ⟨τ, ⟨?_, ?_⟩⟩
  · intro term mentioned
    have equal := incoming term mentioned
    change τ.applyTerm ((Subst.id signature).applyTerm term) = ξ.applyTerm term at equal
    simpa only [Subst.applyTerm_id] using equal.symm
  · intro term authored
    have equal := localValues term (same.rule ▸ authored)
    change τ.applyTerm (second.opening.applyTerm term) = (ξ.comp first.opening).applyTerm term at equal
    simpa only [Subst.applyTerm_comp] using equal.symm

omit [DecidableEq O] in
private theorem Agree.labelValue {left right : Subst signature} (values : Agree first second left right)
    (i : O) (live : i ∈ before.present) :
    left.applyTerm (before.label i) = right.applyTerm (before.label i) :=
  values.incoming _ (.inr (.inr ⟨i, live, rfl⟩))

theorem model_transport (same : SameInput first second)
    {left right : Subst signature} (values : Agree first second left right)
    (available : Enabled (fun _ : O => ()) before.present (first.selection.commit (T := Unit)))
    (model : Unifies left (first.information (act signature) before)) :
    Unifies right (second.information (act signature) before) := by
  obtain ⟨knowledge, matched, told⟩ := (models_information_iff before first left).mp model
  apply (models_information_iff before second right).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro equation member
    have lhs := values.incoming equation.1 (.inl (List.mem_map.mpr ⟨equation, member, rfl⟩))
    have rhs := values.incoming equation.2 (.inr (.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)))
    rw [← lhs, ← rhs]
    exact knowledge equation member
  · intro pair member
    have inside : pair ∈ (presentation first).uses := same.presentation_eq ▸ member
    have endpoints : pair.1 ∈ first.rule.terms ∧ pair.2 ∈ before.present := by
      simp only [presentation, RuleSyntax.JointFirings.SymmetricMatches.Presentation.uses,
        Multiset.mem_add, Multiset.mem_coe] at inside
      rcases inside with found | found
      · obtain ⟨term, live⟩ := List.of_mem_zip found
        exact ⟨by simp [RuleSyntax.Rule.terms, term],
          available.taken_subset (List.mem_toFinset.mpr live)⟩
      · obtain ⟨term, live⟩ := List.of_mem_zip found
        exact ⟨by simp [RuleSyntax.Rule.terms, term],
          available.kept_subset (List.mem_toFinset.mpr live)⟩
    simp only [Subst.applyTerm_comp] at matched ⊢
    rw [← values.localValue _ endpoints.1, ← values.labelValue _ endpoints.2]
    exact matched pair (same.presentation_eq ▸ member)
  · intro equation inside
    have authored : equation ∈ first.rule.body.tell := same.rule ▸ inside
    have lhs : equation.1 ∈ first.rule.terms := by
      simp [RuleSyntax.Rule.terms, List.mem_map.mpr ⟨equation, authored, rfl⟩]
    have rhs : equation.2 ∈ first.rule.terms := by
      simp [RuleSyntax.Rule.terms, List.mem_map.mpr ⟨equation, authored, rfl⟩]
    simp only [Subst.applyTerm_comp] at told ⊢
    rw [← values.localValue _ lhs, ← values.localValue _ rhs]
    simpa only [Subst.applyTerm_comp] using told equation authored

omit [DecidableEq O] in
private theorem Agree.matches {left right : Subst signature} (values : Agree first second left right)
    {pattern : Term signature} (authored : pattern ∈ first.rule.terms) :
    RuleSyntax.matchesAt (act signature) (b := PUnit.unit) left (first.row (act signature) before)
      before.present (first.opening.applyTerm pattern) =
    RuleSyntax.matchesAt (act signature) (b := PUnit.unit) right (second.row (act signature) before)
      before.present (second.opening.applyTerm pattern) := by
  ext i
  rw [RuleSyntax.mem_matchesAt, RuleSyntax.mem_matchesAt, row_identity, row_identity]
  apply and_congr_right
  intro live
  change (left.applyTerm (first.opening.applyTerm pattern) = left.applyTerm (before.label i)) ↔
    (right.applyTerm (second.opening.applyTerm pattern) = right.applyTerm (before.label i))
  rw [values.localValue _ authored, values.labelValue i live]

omit [DecidableEq O] in
private theorem Agree.check {left right : Subst signature} (values : Agree first second left right)
    (query : Check (Term signature)) (authored : query ∈ first.rule.body.checks) :
    RuleSyntax.checkHolds (act signature) (b := PUnit.unit) left (first.row (act signature) before)
      before.present (query.map first.opening.applyTerm) ↔
    RuleSyntax.checkHolds (act signature) (b := PUnit.unit) right (second.row (act signature) before)
      before.present (query.map second.opening.applyTerm) := by
  have terms : ∀ t ∈ RuleSyntax.checkTerms query, t ∈ first.rule.terms := by
    intro t used
    simp only [RuleSyntax.Rule.terms, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨query, authored, used⟩))
  cases query with
  | equal lhs rhs =>
    change (left.applyTerm (first.opening.applyTerm lhs) = left.applyTerm (first.opening.applyTerm rhs)) ↔
      (right.applyTerm (second.opening.applyTerm lhs) = right.applyTerm (second.opening.applyTerm rhs))
    rw [values.localValue _ (terms _ (by simp [RuleSyntax.checkTerms])),
      values.localValue _ (terms _ (by simp [RuleSyntax.checkTerms]))]
  | predicate q pattern =>
    have equal := values.localValue pattern (terms _ (by simp [RuleSyntax.checkTerms]))
    simp only [Check.map, RuleSyntax.checkHolds, row_identity]
    apply q.holds_congr
    intro i live
    change (left.applyTerm (first.opening.applyTerm pattern) = left.applyTerm (before.label i)) ↔
      (right.applyTerm (second.opening.applyTerm pattern) = right.applyTerm (before.label i))
    rw [equal, values.labelValue i live]
  | count pattern number =>
    simp only [Check.map, RuleSyntax.checkHolds, values.matches (terms pattern (by simp [RuleSyntax.checkTerms]))]

omit [DecidableEq O] in
theorem holds_transport (same : SameInput first second)
    {left right : Subst signature} (values : Agree first second left right)
    (holds : first.Holds (act signature) before (b := PUnit.unit) left) :
    second.Holds (act signature) before (b := PUnit.unit) right := by
  constructor
  · intro guard found
    change guard ∈ second.rule.body.checks.map (Check.map second.opening.applyTerm) at found
    obtain ⟨query, authored, rfl⟩ := List.mem_map.mp found
    have inFirst : query ∈ first.rule.body.checks := same.rule ▸ authored
    exact (values.check query inFirst).mp (holds.1 _
      (List.mem_map.mpr ⟨query, inFirst, rfl⟩))
  · intro claim found
    change claim ∈ (second.rule.collect.map second.opening.applyTerm).zip second.seen at found
    rw [List.zip_map_left] at found
    obtain ⟨⟨pattern, seen⟩, authored, returned⟩ := List.mem_map.mp found
    obtain rfl := returned
    have inFirst : (pattern, seen) ∈ first.rule.collect.zip first.seen := by
      rw [same.rule, same.seen]
      exact authored
    have exposed : pattern ∈ first.rule.terms := by
      simp [RuleSyntax.Rule.terms, (List.of_mem_zip inFirst).1]
    have collected := holds.2 (first.opening.applyTerm pattern, seen) (by
      change _ ∈ (first.rule.collect.map first.opening.applyTerm).zip first.seen
      rw [List.zip_map_left]
      exact List.mem_map.mpr ⟨(pattern, seen), inFirst, rfl⟩)
    exact (values.matches exposed).symm.trans collected

theorem admitted (same : SameInput first second) (previous : first.Admits (act signature) before)
    (shaped : second.Shapes (act signature) before)
    (available : Enabled (fun _ : O => ()) before.present (second.selection.commit (T := Unit))) :
    second.Admits (act signature) before := by
  obtain ⟨b, ξ, model⟩ := previous.2.2.1
  cases b
  obtain ⟨τ, agreement⟩ := same.realise shaped.1 ξ
  refine ⟨shaped, available, ⟨PUnit.unit, τ, same.model_transport agreement previous.2.1 model⟩, ?_⟩
  intro b ρ solved
  cases b
  obtain ⟨η, agreement⟩ := same.symm.realise previous.1.1 ρ
  have read := same.symm.model_transport agreement available solved
  exact same.holds_transport (agreement.reverse same.symm) (previous.2.2.2 PUnit.unit η read)

theorem result_models (same : SameInput first second)
    (firstAdmitted : first.Admits (act signature) before)
    (secondAdmitted : second.Admits (act signature) before)
    (incoming : Subst signature) (produced : List (Term signature)) :
    ResultModel before first incoming produced ↔ ResultModel before second incoming produced := by
  rw [resultModel_iff before first firstAdmitted,
    resultModel_iff before second secondAdmitted, same.presentation_eq]

end SameInput

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
