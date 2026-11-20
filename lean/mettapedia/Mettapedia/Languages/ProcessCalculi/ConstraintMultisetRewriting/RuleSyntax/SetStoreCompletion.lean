import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFiringResults
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricGivenValues

/-! # Complete match regions contain every ground propagation consequence -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

theorem ground_source_agrees (rows : Finset (Term signature)) (ground : GroundRows rows)
    (first second : Subst signature) :
    SymmetricMatches.SourceAgrees (SetStore.represent rows) first second := by
  intro term mentioned
  obtain (known | known | ⟨row, inside, rfl⟩) := mentioned
  · cases known
  · cases known
  · change first.applyTerm row.1 = second.applyTerm row.1
    rw [FirstOrder.ground_fixed first row.1 (ground row.1 (present_value rows inside)),
      FirstOrder.ground_fixed second row.1 (ground row.1 (present_value rows inside))]

theorem source_fixed (rows : Finset (Term signature)) (ground : GroundRows rows)
    (term : Term signature) (mentioned : (SetStore.represent rows).Mentions term) (assignment : Subst signature) :
    assignment.applyTerm term = term := by
  obtain (known | known | ⟨row, inside, rfl⟩) := mentioned
  · cases known
  · cases known
  · exact FirstOrder.ground_fixed _ _ (ground row.1 (present_value rows inside))

theorem models_agree_on_reads (rows : Finset (Term signature)) (ground : GroundRows rows)
    (f : F (P := P)) (yes : f.Admits X (SetStore.represent rows)) (first second : Subst signature)
    (one : X.Models (a := PUnit.unit) (b := PUnit.unit) first (f.information X (SetStore.represent rows)))
    (two : X.Models (a := PUnit.unit) (b := PUnit.unit) second (f.information X (SetStore.represent rows))) :
    ∀ term ∈ f.rule.body.read,
      (first.comp f.opening).applyTerm term = (second.comp f.opening).applyTerm term := by
  intro term read
  have lengths : (f.opened X).read.length = f.selection.read.length := by
    simpa only [Firing.opened, RuleInstance.map, List.length_map] using yes.1.2.2.2.2.1
  obtain ⟨row, pair⟩ := SetStore.zip_left lengths (List.mem_map.mpr ⟨term, read, rfl⟩)
  have present := yes.2.1.kept_subset (List.mem_toFinset.mpr (List.of_mem_zip pair).2)
  have rigid := ground row.1 (present_value rows present)
  have left := f.read_solved (X := X) (s := SetStore.represent rows) one pair
  have right := f.read_solved (X := X) (s := SetStore.represent rows) two pair
  change first.applyTerm (f.opening.applyTerm term) = first.applyTerm ((Subst.id signature).applyTerm row.1) at left
  change second.applyTerm (f.opening.applyTerm term) = second.applyTerm ((Subst.id signature).applyTerm row.1) at right
  rw [Subst.applyTerm_id, FirstOrder.ground_fixed first _ rigid] at left
  rw [Subst.applyTerm_id, FirstOrder.ground_fixed second _ rigid] at right
  rw [Subst.applyTerm_comp, Subst.applyTerm_comp]
  exact left.trans right.symm

theorem models_agree_on_produce (rows : Finset (Term signature)) (ground : GroundRows rows)
    (f : F (P := P)) (pure : Propagates f.rule) (yes : f.Admits X (SetStore.represent rows))
    (first second : Subst signature)
    (one : X.Models (a := PUnit.unit) (b := PUnit.unit) first (f.information X (SetStore.represent rows)))
    (two : X.Models (a := PUnit.unit) (b := PUnit.unit) second (f.information X (SetStore.represent rows))) :
    (f.opened X).produce.map first.applyTerm = (f.opened X).produce.map second.applyTerm := by
  have reads := models_agree_on_reads rows ground f yes first second one two
  change (f.rule.body.produce.map f.opening.applyTerm).map first.applyTerm =
    (f.rule.body.produce.map f.opening.applyTerm).map second.applyTerm
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro term inside
  have agree : ∀ v ∈ term.freeVars, (first.comp f.opening) v = (second.comp f.opening) v := by
    intro v mentioned
    obtain ⟨read, inRead, mentions⟩ := (mem_variables _ _).mp
      (pure.madeScoped ((mem_variables _ _).mpr ⟨term, inside, mentioned⟩))
    exact agree_of_apply_eq _ _ read (reads read inRead) v mentions
  have same := apply_eq_of_agree (first.comp f.opening) (second.comp f.opening) term agree
  simpa only [Subst.applyTerm_comp, Function.comp_def] using same

/-- The symmetric key transports actual residual result models, not just answer counts. -/
theorem same_key_produce (rows : Finset (Term signature)) (ground : GroundRows rows)
    (first second : F (P := P))
    (pure : Propagates second.rule)
    (firstYes : first.Admits X (SetStore.represent rows)) (secondYes : second.Admits X (SetStore.represent rows))
    (same : SymmetricMatches.identity.key first = SymmetricMatches.identity.key second)
    (one two : Subst signature)
    (firstModel : X.Models (a := PUnit.unit) (b := PUnit.unit) one (first.information X (SetStore.represent rows)))
    (secondModel : X.Models (a := PUnit.unit) (b := PUnit.unit) two (second.information X (SetStore.represent rows))) :
    (first.opened X).produce.map one.applyTerm = (second.opened X).produce.map two.applyTerm := by
  let output := (first.opened X).produce.map one.applyTerm
  have firstResult : SymmetricMatches.ResultModel (SetStore.represent rows) first (Subst.id signature) output :=
    ⟨one, firstModel, ground_source_agrees rows ground one _, rfl⟩
  have realizes := ((SymmetricMatches.resultModel_iff _ first firstYes _ output).mp firstResult).2
  have relation := (SymmetricMatches.key_eq_iff (SymmetricMatches.presentation first) (SymmetricMatches.presentation second)).mp same
  have secondRealizes := (SymmetricMatches.Same.realizes_iff relation _ (Subst.id signature) output).mp realizes
  have knowledge : Unifies (Subst.id signature) (SetStore.represent rows).knowledge := by
    intro equation inside
    cases inside
  have secondResult := (SymmetricMatches.resultModel_iff _ second secondYes _ output).mpr
    ⟨knowledge, secondRealizes⟩
  obtain ⟨assignment, model, _, result⟩ := secondResult
  exact result.trans (models_agree_on_produce rows ground second pure secondYes assignment two model secondModel)

theorem complete_contains_consequence (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule) (bag : SetStore.Candidate P)
    (own : bag.AdmitsOwn X (SetStore.represent rows))
    (complete : bag.CompleteBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ)
    (answer : Subst signature)
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer (bag.information X (SetStore.represent rows)))
    (match_ : GroundMatch P) (enabled : (consequence match_).read ⊆ rows) :
    (consequence match_).made ⊆ SetStore.setResult rows bag answer := by
  have original := firing_admitted match_ rows ground enabled
  have key := complete match_.firing (Set.mem_univ (SymmetricMatches.identity.key match_.firing)) original
  obtain ⟨member, inside, same⟩ := List.mem_map.mp key
  have memberYes := Bag.admits_member X (fun _ _ => ⟨Subst.id signature⟩) own inside
  have originalModel : X.Models (a := PUnit.unit) (b := PUnit.unit) match_.assignment
      (match_.firing.information X (SetStore.represent rows)) := by
    rw [firing_information]
    exact problem_solved match_
  have memberModel := Bag.models_member X inside solved
  have output := same_key_produce rows ground match_.firing member.firing (pure member.rule member.member)
    original memberYes same.symm match_.assignment answer originalModel memberModel
  rw [firing_produce] at output
  intro value made
  have produced : value ∈ (member.firing.opened X).produce.map answer.applyTerm := by
    rw [← output]
    exact List.mem_toFinset.mp made
  obtain ⟨term, inProduce, rfl⟩ := List.mem_map.mp produced
  apply (SetStore.mem_update).mpr
  right
  exact Finset.mem_image.mpr ⟨term, List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨member, inside, inProduce⟩), rfl⟩

/-- A complete bag makes progress whenever the positive region is not closed. -/
theorem complete_progress_witness (timing : SetStore.AskTiming) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule) (bag : SetStore.Candidate P)
    (own : bag.AdmitsOwn X (SetStore.represent rows))
    (complete : bag.CompleteBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ)
    (notClosed : ¬ SetStoreClosure.Closed (consequence (P := P)) rows) :
    ∃ answer, unifyTotal (bag.information X (SetStore.represent rows)) = some answer ∧
      bag.members ≠ [] ∧ SetStore.admitted timing rows bag ∧
        ¬ SetStore.SameRows rows (SetStore.setResult rows bag answer) := by
  obtain ⟨match_, enabled, outside⟩ : ∃ match_ : GroundMatch P,
      (consequence match_).read ⊆ rows ∧ ¬ (consequence match_).made ⊆ rows := by
    obtain ⟨match_, failure⟩ := Classical.not_forall.mp notClosed
    obtain ⟨enabled, outside⟩ := Classical.not_imp.mp failure
    exact ⟨match_, enabled, outside⟩
  obtain ⟨value, made, missing⟩ := Finset.not_subset.mp outside
  have yes := Bag.admits_of_admitsOwn X own
  obtain ⟨b, witness, model⟩ := own.2.2.1
  cases b
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent _).mpr ⟨witness, model⟩
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer (bag.information X (SetStore.represent rows)) :=
    unifyTotal_sound _ _ accepted
  have contains := complete_contains_consequence rows ground pure bag own complete answer solved match_ enabled made
  have changed : ¬ SetStore.SameRows rows (SetStore.setResult rows bag answer) := by
    intro same
    exact missing ((sameRows_ground_eq ground same) ▸ contains)
  have nonempty : bag.members ≠ [] := by
    intro empty
    have present := complete match_.firing (Set.mem_univ (SymmetricMatches.identity.key match_.firing))
      (firing_admitted match_ rows ground enabled)
    simp [Bag.keysBy, empty] at present
  have admitted : SetStore.admitted timing rows bag := by
    cases timing with
    | afterTells => exact yes
    | beforeTells =>
      apply (Bag.beforeTells_iff_of_no_tells X (SetStore.represent rows) bag ?_).mpr yes
      intro m _
      change m.rule.body.tell.map _ = []
      rw [(pure m.rule m.member).noTell, List.map_nil]
  exact ⟨answer, accepted, nonempty, admitted, changed⟩

theorem complete_progress (timing : SetStore.AskTiming) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule) (bag : SetStore.Candidate P)
    (own : bag.AdmitsOwn X (SetStore.represent rows))
    (complete : bag.CompleteBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ)
    (notClosed : ¬ SetStoreClosure.Closed (consequence (P := P)) rows) :
    ∃ after, SetStore.Step timing P rows after ∧
      ∃ answer, unifyTotal (bag.information X (SetStore.represent rows)) = some answer ∧
        after = SetStore.setResult rows bag answer := by
  obtain ⟨answer, accepted, nonempty, admitted, changed⟩ :=
    complete_progress_witness timing rows ground pure bag own complete notClosed
  exact ⟨_, ⟨bag, nonempty, admitted, answer, accepted, rfl, changed⟩, answer, accepted, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
