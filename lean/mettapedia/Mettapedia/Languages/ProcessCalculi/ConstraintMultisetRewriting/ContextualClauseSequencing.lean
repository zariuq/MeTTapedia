import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseAdmissionViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseRealizationRefinement

/-!
# A subsequent resolved clause sees the same source and compiled state

The next rule may join conditional schemas, tell shared equations, retain
shared references and test absence or counts. Its selected occurrences and
guard world are preserved. The rule's captured variables travel through
the actual previous compiler frame; its query variables remain private.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequencing

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualGuardMatching ContextualConditionalRows
open ContextualClauseViewModels ContextualClauseRealizationRefinement

variable {S : Signature} {Local Query More O : Type} {Γ : Ctx S} {sort : S.Srt}
    [DecidableEq Local] [DecidableEq Query] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {queries : Query → MetaArity S} {locals : Local → MetaArity S}
    {before : ContextualClauseSourceState.World locals O Γ sort} {occupied : Finset Nat}
    {plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort)}
    {picked : Selection O}
    (compiled : ContextualConditionalClauses.Compiled queries locals (before := before.native occupied) plan picked)

theorem next_admitted_iff (more : More → MetaArity S)
    (code : RuleInstance (Term (signature S
      (queryFamily more (ContextualClauseSourceState.resultFamily queries locals before))) Γ sort))
    (selection : Selection O) :
    ContextualConditionalSourceAdmission.Admitted more
        (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
        compiled.firing.target.declarations selection
        (mappedRule more (ContextualClauseSourceState.resultFamily queries locals before) compiled.sourceFrame code)
        compiled.firing.target.rows compiled.firing.target.equations compiled.firing.target.present ↔
      ContextualConditionalSourceAdmission.Admitted more
        (ContextualClauseSourceState.resultLocals queries locals before)
        (ContextualClauseSourceState.resultFamily queries locals before) selection code
        (ContextualClauseSourceState.target queries locals before plan picked).rows
        (ContextualClauseSourceState.target queries locals before plan picked).equations
        (ContextualClauseSourceState.target queries locals before plan picked).present := by
  rw [ContextualClauseStateRefinement.information_exact compiled, ContextualClauseStateRefinement.physical_exact compiled]
  exact ContextualClauseAdmissionViews.admitted_iff (frame := compiled.sourceFrame)
    (fun _ next candidate pattern occurrence => all_rows compiled occurrence next candidate pattern)
    (sourceImages compiled (generator compiled.firing.target.declarations))
    (nativeImages compiled (generator compiled.firing.target.declarations))

def nextPlan (more : More → MetaArity S)
    (source : ContextualPublication.Plan (Term (signature S
      (queryFamily more (ContextualClauseSourceState.resultFamily queries locals before))) Γ sort)) :
    ContextualPublication.Plan (Term (signature S (queryFamily more compiled.firing.target.declarations)) Γ sort) :=
  ⟨mappedRule more (ContextualClauseSourceState.resultFamily queries locals before) compiled.sourceFrame source.rule,
    source.reusable, by
      change source.reusable.length = (source.rule.produce.map _).length
      erw [List.length_map]
      exact source.shape⟩

theorem next_compilation_iff [DecidableEq More] (more : More → MetaArity S)
    (source : ContextualPublication.Plan (Term (signature S
      (queryFamily more (ContextualClauseSourceState.resultFamily queries locals before))) Γ sort))
    (selection : Selection O) (fuel : Nat) :
    let _ : DecidableEq compiled.firing.update.Variables := compiled.firing.update.equality
    (∃ following : ContextualConditionalClauses.Compiled more
        (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
        (before := compiled.firing.target) (nextPlan compiled more source) selection,
      following.firing.fuel = fuel) ↔
    ContextualConditionalSourceAdmission.Admitted more
      (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before) selection source.rule
      (ContextualClauseSourceState.target queries locals before plan picked).rows
      (ContextualClauseSourceState.target queries locals before plan picked).equations
      (ContextualClauseSourceState.target queries locals before plan picked).present := by
  let _ := compiled.firing.update.equality
  constructor
  · rintro ⟨following, _⟩
    exact (next_admitted_iff compiled more source.rule selection).mp following.source_admitted
  · intro admitted
    exact ContextualConditionalClauses.realize more _ (before := compiled.firing.target)
      (nextPlan compiled more source) selection ((next_admitted_iff compiled more source.rule selection).mpr admitted) fuel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequencing
