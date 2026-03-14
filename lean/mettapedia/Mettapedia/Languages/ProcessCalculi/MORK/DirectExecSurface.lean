import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
import Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment

/-!
# MM2/MORK Direct-Exec Surface

Packages the scheduler-level exactness theorems (Tasks A/B/C) into a single
reusable "directExec seam" and composes the first real PeTTa fragment through it.

## What this file IS

A narrow packaging of:
1. Scheduler order agreement on `schedulerLocFragment`
2. Base / unfold / fold phase exactness
3. The sharpened scheduler–source relation (`fireExecFact = source − exec atom`)
4. Scheduler progress (`selectNextExec = some → cWorkQueueStep = some`)

Plus one honest bridge theorem: PeTTa eval/evalc steps fire through this seam.

## What this file is NOT

- Not a redesign of MM2 or the scheduler
- Not a claim that all MeTTa runtime semantics are directly executable
- Not a lift of scheduler metadata upward into RuntimeSpec
- Not a coverage claim for congElem, beta-reduction, or full runtime control

## Honest blockers for features NOT yet covered

- `add-atom` / `remove-atom`: MORK sinks support `.add`/`.remove`, and
  `base_step_exactness` handles the single-add-result case. The blocker is
  on the MeTTa side: no MeTTaIL-level formalization of `add-atom` as a
  rewrite rule that can be translated to a SourceExecRule. The MORK side is
  ready; the bridge premise is missing.

- Collection-pattern matching: excluded by `morkTranslatable` (no rest-vars).

- Beta-reduction: `.subst` nodes rejected by `morkTranslatable`.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.DirectExecSurface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
open Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILRewriteRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILBindings := Mettapedia.OSLF.MeTTaIL.Match.Bindings
private abbrev CSpace :=
  Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.CSpace

/-! ## Part 1: Scheduler-level exactness package

Re-exported as a coherent family. Each theorem is proven in
`WorkQueueOrder.lean` or `ThreePhaseRefinement.lean`. -/

namespace SchedulerSeam

/-- Scheduler byte-key order agrees with shortlex on (priority, name). -/
abbrev orderAgreement := @atomKey_order_on_fragment

/-- Scheduler order is irreflexive. -/
abbrev orderIrrefl := @locLt_irrefl

/-- Scheduler order is asymmetric. -/
abbrev orderAsymm := @locLt_asymm

/-- Scheduler order is transitive. -/
abbrev orderTrans := @locLt_trans

/-- Base phase: scheduler step = `applyBase`. -/
abbrev baseExactness := @base_step_exactness

/-- Unfold phase: scheduler step = `applyUnfold`. -/
abbrev unfoldExactness := @unfold_step_exactness

/-- Fold phase: scheduler step = `applyFold`. -/
abbrev foldExactness := @fold_step_exactness

/-- Scheduler result = source result minus consumed exec atom. -/
abbrev sourceBridge := @fireExecFact_eq_applySinks_sdiff

/-- `applySinks` commutes with set difference when no sink produces the atom. -/
abbrev sinksSdiffComm := @applySinks_sdiff_comm

/-- Non-production predicate: no sink adds the given atom. -/
abbrev nonProduction := @SinksDontProduce

/-- Scheduler progress: selected exec fact → `cWorkQueueStep = some`. -/
abbrev progress := @scheduler_progress

end SchedulerSeam

/-! ## Part 2: Query seam (re-export)

Queries (`match &self`, `get-atoms &self`) don't fire through the scheduler —
they're pattern matches against the workspace that happen as premises during
a source-rule fire. The existing source-query seam is already the right
abstraction level.

Re-exported here for proximity. -/

namespace QuerySeam

/-- `(match &self $x tmpl)` lands on MORK source-query (spec level). -/
abbrev matchSelfSpec := @anyFactMatch_toMorkSourceQuery

/-- `(match &self $x tmpl)` lands on MORK source-query (computable). -/
abbrev matchSelfComputable := @anyFactMatch_toComputableSourceQuery

/-- `(get-atoms &self)` lands on MORK source-query (computable). -/
abbrev getAtomsComputable := @getAtoms_toComputableSourceQuery

end QuerySeam

/-! ## Part 3: PeTTa eval fragment → scheduler seam

Composes `evalStep_toMorkSourceFire` (PeTTa step → source-level fire)
with `fireExecFact_eq_applySinks_sdiff` (source fire → scheduler fire).

The result: a PeTTa eval step, when executed through an aligned exec fact
in the workspace, produces the source-level result minus the consumed exec atom.

### Hypotheses (honest list of what the MM2 compiler must ensure)

1. **Exec-fact alignment**: an exec fact `ef` in the workspace encodes the
   translated source rule, meaning `ef.rule.tmpl = r_source.tmpl` and
   the binding substitution matches.
2. **Single-match condition**: the exec pattern matches uniquely against
   the workspace.
3. **Non-production**: no sink in the template adds `ef.atom` back.

These are genuine encoding invariants that the MM2 compiler maintains by
construction; they cannot be proven in Lean without an encoder function
(which lives in the Rust runtime). -/

/-- PeTTa eval step fires through the MM2/MORK scheduler seam.

Given:
- A PeTTa eval step producing result `q` via rule `r` with bindings `bs`
- A workspace containing `morkPatternToAtom p` (the input)
- An exec fact `ef` in the workspace encoding `r`
- Single-match and non-production conditions

Conclusion:
The scheduler-level `fireExecFact` result equals `S \ {ef.atom}` where
`S` is a member of the source-level `fireSourceRule` result set.

This is the first real MeTTa fragment that honestly lands on the MM2
scheduler seam, using the exactness results from Tasks A/B/C. -/
theorem pettaEvalStep_schedulerFires
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {r : ILRewriteRule} {bs : ILBindings} {p q : ILPattern}
    (hr : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm : bs ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
    (hcore : pettaCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    -- Workspace with input atom
    {workspace : Space}
    (hp_in : morkPatternToAtom p ∈ workspace)
    -- Exec fact encoding the rule
    (ef : ExecFact) (hef_in : ef.atom ∈ workspace)
    -- Alignment: exec fact template matches the source rule's template
    (hef_tmpl : ef.rule.tmpl = (rewriteRuleToSourceExecRule r).tmpl)
    -- Single match: the exec pattern yields the same substitution
    (σ : Subst) (consumed : Finset Atom)
    (hσ_eq : σ = bindingsToSubst bs)
    (hunique : matchPattern [] workspace ef.rule.pat = [(σ, consumed)])
    -- Non-production: no sink adds ef.atom
    (hndp : SinksDontProduce ef.atom σ ef.rule.tmpl.sinks) :
    -- Conclusion: scheduler result = source result minus exec atom
    ∃ r_source ∈ Mettapedia.Languages.ProcessCalculi.MORK.languageDefToSourceExecRules
        (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s),
      ∃ S ∈ fireSourceRule workspace r_source,
        fireExecFact workspace ef = S \ {ef.atom} := by
  -- Step 1: Source-level fire (from existing PeTTa core fragment bridge)
  obtain ⟨r_source, hr_mem, hfire⟩ :=
    evalStep_toMorkSourceFire hr hprem hm hq hcore hground hp_in
  refine ⟨r_source, hr_mem, applySinks workspace σ ef.rule.tmpl, ?_, ?_⟩
  · -- The source-level result is in fireSourceRule
    rw [hσ_eq, hef_tmpl]; exact hfire
  · -- The scheduler result = source result minus exec atom
    exact fireExecFact_eq_applySinks_sdiff workspace ef hef_in σ consumed hunique hndp

/-- `evalc` variant: same theorem for the `evalc` control symbol. -/
theorem pettaEvalcStep_schedulerFires
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {r : ILRewriteRule} {bs : ILBindings} {p q : ILPattern}
    (hr : r ∈ s.rules) (hprem : r.premises = [])
    (hm : bs ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
    (hcore : pettaCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    {workspace : Space} (hp_in : morkPatternToAtom p ∈ workspace)
    (ef : ExecFact) (hef_in : ef.atom ∈ workspace)
    (hef_tmpl : ef.rule.tmpl = (rewriteRuleToSourceExecRule r).tmpl)
    (σ : Subst) (consumed : Finset Atom)
    (hσ_eq : σ = bindingsToSubst bs)
    (hunique : matchPattern [] workspace ef.rule.pat = [(σ, consumed)])
    (hndp : SinksDontProduce ef.atom σ ef.rule.tmpl.sinks) :
    ∃ r_source ∈ Mettapedia.Languages.ProcessCalculi.MORK.languageDefToSourceExecRules
        (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s),
      ∃ S ∈ fireSourceRule workspace r_source,
        fireExecFact workspace ef = S \ {ef.atom} :=
  pettaEvalStep_schedulerFires hr hprem hm hq hcore hground hp_in
    ef hef_in hef_tmpl σ consumed hσ_eq hunique hndp

/-! ## Canaries -/

section Canaries
#check @SchedulerSeam.orderAgreement
#check @SchedulerSeam.baseExactness
#check @SchedulerSeam.unfoldExactness
#check @SchedulerSeam.foldExactness
#check @SchedulerSeam.sourceBridge
#check @SchedulerSeam.progress
#check @QuerySeam.matchSelfSpec
#check @QuerySeam.matchSelfComputable
#check @QuerySeam.getAtomsComputable
#check @pettaEvalStep_schedulerFires
#check @pettaEvalcStep_schedulerFires
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms pettaEvalStep_schedulerFires
end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.DirectExecSurface
