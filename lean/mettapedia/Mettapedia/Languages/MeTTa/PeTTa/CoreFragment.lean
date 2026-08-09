import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness

/-!
# PeTTa Core Fragment

Defines the first real PeTTa runtime fragment that lands cleanly on the current
`R_exec₀` theorem boundary.

The fragment is intentionally small:
- `evalStep`
- `evalcStep`

Both are genuine PeTTa runtime constructors, both are top-level rule-application
steps, and both can be pushed to the current MORK source-rule boundary without
pretending that beta-reduction or substitution-heavy steps are already covered.

Positive example:
- a safe PeTTa `evalStep` with `fvar` LHS lands on `fireSourceRule`.

Negative example:
- `betaReduce` is not in this fragment, because the current MORK bridge still
  excludes `.subst`-driven runtime reduction.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.CoreFragment

open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.ProcessCalculi.MORK

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILRewriteRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILBindings := Mettapedia.OSLF.MeTTaIL.Match.Bindings

/-- A PeTTa rule belongs to the current core fragment exactly when:
- it satisfies the existing safe/runtime-side fragment check, and
- its LHS is an `fvar`, matching the current theoremic MORK source bridge. -/
def pettaCoreRule (r : ILRewriteRule) : Prop :=
  Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaRuleSafe r = true ∧
    ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x

/-- The first explicit PeTTa runtime core fragment.

This is the maximal low-risk fragment that already aligns with the current
`R_exec₀` proof interface. It deliberately stays on rule application and does not
claim coverage for substitution-heavy runtime steps.
-/
inductive PeTTaCoreStep (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) :
    ILPattern → ILPattern → Prop where
  | evalStep (r : ILRewriteRule) (bs : ILBindings) (p q : ILPattern)
      (hr : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm : bs ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
      (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
      (hcore : pettaCoreRule r) :
      PeTTaCoreStep s (.apply "eval" [p]) q
  | evalcStep (r : ILRewriteRule) (bs : ILBindings) (p q : ILPattern)
      (hr : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm : bs ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
      (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
      (hcore : pettaCoreRule r) :
      PeTTaCoreStep s (.apply "evalc" [p]) q

/-- Reflexive-transitive closure of the first PeTTa runtime core fragment. -/
abbrev PeTTaCoreStepStar (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) :=
  Relation.ReflTransGen (PeTTaCoreStep s)

@[simp] theorem pettaCoreRule_safe {r : ILRewriteRule}
    (h : pettaCoreRule r) :
    Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaRuleSafe r = true := h.1

theorem pettaCoreRule_fvar {r : ILRewriteRule}
    (h : pettaCoreRule r) :
    ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x := h.2

/-- PeTTa rules in the current packaged runtime-core steps are guardless because
their active theorem boundary uses no-premise rule application. -/
@[simp] theorem noPremiseRule_guards_empty {r : ILRewriteRule}
    (hprem : r.premises = []) :
    premisesToSourceGuards r.premises = [] := by
  simp [hprem, premisesToSourceGuards]

/-- For the current PeTTa runtime-core path, the extended source-rule
translation collapses back to the existing guardless one whenever the rule has
no premises. This matches the fact that `PeTTaCoreStep` is currently a
no-premise rule-application fragment. -/
@[simp] theorem noPremiseRule_extendedTranslation_eq {r : ILRewriteRule}
    (hprem : r.premises = []) :
    rewriteRuleToSourceExecRuleExt r = rewriteRuleToSourceExecRule r := by
  cases r
  cases hprem
  simp [rewriteRuleToSourceExecRuleExt, rewriteRuleToSourceExecRule,
    premisesToSourceFactorsExt, premisesToSourceFactors, premisesToSourceGuards,
    premiseToFactorOrGuard]

/-- Forget the core-fragment restriction back to the full PeTTa small-step
relation. -/
theorem toMeTTaStep {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {p q : ILPattern} (h : PeTTaCoreStep s p q) :
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaStep s p q := by
  cases h with
  | evalStep r bs p q hr hprem hm hq _ =>
      exact Mettapedia.Languages.MeTTa.PeTTa.MeTTaStep.evalStep r bs p q hr hprem hm hq
  | evalcStep r bs p q hr hprem hm hq _ =>
      exact Mettapedia.Languages.MeTTa.PeTTa.MeTTaStep.evalcStep r bs p q hr hprem hm hq

/-- Star closure in the core fragment forgets to star closure in the full PeTTa
runtime relation. -/
theorem toMeTTaStepStar {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {p q : ILPattern} (h : PeTTaCoreStepStar s p q) :
    Relation.ReflTransGen (Mettapedia.Languages.MeTTa.PeTTa.MeTTaStep s) p q := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
      exact Relation.ReflTransGen.tail ih (toMeTTaStep hstep)

/-- A core-fragment `eval` step lands on the current `R_exec₀` source-rule
firing boundary. -/
theorem evalStep_toMorkSourceFire
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {r : ILRewriteRule} {bs : ILBindings} {p q : ILPattern}
    (hr : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm : bs ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
    (hcore : pettaCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    {workspace : Space}
    (hp_in : morkPatternToAtom p ∈ workspace) :
    ∃ r_source ∈ morkRuntimeExec0.sourceRuleSetTranslation
        (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s),
      applySinks workspace (morkRuntimeExec0.bindingsTranslation bs) r_source.tmpl ∈
        fireSourceRule workspace r_source := by
  rcases pettaCoreRule_fvar hcore with ⟨x, hlhs⟩
  have hsafe_parts :=
    (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaRuleSafe_iff r).1
      (pettaCoreRule_safe hcore)
  have htrans_rhs : morkRuntimeExec0.fragmentPredicate r.right = true := hsafe_parts.2.1
  have hr_lang :
      r ∈ (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s).rewrites := by
    simpa [Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef_rewrites] using hr
  refine ⟨morkRuntimeExec0.sourceRuleTranslation r, ?_, ?_⟩
  · show rewriteRuleToSourceExecRule r ∈
        languageDefToSourceExecRules
          (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s)
    simp only [languageDefToSourceExecRules, List.mem_filterMap]
    refine ⟨r, hr_lang, ?_⟩
    simp [hprem, allPremisesTranslatable, premiseToSourceFactor]
  · simpa [morkRuntimeExec0, MeTTaRuntimeExecInterface.bindingsTranslation,
      MeTTaRuntimeExecInterface.sourceRuleTranslation] using
      (morkRuntimeExec0.noPremiseBridge p q x r
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s)
        hlhs htrans_rhs hprem bs hm hq hground workspace hp_in)

/-- A core-fragment `evalc` step lands on the current `R_exec₀` source-rule
firing boundary.  Operationally this is the same source-rule application shape
as `eval`; the difference is only the outer control symbol. -/
theorem evalcStep_toMorkSourceFire
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {r : ILRewriteRule} {bs : ILBindings} {p q : ILPattern}
    (hr : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm : bs ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
    (hcore : pettaCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    {workspace : Space}
    (hp_in : morkPatternToAtom p ∈ workspace) :
    ∃ r_source ∈ morkRuntimeExec0.sourceRuleSetTranslation
        (Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef s),
      applySinks workspace (morkRuntimeExec0.bindingsTranslation bs) r_source.tmpl ∈
        fireSourceRule workspace r_source := by
  exact evalStep_toMorkSourceFire hr hprem hm hq hcore hground hp_in

end Mettapedia.Languages.MeTTa.PeTTa.CoreFragment
