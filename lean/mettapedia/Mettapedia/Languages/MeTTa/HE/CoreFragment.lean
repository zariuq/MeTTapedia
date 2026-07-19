import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# HE Core Fragment

Defines the first explicit HE runtime fragment that lands cleanly on the current
`R_exec₀` theorem boundary.

The initial fragment is intentionally narrow:
- only direct authored-rule applications in `mettaHE`
- only no-premise rules
- only `fvar`-headed LHS rules
- only MORK-translatable RHS terms

This is the mathematically honest overlap between the current HE runtime-facing
relation and the already-proved MORK source-rule boundary.

Positive example:
- top-level HE state-machine rule application with no premises and a translatable
  RHS lands on `fireSourceRule`.

Negative example:
- contextual rules are admitted only through explicit premises authored in
  `mettaHE`; collection representation alone grants no closure.
- scheduler priority and sink/update phase distinctions remain execution metadata
  below this theorem boundary.

Audit note:
- The next honest widening is premise-bearing rule application through the
  least authored contextual relation plus a
  `PremiseChain` witness. That widening is theoremically valid and still does
  not require scheduler or sink metadata.
-/

namespace Mettapedia.Languages.MeTTa.HE.CoreFragment

open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.HE.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILBindings := Mettapedia.OSLF.MeTTaIL.Match.Bindings
private abbrev ILRewriteRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILPremise := Mettapedia.OSLF.MeTTaIL.Syntax.Premise
private abbrev ILRelEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv
private abbrev applyPremisesWithEnv := Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv

/-- An HE rule belongs to the current core fragment exactly when:
- its LHS is an `fvar`, matching the current theoremic MORK source bridge
- its RHS lies in the current MORK translatable fragment -/
def heCoreRule (r : ILRewriteRule) : Prop :=
  (∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x) ∧
    morkRuntimeExec0.fragmentPredicate r.right = true

/-- Premise-bearing extension of the HE core rule. The rule shape is still the
same as `heCoreRule`; the only additional requirement is that every premise is
already accepted by the current proved source-rule translation.

At the moment this means `relationQuery` premises only. Freshness is already
classified on the MORK side, but the full HE fragment theorem through guarded
source rules is not packaged yet. -/
def hePremiseCoreRule (r : ILRewriteRule) : Prop :=
  heCoreRule r ∧ allPremisesTranslatable r.premises = true

/-- Future-facing guarded extension of the HE core rule.

This is not the current live HE core fragment. It packages the next honest
theoremic widening: rules whose premises are already accepted by the extended
MORK bridge (`relationQuery` plus `freshness`), while still keeping the runtime
surface at top-level rule application.
-/
def heGuardedPremiseCoreRule (r : ILRewriteRule) : Prop :=
  heCoreRule r ∧ allPremisesTranslatableExt r.premises = true

/-- The first explicit HE runtime core fragment.

This is the maximal low-risk fragment that already aligns with the current
`R_exec₀` proof surface. It deliberately stays at top-level rule application and
does not claim coverage for collection congruence or scheduler-level execution.
-/
inductive HECoreStep : ILPattern → ILPattern → Prop where
  | rule (r : ILRewriteRule) (bs : ILBindings) (p q : ILPattern)
      (hr : r ∈ mettaHE.rewrites)
      (hprem : r.premises = [])
      (hmatch : MatchRel r.left p bs)
      (hq : applyBindings bs r.right = q)
      (hcore : heCoreRule r) :
      HECoreStep p q

/-- Reflexive-transitive closure of the first HE runtime core fragment. -/
abbrev HECoreStepStar := Relation.ReflTransGen HECoreStep

/-- First premise-bearing HE runtime core fragment.

This fragment still stays at top-level rule application, but it moves from the
legacy no-premise reduction surface to the honest premise-aware reduction
surface of the least authored contextual relation.

Positive example:
- `relationQuery`-driven HE top rules can live here and still lower to the
  current source-rule execution boundary.

Negative example:
- contextual collection descent requires an explicit authored rule
- freshness is not yet included in the packaged fragment theorem
-/
inductive HEPremiseCoreStep (relEnv : ILRelEnv) : ILPattern → ILPattern → Prop where
  | rule (r : ILRewriteRule) (bs0 bs : ILBindings) (p q : ILPattern)
      (hr : r ∈ mettaHE.rewrites)
      (hbs0 : bs0 ∈ matchPattern r.left p)
      (hbs : bs ∈ applyPremisesWithEnv relEnv mettaHE r.premises bs0)
      (hq : applyBindings bs r.right = q)
      (hcore : hePremiseCoreRule r) :
      HEPremiseCoreStep relEnv p q

/-- Reflexive-transitive closure of the first premise-bearing HE runtime core
fragment. -/
abbrev HEPremiseCoreStepStar (relEnv : ILRelEnv) :=
  Relation.ReflTransGen (HEPremiseCoreStep relEnv)

@[simp] theorem heCoreRule_fvar {r : ILRewriteRule}
    (h : heCoreRule r) :
    ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x := h.1

@[simp] theorem heCoreRule_translatable {r : ILRewriteRule}
    (h : heCoreRule r) :
    morkRuntimeExec0.fragmentPredicate r.right = true := h.2

@[simp] theorem hePremiseCoreRule_core {r : ILRewriteRule}
    (h : hePremiseCoreRule r) :
    heCoreRule r := h.1

@[simp] theorem hePremiseCoreRule_premises {r : ILRewriteRule}
    (h : hePremiseCoreRule r) :
    allPremisesTranslatable r.premises = true := h.2

@[simp] theorem heGuardedPremiseCoreRule_core {r : ILRewriteRule}
    (h : heGuardedPremiseCoreRule r) :
    heCoreRule r := h.1

@[simp] theorem heGuardedPremiseCoreRule_premises {r : ILRewriteRule}
    (h : heGuardedPremiseCoreRule r) :
    allPremisesTranslatableExt r.premises = true := h.2

private theorem allPremisesTranslatable_implies_ext (premises : List ILPremise)
    (hall : allPremisesTranslatable premises = true) :
    allPremisesTranslatableExt premises = true := by
  simp only [allPremisesTranslatable, allPremisesTranslatableExt, List.all_eq_true] at hall ⊢
  intro prem hprem
  specialize hall prem hprem
  cases prem <;> simp [premiseToSourceFactor, premiseToFactorOrGuard] at hall ⊢

private theorem allPremisesTranslatable_noncontextual
    (premises : List ILPremise)
    (accepted : allPremisesTranslatable premises = true) :
    NoncontextualPremises premises := by
  induction premises with
  | nil => exact .nil
  | cons premise premises ih =>
      simp only [allPremisesTranslatable, List.all_cons, Bool.and_eq_true] at accepted
      cases premise with
      | relationQuery relation arguments =>
          exact .relationQuery (ih accepted.2)
      | _ => simp [premiseToSourceFactor] at accepted

private theorem allPremisesTranslatableExt_noncontextual
    (premises : List ILPremise)
    (accepted : allPremisesTranslatableExt premises = true) :
    NoncontextualPremises premises := by
  induction premises with
  | nil => exact .nil
  | cons premise premises ih =>
      simp only [allPremisesTranslatableExt, List.all_cons, Bool.and_eq_true] at accepted
      cases premise with
      | freshness condition => exact .freshness (ih accepted.2)
      | relationQuery relation arguments => exact .relationQuery (ih accepted.2)
      | _ => simp [premiseToFactorOrGuard] at accepted

/-- RelationQuery-only HE premise-core rules automatically sit inside the
future guarded/source-aware bridge as well. This records that the current HE
premise-core fragment is already compatible with the extended `R_exec₀`
surface, even though no live HE rule currently needs guards. -/
theorem hePremiseCoreRule_to_guarded {r : ILRewriteRule}
    (h : hePremiseCoreRule r) :
    heGuardedPremiseCoreRule r := by
  exact ⟨h.1, allPremisesTranslatable_implies_ext r.premises h.2⟩

/-- The current packaged HE premise-core fragment still translates to no source
guards. This makes precise that relationQuery-only HE premise rules remain
within the guardless `R_exec₀` boundary. -/
@[simp] theorem hePremiseCoreRule_guards_empty {r : ILRewriteRule}
    (h : hePremiseCoreRule r) :
    premisesToSourceGuards r.premises = [] :=
  premisesToSourceGuards_compat r.premises (hePremiseCoreRule_premises h)

/-- For the current packaged HE premise-core fragment, the extended MORK source
rule translation collapses back to the existing guardless one. This is the
formal audit result that no MM2/MORK guard extension is needed for the live HE
premise fragment yet. -/
@[simp] theorem hePremiseCoreRule_extendedTranslation_eq {r : ILRewriteRule}
    (h : hePremiseCoreRule r) :
    rewriteRuleToSourceExecRuleExt r = rewriteRuleToSourceExecRule r := by
  cases r
  simp [rewriteRuleToSourceExecRuleExt, rewriteRuleToSourceExecRule,
    premisesToSourceFactorsExt_compat, premisesToSourceGuards_compat,
    hePremiseCoreRule_premises h]

/-- Every no-premise HE core step belongs to the least authored contextual
relation generated by `mettaHE`. -/
theorem toLanguageStep {p q : ILPattern} (h : HECoreStep p q) :
    Step (engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      mettaHE p q := by
  cases h with
  | rule r bs p q hr hprem hmatch hq _ =>
      have matched : bs ∈
          Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
            mettaHE r p := by
        simpa [mettaHE] using matchRel_complete hmatch
      have premises : bs ∈
          applyPremisesWithEnv
            Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
            mettaHE r.premises bs := by
        simp [hprem, Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
      have target :
          Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
            mettaHE r bs = q := by
        simpa [mettaHE] using hq
      exact step_of_rule hr matched (by rw [hprem]; exact .nil) premises target

/-- Star closure of the no-premise fragment embeds in the authored contextual
relation's star closure. -/
theorem toLanguageStepStar {p q : ILPattern} (h : HECoreStepStar p q) :
    Relation.ReflTransGen
      (Step (engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
        mettaHE) p q := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
      exact Relation.ReflTransGen.tail ih (toLanguageStep hstep)

/-- Every premise-bearing HE core step belongs to the least authored contextual
relation generated by `mettaHE`. -/
theorem premiseCoreToLanguageStep {relEnv : ILRelEnv} {p q : ILPattern}
    (h : HEPremiseCoreStep relEnv p q) :
    Step (engineBasePremises relEnv) mettaHE p q := by
  cases h with
  | rule r bs0 bs p q hr hbs0 hbs hq hcore =>
      apply step_of_rule hr
      · simpa [mettaHE] using hbs0
      · exact allPremisesTranslatable_noncontextual r.premises
          (hePremiseCoreRule_premises hcore)
      · exact hbs
      · simpa [mettaHE] using hq

/-- Star closure of the premise-bearing fragment embeds in the authored
contextual relation's star closure. -/
theorem premiseCoreToLanguageStepStar {relEnv : ILRelEnv} {p q : ILPattern}
    (h : HEPremiseCoreStepStar relEnv p q) :
    Relation.ReflTransGen (Step (engineBasePremises relEnv) mettaHE) p q := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
      exact Relation.ReflTransGen.tail ih (premiseCoreToLanguageStep hstep)

/-- A core-fragment HE rule step lands on the current `R_exec₀`
source-rule firing boundary. -/
theorem rule_toMorkSourceFire
    {r : ILRewriteRule} {bs : ILBindings} {p q : ILPattern}
    (hr : r ∈ mettaHE.rewrites)
    (hprem : r.premises = [])
    (hmatch : MatchRel r.left p bs)
    (hq : applyBindings bs r.right = q)
    (hcore : heCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    {workspace : Mettapedia.Languages.ProcessCalculi.MORK.Space}
    (hp_in : morkPatternToAtom p ∈ workspace) :
    ∃ r_source ∈ morkRuntimeExec0.sourceRuleSetTranslation mettaHE,
      applySinks workspace (morkRuntimeExec0.bindingsTranslation bs) r_source.tmpl ∈
        fireSourceRule workspace r_source := by
  rcases heCoreRule_fvar hcore with ⟨x, hlhs⟩
  have htrans_rhs : morkRuntimeExec0.fragmentPredicate r.right = true :=
    heCoreRule_translatable hcore
  have hmatch_mem : bs ∈ matchPattern r.left p := matchRel_complete hmatch
  refine ⟨morkRuntimeExec0.sourceRuleTranslation r, ?_, ?_⟩
  · show rewriteRuleToSourceExecRule r ∈ languageDefToSourceExecRules mettaHE
    simp only [languageDefToSourceExecRules, List.mem_filterMap]
    refine ⟨r, hr, ?_⟩
    simp [hprem, allPremisesTranslatable, premiseToSourceFactor]
  · simpa [morkRuntimeExec0, MeTTaRuntimeExecSurface.bindingsTranslation,
      MeTTaRuntimeExecSurface.sourceRuleTranslation] using
      (morkRuntimeExec0.noPremiseBridge p q x r
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty mettaHE
        hlhs htrans_rhs hprem bs hmatch_mem hq hground workspace hp_in)

/-- Premise-bearing HE top-level rule application can also land on the current
MORK source-rule firing boundary, provided the premises are already in the
translatable fragment and we have a `PremiseChain` witness linking premise
resolution to workspace atoms.

This theorem is the honest next widening after `HECoreStep`: still one authored rule,
still no scheduler semantics, but now permitting translatable `relationQuery`
premises through the least authored contextual relation.

Freshness is the next plausible extension, but that needs a packaged theorem
through guarded source rules, not the current relationQuery-only bridge.
-/
theorem ruleWithPremises_toMorkSourceFire
    {relEnv : ILRelEnv} {r : ILRewriteRule} {bs0 bs : ILBindings}
    {p q : ILPattern} {workspace : Mettapedia.Languages.ProcessCalculi.MORK.Space}
    {witnesses : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (hr : r ∈ mettaHE.rewrites)
    (hbs0 : bs0 ∈ matchPattern r.left p)
    (_hbs : bs ∈ applyPremisesWithEnv relEnv mettaHE r.premises bs0)
    (hq : applyBindings bs r.right = q)
    (hcore : hePremiseCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hp_in : morkPatternToAtom p ∈ workspace)
    (hchain : PremiseChain relEnv mettaHE workspace bs0 r.premises witnesses bs)
    (hnodup : witnesses.Nodup)
    (hwit_ne_p : ∀ a ∈ witnesses, a ≠ morkPatternToAtom p) :
    ∃ r_source ∈ languageDefToSourceExecRules mettaHE,
      ∃ σ : Subst, applySinks workspace σ r_source.tmpl ∈ fireSourceRule workspace r_source := by
  rcases heCoreRule_fvar (hePremiseCoreRule_core hcore) with ⟨x, hlhs⟩
  have htrans_rhs : morkTranslatable r.right = true :=
    heCoreRule_translatable (hePremiseCoreRule_core hcore)
  have htrans_prem : allPremisesTranslatable r.premises = true :=
    hePremiseCoreRule_premises hcore
  exact ⟨rewriteRuleToSourceExecRule r,
    by
      simp only [languageDefToSourceExecRules, List.mem_filterMap]
      exact ⟨r, hr, by simp [htrans_prem]⟩,
    bindingsToSubst bs,
    matchedRule_multiPremise_fvar_mork_fireSourceRule
      p q x r relEnv mettaHE hlhs htrans_rhs htrans_prem bs0 hbs0 bs hq hground
      workspace hp_in witnesses hchain hnodup hwit_ne_p⟩

/-- Future-facing guarded/source-aware widening of the HE top-rule execution
boundary.

This theorem is not claiming that current HE core execution needs guards. It
packages the next honest extension point above the live relationQuery-only
fragment and below any larger runtime redesign. The additional hypothesis
`hguards` is exactly the existing MORK-side final-substitution guard check.
-/
theorem ruleWithExtPremises_toMorkSourceFire
    {relEnv : ILRelEnv} {r : ILRewriteRule} {bs0 bs : ILBindings}
    {p q : ILPattern} {workspace : Mettapedia.Languages.ProcessCalculi.MORK.Space}
    {witnesses : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (hr : r ∈ mettaHE.rewrites)
    (hbs0 : bs0 ∈ matchPattern r.left p)
    (_hbs : bs ∈ applyPremisesWithEnv relEnv mettaHE r.premises bs0)
    (hq : applyBindings bs r.right = q)
    (hcore : heGuardedPremiseCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hp_in : morkPatternToAtom p ∈ workspace)
    (hchain : PremiseChain relEnv mettaHE workspace bs0 r.premises witnesses bs)
    (hnodup : witnesses.Nodup)
    (hwit_ne_p : ∀ a ∈ witnesses, a ≠ morkPatternToAtom p)
    (hguards : matchSourceGuards (bindingsToSubst bs)
        (premisesToSourceGuards r.premises) = true) :
    ∃ r_source ∈ languageDefToSourceExecRulesExt mettaHE,
      ∃ σ : Subst, applySinks workspace σ r_source.tmpl ∈ fireSourceRule workspace r_source := by
  rcases heCoreRule_fvar (heGuardedPremiseCoreRule_core hcore) with ⟨x, hlhs⟩
  have htrans_rhs : morkTranslatable r.right = true :=
    heCoreRule_translatable (heGuardedPremiseCoreRule_core hcore)
  have htrans_prem : allPremisesTranslatableExt r.premises = true :=
    heGuardedPremiseCoreRule_premises hcore
  exact ⟨rewriteRuleToSourceExecRuleExt r,
    by
      simp only [languageDefToSourceExecRulesExt, List.mem_filterMap]
      exact ⟨r, hr, by simp [htrans_prem]⟩,
    bindingsToSubst bs,
    matchedRule_multiPremise_fvar_mork_fireSourceRuleExt
      p q x r relEnv mettaHE hlhs htrans_rhs htrans_prem bs0 hbs0 bs hq hground
      workspace hp_in witnesses hchain hnodup hwit_ne_p hguards⟩

/-! ## Guarded premise-bearing HE core fragment

The next honest widening after `HEPremiseCoreStep`: rules whose premises are
`relationQuery` or `freshness`, with a final-substitution guard check. The
`hguards` hypothesis matches the MORK-side `matchSourceGuards` pass. -/

/-- Guarded premise-bearing HE core step. Extends `HEPremiseCoreStep` with
    freshness-premise support and a final-substitution guard check. -/
inductive HEGuardedPremiseCoreStep (relEnv : ILRelEnv) : ILPattern → ILPattern → Prop where
  | rule (r : ILRewriteRule) (bs0 bs : ILBindings) (p q : ILPattern)
      (hr : r ∈ mettaHE.rewrites)
      (hbs0 : bs0 ∈ matchPattern r.left p)
      (hbs : bs ∈ applyPremisesWithEnv relEnv mettaHE r.premises bs0)
      (hq : applyBindings bs r.right = q)
      (hcore : heGuardedPremiseCoreRule r)
      (hguards : matchSourceGuards (bindingsToSubst bs)
          (premisesToSourceGuards r.premises) = true) :
      HEGuardedPremiseCoreStep relEnv p q

/-- Reflexive-transitive closure of the guarded premise-bearing HE core fragment. -/
abbrev HEGuardedPremiseCoreStepStar (relEnv : ILRelEnv) :=
  Relation.ReflTransGen (HEGuardedPremiseCoreStep relEnv)

/-- A premise-bearing HE core step (relationQuery only) is also a guarded core step
    (since it has no guards to check). -/
theorem premiseCoreToGuarded {relEnv : ILRelEnv} {p q : ILPattern}
    (h : HEPremiseCoreStep relEnv p q) :
    HEGuardedPremiseCoreStep relEnv p q := by
  cases h with
  | rule r bs0 bs p q hr hbs0 hbs hq hcore =>
    exact .rule r bs0 bs p q hr hbs0 hbs hq
      (hePremiseCoreRule_to_guarded hcore)
      (by simp [hePremiseCoreRule_guards_empty hcore, matchSourceGuards, List.all_nil])

/-- The guarded HE core fragment embeds in the least authored contextual
relation. -/
theorem guardedCoreToLanguageStep {relEnv : ILRelEnv} {p q : ILPattern}
    (h : HEGuardedPremiseCoreStep relEnv p q) :
    Step (engineBasePremises relEnv) mettaHE p q := by
  cases h with
  | rule r bs0 bs p q hr hbs0 hbs hq hcore _ =>
      apply step_of_rule hr
      · simpa [mettaHE] using hbs0
      · exact allPremisesTranslatableExt_noncontextual r.premises
          (heGuardedPremiseCoreRule_premises hcore)
      · exact hbs
      · simpa [mettaHE] using hq

/-- Star closure of guarded core steps embeds in the authored contextual
relation's star closure. -/
theorem guardedCoreToLanguageStepStar {relEnv : ILRelEnv} {p q : ILPattern}
    (h : HEGuardedPremiseCoreStepStar relEnv p q) :
    Relation.ReflTransGen (Step (engineBasePremises relEnv) mettaHE) p q := by
  induction h with
  | refl => exact .refl
  | tail hrest hstep ih =>
    exact Relation.ReflTransGen.tail ih (guardedCoreToLanguageStep hstep)

/-- Star closure of premise-bearing core forgets to star closure of guarded core. -/
theorem premiseCoreStarToGuardedStar {relEnv : ILRelEnv} {p q : ILPattern}
    (h : HEPremiseCoreStepStar relEnv p q) :
    HEGuardedPremiseCoreStepStar relEnv p q := by
  induction h with
  | refl => exact .refl
  | tail hrest hstep ih =>
    exact Relation.ReflTransGen.tail ih (premiseCoreToGuarded hstep)

/-! ## End-to-end chain: HE → computable execution

Composes the spec-level bridge (`ruleWithPremises_toMorkSourceFire`) with
the backward completeness theorem (`fireSourceRule_toFinset_complete`) to
obtain a computable `cfireSourceRule` witness from an HE premise-core step. -/

open Mettapedia.Languages.ProcessCalculi.MORK.Conformance
  Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable in
/-- End-to-end: HE premise-core step → computable `cfireSourceRule` witness.

    Given an HE rewrite rule application with premises (all `relationQuery`),
    a computable workspace (as `List Atom`), and a `PremiseChain` linking
    premise resolution to workspace atoms, there exists a source rule whose
    computable firing produces a space that agrees with the spec-level firing.

    This composes:
    1. `ruleWithPremises_toMorkSourceFire` (HE step → spec `fireSourceRule`)
    2. `fireSourceRule_toFinset_complete` (spec → computable `cfireSourceRule`) -/
theorem hePremiseCoreStep_to_computableFire
    {relEnv : ILRelEnv} {r : ILRewriteRule} {bs0 bs : ILBindings}
    {p q : ILPattern}
    (hr : r ∈ mettaHE.rewrites)
    (hbs0 : bs0 ∈ matchPattern r.left p)
    (_hbs : bs ∈ applyPremisesWithEnv relEnv mettaHE r.premises bs0)
    (hq : applyBindings bs r.right = q)
    (hcore : hePremiseCoreRule r)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    -- Workspace as a computable list
    (workspace : CSpace) (hnodup : workspace.Nodup)
    (hp_in : morkPatternToAtom p ∈ workspace)
    -- Premise witness chain
    (witnesses : List Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (hchain : PremiseChain relEnv mettaHE workspace.toFinset bs0 r.premises witnesses bs)
    (hnodup_wit : witnesses.Nodup)
    (hwit_ne_p : ∀ a ∈ witnesses, a ≠ morkPatternToAtom p)
    -- NodupSafe for computable sink application
    (hsafe : ∀ σ : Subst, NodupSafe workspace σ
        (rewriteRuleToSourceExecRule r).tmpl.sinks) :
    ∃ r_source ∈ languageDefToSourceExecRules mettaHE,
      ∃ cs' ∈ cfireSourceRule workspace r_source,
        cs'.toFinset ∈ fireSourceRule workspace.toFinset r_source := by
  -- The source rule is deterministically rewriteRuleToSourceExecRule r
  set r_source := rewriteRuleToSourceExecRule r
  -- Membership in source rule set
  have hr_mem : r_source ∈ languageDefToSourceExecRules mettaHE := by
    simp only [r_source, languageDefToSourceExecRules, List.mem_filterMap]
    exact ⟨r, hr, by simp [hePremiseCoreRule_premises hcore]⟩
  -- Spec-level fire: reuse the per-rule bridge directly
  have hfire : ∃ σ : Subst, applySinks workspace.toFinset σ r_source.tmpl ∈
      fireSourceRule workspace.toFinset r_source := by
    rcases heCoreRule_fvar (hePremiseCoreRule_core hcore) with ⟨x, hlhs⟩
    exact ⟨bindingsToSubst bs,
      matchedRule_multiPremise_fvar_mork_fireSourceRule
        p q x r relEnv mettaHE hlhs
        (heCoreRule_translatable (hePremiseCoreRule_core hcore))
        (hePremiseCoreRule_premises hcore) bs0 hbs0 bs hq hground
        workspace.toFinset (List.mem_toFinset.mpr hp_in)
        witnesses hchain hnodup_wit hwit_ne_p⟩
  obtain ⟨σ, hfire_mem⟩ := hfire
  -- Backward completeness: spec → computable
  obtain ⟨cs', hcs'_mem, hcs'_eq⟩ :=
    fireSourceRule_toFinset_complete workspace r_source hnodup
      (applySinks workspace.toFinset σ r_source.tmpl) hfire_mem hsafe
  exact ⟨r_source, hr_mem, cs', hcs'_mem, hcs'_eq ▸ hfire_mem⟩

end Mettapedia.Languages.MeTTa.HE.CoreFragment
