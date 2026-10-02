import Mettapedia.GSLT.LanguageDef.ReactiveContexts
import Mettapedia.GSLT.LanguageDef.Interaction.Strength

/-!
# The events available now

A splitting of a term is a context and a subterm that plug together to the
term.  The splitting exposes a redex when its subterm matches the left side
of some base rewrite.  It is an available event when, in addition, the base
rewrite can be applied there and the context is one in which rewrites fire.

The second condition is not decoration.  A redex beneath a context in which
no rewrite fires matches a base rewrite and is not a direction in which the
state can move.

Three facts are proved for every language whose rules are base rewrites or
congruences.

* The available events of a state are exactly the directions in which it can
  move: the state reduces to `next` precisely when some available event has
  `next` as its result.
* When every base rewrite is headed by a member of a family of constructors,
  the subterm of every splitting that exposes a redex is headed by a member
  of the family; every other cut of the term is inert.
* The same context plugged with different subterms gives different terms: a
  context alone does not locate anything.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## Splittings -/

/-- A splitting of a term: a context and a subterm that plug to it. -/
structure Splitting (term : Pattern) where
  context : OneHoleContext
  subterm : Pattern
  plugs : context.fill subterm = term

namespace Splitting

/-- The splitting at the root: the whole term beneath the empty context. -/
def root (term : Pattern) : Splitting term where
  context := .hole
  subterm := term
  plugs := rfl

/-- A splitting selects an occurrence of its subterm. -/
theorem selects {term : Pattern} (splitting : Splitting term) :
    Selects splitting.subterm splitting.context term := by
  have selected := Selects.of_fill splitting.context splitting.subterm
  rwa [splitting.plugs] at selected

/-- The splittings of a term with a given subterm are found by the zipper
enumeration: the fibre of plugging over a term is finite and computed. -/
theorem context_mem_zippersAt {term : Pattern} (splitting : Splitting term) :
    splitting.context ∈ zippersAt splitting.subterm term :=
  mem_zippersAt_iff_selects.mpr splitting.selects

/-- Every zipper of a term is the context of a splitting of it. -/
def ofZipper {term needle : Pattern} {context : OneHoleContext}
    (membership : context ∈ zippersAt needle term) : Splitting term where
  context := context
  subterm := needle
  plugs := (mem_zippersAt_iff_selects.mp membership).fill_eq

end Splitting

/-- **A context is a shape, not a place.**  Plugging is injective in the
subterm, so one context around two different subterms gives two different
terms: the context alone does not say which term it is a part of. -/
theorem fill_injective : ∀ context : OneHoleContext, Function.Injective context.fill
  | .hole => fun _ _ same => same
  | .apply _ before inner _ => fun _ _ same => by
      simp only [OneHoleContext.fill, Pattern.apply.injEq, true_and] at same
      exact fill_injective inner (List.cons.inj (List.append_cancel_left same)).1
  | .lambda _ inner => fun _ _ same => by
      simp only [OneHoleContext.fill, Pattern.lambda.injEq, true_and] at same
      exact fill_injective inner same
  | .multiLambda _ _ inner => fun _ _ same => by
      simp only [OneHoleContext.fill, Pattern.multiLambda.injEq, true_and] at same
      exact fill_injective inner same
  | .substBody inner _ => fun _ _ same => by
      simp only [OneHoleContext.fill, Pattern.subst.injEq, and_true] at same
      exact fill_injective inner same
  | .substReplacement _ inner => fun _ _ same => by
      simp only [OneHoleContext.fill, Pattern.subst.injEq, true_and] at same
      exact fill_injective inner same
  | .collection _ before inner _ _ => fun _ _ same => by
      simp only [OneHoleContext.fill, Pattern.collection.injEq, true_and, and_true] at same
      exact fill_injective inner (List.cons.inj (List.append_cancel_left same)).1

/-! ## Exposed redexes and available events -/

/-- The subterm side exposes a redex: it matches the left side of a base
rewrite. -/
def Splitting.ExposesRedex (language : LanguageDef) {term : Pattern}
    (splitting : Splitting term) : Prop :=
  ∃ rule ∈ language.rewrites, IsBaseRewrite rule ∧
    ∃ bindings, bindings ∈ matchPatternForRule language rule splitting.subterm

/-- **An available event.**  The subterm is contracted by a base rewrite
whose side conditions hold, and the context is one in which rewrites fire. -/
def Splitting.Fires (relEnv : RelationEnv) (language : LanguageDef) {term : Pattern}
    (splitting : Splitting term) : Prop :=
  (∃ residual, Reactive language splitting.context residual) ∧
    ∃ reduct, BaseStep relEnv language splitting.subterm reduct

/-- An available event with its result: the reduct returned in the context
that the reactive context pairs with it. -/
def Splitting.FiresTo (relEnv : RelationEnv) (language : LanguageDef) {term : Pattern}
    (splitting : Splitting term) (next : Pattern) : Prop :=
  ∃ residual reduct, Reactive language splitting.context residual ∧
    BaseStep relEnv language splitting.subterm reduct ∧ residual.fill reduct = next

/-- An available event exposes a redex. -/
theorem Splitting.exposesRedex_of_fires {relEnv : RelationEnv} {language : LanguageDef}
    {term : Pattern} {splitting : Splitting term} (fires : splitting.Fires relEnv language) :
    splitting.ExposesRedex language := by
  obtain ⟨-, reduct, rule, listed, base, initial, matched, -⟩ := fires
  exact ⟨rule, listed, base, initial, matched⟩

/-- An available event has a result. -/
theorem Splitting.fires_iff_exists_firesTo {relEnv : RelationEnv} {language : LanguageDef}
    {term : Pattern} {splitting : Splitting term} :
    splitting.Fires relEnv language ↔ ∃ next, splitting.FiresTo relEnv language next := by
  constructor
  · rintro ⟨⟨residual, reactive⟩, reduct, contraction⟩
    exact ⟨residual.fill reduct, residual, reduct, reactive, contraction, rfl⟩
  · rintro ⟨next, residual, reduct, reactive, contraction, -⟩
    exact ⟨⟨residual, reactive⟩, reduct, contraction⟩

/-- **An available event is a direction in which the state can move.** -/
theorem Splitting.step_of_firesTo {relEnv : RelationEnv} {language : LanguageDef}
    {term next : Pattern} {splitting : Splitting term}
    (fires : splitting.FiresTo relEnv language next) :
    Step (engineBasePremises relEnv) language term next := by
  obtain ⟨residual, reduct, reactive, contraction, rfl⟩ := fires
  have stepped := reactive.step contraction.step
  rwa [splitting.plugs] at stepped

/-- **The directions in which a state can move are its available events.**
The statement restates the decomposition of a reduction through the bundle
of events: the state reduces to `next` exactly when one of its splittings
fires with result `next`. -/
theorem step_iff_exists_firesTo {relEnv : RelationEnv} {language : LanguageDef}
    (rules : FiresInContexts language) {state next : Pattern} :
    Step (engineBasePremises relEnv) language state next ↔
      ∃ splitting : Splitting state, splitting.FiresTo relEnv language next := by
  constructor
  · intro step
    obtain ⟨context, residual, redex, reduct, reactive, plugs, lands, contraction⟩ :=
      (step_iff_baseStep_in_context rules).mp step
    exact ⟨⟨context, redex, plugs⟩, residual, reduct, reactive, contraction, lands⟩
  · rintro ⟨splitting, fires⟩
    exact splitting.step_of_firesTo fires

/-- A state can move exactly when one of its cuts is an available event. -/
theorem exists_step_iff_exists_fires {relEnv : RelationEnv} {language : LanguageDef}
    (rules : FiresInContexts language) {state : Pattern} :
    (∃ next, Step (engineBasePremises relEnv) language state next) ↔
      ∃ splitting : Splitting state, splitting.Fires relEnv language := by
  constructor
  · rintro ⟨next, step⟩
    obtain ⟨splitting, fires⟩ := (step_iff_exists_firesTo rules).mp step
    exact ⟨splitting, Splitting.fires_iff_exists_firesTo.mpr ⟨next, fires⟩⟩
  · rintro ⟨splitting, fires⟩
    obtain ⟨next, firesTo⟩ := Splitting.fires_iff_exists_firesTo.mp fires
    exact ⟨next, splitting.step_of_firesTo firesTo⟩

/-! ## Base contractions of premise-free rules -/

/-- A premise-free rule contracts whatever its left side matches. -/
theorem BaseStep.of_match {relEnv : RelationEnv} {language : LanguageDef}
    {rule : RewriteRule} {redex reduct : Pattern} (listed : rule ∈ language.rewrites)
    (premiseFree : rule.premises = []) (aligned : ruleDepthAligned rule = true)
    (matched : ∃ bindings ∈ matchPattern rule.left redex,
      applyBindings bindings rule.right = reduct) :
    BaseStep relEnv language redex reduct := by
  obtain ⟨bindings, membership, applied⟩ := matched
  refine ⟨rule, listed, isBaseRewrite_of_premises_eq_nil premiseFree, bindings,
    by simpa using membership, bindings, ?_, ?_⟩
  · rw [premiseFree]
    simp [applyPremisesWithEnv]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ aligned]
    exact applied

/-- A term that no rule's left side matches has no base contraction. -/
theorem not_baseStep_of_no_match {relEnv : RelationEnv} {language : LanguageDef}
    {redex : Pattern}
    (unmatched : ∀ rule ∈ language.rewrites, matchPattern rule.left redex = [])
    (reduct : Pattern) : ¬ BaseStep relEnv language redex reduct := by
  rintro ⟨rule, listed, -, initial, matched, -⟩
  have membership : initial ∈ matchPattern rule.left redex := by simpa using matched
  rw [unmatched rule listed] at membership
  cases membership

/-- In a language with no congruence rule, rewrites fire only at the root. -/
theorem Reactive.eq_hole_of_base {language : LanguageDef}
    (base : ∀ rule ∈ language.rewrites, IsBaseRewrite rule)
    {context residual : OneHoleContext} (reactive : Reactive language context residual) :
    context = .hole ∧ residual = .hole := by
  cases reactive with
  | hole => exact ⟨rfl, rfl⟩
  | argument _ _ listed congruence =>
      exact absurd (base _ listed)
        (not_isBaseRewrite_of_congruence
          (congruence.premises ▸ List.mem_singleton.mpr rfl))
  | element _ _ _ listed congruence =>
      exact absurd (base _ listed)
        (not_isBaseRewrite_of_congruence
          (congruence.premises ▸ List.mem_singleton.mpr rfl))

/-! ## Available events sit at the distinguished family -/

/-- A term matched by a headed schema has the same head. -/
theorem patternHead?_of_match {schema term : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern schema term) {head : PatternHead}
    (headed : patternHead? schema = some head) : patternHead? term = some head := by
  have relation := matchPattern_sound matched
  cases relation with
  | fvar => cases headed
  | bvar => cases headed
  | apply _ _ => exact headed
  | lambda _ => cases headed
  | multiLambda _ => cases headed
  | collection _ _ => exact headed
  | vector _ => exact headed
  | vectorRest _ _ => exact headed
  | subst _ _ _ => cases headed

/-- **Exposed redexes sit at the family.**  When every base rewrite is headed
by a member of a family, the subterm of a splitting that exposes a redex is
headed by a member of the family. -/
theorem Splitting.headed_of_exposesRedex {language : LanguageDef}
    {family : List PatternHead} (headed : BaseRewritesHeadedBy language family)
    {term : Pattern} {splitting : Splitting term}
    (exposes : splitting.ExposesRedex language) :
    ∃ head ∈ family, patternHead? splitting.subterm = some head := by
  obtain ⟨rule, listed, base, bindings, matched⟩ := exposes
  obtain ⟨head, inFamily, ruleHead⟩ := headed rule listed base
  rw [matchPatternForRule_eq_syntactic] at matched
  exact ⟨head, inFamily, patternHead?_of_match matched ruleHead⟩

/-- **Every other cut is inert.**  A splitting whose subterm is not headed by
the family exposes no redex, and is therefore not an available event. -/
theorem Splitting.not_fires_of_head {relEnv : RelationEnv} {language : LanguageDef}
    {family : List PatternHead} (headed : BaseRewritesHeadedBy language family)
    {term : Pattern} (splitting : Splitting term)
    (other : ∀ head ∈ family, patternHead? splitting.subterm ≠ some head) :
    ¬ splitting.Fires relEnv language := by
  intro fires
  obtain ⟨head, inFamily, same⟩ :=
    Splitting.headed_of_exposesRedex headed (Splitting.exposesRedex_of_fires fires)
  exact other head inFamily same

end Mettapedia.GSLT.LanguageDef
