import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Separation

/-!
# Control: homomorphism modulo equations is satisfiable on a presentation

The criterion asks homomorphism up to the target's equations. On a presentation that has a parallel
context rule and the authored equation `Idem` (`{P, P} = P`), the constant translation to the
success term `ω` is homomorphic modulo equations and preserves reachable success, and it does not
reflect it at the blocked composite (`constant_into_idempotent`). So the hypotheses of
`no_uniformTranslation_presentation` other than reflection can all hold on a presentation target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PresentationControl

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv EquationInstance
  EquationInstanceAt equationInstance_equivalent readsRaw_of_none)

/-- The authored equation `{P, P} = P`. -/
def idem : Mettapedia.OSLF.MeTTaIL.Syntax.Equation where
  name := "Idem"
  typeContext := []
  premises := []
  left := .collection .hashBag [.fvar "P", .fvar "P"] none
  right := .fvar "P"

/-- A presentation with a parallel context rule and the equation `Idem`. -/
def idempotent : LanguageDef :=
  { ParallelClosed.Controls.withContext with equations := [idem] }

theorem idempotent_hasParallelContextRule : HasParallelContextRule .hashBag idempotent :=
  ⟨rhoParCongRewrite, by simp [idempotent, ParallelClosed.Controls.withContext],
    "S", "T", "rest", by decide, by decide, by decide, rfl, rfl, rfl⟩

/-- **`t` beside itself is `t`, modulo the equations.** -/
theorem beside_self_equiv (base : BasePremiseEvaluator) (t : Pattern) :
    EquationEquiv base idempotent (beside .hashBag t t) t := by
  have matched : [("P", t)] ∈ matchPattern idem.left (beside .hashBag t t) := by
    apply matchPattern_iff_matchRel.mpr
    show MatchRel (.collection .hashBag [.fvar "P", .fvar "P"] none)
      (.collection .hashBag [t, t] none) [("P", t)]
    have inner : MatchBagRel [.fvar "P"] none .hashBag [t] [("P", t)] :=
      .cons 0 (by simp) .fvar .nilNoRest (by simp [mergeBindings])
    exact MatchRel.collection (by decide) (.cons 0 (by simp) .fvar inner (by simp [mergeBindings]))
  have instance_ : EquationInstance base idempotent (beside .hashBag t t) t :=
    ⟨0, .forward (List.Mem.head []) (readsRaw_of_none rfl) matched (.nil _)
      (by simp [applyBindings, idem])⟩
  exact equationInstance_equivalent instance_

/-- **Homomorphic modulo equations and preserving, not reflecting**, into a presentation with a
parallel context rule: the constant translation to `ω`. -/
theorem constant_into_idempotent (base : BasePremiseEvaluator) (ω : Pattern) :
    (presentationCalculus base idempotent .hashBag ω).Persistent ∧
      (∀ s s', source.composable s s' →
        EquationEquiv base idempotent ω (beside .hashBag ω ω)) ∧
      (∀ s, source.Succeeds s → (presentationCalculus base idempotent .hashBag ω).Succeeds ω) ∧
      ¬ ∀ s, (presentationCalculus base idempotent .hashBag ω).Succeeds ω → source.Succeeds s := by
  have shows : (presentationCalculus base idempotent .hashBag ω).Succeeds ω :=
    ParallelCalculus.succeeds_of_success _
      ⟨ω, (Mettapedia.GSLT.LanguageDef.EquationSemantics.equationSetoid base idempotent).iseqv.refl ω,
        .here⟩
  exact ⟨presentationCalculus_persistent idempotent_hasParallelContextRule ω,
    fun _ _ _ => (Mettapedia.GSLT.LanguageDef.EquationSemantics.equationSetoid base
      idempotent).iseqv.symm (beside_self_equiv base ω),
    fun _ _ => shows,
    fun reflects => beside_blocked (reflects _ shows)⟩

#print axioms idempotent_hasParallelContextRule
#print axioms beside_self_equiv
#print axioms constant_into_idempotent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PresentationControl
