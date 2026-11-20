import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsStages

/-!
# Curried DTL derivations and the forward closure of one application rule

At a fixed caller interpretation, a shared row supplies its one reading and a
schematic row supplies its independently instantiated readings. DTL derivations
are built from these hypotheses and binary typed application, retaining the
object-level proof term. The target is the existing least simultaneous closure
of the application instances, not a second proof interpreter.

The seed's reading set can be infinite even when its stored representation is
finite. Finitary derivability still coincides with that least closure. This is
the logical closure result; an actual held-row run correspondence is a separate
operational obligation. Source-anchored or depth-bounded search APIs do not
become equal to exhaustive closure merely by using this application rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics

open Mettapedia.Logic.LP
open Mettapedia.GSLT.OpenEnded
open OneFrame (Terms frames)
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open StepWeb.KernelRounds

abbrev X := frames (FirstOrder.action rowSig)
abbrev Data := List (Row (Terms Tm) PUnit.unit)

def hypotheses (data : Data) (source : Subst rowSig) : Set Tm :=
  {value | ∃ row ∈ data, Row.ReadsAt X (b := PUnit.unit) source value row}

inductive Derives (judgmentTag arrowTag : Nat) (data : Data) (source : Subst rowSig) : Tm → Prop
  | hypothesis {value : Tm} (assumed : value ∈ hypotheses data source) : Derives judgmentTag arrowTag data source value
  | apply {function argument domain codomain : Tm}
      (major : Derives judgmentTag arrowTag data source (judgment judgmentTag function (arrow arrowTag domain codomain)))
      (minor : Derives judgmentTag arrowTag data source (judgment judgmentTag argument domain)) :
      Derives judgmentTag arrowTag data source (judgment judgmentTag (app function argument) codomain)

structure Application where
  function : Tm
  argument : Tm
  domain : Tm
  codomain : Tm

def consequence (judgmentTag arrowTag : Nat) (application : Application) : SetStoreClosure.Instance Tm :=
  ⟨{judgment judgmentTag application.function (arrow arrowTag application.domain application.codomain),
      judgment judgmentTag application.argument application.domain},
    {judgment judgmentTag (app application.function application.argument) application.codomain}⟩

def forwardClosure (judgmentTag arrowTag : Nat) (data : Data) (source : Subst rowSig) : Set Tm :=
  ChaoticIteration.target (fun application => SetStoreClosure.action (consequence judgmentTag arrowTag application))
    (hypotheses data source)

theorem stage_sound (judgmentTag arrowTag : Nat) (data : Data) (source : Subst rowSig) :
    ∀ n value, value ∈ stage (consequence judgmentTag arrowTag) (hypotheses data source) n →
      Derives judgmentTag arrowTag data source value := by
  intro n
  induction n with
  | zero => intro value member; exact .hypothesis member
  | succ n ih =>
    intro value member
    rcases member with old | ⟨application, enabled, made⟩
    · exact ih value old
    · have same : value = judgment judgmentTag (app application.function application.argument) application.codomain :=
        Finset.mem_singleton.mp made
      subst value
      exact .apply (domain := application.domain) (ih _ (enabled _ (by simp [consequence])))
        (ih _ (enabled _ (by simp [consequence])))

theorem derivation_in_finite_stages (judgmentTag arrowTag : Nat) (data : Data) (source : Subst rowSig)
    {value : Tm} (derivation : Derives judgmentTag arrowTag data source value) :
    value ∈ finiteProofs (consequence judgmentTag arrowTag) (hypotheses data source) := by
  induction derivation with
  | hypothesis assumed => exact ⟨0, assumed⟩
  | @apply function argument domain codomain _ _ major minor =>
    apply finiteProofs_closed (consequence judgmentTag arrowTag) (hypotheses data source)
      (⟨function, argument, domain, codomain⟩ : Application)
    · intro premise member
      simp only [consequence, Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact major
      · exact minor
    · simp [consequence]

theorem forward_closure_iff_derives (judgmentTag arrowTag : Nat) (data : Data) (source : Subst rowSig)
    (value : Tm) : value ∈ forwardClosure judgmentTag arrowTag data source ↔
      Derives judgmentTag arrowTag data source value := by
  change value ∈ ChaoticIteration.target
    (fun application => SetStoreClosure.action (consequence judgmentTag arrowTag application))
    (hypotheses data source) ↔ _
  rw [← finiteProofs_eq_target]
  constructor
  · rintro ⟨n, member⟩
    exact stage_sound judgmentTag arrowTag data source n value member
  · exact derivation_in_finite_stages judgmentTag arrowTag data source

#print axioms stage_sound
#print axioms derivation_in_finite_stages
#print axioms forward_closure_iff_derives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics
