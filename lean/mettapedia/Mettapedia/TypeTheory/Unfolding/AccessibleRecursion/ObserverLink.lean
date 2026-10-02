import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Checker
import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity

/-!
# Carved equality as an observer-relative equivalence

Terms of one type over one data context form a presentation with syntactic
identity as its equations and no reduction (`carvedTermGSLT`).  An observer is
an operation on such terms; the *beta-respecting* observers
(`BetaRespecting`) send beta-convertible terms to beta-convertible terms.  The
base observation reads the beta normal form (`normalFormObservations`), the
readout the carved checker computes.

* **Positive.**  For every admissible class of beta-respecting observers, the
  saturated relative equivalence of the normal-form readout is exactly carved
  definitional equality (`relEquiv_normalForm_iff`).  The equivalence does not
  depend on which beta-respecting observers are admitted.
* **Negative.**  An observer that reads syntax separates a beta redex from its
  reduct (`syntactic_observer_separates`), so the relative equivalence of the
  class of all observers is strictly finer than carved definitional equality:
  the collapse to syntax that code-reading observers cause.
* **Propositional equality is coarser.**  The positive control's recursor
  application and its unfolding are propositionally equal in the carved
  variant but not related by the normal-form equivalence
  (`propositional_not_normalForm`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

variable {A P : Ty}

variable (A P) in
/-- Terms of one type over one data context, with syntactic identity as
equations and no reduction. -/
abbrev carvedTermGSLT (Γ : List Ty) (T : Ty) : GSLT where
  Term := Tm A P Γ T
  equations := ⟨Eq, eq_equivalence⟩
  rewrites _ _ := False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

variable (A P) in
/-- An observer that sends beta-convertible terms to beta-convertible terms. -/
structure BetaRespecting (Γ : List Ty) (T : Ty) where
  apply : Tm A P Γ T → Tm A P Γ T
  respects : ∀ {left right : Tm A P Γ T}, BetaConv left right → BetaConv (apply left) (apply right)

variable (A P) in
/-- Beta-respecting observers, composed as functions. -/
abbrev betaRespectingRules (Γ : List Ty) (T : Ty) : ContextualRules (carvedTermGSLT A P Γ T) where
  Context := BetaRespecting A P Γ T
  identity := ⟨id, id⟩
  compose outer inner := ⟨outer.apply ∘ inner.apply, fun convertible =>
    outer.respects (inner.respects convertible)⟩
  plug context term := context.apply term
  plug_identity _ := rfl
  plug_compose _ _ _ := rfl
  plug_resp context := fun same => congrArg context.apply same
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

variable (A P) in
/-- The normal-form readout: an atom is a term, observed of a term whose beta
normal form it is. -/
abbrev normalFormObservations (Γ : List Ty) (T : Ty) :
    ContextualRules.Observations.{0} (carvedTermGSLT A P Γ T) where
  Atom := Tm A P Γ T
  observes normal term := (Normalization.normalize term).normalForm = normal
  observes_resp _ _ _ same := by
    change _ = _ at same
    subst same
    exact Iff.rfl

/-- **Carved definitional equality is the relative equivalence of the
normal-form readout**, for every admissible class of beta-respecting
observers. -/
theorem relEquiv_normalForm_iff {Γ : List Ty} {hyps : List (Tm A P Γ prop)} {T : Ty}
    (admissible : AdmissibleClass (betaRespectingRules A P Γ T)) (left right : Tm A P Γ T) :
    admissible.RelEquiv (normalFormObservations A P Γ T) left right ↔
      Carved A P (.conv Γ hyps T left right) := by
  rw [carved_conv_iff]
  constructor
  · intro related
    have agree := (admissible.isReductionBisimulation_relEquiv
      (normalFormObservations A P Γ T)).2 related (Normalization.normalize left).normalForm
    have normalForms : (Normalization.normalize right).normalForm =
        (Normalization.normalize left).normalForm := agree.mp rfl
    exact (ConversionDecision.normalize_eq_iff_betaConv left right).mp normalForms.symm
  · intro convertible
    refine admissible.relEquiv_of_isReductionBisimulation (normalFormObservations A P Γ T)
      (relation := fun first second => BetaConv first second) ?_ ?_ convertible
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro _ _ _ _ impossible
        exact impossible.elim
      · intro _ _ _ _ impossible
        exact impossible.elim
      · intro first second related normal
        change (Normalization.normalize first).normalForm = normal ↔
          (Normalization.normalize second).normalForm = normal
        rw [(ConversionDecision.normalize_eq_iff_betaConv first second).mpr related]
    · intro context _ _ _ related
      exact context.respects related

/-! ## Syntactic observers collapse the equivalence -/

variable (A P) in
/-- All operations on terms, including those that read syntax. -/
abbrev syntacticRules (Γ : List Ty) (T : Ty) : ContextualRules (carvedTermGSLT A P Γ T) where
  Context := Tm A P Γ T → Tm A P Γ T
  identity := id
  compose outer inner := outer ∘ inner
  plug context term := context term
  plug_identity _ := rfl
  plug_compose _ _ _ := rfl
  plug_resp context := fun same => congrArg context same
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

variable (A P) in
/-- The class of all observers. -/
def allObservers (Γ : List Ty) (T : Ty) : AdmissibleClass (syntacticRules A P Γ T) where
  Admissible _ := True
  identity_mem := trivial
  compose_mem _ _ := trivial

/-- The normal-form readout, for the syntactic observers. -/
abbrev syntacticNormalForms (Γ : List Ty) (T : Ty) :
    ContextualRules.Observations.{0} (carvedTermGSLT A P Γ T) :=
  normalFormObservations A P Γ T

/-- The redex `(λp. p) q` over a proposition variable `q`. -/
def identityRedex : Tm A P [prop] prop := .app (.lam (.var .zero)) (.var .zero)

/-- **A syntactic observer separates a beta redex from its reduct**, although
they are carved-convertible. -/
theorem syntactic_observer_separates :
    Carved A P (.conv [prop] [] prop identityRedex (.var .zero)) ∧
      ¬ (allObservers A P [prop] prop).RelEquiv (syntacticNormalForms [prop] prop)
        identityRedex (.var .zero) := by
  refine ⟨carved_conv_iff.mpr (.rel _ _ (BetaStep.beta (.var .zero) (.var .zero))), ?_⟩
  intro related
  let reader : Tm A P [prop] prop → Tm A P [prop] prop :=
    fun term => if term = identityRedex then falsum else .var .zero
  have agree := AdmissibleContextCongruence.bisimilar_observes related
    ((Normalization.normalize (reader identityRedex)).normalForm,
      (⟨reader, trivial⟩ : {context : (syntacticRules A P [prop] prop).Context //
        (allObservers A P [prop] prop).Admissible context}))
  have normalForms : (Normalization.normalize (reader (.var .zero))).normalForm =
      (Normalization.normalize (reader identityRedex)).normalForm := agree.mp rfl
  have readerRedex : reader identityRedex = falsum := if_pos rfl
  have readerVariable : reader (.var .zero) = .var .zero := if_neg (by
    intro same
    cases same)
  rw [readerRedex, readerVariable] at normalForms
  have convertible : BetaConv (Term.var Var.zero : Tm A P [prop] prop) falsum :=
    (ConversionDecision.normalize_eq_iff_betaConv _ _).mp normalForms
  let environment : Environment Prop ([prop] ++ signature A P) :=
    Environment.extend (A := prop) True (sigEnvironmentAt (fun _ _ _ => Val.default P))
  have standard : Standard (Γ := [prop]) (fun _ _ _ => Val.default P) environment :=
    Standard.extend (sigEnvironment_standard _) (B := prop) True
  have denotations := BetaConv.denote convertible environment
  change True = (falsum : Tm A P [prop] prop).denote environment at denotations
  rw [denote_falsum standard] at denotations
  have everything : ∀ p : Prop, p := denotations ▸ trivial
  exact everything False

/-! ## Propositional equality is coarser -/

/-- **Carved propositional equality is strictly coarser than the normal-form
equivalence**: the positive control's recursor application equals its
unfolding propositionally, but no class of beta-respecting observers relates
them. -/
theorem propositional_not_normalForm
    (admissible : AdmissibleClass (betaRespectingRules A P (positiveContext A P) P)) :
    Carved A P (.equal (positiveContext A P) positiveHyps P positiveRec positiveUnfold) ∧
      ¬ admissible.RelEquiv (normalFormObservations A P (positiveContext A P) P)
        positiveRec positiveUnfold :=
  ⟨positive_carved_equal, fun related =>
    positive_carved_not_conv ((relEquiv_normalForm_iff (hyps := positiveHyps) admissible _ _).mp
      related)⟩

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
