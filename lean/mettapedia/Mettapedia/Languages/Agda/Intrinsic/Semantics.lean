import Mettapedia.Languages.Agda.Intrinsic.Completeness
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPresheaf
import Mettapedia.OSLF.Syntax.EventGraphModalTransport

/-!
# Presheaf events and OSLF of the structural Agda terms

The binding signature determines the term clone and its substitution category.
The authored rules determine an event presheaf in that category. Its endpoint
image, compared here to the independent compatible reduction, supplies OSLF
modalities on program terms. These are not modalities on checker search states.

This constructs the presheaf interpretation and its free rule-tree model. It
does not assert the stronger universal property of a combined classifying
category, nor identify behavioral predicates with Agda's typing judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Semantics

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Authored


/-- Substitution contexts, with their variance made explicit. -/
def context (Γ : Ctx sig) : IntrinsicScopedConditionalPresheaf.Base algebra :=
  Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
    algebra.substitution.toClone Γ)

/-- The actual representable program object, not a constant presheaf. -/
def programs := IntrinsicScopedConditionalPresheaf.programs algebra .term

/-- Programs as represented substitutions agree naturally with scoped terms. -/
def representedPrograms : programs ≅ IntrinsicScopedConditionalPresheaf.semanticPrograms algebra .term :=
  IntrinsicScopedConditionalPresheaf.programsIso algebra .term

/-- A bound body is an internal function object in the presheaf category. -/
def representedBinder :
    (programs.functorHom programs) ≅ IntrinsicScopedConditionalPresheaf.binderBodies algebra .term .term :=
  IntrinsicScopedConditionalPresheaf.binderBodiesIso algebra .term .term

/-- Initiality retains whole firing trees and commutes with substitution. -/
noncomputable def firingModelInitial :
    Limits.IsInitial (SubstitutionModel.free rules algebra) :=
  SubstitutionModel.freeIsInitial rules algebra

/-- Edges retain the selected authored rule and every premise derivation. -/
noncomputable def eventGraph := EventGraphImageMorphism.variableGraph (IntrinsicScopedConditionalPresheaf.graph rules algebra)

/-- OSLF's input is the endpoint image of those program events. -/
noncomputable def theory (Γ : Ctx sig) := EventGraphModalTransport.theoryAt eventGraph (context Γ)

def state {Γ : Ctx sig} (t : Tm Γ) : (theory Γ).Term := ⟨.term, t⟩

/-- This comparison is proved through the rule table, not by defining the
independent reduction to be the endpoint image. -/
theorem step_iff {Γ : Ctx sig} (source target : Tm Γ) :
    (theory Γ).Step (state source) (state target) ↔ Step source target := by
  exact (IntrinsicScopedConditionalPresheaf.mem_reduction_iff rules algebra (context Γ) .term source target).trans
    firing_iff_step

def predicate {Γ : Ctx sig} (φ : Tm Γ → Prop) : (theory Γ).Term → Prop
  | ⟨.term, t⟩ => φ t

/-- The generated diamond means precisely a possible computation of an Agda
term, with no intermediate encoding as a proof-search goal. -/
theorem diamond_iff {Γ : Ctx sig} (φ : Tm Γ → Prop) (source : Tm Γ) :
    gsltDiamond (theory Γ) (predicate φ) (state source) ↔
      ∃ target, Step source target ∧ φ target := by
  rw [gsltDiamond_spec]
  constructor
  · rintro ⟨⟨sort, target⟩, step, holds⟩
    cases sort
    exact ⟨target, (step_iff source target).mp step, holds⟩
  · rintro ⟨target, step, holds⟩
    exact ⟨state target, (step_iff source target).mpr step, holds⟩

/-- The right adjoint in this OSLF library quantifies over predecessors.
It is not the usual future-universal modal box. -/
theorem pastBox_iff {Γ : Ctx sig} (φ : Tm Γ → Prop) (target : Tm Γ) :
    gsltBox (theory Γ) (predicate φ) (state target) ↔
      ∀ source, Step source target → φ source := by
  rw [gsltBox_spec]
  constructor
  · intro all source step
    exact all (state source) ((step_iff source target).mpr step)
  · rintro all ⟨sort, source⟩ step
    cases sort
    exact all source ((step_iff source target).mp step)

theorem modal_adjunction (Γ : Ctx sig) :
    GaloisConnection (gsltDiamond (theory Γ)) (gsltBox (theory Γ)) :=
  gsltGalois (theory Γ)

/-- Reindexing preserves computation. Reflection requires more: a
substitution can expose new redexes. -/
theorem diamond_substitute {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ)
    (φ : Tm Δ → Prop) (source : Tm Γ)
    (may : gsltDiamond (theory Γ) (predicate (fun t => φ (bind σ t)))
      (state source)) :
    gsltDiamond (theory Δ) (predicate φ) (state (bind σ source)) := by
  obtain ⟨target, step, holds⟩ := (diamond_iff _ _).mp may
  exact (diamond_iff _ _).mpr ⟨bind σ target, step_substitute step σ, holds⟩

theorem beta_observable {Γ : Ctx sig} (body : Tm (.term :: Γ)) (arg : Tm Γ) :
    gsltDiamond (theory Γ) (predicate (fun t => t = inst body arg))
      (state (app (lam body) arg)) :=
  (diamond_iff _ _).mpr ⟨inst body arg, .root (.beta body arg), rfl⟩

theorem zero_has_no_observation (φ : Tm [] → Prop) :
    ¬ gsltDiamond (theory []) (predicate φ) (state zero) := by
  intro may
  obtain ⟨target, step, _⟩ := (diamond_iff _ _).mp may
  exact zero_inert target step

/-- No backwards-modal law follows merely from the substitution laws. -/
theorem substitution_can_create_computation :
    ∃ (σ : Sub sig [.term] []) (source : Tm [.term]),
      gsltDiamond (theory []) (predicate (fun t => t = zero))
        (state (bind σ source)) ∧
      ¬ ∃ target, Step source target := by
  let σ : Sub sig [.term] [] := fun _ _ => app (lam (.var .zero)) zero
  refine ⟨σ, .var .zero, ?_, ?_⟩
  · exact beta_observable (.var .zero) zero
  · rintro ⟨target, step⟩
    exact variable_inert .zero target step

end Mettapedia.Languages.Agda.Intrinsic.Semantics
