import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUnaryConstancy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentParameterExchange

/-!
# Function declarations with an independent result type

The actual formed Pi annotation and its universe metadata are retained.
Application, constant abstraction, and reindexing compute on the existing
syntax. These operations support pruning an unused argument without choosing
an inhabitant of its type or choosing a new universe for the function.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantShape

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.DependentTypes TypedContextual.QuotientComprehensionSyntax

variable {Head : Type} {rules : Rules Head}

structure Shape (Γ : Context rules) where
  domain : TypeOver Γ
  codomain : TypeOver Γ
  whole : TypeOver Γ
  code : whole.code = .pi domain.code (Presentation.rename wk codomain.code)

namespace Shape

variable {Γ : Context rules} (shape : Shape Γ)

def reindex {Δ : Context rules} (base : Δ ⟶ Γ) : Shape Δ where
  domain := shape.domain.reindex base
  codomain := shape.codomain.reindex base
  whole := shape.whole.reindex base
  code := by
    change subst base.substitution shape.whole.code =
      .pi (subst base.substitution shape.domain.code) (Presentation.rename wk (subst base.substitution shape.codomain.code))
    rw [shape.code]
    simp only [subst, subst_liftSub_wk]

def apply {Δ : Context rules} (base : Δ ⟶ Γ) (function : Term Δ (shape.whole.reindex base))
    (argument : Term Δ (shape.domain.reindex base)) : Term Δ (shape.codomain.reindex base) := by
  refine ⟨.app function.code argument.code, ?_⟩
  have typed := function.typed
  change Typed rules Δ.raw function.code (subst base.substitution shape.whole.code) at typed
  rw [shape.code] at typed
  have applied := Derivable.appElim typed argument.typed
  change Typed rules Δ.raw (.app function.code argument.code)
    (inst0 argument.code (subst (liftSub base.substitution) (Presentation.rename wk shape.codomain.code))) at applied
  rw [subst_liftSub_wk, inst0_rename_wk] at applied
  exact applied

def constant {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (shape.codomain.reindex base)) :
    Term Δ (shape.whole.reindex base) := by
  refine ⟨.lam (Presentation.rename wk value.code), ?_⟩
  have formed := (shape.whole.reindex base).formed
  change Typed rules Δ.raw (subst base.substitution shape.whole.code) (.head shape.whole.level) at formed
  rw [shape.code] at formed
  change Typed rules Δ.raw (.lam (Presentation.rename wk value.code)) (subst base.substitution shape.whole.code)
  rw [shape.code]
  simp only [subst, subst_liftSub_wk] at formed ⊢
  exact .lamIntro formed shape.whole.universeWitness value.typed.weaken

def constantHere (value : Term Γ shape.codomain) : Term Γ shape.whole :=
  (shape.constant (𝟙 Γ) (value.cast shape.codomain.reindex_id.symm)).cast shape.whole.reindex_id

theorem constantHere_code (value : Term Γ shape.codomain) :
    (shape.constantHere value).code = .lam (Presentation.rename wk value.code) := by
  simp only [constantHere, Term.cast_code, constant]

def fresh (function : Term Γ shape.whole) :
    Term (extend Γ shape.domain) (shape.codomain.reindex (projectionHom Γ shape.domain)) :=
  shape.apply (projectionHom Γ shape.domain) (function.reindex (projectionHom Γ shape.domain)) (newest Γ shape.domain)

theorem fresh_code (function : Term Γ shape.whole) :
    (shape.fresh function).code = .app (Presentation.rename wk function.code) (.var 0) := by
  change Tm.app (subst projection function.code) (.var 0) = _
  rw [subst_projection]

theorem apply_constant {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (shape.codomain.reindex base))
    (argument : Term Δ (shape.domain.reindex base)) :
    Equal rules Δ.raw (shape.apply base (shape.constant base value) argument).code value.code
      (shape.codomain.reindex base).code := by
  have formed := (shape.whole.reindex base).formed
  change Typed rules Δ.raw (subst base.substitution shape.whole.code) (.head shape.whole.level) at formed
  rw [shape.code] at formed
  simp only [subst, subst_liftSub_wk] at formed
  have beta := Derivable.betaPi formed shape.whole.universeWitness value.typed.weaken argument.typed
  change Equal rules Δ.raw (.app (.lam (Presentation.rename wk value.code)) argument.code)
    value.code (subst base.substitution shape.codomain.code)
  simpa only [inst0_rename_wk] using beta

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

theorem canonical_code :
    (rawPi levels shape.domain (shape.codomain.reindex (projectionHom Γ shape.domain))).code = shape.whole.code := by
  rw [shape.code]
  change Tm.pi shape.domain.code (subst projection shape.codomain.code) = _
  rw [subst_projection]

noncomputable def canonical (function : Term Γ shape.whole) :
    Term Γ (rawPi levels shape.domain (shape.codomain.reindex (projectionHom Γ shape.domain))) :=
  function.convertType _ (by rw [shape.canonical_code levels]; exact shape.whole.isType.refl)

theorem canonical_value_code (function : Term Γ shape.whole) :
    (shape.canonical levels function).code = function.code := Term.convertType_code _ _ _

theorem canonical_fresh_code (function : Term Γ shape.whole) :
    (Products.rawFreshApp levels (shape.canonical levels function)).code = (shape.fresh function).code := by
  rw [shape.fresh_code]
  change Tm.app (Presentation.rename wk (shape.canonical levels function).code) (.var 0) = _
  rw [canonical, Term.convertType_code]

theorem constant_of_recovery (function : Term Γ shape.whole)
    (recovered : ContextualDependentProjectionInversion.Recovery levels (projectionHom Γ shape.domain) shape.codomain
      (⟨_, shape.fresh function⟩ : TotalTerm (extend Γ shape.domain))) :
    Equal rules Γ.raw function.code (shape.constantHere recovered.body).code shape.whole.code := by
  have original := ContextualDependentUnaryConstancy.constant_of_recovery levels shape.domain shape.codomain
    (shape.canonical levels function) (⟨recovered.body, by
      refine ⟨recovered.solves.1, ?_⟩
      have same := recovered.solves.2
      change Equal rules (extend Γ shape.domain).raw (subst projection recovered.body.code)
        (Products.rawFreshApp levels (shape.canonical levels function)).code
        (shape.codomain.reindex (projectionHom Γ shape.domain)).code
      rw [shape.canonical_fresh_code]
      exact same⟩)
  change Equal rules Γ.raw (shape.canonical levels function).code
    (.lam (subst projection recovered.body.code))
    (rawPi levels shape.domain (shape.codomain.reindex (projectionHom Γ shape.domain))).code at original
  rw [shape.canonical_code, shape.canonical_value_code, subst_projection] at original
  rw [shape.constantHere_code]
  exact original

end Shape
end ContextualDependentConstantShape
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
