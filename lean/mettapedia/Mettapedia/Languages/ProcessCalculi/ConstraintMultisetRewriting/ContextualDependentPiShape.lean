import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScope
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigma

/-!
# Typed opening and abstraction at a supplied dependent Pi annotation

The actual domain, dependent codomain, whole annotation, and universe
metadata are retained. Fresh application and abstraction compute directly on
syntax. Beta, eta, congruence, and reindexing use the native typed judgment;
no normalization, closed inhabitant, or choice of a new universe is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiShape

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax

variable {Head : Type} {rules : Rules Head}

structure Shape (Γ : Context rules) where
  domain : TypeOver Γ
  codomain : TypeOver (extend Γ domain)
  whole : TypeOver Γ
  code : whole.code = .pi domain.code codomain.code

namespace Shape

variable {Γ : Context rules} (shape : Shape Γ)

def fresh (function : Term Γ shape.whole) : Term (extend Γ shape.domain) shape.codomain where
  code := .app (Presentation.rename wk function.code) (.var 0)
  typed := by
    have typed := function.typed
    rw [shape.code] at typed
    have applied := Derivable.appElim (typed.rename (CtxRen.wk Γ.raw shape.domain.code))
      (Derivable.var (R := rules) (Γ := (extend Γ shape.domain).raw) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using applied

def abstract (body : Term (extend Γ shape.domain) shape.codomain) : Term Γ shape.whole where
  code := .lam body.code
  typed := by
    have formed := shape.whole.formed
    rw [shape.code] at formed ⊢
    exact .lamIntro formed shape.whole.universeWitness body.typed

theorem fresh_congruent (first second : Term Γ shape.whole)
    (same : Equal rules Γ.raw first.code second.code shape.whole.code) :
    Equal rules (extend Γ shape.domain).raw (shape.fresh first).code (shape.fresh second).code shape.codomain.code := by
  rw [shape.code] at same
  have compared := Derivable.appCong (same.rename (CtxRen.wk Γ.raw shape.domain.code))
    (Derivable.refl (Derivable.var (R := rules) (Γ := (extend Γ shape.domain).raw) 0))
  simpa only [fresh, Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using compared

theorem abstract_congruent (first second : Term (extend Γ shape.domain) shape.codomain)
    (same : Equal rules (extend Γ shape.domain).raw first.code second.code shape.codomain.code) :
    Equal rules Γ.raw (shape.abstract first).code (shape.abstract second).code shape.whole.code := by
  have formed := shape.whole.formed
  rw [shape.code] at formed ⊢
  exact .lamCong formed shape.whole.universeWitness same

theorem fresh_beta (body : Term (extend Γ shape.domain) shape.codomain) :
    Equal rules (extend Γ shape.domain).raw (shape.fresh (shape.abstract body)).code body.code shape.codomain.code := by
  have formed := shape.whole.formed
  rw [shape.code] at formed
  have compared := Derivable.betaPi (formed.rename (CtxRen.wk Γ.raw shape.domain.code)) shape.whole.universeWitness
    (body.typed.rename ((CtxRen.wk Γ.raw shape.domain.code).snoc shape.domain.code))
    (Derivable.var (R := rules) (Γ := (extend Γ shape.domain).raw) 0)
  simpa only [fresh, abstract, Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using compared

theorem eta (function : Term Γ shape.whole) :
    Equal rules Γ.raw (shape.abstract (shape.fresh function)).code function.code shape.whole.code := by
  have first := (shape.abstract (shape.fresh function)).typed
  have second := function.typed
  rw [shape.code] at first second ⊢
  exact .etaPi first second (shape.fresh_beta (shape.fresh function))

theorem fresh_equal_iff (first second : Term Γ shape.whole) :
    Equal rules Γ.raw first.code second.code shape.whole.code ↔
      Equal rules (extend Γ shape.domain).raw (shape.fresh first).code (shape.fresh second).code shape.codomain.code := by
  constructor
  · exact shape.fresh_congruent first second
  · intro same
    exact (shape.eta first).symm.trans ((shape.abstract_congruent _ _ same).trans (shape.eta second))

theorem abstract_equal_iff (first second : Term (extend Γ shape.domain) shape.codomain) :
    Equal rules Γ.raw (shape.abstract first).code (shape.abstract second).code shape.whole.code ↔
      Equal rules (extend Γ shape.domain).raw first.code second.code shape.codomain.code := by
  constructor
  · intro same
    exact (shape.fresh_beta first).symm.trans
      ((shape.fresh_congruent _ _ same).trans (shape.fresh_beta second))
  · exact shape.abstract_congruent first second

def reindex {Δ : Context rules} (base : Δ ⟶ Γ) : Shape Δ where
  domain := shape.domain.reindex base
  codomain := shape.codomain.reindex (rawLift base shape.domain)
  whole := shape.whole.reindex base
  code := by
    change subst base.substitution shape.whole.code = .pi (subst base.substitution shape.domain.code)
      (subst (liftSub base.substitution) shape.codomain.code)
    rw [shape.code]
    rfl

theorem fresh_reindex {Δ : Context rules} (base : Δ ⟶ Γ) (function : Term Γ shape.whole) :
    (shape.fresh function).reindex (rawLift base shape.domain) = (shape.reindex base).fresh (function.reindex base) := by
  apply Term.ext
  change Tm.app (subst (liftSub base.substitution) (Presentation.rename wk function.code)) (.var 0) =
    .app (Presentation.rename wk (subst base.substitution function.code)) (.var 0)
  rw [subst_liftSub_wk]

theorem abstract_reindex {Δ : Context rules} (base : Δ ⟶ Γ) (body : Term (extend Γ shape.domain) shape.codomain) :
    (shape.abstract body).reindex base = (shape.reindex base).abstract (body.reindex (rawLift base shape.domain)) :=
  Term.ext rfl

def apply {Δ : Context rules} (base : Δ ⟶ Γ) (function : Term Δ (shape.whole.reindex base))
    (argument : Term Δ (shape.domain.reindex base)) : Term Δ (shape.codomain.reindex (pair base argument)) := by
  refine ⟨.app function.code argument.code, ?_⟩
  have typed := function.typed
  change Typed rules Δ.raw function.code (subst base.substitution shape.whole.code) at typed
  rw [shape.code] at typed
  have applied := Derivable.appElim typed argument.typed
  change Typed rules Δ.raw (.app function.code argument.code)
    (inst0 argument.code (subst (liftSub base.substitution) shape.codomain.code)) at applied
  rw [ContextualDependentSigma.inst0_lift] at applied
  exact applied

end Shape
end ContextualDependentPiShape
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
