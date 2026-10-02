import Mettapedia.OSLF.Syntax.BindingCloneEquationTransport
import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra

/-!
# Source equations constrain incoming accounted clone maps

An observed account model maps to its source. Such an observation alone does
not supply a map in the opposite direction. If a full clone map does enter
the model from the rho equation source, QuoteDrop holds at every target
name, including account-acted names outside any established image.

The existing raw marker model is a nontrivial positive observation model
receiving the raw term clone. Its literal constructor distinctions prevent
an incoming clone map from the full rho equation quotient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.AccountBindingEquationBoundary

open Mettapedia.OSLF.Binding
open BindingCloneFoldSubstitution BindingCloneEquationTransport BindingSubstitutionAlgebra
open FreeBindingTerms RhoSchema RhoSourceEquationModel
open AccountBindingAlgebra

universe u

/-- Full preservation of the variable instance forces reflection at every
target name. No target element is required to come from the source map. -/
theorem quote_drop_of_source_hom (target : BindingCloneAlgebra.Algebra.{u} sig)
    (incoming : FreeBindingClone.Hom RhoSourceComparison.source target)
    {Γ : Ctx sig} (name : target.substitution.Carrier Γ Srt.nm) :
    target.operation Op.quo (.cons (target.operation Op.drp (.cons name .nil)) .nil) =
      name := by
  let env : Environment sig target.substitution.Carrier [Srt.nm] Γ :=
    fun _ index =>
      match index with
      | .zero => name
      | .succ impossible => nomatch impossible
  have equation := target_environment_eqClosure incoming RhoSourceComparison.source_equations
    quote_drop_source_equation env
  simpa only [quotedDroppedName, nameVariable, interpret, fold, foldArgs,
    BindingCloneAlgebra.Algebra.toRaw, target.operation_substitute,
    BindingSubstitutionAlgebra.Algebra.substituteArgs,
    BindingSubstitutionAlgebra.Algebra.liftEnvironment, target.substitution.substitute_var,
    env] using equation

/-- The actual source equation clone inhabits the incoming-map hypothesis
and satisfies the law on all its name classes. -/
theorem source_quote_drop {Γ : Ctx sig}
    (name : RhoSourceComparison.source.substitution.Carrier Γ Srt.nm) :
    RhoSourceComparison.source.operation Op.quo
      (.cons (RhoSourceComparison.source.operation Op.drp (.cons name .nil)) .nil) = name :=
  quote_drop_of_source_hom RhoSourceComparison.source
    (FreeBindingClone.Hom.id RhoSourceComparison.source) name

/-- The source observation in an account model is not an incoming unit.
Whenever an incoming full clone map exists, all its target names satisfy
the source variable-instance equation. -/
theorem model_quote_drop (target : Model RhoSourceComparison.source Srt.pr)
    (incoming : FreeBindingClone.Hom RhoSourceComparison.source target.observed.left)
    {Γ : Ctx sig} (name : target.observed.left.substitution.Carrier Γ Srt.nm) :
    target.observed.left.operation Op.quo
      (.cons (target.observed.left.operation Op.drp (.cons name .nil)) .nil) = name :=
  quote_drop_of_source_hom target.observed.left incoming name

/-- Acting on a target name does not exempt it from the forced equation,
whether or not that acted name is in the incoming morphism's image. -/
theorem acted_name_quote_drop (target : Model RhoSourceComparison.source Srt.pr)
    (incoming : FreeBindingClone.Hom RhoSourceComparison.source target.observed.left)
    {Γ : Ctx sig} (account : SourceAccountSubstitution.Account RhoSourceComparison.source Srt.pr Γ)
    (name : target.observed.left.substitution.Carrier Γ Srt.nm) :
    target.observed.left.operation Op.quo
      (.cons (target.observed.left.operation Op.drp
        (.cons (target.act account name) .nil)) .nil) = target.act account name :=
  model_quote_drop target incoming (target.act account name)

/-- The actual raw marker comparison receives the raw term clone through
its standard full constructor-and-substitution interpretation. -/
noncomputable def rawMarkerIncoming :
    FreeBindingClone.Hom (BindingCloneAlgebra.terms sig)
      RhoSourceComparison.model.observed.left :=
  FreeBindingClone.interpretHom RhoSourceComparison.model.observed.left

theorem rawMarkerIncoming_embed {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    rawMarkerIncoming.raw.map term =
      embed (M := (OccurrenceMarker.context (S := sig) Srt.pr).arities) term :=
  SecondOrderContext.termAlgebra_interpret (OccurrenceMarker.context (S := sig) Srt.pr) term

/-- The positive map retains the entire source equation-class observation,
including terms with nontrivial binding structure. -/
theorem rawMarkerIncoming_observe {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    RhoSourceComparison.model.observed.hom.raw.map (rawMarkerIncoming.raw.map term) =
      (Quotient.mk _ term : TermQ rhoSourceE Γ sort) := by
  rw [rawMarkerIncoming_embed]
  exact RhoSourceComparison.observe_source term

/-- A genuine source account creates a target value outside the positive
raw-term map's image. The target has more than the mapped source terms. -/
theorem acted_process_outside_raw_image :
    ¬ ∃ term : Term sig [Srt.pr] Srt.pr,
      rawMarkerIncoming.raw.map term =
        RhoSourceComparison.model.act
          (FreeMonoid.of (RhoSourceComparison.source.substitution.injectVar
            (Var.zero : Var [Srt.pr] Srt.pr))) (Term.var Var.zero) := by
  rintro ⟨term, equal⟩
  rw [rawMarkerIncoming_embed] at equal
  change embed term = OccurrenceMarker.markAt (S := sig) Srt.pr (Term.var Var.zero) at equal
  simp only [OccurrenceMarker.markAt, dif_pos] at equal
  cases term <;> cases equal

/-- Literal raw rho syntax cannot receive a clone map from the equation
source: its quote/drop tree is distinct from its name variable. -/
theorem no_raw_term_incoming :
    ¬ Nonempty (FreeBindingClone.Hom RhoSourceComparison.source
      (BindingCloneAlgebra.terms sig)) := by
  rintro ⟨incoming⟩
  have equation := quote_drop_of_source_hom (BindingCloneAlgebra.terms sig) incoming
    (.var .zero : Term sig [Srt.nm] Srt.nm)
  change Term.op Op.quo (.cons (.op Op.drp (.cons (.var Var.zero) .nil)) .nil) =
    (.var Var.zero : Term sig [Srt.nm] Srt.nm) at equation
  cases equation

/-- The independently constructed nontrivial account model remains raw
syntax at its name sort. Its observation map therefore cannot be reversed
to any full clone map from the equation source. -/
theorem no_raw_marker_incoming :
    ¬ Nonempty (FreeBindingClone.Hom RhoSourceComparison.source
      RhoSourceComparison.model.observed.left) := by
  rintro ⟨incoming⟩
  have equation := model_quote_drop RhoSourceComparison.model incoming
    (Term.var Var.zero (S := withMetas sig (OccurrenceMarker.context (S := sig) Srt.pr).arities)
      (Γ := [Srt.nm]))
  change Term.op (Sum.inl Op.quo)
      (.cons (.op (Sum.inl Op.drp) (.cons (.var Var.zero) .nil)) .nil) =
    (Term.var Var.zero : Term (withMetas sig
      (OccurrenceMarker.context (S := sig) Srt.pr).arities) [Srt.nm] Srt.nm) at equation
  cases equation

end Mettapedia.GSLT.LanguageDef.Cost.AccountBindingEquationBoundary
