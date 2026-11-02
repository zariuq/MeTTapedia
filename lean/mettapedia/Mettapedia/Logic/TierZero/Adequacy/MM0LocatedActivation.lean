import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedProcess
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequest

/-!
# Located natural MM0 activation retains its installed source origin

Actual request consumption is in the request space. Premise reads and
conclusions occupy the protected judgment space. These are immutable physical
locations under the product substitution action, independent of payload shape.

The raw instance comes from the natural catalog activation, with retained
source key, finite arguments and actual contextual-body computation. The
comparison to source metadata is a theorem, not an alternative runtime path.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0LocatedActivation

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintCatalog
open MM0ConstraintInputNormalization
open MM0ConstraintTheoremApplication (falseHead trueHead)

abbrev Value := Space × Tm
abbrev action (target : Context) := LocatedSubstitution.action (N := Space) (MM0ConstraintParameters.action target)

def locate (raw : RuleInstance Tm) : RuleInstance Value :=
  LocatedRequest.lift .requests .judgments .requests .judgments raw

def activate (theory : Theory) (target : Context) (key : RuleKey) (arguments : List Preterm) :
    Option (RuleInstance Value) :=
  (MM0ScopedCatalogActivation.activate theory target key arguments).map locate

theorem origin (theory : Theory) (target : Context) (key : RuleKey) (arguments : List Preterm)
    {located : RuleInstance Value} (computed : activate theory target key arguments = some located) :
    ∃ raw, MM0ScopedCatalogActivation.activate theory target key arguments = some raw ∧ located = locate raw := by
  obtain ⟨raw, natural, same⟩ := Option.map_eq_some_iff.mp computed
  exact ⟨raw, natural, same.symm⟩

theorem source_origin {sorts : SortSignature} (theory : Theory) (target : Context)
    (formed : Context.WellFormed sorts target) (key : RuleKey) (arguments : List Preterm)
    {raw : RuleInstance Tm} (computed : MM0ScopedCatalogActivation.activate theory target key arguments = some raw) :
    ∃ schema, schemaFor theory target key = some schema ∧ arguments.length = schema.arity ∧
      RequestActivation.activate ContextualPatterns.layer falseHead trueHead (schema.requestRecipe target key.name)
        (RequestActivation.boundedAssignment schema.arity (arguments.map (encode target))) = some raw := by
  have compatibility := MM0ScopedCatalogActivation.natural_reflects_compatibility theory target formed key arguments computed
  cases compiled : schemaFor theory target key with
  | none => simp [MM0ScopedCatalogActivation.compatibilityActivate, compiled] at compatibility
  | some schema =>
      simp only [MM0ScopedCatalogActivation.compatibilityActivate, compiled, Option.bind_eq_bind, Option.bind_some] at compatibility
      split at compatibility
      · rename_i count
        refine ⟨schema, rfl, count, ?_⟩
        rw [← count, bounded_encoded_assignment]
        exact compatibility
      · cases compatibility

theorem equality_checks {sorts : SortSignature} (theory : Theory) (target : Context)
    (formed : Context.WellFormed sorts target) (key : RuleKey) (arguments : List Preterm)
    {raw : RuleInstance Tm} (computed : MM0ScopedCatalogActivation.activate theory target key arguments = some raw) :
    LocatedRequest.EqualityChecks raw := by
  obtain ⟨schema, _, _, actual⟩ := source_origin theory target formed key arguments computed
  obtain ⟨request, premises, conclusion, _, _, _, rfl⟩ :=
    (RequestActivation.activate_iff ContextualPatterns.layer falseHead trueHead
      (schema.requestRecipe target key.name) _ raw).mp actual
  intro check member
  have same : check = ABTDataChecks.check falseHead trueHead
      (schema.dataCondition (RequestActivation.boundedAssignment schema.arity (arguments.map (encode target)))) := by
    simpa [RequestActivation.fromValues, Schema.requestRecipe] using member
  subst check
  exact ⟨_, _, rfl⟩

theorem request_instance_stays_data (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (target : Context) (hypotheses : List Preterm)
    (assignment : Subst Nat Tm) (width arity : Nat) (name : String) (value : Tm)
    (instantiated : ContextualPatterns.layer.inst assignment (theoremRequest width arity name) = some value) :
    ValidValue signature definitions theorems target hypotheses value := by
  have raw := ((ContextualPatterns.Pattern.inst_iff assignment (theoremRequest width arity name) value).mp instantiated).1
  change ((expressionFields width (formals arity)).inst (ContextualPatterns.Pattern.atOccurrence assignment)).map
    (Term.node (.judgment (requestTag name))) = some value at raw
  obtain ⟨fields, _, same⟩ := Option.map_eq_some_iff.mp raw
  rw [← same]
  constructor
  · intro expression equal
    have tags : requestTag name = "pf" := Head.judgment.inj (Term.node.inj equal).1
    exact False.elim (requestTag_ne_proof name tags)
  · intro sort left right equal
    have tags : requestTag name = "cv" := Head.judgment.inj (Term.node.inj equal).1
    exact False.elim (requestTag_ne_conversion name tags)

end Mettapedia.Logic.TierZero.Adequacy.MM0LocatedActivation
