import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticTypingCore
import Mettapedia.GSLT.LanguageDef.CanonicalConstructorSupport

/-!
# Supported source terms for finite Cost profiles

This is the static source fibre used by retained regions, indexed by the
existing interactive theory, cut, and finite continuation profile. It does
not require the two-slot continued object or any iteration-closure field.
Source binders and available target binders remain separate indices.

Normalization uses an existing contextual section and its declaration-aware
fragment theorem. Concrete sections discharge these inputs separately; the
carrier itself contains no normalizer or assumed closure law. An equation
path here retains the static fragment at every intermediate vertex.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open WellSorted

namespace ContinuationDecorationProfile
variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- The existing reflective source fibre with precisely the static-fragment
and target-support evidence needed by a generated Cost region. -/
structure StaticSourceTerm (profile : ContinuationDecorationProfile cut)
    (reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language) (color : CostStaticColor)
    (free : FreeTypeContext) (support : ContextSupport.Support)
    (sourceBound targetBound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) where
  term : ReflectiveWellSorted.OpenTerm reflection.1
    theory.presentation.presentation.language free sourceBound sort
  supported : HasTypeWithConstructors theory.presentation.presentation.language
    (· ∈ profile.wrappedLabels) free sourceBound term.1 (.base sort.1)
  safe : term.2.1.1.ReflectiveSupportSafeAt reflection.1 support targetBound
    (mapTypeExpr (color.symbolsOf theory))

namespace StaticSourceTerm
variable {profile : ContinuationDecorationProfile cut}
  {reflection : ReflectionExtension.AdmittedProfile theory.presentation.presentation.language}
  {color : CostStaticColor} {free : FreeTypeContext} {support : ContextSupport.Support}
  {sourceBound targetBound : List TypeExpr}
  {sort : LangSort theory.presentation.presentation.language}

@[ext] theorem ext
    {left right : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort}
    (same : left.term = right.term) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- One actual source equation edge, including the selected reflection. -/
def generator
    (left right : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort) :
    Prop :=
  ReflectiveEquationSemantics.ReflectiveEquationContextStep reflection.1 defaultBasePremises
    theory.presentation.presentation.language left.term.1 right.term.1

/-- Intermediate vertices retain both constructor and support certificates. -/
def equationSetoid : Setoid
    (profile.StaticSourceTerm reflection color free support sourceBound targetBound sort) where
  r := Relation.EqvGen generator
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Forgetting the certificates preserves source equation paths. The converse
is not inferred: an unrestricted path may leave the static fragment. -/
theorem equationSetoid_toOpen
    {left right : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort}
    (equivalent : equationSetoid.r left right) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid reflection.1
      defaultBasePremises theory.presentation.presentation.language free sourceBound
      (.base sort.1)).r left.term right.term := by
  induction equivalent with
  | rel left right edge => exact Relation.EqvGen.rel _ _ edge
  | refl term => exact Relation.EqvGen.refl _
  | symm left right relation ih => exact Relation.EqvGen.symm _ _ ih
  | trans left middle right first second firstIH secondIH =>
    exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Map the source representative into the exact finite generated language.
Principal introductions are excluded by the actual closure inventory. -/
theorem mapped_hasType
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort) :
    HasType profile.costWholeLanguage (free.map (color.symbolsOf theory))
      (sourceBound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) term.term.1)
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1)) :=
  profile.mapStatic_hasType nonprincipal color term.supported

variable (canonical : ComputableReflectiveFiberContextualSection theory reflection)
  (preserves : canonical.PreservesTypedConstructors (· ∈ profile.wrappedLabels))

/-- Normalize the source representative while retaining the exact source
and target support indices. No boundary occurrence is reconstructed here. -/
def normalize
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort) :
    profile.StaticSourceTerm reflection color free support sourceBound targetBound sort where
  term := canonical.normalize term.term
  supported := preserves term.term term.supported
  safe := canonical.preservesReflectiveSupport term.term support targetBound
    (mapTypeExpr (color.symbolsOf theory)) term.safe

@[simp] theorem normalize_term
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort) :
    (term.normalize canonical preserves).term = canonical.normalize term.term := rfl

theorem normalize_idempotent
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort) :
    (term.normalize canonical preserves).normalize canonical preserves =
      term.normalize canonical preserves := by
  apply ext
  exact canonical.toComputableReflectiveFiberSection.normalize_idempotent term.term

theorem normalize_eq_of_equationSetoid
    {left right : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort}
    (equivalent : equationSetoid.r left right) :
    left.normalize canonical preserves = right.normalize canonical preserves := by
  apply ext
  exact canonical.complete (equationSetoid_toOpen equivalent)

/-- Typing of the computed representative in either generated static colour. -/
theorem normalized_mapped_hasType
    (nonprincipal : ∀ constructor ∈ profile.constructorClosure,
      constructor ≠ cut.program.constructor ∧ constructor ≠ cut.environment.constructor)
    (term : profile.StaticSourceTerm reflection color free support sourceBound targetBound sort) :
    HasType profile.costWholeLanguage (free.map (color.symbolsOf theory))
      (sourceBound.map (mapTypeExpr (color.symbolsOf theory)))
      (mapPattern (color.symbolsOf theory) (term.normalize canonical preserves).term.1)
      (mapTypeExpr (color.symbolsOf theory) (.base sort.1)) :=
  (term.normalize canonical preserves).mapped_hasType nonprincipal

end StaticSourceTerm
end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
