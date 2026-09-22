import Mettapedia.OSLF.Formula
import Mettapedia.GSLT.LanguageDef.SortedEquationInstance

/-!
# The generated logic of a presentation whose instances read their type contexts

`SortedEquationInstance` supplies the disciplined equation theory and the
operational theory built on it.  This module carries that theory up to the OSLF
layer: the frame of predicates it selects, the formula semantics read in that
frame, and the bridges to the permissive reading.

The bridges run one way only, and that is the point.  A predicate invariant
under the permissive theory is invariant under the disciplined one, because the
disciplined equivalence is smaller; the converse fails, and a presentation whose
equations are instantiated without regard to their declared sorts is where it
fails.  So the disciplined frame is strictly larger, and the extra predicates
are exactly the ones a sort distinction supplies.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SortedEquationFrame

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- **The disciplined generated theory** of a presentation. -/
def langSortedGSLTUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    Mettapedia.GSLT.GSLT :=
  gsltModuloSortedEquations (engineBasePremises relEnv) lang

/-- Its one-step relation, the one OSLF reads. -/
def langSortedSemanticReducesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (source target : Pattern) : Prop :=
  (langSortedGSLTUsing relEnv lang).Step source target

/-- Every disciplined step is a step of the permissive theory. -/
theorem langSemanticReducesUsing_of_sorted
    {relEnv : RelationEnv} {lang : LanguageDef} {source target : Pattern}
    (step : langSortedSemanticReducesUsing relEnv lang source target) :
    langSemanticReducesUsing relEnv lang source target :=
  stepModuloEquations_of_sorted step

/-- Atomic observations of the disciplined logic. -/
abbrev SortedEquationAtomSemUsing (relEnv : RelationEnv) (lang : LanguageDef) :=
  String → EquationPredicate (langSortedGSLTUsing relEnv lang)

/-- **A predicate of the permissive logic is a predicate of the disciplined
one.**  The disciplined equivalence is smaller, so invariance under it is a
weaker demand. -/
def sortedEquationPredicate (relEnv : RelationEnv) (lang : LanguageDef)
    (predicate : EquationPredicate (langGSLTUsing relEnv lang)) :
    EquationPredicate (langSortedGSLTUsing relEnv lang) :=
  ⟨predicate.1, fun _ _ equivalent =>
    predicate.2 (equationEquiv_of_sortedEquationEquiv equivalent)⟩

/-- The same, at a whole family of atomic observations. -/
def sortedEquationAtomSemUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (interpretation : EquationAtomSemUsing relEnv lang) :
    SortedEquationAtomSemUsing relEnv lang :=
  fun atom => sortedEquationPredicate relEnv lang (interpretation atom)

/-- **The frame of the disciplined generated logic**: the predicates its
equations cannot see past, closed under arbitrary intersection and carrying the
saturation that reads a structural connective through the equations. -/
def sortedEquationFrameUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    PredFrame where
  Mem := EquationInvariant (langSortedGSLTUsing relEnv lang)
  mem_inter := by
    intro _ left right equivalent
    constructor
    · intro holds candidate memCandidate selected
      exact (memCandidate equivalent).mp (holds candidate memCandidate selected)
    · intro holds candidate memCandidate selected
      exact (memCandidate equivalent).mpr (holds candidate memCandidate selected)
  close := fun predicate =>
    (saturatePredicate (langSortedGSLTUsing relEnv lang) predicate).1
  le_close := by
    intro predicate term holds
    exact ⟨term, (langSortedGSLTUsing relEnv lang).equations.iseqv.refl term, holds⟩
  mem_close := fun predicate =>
    (saturatePredicate (langSortedGSLTUsing relEnv lang) predicate).2
  close_mono := by
    rintro predicate predicate' weaker term ⟨representative, equivalent, holds⟩
    exact ⟨representative, equivalent, weaker representative holds⟩

/-- **Every predicate of the permissive frame is a predicate of the disciplined
one.** -/
theorem mem_sortedEquationFrame_of_mem_equationFrame
    (relEnv : RelationEnv) (lang : LanguageDef) (predicate : Pattern → Prop)
    (member : (equationFrameUsing relEnv lang).Mem predicate) :
    (sortedEquationFrameUsing relEnv lang).Mem predicate :=
  fun _ _ equivalent => member (equationEquiv_of_sortedEquationEquiv equivalent)

/-- Formula semantics read in the disciplined frame. -/
def langSortedSemUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (I : SortedEquationAtomSemUsing relEnv lang) : OSLFFormula → Pattern → Prop :=
  semEnv (langSortedSemanticReducesUsing relEnv lang)
    (sortedEquationFrameUsing relEnv lang)
    (fun atom => (I atom).1) ScopeEnv.empty

/-- The empty scope environment consists of predicates of the disciplined
logic. -/
theorem sortedEquationInvariant_scopeEnv_empty
    (relEnv : RelationEnv) (lang : LanguageDef) :
    ∀ index, EquationInvariant (langSortedGSLTUsing relEnv lang)
      (ScopeEnv.empty index) :=
  fun _ _ _ _ => Iff.rfl

/-! ## Its metatheory, inherited rather than recopied

The frame a setoid selects, and the invariance of the semantics read in it, are
proved once at that generality in `Formula`.  The disciplined frame is one
instance of that construction and the permissive frame is another, so what
follows is the instantiation and not a second proof. -/

/-- The disciplined frame is the frame its equations select. -/
theorem sortedEquationFrameUsing_eq_setoidFrame
    (relEnv : RelationEnv) (lang : LanguageDef) :
    sortedEquationFrameUsing relEnv lang
      = setoidFrame (langSortedGSLTUsing relEnv lang).equations :=
  rfl

/-- **Formula semantics read in the disciplined frame is invariant under the
disciplined equations**, whenever its atoms and its scope environment are. -/
theorem semEnv_sortedEquationInvariantUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (I : SortedEquationAtomSemUsing relEnv lang) (formula : OSLFFormula) :
    ∀ env : ScopeEnv,
      (∀ index, EquationInvariant (langSortedGSLTUsing relEnv lang) (env index)) →
      EquationInvariant (langSortedGSLTUsing relEnv lang)
        (semEnv (langSortedSemanticReducesUsing relEnv lang)
          (sortedEquationFrameUsing relEnv lang) (fun atom => (I atom).1) env formula) :=
  semEnv_setoidInvariant (langSortedGSLTUsing relEnv lang).equations
    (langSortedSemanticReducesUsing relEnv lang)
    (fun equivalent step =>
      (langSortedGSLTUsing relEnv lang).rewrites_resp_left equivalent step)
    (fun step equivalent =>
      (langSortedGSLTUsing relEnv lang).rewrites_resp_right step equivalent)
    (fun atom => (I atom).1) (fun atom => (I atom).2) formula

/-- **So a generated scope read in the disciplined frame is a fixed point.** -/
theorem frameClosed_sortedEquationFrameUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (I : SortedEquationAtomSemUsing relEnv lang) :
    FrameClosed (langSortedSemanticReducesUsing relEnv lang)
      (sortedEquationFrameUsing relEnv lang) (fun atom => (I atom).1) :=
  fun env formula envInv =>
    semEnv_sortedEquationInvariantUsing relEnv lang I formula env envInv

/-- Formula semantics read in the disciplined frame denotes a predicate of the
disciplined logic. -/
def langSortedFormulaSemUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (I : SortedEquationAtomSemUsing relEnv lang) (formula : OSLFFormula) :
    EquationPredicate (langSortedGSLTUsing relEnv lang) :=
  ⟨langSortedSemUsing relEnv lang I formula,
    semEnv_sortedEquationInvariantUsing relEnv lang I formula ScopeEnv.empty
      (sortedEquationInvariant_scopeEnv_empty relEnv lang)⟩

@[simp] theorem langSortedFormulaSemUsing_apply
    (relEnv : RelationEnv) (lang : LanguageDef)
    (I : SortedEquationAtomSemUsing relEnv lang) (formula : OSLFFormula)
    (term : Pattern) :
    langSortedFormulaSemUsing relEnv lang I formula term ↔
      langSortedSemUsing relEnv lang I formula term := Iff.rfl

end Mettapedia.OSLF.Framework.SortedEquationFrame
