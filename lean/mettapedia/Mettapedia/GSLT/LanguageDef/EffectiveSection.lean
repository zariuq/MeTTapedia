import Mathlib.Computability.Halting
import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Effective sections

A section of the static equivalence of an interactive theory chooses one
representative of every class.  The structure that records one,
`ComputableCanonicalSection`, asks for a function with two laws and nothing
about how that function is obtained.  Every theory has one: choose a
representative of each class (`ComputableCanonicalSection.ofChoice`).  The
structure alone therefore does not distinguish any theory.

This module adds the missing condition.  Closed terms have an injective
structural code in the natural numbers, and a section is *effective* when a
computable function on codes tracks its normal-form function.  An effective
section decides the static equivalence along every computable family of
terms, which is what makes the existence of one a restriction on the theory.

The condition is stated first for a section of any equivalence on the closed
terms of a sort, so that it also applies to a theory with no interaction, and
then for the section of an iGSLT, which is the instance on its interacting
fibre.

The lambda calculus is the positive example: its static equivalence is
equality, and the identity is an effective section.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.Framework.ConstructorCategory

/-! ## Sections on the closed terms of a sort -/

namespace ComputableSetoidSection

variable {language : LanguageDef} {sort : LangSort language}
  {relation : Setoid (WellSorted.ClosedTerm language sort)}

/-- A section on the closed terms of a sort is effective when a computable
function on structural codes tracks its normal-form function. -/
def Effective
    (canonical : ComputableSetoidSection (WellSorted.ClosedTerm language sort) relation) :
    Prop :=
  ∃ track : ℕ → ℕ, Computable track ∧
    ∀ term, patternCode (canonical.normalize term).1 = track (patternCode term.1)

/-- **An effective section decides its equivalence** along every family of
closed terms whose codes are computable. -/
theorem Effective.computablePred
    {canonical : ComputableSetoidSection (WellSorted.ClosedTerm language sort) relation}
    (effective : canonical.Effective)
    {left right : ℕ → WellSorted.ClosedTerm language sort}
    (leftComputable : Computable fun index => patternCode (left index).1)
    (rightComputable : Computable fun index => patternCode (right index).1) :
    ComputablePred fun index => relation.r (left index) (right index) := by
  obtain ⟨track, trackComputable, tracks⟩ := effective
  have decided : ComputablePred fun index =>
      track (patternCode (left index).1) = track (patternCode (right index).1) :=
    ⟨fun _ => inferInstance,
      (Primrec.eq (α := ℕ)).decide.to_comp.comp (trackComputable.comp leftComputable)
        (trackComputable.comp rightComputable)⟩
  refine decided.of_eq fun index => ?_
  have characterized := canonical.equivalent_iff_normalize_eq (left index) (right index)
  constructor
  · intro same
    apply characterized.mpr
    apply Subtype.ext
    apply patternCode_injective
    exact (tracks _).trans (same.trans (tracks _).symm)
  · intro equivalent
    exact (tracks _).symm.trans
      ((congrArg (fun term : WellSorted.ClosedTerm language sort => patternCode term.1)
        (characterized.mp equivalent)).trans (tracks _))

end ComputableSetoidSection

/-! ## The section of an iGSLT -/

/-- The structural code of a closed term of the interacting fibre. -/
def IGSLT.termCode (theory : IGSLT) (term : theory.toGSLT.Term) : ℕ :=
  patternCode (show theory.presentation.Term from term).1

/-- Distinct terms have distinct codes. -/
theorem IGSLT.termCode_injective (theory : IGSLT) : Function.Injective theory.termCode := by
  intro first second same
  have patterns : (show theory.presentation.Term from first).1 =
      (show theory.presentation.Term from second).1 := patternCode_injective same
  exact Subtype.ext patterns

namespace ComputableCanonicalSection

/-- Every theory has a section: choose a representative of each class.  The
construction uses no property of the theory, so the bare structure excludes
nothing. -/
noncomputable def ofChoice (theory : IGSLT) : ComputableCanonicalSection theory where
  normalize := fun term => (Quotient.mk theory.toGSLT.equations term).out
  equivalent := fun term => Quotient.exact (Quotient.out_eq _)
  complete := by
    intro left right equivalent
    exact congrArg Quotient.out (Quotient.sound equivalent)

/-- A section is effective when a computable function on structural codes
tracks its normal-form function. -/
def Effective {theory : IGSLT} (canonical : ComputableCanonicalSection theory) : Prop :=
  ∃ track : ℕ → ℕ, Computable track ∧
    ∀ term : theory.toGSLT.Term,
      theory.termCode (canonical.normalize term) = track (theory.termCode term)

/-- A section of an iGSLT is effective exactly when it is so as a section on
the closed terms of the interacting sort. -/
theorem effective_iff_setoidSection {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory) :
    canonical.Effective ↔ canonical.toComputableSetoidSection.Effective :=
  Iff.rfl

/-- **An effective section decides the static equivalence** along every
family of terms whose codes are computable.  This is the statement for
closed terms of a sort, read on the interacting fibre. -/
theorem Effective.computablePred {theory : IGSLT}
    {canonical : ComputableCanonicalSection theory} (effective : canonical.Effective)
    {left right : ℕ → theory.toGSLT.Term}
    (leftComputable : Computable fun index => theory.termCode (left index))
    (rightComputable : Computable fun index => theory.termCode (right index)) :
    ComputablePred fun index => theory.toGSLT.equations.r (left index) (right index) :=
  ((effective_iff_setoidSection canonical).mp effective).computablePred leftComputable
    rightComputable

/-- A section that fixes every term is effective. -/
theorem effective_of_normalize_eq {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (fixed : ∀ term, canonical.normalize term = term) : canonical.Effective :=
  ⟨id, Computable.id, fun term => by rw [fixed term]; rfl⟩

end ComputableCanonicalSection

/-- The lambda calculus has an effective section: the identity. -/
theorem lambdaCanonicalSection_effective :
    LambdaContinuedInteraction.lambdaCanonicalSection.Effective :=
  ComputableCanonicalSection.effective_of_normalize_eq _ fun _ => rfl

end Mettapedia.GSLT.LanguageDef
