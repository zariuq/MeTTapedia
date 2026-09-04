import Mettapedia.GSLT.Logic.MinimalEnablingContext
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-!
# Minimal-context formulas as generated OSLF native types

This module composes the least-enabling-context labeled transition system with
the sole GSLT-to-OSLF construction.  Labels are contexts equipped, at every
transition, with the universal factorization property; formula denotations are
therefore ordinary equation-invariant native types of the same OSLF predicate
frame.

No existence of least contexts is assumed for arbitrary GSLTs.  A language
instance must construct `ContextualRules` and prove the least-enabler witness
used by each admitted transition.  Image-finiteness remains an explicit
hypothesis of adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.MinimalContextNativeTypes

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.MinimalEnablingContext.ContextualRules
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

universe uTerm uContext uRule uAtom

variable {S : GSLT.{uTerm}}
    (rules : ContextualRules.{uContext, uRule} S)
    (observations : ContextualRules.Observations.{uAtom} S)

/-- The full minimal-context formula denotation in the generated OSLF. -/
def formulaNativeType
    (formula : Formula observations.Atom rules.Context) : GSLTNativeType S :=
  HennessyMilnerNativeTypes.formulaNativeType
    (rules.hmlSystem observations) formula

/-- The positive minimal-context formula denotation in the generated OSLF. -/
def positiveFormulaNativeType
    (formula : PosFormula observations.Atom rules.Context) : GSLTNativeType S :=
  HennessyMilnerNativeTypes.positiveFormulaNativeType
    (rules.hmlSystem observations) formula

/-- Native-type satisfaction is precisely satisfaction in the labeled system
whose transitions carry least-enabler proofs. -/
@[simp]
theorem satisfies_formulaNativeType_iff
    (formula : Formula observations.Atom rules.Context) (term : S.Term) :
    (gsltOSLF S).satisfies (S := ()) term
        (formulaNativeType rules observations formula).pred ↔
      (rules.hmlSystem observations).sat formula term :=
  Iff.rfl

/-- A context diamond holds exactly when there is an admitted least-context
transition to a state satisfying its body. -/
theorem satisfies_diamond_iff
    (context : rules.Context)
    (body : Formula observations.Atom rules.Context) (source : S.Term) :
    (gsltOSLF S).satisfies (S := ()) source
        (formulaNativeType rules observations (.dia context body)).pred ↔
      ∃ target, rules.Act context source target ∧
        (gsltOSLF S).satisfies (S := ()) target
          (formulaNativeType rules observations body).pred :=
  Iff.rfl

/-- Under image-finiteness modulo equations, equivalence in all generated
minimal-context formula types is bisimilarity for the least-context labeled
system. -/
theorem formulaNativeTypes_equivalent_iff_bisimilar
    (finite : (rules.hmlSystem observations).ImageFiniteModulo)
    (left right : S.Term) :
    (∀ formula : Formula observations.Atom rules.Context,
      ((gsltOSLF S).satisfies (S := ()) left
          (formulaNativeType rules observations formula).pred ↔
       (gsltOSLF S).satisfies (S := ()) right
          (formulaNativeType rules observations formula).pred)) ↔
      (rules.hmlSystem observations).Bisimilar left right :=
  HennessyMilnerNativeTypes.formulaNativeTypes_equivalent_iff_bisimilar
    (rules.hmlSystem observations) finite left right

/-- Positive minimal-context native types characterize the simulation
preorder under the same finiteness hypothesis. -/
theorem positiveFormulaNativeTypes_preorder_iff_similar
    (finite : (rules.hmlSystem observations).ImageFiniteModulo)
    (left right : S.Term) :
    (∀ formula : PosFormula observations.Atom rules.Context,
      (gsltOSLF S).satisfies (S := ()) left
          (positiveFormulaNativeType rules observations formula).pred →
        (gsltOSLF S).satisfies (S := ()) right
          (positiveFormulaNativeType rules observations formula).pred) ↔
      (rules.hmlSystem observations).Similar left right :=
  HennessyMilnerNativeTypes.positiveFormulaNativeTypes_preorder_iff_similar
    (rules.hmlSystem observations) finite left right

#print axioms satisfies_formulaNativeType_iff
#print axioms satisfies_diamond_iff
#print axioms formulaNativeTypes_equivalent_iff_bisimilar
#print axioms positiveFormulaNativeTypes_preorder_iff_similar

end Mettapedia.OSLF.Framework.MinimalContextNativeTypes
