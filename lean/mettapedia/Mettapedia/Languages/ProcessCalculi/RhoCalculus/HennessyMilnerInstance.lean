import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-!
# Hennessy–Milner adequacy for rho

The established rho GSLT has closed processes as terms, canonical-form
equality as its equations, and the equation-saturated authored step.  Any
family of equation-invariant predicates serves as its observation set, and
the generic adequacy theorem applies once the step is image-finite modulo
the equations.

Image-finiteness modulo the equations for rho is the statement that a
closed process has finitely many successor classes.  It is exactly the
completeness of a canonical-representative stepper for the saturated step,
which the runtime-alignment stage establishes; here it is an explicit
hypothesis of the adequacy theorems, never assumed silently.  The soundness
direction and the descent of the equations into bisimilarity need no such
hypothesis and are unconditional.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerInstance

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

set_option autoImplicit false

universe uAtom

/-- The rho system with an explicit observation set of equation-invariant
predicates. -/
def rhoSystem (Atom : Type uAtom)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) :
    System.{uAtom, 0} rhoLanguageDefGSLT :=
  System.ofObserved ⟨Atom, fun atom => (observe atom).1⟩ fun atom _ _ equivalent =>
    (observe atom).2 equivalent

/-- Equated closed processes are bisimilar under every observation set. -/
theorem bisimilar_of_equiv (Atom : Type uAtom)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT)
    {left right : RhoProcess} (equivalent : rhoLanguageDefGSLT.Equiv left right) :
    (rhoSystem Atom observe).Bisimilar left right :=
  (rhoSystem Atom observe).bisimilar_of_equiv equivalent

/-- Bisimilar closed processes satisfy the same formulas (unconditional). -/
theorem logicallyEquivalent_of_bisimilar (Atom : Type uAtom)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT)
    {left right : RhoProcess} (bisimilar : (rhoSystem Atom observe).Bisimilar left right) :
    (rhoSystem Atom observe).LogicallyEquivalent left right :=
  (rhoSystem Atom observe).logicallyEquivalent_of_bisimilar bisimilar

/-- Adequacy for rho: logical equivalence is bisimilarity, given finitely many
successor classes. -/
theorem logicallyEquivalent_iff_bisimilar (Atom : Type uAtom)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT)
    (finite : (rhoSystem Atom observe).ImageFiniteModulo)
    (left right : RhoProcess) :
    (rhoSystem Atom observe).LogicallyEquivalent left right ↔
      (rhoSystem Atom observe).Bisimilar left right :=
  (rhoSystem Atom observe).logicallyEquivalent_iff_bisimilar finite left right

/-- The negation-free fragment for rho: the logical preorder is the
simulation preorder, given finitely many successor classes. -/
theorem logicalPreorder_iff_similar (Atom : Type uAtom)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT)
    (finite : (rhoSystem Atom observe).ImageFiniteModulo)
    (left right : RhoProcess) :
    (rhoSystem Atom observe).LogicalPreorder left right ↔
      (rhoSystem Atom observe).Similar left right :=
  (rhoSystem Atom observe).logicalPreorder_iff_similar finite left right

/-- Adequacy on rho's equation classes. -/
theorem logicallyEquivalentClass_iff_bisimilarClass (Atom : Type uAtom)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT)
    (finite : (rhoSystem Atom observe).ImageFiniteModulo)
    (left right : Quotient rhoLanguageDefGSLT.equations) :
    (rhoSystem Atom observe).logicallyEquivalentClass left right ↔
      (rhoSystem Atom observe).bisimilarClass left right :=
  (rhoSystem Atom observe).logicallyEquivalentClass_iff_bisimilarClass finite left right

/-- The empty observation set. -/
def bareObservations : ObservedGSLT.{0} rhoLanguageDefGSLT :=
  ⟨PEmpty.{1}, fun atom => (PEmpty.elim atom : EquationPredicate rhoLanguageDefGSLT).1⟩

/-- The observation-free instance: bisimilarity of the pure transition
structure of closed rho processes, with the observed bisimilarity of the GSLT
as its other face. -/
theorem bare_bisimilar_iff (left right : RhoProcess) :
    (rhoSystem PEmpty.{1} (fun atom => PEmpty.elim atom)).Bisimilar left right ↔
      bareObservations.Bisimilar left right :=
  System.ofObserved_bisimilar_iff bareObservations
    (fun atom _ _ equivalent =>
      (PEmpty.elim atom : EquationPredicate rhoLanguageDefGSLT).2 equivalent)
    left right

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerInstance
