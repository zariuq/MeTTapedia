import Mettapedia.OSLF.Syntax.AuthoredPositionedRulePolynomial
import Mettapedia.OSLF.Syntax.AuthoredPositionedRootComparison
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# The authored rho base rule in the semantic operational model

The reflective presentation's actual ACU equations and positioned COMM rule
instantiate the general combined binding/equation/base-rule classifier. An
open continuation depending on the input name supplies a non-ground example.
Duplicating the COMM declaration gives two different free firing witnesses
at the same interpreted endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoPositionedOperationalModel

open CategoryTheory CategoryTheory.Limits
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRootComparison

private noncomputable abbrev quotientModel := FreeBindingEquationModel.presented rhoE
private noncomputable abbrev quotientAlgebra := quotientModel.algebra

/-- The same open continuation as a genuine syntactic contextual assignment.
Its body uses the received name and the ambient payload process. -/
def contextualContinuationTerm : ContextualAssignment sig metas G :=
  fun k => by
    have hk : k = (0 : Fin metas.length) := by
      apply Fin.ext
      have bound : k.val < 1 := by
        simpa only [metas, List.length_singleton] using k.isLt
      simp only [Fin.val_zero]
      omega
    subst k
    exact Term.op (S := sig) Op.par
      (.cons
        (Term.op (S := sig) Op.drp (.cons (.var .zero) .nil))
        (.cons (.var (.succ (.succ .zero))) .nil))

/-- An actual authored COMM root occurrence, before quotienting states. -/
def openCommRoot : RootOccurrence rho.rules :=
  ⟨G, ⟨⟨0, by decide⟩,
    { body := contextualContinuationTerm
      close := fun _ x => Term.var x }⟩⟩

/-- This occurrence projects to the rho equation-class model with the
authored COMM index still present. -/
noncomputable def openCommProjected :
    AuthoredPositionedRulePolynomial.RuleInstance rho.rules quotientAlgebra :=
  projectRoot rho.rules rho.eqs openCommRoot

theorem openCommProjected_index : openCommProjected.index.val = 0 := by
  rfl

/-- A semantic continuation using both its received name and the ambient
payload process. The first process drops the name; the second is captured
from the surrounding rule context. -/
noncomputable def contextualContinuation :
    Valuation (M := metas) quotientAlgebra G :=
  fun k => by
    have hk : k = (0 : Fin metas.length) := by
      apply Fin.ext
      have bound : k.val < 1 := by
        simpa only [metas, List.length_singleton] using k.isLt
      simp only [Fin.val_zero]
      omega
    subst k
    exact quotientAlgebra.operation Op.par
      (.cons
        (quotientAlgebra.operation Op.drp
          (.cons (quotientAlgebra.substitution.injectVar Var.zero) .nil))
        (.cons (quotientAlgebra.substitution.injectVar
          (Var.succ (Var.succ Var.zero))) .nil))

/-- A genuine open occurrence of the authored COMM rule; the ordinary
channel and payload variables remain in their declared context. -/
noncomputable def openComm :
    AuthoredPositionedRulePolynomial.RuleInstance rho.rules quotientAlgebra where
  index := ⟨0, by decide⟩
  valuation := contextualContinuation
  ambient := G
  close := fun _ x => quotientAlgebra.substitution.injectVar x

private theorem projectedContinuation :
    mapValuation (S := sig) (M := metas)
      (BindingEquationQuotientModel.projection rho.eqs)
      (contextualContinuationTerm :
        Valuation (M := metas) (BindingCloneAlgebra.terms sig) G) =
      contextualContinuation := by
  funext k
  have hk : k = (0 : Fin metas.length) := by
    apply Fin.ext
    have bound : k.val < 1 := by
      simpa only [metas, List.length_singleton] using k.isLt
    simp only [Fin.val_zero]
    omega
  subst k
  simp only [mapValuation, contextualContinuationTerm,
    contextualContinuation]
  exact (BindingEquationQuotientModel.interpret_eq_mk rho.eqs
    (Term.op (S := sig) Op.par
      (.cons
        (Term.op (S := sig) Op.drp (.cons (.var .zero) .nil))
        (.cons (.var (.succ (.succ .zero))) .nil)))).symm

theorem openCommProjected_eq_openComm : openCommProjected = openComm := by
  dsimp [openCommProjected, projectRoot, openCommRoot, rootEquiv,
    AuthoredPositionedRulePolynomial.mapInstance, openComm]
  congr 1
  · exact projectedContinuation

/-- This authored occurrence contributes a constructor at its exact
contextual, sorted pair of interpreted endpoints. -/
noncomputable def openCommShape :
    AuthoredPositionedRulePolynomial.Shape rho.rules quotientAlgebra
      (AuthoredPositionedRulePolynomial.judgmentOf rho.rules quotientAlgebra openComm) :=
  ⟨openComm, rfl⟩

/-- The authored rho equation quotient with freely generated individual
COMM firing histories is the combined model for this base-rule fragment. -/
noncomputable def rhoPresented :
    AuthoredPositionedRulePolynomial.Model rho.rules rho.eqs :=
  AuthoredPositionedRulePolynomial.presented rho.rules rho.eqs

/-- The rho base-rule fragment receives a unique interpretation into every
model of its binding operators, ACU equations and positioned COMM action. -/
noncomputable def rhoPresentedIsInitial : IsInitial rhoPresented :=
  AuthoredPositionedRulePolynomial.presentedIsInitial rho.rules rho.eqs

/-- Deliberately duplicate the same authored rule while retaining its two
declaration indices. -/
private abbrev duplicateComm : List (PositionedRewrite schemaSig) :=
  [comm, comm]

private noncomputable def firstComm :
    AuthoredPositionedRulePolynomial.RuleInstance duplicateComm quotientAlgebra where
  index := ⟨0, by decide⟩
  valuation := contextualContinuation
  ambient := G
  close := fun _ x => quotientAlgebra.substitution.injectVar x

private noncomputable def secondComm :
    AuthoredPositionedRulePolynomial.RuleInstance duplicateComm quotientAlgebra where
  index := ⟨1, by decide⟩
  valuation := contextualContinuation
  ambient := G
  close := fun _ x => quotientAlgebra.substitution.injectVar x

/-- The duplicate rules have exactly the same sorted semantic endpoints. -/
theorem duplicate_comm_same_judgment :
    AuthoredPositionedRulePolynomial.judgmentOf duplicateComm quotientAlgebra firstComm =
      AuthoredPositionedRulePolynomial.judgmentOf duplicateComm quotientAlgebra secondComm := by
  rfl

private noncomputable def firstShape :
    AuthoredPositionedRulePolynomial.Shape duplicateComm quotientAlgebra
      (AuthoredPositionedRulePolynomial.judgmentOf duplicateComm quotientAlgebra firstComm) :=
  ⟨firstComm, rfl⟩

private noncomputable def secondShape :
    AuthoredPositionedRulePolynomial.Shape duplicateComm quotientAlgebra
      (AuthoredPositionedRulePolynomial.judgmentOf duplicateComm quotientAlgebra firstComm) :=
  ⟨secondComm, duplicate_comm_same_judgment.symm⟩

/-- Equal endpoints do not merge declaration-indexed firing occurrences. -/
theorem duplicate_comm_shapes_distinct : firstShape ≠ secondShape := by
  intro equal
  have indices := congrArg (fun shape :
      AuthoredPositionedRulePolynomial.Shape duplicateComm quotientAlgebra
        (AuthoredPositionedRulePolynomial.judgmentOf duplicateComm quotientAlgebra firstComm) =>
      shape.1.index.val) equal
  norm_num [firstShape, secondShape, firstComm, secondComm] at indices

/-- The freely generated histories also remain distinct, even though their
endpoint judgment is identical. -/
theorem duplicate_comm_trees_distinct :
    (IndexedPolynomial.Fix.roll firstShape (fun (p : Empty) => p.elim) :
      (AuthoredPositionedRulePolynomial.rules duplicateComm quotientAlgebra).Fix ()
        (AuthoredPositionedRulePolynomial.judgmentOf duplicateComm quotientAlgebra firstComm)) ≠
    IndexedPolynomial.Fix.roll secondShape (fun (p : Empty) => p.elim) := by
  intro equal
  have shapes := congrArg
    (fun tree : (AuthoredPositionedRulePolynomial.rules duplicateComm quotientAlgebra).Fix ()
        (AuthoredPositionedRulePolynomial.judgmentOf duplicateComm quotientAlgebra firstComm) =>
      ((IndexedPolynomial.Fix.out
        (AuthoredPositionedRulePolynomial.rules duplicateComm quotientAlgebra) tree).1))
    equal
  exact duplicate_comm_shapes_distinct shapes

#print axioms rhoPresentedIsInitial
#print axioms openCommProjected_eq_openComm
#print axioms duplicate_comm_same_judgment
#print axioms duplicate_comm_shapes_distinct
#print axioms duplicate_comm_trees_distinct

end Mettapedia.OSLF.Binding.RhoPositionedOperationalModel
