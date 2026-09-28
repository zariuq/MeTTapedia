import Mettapedia.OSLF.Syntax.RhoRulePolynomialMorphism
import Mettapedia.OSLF.Syntax.IndexedOperationalModelsOver

/-!
# Initial binding-equation-and-rule model for the intrinsic rho presentation

The binding-clone model category records all authored equations. The rho
rule-presentation functor attaches COMM, Drop, and recursive ParCong to each
such model, and the indexed free-algebra construction adjoins proof-relevant
firing trees. The relative adjunction and initiality therefore apply to the
combined intrinsic source-equation and rule scheme. A separate comparison is
still required for the canonical LanguageDef hash-bag/collection-rest syntax
and for the additional chosen function structure of the full classifier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoEquationRuleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
open Mettapedia.OSLF.Binding.RhoRulePolynomialMorphism

variable (E : List (EqAxiom sig metas))

/-- Rho rules are functorial over all models of a selected equation list,
including models of the complete Chapter 7 source equations. -/
noncomputable def presentationFunctor :
    FreeBindingEquationModel.Model.{0} E ⥤
      IndexedRulePresentationCategory.Presentation Unit where
  obj X := rhoPresentation X.algebra
  map h := rhoPresentationMap h
  map_id := by intro X; exact rhoPresentationMap_id X.algebra
  map_comp := by
    intro X Y Z first later
    exact rhoPresentationMap_comp first later

/-- An equation model equipped with an algebra interpreting individual
rho firing histories and all recursive ParCong premises. -/
abbrev Model := IndexedOperationalModelsOver.Model (presentationFunctor E)

abbrev Hom (X Y : Model E) :=
  IndexedOperationalModelsOver.Hom (presentationFunctor E) X Y

/-- The free proof-relevant rho rule algebra over any selected equation
model is left adjoint to forgetting that algebra. -/
noncomputable def freeAdjunction :
    IndexedOperationalModelsOver.freeFunctor (presentationFunctor E) ⊣
      IndexedOperationalModelsOver.forget (presentationFunctor E) :=
  IndexedOperationalModelsOver.freeAdjunction (presentationFunctor E)

/-- The presented equation quotient with freely generated COMM, Drop, and
ParCong firing histories. -/
noncomputable def presented : Model E :=
  IndexedOperationalModelsOver.free (presentationFunctor E)
    (FreeBindingEquationModel.presented E)

/-- A lawful semantic equation/rule model receives a unique interpretation
of the presented syntax and every retained recursive firing tree. -/
noncomputable def interpret (target : Model E) :
    Hom E (presented E) target :=
  IndexedOperationalModelsOver.initialHom (presentationFunctor E)
    (FreeBindingEquationModel.presentedIsInitial E) target

/-- The base of the combined interpretation is the existing unique
binding-equation interpretation. -/
theorem interpret_base (target : Model E) :
    (interpret E target).base =
      FreeBindingEquationModel.interpretHom target.base := by
  rfl

/-- The combined intrinsic equation-and-rule presentation is initial among
the corresponding small semantic models. Initiality includes map uniqueness
for substitution, equations, constructor actions, and recursive evidence. -/
noncomputable def presentedIsInitial : IsInitial (presented E) :=
  IndexedOperationalModelsOver.freeIsInitial (presentationFunctor E)
    (FreeBindingEquationModel.presentedIsInitial E)

/-- The actual full source equation list is a concrete instance of the
combined intrinsic rho initiality theorem. -/
noncomputable def sourcePresented : Model rhoSourceE :=
  presented rhoSourceE

noncomputable def sourcePresentedIsInitial :
    IsInitial sourcePresented :=
  presentedIsInitial rhoSourceE

private abbrev raw := BindingCloneAlgebra.terms sig

private noncomputable abbrev sourceAlgebra :=
  (FreeBindingEquationModel.presented rhoSourceE).algebra

/-- The raw syntax generates a genuine COMM firing tree for any authored
continuation body, with no recursive premise invented. -/
def rawCommTree (body : Term sig [Srt.nm] Srt.pr) :
    (rules raw).Fix ()
      (judgment raw
        (commSource raw (Term.var Var.zero)
          (Term.var (Var.succ Var.zero)) (openContinuation body))
        (commTarget raw (Term.var (Var.succ Var.zero))
          (openContinuation body))) :=
  .roll (RuleShape.comm (A := raw) (Γ := G)
    (Term.var Var.zero) (Term.var (Var.succ Var.zero))
    (openContinuation body)) (fun impossible => impossible.elim)

/-- The source-equation quotient receives that same complete constructor
history through the cartesian rule-presentation map. -/
noncomputable def sourceCommTree (body : Term sig [Srt.nm] Srt.pr) :
    (rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw
          (commSource raw (Term.var Var.zero)
            (Term.var (Var.succ Var.zero)) (openContinuation body))
          (commTarget raw (Term.var (Var.succ Var.zero))
            (openContinuation body)))) :=
  interpretTree (FreeBindingClone.interpretHom sourceAlgebra) _
    (rawCommTree body)

/-- Reading the tree at the exact instantiated authored schema judgment
uses the general source/target comparison, not a special closed reduction. -/
theorem sourceCommTree_authored_index
    (body : Term sig [Srt.nm] Srt.pr) :
    Nonempty ((rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw
          (instantiate (singleBody body) commLhs)
          (instantiate (singleBody body) commRhs)))) := by
  rw [← raw_comm_source_body, ← raw_comm_target_body]
  exact ⟨sourceCommTree body⟩

/-- The separately authored Drop rule has a one-node firing history in the
same combined semantic presentation. -/
def rawDropTree :
    (rules raw).Fix ()
      (judgment raw
        (drop raw (quote raw (Term.var (Var.zero : Var [Srt.pr] .pr))))
        (Term.var Var.zero)) :=
  .roll (RuleShape.drop (A := raw) (Γ := [Srt.pr])
    (Term.var Var.zero)) (fun impossible => impossible.elim)

noncomputable def sourceDropTree :
    (rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw
          (drop raw (quote raw (Term.var (Var.zero : Var [Srt.pr] .pr))))
          (Term.var Var.zero))) :=
  interpretTree (FreeBindingClone.interpretHom sourceAlgebra) _
    rawDropTree

theorem sourceDropTree_authored_index :
    Nonempty ((rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw (instantiate contDiscard dropLhs)
          (instantiate contDiscard dropRhs)))) := by
  change Nonempty ((rules sourceAlgebra).Fix ()
    (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
      (judgment raw
        (drop raw (quote raw (Term.var (Var.zero : Var [Srt.pr] .pr))))
        (Term.var Var.zero))))
  exact ⟨sourceDropTree⟩

end Mettapedia.OSLF.Binding.RhoEquationRuleModels
