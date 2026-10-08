import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedCommunicationReadout
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationValues
import Mettapedia.CategoryTheory.RelativeClosedSyntaxAbstractionComparison

/-!
# Fetch evidence inside the independently generated operational guest

An actual unary COMM generator receives the complete stored continuation.
Currying its evidence in the return name earns both whole source and target
function equations. All inputs are categorical arrows, rather than selected
syntactically represented receiver bodies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperational

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
open NamePassingContinuationOperations NamePassingContinuationValues

universe k

abbrev Target := BindingClosedGeneratedOperationalModel.Target.{k}
abbrev binding := BindingClosedGeneratedOperationalModel.binding.{k}
abbrev ordinary := BindingClosedGeneratedOperationalModel.ordinary.{k}
abbrev category := BindingClosedGeneratedOperationalModel.category.{k}
abbrev source := BindingClosedGeneratedCommunicationReadout.source.{k}
abbrev target := BindingClosedGeneratedCommunicationReadout.target.{k}

abbrev fetchDomain := ordinary.{k}.names ⊗ ordinary.termObject

def fetchBody : fetchDomain.{k} ⊗ ordinary.names ⟶ category.edge :=
  BindingClosedGeneratedCommunicationReadout.unary
    (fst fetchDomain ordinary.names ≫ fst ordinary.names ordinary.termObject)
    (snd fetchDomain ordinary.names)
    (fst fetchDomain ordinary.names ≫ snd ordinary.names ordinary.termObject)

def fetch : fetchDomain.{k} ⟶ (ordinary.names ⟶[Target] category.edge) :=
  abstraction fetchBody

def fetchSource : fetchDomain.{k} ⟶ ordinary.termObject :=
  lift (fst ordinary.names ordinary.termObject)
    (lift (snd ordinary.names ordinary.termObject)
      (fst ordinary.names ordinary.termObject ≫ ordinary.reference)) ≫ ordinary.carrier

theorem fetch_before {Z : Target.{k}} (name result : Z ⟶ ordinary.names)
    (value : Z ⟶ ordinary.termObject) :
    call (lift name (lift value (name ≫ ordinary.reference)) ≫ ordinary.carrier) result =
      BindingClosedGeneratedCommunicationReadout.unary name result value ≫ source := by
  rw [carrier_value, BindingClosedGeneratedCommunicationReadout.unary_source]
  unfold Operations.reference
  rw [call_abstraction]

theorem fetchBody_source : fetchBody.{k} ≫ source =
    call (fst fetchDomain ordinary.names ≫ fetchSource) (snd fetchDomain ordinary.names) := by
  have read := fetch_before
    (fst fetchDomain ordinary.names ≫ fst ordinary.names ordinary.termObject)
    (snd fetchDomain ordinary.names)
    (fst fetchDomain ordinary.names ≫ snd ordinary.names ordinary.termObject)
  have complete : fst fetchDomain ordinary.names ≫ fetchSource =
      lift (fst fetchDomain ordinary.names ≫ fst ordinary.names ordinary.termObject)
        (lift (fst fetchDomain ordinary.names ≫ snd ordinary.names ordinary.termObject)
          ((fst fetchDomain ordinary.names ≫ fst ordinary.names ordinary.termObject) ≫ ordinary.reference)) ≫
            ordinary.carrier := by
    simp only [fetchSource, comp_lift_assoc, comp_lift, Category.assoc]
  rw [complete]
  exact read.symm

theorem fetchBody_target : fetchBody.{k} ≫ target =
    call (fst fetchDomain ordinary.names ≫ snd ordinary.names ordinary.termObject)
      (snd fetchDomain ordinary.names) := by
  rw [fetchBody, BindingClosedGeneratedCommunicationReadout.unary_target]
  exact (NamePassingBindingClosedSchemas.call_as_evaluation _ _).symm

theorem fetch_source : fetch.{k} ≫ (ihom ordinary.names).map source = fetchSource := by
  rw [fetch, abstraction_postcomposition, fetchBody_source]
  exact abstraction_evaluation fetchSource

theorem fetch_target : fetch.{k} ≫ (ihom ordinary.names).map target =
    snd ordinary.names ordinary.termObject := by
  rw [fetch, abstraction_postcomposition, fetchBody_target]
  exact abstraction_evaluation (snd ordinary.names ordinary.termObject)

theorem fetch_substitution {W : Target.{k}} (change : W ⟶ fetchDomain) :
    change ≫ fetch = abstraction (change ▷ ordinary.names ≫ fetchBody) :=
  abstraction_natural change fetchBody

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperational
