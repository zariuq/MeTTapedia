import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLImpredicativeRepresentation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLSignatureDenotation

/-!
# Total HOL translation in the signature-generic native denotation

The partial representation of primitive HOL terms becomes total through the
existing impredicative expansion. This module connects that *computed* total
translation to the same native semantic judgment used by the signature-generic
representation square. Source denotation is preserved in every Henkin model;
no separate interpretation of derived connectives is installed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLImpredicativeDenotation

open Mettapedia.Logic
open Mettapedia.Logic.HOL.ImpredicativeConnectives
open HOLImpredicativeRepresentation
open FormationSensitiveHOLInterface
open NativeHOLSignatureDenotation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe u v w
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (signature : LogicalSignature Base Const)
  (model : HOL.HenkinModel.{u, v, w} Base Const)

/-- Every source HOL term, including derived logical connectives, has its
computed total native translation in the existing signature denotation.
The equation is the independently proved impredicative expansion law, not a
new meaning assigned to unsupported source constructors. -/
theorem translate_denotes {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term Const gamma type) :
    Denotes signature model (translate signature term)
      (fun valuation => model.denote term valuation) := by
  have represented := translate_eq signature term
  have interpreted := representation_square (signature := signature) (model := model)
    (expand term) represented
  simpa only [HOL.ImpredicativeConnectives.denote_expand] using interpreted

/-- A closed source definition body retains that source meaning when lifted
into any later HOL context. This is the denotation of the actual native
delta *target*, before any claim about the defined native name. -/
theorem translate_closed_denotes {type : HOL.Ty Base}
    (body : HOL.Term Const [] type) (gamma : HOL.Ctx Base) :
    Denotes signature model (gamma := gamma) (type := type)
      (liftClosed (translate signature body))
      (fun _ => model.denote body (fun index => nomatch index)) := by
  have base := translate_denotes signature model body
  let emptyRename : HOL.Rename Base [] gamma := fun index => nomatch index
  have lifted := base.rename
    (delta := gamma) emptyRename Fin.elim0
    (by intro type index; nomatch index)
  have sameValue :
      (fun valuation : model.Valuation gamma =>
        model.denote body
          (HOL.Soundness.renameVal model emptyRename valuation)) =
      (fun _ => model.denote body (fun index => nomatch index)) := by
    funext valuation
    congr 1
    funext type index
    nomatch index
  rw [sameValue] at lifted
  simpa only [liftClosed] using lifted

/-- Source β and its actual translated native contraction preserve one value
even when the argument computes and the body contains derived connectives.
Both native terms are constructed in the same denotation relation. -/
theorem translated_beta_square {gamma : HOL.Ctx Base}
    {domain codomain : HOL.Ty Base}
    (body : HOL.Term Const (domain :: gamma) codomain)
    (argument : HOL.Term Const gamma domain) :
    translate signature (.app (.lam body) argument) =
      .app (.lam (translate signature body)) (translate signature argument) ∧
    translate signature (HOL.instantiate argument body) =
      inst0 (translate signature argument) (translate signature body) ∧
    Denotes signature model (translate signature (.app (.lam body) argument))
      (fun valuation => model.denote (.app (.lam body) argument) valuation) ∧
    Denotes signature model (translate signature (HOL.instantiate argument body))
      (fun valuation => model.denote (.app (.lam body) argument) valuation) ∧
    ∀ valuation, model.denote (.app (.lam body) argument) valuation =
      model.denote (HOL.instantiate argument body) valuation := by
  have translatedRedex := translate_app signature (.lam body) argument
  have translatedBody := translate_lam signature body
  have translatedContractum := translate_instantiate signature argument body
  have compared := Denotes.beta
    (translate_denotes signature model body)
    (translate_denotes signature model argument)
  refine ⟨by rw [translatedRedex, translatedBody], translatedContractum,
    ?_, ?_, ?_⟩
  · simpa only [translatedRedex, translatedBody,
      HOL.HenkinModel.denote, HOL.PreModel.denote] using compared.1
  · rw [translatedContractum]
    simpa only [HOL.HenkinModel.denote, HOL.PreModel.denote] using compared.2
  · intro valuation
    rw [HOL.Soundness.denote_instantiate_term]
    rfl

/-- Total translation also respects η for a weakened function, including a
function whose source term uses derived logical connectives. -/
theorem translated_eta_square {gamma : HOL.Ctx Base}
    {domain codomain : HOL.Ty Base}
    (function : HOL.Term Const gamma (.arr domain codomain)) :
    translate signature
      (.lam (.app (HOL.weaken (σ := domain) function) (.var .vz))) =
      .lam (.app (rename wk (translate signature function)) (.var 0)) ∧
    Denotes signature model
      (translate signature
        (.lam (.app (HOL.weaken (σ := domain) function) (.var .vz))))
      (fun valuation => model.denote function valuation) ∧
    ∀ valuation, model.denote
      (.lam (.app (HOL.weaken (σ := domain) function) (.var .vz))) valuation =
      model.denote function valuation := by
  have weakened : translate signature (HOL.weaken (σ := domain) function) =
      rename wk (translate signature function) := by
    simpa only [HOL.weaken] using
      translate_rename signature HOL.Rename.weaken wk (fun _ => rfl) function
  have translated : translate signature
      (.lam (.app (HOL.weaken (σ := domain) function) (.var .vz))) =
      .lam (.app (rename wk (translate signature function)) (.var 0)) := by
    simp only [translate_lam, translate_app, weakened, translate_var, variableIndex]
  refine ⟨translated, ?_, ?_⟩
  · rw [translated]
    exact (translate_denotes signature model function).eta
  · intro valuation
    funext x
    change model.denote (HOL.weaken (σ := domain) function)
      (model.extend valuation x) x = model.denote function valuation x
    rw [HOL.Soundness.denote_weaken]

namespace Controls

private def computedArgument : HOL.Term Const [.prop] .prop :=
  .app (.lam (.var .vz)) (.var .vz)

private def derivedBody : HOL.Term Const [.prop, .prop] .prop :=
  .and (.var .vz) (.var (.vs .vz))

private def falseConjunction : HOL.ClosedFormula Const := .and .top .bot

/-- The argument in the worked β instance really computes; it is not a
renamed source variable. -/
theorem computed_argument_not_variable :
    (computedArgument (Const := Const)) ≠ HOL.Term.var .vz := by
  intro impossible
  cases impossible

/-- A derived conjunction inside the body and a computed argument are both
handled by the total β square, not by a fragment-specific interpreter. -/
theorem derived_body_computed_argument_beta :
    Denotes signature model
      (translate signature
        (HOL.instantiate (computedArgument (Const := Const))
          (derivedBody (Const := Const))))
      (fun valuation => model.denote
        (.app (.lam (derivedBody (Const := Const)))
          (computedArgument (Const := Const))) valuation) :=
  (translated_beta_square signature model
    (derivedBody (Const := Const)) (computedArgument (Const := Const))).2.2.2.1

/-- Denotability of a derived formula is not its proof or truth. The false
conjunction is translated, but no Henkin model satisfies it. -/
theorem translated_false_is_not_valid :
    Denotes signature model (translate signature (falseConjunction (Const := Const)))
      (fun valuation => model.denote (falseConjunction (Const := Const)) valuation) ∧
    ¬ model.models (falseConjunction (Const := Const)) := by
  refine ⟨translate_denotes signature model (falseConjunction (Const := Const)), ?_⟩
  intro assumed
  exact (HOL.ImpredicativeConnectives.not_models_expanded_false model)
    ((HOL.ImpredicativeConnectives.models_expand model _).mpr assumed)

end Controls

#print axioms translate_denotes
#print axioms translate_closed_denotes
#print axioms translated_beta_square
#print axioms translated_eta_square
#print axioms Controls.computed_argument_not_variable
#print axioms Controls.derived_body_computed_argument_beta
#print axioms Controls.translated_false_is_not_valid

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLImpredicativeDenotation
