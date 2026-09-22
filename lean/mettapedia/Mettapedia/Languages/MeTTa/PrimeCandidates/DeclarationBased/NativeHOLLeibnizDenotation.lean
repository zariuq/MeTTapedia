import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLFragmentDenotation

/-!
# Constructorwise meaning of native predicate equality

The alternative equality expression is interpreted by the existing native
semantic judgment, not by an additional equality clause. On admissible
valuations its predicate meaning agrees with the original Henkin equality.
Native substitution reindexes the same comparison. This interprets the
equality expression, not arbitrary inhabitants of the native proof decoder.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeHOLLeibnizDenotation

open Presentation FormationSensitiveHOLInterface
open FormationSensitiveHOLUniformList (types rawImp rawAll)
open FormationSensitiveHOLLeibnizInterface (rawLeibniz equality sourceEquality)
open NativeHOLFragmentDenotation
open Mettapedia.Logic HOL.UniformListInduction

universe w
variable {model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol}

def predicateEquality (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol)
    (type : HOL.Ty BaseSort) (x y : HOL.Ty.denote model.Carrier type) :
    HOL.Ty.denote model.Carrier .prop :=
  ULift.up (∀ predicate : HOL.Ty.denote model.Carrier (.arr type .prop),
    model.adm (.arr type .prop) predicate → (predicate x).down → (predicate y).down)

theorem equality_denotes (type : HOL.Ty BaseSort) :
    Denotes model (gamma := []) (type := .arr type (.arr type .prop)) (equality type)
      (fun _ x y => predicateEquality model type x y) := by
  simpa only [sourceEquality, HOLLeibnizProofComparison.Source.leibniz,
    HOL.weaken, HOL.rename, HOL.Rename.weaken, HOL.HenkinModel.denote,
    HOL.PreModel.denote, HOL.PreModel.extend, predicateEquality] using
    (representation_square (model := model) (sourceEquality type)
      (FormationSensitiveHOLLeibnizInterface.sourceEquality_represented type))

theorem equality_denotes_at {gamma : HOL.Ctx BaseSort} (type : HOL.Ty BaseSort) :
    Denotes model (gamma := gamma) (type := .arr type (.arr type .prop))
      (liftClosed (equality type))
      (fun _ x y => predicateEquality model type x y) := by
  exact (equality_denotes type).rename (fun index => nomatch index) Fin.elim0
    (fun index => nomatch index)

theorem application_denotes {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm gamma.length}
    {left right : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (hx : Denotes model x left) (hy : Denotes model y right) :
    Denotes model (type := .prop) (.app (.app (liftClosed (equality type)) x) y)
      (fun valuation => predicateEquality model type (left valuation) (right valuation)) :=
  .application (.application (equality_denotes_at type) hx) hy

theorem raw_denotes {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm gamma.length}
    {left right : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (hx : Denotes model x left) (hy : Denotes model y right) :
    Denotes model (type := .prop) (rawLeibniz type x y)
      (fun valuation => predicateEquality model type (left valuation) (right valuation)) := by
  have xw := hx.rename (HOL.Rename.weaken (σ := .arr type .prop)) wk (fun _ => rfl)
  have yw := hy.rename (HOL.Rename.weaken (σ := .arr type .prop)) wk (fun _ => rfl)
  have px := Denotes.application (a := type) (b := .prop) (Denotes.index (model := model)
    (HOL.Var.vz : HOL.Var (.arr type .prop :: gamma) (.arr type .prop))) xw
  have py := Denotes.application (a := type) (b := .prop) (Denotes.index (model := model)
    (HOL.Var.vz : HOL.Var (.arr type .prop :: gamma) (.arr type .prop))) yw
  have implication := Denotes.application (a := .prop) (b := .prop)
    (Denotes.application (a := .prop) (b := .arr .prop .prop) Denotes.implication px) py
  have universal := Denotes.application (a := .arr (.arr type .prop) .prop) (b := .prop)
    (Denotes.universal (model := model) (typeAt_meaning gamma.length (.arr type .prop)))
    (Denotes.abstraction implication)
  have forget (valuation : model.Valuation gamma)
      (predicate : HOL.Ty.denote model.Carrier (.arr type .prop)) :
      @Eq (model.Valuation gamma)
        (fun {a} index => HOL.Soundness.renameVal model
          (HOL.Rename.weaken (σ := .arr type .prop)) (model.extend valuation predicate) index)
        valuation := by
    funext a index
    rfl
  simpa only [rawLeibniz, rawAll, rawImp, FormationSensitiveHOLUniformList.universal,
    liftClosed, rename, typeAt_rename, forget,
    HOL.HenkinModel.extend, HOL.PreModel.extend, HOL.Rename.weaken,
    predicateEquality, variableIndex] using universal

/-- Henkin closure supplies source witnesses for the interpreted operands;
the already retained source comparison then proves the semantic agreement.
Full predicate domains are not assumed. -/
theorem predicateEquality_iff_eqv {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm gamma.length}
    {left right : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (hx : Denotes model x left) (hy : Denotes model y right)
    (respects : model.FunctionsRespectEqv) {valuation : model.Valuation gamma}
    (admissible : model.ValuationAdmissible valuation) :
    (predicateEquality model type (left valuation) (right valuation)).down ↔
      model.Eqv type (left valuation) (right valuation) := by
  obtain ⟨sourceX, meaningX⟩ := hx.source_denotation
  obtain ⟨sourceY, meaningY⟩ := hy.source_denotation
  have comparison := HOLLeibnizZFSetInterpretation.leibniz_iff_primitive model respects
    sourceX sourceY ⟨valuation, admissible⟩
  simpa only [predicateEquality, meaningX valuation, meaningY valuation,
    HOLLeibnizProofComparison.Source.leibniz, HOL.HenkinModel.denote,
    HOL.PreModel.denote, HOL.Soundness.denote_weaken, HOL.PreModel.extend] using comparison

/-- Independently interpreted redex and contractum have the same value,
and that value is the original HOL equality on the admitted environment. -/
theorem equality_square {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm gamma.length}
    {left right : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (hx : Denotes model x left) (hy : Denotes model y right)
    (respects : model.FunctionsRespectEqv) {valuation : model.Valuation gamma}
    (admissible : model.ValuationAdmissible valuation) :
    Conv FormationSensitiveHOLLeibnizInterface.rules.headEq
        (.app (.app (liftClosed (equality type)) x) y) (rawLeibniz type x y)
        FormationSensitiveHOLLeibnizInterface.rules.computation ∧
      Denotes model (type := .prop) (.app (.app (liftClosed (equality type)) x) y)
        (fun rho => predicateEquality model type (left rho) (right rho)) ∧
      Denotes model (type := .prop) (rawLeibniz type x y)
        (fun rho => predicateEquality model type (left rho) (right rho)) ∧
      ((predicateEquality model type (left valuation) (right valuation)).down ↔
        model.Eqv type (left valuation) (right valuation)) :=
  ⟨FormationSensitiveHOLLeibnizInterface.equality_application_conversion type x y,
    application_denotes hx hy, raw_denotes hx hy,
    predicateEquality_iff_eqv hx hy respects admissible⟩

/-- The semantic environment is supplied by interpretations of the actual
native substitution components. No source substitution is required. -/
theorem equality_substitution_square {gamma delta : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort} {x y : Tower.Tm gamma.length}
    {left right : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (hx : Denotes model x left) (hy : Denotes model y right)
    (sigma : Sub Tower.Head gamma.length delta.length)
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {a} (index : HOL.Var gamma a),
      Denotes model (type := a) (sigma (variableIndex index))
        (fun valuation => environment valuation index))
    (respects : model.FunctionsRespectEqv) {valuation : model.Valuation delta}
    (admissible : model.ValuationAdmissible valuation) :
    subst sigma (rawLeibniz type x y) = rawLeibniz type (subst sigma x) (subst sigma y) ∧
      Denotes model (type := .prop) (subst sigma (rawLeibniz type x y))
        (fun rho => predicateEquality model type (left (environment rho)) (right (environment rho))) ∧
      ((predicateEquality model type (left (environment valuation)) (right (environment valuation))).down ↔
        model.Eqv type (left (environment valuation)) (right (environment valuation))) :=
  ⟨FormationSensitiveHOLLeibnizInterface.rawLeibniz_subst sigma type x y,
    (raw_denotes hx hy).substitute sigma environment components,
    predicateEquality_iff_eqv hx hy respects
      (interpreted_environment_admissible sigma environment components admissible)⟩

/-- Coherence prohibits an independently interpreted equality expression
from asserting truth at an environment where its operands are unequal. -/
theorem unequal_operands_not_true {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm gamma.length}
    {left right : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (hx : Denotes model x left) (hy : Denotes model y right)
    (respects : model.FunctionsRespectEqv) {valuation : model.Valuation gamma}
    (admissible : model.ValuationAdmissible valuation)
    (unequal : ¬ model.Eqv type (left valuation) (right valuation))
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier .prop}
    (meaning : Denotes model (rawLeibniz type x y) value) :
    ¬ (value valuation).down := by
  rw [meaning.coherent (raw_denotes hx hy) valuation]
  exact fun holds => unequal ((predicateEquality_iff_eqv hx hy respects admissible).mp holds)

namespace Controls

abbrev standard := StandardListModel.model
abbrev gamma : HOL.Ctx BaseSort := [element, element]

def valuation : standard.Valuation gamma :=
  standard.extend (Γ := [element]) (σ := element)
    (standard.extend (Γ := []) (σ := element) (fun index => nomatch index)
    (show StandardListModel.LiftedElement from ⟨false⟩))
    (show StandardListModel.LiftedElement from ⟨true⟩)

theorem valuation_admissible : standard.ValuationAdmissible valuation := by
  intro a index
  trivial

theorem standard_respects : standard.FunctionsRespectEqv :=
  standard.functionsRespectEqv_of_fullDomains
    (HOL.HenkinModel.fullDomains_standard StandardListModel.carrier StandardListModel.constant)

theorem same_operand_holds :
    (predicateEquality standard element (valuation HOL.Var.vz) (valuation HOL.Var.vz)).down := by
  intro predicate _ witness
  exact witness

theorem changed_operand_fails :
    ¬ (predicateEquality standard element (valuation HOL.Var.vz)
      (valuation (HOL.Var.vs HOL.Var.vz))).down := by
  have comparison := predicateEquality_iff_eqv
    (Denotes.index (model := standard) (HOL.Var.vz : HOL.Var gamma element))
    (Denotes.index (model := standard) (HOL.Var.vs HOL.Var.vz : HOL.Var gamma element))
    standard_respects valuation_admissible
  intro holds
  have equal := comparison.mp holds
  change (ULift.up true : StandardListModel.LiftedElement) = ULift.up false at equal
  cases equal

theorem changed_operand_not_true_denotation :
    ¬ Denotes standard (gamma := gamma) (type := .prop)
      (rawLeibniz element (.var 0) (.var 1)) (fun _ => ULift.up True) := by
  intro meaning
  have unique := meaning.coherent
    (raw_denotes (Denotes.index (model := standard) (HOL.Var.vz : HOL.Var gamma element))
      (Denotes.index (model := standard) (HOL.Var.vs HOL.Var.vz : HOL.Var gamma element))) valuation
  apply changed_operand_fails
  exact Eq.mp (congrArg ULift.down unique) True.intro

end Controls

#print axioms equality_denotes
#print axioms raw_denotes
#print axioms predicateEquality_iff_eqv
#print axioms equality_square
#print axioms equality_substitution_square
#print axioms unequal_operands_not_true
#print axioms Controls.same_operand_holds
#print axioms Controls.changed_operand_fails
#print axioms Controls.changed_operand_not_true_denotation

end NativeHOLLeibnizDenotation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
