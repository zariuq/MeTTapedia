import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLLeibnizDenotation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizRepresentation

/-!
# Source adequacy of the predicate-equality representation

Expansion of equality is a traversal of the original HOL term. The old
native representation of that expanded term is exactly the alternative
representation of the original. Henkin semantics independently proves the
expansion preserves extensional meaning on admissible valuations. Together
these facts interpret complete represented formulas, not just one equality
application. No full-domain or native proof-term model is asserted.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizRepresentationSemantics

open Mettapedia.Logic HOL.UniformListInduction
open Presentation FormationSensitiveHOLInterface NativeHOLFragmentDenotation

universe w
variable {model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol}

theorem equalityAt_denote {gamma : HOL.Ctx BaseSort} (type : HOL.Ty BaseSort)
    (valuation : model.Valuation gamma) :
    model.denote (equalityAt gamma type) valuation =
      (fun x y => NativeHOLLeibnizDenotation.predicateEquality model type x y) := by
  exact (representation_square (model := model) _ (equalityAt_represented gamma type)).coherent
    (NativeHOLLeibnizDenotation.equality_denotes_at type) valuation

private theorem eqv_congr {type : HOL.Ty BaseSort}
    {x y x' y' : HOL.Ty.denote model.Carrier type}
    (hx : model.Eqv type x x') (hy : model.Eqv type y y') :
    model.Eqv type x y ↔ model.Eqv type x' y' :=
  ⟨fun h => model.eqv_trans (model.eqv_symm hx) (model.eqv_trans h hy),
    fun h => model.eqv_trans hx (model.eqv_trans h (model.eqv_symm hy))⟩

theorem expansion_meaning {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (term : Expr gamma type) (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation gamma) (admissible : model.ValuationAdmissible valuation) :
    model.Eqv type (model.denote (expand term) valuation) (model.denote term valuation) := by
  induction term with
  | var index => exact model.eqv_refl (admissible index)
  | const symbol => exact model.eqv_refl (model.const_mem symbol)
  | app f x ihf ihx =>
      exact model.eqv_trans
        (model.eqv_arr_apply (ihf valuation admissible)
          (model.denote_admissible admissible (expand x)))
        (respects (model.denote_admissible admissible f)
          (model.denote_admissible admissible (expand x))
          (model.denote_admissible admissible x) (ihx valuation admissible))
  | lam body ih =>
      intro x hx
      exact ih (model.extend valuation x) (model.extend_admissible admissible hx)
  | top | bot => exact Iff.rfl
  | «and» p q ihp ihq => exact and_congr (ihp valuation admissible) (ihq valuation admissible)
  | «or» p q ihp ihq => exact or_congr (ihp valuation admissible) (ihq valuation admissible)
  | imp p q ihp ihq => exact imp_congr (ihp valuation admissible) (ihq valuation admissible)
  | «not» p ih => exact not_congr (ih valuation admissible)
  | all p ih =>
      constructor
      · intro holds x hx
        exact (ih (model.extend valuation x) (model.extend_admissible admissible hx)).mp (holds x hx)
      · intro holds x hx
        exact (ih (model.extend valuation x) (model.extend_admissible admissible hx)).mpr (holds x hx)
  | ex p ih =>
      constructor
      · rintro ⟨x, hx, hp⟩
        exact ⟨x, hx, (ih (model.extend valuation x) (model.extend_admissible admissible hx)).mp hp⟩
      · rintro ⟨x, hx, hp⟩
        exact ⟨x, hx, (ih (model.extend valuation x) (model.extend_admissible admissible hx)).mpr hp⟩
  | @eq gamma a x y ihx ihy =>
      change (model.denote (.app (.app (equalityAt gamma a) (expand x)) (expand y)) valuation).down ↔ _
      simp only [HOL.HenkinModel.denote, HOL.PreModel.denote, equalityAt_denote]
      have compared := HOLLeibnizZFSetInterpretation.leibniz_iff_primitive model respects
        (expand x) (expand y) ⟨valuation, admissible⟩
      have equality :
          (NativeHOLLeibnizDenotation.predicateEquality model a
            (model.denote (expand x) valuation) (model.denote (expand y) valuation)).down ↔
          model.Eqv a (model.denote (expand x) valuation) (model.denote (expand y) valuation) := by
        simpa only [NativeHOLLeibnizDenotation.predicateEquality,
          HOLLeibnizProofComparison.Source.leibniz, HOL.HenkinModel.denote,
          HOL.PreModel.denote, HOL.Soundness.denote_weaken, HOL.PreModel.extend] using compared
      exact equality.trans (eqv_congr (ihx valuation admissible) (ihy valuation admissible))

/-- The complete alternate representation has the old source meaning up
to its existing typed Henkin equality, not a postulated native meaning. -/
theorem native_representation_meaning {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (term : Expr gamma type) {code : Tower.Tm gamma.length}
    (represented : represent New.signature term = some code)
    (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation gamma) (admissible : model.ValuationAdmissible valuation) :
    Denotes model code (fun rho => model.denote (expand term) rho) ∧
      model.Eqv type (model.denote (expand term) valuation) (model.denote term valuation) :=
  ⟨representation_square _ ((representation_expand term).trans represented),
    expansion_meaning term respects valuation admissible⟩

/-- Every independent native interpretation of a represented proposition
has exactly the original source truth value on admissible environments. -/
theorem formula_meaning {gamma : HOL.Ctx BaseSort} (formula : Sentence gamma)
    {code : Tower.Tm gamma.length} (represented : represent New.signature formula = some code)
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier .prop}
    (meaning : Denotes model code value) (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation gamma) (admissible : model.ValuationAdmissible valuation) :
    (value valuation).down ↔ (model.denote formula valuation).down := by
  obtain ⟨canonical, agrees⟩ := native_representation_meaning formula represented respects valuation admissible
  rw [meaning.coherent canonical valuation]
  exact agrees

namespace Controls

abbrev standard := StandardListModel.model
def valuation : standard.Valuation [] := fun index => nomatch index

theorem admissible : standard.ValuationAdmissible valuation := by
  intro a index
  exact nomatch index

def falseClaim : Sentence [] := .eq (.const .zero) (.app (.const .succ) (.const .zero))
def trueClaim : Sentence [] := .eq (.const .zero) (.const .zero)

def falseCode : Tower.Tm 0 :=
  .app (.app (FormationSensitiveHOLLeibnizInterface.equality count)
    (.const (FormationSensitiveHOLUniformList.symbolName Symbol.zero)))
    (.app (.const (FormationSensitiveHOLUniformList.symbolName Symbol.succ))
      (.const (FormationSensitiveHOLUniformList.symbolName Symbol.zero)))

theorem falseClaim_represented : represent New.signature falseClaim = some falseCode := rfl

theorem expanded_trueClaim_holds : (standard.denote (expand trueClaim) valuation).down := by
  apply (expansion_meaning trueClaim NativeHOLLeibnizDenotation.Controls.standard_respects
    valuation admissible).mpr
  rfl

theorem expanded_falseClaim_fails : ¬ (standard.denote (expand falseClaim) valuation).down := by
  intro holds
  have impossible := (expansion_meaning falseClaim
    NativeHOLLeibnizDenotation.Controls.standard_respects valuation admissible).mp holds
  change (ULift.up 0 : StandardListModel.LiftedCount) = ULift.up 1 at impossible
  cases impossible

theorem native_falseClaim_not_true :
    ¬ Denotes standard (gamma := []) (type := .prop) falseCode (fun _ => ULift.up True) := by
  intro meaning
  have canonical := representation_square (model := standard) (expand falseClaim)
    ((representation_expand falseClaim).trans falseClaim_represented)
  apply expanded_falseClaim_fails
  exact Eq.mp (congrArg ULift.down (meaning.coherent canonical valuation)) True.intro

end Controls

#print axioms representation_expand
#print axioms expansion_meaning
#print axioms native_representation_meaning
#print axioms formula_meaning
#print axioms Controls.expanded_trueClaim_holds
#print axioms Controls.expanded_falseClaim_fails
#print axioms Controls.native_falseClaim_not_true

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizRepresentationSemantics
