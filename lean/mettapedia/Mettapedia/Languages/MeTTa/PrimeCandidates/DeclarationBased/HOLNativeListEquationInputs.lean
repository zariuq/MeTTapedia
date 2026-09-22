import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListDeclarationInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedLeibnizRules

/-!
# Native computational witnesses for the original list equation inputs

The original source formulas are retained. Their interpreted equality
witnesses follow from independently proved beta/iota conversions, and their
universal quantifiers are introduced by native lambdas.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeListEquationInputs

open Presentation Presentation.Declaration ConstantExpansion FormationSensitiveHOLInterface
open Mettapedia.Logic HOL.UniformListInduction NativeIndexedFamilies IntrinsicMaps
open FormationSensitiveHOLProofFamily (proof)
open HOLNativeListConstantBodies (bodies)

abbrev rules := FormationSensitiveHOLProofListIntegration.rules
abbrev Typing {n : Nat} := @FormationSensitive.Typing Tower.Head rules n
abbrev signature := FormationSensitiveHOLLeibnizInterface.signature
abbrev sourceContext (gamma : HOL.Ctx BaseSort) :=
  context FormationSensitiveHOLUniformList.types gamma

def interpretedContext (element : Tower.Tm 0) (gamma : HOL.Ctx BaseSort) :
    Tower.Ctx gamma.length := expandCtx (bodies element) (sourceContext gamma)

theorem equality_input {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Expr gamma type} {xc yc : Tower.Tm gamma.length}
    (xRep : represent signature x = some xc) (yRep : represent signature y = some yc)
    (conversion : Conv rules.headEq (expand (bodies element) xc)
      (expand (bodies element) yc) rules.computation) :
    ∃ code, represent signature (.eq x y) = some code ∧
      Typing (interpretedContext element gamma) (.lam (.lam (.var 0)))
        (expand (bodies element) (proof code)) := by
  let translation := HOLNativeListDeclarationInterpretation.interpretation elementTyped
  have xTyped := FormationSensitiveHOLProofFamily.include_typed
    (represent_typed signature x xRep)
  have reflexive := FormationSensitiveHOLLeibnizRules.reflexivity xTyped
  have displayed := represent_eq signature x y xRep yRep
  have displayedFormed := FormationSensitiveHOLProofFamily.proof_formed
    (FormationSensitiveHOLProofFamily.include_typed
      (represent_typed signature (.eq x y) displayed))
  have originalReflexiveFormed := FormationSensitiveHOLProofFamily.proof_formed
    (FormationSensitiveHOLProofFamily.include_typed
      (represent_typed signature (.eq x x) (represent_eq signature x x xRep xRep)))
  have toDisplayed := Conv.congApp
    (Relation.EqvGen.refl (.const FormationSensitiveHOLProofFamily.proofName))
    (FormationSensitiveHOLLeibnizInterface.Decoded.include_conversion
      (FormationSensitiveHOLLeibnizInterface.equality_application_conversion type xc xc))
  have sourceReflexive := FormationSensitive.Typing.conv reflexive originalReflexiveFormed
    (.sort Tower.zero) toDisplayed.symm
  refine ⟨_, displayed, ?_⟩
  have converted := translation.typing sourceReflexive
  apply FormationSensitive.Typing.conv converted (translation.typing displayedFormed) (.sort Tower.zero)
  exact Conv.congApp (.refl _) (Conv.congApp (.refl _) conversion)

theorem universal_input {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero))
    {gamma : HOL.Ctx BaseSort} {a : HOL.Ty BaseSort}
    {p : Sentence (a :: gamma)} {code : Tower.Tm (a :: gamma).length}
    {native : Tower.Tm (a :: gamma).length}
    (represented : represent signature p = some code)
    (checked : Typing (interpretedContext element (a :: gamma)) native
      (expand (bodies element) (proof code))) :
    ∃ proposition, represent signature (.all p) = some proposition ∧
      Typing (interpretedContext element gamma) (.lam native)
        (expand (bodies element) (proof proposition)) := by
  let translation := HOLNativeListDeclarationInterpretation.interpretation elementTyped
  have pTyped := FormationSensitiveHOLProofFamily.include_typed
    (represent_typed signature p represented)
  have domain := FormationSensitiveHOLProofFamily.simple_type_formed a (sourceContext gamma)
  have family := FormationSensitiveHOLProofFamily.pi_zero domain
    (FormationSensitiveHOLProofFamily.proof_formed pTyped)
  have displayed : represent signature (.all p) =
      some (FormationSensitiveHOLUniformList.rawAll a code) := by
    simp only [represent, represented]
    rfl
  have displayedFormed := FormationSensitiveHOLProofFamily.proof_formed
    (FormationSensitiveHOLProofFamily.include_typed
      (represent_typed signature (.all p) displayed))
  refine ⟨_, displayed, ?_⟩
  exact .conv (.lamIntro (translation.typing family) (.sort Tower.zero) checked)
    (translation.typing displayedFormed) (.sort Tower.zero)
    (translation.conversion (FormationSensitiveHOLProofFamily.rawAll_conversion a code)).symm

theorem list_path_conversion {n : Nat} {left right : Tower.Tm n}
    (path : IntrinsicNativeListMapComputation.Reduces Tower.zero left right) :
    Conv rules.headEq left right rules.computation := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec
    (IntrinsicNativeListMapComputation.reduction Tower.zero n)
    (fun left right _ => Conv rules.headEq left right rules.computation)
    (fun _ => .refl _) (fun {_ _ _} edge _ ih => ?_) left right path
  exact .trans _ _ _ (.rel _ _
    (FormationSensitiveHOLProofListIntegration.execution_step
      (FormationSensitiveNativeHOLMapExecution.list_computational_step_include edge))) ih

theorem map_nil_conversion {n : Nat} (element function : Tower.Tm n) :
    Conv rules.headEq
      (IntrinsicNativeListMapComputation.applyMap element element function (Intrinsic.nilApp element))
      (Intrinsic.nilApp element) rules.computation :=
  list_path_conversion
    ((IntrinsicNativeListMapComputation.applyMap_beta Tower.zero element element function
      (Intrinsic.nilApp element)).trans
      (IntrinsicNativeListMapComputation.mapped_nil Tower.zero element element function))

theorem mapNil_input {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    ∃ code, represent signature (mapNil (Γ := [])) = some code ∧
      Typing .nil (.lam (.lam (.lam (.var 0))))
        (expand (bodies element) (proof code)) := by
  have eq := equality_input elementTyped
    (gamma := [mapping])
    (x := map (.var .vz) nil) (y := nil)
    (xc := .app (.app (.const `HOLUniformList.map) (.var 0)) (.const `HOLUniformList.nil))
    (yc := .const `HOLUniformList.nil) rfl rfl
    (map_nil_conversion (liftClosed element) (.var 0))
  obtain ⟨code, represented, checked⟩ := eq
  exact universal_input elementTyped represented checked

theorem map_cons_conversion {n : Nat} (element function head tail : Tower.Tm n) :
    Conv rules.headEq
      (IntrinsicNativeListMapComputation.applyMap element element function
        (Intrinsic.consApp element head tail))
      (Intrinsic.consApp element (.app function head)
        (IntrinsicNativeListMapComputation.applyMap element element function tail))
      rules.computation := by
  have initialSteps := list_path_conversion
    ((IntrinsicNativeListMapComputation.applyMap_beta Tower.zero element element function
      (Intrinsic.consApp element head tail)).trans
      (IntrinsicNativeListMapComputation.mapped_cons Tower.zero element element function head tail))
  exact .trans _ _ _ initialSteps (Conv.congApp (.refl _)
    (list_path_conversion
      (IntrinsicNativeListMapComputation.applyMap_beta Tower.zero element element function tail)).symm)

theorem mapCons_input {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    ∃ code, represent signature (mapCons (Γ := [])) = some code ∧
      Typing .nil (.lam (.lam (.lam (.lam (.lam (.var 0))))))
        (expand (bodies element) (proof code)) := by
  have eq := equality_input elementTyped
    (gamma := [sequence, HOL.UniformListInduction.element, mapping])
    (x := map (.var (.vs (.vs .vz))) (cons (.var (.vs .vz)) (.var .vz)))
    (y := cons (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (map (.var (.vs (.vs .vz))) (.var .vz)))
    (xc := .app (.app (.const `HOLUniformList.map) (.var 2))
      (.app (.app (.const `HOLUniformList.cons) (.var 1)) (.var 0)))
    (yc := .app (.app (.const `HOLUniformList.cons) (.app (.var 2) (.var 1)))
      (.app (.app (.const `HOLUniformList.map) (.var 2)) (.var 0))) rfl rfl
    (map_cons_conversion (liftClosed element) (.var 2) (.var 1) (.var 0))
  obtain ⟨code, represented, checked⟩ := eq
  obtain ⟨code, represented, checked⟩ := universal_input elementTyped represented checked
  obtain ⟨code, represented, checked⟩ := universal_input elementTyped represented checked
  exact universal_input elementTyped represented checked

def lengthCall {n : Nat} (element : Tower.Tm 0) (list : Tower.Tm n) : Tower.Tm n :=
  .app (liftClosed (HOLNativeListConstantBodies.lengthBody element)) list

def lengthFold {n : Nat} (element list : Tower.Tm n) : Tower.Tm n :=
  Intrinsic.eliminateApp element (.lam HOLNativeListConstantBodies.countType)
    HOLNativeListConstantBodies.zeroTerm HOLNativeListConstantBodies.lengthStep list

theorem length_lifted {n : Nat} (element : Tower.Tm 0) :
    (liftClosed (HOLNativeListConstantBodies.lengthBody element) : Tower.Tm n) =
      .lam (lengthFold (liftClosed element) (.var 0)) := by
  change rename Fin.elim0 (HOLNativeListConstantBodies.lengthBody element) = _
  simp only [HOLNativeListConstantBodies.lengthBody, lengthFold,
    Intrinsic.eliminateApp, HOLNativeListConstantBodies.countType,
    HOLNativeListConstantBodies.zeroTerm, HOLNativeListConstantBodies.lengthStep,
    HOLNativeListConstantBodies.successorTerm, rename, rename_liftClosed,
    liftRen, Fin.cases_zero]

theorem length_beta {n : Nat} (element : Tower.Tm 0) (list : Tower.Tm n) :
    Conv rules.headEq (lengthCall element list) (lengthFold (liftClosed element) list)
      rules.computation := by
  rw [lengthCall, length_lifted]
  have beta : Conv rules.headEq
      (.app (.lam (lengthFold (liftClosed element) (.var 0))) list)
      (inst0 list (lengthFold (liftClosed element) (.var 0))) rules.computation :=
    .rel _ _ (.betaPi _ _)
  simpa only [lengthFold, Intrinsic.eliminateApp, HOLNativeListConstantBodies.countType,
    HOLNativeListConstantBodies.zeroTerm, HOLNativeListConstantBodies.lengthStep,
    HOLNativeListConstantBodies.successorTerm, inst0, subst, subst_liftClosed,
    subst0, liftSub, Fin.cases_zero] using beta

theorem length_nil_conversion {n : Nat} (element : Tower.Tm 0) :
    Conv rules.headEq (lengthCall element (Intrinsic.nilApp (liftClosed element) : Tower.Tm n))
      HOLNativeListConstantBodies.zeroTerm rules.computation :=
  .trans _ _ _ (length_beta element _)
    (.rel _ _ (.root (.inherited (.declared ⟨.list (.nil _ _ _ _)⟩))))

theorem lengthNil_input {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    ∃ code, represent signature (lengthNil (Γ := [])) = some code ∧
      Typing .nil (.lam (.lam (.var 0))) (expand (bodies element) (proof code)) :=
  equality_input elementTyped (x := length nil) (y := .const .zero)
    (xc := .app (.const `HOLUniformList.length) (.const `HOLUniformList.nil))
    (yc := .const `HOLUniformList.zero) rfl rfl (length_nil_conversion element)

theorem length_step_beta {n : Nat} (head tail result : Tower.Tm n) :
    Conv rules.headEq
      (.app (.app (.app HOLNativeListConstantBodies.lengthStep head) tail) result)
      (.app HOLNativeListConstantBodies.successorTerm result) rules.computation := by
  have first : Conv rules.headEq (.app HOLNativeListConstantBodies.lengthStep head)
      (.lam (.lam (.app HOLNativeListConstantBodies.successorTerm (.var 0))))
      rules.computation := .rel _ _ (.betaPi _ _)
  have second : Conv rules.headEq
      (.app (.lam (.lam (.app HOLNativeListConstantBodies.successorTerm (.var 0)))) tail)
      (.lam (.app HOLNativeListConstantBodies.successorTerm (.var 0)))
      rules.computation := .rel _ _ (.betaPi _ _)
  exact .trans _ _ _ (Conv.congApp (Conv.congApp first (.refl _)) (.refl _))
    (.trans _ _ _ (Conv.congApp second (.refl _)) (.rel _ _ (.betaPi _ _)))

theorem length_cons_conversion {n : Nat} (element : Tower.Tm 0) (head tail : Tower.Tm n) :
    Conv rules.headEq (lengthCall element (Intrinsic.consApp (liftClosed element) head tail))
      (.app HOLNativeListConstantBodies.successorTerm (lengthCall element tail))
      rules.computation := by
  have iota : Conv rules.headEq
      (lengthFold (liftClosed element) (Intrinsic.consApp (liftClosed element) head tail))
      (.app (.app (.app HOLNativeListConstantBodies.lengthStep head) tail)
        (lengthFold (liftClosed element) tail)) rules.computation :=
    .rel _ _ (.root (.inherited (.declared ⟨.list (.cons _ _ _ _ _ _)⟩)))
  exact .trans _ _ _ (length_beta element _)
    (.trans _ _ _ iota (.trans _ _ _ (length_step_beta head tail _)
      (Conv.congApp (.refl _) (length_beta element tail).symm)))

theorem lengthCons_input {element : Tower.Tm 0}
    (elementTyped : Typing .nil element (sortTm Tower.zero)) :
    ∃ code, represent signature (lengthCons (Γ := [])) = some code ∧
      Typing .nil (.lam (.lam (.lam (.lam (.var 0)))))
        (expand (bodies element) (proof code)) := by
  have eq := equality_input elementTyped
    (gamma := [sequence, HOL.UniformListInduction.element])
    (x := length (cons (.var (.vs .vz)) (.var .vz)))
    (y := succ (length (.var .vz)))
    (xc := .app (.const `HOLUniformList.length)
      (.app (.app (.const `HOLUniformList.cons) (.var 1)) (.var 0)))
    (yc := .app (.const `HOLUniformList.succ) (.app (.const `HOLUniformList.length) (.var 0)))
    rfl rfl (length_cons_conversion element (.var 1) (.var 0))
  obtain ⟨code, represented, checked⟩ := eq
  obtain ⟨code, represented, checked⟩ := universal_input elementTyped represented checked
  exact universal_input elementTyped represented checked

#print axioms equality_input
#print axioms universal_input
#print axioms map_nil_conversion
#print axioms mapNil_input
#print axioms map_cons_conversion
#print axioms mapCons_input
#print axioms length_beta
#print axioms length_nil_conversion
#print axioms lengthNil_input
#print axioms length_cons_conversion
#print axioms lengthCons_input

end HOLNativeListEquationInputs
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
