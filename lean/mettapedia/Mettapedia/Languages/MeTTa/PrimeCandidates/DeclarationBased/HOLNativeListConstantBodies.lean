import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLProofListIntegration

/-!
# Closed native List images of the uniform HOL declarations

The source's sequence carrier and operations are interpreted by actual native
List terms in the unchanged mixed proof/List presentation. The retained count
carrier, zero and successor suffice to define length by a native fold. This
translation adds no source conversion between the opaque sequence constant and
List and makes no nonemptiness or whole-model assertion for an arbitrary small
native element type.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeListConstantBodies

open Presentation Presentation.Declaration Presentation.FormationSensitive
open ConstantExpansion FormationSensitiveHOLInterface NativeIndexedFamilies IntrinsicMaps
open RussellTarski
open Presentation.SchemaElaboration
open Mettapedia.Logic HOL.UniformListInduction

namespace Source
export FormationSensitiveHOLUniformList (types baseName rawImp universalType)
end Source

abbrev rules := FormationSensitiveHOLProofListIntegration.rules
abbrev Typing {n : Nat} := @FormationSensitive.Typing Tower.Head rules n

def consBody (element : Tower.Tm 0) : Tower.Tm 0 :=
  .app (.const Intrinsic.consName) element

def mapBody (element : Tower.Tm 0) : Tower.Tm 0 :=
  .app (.app nativeMapTerm element) element

def countType {n : Nat} : Tower.Tm n := .const `HOLUniformList.count
def zeroTerm {n : Nat} : Tower.Tm n := .const `HOLUniformList.zero
def successorTerm {n : Nat} : Tower.Tm n := .const `HOLUniformList.succ

def lengthStep {n : Nat} : Tower.Tm n :=
  .lam (.lam (.lam (.app successorTerm (.var 0))))

def lengthBody (element : Tower.Tm 0) : Tower.Tm 0 :=
  .lam (Intrinsic.eliminateApp (liftClosed element) (.lam countType)
    zeroTerm lengthStep (.var 0))

/-- Simultaneous images; the original declarations remain unchanged. -/
def bodies (element : Tower.Tm 0) : Bodies Tower.Head := fun name =>
  if name = `HOLUniformList.element then element
  else if name = `HOLUniformList.sequence then Intrinsic.listApp element
  else if name = `HOLUniformList.nil then Intrinsic.nilApp element
  else if name = `HOLUniformList.cons then consBody element
  else if name = `HOLUniformList.map then mapBody element
  else if name = `HOLUniformList.length then lengthBody element
  else .const name

@[simp] theorem bodies_element (element : Tower.Tm 0) :
    bodies element `HOLUniformList.element = element := by simp [bodies]
@[simp] theorem bodies_sequence (element : Tower.Tm 0) :
    bodies element `HOLUniformList.sequence = Intrinsic.listApp element := by simp [bodies]
@[simp] theorem bodies_nil (element : Tower.Tm 0) :
    bodies element `HOLUniformList.nil = Intrinsic.nilApp element := by simp [bodies]
@[simp] theorem bodies_cons (element : Tower.Tm 0) :
    bodies element `HOLUniformList.cons = consBody element := by simp [bodies]
@[simp] theorem bodies_map (element : Tower.Tm 0) :
    bodies element `HOLUniformList.map = mapBody element := by simp [bodies]
@[simp] theorem bodies_length (element : Tower.Tm 0) :
    bodies element `HOLUniformList.length = lengthBody element := by simp [bodies]
@[simp] theorem bodies_proof (element : Tower.Tm 0) :
    bodies element FormationSensitiveHOLProofFamily.proofName =
      .const FormationSensitiveHOLProofFamily.proofName := by simp [bodies, FormationSensitiveHOLProofFamily.proofName]
@[simp] theorem bodies_implication (element : Tower.Tm 0) :
    bodies element `HOLUniformList.implication = .const `HOLUniformList.implication := by simp [bodies]
@[simp] theorem bodies_universal (element : Tower.Tm 0) :
    bodies element `HOLUniformList.universal = .const `HOLUniformList.universal := by simp [bodies]

def types (element : Tower.Tm 0) : TypeInterpretation BaseSort where
  proposition := .const `HOLUniformList.prop
  base := fun sort => match sort with
    | .element => element
    | .sequence => Intrinsic.listApp element
    | .count => countType

theorem expand_typeAt (element : Tower.Tm 0) (type : HOL.Ty BaseSort) (n : Nat) :
    expand (bodies element) (typeAt Source.types n type) = typeAt (types element) n type := by
  induction type generalizing n with
  | prop => simp [typeAt, Source.types, FormationSensitiveHOLUniformList.types, types,
      expand, bodies, liftClosed, rename]
  | base sort =>
      cases sort <;> simp [typeAt, Source.types, FormationSensitiveHOLUniformList.types,
        types, FormationSensitiveHOLUniformList.baseName, countType, expand, bodies,
        liftClosed, rename]
  | arr a b ihA ihB => simp only [typeAt, expand, ihA, ihB]

theorem expand_decoder {n : Nat} (element : Tower.Tm 0)
    {left right : Tower.Tm n}
    (step : FormationSensitiveHOLProofFamily.DecoderStep left right) :
    FormationSensitiveHOLProofFamily.DecoderStep
      (expand (bodies element) left) (expand (bodies element) right) := by
  cases step with
  | implication p q =>
      simpa only [FormationSensitiveHOLProofFamily.proof, Source.rawImp,
        FormationSensitiveHOLUniformList.rawImp, FormationSensitiveHOLProofFamily.implicationFamily,
        expand, bodies_proof, bodies_implication, liftClosed, rename, expand_rename]
        using FormationSensitiveHOLProofFamily.DecoderStep.implication
          (expand (bodies element) p) (expand (bodies element) q)
  | universal a f =>
      simpa only [FormationSensitiveHOLProofFamily.proof,
        FormationSensitiveHOLProofFamily.universalProposition,
        FormationSensitiveHOLProofFamily.universalFamily,
        expand, bodies_proof, bodies_universal, liftClosed, rename, expand_rename]
        using FormationSensitiveHOLProofFamily.DecoderStep.universal
          (expand (bodies element) a) (expand (bodies element) f)

theorem root_conversion {n : Nat} (element : Tower.Tm 0)
    {left right : Tower.Tm n}
    (step : FormationSensitiveHOLProofFamily.rules.computation.step left right) :
    Conv rules.headEq (expand (bodies element) left) (expand (bodies element) right)
      rules.computation := by
  cases step with
  | inherited impossible => exact impossible.elim
  | delta known =>
      rw [FormationSensitiveHOLProofConversion.declarations_opaque] at known
      cases known
  | declared decoder => exact .rel _ _ (.root (.declared (expand_decoder element decoder)))

theorem list_typed {n : Nat} {Γ : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing Γ element (sortTm Tower.zero)) :
    Typing Γ (Intrinsic.listApp element) (sortTm Tower.zero) := by
  have symbol := FormationSensitiveHOLProofListIntegration.execution_typed
    (FormationSensitiveNativeHOLMapExecution.listConstant_typed Γ)
  have applied := FormationSensitive.Typing.appElim symbol formed
  simpa [listTypeAt, Intrinsic.listType, Intrinsic.listApp, sameLevelSubstitution,
    RussellTarski.substLevelsTm, RussellTarski.substLevelsHead,
    LevelExpr.subst, Intrinsic.elementLevel, Tm.mapHead, sortTm,
    liftClosed, rename, inst0, subst, subst0, liftSub] using applied

theorem nil_typed {n : Nat} {Γ : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing Γ element (sortTm Tower.zero)) :
    Typing Γ (Intrinsic.nilApp element) (Intrinsic.listApp element) := by
  have symbol := FormationSensitiveHOLProofListIntegration.execution_typed
    (FormationSensitiveNativeHOLMapExecution.nilConstant_typed Γ)
  have applied := FormationSensitive.Typing.appElim symbol formed
  simpa [nilTypeAt, Intrinsic.nilType, Intrinsic.nilApp, Intrinsic.listApp,
    sameLevelSubstitution, RussellTarski.substLevelsTm, RussellTarski.substLevelsHead,
    LevelExpr.subst, Intrinsic.elementLevel, Tm.mapHead, sortTm,
    liftClosed, rename, inst0, subst, subst0, liftSub, liftRen] using applied

theorem cons_typed {element : Tower.Tm 0}
    (formed : Typing .nil element (sortTm Tower.zero)) :
    Typing .nil (consBody element)
      (arrow element (arrow (Intrinsic.listApp element) (Intrinsic.listApp element))) := by
  have symbol := FormationSensitiveHOLProofListIntegration.execution_typed
    (FormationSensitiveNativeHOLMapExecution.consConstant_typed .nil)
  have applied := FormationSensitive.Typing.appElim symbol formed
  have bodyAsArrows : Intrinsic.consBodyType =
      arrow (.var 0) (arrow (Intrinsic.listApp (.var 0)) (Intrinsic.listApp (.var 0))) := by decide
  change Typing .nil (consBody element)
    (inst0 element (rename (liftRen Fin.elim0) Intrinsic.consBodyType)) at applied
  simpa [bodyAsArrows, liftClosed, inst0, subst0] using applied

theorem map_typed {element : Tower.Tm 0}
    (formed : Typing .nil element (sortTm Tower.zero)) :
    Typing .nil (mapBody element)
      (arrow (arrow element element) (arrow (Intrinsic.listApp element) (Intrinsic.listApp element))) := by
  have native := FormationSensitiveHOLProofListIntegration.execution_typed
    FormationSensitiveNativeHOLMapExecution.mapTerm_typed
  have first := FormationSensitive.Typing.appElim native formed
  have second := FormationSensitive.Typing.appElim first formed
  have closedSub (sigma : Sub Tower.Head 0 1) :
      subst sigma element = rename (wk : Ren 0 1) element := by
    have same : sigma = renSub wk := by funext index; exact Fin.elim0 index
    rw [same, subst_renSub]
  simpa [mapBody, nativeMapType, arrow, inst0, subst, subst0, liftSub,
    rename, liftRen, wk, Intrinsic.listApp, subst_rename, rename_subst,
    Fin.cases, Fin.induction, Fin.induction.go, closedSub] using second

theorem pi_zero {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    (domain : Typing Γ A (sortTm Tower.zero))
    (codomain : Typing (.snoc Γ A) B (sortTm Tower.zero)) :
    Typing Γ (.pi A B) (sortTm Tower.zero) := by
  apply FormationSensitive.Typing.cumul
    (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero) (.sorts _ _))
  intro valuation
  simp [LevelExpr.eval, Tower.zero]

theorem proposition_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typing Γ (.const `HOLUniformList.prop) (sortTm Tower.zero) :=
  FormationSensitiveHOLProofListIntegration.proof_typed
    (FormationSensitiveHOLProofFamily.proposition_formed Γ)

theorem count_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typing Γ countType (sortTm Tower.zero) :=
  FormationSensitiveHOLProofListIntegration.proof_typed
    (FormationSensitiveHOLProofFamily.simple_type_formed count Γ)

theorem zero_typed {n : Nat} (Γ : Tower.Ctx n) : Typing Γ zeroTerm countType := by
  have closed := FormationSensitiveHOLProofListIntegration.proof_typed
    (FormationSensitiveHOLProofFamily.include_typed
      (FormationSensitiveHOLUniformList.signature.constant_typed Symbol.zero))
  exact closed_typed closed Γ

theorem successor_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typing Γ successorTerm (arrow countType countType) := by
  have closed := FormationSensitiveHOLProofListIntegration.proof_typed
    (FormationSensitiveHOLProofFamily.include_typed
      (FormationSensitiveHOLUniformList.signature.constant_typed Symbol.succ))
  exact closed_typed closed Γ

theorem type_typed {element : Tower.Tm 0}
    (formed : Typing .nil element (sortTm Tower.zero))
    (type : HOL.Ty BaseSort) {n : Nat} (Γ : Tower.Ctx n) :
    Typing Γ (typeAt (types element) n type) (sortTm Tower.zero) := by
  induction type generalizing n with
  | prop => exact proposition_typed Γ
  | base sort =>
      cases sort with
      | element => exact closed_typed formed Γ
      | sequence => exact list_typed (closed_typed formed Γ)
      | count => exact count_typed Γ
  | arr a b ihA ihB => exact pi_zero (ihA Γ) (ihB _)

theorem constantFamily_typed {n : Nat} {Γ : Tower.Ctx n} {domain target : Tower.Tm n}
    (domainFormed : Typing Γ domain (sortTm Tower.zero))
    (targetFormed : Typing Γ target (sortTm Tower.zero)) :
    Typing Γ (.lam (rename wk target)) (.pi domain (sortTm Tower.zero)) := by
  apply FormationSensitive.Typing.lamIntro
    (.piForm domainFormed (.sort Tower.zero) (.headType (.sort Tower.zero))
      (.sort (.succ Tower.zero)) (.sorts Tower.zero (.succ Tower.zero))) (.sort _)
  simpa only [sortTm, rename] using targetFormed.weaken (extension := domain)

def lengthStepType {n : Nat} (element : Tower.Tm n) : Tower.Tm n :=
  .pi element (.pi (Intrinsic.listApp (rename wk element)) (arrow countType countType))

theorem lengthStepType_typed {n : Nat} {Γ : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing Γ element (sortTm Tower.zero)) :
    Typing Γ (lengthStepType element) (sortTm Tower.zero) := by
  exact pi_zero formed (pi_zero (list_typed formed.weaken)
    (pi_zero (count_typed _) (count_typed _)))

theorem lengthStep_typed {n : Nat} {Γ : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing Γ element (sortTm Tower.zero)) :
    Typing Γ lengthStep (lengthStepType element) := by
  have stepFormed := lengthStepType_typed formed
  obtain ⟨_, _, _, _, _, tailFormed, tailUniverse, _⟩ := stepFormed.piFormation
  obtain ⟨_, _, _, _, _, recFormed, recUniverse, _⟩ := tailFormed.piFormation
  refine .lamIntro stepFormed (.sort Tower.zero)
    (.lamIntro tailFormed tailUniverse (.lamIntro recFormed recUniverse ?_))
  exact .appElim (successor_typed _) (.var 0)

theorem interpreted_sequence_is_native (element : Tower.Tm 0) :
    expand (bodies element) (.const `HOLUniformList.sequence : Tower.Tm 0) =
      Intrinsic.listApp (liftClosed element) := rfl

theorem interpreted_sequence_not_opaque (element : Tower.Tm 0) :
    expand (bodies element) (.const `HOLUniformList.sequence : Tower.Tm 0) ≠
      .const `HOLUniformList.sequence := by
  simp only [expand, bodies_sequence, liftClosed, Intrinsic.listApp, rename]
  intro impossible
  cases impossible

theorem interpreted_map_not_opaque (element : Tower.Tm 0) :
    expand (bodies element) (.const `HOLUniformList.map : Tower.Tm 0) ≠
      .const `HOLUniformList.map := by
  simp only [expand, bodies_map, liftClosed, mapBody, rename]
  intro impossible
  cases impossible

#print axioms expand_typeAt
#print axioms expand_decoder
#print axioms root_conversion
#print axioms list_typed
#print axioms nil_typed
#print axioms cons_typed
#print axioms map_typed
#print axioms type_typed
#print axioms lengthStep_typed
#print axioms interpreted_sequence_is_native
#print axioms interpreted_sequence_not_opaque
#print axioms interpreted_map_not_opaque

end HOLNativeListConstantBodies
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
