import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeListHOLPredicateObservation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeListElimination
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation

/-!
# Formation-sensitive native map in a common HOL/List environment

Native List declarations are instantiated at one universe and extended by
the retained HOL declarations. Formation certificates are transported by
actual rule morphisms. The map remains the existing eliminator program;
logical sequence constants are not identified with native List types.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveNativeHOLMapExecution

open Presentation Presentation.Declaration Presentation.SchemaElaboration NativeIndexedFamilies IntrinsicMaps
open FormationSensitiveHOLInterface
open Mettapedia.Logic HOL.UniformListInduction

variable {n : Nat}

def mapRelIota (map : Tower.Head → Tower.Head) {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.IotaEvidence n left right) :
    IntrinsicRelator.IotaEvidence n (left.mapHead map) (right.mapHead map) := by
  cases evidence with
  | nil => exact .nil _ _ _ _ _ _
  | cons => exact .cons _ _ _ _ _ _ _ _ _ _ _ _

def nativeInstance : LevelInstance IntrinsicRelator.rawSignature (sameLevelSubstitution Tower.zero) where
  computation := IntrinsicRelator.combinedProofRelevantIotaComputation.support
  computationMap := by
    intro n left right step
    rcases step with ⟨evidence⟩
    cases evidence with
    | list evidence => exact ⟨.list (mapIotaEvidence _ evidence)⟩
    | rel evidence => exact ⟨.rel (mapRelIota _ evidence)⟩

def rules : Rules Tower.Head :=
  extendRules nativeInstance.rules FormationSensitiveHOLUniformList.declarations

abbrev Typing (context : Tower.Ctx n) (term type : Tower.Tm n) :=
  FormationSensitive.Typing rules context term type

theorem native_typed {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : FormationSensitiveNativeList.Typing context term type) :
    Typing (RussellTarski.substLevelsCtx (sameLevelSubstitution Tower.zero) context)
      (RussellTarski.substLevelsTm (sameLevelSubstitution Tower.zero) term)
      (RussellTarski.substLevelsTm (sameLevelSubstitution Tower.zero) type) := by
  have instantiated := typed.mapHead nativeInstance.morphism
  have included := instantiated.mapHead
    (includeMorphism nativeInstance.rules FormationSensitiveHOLUniformList.declarations)
  simpa only [Ctx.mapHead_id, Tm.mapHead_id, Typing, rules,
    RussellTarski.substLevelsCtx, RussellTarski.substLevelsTm] using included

theorem holMorphism : FormationSensitiveHOLUniformList.rules.Morphism rules (fun h => h) where
  headTyping := fun h => h
  isUniverse := fun h => h
  join := fun h => h
  cumulative := fun h => h
  headEq := fun h => h
  constantType := by
    intro name type known
    have sourceKnown : FormationSensitiveHOLUniformList.declarations.typeOf? name = some type := known
    obtain ⟨entry, entryKnown, _⟩ := Option.map_eq_some_iff.mp sourceKnown
    have fresh := (HOLNativeRelatorCompatibility.hol_entry_fresh entryKnown).2
    apply combinedType_of_signature nativeInstance.rules FormationSensitiveHOLUniformList.declarations
    · change IntrinsicRelator.rawSignature.typeOf? name = none at fresh
      simp [LevelInstance.rules, extendRules, combinedType, Tower.rules,
        LevelInstance.signature, Signature.typeOf_instantiateLevels, fresh]
    · simpa only [Tm.mapHead_id] using sourceKnown
  computation := by
    intro n left right step
    cases step with
    | inherited impossible => exact impossible.elim
    | delta known => rw [HOLNativeRelatorCompatibility.hol_values_opaque] at known; cases known
    | declared impossible => exact impossible.elim

theorem hol_typed {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : FormationSensitive.Typing FormationSensitiveHOLUniformList.rules context term type) :
    Typing context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead holMorphism

theorem hol_context {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation FormationSensitiveHOLUniformList.rules context) :
    FormationSensitive.ContextFormation rules context := by
  simpa only [Ctx.mapHead_id] using formed.mapHead holMorphism

theorem native_constant (context : Tower.Ctx n) {name : DeclName}
    {type : Tower.Tm 0} {universeHead : Tower.Head}
    (known : IntrinsicRelator.rules.constantType name = some type)
    (formed : FormationSensitiveNativeList.Typing .nil type (.head universeHead))
    (isUniverse : IntrinsicRelator.rules.isUniverse universeHead) :
    Typing context (.const name)
      (liftClosed (RussellTarski.substLevelsTm (sameLevelSubstitution Tower.zero) type)) := by
  apply FormationSensitive.Typing.const
  · have lookup := (includeMorphism nativeInstance.rules
      FormationSensitiveHOLUniformList.declarations).constantType
        (nativeInstance.morphism.constantType known)
    simpa only [Tm.mapHead_id, RussellTarski.substLevelsTm, rules] using lookup
  · exact native_typed formed
  · exact nativeInstance.morphism.isUniverse isUniverse

theorem listConstant_typed (context : Tower.Ctx n) :
    Typing context (.const Intrinsic.listName) (liftClosed (listTypeAt Tower.zero)) :=
  native_constant context (by decide) FormationSensitiveNativeList.listType_hasType (.sort _)

theorem nilConstant_typed (context : Tower.Ctx n) :
    Typing context (.const Intrinsic.nilName) (liftClosed (nilTypeAt Tower.zero)) :=
  native_constant context (by decide) FormationSensitiveNativeList.nilType_hasType (.sort _)

theorem consConstant_typed (context : Tower.Ctx n) :
    Typing context (.const Intrinsic.consName) (liftClosed (consTypeAt Tower.zero)) :=
  native_constant context (by decide) FormationSensitiveNativeList.consType_hasType (.sort _)

theorem eliminateConstant_typed (context : Tower.Ctx n) :
    Typing context (.const Intrinsic.eliminateName) (liftClosed (eliminateTypeAt Tower.zero)) :=
  native_constant context (by decide) FormationSensitiveNativeListElimination.eliminateType_hasType (.sort _)

open RussellTarski Intrinsic

theorem listApp_typed {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing context element (sortTm Tower.zero)) :
    Typing context (Intrinsic.listApp element) (sortTm Tower.zero) := by
  have application := FormationSensitive.Typing.appElim (listConstant_typed context) formed
  simpa [listTypeAt, Intrinsic.listType, Intrinsic.listApp,
    sameLevelSubstitution, substLevelsTm, substLevelsHead, liftClosed,
    LevelExpr.subst, Intrinsic.elementLevel, Tm.mapHead, sortTm,
    Presentation.rename, Presentation.inst0, Presentation.subst] using application

theorem nilApp_typed {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing context element (sortTm Tower.zero)) :
    Typing context (Intrinsic.nilApp element) (Intrinsic.listApp element) := by
  have application := FormationSensitive.Typing.appElim (nilConstant_typed context) formed
  simpa [nilTypeAt, Intrinsic.nilType, Intrinsic.nilApp,
    Intrinsic.listApp, sameLevelSubstitution, substLevelsTm,
    substLevelsHead, LevelExpr.subst, Intrinsic.elementLevel, Tm.mapHead,
    liftClosed, sortTm, Presentation.rename,
    Presentation.inst0, Presentation.subst, Presentation.subst0,
    Presentation.liftRen, Presentation.liftSub] using application

theorem consApp_typed {context : Tower.Ctx n} {element head tail : Tower.Tm n}
    (formed : Typing context element (sortTm Tower.zero))
    (headTyped : Typing context head element)
    (tailTyped : Typing context tail (Intrinsic.listApp element)) :
    Typing context (Intrinsic.consApp element head tail) (Intrinsic.listApp element) := by
  have consBodyAsArrows : Intrinsic.consBodyType =
      arrow (.var 0) (arrow (Intrinsic.listApp (.var 0)) (Intrinsic.listApp (.var 0))) := by decide
  have first := FormationSensitive.Typing.appElim (consConstant_typed context) formed
  change Typing context (.app (.const Intrinsic.consName) element)
    (inst0 element (rename (liftRen Fin.elim0) Intrinsic.consBodyType)) at first
  have firstNormalized : Typing context (.app (.const Intrinsic.consName) element)
      (arrow element (arrow (Intrinsic.listApp element) (Intrinsic.listApp element))) := by
    simpa [consBodyAsArrows, liftClosed, Presentation.inst0, Presentation.subst0] using first
  have second := FormationSensitive.Typing.appElim firstNormalized headTyped
  have secondNormalized : Typing context (.app (.app (.const Intrinsic.consName) element) head)
      (arrow (Intrinsic.listApp element) (Intrinsic.listApp element)) := by
    simpa only [Presentation.inst0_rename_wk] using second
  have third := FormationSensitive.Typing.appElim secondNormalized tailTyped
  simpa only [Intrinsic.consApp, arrow, Presentation.inst0_rename_wk] using third

theorem pi_zero {context : Tower.Ctx n} {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (domain : Typing context a (sortTm Tower.zero))
    (codomain : Typing (.snoc context a) b (sortTm Tower.zero)) :
    Typing context (.pi a b) (sortTm Tower.zero) := by
  apply FormationSensitive.Typing.cumul
    (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero) (.sorts _ _))
  intro valuation
  simp [LevelExpr.eval, Tower.zero]

theorem constantFamily_typed {context : Tower.Ctx n} {domain target : Tower.Tm n}
    (domainFormed : Typing context domain (sortTm Tower.zero))
    (targetFormed : Typing context target (sortTm Tower.zero)) :
    Typing context (.lam (rename wk target)) (.pi domain (sortTm Tower.zero)) := by
  apply FormationSensitive.Typing.lamIntro
    (.piForm domainFormed (.sort Tower.zero) (.headType (.sort Tower.zero))
      (.sort (.succ Tower.zero)) (.sorts Tower.zero (.succ Tower.zero))) (.sort _)
  simpa only [sortTm, rename] using targetFormed.weaken (extension := domain)

theorem constantFamily_app_formed {context : Tower.Ctx n} {domain target argument : Tower.Tm n}
    (domainFormed : Typing context domain (sortTm Tower.zero))
    (targetFormed : Typing context target (sortTm Tower.zero))
    (argumentTyped : Typing context argument domain) :
    Typing context (.app (.lam (rename wk target)) argument) (sortTm Tower.zero) := by
  simpa only [inst0, subst, sortTm] using FormationSensitive.Typing.appElim
    (constantFamily_typed domainFormed targetFormed) argumentTyped

theorem constantFamily_beta (target argument : Tower.Tm n) :
    Conv rules.headEq (.app (.lam (rename wk target)) argument) target rules.computation := by
  simpa only [inst0_rename_wk] using
    (Relation.EqvGen.rel _ _ (Step.betaPi (root := rules.computation) (rename wk target) argument))

theorem mapType_formed : Typing .nil (nativeMapType Tower.zero)
    (sortTm (.max (.succ Tower.zero) (.max (.succ Tower.zero) Tower.zero))) := by
  unfold nativeMapType
  refine FormationSensitive.Typing.piForm (R := rules)
    (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    ?_ (.sort (.max (.succ Tower.zero) Tower.zero)) (.sorts _ _)
  refine FormationSensitive.Typing.piForm (R := rules)
    (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    ?_ (.sort Tower.zero) (.sorts _ _)
  exact pi_zero (pi_zero (.var 1) (.var 1))
    (pi_zero (listApp_typed (.var 2)) (listApp_typed (.var 2)))

theorem consCase_formed : Typing (mapContextABFXs Tower.zero) nativeMapConsCaseType
    (sortTm Tower.zero) :=
  pi_zero (.var 3) (pi_zero (listApp_typed (.var 4))
    (pi_zero (listApp_typed (.var 4)) (listApp_typed (.var 5))))

theorem consCase_typed : Typing (mapContextABFXs Tower.zero) nativeMapConsCase nativeMapConsCaseType := by
  have formed := consCase_formed
  obtain ⟨_, _, _, _, _, second, uSecond, _⟩ := FormationSensitive.Typing.piFormation formed
  obtain ⟨_, _, _, _, _, third, uThird, _⟩ := FormationSensitive.Typing.piFormation second
  apply FormationSensitive.Typing.lamIntro formed (.sort Tower.zero)
  apply FormationSensitive.Typing.lamIntro second uSecond
  apply FormationSensitive.Typing.lamIntro third uThird
  apply consApp_typed (.var 5)
  · have fn : Typing
        (.snoc (.snoc (.snoc (mapContextABFXs Tower.zero) (.var 3))
          (Intrinsic.listApp (.var 4))) (Intrinsic.listApp (.var 4)))
        (.var 4) (arrow (.var 6) (.var 5)) := .var 4
    simpa only [arrow, inst0_rename_wk] using
      FormationSensitive.Typing.appElim fn (.var 2)
  · exact .var 0

theorem consExpected_formed : Typing (mapContextABFXs Tower.zero)
    (nativeMapConsExpected Tower.zero) (sortTm Tower.zero) := by
  rw [nativeMapConsExpected_eq]
  apply pi_zero (.var 3)
  apply pi_zero (listApp_typed (.var 4))
  apply pi_zero
  · apply constantFamily_app_formed (n := 6) (domain := Intrinsic.listApp (.var 5))
      (target := Intrinsic.listApp (.var 4)) (argument := .var 0)
    · exact listApp_typed (.var 5)
    · exact listApp_typed (.var 4)
    · exact .var 0
  · apply constantFamily_app_formed (n := 7) (domain := Intrinsic.listApp (.var 6))
      (target := Intrinsic.listApp (.var 5))
      (argument := Intrinsic.consApp (.var 6) (.var 2) (.var 1))
    · exact listApp_typed (.var 6)
    · exact listApp_typed (.var 5)
    · exact consApp_typed (.var 6) (.var 2) (.var 1)

theorem consExpected_converts : Conv rules.headEq
    (nativeMapConsExpected Tower.zero) nativeMapConsCaseType rules.computation := by
  rw [nativeMapConsExpected_eq]
  apply Conv.congPi (.refl _)
  apply Conv.congPi (.refl _)
  exact Conv.congPi (constantFamily_beta (n := 6) (Intrinsic.listApp (.var 4)) (.var 0))
    (constantFamily_beta (n := 7) (Intrinsic.listApp (.var 5))
      (Intrinsic.consApp (.var 6) (.var 2) (.var 1)))

theorem consCase_expected : Typing (mapContextABFXs Tower.zero)
    nativeMapConsCase (nativeMapConsExpected Tower.zero) :=
  .conv consCase_typed consExpected_formed (.sort Tower.zero) consExpected_converts.symm

theorem mapMotive_typed : Typing (mapContextABFXs Tower.zero) nativeMapMotive
    (.pi (Intrinsic.listApp (.var 3)) (sortTm Tower.zero)) :=
  constantFamily_typed (n := 4) (context := mapContextABFXs Tower.zero)
    (domain := Intrinsic.listApp (.var 3)) (target := Intrinsic.listApp (.var 2))
    (listApp_typed (.var 3)) (listApp_typed (.var 2))

theorem mapBody_typed : Typing (mapContextABFXs Tower.zero) nativeMapBody
    (Intrinsic.listApp (.var 2)) := by
  have afterElement := FormationSensitive.Typing.appElim
    (eliminateConstant_typed (mapContextABFXs Tower.zero)) (.var 3)
  have afterMotive := FormationSensitive.Typing.appElim afterElement mapMotive_typed
  have nilAtMotive : Typing (mapContextABFXs Tower.zero) nativeMapNilCase
      (nativeMapNilExpected Tower.zero) := by
    rw [nativeMapNilExpected_eq]
    apply FormationSensitive.Typing.conv
      (nilApp_typed (context := mapContextABFXs Tower.zero) (element := .var 2) (.var 2))
      (constantFamily_app_formed (n := 4) (context := mapContextABFXs Tower.zero)
        (domain := Intrinsic.listApp (.var 3)) (target := Intrinsic.listApp (.var 2))
        (argument := Intrinsic.nilApp (.var 3)) (listApp_typed (.var 3))
        (listApp_typed (.var 2)) (nilApp_typed (.var 3))) (.sort Tower.zero)
    exact (constantFamily_beta (n := 4) (Intrinsic.listApp (.var 2))
      (Intrinsic.nilApp (.var 3))).symm
  have afterNil := FormationSensitive.Typing.appElim afterMotive nilAtMotive
  have afterCons := FormationSensitive.Typing.appElim afterNil consCase_expected
  have afterConsNormalized : Typing (mapContextABFXs Tower.zero)
      (.app (.app (.app (.app (.const Intrinsic.eliminateName) (.var 3))
        nativeMapMotive) nativeMapNilCase) nativeMapConsCase)
      (nativeMapResultType Tower.zero) := by
    simpa [nativeMapResultType, instantiateFourAt, Presentation.inst0] using afterCons
  rw [nativeMapResultType_eq] at afterConsNormalized
  have afterList := FormationSensitive.Typing.appElim afterConsNormalized (.var 0)
  change Typing (mapContextABFXs Tower.zero) nativeMapBody
    (.app (inst0 (.var 0) (rename wk nativeMapMotive)) (.var 0)) at afterList
  rw [inst0_rename_wk] at afterList
  exact .conv afterList (listApp_typed (.var 2)) (.sort Tower.zero)
    (constantFamily_beta (n := 4) (Intrinsic.listApp (.var 2)) (.var 0))

/-- The existing four-lambda eliminator program is admitted with every
lambda and conversion target formed in the same declaration environment. -/
theorem mapTerm_typed : Typing .nil nativeMapTerm (nativeMapType Tower.zero) := by
  have first := mapType_formed
  obtain ⟨_, _, _, _, _, second, uSecond, _⟩ := FormationSensitive.Typing.piFormation first
  obtain ⟨_, _, _, _, _, third, uThird, _⟩ := FormationSensitive.Typing.piFormation second
  obtain ⟨_, _, _, _, _, fourth, uFourth, _⟩ := FormationSensitive.Typing.piFormation third
  exact .lamIntro first (.sort _)
    (.lamIntro second uSecond (.lamIntro third uThird (.lamIntro fourth uFourth mapBody_typed)))

open IntrinsicNativeListMapComputation

theorem appliedMap_schema : Typing (mapContextABFXs Tower.zero)
    (applyMap (.var 3) (.var 2) (.var 1) (.var 0)) (Intrinsic.listApp (.var 2)) := by
  have mapTyped := closed_typed mapTerm_typed (mapContextABFXs Tower.zero)
  have first := FormationSensitive.Typing.appElim mapTyped (.var 3)
  have second := FormationSensitive.Typing.appElim first (.var 2)
  have third := FormationSensitive.Typing.appElim second (.var 1)
  have fourth := FormationSensitive.Typing.appElim third (.var 0)
  exact fourth

theorem mapArguments_typed {context : Tower.Ctx n} {a b f xs : Tower.Tm n}
    (aFormed : Typing context a (sortTm Tower.zero))
    (bFormed : Typing context b (sortTm Tower.zero))
    (fTyped : Typing context f (arrow a b))
    (xsTyped : Typing context xs (Intrinsic.listApp a)) :
    FormationSensitive.CtxMor rules (mapContextABFXs Tower.zero) context
      (Intrinsic.nilSchemaSubstitution a b f xs) := by
  intro index
  fin_cases index
  · exact xsTyped
  · simpa [mapContextABFXs, mapContextABF, mapContextAB, mapContextA,
      Intrinsic.nilSchemaSubstitution, Intrinsic.nilCaseSchemaSubstitution,
      Intrinsic.motiveSchemaSubstitution, Intrinsic.elementSchemaSubstitution,
      consSub, Ctx.lookup, subst, rename, arrow, wk, liftSub, liftRen,
      Fin.cases, Fin.induction, Fin.induction.go] using fTyped
  · exact bFormed
  · exact aFormed

theorem applyMap_typed {context : Tower.Ctx n} {a b f xs : Tower.Tm n}
    (aFormed : Typing context a (sortTm Tower.zero))
    (bFormed : Typing context b (sortTm Tower.zero))
    (fTyped : Typing context f (arrow a b))
    (xsTyped : Typing context xs (Intrinsic.listApp a)) :
    Typing context (applyMap a b f xs) (Intrinsic.listApp b) := by
  have specialized := appliedMap_schema.substitute (mapArguments_typed aFormed bFormed fTyped xsTyped)
  simpa [applyMap, Intrinsic.listApp, subst,
    Intrinsic.nilSchemaSubstitution, Intrinsic.nilCaseSchemaSubstitution,
    Intrinsic.motiveSchemaSubstitution, Intrinsic.elementSchemaSubstitution,
    consSub, Fin.cases, Fin.induction, Fin.induction.go] using specialized

theorem encode_typed {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing context element (sortTm Tower.zero)) (xs : List (Tower.Tm n))
    (leaves : ∀ x ∈ xs, Typing context x element) :
    Typing context (encode element xs) (Intrinsic.listApp element) := by
  induction xs with
  | nil => exact nilApp_typed formed
  | cons head tail ih =>
      exact consApp_typed formed (leaves head List.mem_cons_self)
        (ih (fun x member => leaves x (List.mem_cons_of_mem _ member)))

theorem arrow_formed {context : Tower.Ctx n} {a b : Tower.Tm n}
    (aFormed : Typing context a (sortTm Tower.zero))
    (bFormed : Typing context b (sortTm Tower.zero)) :
    Typing context (arrow a b) (sortTm Tower.zero) := by
  exact pi_zero aFormed (by simpa only [sortTm, rename] using bFormed.weaken (extension := a))

theorem compose_typed {context : Tower.Ctx n} {a b c f g : Tower.Tm n}
    (aFormed : Typing context a (sortTm Tower.zero))
    (cFormed : Typing context c (sortTm Tower.zero))
    (fTyped : Typing context f (arrow b c))
    (gTyped : Typing context g (arrow a b)) :
    Typing context (compose f g) (arrow a c) := by
  apply FormationSensitive.Typing.lamIntro (arrow_formed aFormed cFormed) (.sort Tower.zero)
  have gLift := gTyped.weaken (extension := a)
  have fLift := fTyped.weaken (extension := a)
  simp only [rename_arrow] at gLift fLift
  have gx := FormationSensitive.Typing.appElim gLift (.var 0)
  have gxTyped : Typing (.snoc context a) (.app (rename wk g) (.var 0)) (rename wk b) := by
    simpa only [inst0_rename_wk] using gx
  have fgx := FormationSensitive.Typing.appElim fLift gxTyped
  simpa only [arrow, inst0_rename_wk] using fgx

theorem application_typed {context : Tower.Ctx n} {a b f x : Tower.Tm n}
    (function : Typing context f (arrow a b)) (argument : Typing context x a) :
    Typing context (.app f x) b := by
  simpa only [arrow, inst0_rename_wk] using FormationSensitive.Typing.appElim function argument

theorem list_root_include {left right : Tower.Tm n}
    (step : (listRulesAt Tower.zero).computation.step left right) :
    rules.computation.step left right := by
  cases step with
  | inherited impossible => exact impossible.elim
  | @delta name value known =>
      have noValue : (listSignatureAt Tower.zero).valueOf? name = none := by
        simp [listSignatureAt, LevelInstance.signature, Intrinsic.rawSignature_valueOf_none]
      change (listSignatureAt Tower.zero).valueOf? name = some value at known
      rw [noValue] at known
      cases known
  | declared evidence =>
      rcases evidence with ⟨evidence⟩
      exact .inherited (.declared ⟨.list evidence⟩)

theorem list_step_include {left right : Tower.Tm n}
    (step : StepCore (listRulesAt Tower.zero).computation (listRulesAt Tower.zero).headEq left right) :
    StepCore rules.computation rules.headEq left right := by
  have mapped := step.mapHead (targetEq := rules.headEq) (fun head => head) (fun eq => eq)
    (fun root => by simpa only [Tm.mapHead_id] using list_root_include root)
  simpa only [Tm.mapHead_id] using mapped

/-- Executable List computation embeds without appealing to semantic
universe-head equality. -/
theorem list_computational_step_include {left right : Tower.Tm n}
    (step : StepCore (listRulesAt Tower.zero).computation
      (fun _ _ => False) left right) :
    StepCore rules.computation rules.headEq left right := by
  have mapped := step.mapHead (targetEq := rules.headEq) (fun head => head)
    (fun impossible => impossible.elim)
    (fun root => by simpa only [Tm.mapHead_id] using list_root_include root)
  simpa only [Tm.mapHead_id] using mapped

def commonReduction (n : Nat) : Mettapedia.GSLT.GSLT :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT (Tower.Tm n)
    (StepCore rules.computation rules.headEq)

abbrev CommonReduces (left right : Tower.Tm n) := (commonReduction n).MultiStep left right

/-- Every old beta/iota edge is an edge of the actual common environment.
This establishes whole-path inclusion, not just endpoint agreement. -/
theorem computation_include {left right : Tower.Tm n}
    (path : Reduces Tower.zero left right) : CommonReduces left right := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (reduction Tower.zero n)
    (fun left right _ => CommonReduces left right) (fun _ => .refl _)
    (fun {_ _ _} edge _ ih => .step (list_computational_step_include edge) ih)
      left right path

theorem fusion_output_typed {context : Tower.Ctx n} {a b c f g : Tower.Tm n}
    (cFormed : Typing context c (sortTm Tower.zero))
    (fTyped : Typing context f (arrow b c)) (gTyped : Typing context g (arrow a b))
    (xs : List (Tower.Tm n)) (leaves : ∀ x ∈ xs, Typing context x a) :
    Typing context (encode c (xs.map (fun x => .app f (.app g x)))) (Intrinsic.listApp c) := by
  apply encode_typed cFormed
  intro value member
  obtain ⟨x, inList, rfl⟩ := List.mem_map.mp member
  exact application_typed fTyped (application_typed gTyped (leaves x inList))

/-- Source programs, their constructor result, and every operational edge
use one actual declaration environment and one formed telescope. Endpoint
admission is constructed directly; this does not claim a new unrestricted
subject-reduction theorem for every mixed-profile term. -/
theorem fusion_endpoint_admission {context : Tower.Ctx n} {a b c f g : Tower.Tm n}
    (contextFormed : FormationSensitive.ContextFormation rules context)
    (aFormed : Typing context a (sortTm Tower.zero))
    (bFormed : Typing context b (sortTm Tower.zero))
    (cFormed : Typing context c (sortTm Tower.zero))
    (fTyped : Typing context f (arrow b c)) (gTyped : Typing context g (arrow a b))
    (xs : List (Tower.Tm n)) (leaves : ∀ x ∈ xs, Typing context x a) :
    FormationSensitive.Judgment rules context
        (applyMap b c f (applyMap a b g (encode a xs))) (Intrinsic.listApp c) ∧
      FormationSensitive.Judgment rules context
        (applyMap a c (compose f g) (encode a xs)) (Intrinsic.listApp c) ∧
      FormationSensitive.Judgment rules context
        (encode c (xs.map (fun x => .app f (.app g x)))) (Intrinsic.listApp c) ∧
      CommonReduces (applyMap b c f (applyMap a b g (encode a xs)))
        (encode c (xs.map (fun x => .app f (.app g x)))) ∧
      CommonReduces (applyMap a c (compose f g) (encode a xs))
        (encode c (xs.map (fun x => .app f (.app g x)))) := by
  have sourceTyped := encode_typed aFormed xs leaves
  obtain ⟨unfused, fused⟩ := fusion_common_output Tower.zero a b c f g xs
  exact ⟨⟨contextFormed, applyMap_typed bFormed cFormed fTyped
      (applyMap_typed aFormed bFormed gTyped sourceTyped)⟩,
    ⟨contextFormed, applyMap_typed aFormed cFormed
      (compose_typed aFormed cFormed fTyped gTyped) sourceTyped⟩,
    ⟨contextFormed, fusion_output_typed cFormed fTyped gTyped xs leaves⟩,
    computation_include unfused, computation_include fused⟩

open NativeListHOLPredicateObservation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

theorem observation_include {source : Tower.Tm n} {predicate : Tower.Tm n → Prop}
    (observed : gsltDiamond (reduction Tower.zero n).closure predicate source) :
    gsltDiamond (commonReduction n).closure predicate source := by
  obtain ⟨target, path, accepted⟩ := (finite_observation_iff Tower.zero predicate source).1 observed
  exact (gsltDiamond_spec (commonReduction n).closure predicate source).2
    ⟨target, ⟨target, computation_include path, rfl⟩, accepted⟩

theorem hol_element_formed (gamma : HOL.Ctx BaseSort) :
    Typing (context FormationSensitiveHOLUniformList.types gamma)
      (elementCode gamma) (sortTm Tower.zero) :=
  hol_typed (FormationSensitiveHOLUniformList.simple_type_formed element _)

theorem hol_functions_typed {gamma : HOL.Ctx BaseSort} {f : Tower.Tm gamma.length}
    {meaning : FunctionMeaning gamma}
    (interpreted : NativeHOLFragmentDenotation.Denotes model (type := mapping) f meaning) :
    Typing (context FormationSensitiveHOLUniformList.types gamma) f
      (arrow (elementCode gamma) (elementCode gamma)) := by
  exact hol_typed interpreted.typed

theorem hol_heads_typed {gamma : HOL.Ctx BaseSort} (heads : Heads gamma)
    (interpreted : ∀ head ∈ heads,
      NativeHOLFragmentDenotation.Denotes model (type := element) head.1 head.2) :
    ∀ x ∈ heads.map Prod.fst,
      Typing (context FormationSensitiveHOLUniformList.types gamma) x (elementCode gamma) := by
  intro x member
  obtain ⟨head, inHeads, rfl⟩ := List.mem_map.mp member
  exact hol_typed (interpreted head inHeads).typed

/-- The same source expression interpretations provide formation-sensitive
input admission, native paths in that declaration environment, and HOL-proof
refinement observations. No assumption of native map typing is supplied by
the caller. -/
theorem hol_fusion_admitted_observed {gamma : HOL.Ctx BaseSort}
    (f g : Tower.Tm gamma.length) (fMeaning gMeaning : FunctionMeaning gamma)
    (fDenotes : NativeHOLFragmentDenotation.Denotes model (type := mapping) f fMeaning)
    (gDenotes : NativeHOLFragmentDenotation.Denotes model (type := mapping) g gMeaning)
    (heads : Heads gamma)
    (interpreted : ∀ head ∈ heads,
      NativeHOLFragmentDenotation.Denotes model (type := element) head.1 head.2)
    (rho : model.Valuation gamma) (property : List Bool → Prop)
    (accepted : property (((headValues heads rho).map (functionValue gMeaning rho)).map
      (functionValue fMeaning rho))) :
    FormationSensitive.Judgment rules (context FormationSensitiveHOLUniformList.types gamma)
        (applyMap (elementCode gamma) (elementCode gamma) f
          (applyMap (elementCode gamma) (elementCode gamma) g
            (encode (elementCode gamma) (heads.map Prod.fst))))
        (Intrinsic.listApp (elementCode gamma)) ∧
      FormationSensitive.Judgment rules (context FormationSensitiveHOLUniformList.types gamma)
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) (heads.map Prod.fst)))
        (Intrinsic.listApp (elementCode gamma)) ∧
      gsltDiamond (commonReduction gamma.length).closure (observes rho property)
        (applyMap (elementCode gamma) (elementCode gamma) f
          (applyMap (elementCode gamma) (elementCode gamma) g
            (encode (elementCode gamma) (heads.map Prod.fst)))) ∧
      gsltDiamond (commonReduction gamma.length).closure (observes rho property)
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) (heads.map Prod.fst))) := by
  have formed := hol_context (context_formed FormationSensitiveHOLUniformList.signature gamma)
  have allTyped := fusion_endpoint_admission formed (hol_element_formed gamma)
    (hol_element_formed gamma) (hol_element_formed gamma)
    (hol_functions_typed fDenotes) (hol_functions_typed gDenotes)
    (heads.map Prod.fst) (hol_heads_typed heads interpreted)
  have observed := fusion_consumes_hol_refinement Tower.zero f g fMeaning gMeaning
    fDenotes gDenotes heads interpreted rho property accepted
  exact ⟨allTyped.1, allTyped.2.1, observation_include observed.1, observation_include observed.2⟩

namespace Examples

open NativeListHOLPredicateObservation.Controls

/-- The concrete source HOL functions and head need no additional native
typing premises: the fused map is admitted and returns the proved value. -/
theorem correct_composition_admitted_observed :
    FormationSensitive.Judgment rules (context FormationSensitiveHOLUniformList.types gamma)
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) [x])) (Intrinsic.listApp (elementCode gamma)) ∧
      gsltDiamond (commonReduction gamma.length).closure
        (observes rho (fun output => output = [true]))
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) [x])) := by
  have interpreted : ∀ head ∈ heads,
      NativeHOLFragmentDenotation.Denotes model (type := element) head.1 head.2 := by
    intro head member
    have same : head = (x, xMeaning) := List.mem_singleton.mp member
    subst head
    exact x_denotes
  have result := hol_fusion_admitted_observed f g fMeaning gMeaning
    f_denotes g_denotes heads interpreted rho (fun output => output = [true]) rfl
  exact ⟨result.2.1, result.2.2.2⟩

/-- A wrong constructor result can be well typed. The HOL observation still
rejects it: typing is not silently substituted for the theorem's meaning. -/
theorem wrong_composition_typed_rejected :
    FormationSensitive.Judgment rules (context FormationSensitiveHOLUniformList.types gamma)
        (encode (elementCode gamma) [.app g (.app f x)])
        (Intrinsic.listApp (elementCode gamma)) ∧
      ¬ observes rho (fun output => output = [true])
        (encode (elementCode gamma) [.app g (.app f x)]) := by
  refine ⟨⟨hol_context (context_formed FormationSensitiveHOLUniformList.signature gamma), ?_⟩,
    wrong_composition_output_rejected⟩
  apply encode_typed (hol_element_formed gamma)
  intro value member
  have same : value = .app g (.app f x) := List.mem_singleton.mp member
  subst value
  exact application_typed (hol_functions_typed g_denotes)
    (application_typed (hol_functions_typed f_denotes) (hol_typed x_denotes.typed))

end Examples

#print axioms nativeInstance
#print axioms holMorphism
#print axioms mapTerm_typed
#print axioms applyMap_typed
#print axioms computation_include
#print axioms fusion_endpoint_admission
#print axioms hol_fusion_admitted_observed
#print axioms Examples.correct_composition_admitted_observed
#print axioms Examples.wrong_composition_typed_rejected

end FormationSensitiveNativeHOLMapExecution
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
