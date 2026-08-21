import Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilies
import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationLevelInstantiation

/-!
# Intrinsic native List maps

This module instantiates the level-polymorphic native List declaration and
constructs ordinary `map` as a Prime term using its dependent eliminator.
The proof-relevant relational lifting is developed as a separate indexed
family below the functional construction; the semantic relator remains the
interpretation target rather than a substitute for intrinsic syntax.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace NativeIndexedFamilies
namespace IntrinsicMaps

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.LevelInstance
open RussellTarski

/-! ## Level-instantiated native List declarations -/

def sameLevelSubstitution (level : LevelExpr) : Nat → LevelExpr :=
  fun _ => level

/-- Iota evidence is natural in the universe-head carrier: level
instantiation changes heads inside authored arguments but does not change
which constructor equation was used. -/
def mapIotaEvidence
    (map : Tower.Head → Tower.Head)
    {left right : Tower.Tm n}
    (evidence : Intrinsic.IotaEvidence n left right) :
    Intrinsic.IotaEvidence n (left.mapHead map) (right.mapHead map) := by
  cases evidence with
  | nil => exact .nil _ _ _ _
  | cons => exact .cons _ _ _ _ _ _
  | identity => exact .identity _ _ _ _

/-- Instantiate both List declaration levels at one chosen universe.  The
same proof-relevant iota family supplies computation after instantiation. -/
def listLevelInstance (level : LevelExpr) :
    LevelInstance Intrinsic.rawSignature (sameLevelSubstitution level) where
  computation := Intrinsic.iotaComputation
  computationMap := by
    intro n left right step
    rcases step with ⟨evidence⟩
    exact ⟨mapIotaEvidence
      (substLevelsHead (sameLevelSubstitution level)) evidence⟩

def listSignatureAt (level : LevelExpr) : Signature Tower.Head :=
  (listLevelInstance level).signature

def listRulesAt (level : LevelExpr) : Rules Tower.Head :=
  (listLevelInstance level).rules

abbrev HasTypeAt (level : LevelExpr) {n : Nat} :=
  @Presentation.HasType Tower.Head (listRulesAt level) n

def listTypeAt (level : LevelExpr) : Tower.Tm 0 :=
  substLevelsTm (sameLevelSubstitution level) Intrinsic.listType

def nilTypeAt (level : LevelExpr) : Tower.Tm 0 :=
  substLevelsTm (sameLevelSubstitution level) Intrinsic.nilType

def consTypeAt (level : LevelExpr) : Tower.Tm 0 :=
  substLevelsTm (sameLevelSubstitution level) Intrinsic.consType

def eliminateTypeAt (level : LevelExpr) : Tower.Tm 0 :=
  substLevelsTm (sameLevelSubstitution level) Intrinsic.eliminateType

@[simp] theorem typeOfAt_list (level : LevelExpr) :
    (listSignatureAt level).typeOf? Intrinsic.listName =
      some (listTypeAt level) := by
  simp [listSignatureAt, LevelInstance.signature, listTypeAt,
    Intrinsic.typeOf_list]

@[simp] theorem typeOfAt_nil (level : LevelExpr) :
    (listSignatureAt level).typeOf? Intrinsic.nilName =
      some (nilTypeAt level) := by
  simp [listSignatureAt, LevelInstance.signature, nilTypeAt,
    Intrinsic.typeOf_nil]

@[simp] theorem typeOfAt_cons (level : LevelExpr) :
    (listSignatureAt level).typeOf? Intrinsic.consName =
      some (consTypeAt level) := by
  simp [listSignatureAt, LevelInstance.signature, consTypeAt,
    Intrinsic.typeOf_cons]

@[simp] theorem typeOfAt_eliminate (level : LevelExpr) :
    (listSignatureAt level).typeOf? Intrinsic.eliminateName =
      some (eliminateTypeAt level) := by
  simp [listSignatureAt, LevelInstance.signature, eliminateTypeAt,
    Intrinsic.typeOf_eliminate]

def listSignatureAt_formed (level : LevelExpr) :
    (listSignatureAt level).Formed Tower.rules :=
  (listLevelInstance level).formed Intrinsic.rawSignature_formed

theorem listConstant_hasTypeAt (level : LevelExpr)
    {context : Tower.Ctx n} :
    HasTypeAt level context (.const Intrinsic.listName)
      (liftClosed (listTypeAt level)) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules (listSignatureAt level)
    Intrinsic.listName = some (listTypeAt level)
  apply combinedType_of_signature
  · rfl
  · exact typeOfAt_list level

theorem nilConstant_hasTypeAt (level : LevelExpr)
    {context : Tower.Ctx n} :
    HasTypeAt level context (.const Intrinsic.nilName)
      (liftClosed (nilTypeAt level)) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules (listSignatureAt level)
    Intrinsic.nilName = some (nilTypeAt level)
  apply combinedType_of_signature
  · rfl
  · exact typeOfAt_nil level

theorem consConstant_hasTypeAt (level : LevelExpr)
    {context : Tower.Ctx n} :
    HasTypeAt level context (.const Intrinsic.consName)
      (liftClosed (consTypeAt level)) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules (listSignatureAt level)
    Intrinsic.consName = some (consTypeAt level)
  apply combinedType_of_signature
  · rfl
  · exact typeOfAt_cons level

theorem eliminateConstant_hasTypeAt (level : LevelExpr)
    {context : Tower.Ctx n} :
    HasTypeAt level context (.const Intrinsic.eliminateName)
      (liftClosed (eliminateTypeAt level)) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules (listSignatureAt level)
    Intrinsic.eliminateName = some (eliminateTypeAt level)
  apply combinedType_of_signature
  · rfl
  · exact typeOfAt_eliminate level

theorem listApp_hasTypeAt (level : LevelExpr)
    {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : HasTypeAt level context element (sortTm level)) :
    HasTypeAt level context (Intrinsic.listApp element)
      (sortTm level) := by
  have application := Presentation.HasType.appElim
    (listConstant_hasTypeAt level (context := context)) elementTyping
  simpa [listTypeAt, Intrinsic.listType, Intrinsic.listApp,
    sameLevelSubstitution, substLevelsTm, substLevelsHead, liftClosed,
    LevelExpr.subst, Intrinsic.elementLevel, Tm.mapHead, sortTm,
    Presentation.rename, Presentation.inst0, Presentation.subst] using
    application

theorem nilApp_hasTypeAt (level : LevelExpr)
    {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : HasTypeAt level context element (sortTm level)) :
    HasTypeAt level context (Intrinsic.nilApp element)
      (Intrinsic.listApp element) := by
  have application := Presentation.HasType.appElim
    (nilConstant_hasTypeAt level (context := context)) elementTyping
  simpa [nilTypeAt, Intrinsic.nilType, Intrinsic.nilApp,
    Intrinsic.listApp, sameLevelSubstitution, substLevelsTm,
    substLevelsHead, LevelExpr.subst, Intrinsic.elementLevel, Tm.mapHead,
    liftClosed, sortTm, Presentation.rename,
    Presentation.inst0, Presentation.subst, Presentation.subst0,
    Presentation.liftRen, Presentation.liftSub] using application

theorem consApp_hasTypeAt (level : LevelExpr)
    {context : Tower.Ctx n} {element head tail : Tower.Tm n}
    (elementTyping : HasTypeAt level context element (sortTm level))
    (headTyping : HasTypeAt level context head element)
    (tailTyping : HasTypeAt level context tail
      (Intrinsic.listApp element)) :
    HasTypeAt level context
      (Intrinsic.consApp element head tail)
      (Intrinsic.listApp element) := by
  have consBodyAsArrows :
      Intrinsic.consBodyType =
        arrow (.var 0)
          (arrow (Intrinsic.listApp (.var 0))
            (Intrinsic.listApp (.var 0))) := by
    decide
  have consBodyLevelInvariant :
      (Intrinsic.consBodyType.mapHead
        (substLevelsHead (sameLevelSubstitution level))) =
        Intrinsic.consBodyType := by
    rfl
  have first := Presentation.HasType.appElim
    (consConstant_hasTypeAt level (context := context)) elementTyping
  rw [consBodyLevelInvariant] at first
  have firstNormalized :
      HasTypeAt level context
        (.app (.const Intrinsic.consName) element)
        (arrow element
          (arrow (Intrinsic.listApp element)
            (Intrinsic.listApp element))) := by
    simpa [consBodyAsArrows, liftClosed, Presentation.inst0,
      Presentation.subst0] using first
  have second := Presentation.HasType.appElim firstNormalized headTyping
  have secondNormalized :
      HasTypeAt level context
        (.app (.app (.const Intrinsic.consName) element) head)
        (arrow (Intrinsic.listApp element)
          (Intrinsic.listApp element)) := by
    simpa only [inst0_rename_wk] using second
  have third := Presentation.HasType.appElim secondNormalized tailTyping
  simpa only [Intrinsic.consApp, arrow, inst0_rename_wk] using third

/-! ## Intrinsic functional map -/

/-- The closed, level-polymorphic type of native List map at one instantiated
universe: `Pi A B, (A -> B) -> List A -> List B`. -/
def nativeMapType (level : LevelExpr) : Tower.Tm 0 :=
  .pi (sortTm level)
    (.pi (sortTm level)
      (.pi (arrow (.var 1) (.var 0))
        (.pi (Intrinsic.listApp (.var 2))
          (Intrinsic.listApp (.var 2)))))

def nativeMapResultLevel (level : LevelExpr) : LevelExpr :=
  .max level level

def nativeMapAfterFunctionLevel (level : LevelExpr) : LevelExpr :=
  .max (.max level level) (nativeMapResultLevel level)

def nativeMapAfterTargetLevel (level : LevelExpr) : LevelExpr :=
  .max (.succ level) (nativeMapAfterFunctionLevel level)

def nativeMapDeclarationLevel (level : LevelExpr) : LevelExpr :=
  .max (.succ level) (nativeMapAfterTargetLevel level)

def mapContextA (level : LevelExpr) : Tower.Ctx 1 :=
  .snoc .nil (sortTm level)

def mapContextAB (level : LevelExpr) : Tower.Ctx 2 :=
  .snoc (mapContextA level) (sortTm level)

def mapContextABF (level : LevelExpr) : Tower.Ctx 3 :=
  .snoc (mapContextAB level) (arrow (.var 1) (.var 0))

def mapContextABFXs (level : LevelExpr) : Tower.Ctx 4 :=
  .snoc (mapContextABF level) (Intrinsic.listApp (.var 2))

@[simp] theorem map_lookup_A (level : LevelExpr) :
    (mapContextABFXs level).lookup 3 = (sortTm level : Tower.Tm 4) := by
  rfl

@[simp] theorem map_lookup_B (level : LevelExpr) :
    (mapContextABFXs level).lookup 2 = (sortTm level : Tower.Tm 4) := by
  rfl

@[simp] theorem map_lookup_f (level : LevelExpr) :
    (mapContextABFXs level).lookup 1 =
      arrow (.var 3) (.var 2) := by
  rfl

@[simp] theorem map_lookup_xs (level : LevelExpr) :
    (mapContextABFXs level).lookup 0 =
      Intrinsic.listApp (.var 3) := by
  rfl

/-- The constant motive `fun _ => List B` used to derive map from the
dependent eliminator. -/
def nativeMapMotive : Tower.Tm 4 :=
  .lam (Intrinsic.listApp (.var 3))

def nativeMapNilCase : Tower.Tm 4 :=
  Intrinsic.nilApp (.var 2)

/-- The map step retains the native recursive result rather than re-encoding
the input List. -/
def nativeMapConsCase : Tower.Tm 4 :=
  .lam (.lam (.lam
    (Intrinsic.consApp (.var 5)
      (.app (.var 4) (.var 2)) (.var 0))))

def nativeMapConsCaseType : Tower.Tm 4 :=
  .pi (.var 3)
    (.pi (Intrinsic.listApp (.var 4))
      (.pi (Intrinsic.listApp (.var 4))
        (Intrinsic.listApp (.var 5))))

def nativeMapBody : Tower.Tm 4 :=
  Intrinsic.eliminateApp (.var 3) nativeMapMotive nativeMapNilCase
    nativeMapConsCase (.var 0)

def nativeMapTerm : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam nativeMapBody)))

theorem map_A_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) (.var 3) (sortTm level) := by
  simpa only [map_lookup_A] using
    (Presentation.HasType.var (R := listRulesAt level)
      (Γ := mapContextABFXs level) (3 : Fin 4))

theorem map_B_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) (.var 2) (sortTm level) := by
  simpa only [map_lookup_B] using
    (Presentation.HasType.var (R := listRulesAt level)
      (Γ := mapContextABFXs level) (2 : Fin 4))

theorem map_f_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) (.var 1)
      (arrow (.var 3) (.var 2)) := by
  simpa only [map_lookup_f] using
    (Presentation.HasType.var (R := listRulesAt level)
      (Γ := mapContextABFXs level) (1 : Fin 4))

theorem map_xs_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) (.var 0)
      (Intrinsic.listApp (.var 3)) := by
  simpa only [map_lookup_xs] using
    (Presentation.HasType.var (R := listRulesAt level)
      (Γ := mapContextABFXs level) (0 : Fin 4))

/-- Formation of the native map type follows from the same instantiated List
signature used by the program; no semantic host List appears in the proof. -/
theorem nativeMapType_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (.nil : Tower.Ctx 0) (nativeMapType level)
      (sortTm (nativeMapDeclarationLevel level)) := by
  unfold nativeMapType nativeMapDeclarationLevel nativeMapAfterTargetLevel
    nativeMapAfterFunctionLevel nativeMapResultLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort level)
  · exact .sort (.succ level)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort level)
    · exact .sort (.succ level)
    · apply Presentation.HasType.piForm
      · apply Presentation.HasType.piForm
        · exact Presentation.HasType.var 1
        · exact .sort level
        · exact Presentation.HasType.var 1
        · exact .sort level
        · exact .sorts level level
      · exact .sort (.max level level)
      · apply Presentation.HasType.piForm
        · apply listApp_hasTypeAt
          exact Presentation.HasType.var 2
        · exact .sort level
        · apply listApp_hasTypeAt
          exact Presentation.HasType.var 2
        · exact .sort level
        · exact .sorts level level
      · exact .sort (.max level level)
      · exact .sorts (.max level level) (.max level level)
    · exact .sort
        (.max (.max level level) (.max level level))
    · exact .sorts (.succ level)
        (.max (.max level level) (.max level level))
  · exact .sort
      (.max (.succ level)
        (.max (.max level level) (.max level level)))
  · exact .sorts (.succ level)
      (.max (.succ level)
        (.max (.max level level) (.max level level)))

theorem nativeMapMotive_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) nativeMapMotive
      (.pi (Intrinsic.listApp (.var 3)) (sortTm level)) := by
  unfold nativeMapMotive
  apply Presentation.HasType.lamIntro
  apply listApp_hasTypeAt
  exact Presentation.HasType.var 3

theorem nativeMapNilCase_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) nativeMapNilCase
      (Intrinsic.listApp (.var 2)) := by
  exact nilApp_hasTypeAt level (map_B_hasTypeAt level)

theorem nativeMapConsCase_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) nativeMapConsCase
      nativeMapConsCaseType := by
  unfold nativeMapConsCase nativeMapConsCaseType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply consApp_hasTypeAt
  · exact Presentation.HasType.var 5
  · have functionTyping :
        HasTypeAt level
          (.snoc
            (.snoc
              (.snoc (mapContextABFXs level) (.var 3))
              (Intrinsic.listApp (.var 4)))
            (Intrinsic.listApp (.var 4)))
          (.var 4) (arrow (.var 6) (.var 5)) := by
      exact Presentation.HasType.var 4
    have argumentTyping :
        HasTypeAt level
          (.snoc
            (.snoc
              (.snoc (mapContextABFXs level) (.var 3))
              (Intrinsic.listApp (.var 4)))
            (Intrinsic.listApp (.var 4)))
          (.var 2) (.var 6) := by
      exact Presentation.HasType.var 2
    simpa only [arrow, inst0_rename_wk] using
      Presentation.HasType.appElim functionTyping argumentTyping
  · exact Presentation.HasType.var 0

/-- Repeated opening after level instantiation.  These operations isolate
the generic de Bruijn algebra from the particular map program. -/
def instantiateTwoAt (level : LevelExpr)
    (element motive : Tower.Tm n) (body : Tower.Tm 2) : Tower.Tm n :=
  Presentation.subst (subst0 motive)
    (Presentation.subst (liftSub (subst0 element))
      (Presentation.rename (liftRen (liftRen Fin.elim0))
        (body.mapHead (substLevelsHead (sameLevelSubstitution level)))))

def instantiateThreeAt (level : LevelExpr)
    (element motive nilCase : Tower.Tm n)
    (body : Tower.Tm 3) : Tower.Tm n :=
  Presentation.subst (subst0 nilCase)
    (Presentation.subst (liftSub (subst0 motive))
      (Presentation.subst (liftSub (liftSub (subst0 element)))
        (Presentation.rename
          (liftRen (liftRen (liftRen Fin.elim0)))
          (body.mapHead
            (substLevelsHead (sameLevelSubstitution level))))))

def instantiateFourAt (level : LevelExpr)
    (element motive nilCase consCase : Tower.Tm n)
    (body : Tower.Tm 4) : Tower.Tm n :=
  Presentation.subst (subst0 consCase)
    (Presentation.subst (liftSub (subst0 nilCase))
      (Presentation.subst (liftSub (liftSub (subst0 motive)))
        (Presentation.subst
          (liftSub (liftSub (liftSub (subst0 element))))
          (Presentation.rename
            (liftRen (liftRen (liftRen (liftRen Fin.elim0))))
            (body.mapHead
              (substLevelsHead (sameLevelSubstitution level)))))))

theorem instantiateTwoAt_eq_subst (level : LevelExpr)
    (element motive : Tower.Tm n) (body : Tower.Tm 2) :
    instantiateTwoAt level element motive body =
      Presentation.subst
        (Intrinsic.motiveSchemaSubstitution element motive)
        (body.mapHead
          (substLevelsHead (sameLevelSubstitution level))) := by
  exact Intrinsic.instantiateTwo_eq_subst element motive
    (body.mapHead (substLevelsHead (sameLevelSubstitution level)))

theorem instantiateThreeAt_eq_subst (level : LevelExpr)
    (element motive nilCase : Tower.Tm n) (body : Tower.Tm 3) :
    instantiateThreeAt level element motive nilCase body =
      Presentation.subst
        (Intrinsic.nilCaseSchemaSubstitution element motive nilCase)
        (body.mapHead
          (substLevelsHead (sameLevelSubstitution level))) := by
  exact Intrinsic.instantiateThree_eq_subst element motive nilCase
    (body.mapHead (substLevelsHead (sameLevelSubstitution level)))

theorem instantiateFourAt_eq_subst (level : LevelExpr)
    (element motive nilCase consCase : Tower.Tm n)
    (body : Tower.Tm 4) :
    instantiateFourAt level element motive nilCase consCase body =
      Presentation.subst
        (Intrinsic.nilSchemaSubstitution element motive nilCase consCase)
        (body.mapHead
          (substLevelsHead (sameLevelSubstitution level))) := by
  exact Intrinsic.instantiateFour_eq_subst element motive nilCase consCase
    (body.mapHead (substLevelsHead (sameLevelSubstitution level)))

@[simp] theorem mapHead_nilCaseType (level : LevelExpr) :
    Intrinsic.nilCaseType.mapHead
        (substLevelsHead (sameLevelSubstitution level)) =
      Intrinsic.nilCaseType := by
  rfl

@[simp] theorem mapHead_consCaseType (level : LevelExpr) :
    Intrinsic.consCaseType.mapHead
        (substLevelsHead (sameLevelSubstitution level)) =
      Intrinsic.consCaseType := by
  rfl

@[simp] theorem mapHead_eliminateResultType (level : LevelExpr) :
    Intrinsic.eliminateResultType.mapHead
        (substLevelsHead (sameLevelSubstitution level)) =
      Intrinsic.eliminateResultType := by
  rfl

def nativeMapNilExpected (level : LevelExpr) : Tower.Tm 4 :=
  instantiateTwoAt level (.var 3) nativeMapMotive Intrinsic.nilCaseType

def nativeMapConsExpected (level : LevelExpr) : Tower.Tm 4 :=
  instantiateThreeAt level (.var 3) nativeMapMotive nativeMapNilCase
    Intrinsic.consCaseType

def nativeMapResultType (level : LevelExpr) : Tower.Tm 4 :=
  instantiateFourAt level (.var 3) nativeMapMotive nativeMapNilCase
    nativeMapConsCase Intrinsic.eliminateResultType

@[simp] theorem nativeMapNilExpected_eq (level : LevelExpr) :
    nativeMapNilExpected level =
      .app nativeMapMotive (Intrinsic.nilApp (.var 3)) := by
  rw [nativeMapNilExpected, instantiateTwoAt_eq_subst,
    mapHead_nilCaseType, Intrinsic.subst_nilCaseType_motiveSchema]

@[simp] theorem nativeMapResultType_eq (level : LevelExpr) :
    nativeMapResultType level =
      .pi (Intrinsic.listApp (.var 3))
        (.app (Presentation.rename wk nativeMapMotive) (.var 0)) := by
  rw [nativeMapResultType, instantiateFourAt_eq_subst,
    mapHead_eliminateResultType,
    Intrinsic.subst_eliminateResult_nilSchema]

/-- A constant motive beta-reduces to its closed-over target in every
declaration-aware calculus. -/
theorem constantMotive_beta
    (level : LevelExpr) (target argument : Tower.Tm n) :
    Conv (listRulesAt level).headEq
      (.app (.lam (Presentation.rename wk target)) argument)
      target (listRulesAt level).computation := by
  simpa only [Presentation.inst0_rename_wk] using
    (Relation.EqvGen.rel _ _
      (Presentation.Step.betaPi
        (root := (listRulesAt level).computation)
        (Presentation.rename wk target) argument))

@[simp] theorem inst0_listApp_succVar
    (argument : Tower.Tm n) (index : Fin n) :
    Presentation.inst0 argument
        (Intrinsic.listApp (.var index.succ)) =
      Intrinsic.listApp (.var index) := by
  rfl

/-- The specialized constant motive used by map, stated without any numeral
arithmetic in the de Bruijn indices. -/
theorem listMotive_beta (level : LevelExpr)
    (argument : Tower.Tm n) (index : Fin n) :
    Conv (listRulesAt level).headEq
      (.app (.lam (Intrinsic.listApp (.var index.succ))) argument)
      (Intrinsic.listApp (.var index))
      (listRulesAt level).computation := by
  simpa only [inst0_listApp_succVar] using
    (Relation.EqvGen.rel _ _
      (Presentation.Step.betaPi
        (root := (listRulesAt level).computation)
        (Intrinsic.listApp (.var index.succ)) argument))

theorem nativeMapMotive_beta (level : LevelExpr)
    (argument : Tower.Tm 4) :
    Conv (listRulesAt level).headEq
      (.app nativeMapMotive argument)
      (Intrinsic.listApp (.var 2))
      (listRulesAt level).computation := by
  exact listMotive_beta level argument (2 : Fin 4)

def nativeMapConsRedexType : Tower.Tm 4 :=
  .pi (.var 3)
    (.pi (Intrinsic.listApp (.var 4))
      (.pi
        (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0))
        (.app (.lam (Intrinsic.listApp (.var 6)))
          (Intrinsic.consApp (.var 6) (.var 2) (.var 1)))))

@[simp] theorem nativeMapConsExpected_eq (level : LevelExpr) :
    nativeMapConsExpected level = nativeMapConsRedexType := by
  rw [nativeMapConsExpected, instantiateThreeAt_eq_subst,
    mapHead_consCaseType]
  rfl

theorem nativeMapConsCase_hasExpectedTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) nativeMapConsCase
      (nativeMapConsExpected level) := by
  rw [nativeMapConsExpected_eq]
  unfold nativeMapConsCase nativeMapConsRedexType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  have functionTyping :
      HasTypeAt level
        (.snoc
          (.snoc
            (.snoc (mapContextABFXs level) (.var 3))
            (Intrinsic.listApp (.var 4)))
          (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0)))
        (.var 4) (arrow (.var 6) (.var 5)) := by
    exact Presentation.HasType.var 4
  have headTyping :
      HasTypeAt level
        (.snoc
          (.snoc
            (.snoc (mapContextABFXs level) (.var 3))
            (Intrinsic.listApp (.var 4)))
          (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0)))
        (.var 2) (.var 6) := by
    exact Presentation.HasType.var 2
  have mappedHeadTyping :
      HasTypeAt level
        (.snoc
          (.snoc
            (.snoc (mapContextABFXs level) (.var 3))
            (Intrinsic.listApp (.var 4)))
          (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0)))
        (.app (.var 4) (.var 2)) (.var 5) := by
    simpa only [arrow, inst0_rename_wk] using
      Presentation.HasType.appElim functionTyping headTyping
  have recursiveTypingAtMotive :
      HasTypeAt level
        (.snoc
          (.snoc
            (.snoc (mapContextABFXs level) (.var 3))
            (Intrinsic.listApp (.var 4)))
          (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0)))
        (.var 0)
        (.app (.lam (Intrinsic.listApp (.var 6))) (.var 1)) := by
    exact Presentation.HasType.var 0
  have recursiveTyping :
      HasTypeAt level
        (.snoc
          (.snoc
            (.snoc (mapContextABFXs level) (.var 3))
            (Intrinsic.listApp (.var 4)))
          (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0)))
        (.var 0) (Intrinsic.listApp (.var 5)) := by
    apply Presentation.HasType.conv recursiveTypingAtMotive
    exact listMotive_beta level (.var (1 : Fin 7)) (5 : Fin 7)
  have constructed :
      HasTypeAt level
        (.snoc
          (.snoc
            (.snoc (mapContextABFXs level) (.var 3))
            (Intrinsic.listApp (.var 4)))
          (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0)))
        (Intrinsic.consApp (.var 5)
          (.app (.var 4) (.var 2)) (.var 0))
        (Intrinsic.listApp (.var 5)) := by
    exact consApp_hasTypeAt level
      (Presentation.HasType.var
        (R := listRulesAt level)
        (Γ :=
          (.snoc
            (.snoc
              (.snoc (mapContextABFXs level) (.var 3))
              (Intrinsic.listApp (.var 4)))
            (.app (.lam (Intrinsic.listApp (.var 5))) (.var 0))))
        (5 : Fin 7))
      mappedHeadTyping recursiveTyping
  apply Presentation.HasType.conv constructed
  have resultBeta :
      Conv (listRulesAt level).headEq
        (.app (.lam (Intrinsic.listApp (.var 6)))
          (Intrinsic.consApp (.var 6) (.var 2) (.var 1)) : Tower.Tm 7)
        (Intrinsic.listApp (.var 5) : Tower.Tm 7)
        (listRulesAt level).computation := by
    exact listMotive_beta level
      (Intrinsic.consApp (.var 6) (.var 2) (.var 1) : Tower.Tm 7)
      (5 : Fin 7)
  exact Relation.EqvGen.symm _ _ resultBeta

theorem nativeMapBody_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (mapContextABFXs level) nativeMapBody
      (Intrinsic.listApp (.var 2)) := by
  unfold nativeMapBody
  have afterElement := Presentation.HasType.appElim
    (eliminateConstant_hasTypeAt level
      (context := mapContextABFXs level))
    (map_A_hasTypeAt level)
  have afterMotive := Presentation.HasType.appElim afterElement
    (nativeMapMotive_hasTypeAt level)
  have nilTyping :
      HasTypeAt level (mapContextABFXs level) nativeMapNilCase
        (nativeMapNilExpected level) := by
    rw [nativeMapNilExpected_eq]
    apply Presentation.HasType.conv (nativeMapNilCase_hasTypeAt level)
    exact Relation.EqvGen.symm _ _
      (nativeMapMotive_beta level (Intrinsic.nilApp (.var 3)))
  have afterNil := Presentation.HasType.appElim afterMotive nilTyping
  have consTyping :
      HasTypeAt level (mapContextABFXs level) nativeMapConsCase
        (nativeMapConsExpected level) := by
    exact nativeMapConsCase_hasExpectedTypeAt level
  have afterCons := Presentation.HasType.appElim afterNil consTyping
  have afterConsNormalized :
      HasTypeAt level (mapContextABFXs level)
        (.app
          (.app
            (.app
              (.app (.const Intrinsic.eliminateName) (.var 3))
              nativeMapMotive)
            nativeMapNilCase)
          nativeMapConsCase)
        (nativeMapResultType level) := by
    simpa [nativeMapResultType, instantiateFourAt,
      Presentation.inst0] using afterCons
  rw [nativeMapResultType_eq] at afterConsNormalized
  have afterList := Presentation.HasType.appElim afterConsNormalized
    (map_xs_hasTypeAt level)
  change HasTypeAt level (mapContextABFXs level)
    (Intrinsic.eliminateApp (.var 3) nativeMapMotive nativeMapNilCase
      nativeMapConsCase (.var 0))
    (.app
      (Presentation.inst0 (.var 0)
        (Presentation.rename wk nativeMapMotive))
      (.var 0)) at afterList
  rw [Presentation.inst0_rename_wk] at afterList
  apply Presentation.HasType.conv afterList
  exact nativeMapMotive_beta level (.var 0)

/-- The intrinsic program itself inhabits the native map type.  In
particular, this is not the semantic `List.map` reintroduced as a constant:
the term is four lambdas followed by the declared List eliminator. -/
theorem nativeMapTerm_hasTypeAt (level : LevelExpr) :
    HasTypeAt level (.nil : Tower.Ctx 0) nativeMapTerm
      (nativeMapType level) := by
  unfold nativeMapTerm nativeMapType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  exact nativeMapBody_hasTypeAt level

/-! ## Axiom audit for the reusable instantiation seam -/

#print axioms listLevelInstance
#print axioms listSignatureAt_formed
#print axioms listApp_hasTypeAt
#print axioms nilApp_hasTypeAt
#print axioms consApp_hasTypeAt
#print axioms nativeMapMotive_beta
#print axioms nativeMapType_hasTypeAt
#print axioms nativeMapConsCase_hasExpectedTypeAt
#print axioms nativeMapBody_hasTypeAt
#print axioms nativeMapTerm_hasTypeAt

end IntrinsicMaps
end NativeIndexedFamilies
end Mettapedia.Languages.MeTTa.PureKernel.Universe
