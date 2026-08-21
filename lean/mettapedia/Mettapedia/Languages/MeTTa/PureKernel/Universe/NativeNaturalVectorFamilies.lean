import Mettapedia.Languages.MeTTa.PureKernel.Universe.IndexedFamilyDeclaration
import Mettapedia.Languages.MeTTa.PureKernel.Universe.SchemaElaboration

/-!
# Native natural numbers and length-indexed vectors

This module is the first object-language stress test of Prime's generic
indexed-family declaration interface.  It declares Peano naturals and vectors
in one signature.  Vector constructors change the length index, and the
dependent eliminator retains both the index and the vector in its motive.

Formation, structural positivity, and canonical typed computation receipts
are established independently of the later uniform preservation theorem.
Consequently the declarations form informative candidates before their raw
equations receive checked computational authority.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace NativeNaturalVectorFamilies

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

def elementLevel : LevelExpr := .param 0
def motiveLevel : LevelExpr := .param 1
def natLevel : LevelExpr := Tower.zero

def natName : DeclName := `Prime.Nat
def zeroName : DeclName := `Prime.Nat.zero
def succName : DeclName := `Prime.Nat.succ
def natEliminateName : DeclName := `Prime.Nat.eliminate
def vecName : DeclName := `Prime.Vec
def vnilName : DeclName := `Prime.Vec.nil
def vconsName : DeclName := `Prime.Vec.cons
def vecEliminateName : DeclName := `Prime.Vec.eliminate

def natTm : Tower.Tm n := .const natName
def zeroTm : Tower.Tm n := .const zeroName
def succApp (number : Tower.Tm n) : Tower.Tm n :=
  .app (.const succName) number

def natEliminateApp (motive zeroCase succCase number : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const natEliminateName) motive)
        zeroCase)
      succCase)
    number

def vecApp (element length : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const vecName) element) length

def vnilApp (element : Tower.Tm n) : Tower.Tm n :=
  .app (.const vnilName) element

def vconsApp (element length head tail : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const vconsName) element)
        length)
      head)
    tail

def vecEliminateApp
    (element motive nilCase consCase length vector : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app (.const vecEliminateName) element)
            motive)
          nilCase)
        consCase)
      length)
    vector

@[simp] theorem rename_natTm (renameMap : Ren n m) :
    Presentation.rename renameMap (natTm : Tower.Tm n) = natTm := rfl

@[simp] theorem subst_natTm (substitution : Sub Tower.Head n m) :
    Presentation.subst substitution (natTm : Tower.Tm n) = natTm := rfl

@[simp] theorem rename_succApp (renameMap : Ren n m)
    (number : Tower.Tm n) :
    Presentation.rename renameMap (succApp number) =
      succApp (Presentation.rename renameMap number) := rfl

@[simp] theorem subst_succApp (substitution : Sub Tower.Head n m)
    (number : Tower.Tm n) :
    Presentation.subst substitution (succApp number) =
      succApp (Presentation.subst substitution number) := rfl

@[simp] theorem rename_vecApp (renameMap : Ren n m)
    (element length : Tower.Tm n) :
    Presentation.rename renameMap (vecApp element length) =
      vecApp (Presentation.rename renameMap element)
        (Presentation.rename renameMap length) := rfl

@[simp] theorem subst_vecApp (substitution : Sub Tower.Head n m)
    (element length : Tower.Tm n) :
    Presentation.subst substitution (vecApp element length) =
      vecApp (Presentation.subst substitution element)
        (Presentation.subst substitution length) := rfl

@[simp] theorem inst0_succApp (argument : Tower.Tm n)
    (number : Tower.Tm (n + 1)) :
    Presentation.inst0 argument (succApp number) =
      succApp (Presentation.inst0 argument number) := rfl

@[simp] theorem inst0_vecApp (argument : Tower.Tm n)
    (element length : Tower.Tm (n + 1)) :
    Presentation.inst0 argument (vecApp element length) =
      vecApp (Presentation.inst0 argument element)
        (Presentation.inst0 argument length) := rfl

/-! ## Closed declaration types -/

/-- `Nat : U 0`. -/
def natType : Tower.Tm 0 := sortTm natLevel

/-- `zero : Nat`. -/
def zeroType : Tower.Tm 0 := natTm

/-- `succ : Nat → Nat`. -/
def succType : Tower.Tm 0 := .pi natTm natTm

/-- A natural-number motive `Nat → U ρ`. -/
def natMotiveType : Tower.Tm 0 :=
  .pi natTm (sortTm motiveLevel)

/-- In context `P`, the zero branch has type `P zero`. -/
def natZeroCaseType : Tower.Tm 1 :=
  .app (.var 0) zeroTm

/-- In context `P,z`, the successor branch is
`Π n, P n → P (succ n)`. -/
def natSuccCaseType : Tower.Tm 2 :=
  .pi natTm
    (.pi (.app (.var 2) (.var 0))
      (.app (.var 3) (succApp (.var 1))))

/-- In context `P,z,s`, natural elimination yields `Π n, P n`. -/
def natEliminateResultType : Tower.Tm 3 :=
  .pi natTm (.app (.var 3) (.var 0))

def natEliminateType : Tower.Tm 0 :=
  .pi natMotiveType
    (.pi natZeroCaseType
      (.pi natSuccCaseType natEliminateResultType))

/-- `Vec : Π (A : U α), Nat → U α`. -/
def vecType : Tower.Tm 0 :=
  .pi (sortTm elementLevel)
    (.pi natTm (sortTm elementLevel))

/-- `vnil : Π A, Vec A zero`. -/
def vnilType : Tower.Tm 0 :=
  .pi (sortTm elementLevel) (vecApp (.var 0) zeroTm)

/-- The portion of `vcons` below its element-type binder. -/
def vconsBodyType : Tower.Tm 1 :=
  .pi natTm
    (.pi (.var 1)
      (.pi (vecApp (.var 2) (.var 1))
        (vecApp (.var 3) (succApp (.var 2)))))

/-- `vcons : Π A n, A → Vec A n → Vec A (succ n)`. -/
def vconsType : Tower.Tm 0 :=
  .pi (sortTm elementLevel) vconsBodyType

/-- In context `A`, a vector motive depends on length and vector. -/
def vecMotiveType : Tower.Tm 1 :=
  .pi natTm
    (.pi (vecApp (.var 1) (.var 0)) (sortTm motiveLevel))

/-- In context `A,P`, the nil branch is `P zero (vnil A)`. -/
def vecNilCaseType : Tower.Tm 2 :=
  .app
    (.app (.var 0) zeroTm)
    (vnilApp (.var 1))

/-- In context `A,P,z`, the cons branch receives length, head, tail, and the
recursive result before producing the successor-indexed motive. -/
def vecConsCaseType : Tower.Tm 3 :=
  .pi natTm
    (.pi (.var 3)
      (.pi (vecApp (.var 4) (.var 1))
        (.pi
          (.app (.app (.var 4) (.var 2)) (.var 0))
          (.app
            (.app (.var 5) (succApp (.var 3)))
            (vconsApp (.var 6) (.var 3) (.var 2) (.var 1))))))

/-- In context `A,P,z,s`, vector elimination returns every indexed fibre. -/
def vecEliminateResultType : Tower.Tm 4 :=
  .pi natTm
    (.pi (vecApp (.var 4) (.var 0))
      (.app (.app (.var 4) (.var 1)) (.var 0)))

def vecEliminateType : Tower.Tm 0 :=
  .pi (sortTm elementLevel)
    (.pi vecMotiveType
      (.pi vecNilCaseType
        (.pi vecConsCaseType vecEliminateResultType)))

/-! ## Proof-relevant iota computation -/

inductive IotaEvidence (n : Nat) : Tower.Tm n → Tower.Tm n → Type where
  | natZero (motive zeroCase succCase : Tower.Tm n) :
      IotaEvidence n
        (natEliminateApp motive zeroCase succCase zeroTm)
        zeroCase
  | natSucc (motive zeroCase succCase number : Tower.Tm n) :
      IotaEvidence n
        (natEliminateApp motive zeroCase succCase (succApp number))
        (.app (.app succCase number)
          (natEliminateApp motive zeroCase succCase number))
  | vecNil (element motive nilCase consCase : Tower.Tm n) :
      IotaEvidence n
        (vecEliminateApp element motive nilCase consCase zeroTm
          (vnilApp element))
        nilCase
  | vecCons (element motive nilCase consCase length head tail : Tower.Tm n) :
      IotaEvidence n
        (vecEliminateApp element motive nilCase consCase (succApp length)
          (vconsApp element length head tail))
        (.app
          (.app
            (.app
              (.app consCase length)
              head)
            tail)
          (vecEliminateApp element motive nilCase consCase length tail))

def IotaEvidence.rename {left right : Tower.Tm n}
    (step : IotaEvidence n left right) (renameMap : Ren n m) :
    IotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases step with
  | natZero => exact .natZero _ _ _
  | natSucc => exact .natSucc _ _ _ _
  | vecNil => exact .vecNil _ _ _ _
  | vecCons => exact .vecCons _ _ _ _ _ _ _

def IotaEvidence.substitute {left right : Tower.Tm n}
    (step : IotaEvidence n left right) (substitution : Sub Tower.Head n m) :
    IotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases step with
  | natZero => exact .natZero _ _ _
  | natSucc => exact .natSucc _ _ _ _
  | vecNil => exact .vecNil _ _ _ _
  | vecCons => exact .vecCons _ _ _ _ _ _ _

def proofRelevantIotaComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := IotaEvidence _
  rename := by
    intro n m renameMap left right step
    exact step.rename renameMap
  substitute := by
    intro n m substitution left right step
    exact step.substitute substitution

def iotaComputation : RootComputation Tower.Head :=
  proofRelevantIotaComputation.support

def declarations : List (DeclName × Entry Tower.Head) :=
  [(natName, { type := natType }),
   (zeroName, { type := zeroType }),
   (succName, { type := succType }),
   (natEliminateName, { type := natEliminateType }),
   (vecName, { type := vecType }),
   (vnilName, { type := vnilType }),
   (vconsName, { type := vconsType }),
   (vecEliminateName, { type := vecEliminateType })]

def rawSignature : Signature Tower.Head where
  entries := (Signature.ofList declarations).entries
  computation := iotaComputation

abbrev rules : Rules Tower.Head :=
  extendRules Tower.rules rawSignature

@[simp] theorem typeOf_nat :
    rawSignature.typeOf? natName = some natType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    natType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_zero :
    rawSignature.typeOf? zeroName = some zeroType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    zeroType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_succ :
    rawSignature.typeOf? succName = some succType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    succType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_natEliminate :
    rawSignature.typeOf? natEliminateName = some natEliminateType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    natEliminateType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_vec :
    rawSignature.typeOf? vecName = some vecType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    vecType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_vnil :
    rawSignature.typeOf? vnilName = some vnilType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    vnilType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_vcons :
    rawSignature.typeOf? vconsName = some vconsType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    vconsType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_vecEliminate :
    rawSignature.typeOf? vecEliminateName = some vecEliminateType := by
  simp [rawSignature, declarations, natName, zeroName, succName,
    natEliminateName, vecName, vnilName, vconsName, vecEliminateName,
    vecEliminateType, Signature.ofList, Signature.insert, Signature.typeOf?]

abbrev HasType {n : Nat} :=
  @Presentation.HasType Tower.Head rules n

private theorem constant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawSignature.typeOf? name = some type)
    {context : Tower.Ctx n} :
    HasType context (.const name) (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature name = some type
  apply combinedType_of_signature
  · rfl
  · exact lookup

theorem natConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const natName) (liftClosed natType) :=
  constant_hasType typeOf_nat

theorem zeroConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const zeroName) (liftClosed zeroType) :=
  constant_hasType typeOf_zero

theorem succConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const succName) (liftClosed succType) :=
  constant_hasType typeOf_succ

theorem natEliminateConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const natEliminateName) (liftClosed natEliminateType) :=
  constant_hasType typeOf_natEliminate

theorem vecConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const vecName) (liftClosed vecType) :=
  constant_hasType typeOf_vec

theorem vnilConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const vnilName) (liftClosed vnilType) :=
  constant_hasType typeOf_vnil

theorem vconsConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const vconsName) (liftClosed vconsType) :=
  constant_hasType typeOf_vcons

theorem vecEliminateConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const vecEliminateName) (liftClosed vecEliminateType) :=
  constant_hasType typeOf_vecEliminate

theorem natTm_hasType {context : Tower.Ctx n} :
    HasType context natTm (sortTm natLevel) := by
  simpa [natTm, natType, natLevel, liftClosed, sortTm,
    Presentation.rename] using (natConstant_hasType (context := context))

theorem zeroTm_hasType {context : Tower.Ctx n} :
    HasType context zeroTm natTm := by
  simpa [zeroTm, zeroType, natTm, liftClosed, Presentation.rename] using
    (zeroConstant_hasType (context := context))

theorem succApp_hasType {context : Tower.Ctx n} {number : Tower.Tm n}
    (numberTyping : HasType context number natTm) :
    HasType context (succApp number) natTm := by
  have application := Presentation.HasType.appElim
    (succConstant_hasType (context := context)) numberTyping
  simpa [succType, succApp, natTm, liftClosed, Presentation.rename,
    Presentation.inst0, Presentation.subst] using application

theorem vecApp_hasType {context : Tower.Ctx n}
    {element length : Tower.Tm n}
    (elementTyping : HasType context element (sortTm elementLevel))
    (lengthTyping : HasType context length natTm) :
    HasType context (vecApp element length) (sortTm elementLevel) := by
  have afterElement := Presentation.HasType.appElim
    (vecConstant_hasType (context := context)) elementTyping
  have afterLength := Presentation.HasType.appElim afterElement lengthTyping
  simpa [vecType, vecApp, natTm, liftClosed, sortTm, Presentation.rename,
    Presentation.inst0, Presentation.subst] using afterLength

theorem vnilApp_hasType {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : HasType context element (sortTm elementLevel)) :
    HasType context (vnilApp element) (vecApp element zeroTm) := by
  have application := Presentation.HasType.appElim
    (vnilConstant_hasType (context := context)) elementTyping
  simpa [vnilType, vnilApp, vecApp, zeroTm, liftClosed, sortTm,
    Presentation.rename, Presentation.inst0, Presentation.subst,
    Presentation.subst0, Presentation.liftRen, Presentation.liftSub] using
    application

@[simp] theorem liftedSingleton_at_one (element : Tower.Tm n) :
    Fin.cases (.var 0 : Tower.Tm (n + 1))
        (fun _ : Fin 1 => Presentation.rename wk element)
        (1 : Fin 2) =
      Presentation.rename wk element := by
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide]
  rfl

theorem vconsApp_hasType {context : Tower.Ctx n}
    {element length head tail : Tower.Tm n}
    (elementTyping : HasType context element (sortTm elementLevel))
    (lengthTyping : HasType context length natTm)
    (headTyping : HasType context head element)
    (tailTyping : HasType context tail (vecApp element length)) :
    HasType context (vconsApp element length head tail)
      (vecApp element (succApp length)) := by
  have vconsBodyAsArrows :
      vconsBodyType =
        .pi natTm
          (arrow (.var (Fin.succ 0))
            (arrow (vecApp (.var (Fin.succ 0)) (.var 0))
              (vecApp (.var (Fin.succ 0)) (succApp (.var 0))))) := by
    decide
  have first := Presentation.HasType.appElim
    (vconsConstant_hasType (context := context)) elementTyping
  have firstNormalized :
      HasType context (.app (.const vconsName) element)
        (.pi natTm
          (arrow (Presentation.rename wk element)
            (arrow
              (vecApp (Presentation.rename wk element) (.var 0))
              (vecApp (Presentation.rename wk element)
                (succApp (.var 0)))))) := by
    simpa [vconsType, vconsBodyAsArrows, liftClosed,
      Presentation.subst, Presentation.liftSub] using first
  have second := Presentation.HasType.appElim firstNormalized lengthTyping
  have secondNormalized :
      HasType context
        (.app (.app (.const vconsName) element) length)
        (arrow element
          (arrow (vecApp element length)
            (vecApp element (succApp length)))) := by
    simpa only [inst0_arrow, inst0_rename_wk, inst0_vecApp,
      inst0_succApp, inst0_var_zero] using second
  have third := Presentation.HasType.appElim secondNormalized headTyping
  have thirdNormalized :
      HasType context
        (.app (.app (.app (.const vconsName) element) length) head)
        (arrow (vecApp element length)
          (vecApp element (succApp length))) := by
    simpa only [inst0_rename_wk] using third
  have fourth := Presentation.HasType.appElim thirdNormalized tailTyping
  simpa only [vconsApp, arrow, inst0_rename_wk] using fourth

theorem natMotiveApp_hasType {context : Tower.Ctx n}
    {motive number : Tower.Tm n}
    (motiveTyping : HasType context motive
      (.pi natTm (sortTm motiveLevel)))
    (numberTyping : HasType context number natTm) :
    HasType context (.app motive number) (sortTm motiveLevel) := by
  have application := Presentation.HasType.appElim motiveTyping numberTyping
  simpa [sortTm, Presentation.inst0, Presentation.subst] using application

theorem vecMotiveApp_hasType {context : Tower.Ctx n}
    {element motive length vector : Tower.Tm n}
    (motiveTyping : HasType context motive
      (.pi natTm
        (.pi (vecApp (Presentation.rename wk element) (.var 0))
          (sortTm motiveLevel))))
    (lengthTyping : HasType context length natTm)
    (vectorTyping : HasType context vector (vecApp element length)) :
    HasType context (.app (.app motive length) vector)
      (sortTm motiveLevel) := by
  have afterLength := Presentation.HasType.appElim motiveTyping lengthTyping
  have elementCancellation :
      Presentation.subst (Presentation.subst0 length)
          (Presentation.rename wk element) = element := by
    exact inst0_rename_wk length element
  have afterLengthNormalized :
      HasType context (.app motive length)
        (.pi (vecApp element length) (sortTm motiveLevel)) := by
    simpa [vecApp, sortTm, Presentation.inst0, Presentation.subst,
      Presentation.subst0, Presentation.liftSub, elementCancellation] using
      afterLength
  have afterVector := Presentation.HasType.appElim
    afterLengthNormalized vectorTyping
  simpa [vecApp, sortTm, Presentation.inst0, Presentation.subst,
    Presentation.subst0, Presentation.liftSub] using afterVector

/-! ## Declaration formation -/

def natDeclarationLevel : LevelExpr := .succ natLevel

def succDeclarationLevel : LevelExpr := .max natLevel natLevel

theorem natType_hasType :
    HasType (.nil : Tower.Ctx 0) natType
      (sortTm natDeclarationLevel) := by
  exact Presentation.HasType.headType (.sort natLevel)

theorem zeroType_hasType :
    HasType (.nil : Tower.Ctx 0) zeroType (sortTm natLevel) := by
  exact natTm_hasType

theorem succType_hasType :
    HasType (.nil : Tower.Ctx 0) succType
      (sortTm succDeclarationLevel) := by
  unfold succType succDeclarationLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · exact natTm_hasType
  · exact .sort natLevel
  · exact .sorts natLevel natLevel

def natContextP : Tower.Ctx 1 :=
  .snoc .nil natMotiveType

def natContextPZ : Tower.Ctx 2 :=
  .snoc natContextP natZeroCaseType

def natContextPZS : Tower.Ctx 3 :=
  .snoc natContextPZ natSuccCaseType

def natMotiveTypeLevel : LevelExpr :=
  .max natLevel (.succ motiveLevel)

theorem natMotiveType_hasType :
    HasType (.nil : Tower.Ctx 0) natMotiveType
      (sortTm natMotiveTypeLevel) := by
  unfold natMotiveType natMotiveTypeLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · exact .headType (.sort motiveLevel)
  · exact .sort (.succ motiveLevel)
  · exact .sorts natLevel (.succ motiveLevel)

theorem natZeroCaseType_hasType :
    HasType natContextP natZeroCaseType (sortTm motiveLevel) := by
  unfold natContextP natZeroCaseType
  apply natMotiveApp_hasType
  · exact Presentation.HasType.var 0
  · exact zeroTm_hasType

def natSuccInnerLevel : LevelExpr :=
  .max motiveLevel motiveLevel

def natSuccCaseLevel : LevelExpr :=
  .max natLevel natSuccInnerLevel

theorem natSuccCaseType_hasType :
    HasType natContextPZ natSuccCaseType
      (sortTm natSuccCaseLevel) := by
  unfold natContextPZ natSuccCaseType natSuccCaseLevel natSuccInnerLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · apply Presentation.HasType.piForm
    · apply natMotiveApp_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · exact .sort motiveLevel
    · apply natMotiveApp_hasType
      · exact Presentation.HasType.var 3
      · apply succApp_hasType
        exact Presentation.HasType.var 1
    · exact .sort motiveLevel
    · exact .sorts motiveLevel motiveLevel
  · exact .sort (.max motiveLevel motiveLevel)
  · exact .sorts natLevel (.max motiveLevel motiveLevel)

def natEliminateResultLevel : LevelExpr :=
  .max natLevel motiveLevel

theorem natEliminateResultType_hasType :
    HasType natContextPZS natEliminateResultType
      (sortTm natEliminateResultLevel) := by
  unfold natContextPZS natEliminateResultType natEliminateResultLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · apply natMotiveApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 0
  · exact .sort motiveLevel
  · exact .sorts natLevel motiveLevel

def natEliminateAfterSuccLevel : LevelExpr :=
  .max natSuccCaseLevel natEliminateResultLevel

def natEliminateAfterZeroLevel : LevelExpr :=
  .max motiveLevel natEliminateAfterSuccLevel

def natEliminateDeclarationLevel : LevelExpr :=
  .max natMotiveTypeLevel natEliminateAfterZeroLevel

theorem natEliminateType_hasType :
    HasType (.nil : Tower.Ctx 0) natEliminateType
      (sortTm natEliminateDeclarationLevel) := by
  unfold natEliminateType natEliminateDeclarationLevel
    natEliminateAfterZeroLevel natEliminateAfterSuccLevel
  apply Presentation.HasType.piForm
  · exact natMotiveType_hasType
  · exact .sort natMotiveTypeLevel
  · apply Presentation.HasType.piForm
    · exact natZeroCaseType_hasType
    · exact .sort motiveLevel
    · apply Presentation.HasType.piForm
      · exact natSuccCaseType_hasType
      · exact .sort natSuccCaseLevel
      · exact natEliminateResultType_hasType
      · exact .sort natEliminateResultLevel
      · exact .sorts natSuccCaseLevel natEliminateResultLevel
    · exact .sort natEliminateAfterSuccLevel
    · exact .sorts motiveLevel natEliminateAfterSuccLevel
  · exact .sort natEliminateAfterZeroLevel
  · exact .sorts natMotiveTypeLevel natEliminateAfterZeroLevel

def vecContextA : Tower.Ctx 1 :=
  .snoc .nil (sortTm elementLevel)

def vecContextAP : Tower.Ctx 2 :=
  .snoc vecContextA vecMotiveType

def vecContextAPZ : Tower.Ctx 3 :=
  .snoc vecContextAP vecNilCaseType

def vecContextAPZS : Tower.Ctx 4 :=
  .snoc vecContextAPZ vecConsCaseType

def vecBodyLevel : LevelExpr :=
  .max natLevel (.succ elementLevel)

def vecDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) vecBodyLevel

theorem vecType_hasType :
    HasType (.nil : Tower.Ctx 0) vecType
      (sortTm vecDeclarationLevel) := by
  unfold vecType vecDeclarationLevel vecBodyLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply Presentation.HasType.piForm
    · exact natTm_hasType
    · exact .sort natLevel
    · exact .headType (.sort elementLevel)
    · exact .sort (.succ elementLevel)
    · exact .sorts natLevel (.succ elementLevel)
  · exact .sort vecBodyLevel
  · exact .sorts (.succ elementLevel) vecBodyLevel

def vnilDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) elementLevel

theorem vnilType_hasType :
    HasType (.nil : Tower.Ctx 0) vnilType
      (sortTm vnilDeclarationLevel) := by
  unfold vnilType vnilDeclarationLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply vecApp_hasType
    · exact Presentation.HasType.var 0
    · exact zeroTm_hasType
  · exact .sort elementLevel
  · exact .sorts (.succ elementLevel) elementLevel

def vconsTailLevel : LevelExpr :=
  .max elementLevel elementLevel

def vconsHeadLevel : LevelExpr :=
  .max elementLevel vconsTailLevel

def vconsBodyLevel : LevelExpr :=
  .max natLevel vconsHeadLevel

def vconsDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) vconsBodyLevel

theorem vconsBodyType_hasType :
    HasType vecContextA vconsBodyType (sortTm vconsBodyLevel) := by
  unfold vecContextA vconsBodyType vconsBodyLevel vconsHeadLevel
    vconsTailLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · apply Presentation.HasType.piForm
    · exact Presentation.HasType.var 1
    · exact .sort elementLevel
    · apply Presentation.HasType.piForm
      · apply vecApp_hasType
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 1
      · exact .sort elementLevel
      · apply vecApp_hasType
        · exact Presentation.HasType.var 3
        · apply succApp_hasType
          exact Presentation.HasType.var 2
      · exact .sort elementLevel
      · exact .sorts elementLevel elementLevel
    · exact .sort vconsTailLevel
    · exact .sorts elementLevel vconsTailLevel
  · exact .sort vconsHeadLevel
  · exact .sorts natLevel vconsHeadLevel

theorem vconsType_hasType :
    HasType (.nil : Tower.Ctx 0) vconsType
      (sortTm vconsDeclarationLevel) := by
  unfold vconsType vconsDeclarationLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · exact vconsBodyType_hasType
  · exact .sort vconsBodyLevel
  · exact .sorts (.succ elementLevel) vconsBodyLevel

def vecMotiveInnerLevel : LevelExpr :=
  .max elementLevel (.succ motiveLevel)

def vecMotiveTypeLevel : LevelExpr :=
  .max natLevel vecMotiveInnerLevel

theorem vecMotiveType_hasType :
    HasType vecContextA vecMotiveType (sortTm vecMotiveTypeLevel) := by
  unfold vecContextA vecMotiveType vecMotiveTypeLevel vecMotiveInnerLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · apply Presentation.HasType.piForm
    · apply vecApp_hasType
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · exact .sort elementLevel
    · exact .headType (.sort motiveLevel)
    · exact .sort (.succ motiveLevel)
    · exact .sorts elementLevel (.succ motiveLevel)
  · exact .sort vecMotiveInnerLevel
  · exact .sorts natLevel vecMotiveInnerLevel

theorem vecNilCaseType_hasType :
    HasType vecContextAP vecNilCaseType (sortTm motiveLevel) := by
  unfold vecContextAP vecNilCaseType
  apply vecMotiveApp_hasType (element := (.var 1 : Tower.Tm 2))
  · exact Presentation.HasType.var 0
  · exact zeroTm_hasType
  · apply vnilApp_hasType
    exact Presentation.HasType.var 1

def vecConsHypothesisLevel : LevelExpr :=
  .max motiveLevel motiveLevel

def vecConsTailLevel : LevelExpr :=
  .max elementLevel vecConsHypothesisLevel

def vecConsHeadLevel : LevelExpr :=
  .max elementLevel vecConsTailLevel

def vecConsCaseLevel : LevelExpr :=
  .max natLevel vecConsHeadLevel

theorem vecConsCaseType_hasType :
    HasType vecContextAPZ vecConsCaseType
      (sortTm vecConsCaseLevel) := by
  unfold vecContextAPZ vecConsCaseType vecConsCaseLevel vecConsHeadLevel
    vecConsTailLevel vecConsHypothesisLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · apply Presentation.HasType.piForm
    · exact Presentation.HasType.var 3
    · exact .sort elementLevel
    · apply Presentation.HasType.piForm
      · apply vecApp_hasType
        · exact Presentation.HasType.var 4
        · exact Presentation.HasType.var 1
      · exact .sort elementLevel
      · apply Presentation.HasType.piForm
        · apply vecMotiveApp_hasType (element := (.var 5 : Tower.Tm 6))
          · exact Presentation.HasType.var 4
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 0
        · exact .sort motiveLevel
        · apply vecMotiveApp_hasType (element := (.var 6 : Tower.Tm 7))
          · exact Presentation.HasType.var 5
          · apply succApp_hasType
            exact Presentation.HasType.var 3
          · apply vconsApp_hasType
            · exact Presentation.HasType.var 6
            · exact Presentation.HasType.var 3
            · exact Presentation.HasType.var 2
            · exact Presentation.HasType.var 1
        · exact .sort motiveLevel
        · exact .sorts motiveLevel motiveLevel
      · exact .sort vecConsHypothesisLevel
      · exact .sorts elementLevel vecConsHypothesisLevel
    · exact .sort vecConsTailLevel
    · exact .sorts elementLevel vecConsTailLevel
  · exact .sort vecConsHeadLevel
  · exact .sorts natLevel vecConsHeadLevel

def vecEliminateInnerLevel : LevelExpr :=
  .max elementLevel motiveLevel

def vecEliminateResultLevel : LevelExpr :=
  .max natLevel vecEliminateInnerLevel

theorem vecEliminateResultType_hasType :
    HasType vecContextAPZS vecEliminateResultType
      (sortTm vecEliminateResultLevel) := by
  unfold vecContextAPZS vecEliminateResultType vecEliminateResultLevel
    vecEliminateInnerLevel
  apply Presentation.HasType.piForm
  · exact natTm_hasType
  · exact .sort natLevel
  · apply Presentation.HasType.piForm
    · apply vecApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 0
    · exact .sort elementLevel
    · apply vecMotiveApp_hasType (element := (.var 5 : Tower.Tm 6))
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · exact .sort motiveLevel
    · exact .sorts elementLevel motiveLevel
  · exact .sort vecEliminateInnerLevel
  · exact .sorts natLevel vecEliminateInnerLevel

def vecEliminateAfterConsLevel : LevelExpr :=
  .max vecConsCaseLevel vecEliminateResultLevel

def vecEliminateAfterNilLevel : LevelExpr :=
  .max motiveLevel vecEliminateAfterConsLevel

def vecEliminateAfterMotiveLevel : LevelExpr :=
  .max vecMotiveTypeLevel vecEliminateAfterNilLevel

def vecEliminateDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) vecEliminateAfterMotiveLevel

theorem vecEliminateType_hasType :
    HasType (.nil : Tower.Ctx 0) vecEliminateType
      (sortTm vecEliminateDeclarationLevel) := by
  unfold vecEliminateType vecEliminateDeclarationLevel
    vecEliminateAfterMotiveLevel vecEliminateAfterNilLevel
    vecEliminateAfterConsLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply Presentation.HasType.piForm
    · exact vecMotiveType_hasType
    · exact .sort vecMotiveTypeLevel
    · apply Presentation.HasType.piForm
      · exact vecNilCaseType_hasType
      · exact .sort motiveLevel
      · apply Presentation.HasType.piForm
        · exact vecConsCaseType_hasType
        · exact .sort vecConsCaseLevel
        · exact vecEliminateResultType_hasType
        · exact .sort vecEliminateResultLevel
        · exact .sorts vecConsCaseLevel vecEliminateResultLevel
      · exact .sort vecEliminateAfterConsLevel
      · exact .sorts motiveLevel vecEliminateAfterConsLevel
    · exact .sort vecEliminateAfterNilLevel
    · exact .sorts vecMotiveTypeLevel vecEliminateAfterNilLevel
  · exact .sort vecEliminateAfterMotiveLevel
  · exact .sorts (.succ elementLevel) vecEliminateAfterMotiveLevel

/-! ## Formed declaration signature -/

@[simp] theorem rawSignature_valueOf_none (name : DeclName) :
    rawSignature.valueOf? name = none := by
  by_cases isNat : name = natName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  by_cases isZero : name = zeroName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat]
  by_cases isSucc : name = succName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero]
  by_cases isNatEliminate : name = natEliminateName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero, isSucc]
  by_cases isVec : name = vecName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero, isSucc,
      isNatEliminate]
  by_cases isVnil : name = vnilName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero, isSucc,
      isNatEliminate, isVec]
  by_cases isVcons : name = vconsName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero, isSucc,
      isNatEliminate, isVec, isVnil]
  by_cases isVecEliminate : name = vecEliminateName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero, isSucc,
      isNatEliminate, isVec, isVnil, isVcons]
  · simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero, isSucc,
      isNatEliminate, isVec, isVnil, isVcons, isVecEliminate]

theorem rawSignature_types_formed {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      Tower.rules.isUniverse level ∧
      HasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isNat : name = natName
  · subst name
    have typeEquality : type = natType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort natDeclarationLevel, .sort natDeclarationLevel,
      natType_hasType⟩
  by_cases isZero : name = zeroName
  · subst name
    have typeEquality : type = zeroType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort natLevel, .sort natLevel, zeroType_hasType⟩
  by_cases isSucc : name = succName
  · subst name
    have typeEquality : type = succType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort succDeclarationLevel, .sort succDeclarationLevel,
      succType_hasType⟩
  by_cases isNatEliminate : name = natEliminateName
  · subst name
    have typeEquality : type = natEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort natEliminateDeclarationLevel,
      .sort natEliminateDeclarationLevel, natEliminateType_hasType⟩
  by_cases isVec : name = vecName
  · subst name
    have typeEquality : type = vecType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort vecDeclarationLevel, .sort vecDeclarationLevel,
      vecType_hasType⟩
  by_cases isVnil : name = vnilName
  · subst name
    have typeEquality : type = vnilType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort vnilDeclarationLevel, .sort vnilDeclarationLevel,
      vnilType_hasType⟩
  by_cases isVcons : name = vconsName
  · subst name
    have typeEquality : type = vconsType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort vconsDeclarationLevel, .sort vconsDeclarationLevel,
      vconsType_hasType⟩
  by_cases isVecEliminate : name = vecEliminateName
  · subst name
    have typeEquality : type = vecEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort vecEliminateDeclarationLevel,
      .sort vecEliminateDeclarationLevel, vecEliminateType_hasType⟩
  · simp [rawSignature, declarations, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty, isNat, isZero, isSucc,
      isNatEliminate, isVec, isVnil, isVcons, isVecEliminate] at lookup

theorem rawSignature_fresh {name : DeclName} {entry : Entry Tower.Head}
    (_lookup : rawSignature.entries name = some entry) :
    Tower.rules.constantType name = none :=
  rfl

/-- Formation, freshness, and the absence of hidden delta definitions are
proved independently of computational preservation. -/
def rawSignature_formed : rawSignature.Formed Tower.rules where
  fresh := rawSignature_fresh
  types := rawSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ## Canonical proof-relevant iota receipts -/

abbrev TypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt Tower.rules rawSignature
    proofRelevantIotaComputation context left right type

def TypedIotaReceipt.toDeclaredReceipt
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (receipt : TypedIotaReceipt context left right type) :
    DeclaredStepReceipt Tower.rules rawSignature context left right type :=
  ProofRelevantStepReceipt.toDeclaredReceipt receipt rfl

def TypedIotaReceipt.substitute
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {left right type : Tower.Tm n} (substitution : Sub Tower.Head n m)
    (receipt : TypedIotaReceipt sourceContext left right type)
    (typed : CtxMor rules sourceContext targetContext substitution) :
    TypedIotaReceipt targetContext (Presentation.subst substitution left)
      (Presentation.subst substitution right)
      (Presentation.subst substitution type) :=
  ProofRelevantStepReceipt.substitute substitution receipt typed

/-- The exact typed-substitution image of one Nat/Vec iota schema. -/
abbrev TypedIotaReceipt.InstanceAt
    {sourceContext : Tower.Ctx n}
    {sourceLeft sourceRight sourceType : Tower.Tm n}
    (schema : TypedIotaReceipt sourceContext sourceLeft sourceRight sourceType)
    (targetContext : Tower.Ctx m)
    (left right type : Tower.Tm m) : Type :=
  ProofRelevantStepReceipt.InstanceAt schema targetContext left right type

def TypedIotaReceipt.InstanceAt.toReceipt
    {sourceContext : Tower.Ctx n}
    {sourceLeft sourceRight sourceType : Tower.Tm n}
    {schema : TypedIotaReceipt sourceContext sourceLeft sourceRight sourceType}
    {targetContext : Tower.Ctx m} {left right type : Tower.Tm m}
    (occurrence : schema.InstanceAt targetContext left right type) :
    TypedIotaReceipt targetContext left right type :=
  ProofRelevantStepReceipt.InstanceAt.toReceipt occurrence

def TypedIotaReceipt.identityInstance
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (schema : TypedIotaReceipt context left right type) :
    schema.InstanceAt context left right type :=
  ProofRelevantStepReceipt.identityInstance schema

/-! ### Natural-number computation -/

def natEliminateAtParameters : Tower.Tm 3 :=
  .app
    (.app
      (.app (.const natEliminateName) (.var 2))
      (.var 1))
    (.var 0)

def natEliminateAtParametersType : Tower.Tm 3 :=
  .pi natTm (.app (.var 3) (.var 0))

theorem natEliminateAtParameters_hasType :
    HasType natContextPZS natEliminateAtParameters
      natEliminateAtParametersType := by
  have motiveTyping :
      HasType natContextPZS (.var 2)
        (.pi natTm (sortTm motiveLevel)) := by
    exact Presentation.HasType.var 2
  have zeroCaseTyping :
      HasType natContextPZS (.var 1)
        (.app (.var 2) zeroTm) := by
    exact Presentation.HasType.var 1
  have succCaseTyping :
      HasType natContextPZS (.var 0)
        (Presentation.rename wk natSuccCaseType) := by
    exact Presentation.HasType.var 0
  have afterMotive := Presentation.HasType.appElim
    (natEliminateConstant_hasType (context := natContextPZS)) motiveTyping
  have afterZero := Presentation.HasType.appElim afterMotive zeroCaseTyping
  have afterSucc := Presentation.HasType.appElim afterZero succCaseTyping
  convert afterSucc using 1 <;> decide

def natZeroIotaLeft : Tower.Tm 3 :=
  .app natEliminateAtParameters zeroTm

def natZeroIotaRight : Tower.Tm 3 := .var 1

def natZeroIotaType : Tower.Tm 3 :=
  .app (.var 2) zeroTm

def natZeroIotaReceipt :
    TypedIotaReceipt natContextPZS
      natZeroIotaLeft natZeroIotaRight natZeroIotaType where
  sourceTyping := by
    have result := Presentation.HasType.appElim
      natEliminateAtParameters_hasType zeroTm_hasType
    convert result using 1 <;> decide
  targetTyping := Presentation.HasType.var 1
  evidence := .natZero (.var 2) (.var 1) (.var 0)

def natContextPZSN : Tower.Ctx 4 :=
  .snoc natContextPZS natTm

def natEliminateAtSuccParameters : Tower.Tm 4 :=
  Presentation.rename wk natEliminateAtParameters

def natEliminateAtSuccParametersType : Tower.Tm 4 :=
  .pi natTm (.app (.var 4) (.var 0))

theorem natEliminateAtSuccParameters_hasType :
    HasType natContextPZSN natEliminateAtSuccParameters
      natEliminateAtSuccParametersType := by
  have weakened := natEliminateAtParameters_hasType.weaken
    (extension := natTm)
  unfold natContextPZSN
  convert weakened using 1 <;> decide

def natSuccIotaLeft : Tower.Tm 4 :=
  .app natEliminateAtSuccParameters (succApp (.var 0))

def natSuccIotaRight : Tower.Tm 4 :=
  .app
    (.app (.var 1) (.var 0))
    (.app natEliminateAtSuccParameters (.var 0))

def natSuccIotaType : Tower.Tm 4 :=
  .app (.var 3) (succApp (.var 0))

def natSuccIotaReceipt :
    TypedIotaReceipt natContextPZSN
      natSuccIotaLeft natSuccIotaRight natSuccIotaType where
  sourceTyping := by
    have numberTyping : HasType natContextPZSN (.var 0) natTm :=
      Presentation.HasType.var 0
    have result := Presentation.HasType.appElim
      natEliminateAtSuccParameters_hasType (succApp_hasType numberTyping)
    convert result using 1 <;> decide
  targetTyping := by
    have numberTyping : HasType natContextPZSN (.var 0) natTm :=
      Presentation.HasType.var 0
    have succCaseTyping :
        HasType natContextPZSN (.var 1)
          (Presentation.rename wk (Presentation.rename wk natSuccCaseType)) :=
      Presentation.HasType.var 1
    have recursiveTyping := Presentation.HasType.appElim
      natEliminateAtSuccParameters_hasType numberTyping
    have afterNumber := Presentation.HasType.appElim
      succCaseTyping numberTyping
    have result := Presentation.HasType.appElim afterNumber recursiveTyping
    convert result using 1 <;> decide
  evidence := .natSucc (.var 3) (.var 2) (.var 1) (.var 0)

/-! ### Vector computation -/

def vecEliminateAtParameters : Tower.Tm 4 :=
  .app
    (.app
      (.app
        (.app (.const vecEliminateName) (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

theorem vecEliminateAtParameters_hasType :
    HasType vecContextAPZS vecEliminateAtParameters
      vecEliminateResultType := by
  have elementTyping :
      HasType vecContextAPZS (.var 3) (sortTm elementLevel) :=
    Presentation.HasType.var 3
  have motiveTyping :
      HasType vecContextAPZS (.var 2)
        (.pi natTm
          (.pi (vecApp (.var 4) (.var 0)) (sortTm motiveLevel))) :=
    Presentation.HasType.var 2
  have nilCaseTyping :
      HasType vecContextAPZS (.var 1)
        (.app (.app (.var 2) zeroTm) (vnilApp (.var 3))) :=
    Presentation.HasType.var 1
  have consCaseTyping :
      HasType vecContextAPZS (.var 0)
        (Presentation.rename wk vecConsCaseType) :=
    Presentation.HasType.var 0
  have afterElement := Presentation.HasType.appElim
    (vecEliminateConstant_hasType (context := vecContextAPZS)) elementTyping
  have afterMotive := Presentation.HasType.appElim afterElement motiveTyping
  have afterNil := Presentation.HasType.appElim afterMotive nilCaseTyping
  have afterCons := Presentation.HasType.appElim afterNil consCaseTyping
  convert afterCons using 1 <;> decide

def vecNilIotaLeft : Tower.Tm 4 :=
  .app
    (.app vecEliminateAtParameters zeroTm)
    (vnilApp (.var 3))

def vecNilIotaRight : Tower.Tm 4 := .var 1

def vecNilIotaType : Tower.Tm 4 :=
  .app (.app (.var 2) zeroTm) (vnilApp (.var 3))

def vecNilIotaReceipt :
    TypedIotaReceipt vecContextAPZS
      vecNilIotaLeft vecNilIotaRight vecNilIotaType where
  sourceTyping := by
    have elementTyping :
        HasType vecContextAPZS (.var 3) (sortTm elementLevel) :=
      Presentation.HasType.var 3
    have afterLength := Presentation.HasType.appElim
      vecEliminateAtParameters_hasType zeroTm_hasType
    have result := Presentation.HasType.appElim afterLength
      (vnilApp_hasType elementTyping)
    convert result using 1 <;> decide
  targetTyping := Presentation.HasType.var 1
  evidence := .vecNil (.var 3) (.var 2) (.var 1) (.var 0)

def vecContextAPZSN : Tower.Ctx 5 :=
  .snoc vecContextAPZS natTm

def vecContextAPZSNHead : Tower.Ctx 6 :=
  .snoc vecContextAPZSN (.var 4)

def vecContextAPZSNHeadTail : Tower.Ctx 7 :=
  .snoc vecContextAPZSNHead (vecApp (.var 5) (.var 1))

def vecEliminateAtConsParameters : Tower.Tm 7 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk vecEliminateAtParameters))

def vecEliminateAtConsParametersType : Tower.Tm 7 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk vecEliminateResultType))

theorem vecEliminateAtConsParameters_hasType :
    HasType vecContextAPZSNHeadTail vecEliminateAtConsParameters
      vecEliminateAtConsParametersType := by
  have afterLength := vecEliminateAtParameters_hasType.weaken
    (extension := natTm)
  have afterHead := afterLength.weaken
    (extension := (.var 4 : Tower.Tm 5))
  have afterTail := afterHead.weaken
    (extension := vecApp (.var 5 : Tower.Tm 6) (.var 1))
  unfold vecContextAPZSNHeadTail vecContextAPZSNHead vecContextAPZSN
    vecEliminateAtConsParameters vecEliminateAtConsParametersType
  exact afterTail

def vecConsIotaLeft : Tower.Tm 7 :=
  .app
    (.app vecEliminateAtConsParameters (succApp (.var 2)))
    (vconsApp (.var 6) (.var 2) (.var 1) (.var 0))

def vecConsIotaRight : Tower.Tm 7 :=
  .app
    (.app
      (.app
        (.app (.var 3) (.var 2))
        (.var 1))
      (.var 0))
    (.app
      (.app vecEliminateAtConsParameters (.var 2))
      (.var 0))

def vecConsIotaType : Tower.Tm 7 :=
  .app
    (.app (.var 5) (succApp (.var 2)))
    (vconsApp (.var 6) (.var 2) (.var 1) (.var 0))

def vecConsIotaReceipt :
    TypedIotaReceipt vecContextAPZSNHeadTail
      vecConsIotaLeft vecConsIotaRight vecConsIotaType where
  sourceTyping := by
    have elementTyping :
        HasType vecContextAPZSNHeadTail (.var 6)
          (sortTm elementLevel) :=
      Presentation.HasType.var 6
    have lengthTyping :
        HasType vecContextAPZSNHeadTail (.var 2) natTm :=
      Presentation.HasType.var 2
    have headTyping :
        HasType vecContextAPZSNHeadTail (.var 1) (.var 6) :=
      Presentation.HasType.var 1
    have tailTyping :
        HasType vecContextAPZSNHeadTail (.var 0)
          (vecApp (.var 6) (.var 2)) :=
      Presentation.HasType.var 0
    have afterLength := Presentation.HasType.appElim
      vecEliminateAtConsParameters_hasType
      (succApp_hasType lengthTyping)
    have vectorTyping := vconsApp_hasType elementTyping lengthTyping
      headTyping tailTyping
    have result := Presentation.HasType.appElim afterLength vectorTyping
    convert result using 1 <;> decide
  targetTyping := by
    have lengthTyping :
        HasType vecContextAPZSNHeadTail (.var 2) natTm :=
      Presentation.HasType.var 2
    have headTyping :
        HasType vecContextAPZSNHeadTail (.var 1) (.var 6) :=
      Presentation.HasType.var 1
    have tailTyping :
        HasType vecContextAPZSNHeadTail (.var 0)
          (vecApp (.var 6) (.var 2)) :=
      Presentation.HasType.var 0
    have consCaseTyping :
        HasType vecContextAPZSNHeadTail (.var 3)
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk vecConsCaseType)))) :=
      Presentation.HasType.var 3
    have afterLength := Presentation.HasType.appElim
      consCaseTyping lengthTyping
    have afterHead := Presentation.HasType.appElim afterLength headTyping
    have afterTail := Presentation.HasType.appElim afterHead tailTyping
    have recursiveAfterLength := Presentation.HasType.appElim
      vecEliminateAtConsParameters_hasType lengthTyping
    have recursiveTyping := Presentation.HasType.appElim
      recursiveAfterLength tailTyping
    have result := Presentation.HasType.appElim afterTail recursiveTyping
    convert result using 1 <;> decide
  evidence :=
    .vecCons (.var 6) (.var 5) (.var 4) (.var 3)
      (.var 2) (.var 1) (.var 0)

/-! ## The exact proof-carrying Nat/Vec computation image -/

/-- The named fragment generated by typed substitutions of the four canonical
Nat/Vec schemas.  This is the sound executable image of the family equations;
it does not assert that every typed raw iota edge has already been inverted
into a canonical schema instance. -/
inductive TypedIotaInstance (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type where
  | natZero (occurrence :
      natZeroIotaReceipt.InstanceAt context left right type) :
      TypedIotaInstance context left right type
  | natSucc (occurrence :
      natSuccIotaReceipt.InstanceAt context left right type) :
      TypedIotaInstance context left right type
  | vecNil (occurrence :
      vecNilIotaReceipt.InstanceAt context left right type) :
      TypedIotaInstance context left right type
  | vecCons (occurrence :
      vecConsIotaReceipt.InstanceAt context left right type) :
      TypedIotaInstance context left right type

/-- Every recognized Nat/Vec instance reconstructs both endpoint typings and
the exact rule witness. -/
def TypedIotaInstance.toReceipt
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    TypedIotaReceipt context left right type := by
  cases occurrence with
  | natZero schemaInstance => exact schemaInstance.toReceipt
  | natSucc schemaInstance => exact schemaInstance.toReceipt
  | vecNil schemaInstance => exact schemaInstance.toReceipt
  | vecCons schemaInstance => exact schemaInstance.toReceipt

def TypedIotaInstance.toDeclaredReceipt
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    DeclaredStepReceipt Tower.rules rawSignature context left right type :=
  occurrence.toReceipt.toDeclaredReceipt

def TypedIotaInstance.sourceTyping
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    HasType context left type :=
  occurrence.toReceipt.sourceTyping

/-- Subject preservation is structural on the exact proof-carrying image. -/
def TypedIotaInstance.targetTyping
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    HasType context right type :=
  occurrence.toReceipt.targetTyping

/-- A principal typed schema instance followed by an explicit directed
conversion/cumulativity adjustment to the displayed type. -/
structure TypedIotaInstance.Adjusted (context : Tower.Ctx n)
    (left right displayedType : Tower.Tm n) : Type where
  principalType : Tower.Tm n
  principal : TypedIotaInstance context left right principalType
  adjustment : TypeAdjustment rules principalType displayedType

def TypedIotaInstance.asAdjusted
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    TypedIotaInstance.Adjusted context left right type where
  principalType := type
  principal := occurrence
  adjustment := .refl type

def TypedIotaInstance.Adjusted.toReceipt
    {context : Tower.Ctx n} {left right displayedType : Tower.Tm n}
    (occurrence : TypedIotaInstance.Adjusted context left right displayedType) :
    TypedIotaReceipt context left right displayedType :=
  let principalReceipt := occurrence.principal.toReceipt
  { sourceTyping := principalReceipt.sourceTyping.adjust occurrence.adjustment
    targetTyping := principalReceipt.targetTyping.adjust occurrence.adjustment
    evidence := principalReceipt.evidence }

def TypedIotaInstance.Adjusted.targetTyping
    {context : Tower.Ctx n} {left right displayedType : Tower.Tm n}
    (occurrence : TypedIotaInstance.Adjusted context left right displayedType) :
    HasType context right displayedType :=
  occurrence.toReceipt.targetTyping

def canonicalNatZeroInstance :
    TypedIotaInstance natContextPZS
      natZeroIotaLeft natZeroIotaRight natZeroIotaType :=
  .natZero natZeroIotaReceipt.identityInstance

def canonicalNatSuccInstance :
    TypedIotaInstance natContextPZSN
      natSuccIotaLeft natSuccIotaRight natSuccIotaType :=
  .natSucc natSuccIotaReceipt.identityInstance

def canonicalVecNilInstance :
    TypedIotaInstance vecContextAPZS
      vecNilIotaLeft vecNilIotaRight vecNilIotaType :=
  .vecNil vecNilIotaReceipt.identityInstance

def canonicalVecConsInstance :
    TypedIotaInstance vecContextAPZSNHeadTail
      vecConsIotaLeft vecConsIotaRight vecConsIotaType :=
  .vecCons vecConsIotaReceipt.identityInstance

/-! ### Raw-support negative control -/

def undeclaredCaseName : DeclName := `Prime.Nat.UndeclaredCase

def undeclaredCase : Tower.Tm 0 := .const undeclaredCaseName

def untypedNatZeroLeft : Tower.Tm 0 :=
  natEliminateApp zeroTm zeroTm undeclaredCase zeroTm

def untypedNatZeroEvidence :
    IotaEvidence 0 untypedNatZeroLeft zeroTm :=
  .natZero zeroTm zeroTm undeclaredCase

theorem undeclaredCase_not_hasType (type : Tower.Tm 0) :
    ¬ HasType (.nil : Tower.Ctx 0) undeclaredCase type := by
  have missing : rules.constantType undeclaredCaseName = none := by
    simp [undeclaredCaseName, rules, extendRules, combinedType, Tower.rules,
      rawSignature, declarations, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty, natName, zeroName, succName,
      natEliminateName, vecName, vnilName, vconsName, vecEliminateName]
  exact Presentation.HasType.constantImpossibleWhenMissing missing

theorem untypedNatZeroLeft_not_hasType (type : Tower.Tm 0) :
    ¬ HasType (.nil : Tower.Ctx 0) untypedNatZeroLeft type := by
  intro sourceTyping
  rcases sourceTyping.appGeneration with
    ⟨_functionDomain, _functionCodomain, afterSuccTyping, _numberTyping,
      _finalAdjustment⟩
  rcases afterSuccTyping.appGeneration with
    ⟨succCaseType, _succCaseCodomain, _afterZeroTyping, succCaseTyping,
      _succAdjustment⟩
  exact undeclaredCase_not_hasType succCaseType (by
    simpa [untypedNatZeroLeft, natEliminateApp] using succCaseTyping)

/-- A raw equation witness is not enough to enter the typed authority image. -/
theorem untypedNatZero_not_typedInstance (type : Tower.Tm 0) :
    TypedIotaInstance (.nil : Tower.Ctx 0)
      untypedNatZeroLeft zeroTm type → False := by
  intro occurrence
  exact untypedNatZeroLeft_not_hasType type occurrence.sourceTyping

theorem raw_iota_support_does_not_imply_typed_instance :
    Nonempty (IotaEvidence 0 untypedNatZeroLeft zeroTm) ∧
      ∀ type : Tower.Tm 0,
        TypedIotaInstance (.nil : Tower.Ctx 0)
          untypedNatZeroLeft zeroTm type → False :=
  ⟨⟨untypedNatZeroEvidence⟩, untypedNatZero_not_typedInstance⟩

/-! ## Strictly-positive family packages -/

def natFamilyApplication :
    FamilyApplication natName 0 (natTm : Tower.Tm n) :=
  .intro [] rfl (by
    intro argument membership
    cases membership) rfl

def vecFamilyApplication (element length : Tower.Tm n)
    (elementFree : FreeOf vecName element)
    (lengthFree : FreeOf vecName length) :
    FamilyApplication vecName 2 (vecApp element length) :=
  .intro [element, length] rfl (by
    intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact elementFree
    · exact lengthFree) rfl

def zeroConstructorPositive : ConstructorType natName 0 zeroType := by
  unfold zeroType
  exact .result natFamilyApplication

def succConstructorPositive : ConstructorType natName 0 succType := by
  unfold succType
  exact .field (.recursive natFamilyApplication)
    (.result natFamilyApplication)

def vnilConstructorPositive : ConstructorType vecName 2 vnilType := by
  unfold vnilType
  exact .field (.free (.head _))
    (.result (vecFamilyApplication (.var 0) zeroTm
      (.var 0) (.const (by decide))))

def vconsConstructorPositive : ConstructorType vecName 2 vconsType := by
  unfold vconsType vconsBodyType
  exact .field (.free (.head _))
    (.field (.free (.const (by decide)))
      (.field (.free (.var 1))
        (.field
          (.recursive (vecFamilyApplication (.var 2) (.var 1)
            (.var 2) (.var 1)))
          (.result (vecFamilyApplication (.var 3) (succApp (.var 2))
            (.var 3) (.app (.const (by decide)) (.var 2)))))))

def zeroConstructorSpec :
    ConstructorSpec rawSignature natName 0 where
  name := zeroName
  type := zeroType
  declared := typeOf_zero
  positive := zeroConstructorPositive

def succConstructorSpec :
    ConstructorSpec rawSignature natName 0 where
  name := succName
  type := succType
  declared := typeOf_succ
  positive := succConstructorPositive

def natConstructors :
    List (ConstructorSpec rawSignature natName 0) :=
  [zeroConstructorSpec, succConstructorSpec]

def natEliminatorSpec : EliminatorSpec rawSignature where
  name := natEliminateName
  type := natEliminateType
  declared := typeOf_natEliminate

def natZeroIotaSchema :
    IotaSchema Tower.rules rawSignature proofRelevantIotaComputation 3 where
  context := natContextPZS
  left := natZeroIotaLeft
  right := natZeroIotaRight
  type := natZeroIotaType
  receipt := natZeroIotaReceipt

def natSuccIotaSchema :
    IotaSchema Tower.rules rawSignature proofRelevantIotaComputation 4 where
  context := natContextPZSN
  left := natSuccIotaLeft
  right := natSuccIotaRight
  type := natSuccIotaType
  receipt := natSuccIotaReceipt

def natEliminateAtParameters_applicationHead :
    ApplicationHead natEliminateName natEliminateAtParameters :=
  .app (.app (.app .const))

def zeroIotaClause :
    IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (natConstructors.map ConstructorSpec.name) natEliminatorSpec.name where
  constructorName := zeroName
  constructorDeclared := by
    simp [natConstructors, zeroConstructorSpec]
  arity := 3
  schema := natZeroIotaSchema
  eliminatorHead := .app natEliminateAtParameters_applicationHead
  constructorOccurrence := .appArgument .here

noncomputable def succIotaClause :
    IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (natConstructors.map ConstructorSpec.name) natEliminatorSpec.name where
  constructorName := succName
  constructorDeclared := by
    simp [natConstructors, zeroConstructorSpec, succConstructorSpec]
  arity := 4
  schema := natSuccIotaSchema
  eliminatorHead := by
    exact .app (natEliminateAtParameters_applicationHead.rename wk)
  constructorOccurrence := .appArgument (.appFunction .here)

noncomputable def natIotaClauses :
    List (IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (natConstructors.map ConstructorSpec.name) natEliminatorSpec.name) :=
  [zeroIotaClause, succIotaClause]

noncomputable def natCandidate : Candidate Tower.rules where
  signature := rawSignature
  formed := rawSignature_formed
  computation := proofRelevantIotaComputation
  computationSupport := rfl
  familyName := natName
  familyParameterCount := 0
  familyIndexCount := 0
  familyType := natType
  familyDeclared := typeOf_nat
  constructors := natConstructors
  constructorNamesNodup := by
    change [zeroName, succName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [natConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  eliminator := natEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [natConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  iotaClauses := natIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [natConstructors, zeroConstructorSpec, succConstructorSpec]
      at membership
    rcases membership with rfl | rfl <;>
      simp [natIotaClauses, zeroIotaClause, succIotaClause]

def vnilConstructorSpec :
    ConstructorSpec rawSignature vecName 2 where
  name := vnilName
  type := vnilType
  declared := typeOf_vnil
  positive := vnilConstructorPositive

def vconsConstructorSpec :
    ConstructorSpec rawSignature vecName 2 where
  name := vconsName
  type := vconsType
  declared := typeOf_vcons
  positive := vconsConstructorPositive

def vecConstructors :
    List (ConstructorSpec rawSignature vecName 2) :=
  [vnilConstructorSpec, vconsConstructorSpec]

def vecEliminatorSpec : EliminatorSpec rawSignature where
  name := vecEliminateName
  type := vecEliminateType
  declared := typeOf_vecEliminate

def vecNilIotaSchema :
    IotaSchema Tower.rules rawSignature proofRelevantIotaComputation 4 where
  context := vecContextAPZS
  left := vecNilIotaLeft
  right := vecNilIotaRight
  type := vecNilIotaType
  receipt := vecNilIotaReceipt

def vecConsIotaSchema :
    IotaSchema Tower.rules rawSignature proofRelevantIotaComputation 7 where
  context := vecContextAPZSNHeadTail
  left := vecConsIotaLeft
  right := vecConsIotaRight
  type := vecConsIotaType
  receipt := vecConsIotaReceipt

def vecEliminateAtParameters_applicationHead :
    ApplicationHead vecEliminateName vecEliminateAtParameters :=
  .app (.app (.app (.app .const)))

def vnilApp_constantOccurrence (element : Tower.Tm n) :
    ConstantOccurrence vnilName (vnilApp element) :=
  .appFunction .here

def vconsApp_constantOccurrence
    (element length head tail : Tower.Tm n) :
    ConstantOccurrence vconsName (vconsApp element length head tail) :=
  .appFunction (.appFunction (.appFunction (.appFunction .here)))

def vnilIotaClause :
    IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (vecConstructors.map ConstructorSpec.name) vecEliminatorSpec.name where
  constructorName := vnilName
  constructorDeclared := by
    simp [vecConstructors, vnilConstructorSpec]
  arity := 4
  schema := vecNilIotaSchema
  eliminatorHead := .app (.app vecEliminateAtParameters_applicationHead)
  constructorOccurrence :=
    .appArgument (vnilApp_constantOccurrence (.var 3))

noncomputable def vconsIotaClause :
    IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (vecConstructors.map ConstructorSpec.name) vecEliminatorSpec.name where
  constructorName := vconsName
  constructorDeclared := by
    simp [vecConstructors, vnilConstructorSpec, vconsConstructorSpec]
  arity := 7
  schema := vecConsIotaSchema
  eliminatorHead := by
    exact .app (.app
      (((vecEliminateAtParameters_applicationHead.rename wk).rename wk).rename wk))
  constructorOccurrence :=
    .appArgument
      (vconsApp_constantOccurrence (.var 6) (.var 2) (.var 1) (.var 0))

noncomputable def vecIotaClauses :
    List (IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (vecConstructors.map ConstructorSpec.name) vecEliminatorSpec.name) :=
  [vnilIotaClause, vconsIotaClause]

noncomputable def vecCandidate : Candidate Tower.rules where
  signature := rawSignature
  formed := rawSignature_formed
  computation := proofRelevantIotaComputation
  computationSupport := rfl
  familyName := vecName
  familyParameterCount := 1
  familyIndexCount := 1
  familyType := vecType
  familyDeclared := typeOf_vec
  constructors := vecConstructors
  constructorNamesNodup := by
    change [vnilName, vconsName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [vecConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  eliminator := vecEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [vecConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  iotaClauses := vecIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [vecConstructors, vnilConstructorSpec, vconsConstructorSpec]
      at membership
    rcases membership with rfl | rfl <;>
      simp [vecIotaClauses, vnilIotaClause, vconsIotaClause]

/-! ## Negative controls -/

theorem natInFunctionDomain_not_strictlyPositive :
    StrictlyPositive natName 0
      (.pi (natTm : Tower.Tm 0) natTm) → False :=
  recursivePiDomain_not_strictlyPositive natFamilyApplication natTm

theorem vecInFunctionDomain_not_strictlyPositive :
    StrictlyPositive vecName 2
      (.pi (vecApp (.var 0 : Tower.Tm 1) zeroTm) (.var 0)) → False :=
  recursivePiDomain_not_strictlyPositive
    (vecFamilyApplication (.var 0) zeroTm (.var 0) (.const (by decide)))
    (.var 0)

theorem partialVecApplication_not_familyApplication :
    FamilyApplication vecName 2
      (.app (.const vecName) (.var 0 : Tower.Tm 1)) → False := by
  rintro ⟨arguments, length, _argumentsFree, equation⟩
  rcases arguments with _ | ⟨first, rest⟩
  · cases length
  rcases rest with _ | ⟨second, rest⟩
  · cases length
  rcases rest with _ | ⟨third, rest⟩
  · cases equation
  · simp at length

/-! ## Computational readouts -/

theorem iota_natZero {motive zeroCase succCase : Tower.Tm n} :
    rules.computation.step
      (natEliminateApp motive zeroCase succCase zeroTm)
      zeroCase :=
  RootStep.declared ⟨.natZero motive zeroCase succCase⟩

theorem iota_natSucc
    {motive zeroCase succCase number : Tower.Tm n} :
    rules.computation.step
      (natEliminateApp motive zeroCase succCase (succApp number))
      (.app (.app succCase number)
        (natEliminateApp motive zeroCase succCase number)) :=
  RootStep.declared ⟨.natSucc motive zeroCase succCase number⟩

theorem iota_vecNil
    {element motive nilCase consCase : Tower.Tm n} :
    rules.computation.step
      (vecEliminateApp element motive nilCase consCase zeroTm
        (vnilApp element))
      nilCase :=
  RootStep.declared ⟨.vecNil element motive nilCase consCase⟩

theorem iota_vecCons
    {element motive nilCase consCase length head tail : Tower.Tm n} :
    rules.computation.step
      (vecEliminateApp element motive nilCase consCase (succApp length)
        (vconsApp element length head tail))
      (.app
        (.app
          (.app
            (.app consCase length)
            head)
          tail)
        (vecEliminateApp element motive nilCase consCase length tail)) :=
  RootStep.declared
    ⟨.vecCons element motive nilCase consCase length head tail⟩

/-! ## Axiom audit -/

#print axioms rawSignature_formed
#print axioms natZeroIotaReceipt
#print axioms natSuccIotaReceipt
#print axioms vecNilIotaReceipt
#print axioms vecConsIotaReceipt
#print axioms TypedIotaInstance.targetTyping
#print axioms TypedIotaInstance.Adjusted.toReceipt
#print axioms canonicalVecConsInstance
#print axioms raw_iota_support_does_not_imply_typed_instance
#print axioms natCandidate
#print axioms vecCandidate
#print axioms natInFunctionDomain_not_strictlyPositive
#print axioms vecInFunctionDomain_not_strictlyPositive
#print axioms partialVecApplication_not_familyApplication

end NativeNaturalVectorFamilies
end Mettapedia.Languages.MeTTa.PureKernel.Universe
