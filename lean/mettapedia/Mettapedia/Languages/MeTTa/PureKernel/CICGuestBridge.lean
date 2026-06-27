import Mettapedia.Languages.MeTTa.PureKernel.TypedLangDef
import Mettapedia.Languages.MeTTa.PureKernel.RecursorDecl
import Mettapedia.Languages.MeTTa.PureKernel.Inst0BridgeDerived
import Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
import Mettapedia.Languages.MeTTa.PureCheckingService
import Provenance.Util.ValueTypeString

namespace Mettapedia.Languages.MeTTa.PureKernel.CICGuestBridge

open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
open Mettapedia.Languages.MeTTa.PureKernel.Assembly
open Mettapedia.Languages.MeTTa.PureKernel.RecursorDecl
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.ElaboratedCore

/-- Lean-side declaration names mirroring the covered Stage-3 cic.dk guest fragment.
This is the target kernel interface after guest normalization, not the guest-side
`max` / `lift` rewrite engine itself. -/
def cicNatName : DeclName := `Nat
def cicZeroName : DeclName := `z
def cicNatSuccName : DeclName := `s
def cicNatMaxName : DeclName := `m
def cicSortName : DeclName := `Sort
def cicPropName : DeclName := `prop
def cicTypeName : DeclName := `type
def cicSortSuccName : DeclName := `succ
def cicRuleName : DeclName := `rule
def cicMaxName : DeclName := `max
def cicUnivName : DeclName := `Univ
def cicTermName : DeclName := `Term
def cicUnivCtorName : DeclName := `univ
def cicLiftName : DeclName := `lift
def cicProdName : DeclName := `prod

def cicNatTm : PureTm n := .const cicNatName
def cicZeroTm : PureTm n := .const cicZeroName
def cicNatSuccTm : PureTm n := .const cicNatSuccName
def cicNatMaxTm : PureTm n := .const cicNatMaxName
def cicNatMax (i j : PureTm n) : PureTm n := .app (.app cicNatMaxTm i) j
def cicSortTm : PureTm n := .const cicSortName
def cicPropTm : PureTm n := .const cicPropName
def cicSortSucc (s : PureTm n) : PureTm n := .app (.const cicSortSuccName) s
def cicType (i : PureTm n) : PureTm n := .app (.const cicTypeName) i
def cicRule (s₁ s₂ : PureTm n) : PureTm n := .app (.app (.const cicRuleName) s₁) s₂
def cicMax (s₁ s₂ : PureTm n) : PureTm n := .app (.app (.const cicMaxName) s₁) s₂
def cicUniv (s : PureTm n) : PureTm n := .app (.const cicUnivName) s
def cicUnivCtor (s : PureTm n) : PureTm n := .app (.const cicUnivCtorName) s
def cicTerm (s a : PureTm n) : PureTm n := .app (.app (.const cicTermName) s) a
def cicLift (s₁ s₂ a : PureTm n) : PureTm n := .app (.app (.app (.const cicLiftName) s₁) s₂) a
def cicProd (s₁ s₂ a b : PureTm n) : PureTm n :=
  .app (.app (.app (.app (.const cicProdName) s₁) s₂) a) b
def cicType0 : PureTm n := cicType cicZeroTm
def cicType1 : PureTm n := cicType (.app cicNatSuccTm cicZeroTm)

def cicNatSpec : DeclSpec :=
  { name := cicNatName, type := .u0 }

def cicZeroSpec : DeclSpec :=
  { name := cicZeroName, type := cicNatTm }

def cicNatSuccSpec : DeclSpec :=
  { name := cicNatSuccName, type := .pi cicNatTm cicNatTm }

def cicNatMaxSpec : DeclSpec :=
  { name := cicNatMaxName, type := .pi cicNatTm (.pi cicNatTm cicNatTm) }

def cicSortSpec : DeclSpec :=
  { name := cicSortName, type := .u0 }

def cicPropSpec : DeclSpec :=
  { name := cicPropName, type := cicSortTm }

def cicTypeSpec : DeclSpec :=
  { name := cicTypeName, type := .pi cicNatTm cicSortTm }

def cicSortSuccSpec : DeclSpec :=
  { name := cicSortSuccName, type := .pi cicSortTm cicSortTm }

def cicRuleSpec : DeclSpec :=
  { name := cicRuleName, type := .pi cicSortTm (.pi cicSortTm cicSortTm) }

def cicMaxSpec : DeclSpec :=
  { name := cicMaxName, type := .pi cicSortTm (.pi cicSortTm cicSortTm) }

def cicUnivSpec : DeclSpec :=
  { name := cicUnivName, type := .pi cicSortTm .u0 }

def cicTermSpec : DeclSpec :=
  { name := cicTermName
    type := .pi cicSortTm (.pi (cicUniv (.var 0)) .u0) }

def cicUnivCtorSpec : DeclSpec :=
  { name := cicUnivCtorName
    type := .pi cicSortTm (cicUniv (cicSortSucc (.var 0))) }

def cicLiftSpec : DeclSpec :=
  { name := cicLiftName
    type := .pi cicSortTm
      (.pi cicSortTm
        (.pi (cicUniv (.var 1))
          (cicUniv (cicMax (.var 2) (.var 1))))) }

def cicProdSpec : DeclSpec :=
  { name := cicProdName
    type := .pi cicSortTm
      (.pi cicSortTm
        (.pi (cicUniv (.var 1))
          (.pi (.pi (cicTerm (.var 2) (.var 0)) (cicUniv (.var 2)))
            (cicUniv (cicRule (.var 3) (.var 2)))))) }

/-- The full all-none target signature for the current covered Stage-3 guest fragment. -/
def cicStage3Specs : List DeclSpec :=
  [ cicNatSpec
  , cicZeroSpec
  , cicNatSuccSpec
  , cicNatMaxSpec
  , cicSortSpec
  , cicPropSpec
  , cicTypeSpec
  , cicSortSuccSpec
  , cicRuleSpec
  , cicMaxSpec
  , cicUnivSpec
  , cicTermSpec
  , cicUnivCtorSpec
  , cicLiftSpec
  , cicProdSpec
  ]

def cicStage3DeclEnv : DeclEnv := envOfSpecs cicStage3Specs

theorem cicStage3Specs_allNone :
    ∀ s ∈ cicStage3Specs, s.value? = none := by
  decide

def cicStage3SignatureWellFormed : SignatureWellFormed cicStage3Specs where
  noShadowing := by
    decide
  obligations := declSpecObligations_of_all_none cicStage3Specs cicStage3Specs_allNone

/-- The strongest fully discharged declaration-side package currently available
for the normalized Stage-3 target signature: checked no-values SR/confluence
plus normalization-backed conversion on the target kernel side. -/
def cicStage3Boundary :
    CheckedNoValuesDeclKernelBoundary
      cicStage3SignatureWellFormed
      cicStage3Specs_allNone :=
  checkedNoValuesDeclKernelBoundary
    cicStage3SignatureWellFormed
    cicStage3Specs_allNone

private theorem defaultBinderName_injective : Function.Injective defaultBinderName := by
  intro a b hab
  rw [← natStringValue_repr a, ← natStringValue_repr b]
  simpa [defaultBinderName, natStringValue, parseDigits, digitNat] using congrArg natStringValue hab

private theorem defaultBinderName_quoteCompat0 :
    QuoteCompat defaultBinderName 0 emptyEnv :=
  quoteCompat_empty defaultBinderName defaultBinderName_injective 0

/-- Any closed Stage-3 declaration-side typing witness can already be replayed
through the existing no-values declaration/profile bridge as a quoted Pure
profile star witness. The current bridge is reflexive here because the target
kernel artifact is already the normalized landing term checked by the guest. -/
theorem cicStage3ClosedTerm_subjectReduction_and_profileBridge
    {t A : PureTm 0}
    (ht : HasTypeDecl cicStage3DeclEnv .nil t A) :
    HasTypeDecl cicStage3DeclEnv .nil t A ∧
      PureProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm t) := by
  simpa [cicStage3DeclEnv] using
    (checkedNoValuesDeclKernelBoundary_closedSubjectReduction_and_profileBridge
      (hBoundary := cicStage3Boundary)
      inst0OpenBridgeCompat_defaultBinderName
      defaultBinderName_quoteCompat0
      (t := t) (u := t) (A := A)
      ht
      (RedStarDecl.refl t))

theorem cicStage3ClosedTerm_profileBridge
    {t A : PureTm 0}
    (ht : HasTypeDecl cicStage3DeclEnv .nil t A) :
    PureProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm t) :=
  (cicStage3ClosedTerm_subjectReduction_and_profileBridge ht).2

@[simp] theorem typeOf_cicSort :
    typeOf? cicStage3DeclEnv cicSortName = some (.u0 : PureTm 0) := by
  decide

@[simp] theorem typeOf_cicProp :
    typeOf? cicStage3DeclEnv cicPropName = some (cicSortTm : PureTm 0) := by
  decide

@[simp] theorem typeOf_cicType :
    typeOf? cicStage3DeclEnv cicTypeName =
      some (.pi (cicNatTm : PureTm 0) (cicSortTm : PureTm 1)) := by
  decide

@[simp] theorem typeOf_cicUniv :
    typeOf? cicStage3DeclEnv cicUnivName = some (.pi (cicSortTm : PureTm 0) .u0) := by
  decide

@[simp] theorem typeOf_cicSortSucc :
    typeOf? cicStage3DeclEnv cicSortSuccName =
      some (.pi (cicSortTm : PureTm 0) (cicSortTm : PureTm 1)) := by
  decide

@[simp] theorem typeOf_cicRule :
    typeOf? cicStage3DeclEnv cicRuleName =
      some (.pi (cicSortTm : PureTm 0) (.pi (cicSortTm : PureTm 1) (cicSortTm : PureTm 2))) := by
  decide

@[simp] theorem typeOf_cicTerm :
    typeOf? cicStage3DeclEnv cicTermName =
      some (.pi (cicSortTm : PureTm 0) (.pi (cicUniv (.var 0)) .u0)) := by
  decide

@[simp] theorem typeOf_cicUnivCtor :
    typeOf? cicStage3DeclEnv cicUnivCtorName =
      some (.pi (cicSortTm : PureTm 0) (cicUniv (cicSortSucc (.var 0)))) := by
  decide

@[simp] theorem typeOf_cicZero :
    typeOf? cicStage3DeclEnv cicZeroName = some (cicNatTm : PureTm 0) := by
  decide

@[simp] theorem typeOf_cicNatSucc :
    typeOf? cicStage3DeclEnv cicNatSuccName =
      some (.pi (cicNatTm : PureTm 0) (cicNatTm : PureTm 1)) := by
  decide

@[simp] theorem typeOf_cicNatMax :
    typeOf? cicStage3DeclEnv cicNatMaxName =
      some (.pi (cicNatTm : PureTm 0) (.pi (cicNatTm : PureTm 1) (cicNatTm : PureTm 2))) := by
  decide

@[simp] theorem typeOf_cicMax :
    typeOf? cicStage3DeclEnv cicMaxName =
      some (.pi (cicSortTm : PureTm 0) (.pi (cicSortTm : PureTm 1) (cicSortTm : PureTm 2))) := by
  decide

theorem hasType_cicSort {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ cicSortTm .u0 :=
  hasType_const_from_lookup (E := cicStage3DeclEnv) (Γ := Γ) (c := cicSortName) (A0 := .u0) (by
    simp)

theorem hasType_cicProp {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ cicPropTm cicSortTm :=
  hasType_const_from_lookup (E := cicStage3DeclEnv) (Γ := Γ) (c := cicPropName) (A0 := cicSortTm) (by
    simp)

theorem hasType_cicTypeFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.const cicTypeName) (.pi cicNatTm (cicSortTm : PureTm (n + 1))) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicTypeName) (A0 := .pi (cicNatTm : PureTm 0) (cicSortTm : PureTm 1)) (by
      simp)

theorem hasType_cicUnivFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.const cicUnivName) (.pi cicSortTm .u0) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicUnivName) (A0 := .pi cicSortTm .u0) (by
      simp)

theorem hasType_cicSortSuccFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.const cicSortSuccName)
      (.pi cicSortTm (cicSortTm : PureTm (n + 1))) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicSortSuccName)
    (A0 := .pi (cicSortTm : PureTm 0) (cicSortTm : PureTm 1)) (by
      simp)

theorem hasType_cicRuleFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.const cicRuleName)
      (.pi cicSortTm (.pi (cicSortTm : PureTm (n + 1)) (cicSortTm : PureTm (n + 2)))) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicRuleName)
    (A0 := .pi (cicSortTm : PureTm 0) (.pi (cicSortTm : PureTm 1) (cicSortTm : PureTm 2))) (by
      simp)

theorem hasType_cicTermFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.const cicTermName) (.pi cicSortTm (.pi (cicUniv (.var 0)) .u0)) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicTermName) (A0 := .pi cicSortTm (.pi (cicUniv (.var 0)) .u0)) (by
      simp)

theorem hasType_cicUnivCtorFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.const cicUnivCtorName)
      (.pi cicSortTm (cicUniv (cicSortSucc (.var 0)))) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicUnivCtorName)
    (A0 := .pi cicSortTm (cicUniv (cicSortSucc (.var 0)))) (by
      simp)

theorem hasType_cicZero {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ cicZeroTm cicNatTm :=
  hasType_const_from_lookup (E := cicStage3DeclEnv) (Γ := Γ) (c := cicZeroName) (A0 := cicNatTm) (by
    simp)

theorem hasType_cicNatSuccFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ cicNatSuccTm (.pi cicNatTm (cicNatTm : PureTm (n + 1))) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicNatSuccName) (A0 := .pi (cicNatTm : PureTm 0) (cicNatTm : PureTm 1)) (by
      simp)

theorem hasType_cicNatMaxFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ cicNatMaxTm
      (.pi cicNatTm (.pi (cicNatTm : PureTm (n + 1)) (cicNatTm : PureTm (n + 2)))) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicNatMaxName)
    (A0 := .pi (cicNatTm : PureTm 0) (.pi (cicNatTm : PureTm 1) (cicNatTm : PureTm 2))) (by
      simp)

theorem hasType_cicMaxFn {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.const cicMaxName)
      (.pi cicSortTm (.pi (cicSortTm : PureTm (n + 1)) (cicSortTm : PureTm (n + 2)))) :=
  hasType_const_from_lookup
    (E := cicStage3DeclEnv) (Γ := Γ) (c := cicMaxName)
    (A0 := .pi (cicSortTm : PureTm 0) (.pi (cicSortTm : PureTm 1) (cicSortTm : PureTm 2))) (by
      simp)

theorem hasType_cicNatSuccZero {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (.app cicNatSuccTm cicZeroTm) cicNatTm :=
  .app_elim hasType_cicNatSuccFn hasType_cicZero

theorem hasType_cicNatSuccOf {Γ : Ctx n} {i : PureTm n}
    (hi : HasTypeDecl cicStage3DeclEnv Γ i cicNatTm) :
    HasTypeDecl cicStage3DeclEnv Γ (.app cicNatSuccTm i) cicNatTm :=
  .app_elim hasType_cicNatSuccFn hi

theorem hasType_cicTypeOf {Γ : Ctx n} {i : PureTm n}
    (hi : HasTypeDecl cicStage3DeclEnv Γ i cicNatTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicType i) cicSortTm :=
  .app_elim hasType_cicTypeFn hi

theorem hasType_cicType0 {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ cicType0 cicSortTm :=
  hasType_cicTypeOf hasType_cicZero

theorem hasType_cicType1 {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ cicType1 cicSortTm :=
  hasType_cicTypeOf hasType_cicNatSuccZero

theorem hasType_cicNatMax {Γ : Ctx n} {i j : PureTm n}
    (hi : HasTypeDecl cicStage3DeclEnv Γ i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv Γ j cicNatTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicNatMax i j) cicNatTm := by
  have hHead :
      HasTypeDecl cicStage3DeclEnv Γ (.app cicNatMaxTm i)
        (.pi (cicNatTm : PureTm n) (cicNatTm : PureTm (n + 1))) :=
    .app_elim hasType_cicNatMaxFn hi
  exact .app_elim hHead hj

theorem hasType_cicMaxPropRight {Γ : Ctx n} {s : PureTm n}
    (hs : HasTypeDecl cicStage3DeclEnv Γ s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicMax cicPropTm s) cicSortTm := by
  have hHead :
      HasTypeDecl cicStage3DeclEnv Γ (.app (.const cicMaxName) cicPropTm)
        (.pi (cicSortTm : PureTm n) (cicSortTm : PureTm (n + 1))) :=
    .app_elim hasType_cicMaxFn hasType_cicProp
  exact .app_elim hHead hs

theorem hasType_cicMaxLeftProp {Γ : Ctx n} {s : PureTm n}
    (hs : HasTypeDecl cicStage3DeclEnv Γ s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicMax s cicPropTm) cicSortTm := by
  have hHead :
      HasTypeDecl cicStage3DeclEnv Γ (.app (.const cicMaxName) s)
        (.pi (cicSortTm : PureTm n) (cicSortTm : PureTm (n + 1))) :=
    .app_elim hasType_cicMaxFn hs
  exact .app_elim hHead hasType_cicProp

theorem hasType_cicMaxTypeTypeSource {Γ : Ctx n} {i j : PureTm n}
    (hi : HasTypeDecl cicStage3DeclEnv Γ i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv Γ j cicNatTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicMax (cicType i) (cicType j)) cicSortTm := by
  have hLeft :
      HasTypeDecl cicStage3DeclEnv Γ (cicType i) cicSortTm :=
    hasType_cicTypeOf hi
  have hRight :
      HasTypeDecl cicStage3DeclEnv Γ (cicType j) cicSortTm :=
    hasType_cicTypeOf hj
  have hHead :
      HasTypeDecl cicStage3DeclEnv Γ (.app (.const cicMaxName) (cicType i))
        (.pi (cicSortTm : PureTm n) (cicSortTm : PureTm (n + 1))) :=
    .app_elim hasType_cicMaxFn hLeft
  exact .app_elim hHead hRight

theorem hasType_cicMaxTypeTypeTarget {Γ : Ctx n} {i j : PureTm n}
    (hi : HasTypeDecl cicStage3DeclEnv Γ i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv Γ j cicNatTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicType (cicNatMax i j)) cicSortTm :=
  hasType_cicTypeOf (hasType_cicNatMax hi hj)

theorem hasType_cicUnivProp {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (cicUniv cicPropTm) .u0 :=
  .app_elim hasType_cicUnivFn hasType_cicProp

theorem hasType_cicSortSuccOf {Γ : Ctx n} {s : PureTm n}
    (hs : HasTypeDecl cicStage3DeclEnv Γ s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicSortSucc s) cicSortTm := by
  simpa [cicSortSucc, cicSortTm, Substitution.inst0, Substitution.subst] using
    (HasTypeDecl.app_elim hasType_cicSortSuccFn hs)

theorem hasType_cicRuleOf {Γ : Ctx n} {s₁ s₂ : PureTm n}
    (hs₁ : HasTypeDecl cicStage3DeclEnv Γ s₁ cicSortTm)
    (hs₂ : HasTypeDecl cicStage3DeclEnv Γ s₂ cicSortTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicRule s₁ s₂) cicSortTm := by
  have hHead :
      HasTypeDecl cicStage3DeclEnv Γ (.app (.const cicRuleName) s₁)
        (.pi (cicSortTm : PureTm n) (cicSortTm : PureTm (n + 1))) :=
    .app_elim hasType_cicRuleFn hs₁
  exact .app_elim hHead hs₂

theorem hasType_cicUnivOf {Γ : Ctx n} {s : PureTm n}
    (hs : HasTypeDecl cicStage3DeclEnv Γ s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicUniv s) .u0 :=
  .app_elim hasType_cicUnivFn hs

theorem hasType_cicUnivType0 {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (cicUniv cicType0) .u0 :=
  .app_elim hasType_cicUnivFn hasType_cicType0

theorem hasType_cicUnivType1 {Γ : Ctx n} :
    HasTypeDecl cicStage3DeclEnv Γ (cicUniv cicType1) .u0 :=
  hasType_cicUnivOf hasType_cicType1

theorem hasType_cicUnivCtorOf {Γ : Ctx n} {s : PureTm n}
    (hs : HasTypeDecl cicStage3DeclEnv Γ s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv Γ (cicUnivCtor s) (cicUniv (cicSortSucc s)) := by
  simpa [cicUnivCtor, cicUniv, cicSortSucc, Substitution.inst0, Substitution.subst] using
    (HasTypeDecl.app_elim hasType_cicUnivCtorFn hs)

theorem hasType_cicTermOf {Γ : Ctx n} {s a : PureTm n}
    (hs : HasTypeDecl cicStage3DeclEnv Γ s cicSortTm)
    (ha : HasTypeDecl cicStage3DeclEnv Γ a (cicUniv s)) :
    HasTypeDecl cicStage3DeclEnv Γ (cicTerm s a) .u0 := by
  have hHead :
      HasTypeDecl cicStage3DeclEnv Γ (.app (.const cicTermName) s)
        (.pi (cicUniv s) .u0) := by
    simpa [cicUniv, Substitution.inst0, Substitution.subst] using
      (HasTypeDecl.app_elim hasType_cicTermFn hs)
  simpa [cicTerm, Substitution.inst0, Substitution.subst] using
    HasTypeDecl.app_elim hHead ha

theorem hasType_cicVar0_univProp :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicPropTm)) (.var 0) (cicUniv cicPropTm) := by
  change HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicPropTm)) (.var 0)
    (Renaming.rename Renaming.wk (cicUniv (cicPropTm : PureTm 0)))
  exact HasTypeDecl.var (E := cicStage3DeclEnv) (Γ := .snoc .nil (cicUniv cicPropTm)) (i := (0 : Fin 1))

theorem hasType_cicVar0_univType0 :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType0)) (.var 0) (cicUniv cicType0) := by
  change HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType0)) (.var 0)
    (Renaming.rename Renaming.wk (cicUniv (cicType0 : PureTm 0)))
  exact HasTypeDecl.var (E := cicStage3DeclEnv) (Γ := .snoc .nil (cicUniv cicType0)) (i := (0 : Fin 1))

theorem hasType_cicVar0_univType1 :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType1)) (.var 0) (cicUniv cicType1) := by
  change HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType1)) (.var 0)
    (Renaming.rename Renaming.wk (cicUniv (cicType1 : PureTm 0)))
  exact HasTypeDecl.var (E := cicStage3DeclEnv) (Γ := .snoc .nil (cicUniv cicType1)) (i := (0 : Fin 1))

private theorem rename_closed_eq_liftClosed {m : Nat} (ρ : Renaming.Ren 0 m) (t : PureTm 0) :
    Renaming.rename ρ t = liftClosed (n := m) t := by
  unfold liftClosed
  exact Renaming.rename_ext (ρ := ρ) (ξ := fun i : Fin 0 => nomatch i) (by
    intro i
    nomatch i) t

theorem hasType_cicVar0_univOf {s : PureTm 0}
    (_hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv s)) (.var 0)
      (liftClosed (n := 1) (cicUniv s)) := by
  simpa [rename_closed_eq_liftClosed] using
    (HasTypeDecl.var (E := cicStage3DeclEnv) (Γ := .snoc .nil (cicUniv s)) (i := (0 : Fin 1)))

theorem hasType_cicTermPropVar0 :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicPropTm)) (cicTerm cicPropTm (.var 0)) .u0 := by
  have hTermProp :
      HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicPropTm))
        (.app (.const cicTermName) cicPropTm)
        (.pi (cicUniv cicPropTm) .u0) :=
    .app_elim hasType_cicTermFn hasType_cicProp
  simpa [cicTerm, Substitution.inst0, Substitution.subst] using
    HasTypeDecl.app_elim hTermProp hasType_cicVar0_univProp

theorem hasType_cicTermType0Var0 :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType0)) (cicTerm cicType0 (.var 0)) .u0 := by
  have hTermType0 :
      HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType0))
        (.app (.const cicTermName) cicType0)
        (.pi (cicUniv cicType0) .u0) :=
    .app_elim hasType_cicTermFn hasType_cicType0
  have hVar0 :
      HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType0)) (.var 0) (cicUniv cicType0) := by
    exact hasType_cicVar0_univType0
  simpa [cicTerm, Substitution.inst0, Substitution.subst] using
    HasTypeDecl.app_elim hTermType0 hVar0

theorem hasType_cicTermType1Var0 :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType1)) (cicTerm cicType1 (.var 0)) .u0 := by
  have hTermType1 :
      HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv cicType1))
        (.app (.const cicTermName) cicType1)
        (.pi (cicUniv cicType1) .u0) :=
    .app_elim hasType_cicTermFn hasType_cicType1
  simpa [cicTerm, Substitution.inst0, Substitution.subst] using
    HasTypeDecl.app_elim hTermType1 hasType_cicVar0_univType1

theorem hasType_cicTermVar0Of {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv s))
      (cicTerm (liftClosed (n := 1) s) (.var 0)) .u0 := by
  have hsLifted :
      HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv s))
        (liftClosed (n := 1) s) cicSortTm := by
    simpa [cicSortTm, rename_closed_eq_liftClosed] using
      (weakening_decl (Γ := .nil) (U := cicUniv s) hs)
  have hVar0 :
      HasTypeDecl cicStage3DeclEnv (.snoc .nil (cicUniv s)) (.var 0)
        (cicUniv (liftClosed (n := 1) s)) := by
    simpa [cicUniv, liftClosed, Renaming.rename] using hasType_cicVar0_univOf hs
  exact hasType_cicTermOf hsLifted hVar0

/-- Lean-side inventory family for the inherited Stage-1 nat-max obligations. -/
inductive CicStage1ClosedNatMaxStep : PureTm 0 → PureTm 0 → Prop
  | m_i_z {i : PureTm 0}
      (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm) :
      CicStage1ClosedNatMaxStep (cicNatMax i cicZeroTm) i
  | m_z_j {j : PureTm 0}
      (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm) :
      CicStage1ClosedNatMaxStep (cicNatMax cicZeroTm j) j
  | m_s_s {i j : PureTm 0}
      (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
      (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm) :
      CicStage1ClosedNatMaxStep
        (cicNatMax (.app cicNatSuccTm i) (.app cicNatSuccTm j))
        (.app cicNatSuccTm (cicNatMax i j))

theorem CicStage1ClosedNatMaxStep.typed
    {t u : PureTm 0} (h : CicStage1ClosedNatMaxStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil t cicNatTm ∧
      HasTypeDecl cicStage3DeclEnv .nil u cicNatTm := by
  cases h with
  | m_i_z hi =>
      exact ⟨hasType_cicNatMax hi hasType_cicZero, hi⟩
  | m_z_j hj =>
      exact ⟨hasType_cicNatMax hasType_cicZero hj, hj⟩
  | m_s_s hi hj =>
      exact
        ⟨ hasType_cicNatMax (hasType_cicNatSuccOf hi) (hasType_cicNatSuccOf hj)
        , hasType_cicNatSuccOf (hasType_cicNatMax hi hj)
        ⟩

theorem CicStage1ClosedNatMaxStep.target_profile
    {t u : PureTm 0} (h : CicStage1ClosedNatMaxStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil u cicNatTm ∧
      PureProfileTheoryStepStar (quoteClosedTm u) (quoteClosedTm u) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge h.typed.2

theorem cicType_target_profile_of_nat_target
    {k : PureTm 0}
    (hk : HasTypeDecl cicStage3DeclEnv .nil k cicNatTm) :
    HasTypeDecl cicStage3DeclEnv .nil (cicType k) cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType k))
        (quoteClosedTm (cicType k)) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge
    (hasType_cicTypeOf hk)

/-- Lean-side inventory family for the inherited Stage-1 `succ` obligations. -/
inductive CicStage1ClosedSuccStep : PureTm 0 → PureTm 0 → Prop
  | succ_prop :
      CicStage1ClosedSuccStep (cicSortSucc cicPropTm) cicType0
  | succ_type {i : PureTm 0}
      (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm) :
      CicStage1ClosedSuccStep (cicSortSucc (cicType i)) (cicType (.app cicNatSuccTm i))

theorem CicStage1ClosedSuccStep.typed
    {t u : PureTm 0} (h : CicStage1ClosedSuccStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil t cicSortTm ∧
      HasTypeDecl cicStage3DeclEnv .nil u cicSortTm := by
  cases h with
  | succ_prop =>
      exact ⟨hasType_cicSortSuccOf hasType_cicProp, hasType_cicType0⟩
  | succ_type hi =>
      exact
        ⟨ hasType_cicSortSuccOf (hasType_cicTypeOf hi)
        , hasType_cicTypeOf (hasType_cicNatSuccOf hi)
        ⟩

theorem CicStage1ClosedSuccStep.target_profile
    {t u : PureTm 0} (h : CicStage1ClosedSuccStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil u cicSortTm ∧
      PureProfileTheoryStepStar (quoteClosedTm u) (quoteClosedTm u) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge h.typed.2

/-- Lean-side inventory family for the inherited Stage-1 `rule` obligations. -/
inductive CicStage1ClosedRuleStep : PureTm 0 → PureTm 0 → Prop
  | rule_s1_prop {s₁ : PureTm 0}
      (hs₁ : HasTypeDecl cicStage3DeclEnv .nil s₁ cicSortTm) :
      CicStage1ClosedRuleStep (cicRule s₁ cicPropTm) cicPropTm
  | rule_prop_s2 {s₂ : PureTm 0}
      (hs₂ : HasTypeDecl cicStage3DeclEnv .nil s₂ cicSortTm) :
      CicStage1ClosedRuleStep (cicRule cicPropTm s₂) s₂
  | rule_type_type {i j : PureTm 0}
      (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
      (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm) :
      CicStage1ClosedRuleStep
        (cicRule (cicType i) (cicType j))
        (cicType (cicNatMax i j))

theorem CicStage1ClosedRuleStep.typed
    {t u : PureTm 0} (h : CicStage1ClosedRuleStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil t cicSortTm ∧
      HasTypeDecl cicStage3DeclEnv .nil u cicSortTm := by
  cases h with
  | rule_s1_prop hs₁ =>
      exact ⟨hasType_cicRuleOf hs₁ hasType_cicProp, hasType_cicProp⟩
  | rule_prop_s2 hs₂ =>
      exact ⟨hasType_cicRuleOf hasType_cicProp hs₂, hs₂⟩
  | rule_type_type hi hj =>
      exact
        ⟨ hasType_cicRuleOf (hasType_cicTypeOf hi) (hasType_cicTypeOf hj)
        , hasType_cicTypeOf (hasType_cicNatMax hi hj)
        ⟩

theorem CicStage1ClosedRuleStep.target_profile
    {t u : PureTm 0} (h : CicStage1ClosedRuleStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil u cicSortTm ∧
      PureProfileTheoryStepStar (quoteClosedTm u) (quoteClosedTm u) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge h.typed.2

/-- First landing-closure theorem for the Stage-1 guest seam: once the inner
`nat-max` subproblem has a closed landing `k`, the outer `rule (type i)
(type j)` row lands on `type k`. This turns the head/index decomposition into a
derived final covered row rather than merely storing both pieces side-by-side. -/
theorem cicStage1ClosedRule_type_type_landing_of_closedNatMax
    {i j k : PureTm 0}
    (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm)
    (hNat : CicStage1ClosedNatMaxStep (cicNatMax i j) k) :
    CicStage1ClosedRuleStep
        (cicRule (cicType i) (cicType j))
        (cicType (cicNatMax i j)) ∧
      HasTypeDecl cicStage3DeclEnv .nil (cicType k) cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType k))
        (quoteClosedTm (cicType k)) := by
  refine ⟨.rule_type_type hi hj, ?_⟩
  exact cicType_target_profile_of_nat_target hNat.typed.2

/-- First Lean-side covered obligation family from the Stage-3 cic.dk guest:
the closed/max-only normalization cases already asserted in the guest checks.
Unlike `lift`/`term-lift`, both the source and target remain ordinary sort terms
on the current declaration boundary, so this family lands directly in the
assumption-free Stage-3 slice. -/
inductive CicStage3ClosedMaxStep : PureTm 0 → PureTm 0 → Prop
  | max_prop_s2 {s : PureTm 0}
      (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
      CicStage3ClosedMaxStep (cicMax cicPropTm s) s
  | max_s1_prop {s : PureTm 0}
      (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
      CicStage3ClosedMaxStep (cicMax s cicPropTm) s
  | max_type_type {i j : PureTm 0}
      (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
      (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm) :
      CicStage3ClosedMaxStep
        (cicMax (cicType i) (cicType j))
        (cicType (cicNatMax i j))

theorem CicStage3ClosedMaxStep.typed
    {t u : PureTm 0} (h : CicStage3ClosedMaxStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil t cicSortTm ∧
      HasTypeDecl cicStage3DeclEnv .nil u cicSortTm := by
  cases h with
  | max_prop_s2 hs =>
      exact ⟨hasType_cicMaxPropRight hs, hs⟩
  | max_s1_prop hs =>
      exact ⟨hasType_cicMaxLeftProp hs, hs⟩
  | max_type_type hi hj =>
      exact
        ⟨ hasType_cicMaxTypeTypeSource hi hj
        , hasType_cicMaxTypeTypeTarget hi hj
        ⟩

theorem cicStage3ClosedMax_prop_type0 :
    CicStage3ClosedMaxStep (cicMax cicPropTm cicType0) cicType0 :=
  .max_prop_s2 hasType_cicType0

theorem cicStage3ClosedMax_type0_prop :
    CicStage3ClosedMaxStep (cicMax cicType0 cicPropTm) cicType0 :=
  .max_s1_prop hasType_cicType0

theorem cicStage3ClosedMax_type0_type0_head :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) :=
  CicStage3ClosedMaxStep.max_type_type hasType_cicZero hasType_cicZero

theorem cicStage3ClosedMax_prop_type0_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3ClosedMax_prop_type0.typed.2

theorem cicStage3ClosedMax_type0_prop_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3ClosedMax_type0_prop.typed.2

theorem cicStage3ClosedMax_type0_type0_head_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicType (cicNatMax cicZeroTm cicZeroTm))
      cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm)))
        (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm))) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3ClosedMax_type0_type0_head.typed.2

/-- Stage-3 analogue of the Stage-1 landing-closure theorem above: once the
shared nat-index closure lands on `k`, the covered `max (type i) (type j)` row
lands on `type k`. This is the theorem-level seam where the inherited Stage-1
nat closure begins to discharge Stage-3 sort rows. -/
theorem cicStage3ClosedMax_type_type_landing_of_closedNatMax
    {i j k : PureTm 0}
    (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm)
    (hNat : CicStage1ClosedNatMaxStep (cicNatMax i j) k) :
    CicStage3ClosedMaxStep
        (cicMax (cicType i) (cicType j))
        (cicType (cicNatMax i j)) ∧
      HasTypeDecl cicStage3DeclEnv .nil (cicType k) cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType k))
        (quoteClosedTm (cicType k)) := by
  refine ⟨.max_type_type hi hj, ?_⟩
  exact cicType_target_profile_of_nat_target hNat.typed.2

/-- Convergence seed for the stubborn `type0/type0` Stage-3 max case:
the outer sort-level head is already typed on the Stage-3 declaration boundary,
and its inner nat-index subproblem lines up with the existing closed zero-iota
contract from the recursor lane. This does not yet realize the recursor inside
the Stage-3 declaration environment; it records the exact lane where that
remaining discharge must happen. -/
abbrev cicStage3Type0Type0IndexRecSource : PureTm 0 :=
  natRecZeroClosedIotaRule.source

abbrev cicStage3Type0Type0IndexRecTarget : PureTm 0 :=
  natRecZeroClosedIotaRule.target

theorem cicStage3Type0Type0IndexRecChecked :
    ∃ A : PureTm 0,
      HasTypeDecl natRecDeclEnv .nil cicStage3Type0Type0IndexRecSource A ∧
      HasTypeDecl natRecDeclEnv .nil cicStage3Type0Type0IndexRecTarget A := by
  rcases natRecZeroClosedIotaRule_checked with ⟨A, hSrc, _, hTgt⟩
  exact
    ⟨ A
    , by simpa [cicStage3Type0Type0IndexRecSource] using hSrc
    , by simpa [cicStage3Type0Type0IndexRecTarget] using hTgt
    ⟩

theorem cicStage3Type0Type0IndexRecNormalize :
    generatedRecursorContractClosedIotaNormalize natRecContract
        cicStage3Type0Type0IndexRecSource =
      cicStage3Type0Type0IndexRecTarget := by
  simp [cicStage3Type0Type0IndexRecSource, cicStage3Type0Type0IndexRecTarget,
    generatedRecursorContractClosedIotaNormalize,
    generatedRecursorContractClosedIotaTarget?,
    generatedClosedIotaTargetFromRules?,
    generatedRecursorContractClosedIotaRules,
    generatedRecursorPilot,
    generatedClosedIotaRules,
    generateClosedIotaRule?,
    natRecContract,
    natRecZeroClosedIotaRule,
    natRecName, unitRecName, unitRecCtorIotaObligation, natRecZeroIotaObligation]

theorem cicStage3Type0Type0IndexRecConv :
    GeneratedRecursorContractClosedIotaConv natRecContract
      cicStage3Type0Type0IndexRecSource
      cicStage3Type0Type0IndexRecTarget :=
  (generatedRecursorContractClosedIotaConv_iff_normalize_eq
    (contract := natRecContract)
    (t := cicStage3Type0Type0IndexRecSource)
    (u := cicStage3Type0Type0IndexRecTarget)).2
      cicStage3Type0Type0IndexRecNormalize

theorem natRecContract_admitted :
    GeneratedRecursorContractAdmitted natRecContract := by
  refine ⟨
    { contract := natRecContract
      obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
      value? := none }
    , ?_⟩
  exact generatedRecursorPilot_nat_obligations_no_value

/-- The active sealed recursor frontier currently available for the index debt
behind the Stage-3 `type0/type0` max case. This now routes through the stronger
resolved generator boundary: the nat successor branch is no longer treated as a
live "open exception" in the active bridge package, even though the current
closed declaration slice still does not realize it as a closed `δ`-step. -/
theorem cicStage3Type0Type0ResolvedFrontier :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract :=
  generatedRecursorContract_admitted_current_boundary_package_of_resolved_frontier_sealed
    (contract := natRecContract)
    natRecContract_admitted

theorem cicStage3Type0Type0ConditionalFrontier :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage natRecContract :=
  generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_sealed
    (contract := natRecContract)
    natRecContract_admitted

theorem cicStage3Type0Type0ExactConditionalFrontierPackage :
    GeneratedRecursorAdmittedExactConditionalFrontierPackage natRecContract :=
  generatedRecursorContract_admitted_exact_conditional_frontier_package_sealed
    (contract := natRecContract)
    natRecContract_admitted

theorem cicStage3Type0Type0ExactConditionalNatFrontier :
    natRecContract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations natRecContract =
        [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases cicStage3Type0Type0ExactConditionalFrontierPackage with hUnit | hNat
  · simp [natRecContract, natRecName, unitRecName] at hUnit
  · exact hNat

theorem cicStage3Type0Type0ExactResolvedFrontierPackage :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage natRecContract :=
  generatedRecursorContract_admitted_exact_resolved_frontier_package_sealed
    (contract := natRecContract)
    natRecContract_admitted

theorem cicStage3Type0Type0ExactResolvedNatFrontier :
    natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases cicStage3Type0Type0ExactResolvedFrontierPackage with hUnit | hNat
  · simp [natRecContract, natRecName, unitRecName] at hUnit
  · exact hNat

theorem cicStage3Type0Type0ResolvedGeneratorBoundary :
    generatedRecursorContractResolvedIotaObligations natRecContract = [] := by
  exact generatedRecursorContractResolvedIotaObligations_nat

theorem cicStage3Type0Type0IndexZero :
    CicStage1ClosedNatMaxStep (cicNatMax cicZeroTm cicZeroTm) cicZeroTm :=
  .m_i_z hasType_cicZero

theorem cicStage3Type0Type0IndexZero_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicZeroTm cicNatTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicZeroTm)
        (quoteClosedTm cicZeroTm) := by
  exact CicStage1ClosedNatMaxStep.target_profile cicStage3Type0Type0IndexZero

theorem cicStage3Type0Type0LandedTarget_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact
    (cicStage3ClosedMax_type_type_landing_of_closedNatMax
      hasType_cicZero
      hasType_cicZero
      cicStage3Type0Type0IndexZero).2

/-- Exact theorem-facing frontier for the stubborn Stage-3 `max type_0 type_0`
row. This isolates the current Nat-rec boundary by naming only the irreducible
pieces: the covered outer head, the closed zero-iota index replay, the active
resolved recursor frontier, the exact Nat declaration-side limitation, and the
current landing theorem on the Stage-3 kernel side. -/
structure CicStage3MaxTypeTypeFrontier where
  head :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm))
  index_checked :
    ∃ A : PureTm 0,
      HasTypeDecl natRecDeclEnv .nil cicStage3Type0Type0IndexRecSource A ∧
      HasTypeDecl natRecDeclEnv .nil cicStage3Type0Type0IndexRecTarget A
  index_conv :
    GeneratedRecursorContractClosedIotaConv natRecContract
      cicStage3Type0Type0IndexRecSource
      cicStage3Type0Type0IndexRecTarget
  conditional_frontier :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage natRecContract
  exact_conditional_frontier_package :
    GeneratedRecursorAdmittedExactConditionalFrontierPackage natRecContract
  resolved_frontier :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract
  exact_resolved_frontier_package :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage natRecContract
  index_zero :
    CicStage1ClosedNatMaxStep (cicNatMax cicZeroTm cicZeroTm) cicZeroTm
  landing :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0)

theorem CicStage3MaxTypeTypeFrontier.head_target_profile
    (frontier : CicStage3MaxTypeTypeFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicType (cicNatMax cicZeroTm cicZeroTm))
      cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm)))
        (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm))) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    frontier.head.typed.2

theorem CicStage3MaxTypeTypeFrontier.index_zero_target_profile
    (frontier : CicStage3MaxTypeTypeFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicZeroTm cicNatTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicZeroTm)
        (quoteClosedTm cicZeroTm) :=
  CicStage1ClosedNatMaxStep.target_profile frontier.index_zero

theorem CicStage3MaxTypeTypeFrontier.exact_conditional_nat_frontier
    (frontier : CicStage3MaxTypeTypeFrontier) :
    natRecContract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations natRecContract =
        [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases frontier.exact_conditional_frontier_package with hUnit | hNat
  · simp [natRecContract, natRecName, unitRecName] at hUnit
  · exact hNat

theorem CicStage3MaxTypeTypeFrontier.exact_resolved_nat_frontier
    (frontier : CicStage3MaxTypeTypeFrontier) :
    natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases frontier.exact_resolved_frontier_package with hUnit | hNat
  · simp [natRecContract, natRecName, unitRecName] at hUnit
  · exact hNat

theorem CicStage3MaxTypeTypeFrontier.open_generator_boundary
    (frontier : CicStage3MaxTypeTypeFrontier) :
    generatedRecursorContractOpenIotaObligations natRecContract =
      [natRecSuccIotaObligation] :=
  frontier.exact_conditional_nat_frontier.2.1

theorem CicStage3MaxTypeTypeFrontier.resolved_generator_boundary
    (frontier : CicStage3MaxTypeTypeFrontier) :
    generatedRecursorContractResolvedIotaObligations natRecContract = [] :=
  frontier.exact_resolved_nat_frontier.2.1

theorem CicStage3MaxTypeTypeFrontier.subjectReduction_and_profile
    (frontier : CicStage3MaxTypeTypeFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  frontier.landing.2

theorem CicStage3MaxTypeTypeFrontier.resolved_frontier_and_nat_limitation
    (frontier : CicStage3MaxTypeTypeFrontier) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A :=
  ⟨frontier.resolved_frontier, frontier.exact_resolved_nat_frontier⟩

theorem CicStage3MaxTypeTypeFrontier.conditional_frontier_and_nat_limitation
    (frontier : CicStage3MaxTypeTypeFrontier) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations natRecContract =
        [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A :=
  ⟨frontier.conditional_frontier, frontier.exact_conditional_nat_frontier⟩

def cicStage3MaxTypeTypeFrontierCertificate :
    CicStage3MaxTypeTypeFrontier :=
  { head := cicStage3ClosedMax_type0_type0_head
    index_checked := cicStage3Type0Type0IndexRecChecked
    index_conv := cicStage3Type0Type0IndexRecConv
    conditional_frontier := cicStage3Type0Type0ConditionalFrontier
    exact_conditional_frontier_package :=
      cicStage3Type0Type0ExactConditionalFrontierPackage
    resolved_frontier := cicStage3Type0Type0ResolvedFrontier
    exact_resolved_frontier_package :=
      cicStage3Type0Type0ExactResolvedFrontierPackage
    index_zero := cicStage3Type0Type0IndexZero
    landing :=
      ⟨cicStage3ClosedMax_type0_type0_head, cicStage3Type0Type0LandedTarget_profile⟩ }

/-- The normalized positive Stage-3 cumulativity witnesses currently all erase
to the same kernel term: the identity function over the carried element. -/
def cicStage3IdentityWitness : PureTm 0 := .lam (.lam (.var 0))

def cicStage3PropToType0Type : PureTm 0 :=
  .pi (cicUniv cicPropTm)
    (.pi (cicTerm cicPropTm (.var 0))
      (cicTerm cicPropTm (.var 1)))

def cicStage3Type0ToType1Type : PureTm 0 :=
  .pi (cicUniv cicType0)
    (.pi (cicTerm cicType0 (.var 0))
      (cicTerm cicType0 (.var 1)))

/-- Lean-side replay of the normalized `Prop -> Type_0` Stage-3 witness. -/
theorem cicStage3IdentityWitness_hasType_propToType0 :
    HasTypeDecl cicStage3DeclEnv .nil cicStage3IdentityWitness cicStage3PropToType0Type := by
  refine .lam_intro ?_
  refine .lam_intro ?_
  exact .var 0

/-- Lean-side replay of the normalized `Type_0 -> Type_1` Stage-3 witness. -/
theorem cicStage3IdentityWitness_hasType_type0ToType1 :
    HasTypeDecl cicStage3DeclEnv .nil cicStage3IdentityWitness cicStage3Type0ToType1Type := by
  refine .lam_intro ?_
  refine .lam_intro ?_
  exact .var 0

/-- Generic Lean-side target family for the inherited Stage-1 `term-prod`
obligation. The current guest artifacts exercise it at `prop`, `type_0`, and
`type_1`; we keep those concrete aliases below because Stage-3 reuses the first
two and the third remains a useful named checkpoint. -/
def cicStage1IdentityType (s : PureTm 0) : PureTm 0 :=
  .pi (cicUniv s)
    (.pi (cicTerm (liftClosed (n := 1) s) (.var 0))
      (cicTerm (liftClosed (n := 2) s) (.var 1)))

abbrev cicStage1PropIdType : PureTm 0 := cicStage1IdentityType cicPropTm

abbrev cicStage1Type0IdType : PureTm 0 := cicStage1IdentityType cicType0

abbrev cicStage1Type1IdType : PureTm 0 := cicStage1IdentityType cicType1

abbrev cicStage3Type1ToType2Type : PureTm 0 := cicStage1Type1IdType

theorem cicStage1IdentityWitness_hasType_of_sort {s : PureTm 0}
    (_hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil cicStage3IdentityWitness (cicStage1IdentityType s) := by
  refine .lam_intro ?_
  refine .lam_intro ?_
  simpa [cicTerm, Renaming.rename, Renaming.wk] using
    (HasTypeDecl.var
      (E := cicStage3DeclEnv)
      (Γ := .snoc (.snoc .nil (cicUniv s))
        (cicTerm (liftClosed (n := 1) s) (.var 0)))
      (i := (0 : Fin 2)))

theorem cicStage1IdentityWitness_hasType_propId :
    HasTypeDecl cicStage3DeclEnv .nil cicStage3IdentityWitness cicStage1PropIdType := by
  simpa [cicStage1PropIdType] using
    (cicStage1IdentityWitness_hasType_of_sort hasType_cicProp)

theorem cicStage1IdentityWitness_hasType_type0Id :
    HasTypeDecl cicStage3DeclEnv .nil cicStage3IdentityWitness cicStage1Type0IdType := by
  simpa [cicStage1Type0IdType] using
    (cicStage1IdentityWitness_hasType_of_sort hasType_cicType0)

theorem cicStage1IdentityWitness_hasType_type1Id :
    HasTypeDecl cicStage3DeclEnv .nil cicStage3IdentityWitness cicStage1Type1IdType := by
  simpa [cicStage1Type1IdType] using
    (cicStage1IdentityWitness_hasType_of_sort hasType_cicType1)

/-- Lean-side replay of the normalized `Type_1 -> Type_2` Stage-3 witness. -/
theorem cicStage3IdentityWitness_hasType_type1ToType2 :
    HasTypeDecl cicStage3DeclEnv .nil cicStage3IdentityWitness cicStage3Type1ToType2Type := by
  simpa [cicStage3Type1ToType2Type] using
    cicStage1IdentityWitness_hasType_type1Id

theorem cicStage1IdentityWitness_profile_of_sort {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness) :=
  (cicStage3ClosedTerm_subjectReduction_and_profileBridge
    (cicStage1IdentityWitness_hasType_of_sort hs)).2

theorem cicStage1IdentityWitness_profile_propId :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness) :=
  cicStage1IdentityWitness_profile_of_sort hasType_cicProp

theorem cicStage1IdentityWitness_profile_type0Id :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness) :=
  cicStage1IdentityWitness_profile_of_sort hasType_cicType0

theorem cicStage1IdentityWitness_profile_type1Id :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness) :=
  cicStage1IdentityWitness_profile_of_sort hasType_cicType1

/-- Generic kernel-side target family for the normalized identity witness over
any checked Stage-3 sort. The current hosted CIC witness artifacts only re-host
the `prop` and `type_0` specializations as declaration-valued constants, but
the target-side typing/profile seam is already fully generic here. -/
structure CicStage3IdentityWitnessTargetFamily where
  target :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        HasTypeDecl cicStage3DeclEnv .nil
          cicStage3IdentityWitness
          (cicStage1IdentityType s)
  target_profile :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        PureProfileTheoryStepStar
          (quoteClosedTm cicStage3IdentityWitness)
          (quoteClosedTm cicStage3IdentityWitness)

theorem CicStage3IdentityWitnessTargetFamily.subjectReduction_and_profile_of_sort
    (family : CicStage3IdentityWitnessTargetFamily)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      (cicStage1IdentityType s) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  ⟨family.target hs, family.target_profile hs⟩

def cicStage3IdentityWitnessTargetFamilyCertificate :
    CicStage3IdentityWitnessTargetFamily :=
  { target := by
      intro s hs
      exact cicStage1IdentityWitness_hasType_of_sort hs
    target_profile := by
      intro s hs
      exact cicStage1IdentityWitness_profile_of_sort hs }

theorem cicStage1ClosedSucc_type0 :
    CicStage1ClosedSuccStep (cicSortSucc cicType0) cicType1 :=
  .succ_type hasType_cicZero

theorem cicStage1ClosedSucc_prop_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact CicStage1ClosedSuccStep.target_profile .succ_prop

theorem cicStage1ClosedSucc_type0_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) := by
  exact CicStage1ClosedSuccStep.target_profile cicStage1ClosedSucc_type0

theorem cicStage1ClosedNatMax_succ_zero_succ_zero_head :
    CicStage1ClosedNatMaxStep
      (cicNatMax (.app cicNatSuccTm cicZeroTm) (.app cicNatSuccTm cicZeroTm))
      (.app cicNatSuccTm (cicNatMax cicZeroTm cicZeroTm)) :=
  .m_s_s hasType_cicZero hasType_cicZero

theorem cicStage1ClosedNatMax_succ_zero_succ_zero_head_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil
      (.app cicNatSuccTm (cicNatMax cicZeroTm cicZeroTm))
      cicNatTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (.app cicNatSuccTm (cicNatMax cicZeroTm cicZeroTm)))
        (quoteClosedTm (.app cicNatSuccTm (cicNatMax cicZeroTm cicZeroTm))) := by
  exact CicStage1ClosedNatMaxStep.target_profile
    cicStage1ClosedNatMax_succ_zero_succ_zero_head

theorem cicStage1ClosedNatMax_zero_zero :
    CicStage1ClosedNatMaxStep (cicNatMax cicZeroTm cicZeroTm) cicZeroTm :=
  .m_i_z hasType_cicZero

theorem cicStage1ClosedNatMax_zero_zero_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicZeroTm cicNatTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicZeroTm)
        (quoteClosedTm cicZeroTm) := by
  exact CicStage1ClosedNatMaxStep.target_profile
    cicStage1ClosedNatMax_zero_zero

theorem cicStage1ClosedNatMax_succ_zero_succ_zero_landed_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil (.app cicNatSuccTm cicZeroTm) cicNatTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (.app cicNatSuccTm cicZeroTm))
        (quoteClosedTm (.app cicNatSuccTm cicZeroTm)) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge hasType_cicNatSuccZero

theorem cicStage1ClosedRule_prop_prop :
    CicStage1ClosedRuleStep (cicRule cicPropTm cicPropTm) cicPropTm :=
  .rule_prop_s2 hasType_cicProp

theorem cicStage1ClosedRule_prop_prop_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicPropTm cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicPropTm)
        (quoteClosedTm cicPropTm) := by
  exact CicStage1ClosedRuleStep.target_profile
    cicStage1ClosedRule_prop_prop

theorem cicStage1ClosedRule_prop_type0 :
    CicStage1ClosedRuleStep (cicRule cicPropTm cicType0) cicType0 :=
  .rule_prop_s2 hasType_cicType0

theorem cicStage1ClosedRule_prop_type0_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact CicStage1ClosedRuleStep.target_profile
    cicStage1ClosedRule_prop_type0

theorem cicStage1ClosedRule_type0_type0_head :
    CicStage1ClosedRuleStep
      (cicRule cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) :=
  .rule_type_type hasType_cicZero hasType_cicZero

theorem cicStage1ClosedRule_type0_type0_head_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicType (cicNatMax cicZeroTm cicZeroTm))
      cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm)))
        (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm))) := by
  exact CicStage1ClosedRuleStep.target_profile
    cicStage1ClosedRule_type0_type0_head

theorem cicStage1Rule_type0_type0_landing :
    CicStage1ClosedRuleStep
      (cicRule cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact
    cicStage1ClosedRule_type_type_landing_of_closedNatMax
      hasType_cicZero
      hasType_cicZero
      cicStage1ClosedNatMax_zero_zero

theorem cicStage1ClosedRule_type0_type0_landed_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact cicStage1Rule_type0_type0_landing.2

theorem cicStage1ClosedRule_type1_type0_head :
    CicStage1ClosedRuleStep
      (cicRule cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) :=
  .rule_type_type hasType_cicNatSuccZero hasType_cicZero

theorem cicStage1ClosedRule_type1_type0_head_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm))
      cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)))
        (quoteClosedTm (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm))) := by
  exact CicStage1ClosedRuleStep.target_profile
    cicStage1ClosedRule_type1_type0_head

theorem cicStage1ClosedNatMax_succ_zero_zero :
    CicStage1ClosedNatMaxStep
      (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)
      (.app cicNatSuccTm cicZeroTm) :=
  .m_i_z hasType_cicNatSuccZero

theorem cicStage1ClosedNatMax_succ_zero_zero_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil (.app cicNatSuccTm cicZeroTm) cicNatTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (.app cicNatSuccTm cicZeroTm))
        (quoteClosedTm (.app cicNatSuccTm cicZeroTm)) := by
  exact CicStage1ClosedNatMaxStep.target_profile
    cicStage1ClosedNatMax_succ_zero_zero

theorem cicStage1ClosedNatMax_zero_succ_zero :
    CicStage1ClosedNatMaxStep
      (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))
      (.app cicNatSuccTm cicZeroTm) :=
  .m_z_j hasType_cicNatSuccZero

theorem cicStage1ClosedNatMax_zero_succ_zero_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil (.app cicNatSuccTm cicZeroTm) cicNatTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (.app cicNatSuccTm cicZeroTm))
        (quoteClosedTm (.app cicNatSuccTm cicZeroTm)) := by
  exact CicStage1ClosedNatMaxStep.target_profile
    cicStage1ClosedNatMax_zero_succ_zero

theorem cicStage1Rule_type1_type0_landing :
    CicStage1ClosedRuleStep
      (cicRule cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) := by
  exact
    cicStage1ClosedRule_type_type_landing_of_closedNatMax
      hasType_cicNatSuccZero
      hasType_cicZero
      cicStage1ClosedNatMax_succ_zero_zero

theorem cicStage1ClosedRule_type1_type0_landed_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) := by
  exact cicStage1Rule_type1_type0_landing.2

theorem cicStage1TermUniv_prop_target_profile :
    HasTypeDecl cicStage3DeclEnv .nil (cicUniv cicPropTm) .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicPropTm))
        (quoteClosedTm (cicUniv cicPropTm)) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge hasType_cicUnivProp

/-- Exact reusable certificate for the currently covered Stage-1 sorts/`Π`
guest micro in `02_cic_guest_sorts_pi_micro.metta`.

Rows that normalize farther than one generic obligation-family step are kept as
head/index/landing decompositions, so the certificate mirrors the actual guest
artifact rather than pretending the broad obligation inventory already lands on
the final row by itself. The proof-check rows are represented by the exact
checked witness-at-type artifacts they produce. -/
structure CicStage1CoveredMicroFrontier where
  identity_target_family :
    CicStage3IdentityWitnessTargetFamily
  succ_prop :
    CicStage1ClosedSuccStep (cicSortSucc cicPropTm) cicType0
  succ_prop_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicType0)
      (quoteClosedTm cicType0)
  succ_type0 :
    CicStage1ClosedSuccStep (cicSortSucc cicType0) cicType1
  succ_type0_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicType1)
      (quoteClosedTm cicType1)
  natmax_succ_zero_succ_zero_head :
    CicStage1ClosedNatMaxStep
      (cicNatMax (.app cicNatSuccTm cicZeroTm) (.app cicNatSuccTm cicZeroTm))
      (.app cicNatSuccTm (cicNatMax cicZeroTm cicZeroTm))
  natmax_succ_zero_succ_zero_head_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (.app cicNatSuccTm (cicNatMax cicZeroTm cicZeroTm)))
      (quoteClosedTm (.app cicNatSuccTm (cicNatMax cicZeroTm cicZeroTm)))
  natmax_zero_zero :
    CicStage1ClosedNatMaxStep (cicNatMax cicZeroTm cicZeroTm) cicZeroTm
  natmax_zero_zero_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicZeroTm)
      (quoteClosedTm cicZeroTm)
  natmax_succ_zero_succ_zero_landed_target :
    HasTypeDecl cicStage3DeclEnv .nil (.app cicNatSuccTm cicZeroTm) cicNatTm
  natmax_succ_zero_succ_zero_landed_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (.app cicNatSuccTm cicZeroTm))
      (quoteClosedTm (.app cicNatSuccTm cicZeroTm))
  rule_prop_prop :
    CicStage1ClosedRuleStep (cicRule cicPropTm cicPropTm) cicPropTm
  rule_prop_prop_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicPropTm)
      (quoteClosedTm cicPropTm)
  rule_prop_type0 :
    CicStage1ClosedRuleStep (cicRule cicPropTm cicType0) cicType0
  rule_prop_type0_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicType0)
      (quoteClosedTm cicType0)
  rule_type0_type0_head :
    CicStage1ClosedRuleStep
      (cicRule cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm))
  rule_type0_type0_head_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm)))
      (quoteClosedTm (cicType (cicNatMax cicZeroTm cicZeroTm)))
  rule_type0_type0_index_zero :
    CicStage1ClosedNatMaxStep (cicNatMax cicZeroTm cicZeroTm) cicZeroTm
  rule_type0_type0_index_zero_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicZeroTm)
      (quoteClosedTm cicZeroTm)
  rule_type0_type0_landing :
    CicStage1ClosedRuleStep
      (cicRule cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0)
  rule_type1_type0_head :
    CicStage1ClosedRuleStep
      (cicRule cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm))
  rule_type1_type0_head_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)))
      (quoteClosedTm (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)))
  rule_type1_type0_index_zero :
    CicStage1ClosedNatMaxStep
      (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)
      (.app cicNatSuccTm cicZeroTm)
  rule_type1_type0_index_zero_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (.app cicNatSuccTm cicZeroTm))
      (quoteClosedTm (.app cicNatSuccTm cicZeroTm))
  rule_type1_type0_landing :
    CicStage1ClosedRuleStep
      (cicRule cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1)
  term_univ_prop_target :
    HasTypeDecl cicStage3DeclEnv .nil (cicUniv cicPropTm) .u0
  term_univ_prop_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUniv cicPropTm))
      (quoteClosedTm (cicUniv cicPropTm))
  prop_id_checked_witness :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      cicStage1PropIdType
  prop_id_checked_witness_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness)
  type0_id_checked_witness :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      cicStage1Type0IdType
  type0_id_checked_witness_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness)
  type1_id_checked_witness :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      cicStage1Type1IdType
  type1_id_checked_witness_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness)

def cicStage1CoveredMicroCertificate : CicStage1CoveredMicroFrontier :=
  { identity_target_family := cicStage3IdentityWitnessTargetFamilyCertificate
    succ_prop := .succ_prop
    succ_prop_target_profile := cicStage1ClosedSucc_prop_target_profile.2
    succ_type0 := cicStage1ClosedSucc_type0
    succ_type0_target_profile := cicStage1ClosedSucc_type0_target_profile.2
    natmax_succ_zero_succ_zero_head := cicStage1ClosedNatMax_succ_zero_succ_zero_head
    natmax_succ_zero_succ_zero_head_target_profile :=
      cicStage1ClosedNatMax_succ_zero_succ_zero_head_target_profile.2
    natmax_zero_zero := cicStage1ClosedNatMax_zero_zero
    natmax_zero_zero_target_profile := cicStage1ClosedNatMax_zero_zero_target_profile.2
    natmax_succ_zero_succ_zero_landed_target :=
      cicStage1ClosedNatMax_succ_zero_succ_zero_landed_target_profile.1
    natmax_succ_zero_succ_zero_landed_target_profile :=
      cicStage1ClosedNatMax_succ_zero_succ_zero_landed_target_profile.2
    rule_prop_prop := cicStage1ClosedRule_prop_prop
    rule_prop_prop_target_profile := cicStage1ClosedRule_prop_prop_target_profile.2
    rule_prop_type0 := cicStage1ClosedRule_prop_type0
    rule_prop_type0_target_profile := cicStage1ClosedRule_prop_type0_target_profile.2
    rule_type0_type0_head := cicStage1ClosedRule_type0_type0_head
    rule_type0_type0_head_target_profile := cicStage1ClosedRule_type0_type0_head_target_profile.2
    rule_type0_type0_index_zero := cicStage1ClosedNatMax_zero_zero
    rule_type0_type0_index_zero_target_profile := cicStage1ClosedNatMax_zero_zero_target_profile.2
    rule_type0_type0_landing := cicStage1Rule_type0_type0_landing
    rule_type1_type0_head := cicStage1ClosedRule_type1_type0_head
    rule_type1_type0_head_target_profile := cicStage1ClosedRule_type1_type0_head_target_profile.2
    rule_type1_type0_index_zero := cicStage1ClosedNatMax_succ_zero_zero
    rule_type1_type0_index_zero_target_profile := cicStage1ClosedNatMax_succ_zero_zero_target_profile.2
    rule_type1_type0_landing := cicStage1Rule_type1_type0_landing
    term_univ_prop_target := cicStage1TermUniv_prop_target_profile.1
    term_univ_prop_target_profile := cicStage1TermUniv_prop_target_profile.2
    prop_id_checked_witness := cicStage1IdentityWitness_hasType_propId
    prop_id_checked_witness_profile := cicStage1IdentityWitness_profile_propId
    type0_id_checked_witness := cicStage1IdentityWitness_hasType_type0Id
    type0_id_checked_witness_profile := cicStage1IdentityWitness_profile_type0Id
    type1_id_checked_witness := cicStage1IdentityWitness_hasType_type1Id
    type1_id_checked_witness_profile := cicStage1IdentityWitness_profile_type1Id }

/-- One declaration-valued constant carrying the positive `Prop -> Type_0`
Stage-3 witness through the declaration-aware checking boundary. This does not
add a new kernel path; it packages the existing witness as a real `δ`-step
artifact in a tiny value-bearing extension of the Stage-3 target environment. -/
def cicStage3PropToType0WitnessName : DeclName := `cic_stage3_prop_to_type0_witness

def cicStage3PropToType0WitnessSpec : DeclSpec :=
  { name := cicStage3PropToType0WitnessName
    type := cicStage3PropToType0Type
    value? := some cicStage3IdentityWitness }

def cicStage3PropToType0WitnessSpecs : List DeclSpec :=
  cicStage3Specs ++ [cicStage3PropToType0WitnessSpec]

def cicStage3PropToType0WitnessDeclEnv : DeclEnv :=
  envOfSpecs cicStage3PropToType0WitnessSpecs

theorem cicStage3PropToType0WitnessName_fresh :
    cicStage3PropToType0WitnessName ∉ prefixNames cicStage3Specs := by
  decide

theorem cicStage3PropToType0WitnessSpecs_noShadowing :
    (prefixNames cicStage3PropToType0WitnessSpecs).Nodup := by
  have hBase : (prefixNames cicStage3Specs).Nodup := cicStage3SignatureWellFormed.noShadowing
  have hAppend : (prefixNames cicStage3Specs ++ [cicStage3PropToType0WitnessName]).Nodup := by
    exact List.nodup_append.mpr
      ⟨hBase, by simp, by
        intro a ha b hb
        simp at hb
        subst hb
        intro hEq
        subst hEq
        exact cicStage3PropToType0WitnessName_fresh ha⟩
  simpa [cicStage3PropToType0WitnessSpecs, prefixNames, cicStage3PropToType0WitnessSpec] using
    hAppend

theorem cicStage3PropToType0WitnessDeclEnv_extends :
    Extends cicStage3DeclEnv cicStage3PropToType0WitnessDeclEnv := by
  change Extends
    (envOfSpecs cicStage3Specs)
    (envOfSpecs (cicStage3Specs ++ [cicStage3PropToType0WitnessSpec]))
  exact envOfSpecs_extends_of_prefix_append
    (pre := cicStage3Specs)
    (post := [cicStage3PropToType0WitnessSpec])
    cicStage3PropToType0WitnessSpecs_noShadowing

theorem cicStage3IdentityWitness_hasType_propToType0_inDeclaredEnv :
    HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
      cicStage3IdentityWitness
      cicStage3PropToType0Type := by
  exact hasTypeDecl_monotone
    cicStage3PropToType0WitnessDeclEnv_extends
    cicStage3IdentityWitness_hasType_propToType0

theorem cicStage3PropToType0WitnessSpecs_obligations :
    DeclSpecObligations cicStage3PropToType0WitnessSpecs where
  valuesWellTyped := by
    intro s hs v0 hVal
    rcases List.mem_append.mp hs with hsBase | hsWitness
    · have hsNone : s.value? = none := cicStage3Specs_allNone s hsBase
      simp [hsNone] at hVal
    · simp at hsWitness
      subst hsWitness
      simp [cicStage3PropToType0WitnessSpec] at hVal
      subst hVal
      exact cicStage3IdentityWitness_hasType_propToType0_inDeclaredEnv
  noSelfDelta := by
    intro s hs v0 hVal
    rcases List.mem_append.mp hs with hsBase | hsWitness
    · have hsNone : s.value? = none := cicStage3Specs_allNone s hsBase
      simp [hsNone] at hVal
    · simp at hsWitness
      subst hsWitness
      simp [cicStage3PropToType0WitnessSpec] at hVal
      subst hVal
      intro hEq
      cases hEq

def cicStage3PropToType0WitnessDeclEnv_wellFormed :
    DeclEnvWellFormed cicStage3PropToType0WitnessDeclEnv :=
  envOfSpecs_wellFormed_of_specObligations
    cicStage3PropToType0WitnessSpecs
    cicStage3PropToType0WitnessSpecs_obligations

theorem typeOf_cicStage3PropToType0Witness :
    typeOf? cicStage3PropToType0WitnessDeclEnv cicStage3PropToType0WitnessName =
      some cicStage3PropToType0Type := by
  exact
    typeOf_envOfSpecs_eq_of_mem_of_nodup
      cicStage3PropToType0WitnessSpecs_noShadowing
      (by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_singleton.mpr rfl))

theorem hasType_cicStage3PropToType0WitnessConst :
    HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
      (.const cicStage3PropToType0WitnessName)
      cicStage3PropToType0Type :=
  hasType_const_from_lookup
    (E := cicStage3PropToType0WitnessDeclEnv)
    (Γ := .nil)
    (c := cicStage3PropToType0WitnessName)
    (A0 := cicStage3PropToType0Type)
    typeOf_cicStage3PropToType0Witness

theorem valueOf_cicStage3PropToType0Witness :
    valueOf? cicStage3PropToType0WitnessDeclEnv cicStage3PropToType0WitnessName =
      some cicStage3IdentityWitness := by
  exact
    valueOf_envOfSpecs_eq_of_mem_some_of_nodup
      cicStage3PropToType0WitnessSpecs_noShadowing
      (by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_singleton.mpr rfl))
      rfl

def cicStage3PropToType0DeclaredDelta :
    CheckedDeclaredConstantDelta :=
  pureCheckingBoundary.checkDeclaredConstantDelta
    cicStage3PropToType0WitnessDeclEnv
    cicStage3PropToType0WitnessDeclEnv_wellFormed
    cicStage3PropToType0WitnessName
    cicStage3PropToType0Type
    cicStage3IdentityWitness
    typeOf_cicStage3PropToType0Witness
    valueOf_cicStage3PropToType0Witness

theorem cicStage3PropToType0DeclaredDelta_source :
    cicStage3PropToType0DeclaredDelta.sourceTerm =
      (.const cicStage3PropToType0WitnessName : PureTm 0) := rfl

theorem cicStage3PropToType0DeclaredDelta_target :
    cicStage3PropToType0DeclaredDelta.targetTerm = cicStage3IdentityWitness := by
  simp [cicStage3PropToType0DeclaredDelta, CheckedDeclaredConstantDelta.targetTerm,
    PureCheckingBoundary.checkDeclaredConstantDelta, liftClosed_zero]

theorem cicStage3PropToType0DeclaredDelta_deltaStep :
    RedDecl cicStage3PropToType0WitnessDeclEnv
      (.const cicStage3PropToType0WitnessName : PureTm 0)
      cicStage3IdentityWitness := by
  simpa [liftClosed_zero] using
    (red_const_from_unfold0 valueOf_cicStage3PropToType0Witness)

theorem cicStage3PropToType0DeclaredDelta_targetTyping :
    HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
      cicStage3IdentityWitness
      cicStage3PropToType0Type := by
  exact cicStage3PropToType0WitnessDeclEnv_wellFormed.valuesWellTyped
    typeOf_cicStage3PropToType0Witness
    valueOf_cicStage3PropToType0Witness

/-- One declaration-valued constant carrying the positive `Type_0 -> Type_1`
Stage-3 witness through the declaration-aware checking boundary. This mirrors
the `Prop -> Type_0` artifact path so both covered positive witnesses land as
real declaration-side `δ`-step artifacts. -/
def cicStage3Type0ToType1WitnessName : DeclName := `cic_stage3_type0_to_type1_witness

def cicStage3Type0ToType1WitnessSpec : DeclSpec :=
  { name := cicStage3Type0ToType1WitnessName
    type := cicStage3Type0ToType1Type
    value? := some cicStage3IdentityWitness }

def cicStage3Type0ToType1WitnessSpecs : List DeclSpec :=
  cicStage3Specs ++ [cicStage3Type0ToType1WitnessSpec]

def cicStage3Type0ToType1WitnessDeclEnv : DeclEnv :=
  envOfSpecs cicStage3Type0ToType1WitnessSpecs

theorem cicStage3Type0ToType1WitnessName_fresh :
    cicStage3Type0ToType1WitnessName ∉ prefixNames cicStage3Specs := by
  decide

theorem cicStage3Type0ToType1WitnessSpecs_noShadowing :
    (prefixNames cicStage3Type0ToType1WitnessSpecs).Nodup := by
  have hBase : (prefixNames cicStage3Specs).Nodup := cicStage3SignatureWellFormed.noShadowing
  have hAppend : (prefixNames cicStage3Specs ++ [cicStage3Type0ToType1WitnessName]).Nodup := by
    exact List.nodup_append.mpr
      ⟨hBase, by simp, by
        intro a ha b hb
        simp at hb
        subst hb
        intro hEq
        subst hEq
        exact cicStage3Type0ToType1WitnessName_fresh ha⟩
  simpa [cicStage3Type0ToType1WitnessSpecs, prefixNames, cicStage3Type0ToType1WitnessSpec] using
    hAppend

theorem cicStage3Type0ToType1WitnessDeclEnv_extends :
    Extends cicStage3DeclEnv cicStage3Type0ToType1WitnessDeclEnv := by
  change Extends
    (envOfSpecs cicStage3Specs)
    (envOfSpecs (cicStage3Specs ++ [cicStage3Type0ToType1WitnessSpec]))
  exact envOfSpecs_extends_of_prefix_append
    (pre := cicStage3Specs)
    (post := [cicStage3Type0ToType1WitnessSpec])
    cicStage3Type0ToType1WitnessSpecs_noShadowing

theorem cicStage3IdentityWitness_hasType_type0ToType1_inDeclaredEnv :
    HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
      cicStage3IdentityWitness
      cicStage3Type0ToType1Type := by
  exact hasTypeDecl_monotone
    cicStage3Type0ToType1WitnessDeclEnv_extends
    cicStage3IdentityWitness_hasType_type0ToType1

theorem cicStage3Type0ToType1WitnessSpecs_obligations :
    DeclSpecObligations cicStage3Type0ToType1WitnessSpecs where
  valuesWellTyped := by
    intro s hs v0 hVal
    rcases List.mem_append.mp hs with hsBase | hsWitness
    · have hsNone : s.value? = none := cicStage3Specs_allNone s hsBase
      simp [hsNone] at hVal
    · simp at hsWitness
      subst hsWitness
      simp [cicStage3Type0ToType1WitnessSpec] at hVal
      subst hVal
      exact cicStage3IdentityWitness_hasType_type0ToType1_inDeclaredEnv
  noSelfDelta := by
    intro s hs v0 hVal
    rcases List.mem_append.mp hs with hsBase | hsWitness
    · have hsNone : s.value? = none := cicStage3Specs_allNone s hsBase
      simp [hsNone] at hVal
    · simp at hsWitness
      subst hsWitness
      simp [cicStage3Type0ToType1WitnessSpec] at hVal
      subst hVal
      intro hEq
      cases hEq

def cicStage3Type0ToType1WitnessDeclEnv_wellFormed :
    DeclEnvWellFormed cicStage3Type0ToType1WitnessDeclEnv :=
  envOfSpecs_wellFormed_of_specObligations
    cicStage3Type0ToType1WitnessSpecs
    cicStage3Type0ToType1WitnessSpecs_obligations

theorem typeOf_cicStage3Type0ToType1Witness :
    typeOf? cicStage3Type0ToType1WitnessDeclEnv cicStage3Type0ToType1WitnessName =
      some cicStage3Type0ToType1Type := by
  exact
    typeOf_envOfSpecs_eq_of_mem_of_nodup
      cicStage3Type0ToType1WitnessSpecs_noShadowing
      (by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_singleton.mpr rfl))

theorem hasType_cicStage3Type0ToType1WitnessConst :
    HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
      (.const cicStage3Type0ToType1WitnessName)
      cicStage3Type0ToType1Type :=
  hasType_const_from_lookup
    (E := cicStage3Type0ToType1WitnessDeclEnv)
    (Γ := .nil)
    (c := cicStage3Type0ToType1WitnessName)
    (A0 := cicStage3Type0ToType1Type)
    typeOf_cicStage3Type0ToType1Witness

theorem valueOf_cicStage3Type0ToType1Witness :
    valueOf? cicStage3Type0ToType1WitnessDeclEnv cicStage3Type0ToType1WitnessName =
      some cicStage3IdentityWitness := by
  exact
    valueOf_envOfSpecs_eq_of_mem_some_of_nodup
      cicStage3Type0ToType1WitnessSpecs_noShadowing
      (by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_singleton.mpr rfl))
      rfl

def cicStage3Type0ToType1DeclaredDelta :
    CheckedDeclaredConstantDelta :=
  pureCheckingBoundary.checkDeclaredConstantDelta
    cicStage3Type0ToType1WitnessDeclEnv
    cicStage3Type0ToType1WitnessDeclEnv_wellFormed
    cicStage3Type0ToType1WitnessName
    cicStage3Type0ToType1Type
    cicStage3IdentityWitness
    typeOf_cicStage3Type0ToType1Witness
    valueOf_cicStage3Type0ToType1Witness

theorem cicStage3Type0ToType1DeclaredDelta_source :
    cicStage3Type0ToType1DeclaredDelta.sourceTerm =
      (.const cicStage3Type0ToType1WitnessName : PureTm 0) := rfl

theorem cicStage3Type0ToType1DeclaredDelta_target :
    cicStage3Type0ToType1DeclaredDelta.targetTerm = cicStage3IdentityWitness := by
  simp [cicStage3Type0ToType1DeclaredDelta, CheckedDeclaredConstantDelta.targetTerm,
    PureCheckingBoundary.checkDeclaredConstantDelta, liftClosed_zero]

theorem cicStage3Type0ToType1DeclaredDelta_deltaStep :
    RedDecl cicStage3Type0ToType1WitnessDeclEnv
      (.const cicStage3Type0ToType1WitnessName : PureTm 0)
      cicStage3IdentityWitness := by
  simpa [liftClosed_zero] using
    (red_const_from_unfold0 valueOf_cicStage3Type0ToType1Witness)

theorem cicStage3Type0ToType1DeclaredDelta_targetTyping :
    HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
      cicStage3IdentityWitness
      cicStage3Type0ToType1Type := by
  exact cicStage3Type0ToType1WitnessDeclEnv_wellFormed.valuesWellTyped
    typeOf_cicStage3Type0ToType1Witness
    valueOf_cicStage3Type0ToType1Witness

/-- One declaration-valued constant carrying the positive `Type_1 -> Type_2`
Stage-3 witness through the declaration-aware checking boundary. This extends
the same declaration-side artifact path by one further cumulativity step while
keeping the normalized kernel witness unchanged. -/
def cicStage3Type1ToType2WitnessName : DeclName := `cic_stage3_type1_to_type2_witness

def cicStage3Type1ToType2WitnessSpec : DeclSpec :=
  { name := cicStage3Type1ToType2WitnessName
    type := cicStage3Type1ToType2Type
    value? := some cicStage3IdentityWitness }

def cicStage3Type1ToType2WitnessSpecs : List DeclSpec :=
  cicStage3Specs ++ [cicStage3Type1ToType2WitnessSpec]

def cicStage3Type1ToType2WitnessDeclEnv : DeclEnv :=
  envOfSpecs cicStage3Type1ToType2WitnessSpecs

theorem cicStage3Type1ToType2WitnessName_fresh :
    cicStage3Type1ToType2WitnessName ∉ prefixNames cicStage3Specs := by
  decide

theorem cicStage3Type1ToType2WitnessSpecs_noShadowing :
    (prefixNames cicStage3Type1ToType2WitnessSpecs).Nodup := by
  have hBase : (prefixNames cicStage3Specs).Nodup := cicStage3SignatureWellFormed.noShadowing
  have hAppend : (prefixNames cicStage3Specs ++ [cicStage3Type1ToType2WitnessName]).Nodup := by
    exact List.nodup_append.mpr
      ⟨hBase, by simp, by
        intro a ha b hb
        simp at hb
        subst hb
        intro hEq
        subst hEq
        exact cicStage3Type1ToType2WitnessName_fresh ha⟩
  simpa [cicStage3Type1ToType2WitnessSpecs, prefixNames, cicStage3Type1ToType2WitnessSpec] using
    hAppend

theorem cicStage3Type1ToType2WitnessDeclEnv_extends :
    Extends cicStage3DeclEnv cicStage3Type1ToType2WitnessDeclEnv := by
  change Extends
    (envOfSpecs cicStage3Specs)
    (envOfSpecs (cicStage3Specs ++ [cicStage3Type1ToType2WitnessSpec]))
  exact envOfSpecs_extends_of_prefix_append
    (pre := cicStage3Specs)
    (post := [cicStage3Type1ToType2WitnessSpec])
    cicStage3Type1ToType2WitnessSpecs_noShadowing

theorem cicStage3IdentityWitness_hasType_type1ToType2_inDeclaredEnv :
    HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
      cicStage3IdentityWitness
      cicStage3Type1ToType2Type := by
  exact hasTypeDecl_monotone
    cicStage3Type1ToType2WitnessDeclEnv_extends
    cicStage3IdentityWitness_hasType_type1ToType2

theorem cicStage3Type1ToType2WitnessSpecs_obligations :
    DeclSpecObligations cicStage3Type1ToType2WitnessSpecs where
  valuesWellTyped := by
    intro s hs v0 hVal
    rcases List.mem_append.mp hs with hsBase | hsWitness
    · have hsNone : s.value? = none := cicStage3Specs_allNone s hsBase
      simp [hsNone] at hVal
    · simp at hsWitness
      subst hsWitness
      simp [cicStage3Type1ToType2WitnessSpec] at hVal
      subst hVal
      exact cicStage3IdentityWitness_hasType_type1ToType2_inDeclaredEnv
  noSelfDelta := by
    intro s hs v0 hVal
    rcases List.mem_append.mp hs with hsBase | hsWitness
    · have hsNone : s.value? = none := cicStage3Specs_allNone s hsBase
      simp [hsNone] at hVal
    · simp at hsWitness
      subst hsWitness
      simp [cicStage3Type1ToType2WitnessSpec] at hVal
      subst hVal
      intro hEq
      cases hEq

def cicStage3Type1ToType2WitnessDeclEnv_wellFormed :
    DeclEnvWellFormed cicStage3Type1ToType2WitnessDeclEnv :=
  envOfSpecs_wellFormed_of_specObligations
    cicStage3Type1ToType2WitnessSpecs
    cicStage3Type1ToType2WitnessSpecs_obligations

theorem typeOf_cicStage3Type1ToType2Witness :
    typeOf? cicStage3Type1ToType2WitnessDeclEnv cicStage3Type1ToType2WitnessName =
      some cicStage3Type1ToType2Type := by
  exact
    typeOf_envOfSpecs_eq_of_mem_of_nodup
      cicStage3Type1ToType2WitnessSpecs_noShadowing
      (by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_singleton.mpr rfl))

theorem hasType_cicStage3Type1ToType2WitnessConst :
    HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
      (.const cicStage3Type1ToType2WitnessName)
      cicStage3Type1ToType2Type :=
  hasType_const_from_lookup
    (E := cicStage3Type1ToType2WitnessDeclEnv)
    (Γ := .nil)
    (c := cicStage3Type1ToType2WitnessName)
    (A0 := cicStage3Type1ToType2Type)
    typeOf_cicStage3Type1ToType2Witness

theorem valueOf_cicStage3Type1ToType2Witness :
    valueOf? cicStage3Type1ToType2WitnessDeclEnv cicStage3Type1ToType2WitnessName =
      some cicStage3IdentityWitness := by
  exact
    valueOf_envOfSpecs_eq_of_mem_some_of_nodup
      cicStage3Type1ToType2WitnessSpecs_noShadowing
      (by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_singleton.mpr rfl))
      rfl

def cicStage3Type1ToType2DeclaredDelta :
    CheckedDeclaredConstantDelta :=
  pureCheckingBoundary.checkDeclaredConstantDelta
    cicStage3Type1ToType2WitnessDeclEnv
    cicStage3Type1ToType2WitnessDeclEnv_wellFormed
    cicStage3Type1ToType2WitnessName
    cicStage3Type1ToType2Type
    cicStage3IdentityWitness
    typeOf_cicStage3Type1ToType2Witness
    valueOf_cicStage3Type1ToType2Witness

theorem cicStage3Type1ToType2DeclaredDelta_source :
    cicStage3Type1ToType2DeclaredDelta.sourceTerm =
      (.const cicStage3Type1ToType2WitnessName : PureTm 0) := rfl

theorem cicStage3Type1ToType2DeclaredDelta_target :
    cicStage3Type1ToType2DeclaredDelta.targetTerm = cicStage3IdentityWitness := by
  simp [cicStage3Type1ToType2DeclaredDelta, CheckedDeclaredConstantDelta.targetTerm,
    PureCheckingBoundary.checkDeclaredConstantDelta, liftClosed_zero]

theorem cicStage3Type1ToType2DeclaredDelta_deltaStep :
    RedDecl cicStage3Type1ToType2WitnessDeclEnv
      (.const cicStage3Type1ToType2WitnessName : PureTm 0)
      cicStage3IdentityWitness := by
  simpa [liftClosed_zero] using
    (red_const_from_unfold0 valueOf_cicStage3Type1ToType2Witness)

theorem cicStage3Type1ToType2DeclaredDelta_targetTyping :
    HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
      cicStage3IdentityWitness
      cicStage3Type1ToType2Type := by
  exact cicStage3Type1ToType2WitnessDeclEnv_wellFormed.valuesWellTyped
    typeOf_cicStage3Type1ToType2Witness
    valueOf_cicStage3Type1ToType2Witness

/-- One positive hosted-CIC witness packaged as a replayable declaration-side
artifact path: base-kernel typing/profile for the normalized witness together
with the checked declaration-valued `δ`-step that replays the witness through a
concrete extension environment. -/
structure CicStage3HostedWitnessBundle
    (witnessType : PureTm 0) (witnessName : DeclName) (witnessDeclEnv : DeclEnv) where
  kernel_witness :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      witnessType
  kernel_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness)
  declared_delta :
    CheckedDeclaredConstantDelta
  declared_delta_source :
    declared_delta.sourceTerm = (.const witnessName : PureTm 0)
  declared_delta_target :
    declared_delta.targetTerm = cicStage3IdentityWitness
  declared_delta_source_typed :
    HasTypeDecl witnessDeclEnv .nil
      (.const witnessName : PureTm 0)
      witnessType
  declared_delta_step :
    RedDecl witnessDeclEnv
      (.const witnessName : PureTm 0)
      cicStage3IdentityWitness
  declared_delta_target_typed :
    HasTypeDecl witnessDeclEnv .nil
      cicStage3IdentityWitness
      witnessType
  declared_delta_source_artifact_quote :
    declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const witnessName : PureTm 0)
  declared_delta_target_artifact_quote :
    declared_delta.targetArtifact.pattern =
      quoteClosedTm cicStage3IdentityWitness

def cicStage3PropToType0HostedWitnessBundle :
    CicStage3HostedWitnessBundle
      cicStage3PropToType0Type
      cicStage3PropToType0WitnessName
      cicStage3PropToType0WitnessDeclEnv :=
  { kernel_witness := cicStage3IdentityWitness_hasType_propToType0
    kernel_profile :=
      (cicStage3ClosedTerm_subjectReduction_and_profileBridge
        cicStage3IdentityWitness_hasType_propToType0).2
    declared_delta := cicStage3PropToType0DeclaredDelta
    declared_delta_source := cicStage3PropToType0DeclaredDelta_source
    declared_delta_target := cicStage3PropToType0DeclaredDelta_target
    declared_delta_source_typed := hasType_cicStage3PropToType0WitnessConst
    declared_delta_step := cicStage3PropToType0DeclaredDelta_deltaStep
    declared_delta_target_typed := cicStage3PropToType0DeclaredDelta_targetTyping
    declared_delta_source_artifact_quote := by
      simpa [cicStage3PropToType0DeclaredDelta_source] using
        cicStage3PropToType0DeclaredDelta.sourceQuoteAgreement
    declared_delta_target_artifact_quote := by
      simpa [cicStage3PropToType0DeclaredDelta_target] using
        cicStage3PropToType0DeclaredDelta.targetQuoteAgreement }

def cicStage3Type0ToType1HostedWitnessBundle :
    CicStage3HostedWitnessBundle
      cicStage3Type0ToType1Type
      cicStage3Type0ToType1WitnessName
      cicStage3Type0ToType1WitnessDeclEnv :=
  { kernel_witness := cicStage3IdentityWitness_hasType_type0ToType1
    kernel_profile :=
      (cicStage3ClosedTerm_subjectReduction_and_profileBridge
        cicStage3IdentityWitness_hasType_type0ToType1).2
    declared_delta := cicStage3Type0ToType1DeclaredDelta
    declared_delta_source := cicStage3Type0ToType1DeclaredDelta_source
    declared_delta_target := cicStage3Type0ToType1DeclaredDelta_target
    declared_delta_source_typed := hasType_cicStage3Type0ToType1WitnessConst
    declared_delta_step := cicStage3Type0ToType1DeclaredDelta_deltaStep
    declared_delta_target_typed := cicStage3Type0ToType1DeclaredDelta_targetTyping
    declared_delta_source_artifact_quote := by
      simpa [cicStage3Type0ToType1DeclaredDelta_source] using
        cicStage3Type0ToType1DeclaredDelta.sourceQuoteAgreement
    declared_delta_target_artifact_quote := by
      simpa [cicStage3Type0ToType1DeclaredDelta_target] using
        cicStage3Type0ToType1DeclaredDelta.targetQuoteAgreement }

def cicStage3Type1ToType2HostedWitnessBundle :
    CicStage3HostedWitnessBundle
      cicStage3Type1ToType2Type
      cicStage3Type1ToType2WitnessName
      cicStage3Type1ToType2WitnessDeclEnv :=
  { kernel_witness := cicStage3IdentityWitness_hasType_type1ToType2
    kernel_profile :=
      (cicStage3ClosedTerm_subjectReduction_and_profileBridge
        cicStage3IdentityWitness_hasType_type1ToType2).2
    declared_delta := cicStage3Type1ToType2DeclaredDelta
    declared_delta_source := cicStage3Type1ToType2DeclaredDelta_source
    declared_delta_target := cicStage3Type1ToType2DeclaredDelta_target
    declared_delta_source_typed := hasType_cicStage3Type1ToType2WitnessConst
    declared_delta_step := cicStage3Type1ToType2DeclaredDelta_deltaStep
    declared_delta_target_typed := cicStage3Type1ToType2DeclaredDelta_targetTyping
    declared_delta_source_artifact_quote := by
      simpa [cicStage3Type1ToType2DeclaredDelta_source] using
        cicStage3Type1ToType2DeclaredDelta.sourceQuoteAgreement
    declared_delta_target_artifact_quote := by
      simpa [cicStage3Type1ToType2DeclaredDelta_target] using
        cicStage3Type1ToType2DeclaredDelta.targetQuoteAgreement }

/-- Lean-side theorem inventory for the inherited Stage-1 guest rewrite
footprint still imported by the Stage-3 universes micro.

Where the current kernel bridge already supports whole rewrite families, the
fields are quantified (nat-max, `succ`, `rule`, `term-univ`). Where the covered
bridge only currently replays concrete imported targets (`term-prod`), the
fields are the exact covered prop/type0/type1 identity-family artifacts. This
keeps the inventory honest while turning the imported footprint into typed
theorem targets for M2. -/
structure CicStage1InheritedObligationInventory where
  rew_m_i_z :
    ∀ {i : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
        CicStage1ClosedNatMaxStep (cicNatMax i cicZeroTm) i
  rew_m_z_j :
    ∀ {j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        CicStage1ClosedNatMaxStep (cicNatMax cicZeroTm j) j
  rew_m_s_s :
    ∀ {i j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        CicStage1ClosedNatMaxStep
          (cicNatMax (.app cicNatSuccTm i) (.app cicNatSuccTm j))
          (.app cicNatSuccTm (cicNatMax i j))
  rew_m_i_z_target_profile :
    ∀ {i : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
        PureProfileTheoryStepStar (quoteClosedTm i) (quoteClosedTm i)
  rew_m_z_j_target_profile :
    ∀ {j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        PureProfileTheoryStepStar (quoteClosedTm j) (quoteClosedTm j)
  rew_m_s_s_target_profile :
    ∀ {i j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        PureProfileTheoryStepStar
          (quoteClosedTm (.app cicNatSuccTm (cicNatMax i j)))
          (quoteClosedTm (.app cicNatSuccTm (cicNatMax i j)))
  rew_succ_prop :
    CicStage1ClosedSuccStep (cicSortSucc cicPropTm) cicType0
  rew_succ_type :
    ∀ {i : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
        CicStage1ClosedSuccStep (cicSortSucc (cicType i)) (cicType (.app cicNatSuccTm i))
  rew_succ_prop_target_profile :
    PureProfileTheoryStepStar (quoteClosedTm cicType0) (quoteClosedTm cicType0)
  rew_succ_type_target_profile :
    ∀ {i : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
        PureProfileTheoryStepStar
          (quoteClosedTm (cicType (.app cicNatSuccTm i)))
          (quoteClosedTm (cicType (.app cicNatSuccTm i)))
  rew_rule_s1_prop :
    ∀ {s₁ : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s₁ cicSortTm →
        CicStage1ClosedRuleStep (cicRule s₁ cicPropTm) cicPropTm
  rew_rule_prop_s2 :
    ∀ {s₂ : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s₂ cicSortTm →
        CicStage1ClosedRuleStep (cicRule cicPropTm s₂) s₂
  rew_rule_type_type :
    ∀ {i j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        CicStage1ClosedRuleStep
          (cicRule (cicType i) (cicType j))
          (cicType (cicNatMax i j))
  rew_rule_s1_prop_target_profile :
    PureProfileTheoryStepStar (quoteClosedTm cicPropTm) (quoteClosedTm cicPropTm)
  rew_rule_prop_s2_target_profile :
    ∀ {s₂ : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s₂ cicSortTm →
        PureProfileTheoryStepStar (quoteClosedTm s₂) (quoteClosedTm s₂)
  rew_rule_type_type_target_profile :
    ∀ {i j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        PureProfileTheoryStepStar
          (quoteClosedTm (cicType (cicNatMax i j)))
          (quoteClosedTm (cicType (cicNatMax i j)))
  rew_rule_type_type_landing :
    ∀ {i j k : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
      CicStage1ClosedNatMaxStep (cicNatMax i j) k →
        CicStage1ClosedRuleStep
          (cicRule (cicType i) (cicType j))
          (cicType (cicNatMax i j)) ∧
          HasTypeDecl cicStage3DeclEnv .nil (cicType k) cicSortTm ∧
          PureProfileTheoryStepStar
            (quoteClosedTm (cicType k))
            (quoteClosedTm (cicType k))
  rew_term_univ_target :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        HasTypeDecl cicStage3DeclEnv .nil (cicUniv s) .u0
  rew_term_univ_target_profile :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        PureProfileTheoryStepStar
          (quoteClosedTm (cicUniv s))
          (quoteClosedTm (cicUniv s))
  rew_term_prod_target :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        HasTypeDecl cicStage3DeclEnv .nil
          cicStage3IdentityWitness
          (cicStage1IdentityType s)
  rew_term_prod_target_profile :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        PureProfileTheoryStepStar
          (quoteClosedTm cicStage3IdentityWitness)
          (quoteClosedTm cicStage3IdentityWitness)

def cicStage1InheritedObligationCertificate :
    CicStage1InheritedObligationInventory :=
  { rew_m_i_z := by
      intro i hi
      exact .m_i_z hi
    rew_m_z_j := by
      intro j hj
      exact .m_z_j hj
    rew_m_s_s := by
      intro i j hi hj
      exact .m_s_s hi hj
    rew_m_i_z_target_profile := by
      intro i hi
      exact (CicStage1ClosedNatMaxStep.target_profile (.m_i_z hi)).2
    rew_m_z_j_target_profile := by
      intro j hj
      exact (CicStage1ClosedNatMaxStep.target_profile (.m_z_j hj)).2
    rew_m_s_s_target_profile := by
      intro i j hi hj
      exact (CicStage1ClosedNatMaxStep.target_profile (.m_s_s hi hj)).2
    rew_succ_prop := .succ_prop
    rew_succ_type := by
      intro i hi
      exact .succ_type hi
    rew_succ_prop_target_profile := by
      exact (CicStage1ClosedSuccStep.target_profile .succ_prop).2
    rew_succ_type_target_profile := by
      intro i hi
      exact (CicStage1ClosedSuccStep.target_profile (.succ_type hi)).2
    rew_rule_s1_prop := by
      intro s₁ hs₁
      exact .rule_s1_prop hs₁
    rew_rule_prop_s2 := by
      intro s₂ hs₂
      exact .rule_prop_s2 hs₂
    rew_rule_type_type := by
      intro i j hi hj
      exact .rule_type_type hi hj
    rew_rule_s1_prop_target_profile := by
      exact (CicStage1ClosedRuleStep.target_profile (.rule_s1_prop hasType_cicProp)).2
    rew_rule_prop_s2_target_profile := by
      intro s₂ hs₂
      exact (CicStage1ClosedRuleStep.target_profile (.rule_prop_s2 hs₂)).2
    rew_rule_type_type_target_profile := by
      intro i j hi hj
      exact (CicStage1ClosedRuleStep.target_profile (.rule_type_type hi hj)).2
    rew_rule_type_type_landing := by
      intro i j k hi hj hNat
      exact cicStage1ClosedRule_type_type_landing_of_closedNatMax hi hj hNat
    rew_term_univ_target := by
      intro s hs
      exact hasType_cicUnivOf hs
    rew_term_univ_target_profile := by
      intro s hs
      exact cicStage3ClosedTerm_profileBridge (hasType_cicUnivOf hs)
    rew_term_prod_target := by
      intro s hs
      exact cicStage1IdentityWitness_hasType_of_sort hs
    rew_term_prod_target_profile := by
      intro s hs
      exact cicStage3ClosedTerm_profileBridge
        (cicStage1IdentityWitness_hasType_of_sort hs) }

theorem CicStage3ClosedMaxStep.target_profile
    {t u : PureTm 0} (h : CicStage3ClosedMaxStep t u) :
    HasTypeDecl cicStage3DeclEnv .nil u cicSortTm ∧
      PureProfileTheoryStepStar (quoteClosedTm u) (quoteClosedTm u) := by
  exact cicStage3ClosedTerm_subjectReduction_and_profileBridge h.typed.2

/-- Minimal shared-artifact certificate for one closed kernel term. This keeps
the artifact side honest without pretending declaration-aware Stage-3 terms are
already plain env-free Pure certificates. -/
def cicClosedArtifact (t : PureTm 0) : PureCertificate :=
  { term := t
    artifact := ⟨quoteClosedTm t⟩
    artifact_eq := rfl }

/-- Artifact-level encoding for one covered closed Stage-3 `max` row. The
guest names both the source and target terms explicitly; here we package those
two shared artifacts together with the theoremic closed-row replay witness that
still explains why the target is the covered landing term. -/
structure CicStage3ClosedMaxArtifactEncoding where
  source : PureCertificate
  target : PureCertificate
  replay : CicStage3ClosedMaxStep source.term target.term

namespace CicStage3ClosedMaxArtifactEncoding

theorem source_quoteAgreement
    (enc : CicStage3ClosedMaxArtifactEncoding) :
    enc.source.artifact.pattern = quoteClosedTm enc.source.term :=
  enc.source.artifact_eq

theorem target_quoteAgreement
    (enc : CicStage3ClosedMaxArtifactEncoding) :
    enc.target.artifact.pattern = quoteClosedTm enc.target.term :=
  enc.target.artifact_eq

theorem source_typed
    (enc : CicStage3ClosedMaxArtifactEncoding) :
    HasTypeDecl cicStage3DeclEnv .nil enc.source.term cicSortTm :=
  enc.replay.typed.1

theorem target_typed
    (enc : CicStage3ClosedMaxArtifactEncoding) :
    HasTypeDecl cicStage3DeclEnv .nil enc.target.term cicSortTm :=
  enc.replay.typed.2

theorem target_subjectReduction_and_profile
    (enc : CicStage3ClosedMaxArtifactEncoding) :
    HasTypeDecl cicStage3DeclEnv .nil enc.target.term cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm enc.target.term)
        (quoteClosedTm enc.target.term) :=
  CicStage3ClosedMaxStep.target_profile enc.replay

end CicStage3ClosedMaxArtifactEncoding

def cicStage3MaxPropType0ArtifactEncoding :
    CicStage3ClosedMaxArtifactEncoding :=
  { source := cicClosedArtifact (cicMax cicPropTm cicType0)
    target := cicClosedArtifact cicType0
    replay := cicStage3ClosedMax_prop_type0 }

def cicStage3MaxType0PropArtifactEncoding :
    CicStage3ClosedMaxArtifactEncoding :=
  { source := cicClosedArtifact (cicMax cicType0 cicPropTm)
    target := cicClosedArtifact cicType0
    replay := cicStage3ClosedMax_type0_prop }

def cicStage3MaxType0Type0HeadArtifactEncoding :
    CicStage3ClosedMaxArtifactEncoding :=
  { source := cicClosedArtifact (cicMax cicType0 cicType0)
    target := cicClosedArtifact (cicType (cicNatMax cicZeroTm cicZeroTm))
    replay := cicStage3ClosedMax_type0_type0_head }

def cicStage3MaxType1Type0HeadArtifactEncoding :
    CicStage3ClosedMaxArtifactEncoding :=
  { source := cicClosedArtifact (cicMax cicType1 cicType0)
    target :=
      cicClosedArtifact
        (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm))
    replay := CicStage3ClosedMaxStep.max_type_type
      hasType_cicNatSuccZero
      hasType_cicZero }

def cicStage3MaxType0Type1HeadArtifactEncoding :
    CicStage3ClosedMaxArtifactEncoding :=
  { source := cicClosedArtifact (cicMax cicType0 cicType1)
    target :=
      cicClosedArtifact
        (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm)))
    replay := CicStage3ClosedMaxStep.max_type_type
      hasType_cicZero
      hasType_cicNatSuccZero }

/-- Artifact-facing frontier for the currently covered Stage-3 `max` rows. This
packages the five concrete closed-row head artifacts together, while keeping
the landed `type_i/type_j` targets separate whenever the guest check closes a
shared nat-max subproblem afterward rather than by a single outer `max`
rewrite step. -/
structure CicStage3MaxArtifactFrontier where
  max_prop_type0 :
    CicStage3ClosedMaxArtifactEncoding
  max_type0_prop :
    CicStage3ClosedMaxArtifactEncoding
  max_type0_type0_head :
    CicStage3ClosedMaxArtifactEncoding
  max_type1_type0_head :
    CicStage3ClosedMaxArtifactEncoding
  max_type0_type1_head :
    CicStage3ClosedMaxArtifactEncoding
  max_type0_type0_closed_landing :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0)
  max_type1_type0_closed_landing :
    CicStage3ClosedMaxStep
      (cicMax cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1)
  max_type0_type1_closed_landing :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType1)
      (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1)

namespace CicStage3MaxArtifactFrontier

theorem max_prop_type0_target_subjectReduction_and_profile
    (frontier : CicStage3MaxArtifactFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil frontier.max_prop_type0.target.term cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm frontier.max_prop_type0.target.term)
        (quoteClosedTm frontier.max_prop_type0.target.term) :=
  frontier.max_prop_type0.target_subjectReduction_and_profile

theorem max_type0_prop_target_subjectReduction_and_profile
    (frontier : CicStage3MaxArtifactFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil frontier.max_type0_prop.target.term cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm frontier.max_type0_prop.target.term)
        (quoteClosedTm frontier.max_type0_prop.target.term) :=
  frontier.max_type0_prop.target_subjectReduction_and_profile

theorem max_type0_type0_head_target_subjectReduction_and_profile
    (frontier : CicStage3MaxArtifactFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil frontier.max_type0_type0_head.target.term cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm frontier.max_type0_type0_head.target.term)
        (quoteClosedTm frontier.max_type0_type0_head.target.term) :=
  frontier.max_type0_type0_head.target_subjectReduction_and_profile

theorem max_type1_type0_head_target_subjectReduction_and_profile
    (frontier : CicStage3MaxArtifactFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil frontier.max_type1_type0_head.target.term cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm frontier.max_type1_type0_head.target.term)
        (quoteClosedTm frontier.max_type1_type0_head.target.term) :=
  frontier.max_type1_type0_head.target_subjectReduction_and_profile

theorem max_type0_type1_head_target_subjectReduction_and_profile
    (frontier : CicStage3MaxArtifactFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil frontier.max_type0_type1_head.target.term cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm frontier.max_type0_type1_head.target.term)
        (quoteClosedTm frontier.max_type0_type1_head.target.term) :=
  frontier.max_type0_type1_head.target_subjectReduction_and_profile

end CicStage3MaxArtifactFrontier

/-- Profile-side replay of the positive `Prop -> Type_0` hosted CIC witness. -/
theorem cicStage3IdentityWitness_propToType0_profileBridge :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      cicStage3PropToType0Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3IdentityWitness_hasType_propToType0

/-- Profile-side replay of the positive `Type_0 -> Type_1` hosted CIC witness. -/
theorem cicStage3IdentityWitness_type0ToType1_profileBridge :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      cicStage3Type0ToType1Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3IdentityWitness_hasType_type0ToType1

/-- Profile-side replay of the positive `Type_1 -> Type_2` hosted CIC witness. -/
theorem cicStage3IdentityWitness_type1ToType2_profileBridge :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      cicStage3Type1ToType2Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3IdentityWitness_hasType_type1ToType2

/-- Target-side landing zone for the covered Stage-3 `lift-id` micro check
`lift prop prop (univ prop)`. The pre-normal guest source itself still lives on
the guest side of the bridge; what is already honest on the current all-none
declaration boundary is the normalized target term `univ prop` and its target
type `Univ (succ prop)`. -/
theorem cicStage3LiftId_prop_prop_target_typed :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm)) :=
  hasType_cicUnivCtorOf hasType_cicProp

theorem cicStage3LiftId_prop_prop_target_profileBridge :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor cicPropTm))
        (quoteClosedTm (cicUnivCtor cicPropTm)) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3LiftId_prop_prop_target_typed

/-- Target-side replay of the normalized covered Stage-3 `term-lift` witness
`Term type_0 (lift prop type_0 (univ prop)) ↦ Univ prop`. The guest source
depends on the explicit Stage-3 rewrite footprint; the normalized target is
already a checked declaration-side kernel term. -/
theorem cicStage3TermLift_prop_type0_target_typed :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0 :=
  hasType_cicUnivProp

theorem cicStage3TermLift_prop_type0_target_profileBridge :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicPropTm))
        (quoteClosedTm (cicUniv cicPropTm)) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3TermLift_prop_type0_target_typed

/-- Target-side replay of the normalized covered Stage-3 `term-lift` witness
`Term type_1 (lift type_0 type_1 (univ type_0)) ↦ Univ type_0`. As above, the
bridge currently checks the normalized landing term honestly while the
guest-side pre-normal source remains part of the still-explicit rewrite
frontier. -/
theorem cicStage3TermLift_type0_type1_target_typed :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0 :=
  hasType_cicUnivType0

theorem cicStage3TermLift_type0_type1_target_profileBridge :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType0))
        (quoteClosedTm (cicUniv cicType0)) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3TermLift_type0_type1_target_typed

/-- Target-side replay of the normalized covered Stage-3 `term-lift` witness
`Term type_2 (lift type_1 type_2 (univ type_1)) ↦ Univ type_1`. This extends
the same covered `term-lift` family by one more concrete cumulativity step. -/
theorem cicStage3TermLift_type1_type2_target_typed :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0 :=
  hasType_cicUnivType1

theorem cicStage3TermLift_type1_type2_target_profileBridge :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType1))
        (quoteClosedTm (cicUniv cicType1)) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    cicStage3TermLift_type1_type2_target_typed

/-- Generic declaration-side target family already available for the covered
Stage-3 `lift` rows: once the source sort itself is typed on the all-none
boundary, the normalized `univ`/`Univ (succ ...)` targets are checked without
any guest-specific machinery. This is the exact theorem-facing seam where the
current concrete `prop`/`type_0` cases stop being standalone facts and become
specializations of the shared kernel-side family. -/
theorem cicStage3LiftId_target_of_sort
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) :=
  hasType_cicUnivCtorOf hs

theorem cicStage3LiftId_target_profileBridge_of_sort
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor s))
        (quoteClosedTm (cicUnivCtor s)) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    (cicStage3LiftId_target_of_sort hs)

theorem cicStage3TermLift_target_of_sort
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 :=
  hasType_cicUnivOf hs

theorem cicStage3TermLift_target_profileBridge_of_sort
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv s))
        (quoteClosedTm (cicUniv s)) :=
  cicStage3ClosedTerm_subjectReduction_and_profileBridge
    (cicStage3TermLift_target_of_sort hs)

/-- Exact family-level target interface already shared by the covered Stage-3
`lift` rows. This packages the declaration-side `univ` and `Univ (succ ...)`
families so downstream M2 work can discharge concrete guest rows by
specialization instead of re-stating them as isolated artifact facts. -/
structure CicStage3LiftTargetFamily where
  lift_id_target :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        HasTypeDecl cicStage3DeclEnv .nil
          (cicUnivCtor s)
          (cicUniv (cicSortSucc s))
  lift_id_target_profile :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        PureProfileTheoryStepStar
          (quoteClosedTm (cicUnivCtor s))
          (quoteClosedTm (cicUnivCtor s))
  term_lift_target :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        HasTypeDecl cicStage3DeclEnv .nil
          (cicUniv s)
          .u0
  term_lift_target_profile :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        PureProfileTheoryStepStar
          (quoteClosedTm (cicUniv s))
          (quoteClosedTm (cicUniv s))

theorem CicStage3LiftTargetFamily.lift_id_subjectReduction_and_profile
    (family : CicStage3LiftTargetFamily)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor s))
        (quoteClosedTm (cicUnivCtor s)) :=
  ⟨family.lift_id_target hs, family.lift_id_target_profile hs⟩

theorem CicStage3LiftTargetFamily.term_lift_subjectReduction_and_profile
    (family : CicStage3LiftTargetFamily)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv s))
        (quoteClosedTm (cicUniv s)) :=
  ⟨family.term_lift_target hs, family.term_lift_target_profile hs⟩

def cicStage3LiftTargetFamilyCertificate :
    CicStage3LiftTargetFamily :=
  { lift_id_target := by
      intro s hs
      exact cicStage3LiftId_target_of_sort hs
    lift_id_target_profile := by
      intro s hs
      exact (cicStage3LiftId_target_profileBridge_of_sort hs).2
    term_lift_target := by
      intro s hs
      exact cicStage3TermLift_target_of_sort hs
    term_lift_target_profile := by
      intro s hs
      exact (cicStage3TermLift_target_profileBridge_of_sort hs).2 }

/-- Lean-side theorem inventory mirroring the additive Stage-3 guest rewrite
obligation names from `04_cic_guest_universes_micro.metta`.

This is intentionally only the Stage-3-added footprint:
`rew-term-lift`, `rew-lift-id`, `rew-max-s1-prop`, `rew-max-prop-s2`,
`rew-max-type-type`. The inherited Stage-1 footprint remains tracked
separately; this structure records exactly what the current kernel-side bridge
can already justify for the Stage-3-specific extension. -/
structure CicStage3AdditiveObligationInventory where
  rew_max_s1_prop :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        CicStage3ClosedMaxStep (cicMax s cicPropTm) s
  rew_max_prop_s2 :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        CicStage3ClosedMaxStep (cicMax cicPropTm s) s
  rew_max_s1_prop_target_profile :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        PureProfileTheoryStepStar (quoteClosedTm s) (quoteClosedTm s)
  rew_max_prop_s2_target_profile :
    ∀ {s : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil s cicSortTm →
        PureProfileTheoryStepStar (quoteClosedTm s) (quoteClosedTm s)
  rew_max_type_type_head :
    ∀ {i j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        CicStage3ClosedMaxStep
          (cicMax (cicType i) (cicType j))
          (cicType (cicNatMax i j))
  rew_max_type_type_target_profile :
    ∀ {i j : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
        PureProfileTheoryStepStar
          (quoteClosedTm (cicType (cicNatMax i j)))
          (quoteClosedTm (cicType (cicNatMax i j)))
  rew_max_type_type_landing :
    ∀ {i j k : PureTm 0},
      HasTypeDecl cicStage3DeclEnv .nil i cicNatTm →
      HasTypeDecl cicStage3DeclEnv .nil j cicNatTm →
      CicStage1ClosedNatMaxStep (cicNatMax i j) k →
        CicStage3ClosedMaxStep
          (cicMax (cicType i) (cicType j))
          (cicType (cicNatMax i j)) ∧
          HasTypeDecl cicStage3DeclEnv .nil (cicType k) cicSortTm ∧
          PureProfileTheoryStepStar
            (quoteClosedTm (cicType k))
            (quoteClosedTm (cicType k))
  rew_max_type_type_resolved_frontier :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract
  rew_max_type_type_exact_resolved_frontier_package :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage natRecContract
  rew_max_type_type_resolved_generator_boundary :
    generatedRecursorContractResolvedIotaObligations natRecContract = []
  rew_lift_id_prop_prop_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm))
  rew_lift_id_prop_prop_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUnivCtor cicPropTm))
      (quoteClosedTm (cicUnivCtor cicPropTm))
  rew_term_lift_prop_type0_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0
  rew_term_lift_prop_type0_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUniv cicPropTm))
      (quoteClosedTm (cicUniv cicPropTm))
  rew_term_lift_type0_type1_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0
  rew_term_lift_type0_type1_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUniv cicType0))
      (quoteClosedTm (cicUniv cicType0))
  rew_term_lift_type1_type2_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0
  rew_term_lift_type1_type2_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUniv cicType1))
      (quoteClosedTm (cicUniv cicType1))

/-- Exact Lean-side obligation inventory for the currently covered Stage-3
guest extension. This packages the live bridge story using the same obligation
names the guest artifact cites, so subsequent M2 work can replace individual
debt items by theorem-by-theorem closure rather than prose. -/
def cicStage3AdditiveObligationCertificate :
    CicStage3AdditiveObligationInventory :=
  { rew_max_s1_prop := by
      intro s hs
      exact .max_s1_prop hs
    rew_max_prop_s2 := by
      intro s hs
      exact .max_prop_s2 hs
    rew_max_s1_prop_target_profile := by
      intro s hs
      exact (CicStage3ClosedMaxStep.target_profile (.max_s1_prop hs)).2
    rew_max_prop_s2_target_profile := by
      intro s hs
      exact (CicStage3ClosedMaxStep.target_profile (.max_prop_s2 hs)).2
    rew_max_type_type_head := by
      intro i j hi hj
      exact .max_type_type hi hj
    rew_max_type_type_target_profile := by
      intro i j hi hj
      exact (CicStage3ClosedMaxStep.target_profile (.max_type_type hi hj)).2
    rew_max_type_type_landing := by
      intro i j k hi hj hNat
      exact cicStage3ClosedMax_type_type_landing_of_closedNatMax hi hj hNat
    rew_max_type_type_resolved_frontier := cicStage3Type0Type0ResolvedFrontier
    rew_max_type_type_exact_resolved_frontier_package :=
      cicStage3Type0Type0ExactResolvedFrontierPackage
    rew_max_type_type_resolved_generator_boundary := cicStage3Type0Type0ResolvedGeneratorBoundary
    rew_lift_id_prop_prop_target := cicStage3LiftId_prop_prop_target_typed
    rew_lift_id_prop_prop_target_profile := cicStage3LiftId_prop_prop_target_profileBridge.2
    rew_term_lift_prop_type0_target := cicStage3TermLift_prop_type0_target_typed
    rew_term_lift_prop_type0_target_profile := cicStage3TermLift_prop_type0_target_profileBridge.2
    rew_term_lift_type0_type1_target := cicStage3TermLift_type0_type1_target_typed
    rew_term_lift_type0_type1_target_profile := cicStage3TermLift_type0_type1_target_profileBridge.2
    rew_term_lift_type1_type2_target := cicStage3TermLift_type1_type2_target_typed
    rew_term_lift_type1_type2_target_profile := cicStage3TermLift_type1_type2_target_profileBridge.2 }

theorem CicStage3AdditiveObligationInventory.rew_max_type_type_exact_resolved_nat_frontier
    (inventory : CicStage3AdditiveObligationInventory) :
    natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases inventory.rew_max_type_type_exact_resolved_frontier_package with hUnit | hNat
  · simp [natRecContract, natRecName, unitRecName] at hUnit
  · exact hNat

/-- Exact theorem-facing footprint mirroring the current guest-side
`cic-stage3-required-obligations` row order: the Stage-3 `lift` family, the
Stage-3 additive `max` rows, then the inherited Stage-1 package. This gives
M2 one honest object to consume when replacing guest debt items row-by-row by
named closed theorems. -/
structure CicStage3RequiredObligationFootprint where
  lift_target_family :
    CicStage3LiftTargetFamily
  stage3_additive_obligations :
    CicStage3AdditiveObligationInventory
  stage1_inherited_obligations :
    CicStage1InheritedObligationInventory

namespace CicStage3RequiredObligationFootprint

theorem rew_term_lift_subjectReduction_and_profile_of_sort
    (footprint : CicStage3RequiredObligationFootprint)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv s))
        (quoteClosedTm (cicUniv s)) :=
  footprint.lift_target_family.term_lift_subjectReduction_and_profile hs

theorem rew_lift_id_subjectReduction_and_profile_of_sort
    (footprint : CicStage3RequiredObligationFootprint)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor s))
        (quoteClosedTm (cicUnivCtor s)) :=
  footprint.lift_target_family.lift_id_subjectReduction_and_profile hs

theorem rew_max_s1_prop_subjectReduction_and_profile
    (footprint : CicStage3RequiredObligationFootprint)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil s cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm s)
        (quoteClosedTm s) :=
  CicStage3ClosedMaxStep.target_profile
    (footprint.stage3_additive_obligations.rew_max_s1_prop hs)

theorem rew_max_prop_s2_subjectReduction_and_profile
    (footprint : CicStage3RequiredObligationFootprint)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil s cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm s)
        (quoteClosedTm s) :=
  CicStage3ClosedMaxStep.target_profile
    (footprint.stage3_additive_obligations.rew_max_prop_s2 hs)

theorem rew_max_type_type_subjectReduction_and_profile
    (footprint : CicStage3RequiredObligationFootprint)
    {i j : PureTm 0}
    (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicType (cicNatMax i j))
      cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType (cicNatMax i j)))
        (quoteClosedTm (cicType (cicNatMax i j))) :=
  CicStage3ClosedMaxStep.target_profile
    (footprint.stage3_additive_obligations.rew_max_type_type_head hi hj)

theorem rew_max_type_type_landing
    (footprint : CicStage3RequiredObligationFootprint)
    {i j k : PureTm 0}
    (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm)
    (hNat : CicStage1ClosedNatMaxStep (cicNatMax i j) k) :
    CicStage3ClosedMaxStep
      (cicMax (cicType i) (cicType j))
      (cicType (cicNatMax i j)) ∧
      HasTypeDecl cicStage3DeclEnv .nil (cicType k) cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType k))
        (quoteClosedTm (cicType k)) :=
  footprint.stage3_additive_obligations.rew_max_type_type_landing hi hj hNat

theorem rew_max_type_type_resolved_frontier_and_nat_limitation
    (footprint : CicStage3RequiredObligationFootprint) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A :=
  ⟨ footprint.stage3_additive_obligations.rew_max_type_type_resolved_frontier
  , footprint.stage3_additive_obligations.rew_max_type_type_exact_resolved_nat_frontier.1
  , footprint.stage3_additive_obligations.rew_max_type_type_exact_resolved_nat_frontier.2.1
  , footprint.stage3_additive_obligations.rew_max_type_type_exact_resolved_nat_frontier.2.2.1
  , footprint.stage3_additive_obligations.rew_max_type_type_exact_resolved_nat_frontier.2.2.2
  ⟩

end CicStage3RequiredObligationFootprint

def cicStage3RequiredObligationFootprintCertificate :
    CicStage3RequiredObligationFootprint :=
  { lift_target_family := cicStage3LiftTargetFamilyCertificate
    stage3_additive_obligations := cicStage3AdditiveObligationCertificate
    stage1_inherited_obligations := cicStage1InheritedObligationCertificate }

theorem cicStage3Type0Type0Landing_via_additiveObligations :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) := by
  exact
    cicStage3AdditiveObligationCertificate.rew_max_type_type_landing
      (i := cicZeroTm)
      (j := cicZeroTm)
      (k := cicZeroTm)
      hasType_cicZero
      hasType_cicZero
      cicStage3Type0Type0IndexZero

theorem cicStage3Type1Type0Landing_via_additiveObligations :
    CicStage3ClosedMaxStep
      (cicMax cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) := by
  exact
    cicStage3AdditiveObligationCertificate.rew_max_type_type_landing
      (i := .app cicNatSuccTm cicZeroTm)
      (j := cicZeroTm)
      (k := .app cicNatSuccTm cicZeroTm)
      hasType_cicNatSuccZero
      hasType_cicZero
      cicStage1ClosedNatMax_succ_zero_zero

theorem cicStage3Type0Type1Landing_via_additiveObligations :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType1)
      (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) := by
  exact
    cicStage3AdditiveObligationCertificate.rew_max_type_type_landing
      (i := cicZeroTm)
      (j := .app cicNatSuccTm cicZeroTm)
      (k := .app cicNatSuccTm cicZeroTm)
      hasType_cicZero
      hasType_cicNatSuccZero
      cicStage1ClosedNatMax_zero_succ_zero

/-- Exact theorem-facing frontier for the covered Stage-3 `lift` fragment.
This packages the currently covered concrete replay targets together with the
shared generic target family they already live inside on the declaration-side
kernel boundary. -/
structure CicStage3LiftReplayFrontier where
  target_family :
    CicStage3LiftTargetFamily
  lift_id_prop_prop_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm))
  lift_id_prop_prop_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUnivCtor cicPropTm))
      (quoteClosedTm (cicUnivCtor cicPropTm))
  term_lift_prop_type0_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0
  term_lift_prop_type0_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUniv cicPropTm))
      (quoteClosedTm (cicUniv cicPropTm))
  term_lift_type0_type1_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0
  term_lift_type0_type1_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUniv cicType0))
      (quoteClosedTm (cicUniv cicType0))
  term_lift_type1_type2_target :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0
  term_lift_type1_type2_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm (cicUniv cicType1))
      (quoteClosedTm (cicUniv cicType1))

theorem CicStage3LiftReplayFrontier.lift_id_subjectReduction_and_profile_of_sort
    (frontier : CicStage3LiftReplayFrontier)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor s))
        (quoteClosedTm (cicUnivCtor s)) :=
  frontier.target_family.lift_id_subjectReduction_and_profile hs

theorem CicStage3LiftReplayFrontier.term_lift_subjectReduction_and_profile_of_sort
    (frontier : CicStage3LiftReplayFrontier)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv s))
        (quoteClosedTm (cicUniv s)) :=
  frontier.target_family.term_lift_subjectReduction_and_profile hs

theorem CicStage3LiftReplayFrontier.lift_id_prop_prop_subjectReduction_and_profile
    (frontier : CicStage3LiftReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor cicPropTm))
        (quoteClosedTm (cicUnivCtor cicPropTm)) :=
  ⟨frontier.lift_id_prop_prop_target, frontier.lift_id_prop_prop_target_profile⟩

theorem CicStage3LiftReplayFrontier.term_lift_prop_type0_subjectReduction_and_profile
    (frontier : CicStage3LiftReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicPropTm))
        (quoteClosedTm (cicUniv cicPropTm)) :=
  ⟨frontier.term_lift_prop_type0_target, frontier.term_lift_prop_type0_target_profile⟩

theorem CicStage3LiftReplayFrontier.term_lift_type0_type1_subjectReduction_and_profile
    (frontier : CicStage3LiftReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType0))
        (quoteClosedTm (cicUniv cicType0)) :=
  ⟨frontier.term_lift_type0_type1_target, frontier.term_lift_type0_type1_target_profile⟩

theorem CicStage3LiftReplayFrontier.term_lift_type1_type2_subjectReduction_and_profile
    (frontier : CicStage3LiftReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType1))
        (quoteClosedTm (cicUniv cicType1)) :=
  ⟨frontier.term_lift_type1_type2_target, frontier.term_lift_type1_type2_target_profile⟩

def cicStage3LiftReplayFrontierCertificate :
    CicStage3LiftReplayFrontier :=
  { target_family := cicStage3LiftTargetFamilyCertificate
    lift_id_prop_prop_target :=
      cicStage3AdditiveObligationCertificate.rew_lift_id_prop_prop_target
    lift_id_prop_prop_target_profile :=
      cicStage3AdditiveObligationCertificate.rew_lift_id_prop_prop_target_profile
    term_lift_prop_type0_target :=
      cicStage3AdditiveObligationCertificate.rew_term_lift_prop_type0_target
    term_lift_prop_type0_target_profile :=
      cicStage3AdditiveObligationCertificate.rew_term_lift_prop_type0_target_profile
    term_lift_type0_type1_target :=
      cicStage3AdditiveObligationCertificate.rew_term_lift_type0_type1_target
    term_lift_type0_type1_target_profile :=
      cicStage3AdditiveObligationCertificate.rew_term_lift_type0_type1_target_profile
    term_lift_type1_type2_target :=
      cicStage3AdditiveObligationCertificate.rew_term_lift_type1_type2_target
    term_lift_type1_type2_target_profile :=
      cicStage3AdditiveObligationCertificate.rew_term_lift_type1_type2_target_profile }

/-- Exact reusable certificate for the Stage-3 universes/cumulativity micro
currently covered in `04_cic_guest_universes_micro.metta`.

This is intentionally narrower than the guest rewrite-rule names themselves:
it packages the exact positive micro witnesses we currently check, together
with the resolved recursor frontier that now drives the active bridge, plus the
exact nat declaration-side limitation that still explains the concrete
`type0/type0` index debt. It should be read as "the current covered artifact
really lands here", not as "all generic Stage-3 rewrite rules are now fully
discharged." -/
structure CicStage3CoveredMicroFrontier where
  stage1_inherited_obligations :
    CicStage1InheritedObligationInventory
  stage1_covered_micro :
    CicStage1CoveredMicroFrontier
  stage3_additive_obligations :
    CicStage3AdditiveObligationInventory
  max_prop_type0 :
    CicStage3ClosedMaxStep (cicMax cicPropTm cicType0) cicType0
  max_prop_type0_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicType0)
      (quoteClosedTm cicType0)
  max_type0_prop :
    CicStage3ClosedMaxStep (cicMax cicType0 cicPropTm) cicType0
  max_type0_prop_target_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicType0)
      (quoteClosedTm cicType0)
  max_type0_type0_frontier :
    CicStage3MaxTypeTypeFrontier
  max_type1_type0_closed_landing :
    CicStage3ClosedMaxStep
      (cicMax cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1)
  max_type0_type1_closed_landing :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType1)
      (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1)
  lift_frontier :
    CicStage3LiftReplayFrontier
  prop_to_type0_bundle :
    CicStage3HostedWitnessBundle
      cicStage3PropToType0Type
      cicStage3PropToType0WitnessName
      cicStage3PropToType0WitnessDeclEnv
  type0_to_type1_bundle :
    CicStage3HostedWitnessBundle
      cicStage3Type0ToType1Type
      cicStage3Type0ToType1WitnessName
      cicStage3Type0ToType1WitnessDeclEnv
  type1_to_type2_bundle :
    CicStage3HostedWitnessBundle
      cicStage3Type1ToType2Type
      cicStage3Type1ToType2WitnessName
      cicStage3Type1ToType2WitnessDeclEnv

def cicStage3CoveredMicroCertificate : CicStage3CoveredMicroFrontier :=
  { stage1_inherited_obligations := cicStage1InheritedObligationCertificate
    stage1_covered_micro := cicStage1CoveredMicroCertificate
    stage3_additive_obligations := cicStage3AdditiveObligationCertificate
    max_prop_type0 := cicStage3ClosedMax_prop_type0
    max_prop_type0_target_profile := cicStage3ClosedMax_prop_type0_target_profile.2
    max_type0_prop := cicStage3ClosedMax_type0_prop
    max_type0_prop_target_profile := cicStage3ClosedMax_type0_prop_target_profile.2
    max_type0_type0_frontier := cicStage3MaxTypeTypeFrontierCertificate
    max_type1_type0_closed_landing := cicStage3Type1Type0Landing_via_additiveObligations
    max_type0_type1_closed_landing := cicStage3Type0Type1Landing_via_additiveObligations
    lift_frontier := cicStage3LiftReplayFrontierCertificate
    prop_to_type0_bundle := cicStage3PropToType0HostedWitnessBundle
    type0_to_type1_bundle := cicStage3Type0ToType1HostedWitnessBundle
    type1_to_type2_bundle := cicStage3Type1ToType2HostedWitnessBundle }

/-- Exact theorem-facing frontier for the currently covered Stage-3 `max`
obligations. This keeps the two direct `prop/type_0` and `type_0/prop`
replays, the two landed `type_1/type_0` and `type_0/type_1` witnesses, and
the still-conditional `type_0/type_0` lane together so downstream M2/M3 work
can consume the guest's covered `max` footprint row-by-row. -/
structure CicStage3MaxReplayFrontier where
  max_prop_type0 :
    CicStage3ClosedMaxStep (cicMax cicPropTm cicType0) cicType0
  max_type0_prop :
    CicStage3ClosedMaxStep (cicMax cicType0 cicPropTm) cicType0
  max_type0_type0_frontier :
    CicStage3MaxTypeTypeFrontier
  max_type1_type0_closed_landing :
    CicStage3ClosedMaxStep
      (cicMax cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1)
  max_type0_type1_closed_landing :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType1)
      (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1)

theorem CicStage3MaxReplayFrontier.max_prop_type0_subjectReduction_and_profile
    (frontier : CicStage3MaxReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  CicStage3ClosedMaxStep.target_profile frontier.max_prop_type0

theorem CicStage3MaxReplayFrontier.max_type0_prop_subjectReduction_and_profile
    (frontier : CicStage3MaxReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  CicStage3ClosedMaxStep.target_profile frontier.max_type0_prop

theorem CicStage3MaxReplayFrontier.max_type0_type0_subjectReduction_and_profile
    (frontier : CicStage3MaxReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  frontier.max_type0_type0_frontier.subjectReduction_and_profile

theorem CicStage3MaxReplayFrontier.max_type0_type0_closed_landing
    (frontier : CicStage3MaxReplayFrontier) :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  frontier.max_type0_type0_frontier.landing

def cicStage3MaxArtifactFrontierCertificate :
    CicStage3MaxArtifactFrontier :=
  { max_prop_type0 := cicStage3MaxPropType0ArtifactEncoding
    max_type0_prop := cicStage3MaxType0PropArtifactEncoding
    max_type0_type0_head := cicStage3MaxType0Type0HeadArtifactEncoding
    max_type1_type0_head := cicStage3MaxType1Type0HeadArtifactEncoding
    max_type0_type1_head := cicStage3MaxType0Type1HeadArtifactEncoding
    max_type0_type0_closed_landing :=
      cicStage3CoveredMicroCertificate.max_type0_type0_frontier.landing
    max_type1_type0_closed_landing :=
      cicStage3CoveredMicroCertificate.max_type1_type0_closed_landing
    max_type0_type1_closed_landing :=
      cicStage3CoveredMicroCertificate.max_type0_type1_closed_landing }

def cicStage3MaxReplayFrontierCertificate :
    CicStage3MaxReplayFrontier :=
  { max_prop_type0 := cicStage3CoveredMicroCertificate.max_prop_type0
    max_type0_prop := cicStage3CoveredMicroCertificate.max_type0_prop
    max_type0_type0_frontier := cicStage3CoveredMicroCertificate.max_type0_type0_frontier
    max_type1_type0_closed_landing :=
      cicStage3CoveredMicroCertificate.max_type1_type0_closed_landing
    max_type0_type1_closed_landing :=
      cicStage3CoveredMicroCertificate.max_type0_type1_closed_landing }

/-- Compact M3-facing replay frontier for the currently covered hosted Stage-3
CIC slice. This forgets the artifact-local bookkeeping and keeps only the
pieces already replayable as a small declaration-aware bundle: the exact
covered `max` rows, the current replayable `lift` targets, and the three
positive hosted witness bundles. -/
structure CicStage3HostedReplayFrontier where
  max_frontier :
    CicStage3MaxReplayFrontier
  lift_frontier :
    CicStage3LiftReplayFrontier
  identity_target_family :
    CicStage3IdentityWitnessTargetFamily
  prop_to_type0_bundle :
    CicStage3HostedWitnessBundle
      cicStage3PropToType0Type
      cicStage3PropToType0WitnessName
      cicStage3PropToType0WitnessDeclEnv
  type0_to_type1_bundle :
    CicStage3HostedWitnessBundle
      cicStage3Type0ToType1Type
      cicStage3Type0ToType1WitnessName
      cicStage3Type0ToType1WitnessDeclEnv
  type1_to_type2_bundle :
    CicStage3HostedWitnessBundle
      cicStage3Type1ToType2Type
      cicStage3Type1ToType2WitnessName
      cicStage3Type1ToType2WitnessDeclEnv

theorem CicStage3HostedReplayFrontier.max_prop_type0_subjectReduction_and_profile
    (frontier : CicStage3HostedReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  frontier.max_frontier.max_prop_type0_subjectReduction_and_profile

theorem CicStage3HostedReplayFrontier.max_type0_prop_subjectReduction_and_profile
    (frontier : CicStage3HostedReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  frontier.max_frontier.max_type0_prop_subjectReduction_and_profile

theorem CicStage3HostedReplayFrontier.max_type0_type0_subjectReduction_and_profile
    (frontier : CicStage3HostedReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  frontier.max_frontier.max_type0_type0_subjectReduction_and_profile

theorem CicStage3HostedReplayFrontier.max_type0_type0_closed_landing
    (frontier : CicStage3HostedReplayFrontier) :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  frontier.max_frontier.max_type0_type0_closed_landing

theorem CicStage3HostedReplayFrontier.max_type1_type0_closed_landing
    (frontier : CicStage3HostedReplayFrontier) :
    CicStage3ClosedMaxStep
      (cicMax cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) :=
  frontier.max_frontier.max_type1_type0_closed_landing

theorem CicStage3HostedReplayFrontier.max_type0_type1_closed_landing
    (frontier : CicStage3HostedReplayFrontier) :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType1)
      (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) :=
  frontier.max_frontier.max_type0_type1_closed_landing

theorem CicStage3HostedReplayFrontier.lift_id_prop_prop_subjectReduction_and_profile
    (frontier : CicStage3HostedReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor cicPropTm))
        (quoteClosedTm (cicUnivCtor cicPropTm)) :=
  frontier.lift_frontier.lift_id_prop_prop_subjectReduction_and_profile

theorem CicStage3HostedReplayFrontier.term_lift_prop_type0_subjectReduction_and_profile
    (frontier : CicStage3HostedReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicPropTm))
        (quoteClosedTm (cicUniv cicPropTm)) :=
  frontier.lift_frontier.term_lift_prop_type0_subjectReduction_and_profile

theorem CicStage3HostedReplayFrontier.term_lift_type0_type1_subjectReduction_and_profile
    (frontier : CicStage3HostedReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType0))
        (quoteClosedTm (cicUniv cicType0)) :=
  frontier.lift_frontier.term_lift_type0_type1_subjectReduction_and_profile

theorem CicStage3HostedReplayFrontier.term_lift_type1_type2_subjectReduction_and_profile
    (frontier : CicStage3HostedReplayFrontier) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType1))
        (quoteClosedTm (cicUniv cicType1)) :=
  frontier.lift_frontier.term_lift_type1_type2_subjectReduction_and_profile

theorem CicStage3HostedReplayFrontier.identity_subjectReduction_and_profile_of_sort
    (frontier : CicStage3HostedReplayFrontier)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      (cicStage1IdentityType s) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  frontier.identity_target_family.subjectReduction_and_profile_of_sort hs

theorem CicStage3HostedReplayFrontier.lift_id_subjectReduction_and_profile_of_sort
    (frontier : CicStage3HostedReplayFrontier)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor s))
        (quoteClosedTm (cicUnivCtor s)) :=
  frontier.lift_frontier.lift_id_subjectReduction_and_profile_of_sort hs

theorem CicStage3HostedReplayFrontier.term_lift_subjectReduction_and_profile_of_sort
    (frontier : CicStage3HostedReplayFrontier)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv s))
        (quoteClosedTm (cicUniv s)) :=
  frontier.lift_frontier.term_lift_subjectReduction_and_profile_of_sort hs

def cicStage3HostedReplayFrontier :
    CicStage3HostedReplayFrontier :=
  { max_frontier := cicStage3MaxReplayFrontierCertificate
    lift_frontier := cicStage3CoveredMicroCertificate.lift_frontier
    identity_target_family := cicStage3CoveredMicroCertificate.stage1_covered_micro.identity_target_family
    prop_to_type0_bundle := cicStage3CoveredMicroCertificate.prop_to_type0_bundle
    type0_to_type1_bundle := cicStage3CoveredMicroCertificate.type0_to_type1_bundle
    type1_to_type2_bundle := cicStage3CoveredMicroCertificate.type1_to_type2_bundle }

theorem CicStage3HostedWitnessBundle.declared_replay_star
    {witnessType : PureTm 0} {witnessName : DeclName} {witnessDeclEnv : DeclEnv}
    (bundle : CicStage3HostedWitnessBundle witnessType witnessName witnessDeclEnv) :
    RedStarDecl witnessDeclEnv
      (.const witnessName : PureTm 0)
      cicStage3IdentityWitness :=
  RedStarDecl.tail
    (RedStarDecl.refl (.const witnessName : PureTm 0))
    bundle.declared_delta_step

/-- First theorem-facing declared replay package extracted from a hosted witness
bundle. This is the declaration-side replay shape M3 can consume directly:
typed source constant, declaration-aware reduction to the normalized witness,
typed landing term, and quoted source/target artifacts. -/
structure CicStage3DeclaredReplayTheoremBundle
    (witnessType : PureTm 0) (witnessName : DeclName) (witnessDeclEnv : DeclEnv) where
  declared_delta :
    CheckedDeclaredConstantDelta
  source_typed :
    HasTypeDecl witnessDeclEnv .nil
      (.const witnessName : PureTm 0)
      witnessType
  delta_step :
    RedDecl witnessDeclEnv
      (.const witnessName : PureTm 0)
      cicStage3IdentityWitness
  delta_star :
    RedStarDecl witnessDeclEnv
      (.const witnessName : PureTm 0)
      cicStage3IdentityWitness
  target_typed :
    HasTypeDecl witnessDeclEnv .nil
      cicStage3IdentityWitness
      witnessType
  source_artifact_quote :
    declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const witnessName : PureTm 0)
  target_artifact_quote :
    declared_delta.targetArtifact.pattern =
      quoteClosedTm cicStage3IdentityWitness

def CicStage3HostedWitnessBundle.asDeclaredReplayTheoremBundle
    {witnessType : PureTm 0} {witnessName : DeclName} {witnessDeclEnv : DeclEnv}
    (bundle : CicStage3HostedWitnessBundle witnessType witnessName witnessDeclEnv) :
    CicStage3DeclaredReplayTheoremBundle witnessType witnessName witnessDeclEnv :=
  { declared_delta := bundle.declared_delta
    source_typed := bundle.declared_delta_source_typed
    delta_step := bundle.declared_delta_step
    delta_star := bundle.declared_replay_star
    target_typed := bundle.declared_delta_target_typed
    source_artifact_quote := bundle.declared_delta_source_artifact_quote
    target_artifact_quote := bundle.declared_delta_target_artifact_quote }

/-- M2/M3 convergence package for one hosted declared replay: the witness
extension environment sits on the generic declaration-side Church-Rosser
boundary, the standard kernel/profile embedding is recovered from that
boundary, and the concrete declared replay theorem bundle rides on top of the
same declaration interface. -/
structure CicStage3DeclaredReplayChurchRosserFrontier
    (specs : List DeclSpec) (witnessType : PureTm 0) (witnessName : DeclName) where
  signature_well_formed :
    SignatureWellFormed specs
  church_rosser_boundary :
    CheckedChurchRosserDeclKernelBoundary
      signature_well_formed
      (DeclarationSemantics.declChurchRosser (E := envOfSpecs specs))
  boundary_kernel_and_profile :
    (checkedChurchRosserDeclKernelIntoPureProfile
      signature_well_formed
      (DeclarationSemantics.declChurchRosser (E := envOfSpecs specs))).kernel =
        church_rosser_boundary.typed ∧
      (checkedChurchRosserDeclKernelIntoPureProfile
        signature_well_formed
        (DeclarationSemantics.declChurchRosser (E := envOfSpecs specs))).profile =
          Mettapedia.Languages.MeTTa.CoreProfile.pureProfile
  declared_replay :
    CicStage3DeclaredReplayTheoremBundle
      witnessType witnessName (envOfSpecs specs)

theorem CicStage3DeclaredReplayChurchRosserFrontier.replay
    {specs : List DeclSpec} {witnessType : PureTm 0} {witnessName : DeclName}
    (frontier : CicStage3DeclaredReplayChurchRosserFrontier
      specs witnessType witnessName) :
    HasTypeDecl (envOfSpecs specs) .nil
      (.const witnessName : PureTm 0)
      witnessType ∧
      RedStarDecl (envOfSpecs specs)
        (.const witnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl (envOfSpecs specs) .nil
        cicStage3IdentityWitness
        witnessType :=
  ⟨ frontier.declared_replay.source_typed
  , frontier.declared_replay.delta_star
  , frontier.declared_replay.target_typed
  ⟩

theorem CicStage3DeclaredReplayChurchRosserFrontier.artifact_quotes
    {specs : List DeclSpec} {witnessType : PureTm 0} {witnessName : DeclName}
    (frontier : CicStage3DeclaredReplayChurchRosserFrontier
      specs witnessType witnessName) :
    frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const witnessName : PureTm 0) ∧
      frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness :=
  ⟨ frontier.declared_replay.source_artifact_quote
  , frontier.declared_replay.target_artifact_quote
  ⟩

/-- M2/M3 packaged declared replay bridge for one positive external witness:
the declaration extension is carried together with its Church-Rosser boundary,
and the normalized target witness already lands on the base kernel/profile
package checked on the Stage-3 side. -/
structure CicStage3DeclaredReplayKernelProfileBridge
    (specs : List DeclSpec) (witnessType : PureTm 0) (witnessName : DeclName) where
  declared_frontier :
    CicStage3DeclaredReplayChurchRosserFrontier specs witnessType witnessName
  kernel_target :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      witnessType
  kernel_profile :
    PureProfileTheoryStepStar
      (quoteClosedTm cicStage3IdentityWitness)
      (quoteClosedTm cicStage3IdentityWitness)

theorem CicStage3DeclaredReplayKernelProfileBridge.replay_into_kernel_subjectReduction_and_profile
    {specs : List DeclSpec} {witnessType : PureTm 0} {witnessName : DeclName}
    (bridge : CicStage3DeclaredReplayKernelProfileBridge
      specs witnessType witnessName) :
    HasTypeDecl (envOfSpecs specs) .nil
      (.const witnessName : PureTm 0)
      witnessType ∧
      RedStarDecl (envOfSpecs specs)
        (.const witnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        witnessType ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) := by
  rcases bridge.declared_frontier.replay with ⟨hSource, hStar, _hTargetDecl⟩
  exact ⟨hSource, hStar, bridge.kernel_target, bridge.kernel_profile⟩

theorem CicStage3DeclaredReplayKernelProfileBridge.declared_boundary_kernel_and_profile
    {specs : List DeclSpec} {witnessType : PureTm 0} {witnessName : DeclName}
    (bridge : CicStage3DeclaredReplayKernelProfileBridge
      specs witnessType witnessName) :
    (checkedChurchRosserDeclKernelIntoPureProfile
      bridge.declared_frontier.signature_well_formed
      (DeclarationSemantics.declChurchRosser (E := envOfSpecs specs))).kernel =
        bridge.declared_frontier.church_rosser_boundary.typed ∧
      (checkedChurchRosserDeclKernelIntoPureProfile
        bridge.declared_frontier.signature_well_formed
        (DeclarationSemantics.declChurchRosser (E := envOfSpecs specs))).profile =
          Mettapedia.Languages.MeTTa.CoreProfile.pureProfile :=
  bridge.declared_frontier.boundary_kernel_and_profile

theorem CicStage3DeclaredReplayKernelProfileBridge.declared_artifact_quotes
    {specs : List DeclSpec} {witnessType : PureTm 0} {witnessName : DeclName}
    (bridge : CicStage3DeclaredReplayKernelProfileBridge
      specs witnessType witnessName) :
    bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const witnessName : PureTm 0) ∧
      bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness :=
  bridge.declared_frontier.artifact_quotes

def cicStage3PropToType0WitnessSignatureWellFormed :
    SignatureWellFormed cicStage3PropToType0WitnessSpecs where
  noShadowing := cicStage3PropToType0WitnessSpecs_noShadowing
  obligations := cicStage3PropToType0WitnessSpecs_obligations

def cicStage3Type0ToType1WitnessSignatureWellFormed :
    SignatureWellFormed cicStage3Type0ToType1WitnessSpecs where
  noShadowing := cicStage3Type0ToType1WitnessSpecs_noShadowing
  obligations := cicStage3Type0ToType1WitnessSpecs_obligations

def cicStage3Type1ToType2WitnessSignatureWellFormed :
    SignatureWellFormed cicStage3Type1ToType2WitnessSpecs where
  noShadowing := cicStage3Type1ToType2WitnessSpecs_noShadowing
  obligations := cicStage3Type1ToType2WitnessSpecs_obligations

def cicStage3PropToType0DeclaredReplayChurchRosserFrontier :
    CicStage3DeclaredReplayChurchRosserFrontier
      cicStage3PropToType0WitnessSpecs
      cicStage3PropToType0Type
      cicStage3PropToType0WitnessName :=
  let hSig := cicStage3PropToType0WitnessSignatureWellFormed
  let hBoundary :=
    checkedChurchRosserDeclKernelBoundary
      hSig
      (DeclarationSemantics.declChurchRosser
        (E := cicStage3PropToType0WitnessDeclEnv))
  { signature_well_formed := hSig
    church_rosser_boundary := hBoundary
    boundary_kernel_and_profile :=
      checkedChurchRosserDeclKernelBoundary_kernel_and_profile hBoundary
    declared_replay :=
      cicStage3PropToType0HostedWitnessBundle.asDeclaredReplayTheoremBundle }

def cicStage3Type0ToType1DeclaredReplayChurchRosserFrontier :
    CicStage3DeclaredReplayChurchRosserFrontier
      cicStage3Type0ToType1WitnessSpecs
      cicStage3Type0ToType1Type
      cicStage3Type0ToType1WitnessName :=
  let hSig := cicStage3Type0ToType1WitnessSignatureWellFormed
  let hBoundary :=
    checkedChurchRosserDeclKernelBoundary
      hSig
      (DeclarationSemantics.declChurchRosser
        (E := cicStage3Type0ToType1WitnessDeclEnv))
  { signature_well_formed := hSig
    church_rosser_boundary := hBoundary
    boundary_kernel_and_profile :=
      checkedChurchRosserDeclKernelBoundary_kernel_and_profile hBoundary
    declared_replay :=
      cicStage3Type0ToType1HostedWitnessBundle.asDeclaredReplayTheoremBundle }

def cicStage3Type1ToType2DeclaredReplayChurchRosserFrontier :
    CicStage3DeclaredReplayChurchRosserFrontier
      cicStage3Type1ToType2WitnessSpecs
      cicStage3Type1ToType2Type
      cicStage3Type1ToType2WitnessName :=
  let hSig := cicStage3Type1ToType2WitnessSignatureWellFormed
  let hBoundary :=
    checkedChurchRosserDeclKernelBoundary
      hSig
      (DeclarationSemantics.declChurchRosser
        (E := cicStage3Type1ToType2WitnessDeclEnv))
  { signature_well_formed := hSig
    church_rosser_boundary := hBoundary
    boundary_kernel_and_profile :=
      checkedChurchRosserDeclKernelBoundary_kernel_and_profile hBoundary
    declared_replay :=
      cicStage3Type1ToType2HostedWitnessBundle.asDeclaredReplayTheoremBundle }

def cicStage3PropToType0DeclaredReplayKernelProfileBridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3PropToType0WitnessSpecs
      cicStage3PropToType0Type
      cicStage3PropToType0WitnessName :=
  { declared_frontier := cicStage3PropToType0DeclaredReplayChurchRosserFrontier
    kernel_target :=
      cicStage3IdentityWitness_propToType0_profileBridge.1
    kernel_profile :=
      cicStage3IdentityWitness_propToType0_profileBridge.2 }

def cicStage3Type0ToType1DeclaredReplayKernelProfileBridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3Type0ToType1WitnessSpecs
      cicStage3Type0ToType1Type
      cicStage3Type0ToType1WitnessName :=
  { declared_frontier := cicStage3Type0ToType1DeclaredReplayChurchRosserFrontier
    kernel_target :=
      cicStage3IdentityWitness_type0ToType1_profileBridge.1
    kernel_profile :=
      cicStage3IdentityWitness_type0ToType1_profileBridge.2 }

def cicStage3Type1ToType2DeclaredReplayKernelProfileBridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3Type1ToType2WitnessSpecs
      cicStage3Type1ToType2Type
      cicStage3Type1ToType2WitnessName :=
  { declared_frontier := cicStage3Type1ToType2DeclaredReplayChurchRosserFrontier
    kernel_target :=
      cicStage3IdentityWitness_type1ToType2_profileBridge.1
    kernel_profile :=
      cicStage3IdentityWitness_type1ToType2_profileBridge.2 }

/-- First theorem-facing hosted Stage-3 replay bundle. This is the current
replayable metatheory slice: the exact covered `max` rows, the replayable
`lift` targets, the guest-named additive Stage-3 obligation ledger, and the
three positive declared replay bridges. -/
structure CicStage3HostedMetatheoryReplayBundle where
  required_obligation_footprint :
    CicStage3RequiredObligationFootprint
  max_frontier :
    CicStage3MaxReplayFrontier
  max_artifact_frontier :
    CicStage3MaxArtifactFrontier
  lift_frontier :
    CicStage3LiftReplayFrontier
  identity_target_family :
    CicStage3IdentityWitnessTargetFamily
  prop_to_type0_bridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3PropToType0WitnessSpecs
      cicStage3PropToType0Type
      cicStage3PropToType0WitnessName
  type0_to_type1_bridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3Type0ToType1WitnessSpecs
      cicStage3Type0ToType1Type
      cicStage3Type0ToType1WitnessName
  type1_to_type2_bridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3Type1ToType2WitnessSpecs
      cicStage3Type1ToType2Type
      cicStage3Type1ToType2WitnessName

def cicStage3HostedMetatheoryReplayBundle :
    CicStage3HostedMetatheoryReplayBundle :=
  { required_obligation_footprint :=
      cicStage3RequiredObligationFootprintCertificate
    max_frontier := cicStage3HostedReplayFrontier.max_frontier
    max_artifact_frontier := cicStage3MaxArtifactFrontierCertificate
    lift_frontier := cicStage3HostedReplayFrontier.lift_frontier
    identity_target_family := cicStage3HostedReplayFrontier.identity_target_family
    prop_to_type0_bridge :=
      cicStage3PropToType0DeclaredReplayKernelProfileBridge
    type0_to_type1_bridge :=
      cicStage3Type0ToType1DeclaredReplayKernelProfileBridge
    type1_to_type2_bridge :=
      cicStage3Type1ToType2DeclaredReplayKernelProfileBridge }

abbrev CicStage3HostedMetatheoryReplayBundle.stage3_additive_obligations
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    CicStage3AdditiveObligationInventory :=
  bundle.required_obligation_footprint.stage3_additive_obligations

theorem CicStage3HostedMetatheoryReplayBundle.rew_term_lift_subjectReduction_and_profile_of_sort
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv s))
        (quoteClosedTm (cicUniv s)) :=
  bundle.required_obligation_footprint.rew_term_lift_subjectReduction_and_profile_of_sort hs

theorem CicStage3HostedMetatheoryReplayBundle.rew_lift_id_subjectReduction_and_profile_of_sort
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor s))
        (quoteClosedTm (cicUnivCtor s)) :=
  bundle.required_obligation_footprint.rew_lift_id_subjectReduction_and_profile_of_sort hs

theorem CicStage3HostedMetatheoryReplayBundle.rew_max_s1_prop_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil s cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm s)
        (quoteClosedTm s) :=
  bundle.required_obligation_footprint.rew_max_s1_prop_subjectReduction_and_profile hs

theorem CicStage3HostedMetatheoryReplayBundle.rew_max_prop_s2_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil s cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm s)
        (quoteClosedTm s) :=
  bundle.required_obligation_footprint.rew_max_prop_s2_subjectReduction_and_profile hs

theorem CicStage3HostedMetatheoryReplayBundle.rew_max_type_type_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {i j : PureTm 0}
    (hi : HasTypeDecl cicStage3DeclEnv .nil i cicNatTm)
    (hj : HasTypeDecl cicStage3DeclEnv .nil j cicNatTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicType (cicNatMax i j))
      cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicType (cicNatMax i j)))
        (quoteClosedTm (cicType (cicNatMax i j))) :=
  bundle.required_obligation_footprint.rew_max_type_type_subjectReduction_and_profile hi hj

theorem CicStage3HostedMetatheoryReplayBundle.max_prop_type0_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  bundle.max_frontier.max_prop_type0_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.max_type0_prop_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  bundle.max_frontier.max_type0_prop_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.max_type0_type0_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  bundle.max_frontier.max_type0_type0_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.lift_id_prop_prop_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor cicPropTm))
        (quoteClosedTm (cicUnivCtor cicPropTm)) :=
  bundle.lift_frontier.lift_id_prop_prop_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.term_lift_prop_type0_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicPropTm))
        (quoteClosedTm (cicUniv cicPropTm)) :=
  bundle.lift_frontier.term_lift_prop_type0_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.term_lift_type0_type1_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType0))
        (quoteClosedTm (cicUniv cicType0)) :=
  bundle.lift_frontier.term_lift_type0_type1_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.term_lift_type1_type2_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType1))
        (quoteClosedTm (cicUniv cicType1)) :=
  bundle.lift_frontier.term_lift_type1_type2_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.identity_subjectReduction_and_profile_of_sort
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      cicStage3IdentityWitness
      (cicStage1IdentityType s) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  bundle.identity_target_family.subjectReduction_and_profile_of_sort hs

theorem CicStage3HostedMetatheoryReplayBundle.lift_id_subjectReduction_and_profile_of_sort
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor s)
      (cicUniv (cicSortSucc s)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor s))
        (quoteClosedTm (cicUnivCtor s)) :=
  bundle.lift_frontier.lift_id_subjectReduction_and_profile_of_sort hs

theorem CicStage3HostedMetatheoryReplayBundle.term_lift_subjectReduction_and_profile_of_sort
    (bundle : CicStage3HostedMetatheoryReplayBundle)
    {s : PureTm 0}
    (hs : HasTypeDecl cicStage3DeclEnv .nil s cicSortTm) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv s)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv s))
        (quoteClosedTm (cicUniv s)) :=
  bundle.lift_frontier.term_lift_subjectReduction_and_profile_of_sort hs

theorem CicStage3HostedMetatheoryReplayBundle.max_type0_type0_resolved_frontier_and_nat_limitation
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A :=
  bundle.max_frontier.max_type0_type0_frontier.resolved_frontier_and_nat_limitation

theorem CicStage3HostedMetatheoryReplayBundle.max_type0_type0_closed_landing_exact
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  bundle.max_frontier.max_type0_type0_closed_landing

theorem CicStage3HostedMetatheoryReplayBundle.max_type1_type0_closed_landing
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    CicStage3ClosedMaxStep
      (cicMax cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) :=
  bundle.max_frontier.max_type1_type0_closed_landing

theorem CicStage3HostedMetatheoryReplayBundle.max_type0_type1_closed_landing
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType1)
      (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) :=
  bundle.max_frontier.max_type0_type1_closed_landing

theorem CicStage3HostedMetatheoryReplayBundle.max_type0_type0_conditional_frontier_and_nat_limitation
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations natRecContract =
        [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A :=
  bundle.max_frontier.max_type0_type0_frontier.conditional_frontier_and_nat_limitation

theorem CicStage3HostedMetatheoryReplayBundle.prop_to_type0_replay_into_kernel_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
      (.const cicStage3PropToType0WitnessName : PureTm 0)
      cicStage3PropToType0Type ∧
      RedStarDecl cicStage3PropToType0WitnessDeclEnv
        (.const cicStage3PropToType0WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3PropToType0Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  bundle.prop_to_type0_bridge.replay_into_kernel_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.type0_to_type1_replay_into_kernel_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
      (.const cicStage3Type0ToType1WitnessName : PureTm 0)
      cicStage3Type0ToType1Type ∧
      RedStarDecl cicStage3Type0ToType1WitnessDeclEnv
        (.const cicStage3Type0ToType1WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type0ToType1Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  bundle.type0_to_type1_bridge.replay_into_kernel_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.type1_to_type2_replay_into_kernel_subjectReduction_and_profile
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
      (.const cicStage3Type1ToType2WitnessName : PureTm 0)
      cicStage3Type1ToType2Type ∧
      RedStarDecl cicStage3Type1ToType2WitnessDeclEnv
        (.const cicStage3Type1ToType2WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type1ToType2Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  bundle.type1_to_type2_bridge.replay_into_kernel_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryReplayBundle.prop_to_type0_declared_artifact_quotes
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    bundle.prop_to_type0_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3PropToType0WitnessName : PureTm 0) ∧
      bundle.prop_to_type0_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness := by
  exact bundle.prop_to_type0_bridge.declared_artifact_quotes

theorem CicStage3HostedMetatheoryReplayBundle.type0_to_type1_declared_artifact_quotes
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    bundle.type0_to_type1_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3Type0ToType1WitnessName : PureTm 0) ∧
      bundle.type0_to_type1_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness := by
  exact bundle.type0_to_type1_bridge.declared_artifact_quotes

theorem CicStage3HostedMetatheoryReplayBundle.type1_to_type2_declared_artifact_quotes
    (bundle : CicStage3HostedMetatheoryReplayBundle) :
    bundle.type1_to_type2_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3Type1ToType2WitnessName : PureTm 0) ∧
      bundle.type1_to_type2_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness := by
  exact bundle.type1_to_type2_bridge.declared_artifact_quotes

/-- Compact theorem-facing bundle for the currently covered hosted Stage-3 CIC
slice. This is the direct downstream M2/M3 handoff package: the exact covered
`max` rows, the concrete landed `type_1/type_0` and `type_0/type_1` max
witnesses, the Nat limitation, the replayable `lift` targets, the hosted
cumulativity witness replays into the kernel, the guest-named additive
obligation ledger, the declaration-side Church-Rosser replay bridges, and the
exact quoted external artifacts for those declared witnesses. -/
structure CicStage3HostedMetatheoryTheoremSlice where
  required_obligation_footprint :
    CicStage3RequiredObligationFootprint
  max_artifact_frontier :
    CicStage3MaxArtifactFrontier
  max_frontier :
    CicStage3MaxReplayFrontier
  lift_frontier :
    CicStage3LiftReplayFrontier
  identity_target_family :
    CicStage3IdentityWitnessTargetFamily
  prop_to_type0_bridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3PropToType0WitnessSpecs
      cicStage3PropToType0Type
      cicStage3PropToType0WitnessName
  type0_to_type1_bridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3Type0ToType1WitnessSpecs
      cicStage3Type0ToType1Type
      cicStage3Type0ToType1WitnessName
  type1_to_type2_bridge :
    CicStage3DeclaredReplayKernelProfileBridge
      cicStage3Type1ToType2WitnessSpecs
      cicStage3Type1ToType2Type
      cicStage3Type1ToType2WitnessName

abbrev CicStage3HostedMetatheoryTheoremSlice.stage3_additive_obligations
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    CicStage3AdditiveObligationInventory :=
  slice.required_obligation_footprint.stage3_additive_obligations

abbrev CicStage3HostedMetatheoryTheoremSlice.lift_target_family
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    CicStage3LiftTargetFamily :=
  slice.lift_frontier.target_family

theorem CicStage3HostedMetatheoryTheoremSlice.max_prop_type0_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  slice.max_frontier.max_prop_type0_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_prop_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  slice.max_frontier.max_type0_prop_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  slice.max_frontier.max_type0_type0_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_closed_landing
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType0)
      (cicType (cicNatMax cicZeroTm cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType0 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType0)
        (quoteClosedTm cicType0) :=
  slice.max_frontier.max_type0_type0_closed_landing

theorem CicStage3HostedMetatheoryTheoremSlice.max_type1_type0_closed_landing
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    CicStage3ClosedMaxStep
      (cicMax cicType1 cicType0)
      (cicType (cicNatMax (.app cicNatSuccTm cicZeroTm) cicZeroTm)) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) :=
  slice.max_frontier.max_type1_type0_closed_landing

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type1_closed_landing
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    CicStage3ClosedMaxStep
      (cicMax cicType0 cicType1)
      (cicType (cicNatMax cicZeroTm (.app cicNatSuccTm cicZeroTm))) ∧
      HasTypeDecl cicStage3DeclEnv .nil cicType1 cicSortTm ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicType1)
        (quoteClosedTm cicType1) :=
  slice.max_frontier.max_type0_type1_closed_landing

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_conditional_frontier
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage natRecContract :=
  slice.max_frontier.max_type0_type0_frontier.conditional_frontier

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_exact_conditional_frontier_package
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    GeneratedRecursorAdmittedExactConditionalFrontierPackage natRecContract :=
  slice.max_frontier.max_type0_type0_frontier.exact_conditional_frontier_package

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_resolved_frontier
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract :=
  slice.max_frontier.max_type0_type0_frontier.resolved_frontier

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_exact_resolved_frontier_package
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage natRecContract :=
  slice.max_frontier.max_type0_type0_frontier.exact_resolved_frontier_package

theorem CicStage3HostedMetatheoryTheoremSlice.lift_id_prop_prop_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUnivCtor cicPropTm)
      (cicUniv (cicSortSucc cicPropTm)) ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUnivCtor cicPropTm))
        (quoteClosedTm (cicUnivCtor cicPropTm)) :=
  slice.lift_frontier.lift_id_prop_prop_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.term_lift_prop_type0_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicPropTm)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicPropTm))
        (quoteClosedTm (cicUniv cicPropTm)) :=
  slice.lift_frontier.term_lift_prop_type0_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.term_lift_type0_type1_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType0)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType0))
        (quoteClosedTm (cicUniv cicType0)) :=
  slice.lift_frontier.term_lift_type0_type1_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.term_lift_type1_type2_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3DeclEnv .nil
      (cicUniv cicType1)
      .u0 ∧
      PureProfileTheoryStepStar
        (quoteClosedTm (cicUniv cicType1))
        (quoteClosedTm (cicUniv cicType1)) :=
  slice.lift_frontier.term_lift_type1_type2_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.prop_to_type0_replay_into_kernel_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
      (.const cicStage3PropToType0WitnessName : PureTm 0)
      cicStage3PropToType0Type ∧
      RedStarDecl cicStage3PropToType0WitnessDeclEnv
        (.const cicStage3PropToType0WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3PropToType0Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  slice.prop_to_type0_bridge.replay_into_kernel_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.type0_to_type1_replay_into_kernel_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
      (.const cicStage3Type0ToType1WitnessName : PureTm 0)
      cicStage3Type0ToType1Type ∧
      RedStarDecl cicStage3Type0ToType1WitnessDeclEnv
        (.const cicStage3Type0ToType1WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type0ToType1Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  slice.type0_to_type1_bridge.replay_into_kernel_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.type1_to_type2_replay_into_kernel_subjectReduction_and_profile
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
      (.const cicStage3Type1ToType2WitnessName : PureTm 0)
      cicStage3Type1ToType2Type ∧
      RedStarDecl cicStage3Type1ToType2WitnessDeclEnv
        (.const cicStage3Type1ToType2WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type1ToType2Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  slice.type1_to_type2_bridge.replay_into_kernel_subjectReduction_and_profile

theorem CicStage3HostedMetatheoryTheoremSlice.prop_to_type0_declared_artifact_quotes
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    slice.prop_to_type0_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3PropToType0WitnessName : PureTm 0) ∧
      slice.prop_to_type0_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness := by
  exact slice.prop_to_type0_bridge.declared_artifact_quotes

theorem CicStage3HostedMetatheoryTheoremSlice.type0_to_type1_declared_artifact_quotes
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    slice.type0_to_type1_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3Type0ToType1WitnessName : PureTm 0) ∧
      slice.type0_to_type1_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness := by
  exact slice.type0_to_type1_bridge.declared_artifact_quotes

theorem CicStage3HostedMetatheoryTheoremSlice.type1_to_type2_declared_artifact_quotes
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    slice.type1_to_type2_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3Type1ToType2WitnessName : PureTm 0) ∧
      slice.type1_to_type2_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness := by
  exact slice.type1_to_type2_bridge.declared_artifact_quotes

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_conditional_frontier_and_nat_limitation
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations natRecContract =
        [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases slice.max_type0_type0_exact_conditional_frontier_package with hUnit | hNat
  · simp [natRecContract, natRecName, unitRecName] at hUnit
  · exact ⟨slice.max_type0_type0_conditional_frontier, hNat⟩

theorem CicStage3HostedMetatheoryTheoremSlice.max_type0_type0_resolved_frontier_and_nat_limitation
    (slice : CicStage3HostedMetatheoryTheoremSlice) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases slice.max_type0_type0_exact_resolved_frontier_package with hUnit | hNat
  · simp [natRecContract, natRecName, unitRecName] at hUnit
  · exact ⟨slice.max_type0_type0_resolved_frontier, hNat⟩

def cicStage3HostedMetatheoryTheoremSlice :
    CicStage3HostedMetatheoryTheoremSlice :=
  let bundle := cicStage3HostedMetatheoryReplayBundle
  { required_obligation_footprint :=
      bundle.required_obligation_footprint
    max_artifact_frontier :=
      bundle.max_artifact_frontier
    max_frontier :=
      bundle.max_frontier
    lift_frontier :=
      bundle.lift_frontier
    identity_target_family :=
      bundle.identity_target_family
    prop_to_type0_bridge :=
      bundle.prop_to_type0_bridge
    type0_to_type1_bridge :=
      bundle.type0_to_type1_bridge
    type1_to_type2_bridge :=
      bundle.type1_to_type2_bridge }

/-- Theorem-facing projection of a declared hosted replay: typed source
constant, declaration-aware replay star, and typed normalized witness. -/
theorem CicStage3DeclaredReplayTheoremBundle.replay
    {witnessType : PureTm 0} {witnessName : DeclName} {witnessDeclEnv : DeclEnv}
    (bundle : CicStage3DeclaredReplayTheoremBundle
      witnessType witnessName witnessDeclEnv) :
    HasTypeDecl witnessDeclEnv .nil
      (.const witnessName : PureTm 0)
      witnessType ∧
      RedStarDecl witnessDeclEnv
        (.const witnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl witnessDeclEnv .nil
        cicStage3IdentityWitness
        witnessType :=
  ⟨bundle.source_typed, bundle.delta_star, bundle.target_typed⟩

/-- The checked declaration-valued replay also remembers the exact quoted
source and target artifacts that M3 will re-host. -/
theorem CicStage3DeclaredReplayTheoremBundle.artifact_quotes
    {witnessType : PureTm 0} {witnessName : DeclName} {witnessDeclEnv : DeclEnv}
    (bundle : CicStage3DeclaredReplayTheoremBundle
      witnessType witnessName witnessDeclEnv) :
    bundle.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const witnessName : PureTm 0) ∧
      bundle.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness :=
  ⟨bundle.source_artifact_quote, bundle.target_artifact_quote⟩

/-- M3-facing hosted replay seam: the external witness constant is typed in its
extension environment, replays declaration-side to the normalized witness, and
lands on a base-kernel witness that is already checked and profiled. -/
theorem CicStage3HostedWitnessBundle.declared_replay_into_kernel_subjectReduction_and_profile
    {witnessType : PureTm 0} {witnessName : DeclName} {witnessDeclEnv : DeclEnv}
    (bundle : CicStage3HostedWitnessBundle
      witnessType witnessName witnessDeclEnv) :
    HasTypeDecl witnessDeclEnv .nil
      (.const witnessName : PureTm 0)
      witnessType ∧
      RedStarDecl witnessDeclEnv
        (.const witnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        witnessType ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  ⟨ bundle.declared_delta_source_typed
  , bundle.declared_replay_star
  , bundle.kernel_witness
  , bundle.kernel_profile
  ⟩

/-- Current theorem-facing replay of the hosted positive `Prop -> Type_0`
cumulativity witness. -/
theorem cicStage3PropToType0HostedWitness_replay_into_kernel_subjectReduction_and_profile :
    HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
      (.const cicStage3PropToType0WitnessName : PureTm 0)
      cicStage3PropToType0Type ∧
      RedStarDecl cicStage3PropToType0WitnessDeclEnv
        (.const cicStage3PropToType0WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3PropToType0Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  CicStage3HostedWitnessBundle.declared_replay_into_kernel_subjectReduction_and_profile
    cicStage3PropToType0HostedWitnessBundle

/-- Current theorem-facing replay of the hosted positive `Type_0 -> Type_1`
cumulativity witness. -/
theorem cicStage3Type0ToType1HostedWitness_replay_into_kernel_subjectReduction_and_profile :
    HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
      (.const cicStage3Type0ToType1WitnessName : PureTm 0)
      cicStage3Type0ToType1Type ∧
      RedStarDecl cicStage3Type0ToType1WitnessDeclEnv
        (.const cicStage3Type0ToType1WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type0ToType1Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  CicStage3HostedWitnessBundle.declared_replay_into_kernel_subjectReduction_and_profile
    cicStage3Type0ToType1HostedWitnessBundle

/-- Current theorem-facing replay of the hosted positive `Type_1 -> Type_2`
cumulativity witness. -/
theorem cicStage3Type1ToType2HostedWitness_replay_into_kernel_subjectReduction_and_profile :
    HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
      (.const cicStage3Type1ToType2WitnessName : PureTm 0)
      cicStage3Type1ToType2Type ∧
      RedStarDecl cicStage3Type1ToType2WitnessDeclEnv
        (.const cicStage3Type1ToType2WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3DeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type1ToType2Type ∧
      PureProfileTheoryStepStar
        (quoteClosedTm cicStage3IdentityWitness)
        (quoteClosedTm cicStage3IdentityWitness) :=
  CicStage3HostedWitnessBundle.declared_replay_into_kernel_subjectReduction_and_profile
    cicStage3Type1ToType2HostedWitnessBundle

/-- The first declared replay theorem bundle is now consumable without unpacking
the bundle by hand: this is the current external `Prop -> Type_0` witness
replay theorem. -/
theorem cicStage3PropToType0DeclaredReplayTheorem :
    HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
      (.const cicStage3PropToType0WitnessName : PureTm 0)
      cicStage3PropToType0Type ∧
      RedStarDecl cicStage3PropToType0WitnessDeclEnv
        (.const cicStage3PropToType0WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3PropToType0WitnessDeclEnv .nil
        cicStage3IdentityWitness
        cicStage3PropToType0Type :=
  cicStage3HostedMetatheoryReplayBundle.prop_to_type0_bridge.declared_frontier.replay

/-- The first declared replay theorem bundle is now consumable without unpacking
the bundle by hand: this is the current external `Type_0 -> Type_1` witness
replay theorem. -/
theorem cicStage3Type0ToType1DeclaredReplayTheorem :
    HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
      (.const cicStage3Type0ToType1WitnessName : PureTm 0)
      cicStage3Type0ToType1Type ∧
      RedStarDecl cicStage3Type0ToType1WitnessDeclEnv
        (.const cicStage3Type0ToType1WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3Type0ToType1WitnessDeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type0ToType1Type :=
  cicStage3HostedMetatheoryReplayBundle.type0_to_type1_bridge.declared_frontier.replay

/-- The first declared replay theorem bundle is now consumable without unpacking
the bundle by hand: this is the current external `Type_1 -> Type_2` witness
replay theorem. -/
theorem cicStage3Type1ToType2DeclaredReplayTheorem :
    HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
      (.const cicStage3Type1ToType2WitnessName : PureTm 0)
      cicStage3Type1ToType2Type ∧
      RedStarDecl cicStage3Type1ToType2WitnessDeclEnv
        (.const cicStage3Type1ToType2WitnessName : PureTm 0)
        cicStage3IdentityWitness ∧
      HasTypeDecl cicStage3Type1ToType2WitnessDeclEnv .nil
        cicStage3IdentityWitness
        cicStage3Type1ToType2Type :=
  cicStage3HostedMetatheoryReplayBundle.type1_to_type2_bridge.declared_frontier.replay

theorem cicStage3PropToType0DeclaredReplay_artifact_quotes :
    cicStage3HostedMetatheoryReplayBundle.prop_to_type0_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3PropToType0WitnessName : PureTm 0) ∧
      cicStage3HostedMetatheoryReplayBundle.prop_to_type0_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness :=
  cicStage3HostedMetatheoryReplayBundle.prop_to_type0_bridge.declared_artifact_quotes

theorem cicStage3Type0ToType1DeclaredReplay_artifact_quotes :
    cicStage3HostedMetatheoryReplayBundle.type0_to_type1_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3Type0ToType1WitnessName : PureTm 0) ∧
      cicStage3HostedMetatheoryReplayBundle.type0_to_type1_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness :=
  cicStage3HostedMetatheoryReplayBundle.type0_to_type1_bridge.declared_artifact_quotes

theorem cicStage3Type1ToType2DeclaredReplay_artifact_quotes :
    cicStage3HostedMetatheoryReplayBundle.type1_to_type2_bridge.declared_frontier.declared_replay.declared_delta.sourceArtifact.pattern =
      quoteClosedTm (.const cicStage3Type1ToType2WitnessName : PureTm 0) ∧
      cicStage3HostedMetatheoryReplayBundle.type1_to_type2_bridge.declared_frontier.declared_replay.declared_delta.targetArtifact.pattern =
        quoteClosedTm cicStage3IdentityWitness :=
  cicStage3HostedMetatheoryReplayBundle.type1_to_type2_bridge.declared_artifact_quotes

/-- Lean mirror of the DIndG artifact's `sr-ok` witness shape.

The runtime artifact computes a normal form `nf t` and compares `infer t` with
`infer (nf t)`.  On the Lean side we express the trusted part of that claim as:
the source term has type `A`, and the nominated normal form is reachable by the
declaration-aware reduction relation. -/
structure DIndGSRArtifactWitness (specs : List DeclSpec)
    (t nfT A : PureTm 0) where
  source_typed :
    HasTypeDecl (envOfSpecs specs) .nil t A
  normalizes :
    RedStarDecl (envOfSpecs specs) t nfT

/-- Declaration-side type uniqueness, stated explicitly as the metatheory
needed to turn preservation plus the target `infer` typing judgment into
convertibility of the two inferred types.  This is deliberately separate from
the artifact `conv` readout. -/
abbrev DeclTypeUniqueness (E : DeclEnv) : Prop :=
  ∀ {n : Nat} {Γ : Ctx n} {t A B : PureTm n},
    HasTypeDecl E Γ t A →
      HasTypeDecl E Γ t B →
        ConvDecl E A B

/-- Lean-side admission mirror sufficient for the artifact-level SR claim.

This is intentionally only a bridge to the canonical declaration packages:
checked signature well-formedness plus declaration-side Church-Rosser. -/
structure DIndGSRAdmissionMirror (specs : List DeclSpec) where
  signature_well_formed :
    SignatureWellFormed specs
  church_rosser :
    DeclarationSemantics.DeclChurchRosser (envOfSpecs specs)

namespace DIndGSRAdmissionMirror

def ofSignatureWellFormed {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs) :
    DIndGSRAdmissionMirror specs :=
  { signature_well_formed := hSig
    church_rosser := DeclarationSemantics.declChurchRosser }

theorem toDeclSpecChurchRosserPackage {specs : List DeclSpec}
    (admission : DIndGSRAdmissionMirror specs) :
    DeclSpecChurchRosserPackage specs :=
  admission.signature_well_formed.declSpecChurchRosserPackage_of_church_rosser
    admission.church_rosser

/-- The generic Lean theorem corresponding to the artifact's `sr-ok` claim:
normalization preserves the source inferred type whenever the normal form is
reachable by the declaration-aware reduction relation. -/
theorem sr_ok_via_declChurchRosser {specs : List DeclSpec}
    (admission : DIndGSRAdmissionMirror specs)
    {t nfT A : PureTm 0}
    (witness : DIndGSRArtifactWitness specs t nfT A) :
    HasTypeDecl (envOfSpecs specs) .nil nfT A :=
  admission.signature_well_formed.redStarDecl_preserves_type_of_church_rosser
    admission.church_rosser
    witness.source_typed
    witness.normalizes

/-- The corresponding confluence readout: two artifact normalizations from the
same term must be joinable in the declaration-aware reduction relation. -/
theorem normalization_joinable_via_declChurchRosser {specs : List DeclSpec}
    (admission : DIndGSRAdmissionMirror specs)
    {t nf₁ nf₂ : PureTm 0}
    (h₁ : RedStarDecl (envOfSpecs specs) t nf₁)
    (h₂ : RedStarDecl (envOfSpecs specs) t nf₂) :
    ∃ u : PureTm 0,
      RedStarDecl (envOfSpecs specs) nf₁ u ∧
      RedStarDecl (envOfSpecs specs) nf₂ u :=
  admission.signature_well_formed.redStarDecl_confluence_of_church_rosser
    admission.church_rosser
    h₁
    h₂

end DIndGSRAdmissionMirror

/-- Lean mirror of the DIndG artifact's fail-closed admission gate.

The kernel artifact's `sig-admitted-with-elims` gate requires an admitted
signature, generated eliminator admission, constructor-head/current-gate
evidence, and resolved generated-iota preservation evidence before its `sr-ok`
checks are trusted.  This record names exactly that correspondence while
delegating the metatheory to the canonical declaration and recursor packages. -/
structure DIndGAdmitted
    (specs : List DeclSpec) (contracts : List FamilyRecursorDeclContract) where
  signature_admitted :
    SignatureWellFormed specs
  constructor_head_orthogonality :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorCurrentGateWitness contract
  generated_eliminators_admitted :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorContractAdmitted contract
  generated_iota_preservation :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract
  church_rosser :
    DeclarationSemantics.DeclChurchRosser (envOfSpecs specs)

namespace DIndGAdmitted

def toSRAdmissionMirror {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (admission : DIndGAdmitted specs contracts) :
    DIndGSRAdmissionMirror specs :=
  { signature_well_formed := admission.signature_admitted
    church_rosser := admission.church_rosser }

theorem generated_iota_current_gate {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (admission : DIndGAdmitted specs contracts)
    {contract : FamilyRecursorDeclContract}
    (hmem : contract ∈ contracts) :
    GeneratedRecursorCurrentGateWitness contract :=
  admission.constructor_head_orthogonality contract hmem

theorem generated_iota_resolved_obligations {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (admission : DIndGAdmitted specs contracts)
    {contract : FamilyRecursorDeclContract}
    (hmem : contract ∈ contracts) :
    generatedRecursorContractResolvedIotaObligations contract = [] :=
  (admission.generated_iota_preservation contract hmem).2.1

theorem generated_iota_exact_frontier {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (admission : DIndGAdmitted specs contracts)
    {contract : FamilyRecursorDeclContract}
    (hmem : contract ∈ contracts) :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage contract :=
  (admission.generated_iota_preservation contract hmem).2.2

/-- The artifact-level `sr-ok` readout through the full DIndG admission gate:
once the gate supplies the declaration Church-Rosser package, the source
inferred type is preserved along the artifact's `nf` reduction path. -/
theorem sr_ok_via_artifact_gate {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (admission : DIndGAdmitted specs contracts)
    {t nfT A : PureTm 0}
    (witness : DIndGSRArtifactWitness specs t nfT A) :
    HasTypeDecl (envOfSpecs specs) .nil nfT A :=
  DIndGSRAdmissionMirror.sr_ok_via_declChurchRosser
    admission.toSRAdmissionMirror
    witness

end DIndGAdmitted

/-- Artifact witness specialized to a generated-iota normalization path.

The `generated_iota_steps` field records that the artifact's nominated
normalization came from the generated recursor rule family; the inherited
`normalizes` field is the declaration reduction path used by the SR theorem. -/
structure DIndGGeneratedIotaArtifactWitness
    (specs : List DeclSpec) (contracts : List FamilyRecursorDeclContract)
    (t nfT A : PureTm 0)
    extends DIndGSRArtifactWitness specs t nfT A where
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ contracts
  generated_iota_steps :
    Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t nfT

namespace DIndGGeneratedIotaArtifactWitness

theorem closed_slice_steps_to_decl_reduction
    {contract : FamilyRecursorDeclContract}
    (frontier : GeneratedRecursorConditionalDeclFrontierPackage contract)
    {t nfT : PureTm 0}
    (hsteps :
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t nfT) :
    RedStarDecl unitRecDeclEnv t nfT := by
  rcases frontier with ⟨_hGate, hSlice, _hCoverage⟩
  exact hSlice.1 hsteps

theorem closed_slice_preserves_type
    {contract : FamilyRecursorDeclContract}
    (frontier : GeneratedRecursorConditionalDeclFrontierPackage contract)
    {t nfT A : PureTm 0}
    (ht : HasTypeDecl unitRecDeclEnv .nil t A)
    (hsteps :
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t nfT) :
    HasTypeDecl unitRecDeclEnv .nil nfT A := by
  rcases frontier with ⟨_hGate, hSlice, _hCoverage⟩
  exact hSlice.2.1 ht hsteps

theorem frontier_available {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    {t nfT A : PureTm 0}
    (admission : DIndGAdmitted specs contracts)
    (witness : DIndGGeneratedIotaArtifactWitness specs contracts t nfT A) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage witness.contract :=
  admission.generated_iota_preservation witness.contract witness.contract_mem

/-- Generated-iota specialization of the runtime artifact's `sr-ok` theorem. -/
theorem sr_ok_via_artifact_gate {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (admission : DIndGAdmitted specs contracts)
    {t nfT A : PureTm 0}
    (witness : DIndGGeneratedIotaArtifactWitness specs contracts t nfT A) :
    HasTypeDecl (envOfSpecs specs) .nil nfT A :=
  DIndGAdmitted.sr_ok_via_artifact_gate
    admission
    witness.toDIndGSRArtifactWitness

end DIndGGeneratedIotaArtifactWitness

/-- Abstract handle for the runtime artifact's admission predicate.

This is deliberately not a Lean reimplementation of `sig-admitted-with-elims`.
It is the proposition supplied by the artifact bridge for the raw runtime
signature it translates. -/
structure DIndGArtifactGate (ArtifactSig : Type) where
  sigAdmittedWithElims :
    ArtifactSig → Prop

/-- Explicit correspondence from a raw DIndG artifact signature to the
canonical Lean declaration and generated-recursor data.

This is the bridge layer between the executable runtime gate and the Lean
metatheory: once the artifact bridge establishes this record, the mirror
admission used by the SR theorem is derived, not assumed. -/
structure DIndGArtifactCorrespondence
    {ArtifactSig : Type}
    (gate : DIndGArtifactGate ArtifactSig)
    (sig : ArtifactSig)
    (specs : List DeclSpec)
    (contracts : List FamilyRecursorDeclContract) where
  gate_succeeds :
    gate.sigAdmittedWithElims sig
  signature_translation :
    SignatureWellFormed specs
  constructor_head_orthogonality_translation :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorCurrentGateWitness contract
  generated_eliminator_translation :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorContractAdmitted contract
  generated_iota_preservation_translation :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract
  declaration_church_rosser :
    DeclarationSemantics.DeclChurchRosser (envOfSpecs specs)

/-- The Lean metatheory readout supplied after the raw artifact signature has
been translated.  This deliberately does not contain the runtime gate result
itself: the theorem below keeps `sig-admitted-with-elims sig` as an explicit
hypothesis so the final extractor/gate obligation cannot be hidden inside a
Stage-3 instance. -/
structure DIndGArtifactMetatheoryReadout
    {ArtifactSig : Type}
    (_gate : DIndGArtifactGate ArtifactSig)
    (_sig : ArtifactSig)
    (specs : List DeclSpec)
    (contracts : List FamilyRecursorDeclContract) where
  signature_translation :
    SignatureWellFormed specs
  constructor_head_orthogonality_translation :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorCurrentGateWitness contract
  generated_eliminator_translation :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorContractAdmitted contract
  generated_iota_preservation_translation :
    ∀ contract, contract ∈ contracts →
      GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract
  declaration_church_rosser :
    DeclarationSemantics.DeclChurchRosser (envOfSpecs specs)

namespace DIndGArtifactCorrespondence

def ofGateAndReadout {ArtifactSig : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (gateSucceeds : gate.sigAdmittedWithElims sig)
    (readout :
      DIndGArtifactMetatheoryReadout gate sig specs contracts) :
    DIndGArtifactCorrespondence gate sig specs contracts :=
  { gate_succeeds := gateSucceeds
    signature_translation := readout.signature_translation
    constructor_head_orthogonality_translation :=
      readout.constructor_head_orthogonality_translation
    generated_eliminator_translation :=
      readout.generated_eliminator_translation
    generated_iota_preservation_translation :=
      readout.generated_iota_preservation_translation
    declaration_church_rosser := readout.declaration_church_rosser }

def toAdmitted {ArtifactSig : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr :
      DIndGArtifactCorrespondence gate sig specs contracts) :
    DIndGAdmitted specs contracts :=
  { signature_admitted := corr.signature_translation
    constructor_head_orthogonality :=
      corr.constructor_head_orthogonality_translation
    generated_eliminators_admitted :=
      corr.generated_eliminator_translation
    generated_iota_preservation :=
      corr.generated_iota_preservation_translation
    church_rosser := corr.declaration_church_rosser }

end DIndGArtifactCorrespondence

/-- Term-level correspondence for one generated-iota artifact redex and its
runtime-normalized target.

The bridge records both artifact inference results as Lean typing derivations,
separately records that the artifact `nf` path lands as declaration-aware
reduction, and records the artifact-infer readout agreement needed to compare
the computed target type with the type preserved by subject reduction.

This last field is deliberately local to the artifact readout; it is not a
global type-uniqueness claim for the declaration calculus. -/
structure DIndGArtifactTermCorrespondence
    {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (_corr : DIndGArtifactCorrespondence gate sig specs contracts)
    (_term : ArtifactTerm)
    (t nfT sourceInfer targetInfer : PureTm 0) where
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ contracts
  source_infer_typed :
    HasTypeDecl (envOfSpecs specs) .nil t sourceInfer
  nf_to_decl_reduction :
    RedStarDecl (envOfSpecs specs) t nfT
  target_infer_typed :
    HasTypeDecl (envOfSpecs specs) .nil nfT targetInfer
  target_infer_agrees :
    HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer →
      ConvDecl (envOfSpecs specs) sourceInfer targetInfer

namespace DIndGArtifactTermCorrespondence

def ofClosedGeneratedIotaStep {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    {corr : DIndGArtifactCorrespondence gate sig specs contracts}
    {term : ArtifactTerm}
    {contract : FamilyRecursorDeclContract}
    (contractMem : contract ∈ contracts)
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sourceTyped :
      HasTypeDecl (envOfSpecs specs) .nil t sourceInfer)
    (generatedStep :
      GeneratedRecursorContractClosedIotaStep contract t nfT)
    (realized :
      GeneratedRecursorContractClosedIotaRealizedIn
        (envOfSpecs specs) contract)
    (targetTyped :
      HasTypeDecl (envOfSpecs specs) .nil nfT targetInfer)
    (targetInferAgrees :
      HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer →
        ConvDecl (envOfSpecs specs) sourceInfer targetInfer) :
    DIndGArtifactTermCorrespondence
      corr term t nfT sourceInfer targetInfer :=
  { contract := contract
    contract_mem := contractMem
    source_infer_typed := sourceTyped
    nf_to_decl_reduction := realized generatedStep
    target_infer_typed := targetTyped
    target_infer_agrees := targetInferAgrees }

def toSRArtifactWitness {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    {corr : DIndGArtifactCorrespondence gate sig specs contracts}
    {term : ArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (termCorr :
      DIndGArtifactTermCorrespondence
        corr term t nfT sourceInfer targetInfer) :
    DIndGSRArtifactWitness specs t nfT sourceInfer :=
  { source_typed := termCorr.source_infer_typed
    normalizes := termCorr.nf_to_decl_reduction }

  /-- Parameterized artifact SR readout: for any raw DIndG artifact signature whose
  `sig-admitted-with-elims` gate has been connected to Lean by the correspondence
  record, the source inferred type is preserved by `nf`. -/
  theorem source_infer_preserved_by_nf {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGArtifactCorrespondence gate sig specs contracts)
    {term : ArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (termCorr :
      DIndGArtifactTermCorrespondence
        corr term t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer :=
  DIndGAdmitted.sr_ok_via_artifact_gate
    corr.toAdmitted
    termCorr.toSRArtifactWitness

  /-- Parameterized artifact `infer`/`nf` convertibility readout. The conversion is
  obtained from the term correspondence's artifact-infer readout agreement, not
  from a global declaration type-uniqueness theorem. -/
  theorem infer_nf_convertible_by_artifact_readout
    {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGArtifactCorrespondence gate sig specs contracts)
    {term : ArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (termCorr :
      DIndGArtifactTermCorrespondence
        corr term t nfT sourceInfer targetInfer) :
    ConvDecl (envOfSpecs specs) sourceInfer targetInfer :=
  termCorr.target_infer_agrees
    (source_infer_preserved_by_nf corr termCorr)

  /-- The artifact theorem shape with the runtime gate success exposed as a direct
  hypothesis: if `sig-admitted-with-elims sig` succeeds, and the bridge has
  translated that artifact into the canonical Lean metatheory readout, then `nf`
  preserves the source inferred type.  The remaining work for the final kernel
  artifact theorem is deriving the readout and term correspondence from the
  actual runtime artifact data, not assuming them. -/
  theorem source_infer_preserved_of_sig_admitted_with_elims
      {ArtifactSig ArtifactTerm : Type}
      {gate : DIndGArtifactGate ArtifactSig}
      {sig : ArtifactSig}
      {specs : List DeclSpec}
      {contracts : List FamilyRecursorDeclContract}
      (gateSucceeds : gate.sigAdmittedWithElims sig)
      (readout :
        DIndGArtifactMetatheoryReadout gate sig specs contracts)
      {term : ArtifactTerm}
      {t nfT sourceInfer targetInfer : PureTm 0}
      (termCorr :
        DIndGArtifactTermCorrespondence
          (DIndGArtifactCorrespondence.ofGateAndReadout
            gateSucceeds readout)
          term t nfT sourceInfer targetInfer) :
      HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer :=
    source_infer_preserved_by_nf
      (DIndGArtifactCorrespondence.ofGateAndReadout
        gateSucceeds readout)
      termCorr

  /-- Exact `sr-ok` convertibility readout in the same exposed-gate form:
  the runtime `infer sig [] t` and `infer sig [] (nf sig t)` readouts are Lean
  convertible once the term correspondence supplies the artifact-infer
  agreement for the target. -/
  theorem infer_nf_convertible_of_sig_admitted_with_elims
      {ArtifactSig ArtifactTerm : Type}
      {gate : DIndGArtifactGate ArtifactSig}
      {sig : ArtifactSig}
      {specs : List DeclSpec}
      {contracts : List FamilyRecursorDeclContract}
      (gateSucceeds : gate.sigAdmittedWithElims sig)
      (readout :
        DIndGArtifactMetatheoryReadout gate sig specs contracts)
      {term : ArtifactTerm}
      {t nfT sourceInfer targetInfer : PureTm 0}
      (termCorr :
        DIndGArtifactTermCorrespondence
          (DIndGArtifactCorrespondence.ofGateAndReadout
            gateSucceeds readout)
          term t nfT sourceInfer targetInfer) :
      ConvDecl (envOfSpecs specs) sourceInfer targetInfer :=
    infer_nf_convertible_by_artifact_readout
      (DIndGArtifactCorrespondence.ofGateAndReadout
        gateSucceeds readout)
      termCorr

/-- Closed generated-iota readout: when the artifact `nf` step is one of the
generated closed-iota steps and that step is realized by the translated
declaration environment, the generic artifact theorem gives the preserved
source inferred type. -/
theorem source_infer_preserved_by_closed_generated_iota_step
    {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGArtifactCorrespondence gate sig specs contracts)
    {term : ArtifactTerm}
    {contract : FamilyRecursorDeclContract}
    (contractMem : contract ∈ contracts)
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sourceTyped :
      HasTypeDecl (envOfSpecs specs) .nil t sourceInfer)
    (generatedStep :
      GeneratedRecursorContractClosedIotaStep contract t nfT)
    (realized :
      GeneratedRecursorContractClosedIotaRealizedIn
        (envOfSpecs specs) contract)
    (targetTyped :
      HasTypeDecl (envOfSpecs specs) .nil nfT targetInfer)
    (targetInferAgrees :
      HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer →
        ConvDecl (envOfSpecs specs) sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer :=
  source_infer_preserved_by_nf corr
    (ofClosedGeneratedIotaStep
      (corr := corr)
      (term := term)
      contractMem
      sourceTyped
      generatedStep
      realized
      targetTyped
      targetInferAgrees)

/-- Closed generated-iota `infer`/`nf` readout. The generated step and its
declaration realization are explicit, and the only remaining readout obligation
is the artifact-infer agreement for the computed target type. -/
theorem infer_nf_convertible_of_closed_generated_iota_step
    {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGArtifactCorrespondence gate sig specs contracts)
    {term : ArtifactTerm}
    {contract : FamilyRecursorDeclContract}
    (contractMem : contract ∈ contracts)
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sourceTyped :
      HasTypeDecl (envOfSpecs specs) .nil t sourceInfer)
    (generatedStep :
      GeneratedRecursorContractClosedIotaStep contract t nfT)
    (realized :
      GeneratedRecursorContractClosedIotaRealizedIn
        (envOfSpecs specs) contract)
    (targetTyped :
      HasTypeDecl (envOfSpecs specs) .nil nfT targetInfer)
    (targetInferAgrees :
      HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer →
        ConvDecl (envOfSpecs specs) sourceInfer targetInfer) :
    ConvDecl (envOfSpecs specs) sourceInfer targetInfer :=
  infer_nf_convertible_by_artifact_readout corr
    (ofClosedGeneratedIotaStep
      (corr := corr)
      (term := term)
      contractMem
      sourceTyped
      generatedStep
      realized
      targetTyped
      targetInferAgrees)

end DIndGArtifactTermCorrespondence

/-- Generated-iota steps seen by the artifact bridge after the recursor frontier
has been resolved. Closed steps are declaration reductions; unary-open steps are
the Nat-successor style residuals whose target typing is checked directly. -/
inductive DIndGArtifactResolvedIotaStep
    (contract : FamilyRecursorDeclContract) (t nfT : PureTm 0) : Prop where
  | closed :
      GeneratedRecursorContractClosedIotaStep contract t nfT →
        DIndGArtifactResolvedIotaStep contract t nfT
  | unary_open :
      (∃ pilot,
        generatedRecursorPilot contract = some pilot ∧
          GeneratedUnaryOpenIotaStep pilot t nfT) →
        DIndGArtifactResolvedIotaStep contract t nfT

/-- Why the resolved artifact `nf` target preserves the source inferred type.
The first branch is ordinary declaration-level subject reduction. The second is
the explicitly isolated Nat/open-successor style case: not a closed declaration
reduction, but already checked at the preserved type. -/
inductive DIndGArtifactNFJustification
    (E : DeclEnv) (t nfT sourceInfer : PureTm 0) : Prop where
  | decl_reduction :
      RedStarDecl E t nfT →
        DIndGArtifactNFJustification E t nfT sourceInfer
  | direct_generated_iota_preservation :
      HasTypeDecl E .nil nfT sourceInfer →
        DIndGArtifactNFJustification E t nfT sourceInfer

/-- Term-level correspondence for the resolved generated-iota frontier. This is
the artifact-readout shape needed after Nat/open-successor is classified as a
typed computation residual rather than forced into the closed-reduction slice. -/
structure DIndGResolvedArtifactTermCorrespondence
    {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (_corr : DIndGArtifactCorrespondence gate sig specs contracts)
    (_term : ArtifactTerm)
    (t nfT sourceInfer targetInfer : PureTm 0) where
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ contracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract t nfT
  source_infer_typed :
    HasTypeDecl (envOfSpecs specs) .nil t sourceInfer
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs specs) t nfT sourceInfer
  target_infer_typed :
    HasTypeDecl (envOfSpecs specs) .nil nfT targetInfer
  target_infer_agrees :
    HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer →
      ConvDecl (envOfSpecs specs) sourceInfer targetInfer

namespace DIndGResolvedArtifactTermCorrespondence

def ofClosedGeneratedIotaStep {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    {corr : DIndGArtifactCorrespondence gate sig specs contracts}
    {term : ArtifactTerm}
    {contract : FamilyRecursorDeclContract}
    (contractMem : contract ∈ contracts)
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sourceTyped :
      HasTypeDecl (envOfSpecs specs) .nil t sourceInfer)
    (generatedStep :
      GeneratedRecursorContractClosedIotaStep contract t nfT)
    (realized :
      GeneratedRecursorContractClosedIotaRealizedIn
        (envOfSpecs specs) contract)
    (targetTyped :
      HasTypeDecl (envOfSpecs specs) .nil nfT targetInfer)
    (targetInferAgrees :
      HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer →
        ConvDecl (envOfSpecs specs) sourceInfer targetInfer) :
    DIndGResolvedArtifactTermCorrespondence
      corr term t nfT sourceInfer targetInfer :=
  { contract := contract
    contract_mem := contractMem
    generated_iota_step := .closed generatedStep
    source_infer_typed := sourceTyped
    nf_justification := .decl_reduction (realized generatedStep)
    target_infer_typed := targetTyped
    target_infer_agrees := targetInferAgrees }

def ofUnaryOpenGeneratedIotaStep {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    {corr : DIndGArtifactCorrespondence gate sig specs contracts}
    {term : ArtifactTerm}
    {contract : FamilyRecursorDeclContract}
    (contractMem : contract ∈ contracts)
    {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot)
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sourceTyped :
      HasTypeDecl (envOfSpecs specs) .nil t sourceInfer)
    (generatedStep :
      GeneratedUnaryOpenIotaStep pilot t nfT)
    (targetAtSourceInfer :
      HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer)
    (targetTyped :
      HasTypeDecl (envOfSpecs specs) .nil nfT targetInfer)
    (targetInferAgrees :
      HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer →
        ConvDecl (envOfSpecs specs) sourceInfer targetInfer) :
    DIndGResolvedArtifactTermCorrespondence
      corr term t nfT sourceInfer targetInfer :=
  { contract := contract
    contract_mem := contractMem
    generated_iota_step :=
      .unary_open ⟨pilot, hPilot, generatedStep⟩
    source_infer_typed := sourceTyped
    nf_justification :=
      .direct_generated_iota_preservation targetAtSourceInfer
    target_infer_typed := targetTyped
    target_infer_agrees := targetInferAgrees }

/-- Resolved generated-iota readout: closed steps use declaration-level subject
reduction; unary-open resolved steps use the directly checked target typing. -/
theorem source_infer_preserved_by_resolved_nf {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGArtifactCorrespondence gate sig specs contracts)
    {term : ArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (termCorr :
      DIndGResolvedArtifactTermCorrespondence
        corr term t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs specs) .nil nfT sourceInfer := by
  cases termCorr.nf_justification with
  | decl_reduction hred =>
      exact DIndGAdmitted.sr_ok_via_artifact_gate
        corr.toAdmitted
        { source_typed := termCorr.source_infer_typed
          normalizes := hred }
  | direct_generated_iota_preservation htyped =>
      exact htyped

/-- Resolved `infer`/`nf` convertibility readout. The source inferred type is
preserved by the resolved frontier, then compared with the artifact's target
`infer` readout by the local readout-agreement obligation. -/
theorem infer_nf_convertible_by_resolved_artifact_readout
    {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGArtifactCorrespondence gate sig specs contracts)
    {term : ArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (termCorr :
      DIndGResolvedArtifactTermCorrespondence
        corr term t nfT sourceInfer targetInfer) :
    ConvDecl (envOfSpecs specs) sourceInfer targetInfer :=
  termCorr.target_infer_agrees
    (source_infer_preserved_by_resolved_nf corr termCorr)

/-- Exposed-gate form for the resolved generated-iota frontier. This is the
closest current Lean statement to the artifact theorem: the remaining work is
deriving the readout records from the executable artifact, not proving a new
subject-reduction theorem for each witness. -/
theorem infer_nf_convertible_of_sig_admitted_with_elims_resolved
    {ArtifactSig ArtifactTerm : Type}
    {gate : DIndGArtifactGate ArtifactSig}
    {sig : ArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (gateSucceeds : gate.sigAdmittedWithElims sig)
    (readout :
      DIndGArtifactMetatheoryReadout gate sig specs contracts)
    {term : ArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (termCorr :
      DIndGResolvedArtifactTermCorrespondence
        (DIndGArtifactCorrespondence.ofGateAndReadout
          gateSucceeds readout)
        term t nfT sourceInfer targetInfer) :
    ConvDecl (envOfSpecs specs) sourceInfer targetInfer :=
  infer_nf_convertible_by_resolved_artifact_readout
    (DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds readout)
    termCorr

end DIndGResolvedArtifactTermCorrespondence

/-- Sort constants used by the raw DIndG artifact syntax. -/
inductive DIndGArtifactSort where
  | type
  | kind
deriving DecidableEq, Repr

/-- Raw term syntax needed to name the DIndG artifact's signatures and
generated-iota witnesses. This is data for the bridge, not a Lean evaluator for
the artifact. -/
inductive DIndGArtifactTerm where
  | var (index : Nat)
  | srt (sort : DIndGArtifactSort)
  | con (name : DeclName)
  | defn (name : DeclName)
  | pi (domain body : DIndGArtifactTerm)
  | lam (domain body : DIndGArtifactTerm)
  | app (fn arg : DIndGArtifactTerm)
  | indG
      (familyName : DeclName)
      (params : List DIndGArtifactTerm)
      (motive : DIndGArtifactTerm)
      (cases : List (DeclName × DIndGArtifactTerm))
      (indices : List DIndGArtifactTerm)
      (scrutinee : DIndGArtifactTerm)
  | bad (reason : String)

/-- Readout used when a raw artifact `IndG` term is lowered to the current
Lean generated-recursor representation. The subterm plumbing is intentionally
left to the canonical artifact extractor; this record only pins the family to a
generated-recursor contract so `IndG` cannot translate as arbitrary syntax. -/
structure DIndGArtifactIndGTermReadout
    (nameTranslates : DeclName → DeclName → Prop)
    (n : Nat)
    (familyName : DeclName)
    (_params : List DIndGArtifactTerm)
    (_motive : DIndGArtifactTerm)
    (_cases : List (DeclName × DIndGArtifactTerm))
    (_indices : List DIndGArtifactTerm)
    (_scrutinee : DIndGArtifactTerm)
    (_target : PureTm n) : Type where
  leanFamily :
    DeclName
  contract :
    FamilyRecursorDeclContract
  pilot :
    GeneratedRecursorPilot
  family_translates :
    nameTranslates familyName leanFamily
  contract_family :
    contract.familyName = leanFamily
  pilot_generated :
    generatedRecursorPilot contract = some pilot

/-- Raw runtime artifact terms translated into the Lean declaration calculus.
Most constructors map structurally. `IndG` maps only through an explicit
generated-recursor readout, because the Lean core hosts generated recursors
rather than adding a second raw `IndG` term former. -/
inductive DIndGArtifactTermTranslates
    (nameTranslates : DeclName → DeclName → Prop) :
    (n : Nat) → DIndGArtifactTerm → PureTm n → Prop where
  | var {n index : Nat} (h : index < n) :
      DIndGArtifactTermTranslates nameTranslates n
        (.var index) (.var ⟨index, h⟩)
  | srt_type {n : Nat} :
      DIndGArtifactTermTranslates nameTranslates n
        (.srt .type) .u0
  | srt_kind {n : Nat} :
      DIndGArtifactTermTranslates nameTranslates n
        (.srt .kind) .u1
  | con {n : Nat} {raw lean : DeclName}
      (h : nameTranslates raw lean) :
      DIndGArtifactTermTranslates nameTranslates n
        (.con raw) (.const lean)
  | defn {n : Nat} {raw lean : DeclName}
      (h : nameTranslates raw lean) :
      DIndGArtifactTermTranslates nameTranslates n
        (.defn raw) (.const lean)
  | pi {n : Nat}
      {rawDomain rawBody : DIndGArtifactTerm}
      {domain : PureTm n} {body : PureTm (n + 1)}
      (hDomain :
        DIndGArtifactTermTranslates nameTranslates n rawDomain domain)
      (hBody :
        DIndGArtifactTermTranslates nameTranslates (n + 1) rawBody body) :
      DIndGArtifactTermTranslates nameTranslates n
        (.pi rawDomain rawBody) (.pi domain body)
  | lam {n : Nat}
      {rawDomain rawBody : DIndGArtifactTerm}
      {domain : PureTm n} {body : PureTm (n + 1)}
      (hDomain :
        DIndGArtifactTermTranslates nameTranslates n rawDomain domain)
      (hBody :
        DIndGArtifactTermTranslates nameTranslates (n + 1) rawBody body) :
      DIndGArtifactTermTranslates nameTranslates n
        (.lam rawDomain rawBody) (.lam body)
  | app {n : Nat}
      {rawFn rawArg : DIndGArtifactTerm}
      {fn arg : PureTm n}
      (hFn :
        DIndGArtifactTermTranslates nameTranslates n rawFn fn)
      (hArg :
        DIndGArtifactTermTranslates nameTranslates n rawArg arg) :
      DIndGArtifactTermTranslates nameTranslates n
        (.app rawFn rawArg) (.app fn arg)
  | indG {n : Nat}
      {familyName : DeclName}
      {params : List DIndGArtifactTerm}
      {motive : DIndGArtifactTerm}
      {cases : List (DeclName × DIndGArtifactTerm)}
      {indices : List DIndGArtifactTerm}
      {scrutinee : DIndGArtifactTerm}
      {target : PureTm n}
      (readout :
        DIndGArtifactIndGTermReadout
          nameTranslates n familyName params motive cases indices scrutinee target) :
      DIndGArtifactTermTranslates nameTranslates n
        (.indG familyName params motive cases indices scrutinee) target

abbrev DIndGArtifactTel := List DIndGArtifactTerm
abbrev DIndGArtifactArgs := List DIndGArtifactTerm

/-- Raw generated constructor record matching `GCtor name argTel resultIdx`. -/
structure DIndGArtifactCtor where
  name : DeclName
  argTel : DIndGArtifactTel
  resultIdx : DIndGArtifactArgs

/-- Raw declaration forms mirrored from the runtime artifact:
`DConst`, `DDef`, `DAxiom`, and `DIndG`. -/
inductive DIndGArtifactDecl where
  | dconst (name : DeclName) (type : DIndGArtifactTerm)
  | ddef (name : DeclName) (type body : DIndGArtifactTerm)
  | daxiom (name : DeclName) (type : DIndGArtifactTerm)
  | dindg
      (familyName : DeclName)
      (paramTel indexTel : DIndGArtifactTel)
      (ctors : List DIndGArtifactCtor)

namespace DIndGArtifactDecl

/-- A raw DIndG declaration is a source for a Lean generated-recursor contract
when the bridge's name translation maps the family and every generated iota
obligation back to artifact names. -/
def supportsContract
    (nameTranslates : DeclName → DeclName → Prop)
    (decl : DIndGArtifactDecl)
    (contract : FamilyRecursorDeclContract) : Prop :=
  match decl with
  | .dindg rawFamily _paramTel _indexTel ctors =>
      nameTranslates rawFamily contract.familyName ∧
        (∃ rawRecursorName, nameTranslates rawRecursorName contract.recursorName) ∧
        ∀ pilot,
          generatedRecursorPilot contract = some pilot →
            ∀ obligation, obligation ∈ pilot.obligations →
              ∃ ctor, ctor ∈ ctors ∧ nameTranslates ctor.name obligation.ctorName
  | _ => False

end DIndGArtifactDecl

/-- Raw runtime artifact signature plus the bridge outputs it has been translated
to. The translated outputs are data carried across the bridge; their soundness
is still provided by the canonical Lean packages below. -/
structure DIndGArtifactSig where
  decls : List DIndGArtifactDecl
  nameTranslates : DeclName → DeclName → Prop
  translatedSpecs : List DeclSpec
  translatedContracts : List FamilyRecursorDeclContract

/-- Structured Lean meaning of the raw artifact's `sig-admitted-with-elims`
success.  The executable runtime gate is still outside Lean; the bridge imports
its successful certificate as data at the canonical abstraction layer: checked
declarations, generated eliminators, contract provenance, and the resolved
generated-iota frontier. -/
def DIndGArtifactSigAdmittedWithElims
    (sig : DIndGArtifactSig) : Prop :=
  SignatureWellFormed sig.translatedSpecs ∧
    (∀ contract, contract ∈ sig.translatedContracts →
      ∃ decl, decl ∈ sig.decls ∧
        DIndGArtifactDecl.supportsContract
          sig.nameTranslates decl contract) ∧
    (∀ contract, contract ∈ sig.translatedContracts →
      GeneratedRecursorContractAdmitted contract) ∧
    (∀ contract, contract ∈ sig.translatedContracts →
      GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract)

/-- The raw artifact gate uses the structured admission certificate above,
rather than an opaque Boolean shadow in Lean. -/
def dindgRawArtifactGate : DIndGArtifactGate DIndGArtifactSig :=
  { sigAdmittedWithElims := DIndGArtifactSigAdmittedWithElims }

/-- Runtime-generic handle for the executable artifact's `nf`, `infer`, and
`conv` readouts. This is not a checker: it is the readout interface a runtime
instance must justify.

The intended verified instance is LeaTTa's formal HE semantics
(`Eval.lean`, `EvalSpec.lean`, `SmallStep.lean`, `SmallStepSound.lean`),
discharging these obligations by proof. CeTTa remains a deployment-runtime
instance: applying this theorem to CeTTa requires the separate trusted
correspondence residual `CeTTa <= LeaTTa`, pending the MIK-in-CeTTa bridge. -/
structure DIndGArtifactEvaluator where
  nf :
    DIndGArtifactSig → DIndGArtifactTerm →
      DIndGArtifactTerm → Prop
  infer :
    DIndGArtifactSig → DIndGArtifactTerm →
      DIndGArtifactTerm → Prop
  conv :
    DIndGArtifactSig → DIndGArtifactTerm →
      DIndGArtifactTerm → Prop

/-- Soundness obligations for the executable artifact evaluator after raw
terms have been translated to the Lean declaration calculus. These are the
canonical extractor/evaluator obligations: they interpret observed `infer` and
`conv` readouts, without reimplementing the artifact checker in Lean. -/
structure DIndGArtifactEvaluatorSoundness
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Prop where
  infer_sound :
    ∀ {rawTerm rawType : DIndGArtifactTerm}
      {term type : PureTm 0},
      evaluator.infer sig rawTerm rawType →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm term →
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawType type →
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil term type
  conv_sound :
    ∀ {rawLeft rawRight : DIndGArtifactTerm}
      {left right : PureTm 0},
      evaluator.conv sig rawLeft rawRight →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawLeft left →
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawRight right →
            ConvDecl (envOfSpecs sig.translatedSpecs) left right

/-- Completeness/coherence obligation for the executable artifact `infer`.
If `infer` returns a translated type for a translated raw term, then every
Lean declaration type of that term is convertible to the inferred type.  This
is the algorithmic-infer route to final `infer t` / `infer (nf t)` agreement,
and is intentionally weaker than global declarative type uniqueness. -/
structure DIndGArtifactInferCompleteness
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Prop where
  infer_complete :
    ∀ {rawTerm rawType : DIndGArtifactTerm}
      {term inferredType declaredType : PureTm 0},
      evaluator.infer sig rawTerm rawType →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm term →
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawType inferredType →
            HasTypeDecl
              (envOfSpecs sig.translatedSpecs) .nil term declaredType →
              ConvDecl
                (envOfSpecs sig.translatedSpecs) declaredType inferredType

/-- Lean translation carried by one raw artifact `infer` output. -/
structure DIndGArtifactInferTransportReadout
    (sig : DIndGArtifactSig)
    (rawType : DIndGArtifactTerm) : Type where
  type : PureTm 0
  type_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawType type

/-- Lean generated-iota classification carried by one raw artifact `nf` output. -/
structure DIndGArtifactNFTransportReadout
    (sig : DIndGArtifactSig)
    (rawNf : DIndGArtifactTerm)
    (term sourceInfer : PureTm 0) : Type where
  nfTerm : PureTm 0
  contract : FamilyRecursorDeclContract
  nf_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfTerm
  contract_mem :
    contract ∈ sig.translatedContracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract term nfTerm
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs sig.translatedSpecs) term nfTerm sourceInfer

/-- Transport obligations for the executable artifact readouts.  These are
about moving raw runtime outputs across the existing artifact-to-Lean
translation, not about rechecking the kernel in Lean. -/
structure DIndGArtifactEvaluatorTransport
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  infer_translates :
    ∀ {rawTerm rawType : DIndGArtifactTerm}
      {term : PureTm 0},
      evaluator.infer sig rawTerm rawType →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm term →
          DIndGArtifactInferTransportReadout sig rawType
  nf_generated_iota :
    ∀ {rawTerm rawNf : DIndGArtifactTerm}
      {term sourceInfer : PureTm 0},
      evaluator.nf sig rawTerm rawNf →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm term →
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil term sourceInfer →
            DIndGArtifactNFTransportReadout
              sig rawNf term sourceInfer

namespace DIndGArtifactEvaluator

/-- Artifact-level readout of
`let nft = nf sig t; let a = infer sig [] t; let b = infer sig [] nft; conv sig a b`.
The actual runtime evaluator remains external; this predicate only records the
four observable results the bridge must import. -/
def srOkWithReadouts
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm rawNf rawSourceInfer rawTargetInfer :
      DIndGArtifactTerm) : Prop :=
  evaluator.nf sig rawTerm rawNf ∧
    evaluator.infer sig rawTerm rawSourceInfer ∧
      evaluator.infer sig rawNf rawTargetInfer ∧
        evaluator.conv sig rawSourceInfer rawTargetInfer

/-- Artifact-level `sr-ok` with the intermediate `nf` and `infer` readouts
existentially hidden, matching the kernel predicate's public Boolean shape. -/
def srOk
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm : DIndGArtifactTerm) : Prop :=
  ∃ rawNf rawSourceInfer rawTargetInfer,
    evaluator.srOkWithReadouts
      sig rawTerm rawNf rawSourceInfer rawTargetInfer

end DIndGArtifactEvaluator

/-- Evidence-producing form of artifact `sr-ok`.  The propositional `srOk`
above records that the Boolean check succeeded; this certificate keeps the
intermediate `nf`/`infer`/`conv` readouts available to the Lean bridge. -/
structure DIndGArtifactSROKCert
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm : DIndGArtifactTerm) : Type where
  rawNf : DIndGArtifactTerm
  rawSourceInfer : DIndGArtifactTerm
  rawTargetInfer : DIndGArtifactTerm
  nf_readout :
    evaluator.nf sig rawTerm rawNf
  source_infer_readout :
    evaluator.infer sig rawTerm rawSourceInfer
  target_infer_readout :
    evaluator.infer sig rawNf rawTargetInfer
  conv_readout :
    evaluator.conv sig rawSourceInfer rawTargetInfer

namespace DIndGArtifactSROKCert

theorem to_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm) :
    evaluator.srOk sig rawTerm :=
  ⟨cert.rawNf, cert.rawSourceInfer, cert.rawTargetInfer,
    cert.nf_readout, cert.source_infer_readout,
    cert.target_infer_readout, cert.conv_readout⟩

end DIndGArtifactSROKCert

/-- Data-facing Lean mirror of the kernel artifact's
`SRCoreReadout rawNf rawSourceInfer rawTargetInfer True`.
Unlike the public Boolean `srOk`, this record fixes the exact executable
transcript that Lean must lower. -/
structure DIndGArtifactSRCoreReadoutCert
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm : DIndGArtifactTerm) : Type where
  rawNf : DIndGArtifactTerm
  rawSourceInfer : DIndGArtifactTerm
  rawTargetInfer : DIndGArtifactTerm
  nf_readout :
    evaluator.nf sig rawTerm rawNf
  source_infer_readout :
    evaluator.infer sig rawTerm rawSourceInfer
  target_infer_readout :
    evaluator.infer sig rawNf rawTargetInfer
  conv_success :
    evaluator.conv sig rawSourceInfer rawTargetInfer

namespace DIndGArtifactSRCoreReadoutCert

def toSROKCert
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm) :
    DIndGArtifactSROKCert evaluator sig rawTerm :=
  { rawNf := cert.rawNf
    rawSourceInfer := cert.rawSourceInfer
    rawTargetInfer := cert.rawTargetInfer
    nf_readout := cert.nf_readout
    source_infer_readout := cert.source_infer_readout
    target_infer_readout := cert.target_infer_readout
    conv_readout := cert.conv_success }

theorem to_sr_ok_with_readouts
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm) :
    evaluator.srOkWithReadouts
      sig rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer :=
  ⟨cert.nf_readout, cert.source_infer_readout,
    cert.target_infer_readout, cert.conv_success⟩

theorem to_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm) :
    evaluator.srOk sig rawTerm :=
  cert.toSROKCert.to_sr_ok

theorem nonempty_iff_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm} :
    Nonempty (DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm) ↔
      evaluator.srOk sig rawTerm :=
by
  constructor
  · rintro ⟨cert⟩
    exact cert.to_sr_ok
  · intro srOk
    rcases srOk with
      ⟨rawNf, rawSourceInfer, rawTargetInfer,
        nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
    exact
      ⟨{ rawNf := rawNf
         rawSourceInfer := rawSourceInfer
         rawTargetInfer := rawTargetInfer
         nf_readout := nfReadout
         source_infer_readout := sourceInferReadout
         target_infer_readout := targetInferReadout
         conv_success := convReadout }⟩

end DIndGArtifactSRCoreReadoutCert

/-- Evidence-producing form of the normalization/inference observation inside
artifact `sr-ok`, without the final `conv` readout.  This is the SR core: the
real artifact observed `nf sig t`, `infer sig [] t`, and
`infer sig [] (nf sig t)`. -/
structure DIndGArtifactNFInferCert
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm : DIndGArtifactTerm) : Type where
  rawNf : DIndGArtifactTerm
  rawSourceInfer : DIndGArtifactTerm
  rawTargetInfer : DIndGArtifactTerm
  nf_readout :
    evaluator.nf sig rawTerm rawNf
  source_infer_readout :
    evaluator.infer sig rawTerm rawSourceInfer
  target_infer_readout :
    evaluator.infer sig rawNf rawTargetInfer

namespace DIndGArtifactNFInferCert

def ofSROKCert
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm) :
    DIndGArtifactNFInferCert evaluator sig rawTerm :=
  { rawNf := cert.rawNf
    rawSourceInfer := cert.rawSourceInfer
    rawTargetInfer := cert.rawTargetInfer
    nf_readout := cert.nf_readout
    source_infer_readout := cert.source_infer_readout
    target_infer_readout := cert.target_infer_readout }

/-- Local coherence obligation for the target `infer` readout in one
observation transcript.  This is deliberately per-certificate: the raw artifact
language carries annotations that the Lean core erases for lambdas, so the
universal theorem should not require global declaration type uniqueness or
global infer uniqueness for every translated term. -/
structure TargetInferCoherence
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactNFInferCert evaluator sig rawTerm) : Prop where
  target_infer_agrees :
    ∀ {nfT sourceInfer targetInfer : PureTm 0},
      DIndGArtifactTermTranslates sig.nameTranslates 0
        cert.rawNf nfT →
      DIndGArtifactTermTranslates sig.nameTranslates 0
        cert.rawSourceInfer sourceInfer →
      DIndGArtifactTermTranslates sig.nameTranslates 0
        cert.rawTargetInfer targetInfer →
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer →
      ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer

/-- Global algorithmic-`infer` completeness is a sufficient way to obtain the
local target-readout coherence needed by the generated-iota SR theorem. -/
def TargetInferCoherence.ofInferCompleteness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactNFInferCert evaluator sig rawTerm)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig) :
    TargetInferCoherence cert :=
  { target_infer_agrees := by
      intro nfT sourceInfer targetInfer
        hNfTranslates _hSourceTranslates hTargetTranslates hPreserved
      exact inferComplete.infer_complete
        cert.target_infer_readout
        hNfTranslates
        hTargetTranslates
        hPreserved }

end DIndGArtifactNFInferCert

namespace DIndGArtifactSROKCert

/-- Soundness of the artifact's final `conv` readout is another way to discharge
the local target-`infer` coherence obligation for the conv-free SR core.  The
main preservation theorem does not inspect `conv`; this adapter is only for
callers that already have an evidence-producing `sr-ok` certificate. -/
def targetInferCoherenceOfConvSoundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig) :
    DIndGArtifactNFInferCert.TargetInferCoherence
      (DIndGArtifactNFInferCert.ofSROKCert cert) :=
  { target_infer_agrees := by
      intro nfT sourceInfer targetInfer
        _hNfTranslates hSourceTranslates hTargetTranslates _hPreserved
      exact evaluatorSound.conv_sound
        cert.conv_readout
        hSourceTranslates
        hTargetTranslates }

end DIndGArtifactSROKCert

/-- Minimal raw artifact `sr-ok` readout: the executable observations, their
Lean translations, and the resolved generated-iota justification for `nf`.
Unlike `DIndGArtifactSRReadout`, this record does not carry an arbitrary
target-`infer` agreement function; the agreement is derived from evaluator
soundness of the observed `conv` readout. -/
structure DIndGArtifactSRKernelReadout
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm)
    (t nfT sourceInfer targetInfer : PureTm 0) : Type where
  nf_readout :
    evaluator.nf sig rawTerm rawNf
  source_infer_readout :
    evaluator.infer sig rawTerm rawSourceInfer
  target_infer_readout :
    evaluator.infer sig rawNf rawTargetInfer
  conv_readout :
    evaluator.conv sig rawSourceInfer rawTargetInfer
  term_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t
  nf_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT
  source_infer_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawSourceInfer sourceInfer
  target_infer_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTargetInfer targetInfer
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ sig.translatedContracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract t nfT
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs sig.translatedSpecs) t nfT sourceInfer

/-- Observation-only artifact readout for the preservation half of `sr-ok`.
This deliberately excludes the final artifact `conv` result: it records only
the observed `nf`, the two `infer` observations, their Lean translations, and
the generated-iota classification of the observed normal form. -/
structure DIndGArtifactNFInferReadout
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm)
    (t nfT sourceInfer targetInfer : PureTm 0) : Type where
  nf_readout :
    evaluator.nf sig rawTerm rawNf
  source_infer_readout :
    evaluator.infer sig rawTerm rawSourceInfer
  target_infer_readout :
    evaluator.infer sig rawNf rawTargetInfer
  term_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t
  nf_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT
  source_infer_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawSourceInfer sourceInfer
  target_infer_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTargetInfer targetInfer
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ sig.translatedContracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract t nfT
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs sig.translatedSpecs) t nfT sourceInfer

namespace DIndGArtifactNFInferReadout

def ofSRKernelReadout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    DIndGArtifactNFInferReadout evaluator sig
      rawTerm rawNf rawSourceInfer rawTargetInfer
      t nfT sourceInfer targetInfer :=
  { nf_readout := readout.nf_readout
    source_infer_readout := readout.source_infer_readout
    target_infer_readout := readout.target_infer_readout
    term_translates := readout.term_translates
    nf_translates := readout.nf_translates
    source_infer_translates := readout.source_infer_translates
    target_infer_translates := readout.target_infer_translates
    contract := readout.contract
    contract_mem := readout.contract_mem
    generated_iota_step := readout.generated_iota_step
    nf_justification := readout.nf_justification }

/-- Preservation from observation-only data.  The artifact `conv` result is not
used here; the only typing input is the Lean interpretation of the source
`infer` readout. -/
theorem source_infer_preserved_of_source_typing
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGArtifactCorrespondence
        dindgRawArtifactGate sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactNFInferReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer)
    (sourceTyped :
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer := by
  cases readout.nf_justification with
  | decl_reduction hred =>
      exact DIndGAdmitted.sr_ok_via_artifact_gate
        corr.toAdmitted
        { source_typed := sourceTyped
          normalizes := hred }
  | direct_generated_iota_preservation htyped =>
      exact htyped

end DIndGArtifactNFInferReadout

namespace DIndGArtifactNFInferCert

/-- Lower the conv-free executable observation into the Lean readout consumed
by the subject-reduction theorem.  The final artifact `conv` result is not
needed for this step: source typing comes from the observed source `infer`, and
the generated-iota classification comes from transporting the observed `nf`. -/
def to_nf_infer_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert : DIndGArtifactNFInferCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    Sigma (fun nfT : PureTm 0 =>
    Sigma (fun sourceInfer : PureTm 0 =>
    Sigma (fun targetInfer : PureTm 0 =>
    Sigma (fun _readout :
      DIndGArtifactNFInferReadout evaluator sig
        rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer
        t nfT sourceInfer targetInfer =>
      PLift (HasTypeDecl
        (envOfSpecs sig.translatedSpecs) .nil t sourceInfer))))) := by
  let sourceReadout :=
    transport.infer_translates
      cert.source_infer_readout termTranslates
  have sourceTyped :
      HasTypeDecl
        (envOfSpecs sig.translatedSpecs) .nil
        t sourceReadout.type :=
    evaluatorSound.infer_sound
      cert.source_infer_readout
      termTranslates
      sourceReadout.type_translates
  let nfReadout :=
    transport.nf_generated_iota
      cert.nf_readout termTranslates sourceTyped
  let targetReadout :=
    transport.infer_translates
      cert.target_infer_readout
      nfReadout.nf_translates
  exact
    ⟨nfReadout.nfTerm, sourceReadout.type, targetReadout.type,
      { nf_readout := cert.nf_readout
        source_infer_readout := cert.source_infer_readout
        target_infer_readout := cert.target_infer_readout
        term_translates := termTranslates
        nf_translates := nfReadout.nf_translates
        source_infer_translates := sourceReadout.type_translates
        target_infer_translates := targetReadout.type_translates
        contract := nfReadout.contract
        contract_mem := nfReadout.contract_mem
        generated_iota_step := nfReadout.generated_iota_step
        nf_justification := nfReadout.nf_justification },
      PLift.up sourceTyped⟩

end DIndGArtifactNFInferCert

namespace DIndGArtifactSRKernelReadout

theorem raw_sr_ok_with_readouts
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOkWithReadouts
      sig rawTerm rawNf rawSourceInfer rawTargetInfer :=
  ⟨readout.nf_readout, readout.source_infer_readout,
    readout.target_infer_readout, readout.conv_readout⟩

theorem raw_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm :=
  ⟨rawNf, rawSourceInfer, rawTargetInfer,
    readout.raw_sr_ok_with_readouts⟩

theorem source_infer_typed
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer :=
  sound.infer_sound
    readout.source_infer_readout
    readout.term_translates
    readout.source_infer_translates

theorem target_infer_typed
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer :=
  sound.infer_sound
    readout.target_infer_readout
    readout.nf_translates
    readout.target_infer_translates

theorem conv_sound
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  sound.conv_sound
    readout.conv_readout
    readout.source_infer_translates
    readout.target_infer_translates

/-- Local soundness for one executable `sr-ok` readout.  This is the exact
per-run Lean interpretation needed from the artifact extractor: the observed
source `infer`, target `infer`, and final `conv` readouts have already been
translated into the declaration calculus. -/
structure LocalSoundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (_readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) : Prop where
  source_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer
  target_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer
  inferred_types_convertible :
    ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer

def localSoundnessOfEvaluatorSoundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (sound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    LocalSoundness readout :=
  { source_infer_typed := readout.source_infer_typed sound
    target_infer_typed := readout.target_infer_typed sound
    inferred_types_convertible := readout.conv_sound sound }

/-- Subject-reduction half of the artifact theorem from the minimal readout:
the source inferred type is preserved by the artifact `nf` target. -/
theorem source_infer_preserved_of_local_soundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGArtifactCorrespondence
        dindgRawArtifactGate sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer)
    (localSound : LocalSoundness readout) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer := by
  cases readout.nf_justification with
  | decl_reduction hred =>
      exact DIndGAdmitted.sr_ok_via_artifact_gate
        corr.toAdmitted
        { source_typed := localSound.source_infer_typed
          normalizes := hred }
  | direct_generated_iota_preservation htyped =>
      exact htyped

theorem source_infer_preserved
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGArtifactCorrespondence
        dindgRawArtifactGate sig sig.translatedSpecs sig.translatedContracts)
    (sound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer :=
  source_infer_preserved_of_local_soundness corr readout
    (localSoundnessOfEvaluatorSoundness sound readout)

/-- Universal artifact theorem shape over the raw DIndG artifact: under
`sig-admitted-with-elims`, evaluator soundness, and a generated-iota readout,
the runtime `sr-ok` is present, Lean proves subject reduction for `nf`, and the
two artifact `infer` readouts translate to declaration-side convertible types. -/
theorem sr_ok_justified_of_sig_admitted_local
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer)
    (localSound : LocalSoundness readout) :
    evaluator.srOk sig rawTerm ∧
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
            ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  let corr :=
    DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds metatheory
  ⟨readout.raw_sr_ok,
    localSound.source_infer_typed,
    source_infer_preserved_of_local_soundness corr readout localSound,
    localSound.target_infer_typed,
    localSound.inferred_types_convertible⟩

theorem sr_ok_justified_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (sound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm ∧
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
            ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  sr_ok_justified_of_sig_admitted_local
    gateSucceeds metatheory readout
    (localSoundnessOfEvaluatorSoundness sound readout)

end DIndGArtifactSRKernelReadout

namespace DIndGArtifactSROKCert

/-- Build the Lean-facing kernel readout from an evidence-producing `sr-ok`
certificate and evaluator transport. -/
def to_kernel_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    Sigma (fun nfT : PureTm 0 =>
    Sigma (fun sourceInfer : PureTm 0 =>
    Sigma (fun targetInfer : PureTm 0 =>
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer
        t nfT sourceInfer targetInfer))) := by
  let sourceReadout :=
    transport.infer_translates
      cert.source_infer_readout termTranslates
  have sourceTyped :
      HasTypeDecl
        (envOfSpecs sig.translatedSpecs) .nil
        t sourceReadout.type :=
    evaluatorSound.infer_sound
      cert.source_infer_readout
      termTranslates
      sourceReadout.type_translates
  let nfReadout :=
    transport.nf_generated_iota
      cert.nf_readout termTranslates sourceTyped
  let targetReadout :=
    transport.infer_translates
      cert.target_infer_readout
      nfReadout.nf_translates
  exact
    ⟨nfReadout.nfTerm, sourceReadout.type, targetReadout.type,
      { nf_readout := cert.nf_readout
        source_infer_readout := cert.source_infer_readout
        target_infer_readout := cert.target_infer_readout
        conv_readout := cert.conv_readout
        term_translates := termTranslates
        nf_translates := nfReadout.nf_translates
        source_infer_translates := sourceReadout.type_translates
        target_infer_translates := targetReadout.type_translates
        contract := nfReadout.contract
        contract_mem := nfReadout.contract_mem
        generated_iota_step := nfReadout.generated_iota_step
        nf_justification := nfReadout.nf_justification }⟩

/-- Public certificate theorem: an evidence-producing runtime `sr-ok` certificate
plus evaluator transport is enough to enter the universal kernel theorem. -/
theorem justified_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
              ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer := by
  rcases to_kernel_readout
      evaluatorSound transport cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, readout⟩
  exact
    ⟨nfT, sourceInfer, targetInfer,
      DIndGArtifactSRKernelReadout.sr_ok_justified_of_sig_admitted
        gateSucceeds metatheory evaluatorSound readout⟩

end DIndGArtifactSROKCert

/-- Certificate-indexed extraction from an evidence-producing `sr-ok`
certificate.  The extracted Lean readout must use the exact `nf`/`infer`/`conv`
observations carried by the certificate, not a fresh choice from the public
existential. -/
structure DIndGArtifactSROKExtractionSoundness
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  kernel_readout_of_cert :
    ∀ {rawTerm : DIndGArtifactTerm} {t : PureTm 0},
      (cert : DIndGArtifactSROKCert evaluator sig rawTerm) →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t →
          Sigma (fun nfT : PureTm 0 =>
          Sigma (fun sourceInfer : PureTm 0 =>
          Sigma (fun targetInfer : PureTm 0 =>
            DIndGArtifactSRKernelReadout evaluator sig
              rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer
              t nfT sourceInfer targetInfer)))

namespace DIndGArtifactSROKExtractionSoundness

def ofEvaluatorSoundnessTransport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig) :
    DIndGArtifactSROKExtractionSoundness evaluator sig where
  kernel_readout_of_cert := by
    intro rawTerm t cert termTranslates
    exact
      DIndGArtifactSROKCert.to_kernel_readout
        evaluatorSound transport cert termTranslates

/-- Certificate-indexed theorem through the exact extractor: an
evidence-producing `sr-ok` certificate may expose typed Lean data, because the
intermediate artifact observations are explicit in the certificate. -/
theorem cert_justified_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
              ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer := by
  rcases certExtraction.kernel_readout_of_cert
      cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, readout⟩
  exact
    ⟨nfT, sourceInfer, targetInfer,
      DIndGArtifactSRKernelReadout.sr_ok_justified_of_sig_admitted
        gateSucceeds metatheory evaluatorSound readout⟩

/-- Public theorem through the certificate-indexed extractor.  This is the
safer public `sr-ok` route: Lean may open the propositional `sr-ok`, but the
lowering obligation is still stated on the exact certificate witnesses it
opened. -/
theorem public_sr_ok_justified_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let cert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  rcases cert_justified_of_sig_admitted
      gateSucceeds metatheory evaluatorSound
      certExtraction cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, justified⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, justified⟩

end DIndGArtifactSROKExtractionSoundness

/-- Exact extraction contract for the kernel artifact's public `sr-ok`
equation.  This is the remaining non-Lean seam in its final shape: from the
real artifact `sr-ok` run and the source-term translation, produce the observed
`nf`/`infer`/`conv` transcript, its Lean translations, the generated-iota
classification of `nf`, and the local declaration-side soundness of the
observed `infer`/`conv` readouts. -/
structure DIndGArtifactSRKernelExtraction
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Prop where
  kernel_readout_of_sr_ok :
    ∀ {rawTerm : DIndGArtifactTerm} {t : PureTm 0},
      evaluator.srOk sig rawTerm →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t →
          ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
          ∃ nfT sourceInfer targetInfer : PureTm 0,
          ∃ readout :
            DIndGArtifactSRKernelReadout evaluator sig
              rawTerm rawNf rawSourceInfer rawTargetInfer
              t nfT sourceInfer targetInfer,
            DIndGArtifactSRKernelReadout.LocalSoundness readout

namespace DIndGArtifactSRKernelExtraction

theorem ofEvaluatorSoundnessTransport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig) :
    DIndGArtifactSRKernelExtraction evaluator sig := by
  constructor
  intro rawTerm t srOk termTranslates
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let cert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  rcases DIndGArtifactSROKCert.to_kernel_readout
      evaluatorSound transport cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, readout⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, readout,
      DIndGArtifactSRKernelReadout.localSoundnessOfEvaluatorSoundness
        evaluatorSound readout⟩

end DIndGArtifactSRKernelExtraction

/-- Raw artifact `sr-ok` readout, matching the kernel definition
`let nft = nf sig t; let a = infer sig [] t; let b = infer sig [] nft; conv sig a b`.
It also carries the Lean translations and resolved generated-iota evidence
needed to enter the declaration-side theorem. -/
structure DIndGArtifactSRReadout
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm)
    (t nfT sourceInfer targetInfer : PureTm 0) : Type where
  nf_readout :
    evaluator.nf sig rawTerm rawNf
  source_infer_readout :
    evaluator.infer sig rawTerm rawSourceInfer
  target_infer_readout :
    evaluator.infer sig rawNf rawTargetInfer
  conv_readout :
    evaluator.conv sig rawSourceInfer rawTargetInfer
  term_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t
  nf_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT
  source_infer_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawSourceInfer sourceInfer
  target_infer_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTargetInfer targetInfer
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ sig.translatedContracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract t nfT
  source_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs sig.translatedSpecs) t nfT sourceInfer
  target_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer
  target_infer_agrees :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer →
      ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer

namespace DIndGArtifactSRReadout

theorem raw_sr_ok_with_readouts
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOkWithReadouts
      sig rawTerm rawNf rawSourceInfer rawTargetInfer :=
  ⟨readout.nf_readout, readout.source_infer_readout,
    readout.target_infer_readout, readout.conv_readout⟩

theorem raw_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm :=
  ⟨rawNf, rawSourceInfer, rawTargetInfer,
    readout.raw_sr_ok_with_readouts⟩

def toResolvedTermCorrespondence
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGArtifactCorrespondence
        dindgRawArtifactGate sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    DIndGResolvedArtifactTermCorrespondence
      corr rawTerm t nfT sourceInfer targetInfer :=
  { contract := readout.contract
    contract_mem := readout.contract_mem
    generated_iota_step := readout.generated_iota_step
    source_infer_typed := readout.source_infer_typed
    nf_justification := readout.nf_justification
    target_infer_typed := readout.target_infer_typed
    target_infer_agrees := readout.target_infer_agrees }

/-- Raw artifact-level preservation half of `sr-ok`: independently of the
artifact's final target-`infer` agreement readout, the Lean declaration-side
subject-reduction theorem proves that `nf` preserves the source inferred type. -/
theorem source_infer_preserved_of_raw_sr_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGArtifactCorrespondence
        dindgRawArtifactGate sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer :=
  DIndGResolvedArtifactTermCorrespondence.source_infer_preserved_by_resolved_nf
    corr
    (readout.toResolvedTermCorrespondence corr)

/-- Raw artifact-level `sr-ok` theorem shape: once the real artifact evaluator
has supplied `nf`, `infer`, and `conv` readouts for a raw generated-iota term,
the Lean declaration-side theorem justifies the two inferred types as
convertible. -/
theorem infer_nf_convertible_of_raw_sr_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGArtifactCorrespondence
        dindgRawArtifactGate sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGResolvedArtifactTermCorrespondence.infer_nf_convertible_by_resolved_artifact_readout
    corr
    (readout.toResolvedTermCorrespondence corr)

/-- Exposed-gate raw theorem shape. This is parameterized over the raw artifact
signature and the executable evaluator readout, so the remaining obligation is
precisely to derive this readout from the runtime's `sig-admitted-with-elims`/`sr-ok`
execution rather than from bounded examples. -/
theorem infer_nf_convertible_of_raw_sig_admitted_sr_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  infer_nf_convertible_of_raw_sr_readout
    (DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds metatheory)
    readout

/-- Exposed-gate raw preservation theorem. This is the subject-reduction part
of `sr-ok`; it does not use the final target-`infer` agreement obligation. -/
theorem source_infer_preserved_of_raw_sig_admitted_sr_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer :=
  source_infer_preserved_of_raw_sr_readout
    (DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds metatheory)
    readout

/-- Public artifact theorem shape: the runtime `sr-ok` readout is present, and
Lean justifies its two inferred types as declaration-side convertible. -/
theorem raw_sr_ok_and_lean_convertible_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm ∧
      ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  ⟨readout.raw_sr_ok,
    infer_nf_convertible_of_raw_sig_admitted_sr_readout
      gateSucceeds metatheory readout⟩

/-- Compatibility theorem for the older full typed generated-iota readout.
Current artifact-facing entry points use the stricter `SRKernelReadout` plus
`LocalSoundness`; this lemma remains a bridge for earlier correspondence code
that still carries the richer historical readout record. -/
theorem typed_generated_iota_sr_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm ∧
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
            ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  let corr :=
    DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds metatheory
  ⟨readout.raw_sr_ok,
    readout.source_infer_typed,
    source_infer_preserved_of_raw_sr_readout corr readout,
    readout.target_infer_typed,
    infer_nf_convertible_of_raw_sr_readout corr readout⟩

end DIndGArtifactSRReadout

/-- Typed transcript of the executable artifact path for one generated-iota
`sr-ok` observation.  This is the precise seam the runtime-generic lowering path
must supply: the observed `nf`/`infer`/`conv` certificate, the translations of
those raw readouts, and the generated-iota classification of the observed
normal form. -/
structure DIndGArtifactGeneratedIotaExecution
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm : DIndGArtifactTerm)
    (t : PureTm 0) : Type where
  cert :
    DIndGArtifactSROKCert evaluator sig rawTerm
  term_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t
  nfTerm :
    PureTm 0
  sourceInfer :
    PureTm 0
  targetInfer :
    PureTm 0
  nf_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfTerm
  source_infer_translates :
    DIndGArtifactTermTranslates
      sig.nameTranslates 0 cert.rawSourceInfer sourceInfer
  target_infer_translates :
    DIndGArtifactTermTranslates
      sig.nameTranslates 0 cert.rawTargetInfer targetInfer
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ sig.translatedContracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract t nfTerm
  source_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs sig.translatedSpecs) t nfTerm sourceInfer
  target_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfTerm targetInfer
  inferred_types_convertible :
    ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer

namespace DIndGArtifactGeneratedIotaExecution

def to_sr_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (execution :
      DIndGArtifactGeneratedIotaExecution evaluator sig rawTerm t) :
    DIndGArtifactSRReadout evaluator sig
      rawTerm execution.cert.rawNf
      execution.cert.rawSourceInfer execution.cert.rawTargetInfer
      t execution.nfTerm execution.sourceInfer execution.targetInfer :=
  { nf_readout := execution.cert.nf_readout
    source_infer_readout := execution.cert.source_infer_readout
    target_infer_readout := execution.cert.target_infer_readout
    conv_readout := execution.cert.conv_readout
    term_translates := execution.term_translates
    nf_translates := execution.nf_translates
    source_infer_translates := execution.source_infer_translates
    target_infer_translates := execution.target_infer_translates
    contract := execution.contract
    contract_mem := execution.contract_mem
    generated_iota_step := execution.generated_iota_step
    source_infer_typed := execution.source_infer_typed
    nf_justification := execution.nf_justification
    target_infer_typed := execution.target_infer_typed
    target_infer_agrees := fun _ => execution.inferred_types_convertible }

def to_kernel_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (execution :
      DIndGArtifactGeneratedIotaExecution evaluator sig rawTerm t) :
    DIndGArtifactSRKernelReadout evaluator sig
      rawTerm execution.cert.rawNf
      execution.cert.rawSourceInfer execution.cert.rawTargetInfer
      t execution.nfTerm execution.sourceInfer execution.targetInfer :=
  { nf_readout := execution.cert.nf_readout
    source_infer_readout := execution.cert.source_infer_readout
    target_infer_readout := execution.cert.target_infer_readout
    conv_readout := execution.cert.conv_readout
    term_translates := execution.term_translates
    nf_translates := execution.nf_translates
    source_infer_translates := execution.source_infer_translates
    target_infer_translates := execution.target_infer_translates
    contract := execution.contract
    contract_mem := execution.contract_mem
    generated_iota_step := execution.generated_iota_step
    nf_justification := execution.nf_justification }

def to_local_soundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (execution :
      DIndGArtifactGeneratedIotaExecution evaluator sig rawTerm t) :
    DIndGArtifactSRKernelReadout.LocalSoundness
      execution.to_kernel_readout :=
  { source_infer_typed := execution.source_infer_typed
    target_infer_typed := execution.target_infer_typed
    inferred_types_convertible := execution.inferred_types_convertible }

/-- Artifact execution theorem in the exact `sr-ok` transcript shape: once the
real lowering path has produced a typed generated-iota execution transcript,
the declaration-side SR theorem justifies the observable `infer`/`nf` result.
The proof enters through the stricter kernel readout plus local soundness, so it
does not rely on the older arbitrary target-`infer` agreement callback. -/
theorem typed_generated_iota_sr_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (execution :
      DIndGArtifactGeneratedIotaExecution evaluator sig rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  ⟨execution.cert.rawNf,
    execution.cert.rawSourceInfer,
    execution.cert.rawTargetInfer,
    execution.nfTerm,
    execution.sourceInfer,
    execution.targetInfer,
    DIndGArtifactSRKernelReadout.sr_ok_justified_of_sig_admitted_local
      gateSucceeds metatheory
      execution.to_kernel_readout execution.to_local_soundness⟩

end DIndGArtifactGeneratedIotaExecution

/-- Certificate-indexed typed transcript of one generated-iota `sr-ok` run.
Unlike `DIndGArtifactGeneratedIotaExecution`, the observed
`nf`/`infer`/`conv` certificate is an index of the record, so an executable
lowering cannot replace the hidden witnesses opened from `sr-ok`. -/
structure DIndGArtifactGeneratedIotaExecutionForCert
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm : DIndGArtifactTerm)
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm)
    (t : PureTm 0) : Type where
  term_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t
  nfTerm :
    PureTm 0
  sourceInfer :
    PureTm 0
  targetInfer :
    PureTm 0
  nf_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfTerm
  source_infer_translates :
    DIndGArtifactTermTranslates
      sig.nameTranslates 0 cert.rawSourceInfer sourceInfer
  target_infer_translates :
    DIndGArtifactTermTranslates
      sig.nameTranslates 0 cert.rawTargetInfer targetInfer
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ sig.translatedContracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract t nfTerm
  source_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs sig.translatedSpecs) t nfTerm sourceInfer
  target_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfTerm targetInfer
  inferred_types_convertible :
    ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer

namespace DIndGArtifactGeneratedIotaExecutionForCert

def to_kernel_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {cert : DIndGArtifactSROKCert evaluator sig rawTerm}
    {t : PureTm 0}
    (execution :
      DIndGArtifactGeneratedIotaExecutionForCert
        evaluator sig rawTerm cert t) :
    DIndGArtifactSRKernelReadout evaluator sig
      rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer
      t execution.nfTerm execution.sourceInfer execution.targetInfer :=
  { nf_readout := cert.nf_readout
    source_infer_readout := cert.source_infer_readout
    target_infer_readout := cert.target_infer_readout
    conv_readout := cert.conv_readout
    term_translates := execution.term_translates
    nf_translates := execution.nf_translates
    source_infer_translates := execution.source_infer_translates
    target_infer_translates := execution.target_infer_translates
    contract := execution.contract
    contract_mem := execution.contract_mem
    generated_iota_step := execution.generated_iota_step
    nf_justification := execution.nf_justification }

def to_local_soundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {cert : DIndGArtifactSROKCert evaluator sig rawTerm}
    {t : PureTm 0}
    (execution :
      DIndGArtifactGeneratedIotaExecutionForCert
        evaluator sig rawTerm cert t) :
    DIndGArtifactSRKernelReadout.LocalSoundness
      execution.to_kernel_readout :=
  { source_infer_typed := execution.source_infer_typed
    target_infer_typed := execution.target_infer_typed
    inferred_types_convertible := execution.inferred_types_convertible }

theorem typed_generated_iota_sr_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {cert : DIndGArtifactSROKCert evaluator sig rawTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (execution :
      DIndGArtifactGeneratedIotaExecutionForCert
        evaluator sig rawTerm cert t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases DIndGArtifactSRKernelReadout.sr_ok_justified_of_sig_admitted_local
      gateSucceeds metatheory
      execution.to_kernel_readout execution.to_local_soundness with
    ⟨hSrOk, hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨execution.nfTerm,
      execution.sourceInfer,
      execution.targetInfer,
      execution.contract,
      execution.nf_translates,
      execution.source_infer_translates,
      execution.target_infer_translates,
      execution.contract_mem,
      execution.generated_iota_step,
      execution.nf_justification,
      execution.to_kernel_readout.raw_sr_ok_with_readouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

end DIndGArtifactGeneratedIotaExecutionForCert

/-- Certificate-indexed transcript for the conv-free SR core:
`nft = nf sig t; a = infer sig [] t; b = infer sig [] nft`.
The final artifact `conv` readout is intentionally absent; declaration-side
convertibility is obtained later from subject reduction plus local
target-`infer` coherence. -/
structure DIndGArtifactNFInferExecutionForCert
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig)
    (rawTerm : DIndGArtifactTerm)
    (cert : DIndGArtifactNFInferCert evaluator sig rawTerm)
    (t : PureTm 0) : Type where
  term_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t
  nfTerm :
    PureTm 0
  sourceInfer :
    PureTm 0
  targetInfer :
    PureTm 0
  nf_translates :
    DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfTerm
  source_infer_translates :
    DIndGArtifactTermTranslates
      sig.nameTranslates 0 cert.rawSourceInfer sourceInfer
  target_infer_translates :
    DIndGArtifactTermTranslates
      sig.nameTranslates 0 cert.rawTargetInfer targetInfer
  contract :
    FamilyRecursorDeclContract
  contract_mem :
    contract ∈ sig.translatedContracts
  generated_iota_step :
    DIndGArtifactResolvedIotaStep contract t nfTerm
  source_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer
  nf_justification :
    DIndGArtifactNFJustification
      (envOfSpecs sig.translatedSpecs) t nfTerm sourceInfer
  target_infer_typed :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfTerm targetInfer

namespace DIndGArtifactNFInferExecutionForCert

def to_nf_infer_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {cert : DIndGArtifactNFInferCert evaluator sig rawTerm}
    {t : PureTm 0}
    (execution :
      DIndGArtifactNFInferExecutionForCert
        evaluator sig rawTerm cert t) :
    DIndGArtifactNFInferReadout evaluator sig
      rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer
      t execution.nfTerm execution.sourceInfer execution.targetInfer :=
  { nf_readout := cert.nf_readout
    source_infer_readout := cert.source_infer_readout
    target_infer_readout := cert.target_infer_readout
    term_translates := execution.term_translates
    nf_translates := execution.nf_translates
    source_infer_translates := execution.source_infer_translates
    target_infer_translates := execution.target_infer_translates
    contract := execution.contract
    contract_mem := execution.contract_mem
    generated_iota_step := execution.generated_iota_step
    nf_justification := execution.nf_justification }

/-- Exact conv-free kernel theorem for one `nf`/`infer` transcript.  Subject
reduction preserves the source inferred type across the observed `nf`; local
target-`infer` coherence then compares that preserved type with the artifact's
target `infer` readout. -/
theorem infer_nf_convertible_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {cert : DIndGArtifactNFInferCert evaluator sig rawTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (execution :
      DIndGArtifactNFInferExecutionForCert
        evaluator sig rawTerm cert t)
    (targetCoherence :
      DIndGArtifactNFInferCert.TargetInferCoherence cert) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  let readout := execution.to_nf_infer_readout
  let corr :=
    DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds metatheory
  have hPreserved :
      HasTypeDecl
        (envOfSpecs sig.translatedSpecs) .nil
        execution.nfTerm execution.sourceInfer :=
    DIndGArtifactNFInferReadout.source_infer_preserved_of_source_typing
      corr readout execution.source_infer_typed
  have hConv :
      ConvDecl
        (envOfSpecs sig.translatedSpecs)
        execution.sourceInfer execution.targetInfer :=
    targetCoherence.target_infer_agrees
      execution.nf_translates
      execution.source_infer_translates
      execution.target_infer_translates
      hPreserved
  exact
    ⟨execution.nfTerm,
      execution.sourceInfer,
      execution.targetInfer,
      execution.contract,
      execution.nf_translates,
      execution.source_infer_translates,
      execution.target_infer_translates,
      execution.contract_mem,
      execution.generated_iota_step,
      execution.nf_justification,
      cert.nf_readout,
      cert.source_infer_readout,
      cert.target_infer_readout,
      execution.source_infer_typed,
      hPreserved,
      execution.target_infer_typed,
      hConv⟩

end DIndGArtifactNFInferExecutionForCert

/-- Exact lowering contract for the conv-free `nf`/two-`infer` transcript.  It
is the artifact-side obligation needed before the final `conv` readout is
considered. -/
structure DIndGArtifactExactNFInferLowering
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  nf_infer_execution :
    ∀ {rawTerm : DIndGArtifactTerm} {t : PureTm 0},
      (cert : DIndGArtifactNFInferCert evaluator sig rawTerm) →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t →
          DIndGArtifactNFInferExecutionForCert
            evaluator sig rawTerm cert t

namespace DIndGArtifactExactNFInferLowering

def ofEvaluatorSoundnessTransport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig) :
    DIndGArtifactExactNFInferLowering evaluator sig where
  nf_infer_execution := by
    intro rawTerm t cert termTranslates
    let sourceReadout :=
      transport.infer_translates
        cert.source_infer_readout termTranslates
    have sourceTyped :
        HasTypeDecl
          (envOfSpecs sig.translatedSpecs) .nil
          t sourceReadout.type :=
      evaluatorSound.infer_sound
        cert.source_infer_readout
        termTranslates
        sourceReadout.type_translates
    let nfReadout :=
      transport.nf_generated_iota
        cert.nf_readout termTranslates sourceTyped
    let targetReadout :=
      transport.infer_translates
        cert.target_infer_readout
        nfReadout.nf_translates
    have targetTyped :
        HasTypeDecl
          (envOfSpecs sig.translatedSpecs) .nil
          nfReadout.nfTerm targetReadout.type :=
      evaluatorSound.infer_sound
        cert.target_infer_readout
        nfReadout.nf_translates
        targetReadout.type_translates
    exact
      { term_translates := termTranslates
        nfTerm := nfReadout.nfTerm
        sourceInfer := sourceReadout.type
        targetInfer := targetReadout.type
        nf_translates := nfReadout.nf_translates
        source_infer_translates := sourceReadout.type_translates
        target_infer_translates := targetReadout.type_translates
        contract := nfReadout.contract
        contract_mem := nfReadout.contract_mem
        generated_iota_step := nfReadout.generated_iota_step
        source_infer_typed := sourceTyped
        nf_justification := nfReadout.nf_justification
        target_infer_typed := targetTyped }

theorem infer_nf_convertible_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExactNFInferLowering evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (targetCoherence :
      DIndGArtifactNFInferCert.TargetInferCoherence cert)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGArtifactNFInferExecutionForCert.infer_nf_convertible_of_sig_admitted
    gateSucceeds metatheory
    (lowering.nf_infer_execution cert termTranslates)
    targetCoherence

end DIndGArtifactExactNFInferLowering

/-- Local target-`infer` coherence for every conv-free observation certificate.
This is the preferred bridge obligation for the SR core: after subject
reduction proves the normal form still has the source inferred type, this
contract says the executable target `infer` readout agrees with that preserved
type. -/
structure DIndGArtifactExactTargetInferCoherence
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  target_coherence :
    ∀ {rawTerm : DIndGArtifactTerm},
      (cert : DIndGArtifactNFInferCert evaluator sig rawTerm) →
        DIndGArtifactNFInferCert.TargetInferCoherence cert

namespace DIndGArtifactExactTargetInferCoherence

def ofInferCompleteness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig) :
    DIndGArtifactExactTargetInferCoherence evaluator sig where
  target_coherence := by
    intro rawTerm cert
    exact
      DIndGArtifactNFInferCert.TargetInferCoherence.ofInferCompleteness
        cert inferComplete

end DIndGArtifactExactTargetInferCoherence

/-- Single exact extractor contract for the SR core of the indexed kernel
artifact.  It bundles the two obligations that must come from the live artifact
path: lower the exact `nf`/two-`infer` transcript, and prove local coherence of
the target `infer` readout for that same transcript. -/
structure DIndGArtifactExactSRCoreExtractor
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  nf_infer_lowering :
    DIndGArtifactExactNFInferLowering evaluator sig
  target_coherence :
    DIndGArtifactExactTargetInferCoherence evaluator sig

namespace DIndGArtifactExactSRCoreExtractor

/-- Constructor for the conv-free route: evaluator soundness/transport lowers
the executable observations, while algorithmic-`infer` completeness supplies
the local target-readout coherence. -/
def ofEvaluatorSoundnessTransportInferCompleteness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig) :
    DIndGArtifactExactSRCoreExtractor evaluator sig :=
  { nf_infer_lowering :=
      DIndGArtifactExactNFInferLowering.ofEvaluatorSoundnessTransport
        evaluatorSound transport
    target_coherence :=
      DIndGArtifactExactTargetInferCoherence.ofInferCompleteness
        inferComplete }

end DIndGArtifactExactSRCoreExtractor

/-- Live artifact obligations for the conv-free SR core.  This packages the
three executable-side facts needed to turn observed `nf`/`infer` readouts into
the Lean declaration theorem: soundness of `infer`, transport of executable
readouts to Lean terms, and completeness/coherence of the target `infer`
readout. -/
structure DIndGArtifactLiveSRCoreObligations
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  evaluator_sound :
    DIndGArtifactEvaluatorSoundness evaluator sig
  transport :
    DIndGArtifactEvaluatorTransport evaluator sig
  infer_complete :
    DIndGArtifactInferCompleteness evaluator sig

namespace DIndGArtifactLiveSRCoreObligations

def toExactSRCoreExtractor
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (live : DIndGArtifactLiveSRCoreObligations evaluator sig) :
    DIndGArtifactExactSRCoreExtractor evaluator sig :=
  DIndGArtifactExactSRCoreExtractor.ofEvaluatorSoundnessTransportInferCompleteness
    live.evaluator_sound
    live.transport
    live.infer_complete

end DIndGArtifactLiveSRCoreObligations

/-- Compatibility lowering contract from executable runtime artifact readouts to
the typed generated-iota transcript consumed by the Lean theorem.  New
kernel-facing entry points should prefer
`DIndGArtifactExactExecutableSRLowering`, whose transcript is indexed by
the exact certificate opened from `sr-ok`. -/
structure DIndGArtifactExecutableSRLowering
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  generated_iota_execution :
    ∀ {rawTerm : DIndGArtifactTerm} {t : PureTm 0},
      DIndGArtifactSROKCert evaluator sig rawTerm →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t →
          DIndGArtifactGeneratedIotaExecution evaluator sig rawTerm t

namespace DIndGArtifactExecutableSRLowering

def ofEvaluatorSoundnessTransport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig) :
    DIndGArtifactExecutableSRLowering evaluator sig where
  generated_iota_execution := by
    intro rawTerm t cert termTranslates
    let sourceReadout :=
      transport.infer_translates
        cert.source_infer_readout termTranslates
    have sourceTyped :
        HasTypeDecl
          (envOfSpecs sig.translatedSpecs) .nil
          t sourceReadout.type :=
      evaluatorSound.infer_sound
        cert.source_infer_readout
        termTranslates
        sourceReadout.type_translates
    let nfReadout :=
      transport.nf_generated_iota
        cert.nf_readout termTranslates sourceTyped
    let targetReadout :=
      transport.infer_translates
        cert.target_infer_readout
        nfReadout.nf_translates
    have targetTyped :
        HasTypeDecl
          (envOfSpecs sig.translatedSpecs) .nil
          nfReadout.nfTerm targetReadout.type :=
      evaluatorSound.infer_sound
        cert.target_infer_readout
        nfReadout.nf_translates
        targetReadout.type_translates
    have inferredTypesConvertible :
        ConvDecl
          (envOfSpecs sig.translatedSpecs)
          sourceReadout.type targetReadout.type :=
      evaluatorSound.conv_sound
        cert.conv_readout
        sourceReadout.type_translates
        targetReadout.type_translates
    exact
      { cert := cert
        term_translates := termTranslates
        nfTerm := nfReadout.nfTerm
        sourceInfer := sourceReadout.type
        targetInfer := targetReadout.type
        nf_translates := nfReadout.nf_translates
        source_infer_translates := sourceReadout.type_translates
        target_infer_translates := targetReadout.type_translates
        contract := nfReadout.contract
        contract_mem := nfReadout.contract_mem
        generated_iota_step := nfReadout.generated_iota_step
        source_infer_typed := sourceTyped
        nf_justification := nfReadout.nf_justification
        target_infer_typed := targetTyped
        inferred_types_convertible := inferredTypesConvertible }

def ofSROKExtractionSoundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig) :
    DIndGArtifactExecutableSRLowering evaluator sig where
  generated_iota_execution := by
    intro rawTerm t cert termTranslates
    rcases certExtraction.kernel_readout_of_cert
        cert termTranslates with
      ⟨nfT, sourceInfer, targetInfer, readout⟩
    exact
      { cert := cert
        term_translates := readout.term_translates
        nfTerm := nfT
        sourceInfer := sourceInfer
        targetInfer := targetInfer
        nf_translates := readout.nf_translates
        source_infer_translates := readout.source_infer_translates
        target_infer_translates := readout.target_infer_translates
        contract := readout.contract
        contract_mem := readout.contract_mem
        generated_iota_step := readout.generated_iota_step
        source_infer_typed := readout.source_infer_typed evaluatorSound
        nf_justification := readout.nf_justification
        target_infer_typed := readout.target_infer_typed evaluatorSound
        inferred_types_convertible := readout.conv_sound evaluatorSound }

theorem typed_generated_iota_sr_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExecutableSRLowering evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGArtifactGeneratedIotaExecution.typed_generated_iota_sr_of_sig_admitted
    gateSucceeds metatheory
    (lowering.generated_iota_execution cert termTranslates)

/-- Public `sr-ok` form of the executable-lowering theorem.  The kernel
artifact exposes `sr-ok` as a proposition with the intermediate readouts hidden;
because the conclusion is also propositional, the bridge can reveal those
readouts inside Lean and pass the corresponding certificate to the lowering
contract. -/
theorem typed_generated_iota_sr_of_sig_admitted_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExecutableSRLowering evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer := by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let cert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  exact
    typed_generated_iota_sr_of_sig_admitted
      gateSucceeds metatheory lowering cert termTranslates

end DIndGArtifactExecutableSRLowering

/-- Exact lowering contract from executable runtime artifact readouts to the
typed generated-iota transcript.  The certificate opened from the public
`sr-ok` proposition is an index of the produced transcript, so the bridge keeps
the same hidden `nf`/`infer` witnesses throughout the proof. -/
structure DIndGArtifactExactExecutableSRLowering
    (evaluator : DIndGArtifactEvaluator)
    (sig : DIndGArtifactSig) : Type where
  generated_iota_execution :
    ∀ {rawTerm : DIndGArtifactTerm} {t : PureTm 0},
      (cert : DIndGArtifactSROKCert evaluator sig rawTerm) →
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t →
          DIndGArtifactGeneratedIotaExecutionForCert
            evaluator sig rawTerm cert t

namespace DIndGArtifactExactExecutableSRLowering

def ofEvaluatorSoundnessTransport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig) :
    DIndGArtifactExactExecutableSRLowering evaluator sig where
  generated_iota_execution := by
    intro rawTerm t cert termTranslates
    let sourceReadout :=
      transport.infer_translates
        cert.source_infer_readout termTranslates
    have sourceTyped :
        HasTypeDecl
          (envOfSpecs sig.translatedSpecs) .nil
          t sourceReadout.type :=
      evaluatorSound.infer_sound
        cert.source_infer_readout
        termTranslates
        sourceReadout.type_translates
    let nfReadout :=
      transport.nf_generated_iota
        cert.nf_readout termTranslates sourceTyped
    let targetReadout :=
      transport.infer_translates
        cert.target_infer_readout
        nfReadout.nf_translates
    have targetTyped :
        HasTypeDecl
          (envOfSpecs sig.translatedSpecs) .nil
          nfReadout.nfTerm targetReadout.type :=
      evaluatorSound.infer_sound
        cert.target_infer_readout
        nfReadout.nf_translates
        targetReadout.type_translates
    have inferredTypesConvertible :
        ConvDecl
          (envOfSpecs sig.translatedSpecs)
          sourceReadout.type targetReadout.type :=
      evaluatorSound.conv_sound
        cert.conv_readout
        sourceReadout.type_translates
        targetReadout.type_translates
    exact
      { term_translates := termTranslates
        nfTerm := nfReadout.nfTerm
        sourceInfer := sourceReadout.type
        targetInfer := targetReadout.type
        nf_translates := nfReadout.nf_translates
        source_infer_translates := sourceReadout.type_translates
        target_infer_translates := targetReadout.type_translates
        contract := nfReadout.contract
        contract_mem := nfReadout.contract_mem
        generated_iota_step := nfReadout.generated_iota_step
        source_infer_typed := sourceTyped
        nf_justification := nfReadout.nf_justification
        target_infer_typed := targetTyped
        inferred_types_convertible := inferredTypesConvertible }

def ofSROKExtractionSoundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig) :
    DIndGArtifactExactExecutableSRLowering evaluator sig where
  generated_iota_execution := by
    intro rawTerm t cert termTranslates
    rcases certExtraction.kernel_readout_of_cert
        cert termTranslates with
      ⟨nfT, sourceInfer, targetInfer, readout⟩
    exact
      { term_translates := readout.term_translates
        nfTerm := nfT
        sourceInfer := sourceInfer
        targetInfer := targetInfer
        nf_translates := readout.nf_translates
        source_infer_translates := readout.source_infer_translates
        target_infer_translates := readout.target_infer_translates
        contract := readout.contract
        contract_mem := readout.contract_mem
        generated_iota_step := readout.generated_iota_step
        source_infer_typed := readout.source_infer_typed evaluatorSound
        nf_justification := readout.nf_justification
        target_infer_typed := readout.target_infer_typed evaluatorSound
        inferred_types_convertible := readout.conv_sound evaluatorSound }

theorem typed_generated_iota_sr_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExactExecutableSRLowering evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGArtifactGeneratedIotaExecutionForCert.typed_generated_iota_sr_of_sig_admitted
    gateSucceeds metatheory
    (lowering.generated_iota_execution cert termTranslates)

end DIndGArtifactExactExecutableSRLowering

namespace DIndGArtifactSROKCert

/-- Public certificate theorem routed through the strict kernel readout:
`sr-ok` evidence plus evaluator transport/soundness produces exactly the
per-run `nf`/`infer`/`conv` transcript consumed by the universal SR theorem. -/
theorem typed_generated_iota_sr_of_sig_admitted
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert : DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
              ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer := by
  exact
    justified_of_sig_admitted
      gateSucceeds metatheory evaluatorSound transport cert termTranslates

end DIndGArtifactSROKCert

/-- Translation relation from raw DIndG artifact data to the Lean
declaration specs and generated-recursor contracts consumed by the metatheory.
This relation intentionally records provenance and equality of bridge outputs;
it does not re-run `sig-admitted-with-elims` in Lean. -/
structure DIndGArtifactSignatureTranslation
    (sig : DIndGArtifactSig)
    (specs : List DeclSpec)
    (contracts : List FamilyRecursorDeclContract) : Prop where
  specs_eq :
    sig.translatedSpecs = specs
  contracts_eq :
    sig.translatedContracts = contracts
  contract_sources :
    ∀ contract, contract ∈ contracts →
      ∃ decl, decl ∈ sig.decls ∧
        DIndGArtifactDecl.supportsContract
          sig.nameTranslates decl contract

/-- Raw artifact correspondence: the generic correspondence plus the explicit
raw-signature translation relation. -/
structure DIndGRawArtifactCorrespondence
    (sig : DIndGArtifactSig)
    (specs : List DeclSpec)
    (contracts : List FamilyRecursorDeclContract) where
  raw_translation :
    DIndGArtifactSignatureTranslation sig specs contracts
  generic :
    DIndGArtifactCorrespondence
      dindgRawArtifactGate sig specs contracts

/-- Soundness seam for the raw DIndG admission gate: when
`sig-admitted-with-elims` succeeds for a translated raw signature, the bridge
may read off the canonical Lean metatheory package for the translated
declarations and generated recursors. -/
structure DIndGRawAdmissionGateSoundness
    (sig : DIndGArtifactSig)
    (specs : List DeclSpec)
    (contracts : List FamilyRecursorDeclContract) : Type where
  metatheory_of_gate :
    dindgRawArtifactGate.sigAdmittedWithElims sig →
      DIndGArtifactSignatureTranslation sig specs contracts →
        DIndGArtifactMetatheoryReadout
          dindgRawArtifactGate sig specs contracts

namespace DIndGRawAdmissionGateSoundness

/-- Canonical soundness of the structured raw admission gate.  Once a raw
signature's `sig-admitted-with-elims` certificate and translation relation are
available, the Lean metatheory readout is derived directly; callers no longer
need to assume a separate raw-admission oracle. -/
def canonical
    (sig : DIndGArtifactSig)
    (specs : List DeclSpec)
    (contracts : List FamilyRecursorDeclContract) :
    DIndGRawAdmissionGateSoundness sig specs contracts where
  metatheory_of_gate := by
    intro gateSucceeds translation
    rcases gateSucceeds with
      ⟨hSig, _hSources, hElims, hResolved⟩
    exact
      { signature_translation := by
          simpa [translation.specs_eq] using hSig
        constructor_head_orthogonality_translation := by
          intro contract hmem
          have hmemSig : contract ∈ sig.translatedContracts := by
            simpa [translation.contracts_eq] using hmem
          exact (hResolved contract hmemSig).1
        generated_eliminator_translation := by
          intro contract hmem
          have hmemSig : contract ∈ sig.translatedContracts := by
            simpa [translation.contracts_eq] using hmem
          exact hElims contract hmemSig
        generated_iota_preservation_translation := by
          intro contract hmem
          have hmemSig : contract ∈ sig.translatedContracts := by
            simpa [translation.contracts_eq] using hmem
          exact hResolved contract hmemSig
        declaration_church_rosser := DeclarationSemantics.declChurchRosser }

end DIndGRawAdmissionGateSoundness

namespace DIndGRawArtifactCorrespondence

def ofGateSoundness {sig : DIndGArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation : DIndGArtifactSignatureTranslation sig specs contracts)
    (sound :
      DIndGRawAdmissionGateSoundness sig specs contracts) :
    DIndGRawArtifactCorrespondence sig specs contracts :=
  { raw_translation := translation
    generic :=
      DIndGArtifactCorrespondence.ofGateAndReadout
        gateSucceeds
        (sound.metatheory_of_gate gateSucceeds translation) }

def ofGate {sig : DIndGArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation : DIndGArtifactSignatureTranslation sig specs contracts) :
    DIndGRawArtifactCorrespondence sig specs contracts :=
  ofGateSoundness gateSucceeds translation
    (DIndGRawAdmissionGateSoundness.canonical sig specs contracts)

def toGeneric {sig : DIndGArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGRawArtifactCorrespondence sig specs contracts) :
    DIndGArtifactCorrespondence
      dindgRawArtifactGate sig specs contracts :=
  corr.generic

def toMetatheoryReadout {sig : DIndGArtifactSig}
    {specs : List DeclSpec}
    {contracts : List FamilyRecursorDeclContract}
    (corr : DIndGRawArtifactCorrespondence sig specs contracts) :
    DIndGArtifactMetatheoryReadout
      dindgRawArtifactGate sig specs contracts :=
  { signature_translation := corr.generic.signature_translation
    constructor_head_orthogonality_translation :=
      corr.generic.constructor_head_orthogonality_translation
    generated_eliminator_translation :=
      corr.generic.generated_eliminator_translation
    generated_iota_preservation_translation :=
      corr.generic.generated_iota_preservation_translation
    declaration_church_rosser := corr.generic.declaration_church_rosser }

theorem raw_sr_ok_and_lean_convertible
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGRawArtifactCorrespondence
        sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm ∧
      ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGArtifactSRReadout.raw_sr_ok_and_lean_convertible_of_sig_admitted
    corr.generic.gate_succeeds
    corr.toMetatheoryReadout
    readout

theorem source_infer_preserved
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGRawArtifactCorrespondence
        sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer :=
  DIndGArtifactSRReadout.source_infer_preserved_of_raw_sr_readout
    corr.generic
    readout

theorem typed_generated_iota_sr
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGRawArtifactCorrespondence
        sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm ∧
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
            ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGArtifactSRReadout.typed_generated_iota_sr_of_sig_admitted
    corr.generic.gate_succeeds
    corr.toMetatheoryReadout
    readout

theorem sr_ok_justified
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (corr :
      DIndGRawArtifactCorrespondence
        sig sig.translatedSpecs sig.translatedContracts)
    (sound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm ∧
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
            ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGArtifactSRKernelReadout.sr_ok_justified_of_sig_admitted
    corr.generic.gate_succeeds
    corr.toMetatheoryReadout
    sound
    readout

theorem public_sr_ok_justified
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (corr :
      DIndGRawArtifactCorrespondence
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  DIndGArtifactSROKExtractionSoundness.public_sr_ok_justified_of_sig_admitted
    corr.generic.gate_succeeds
    corr.toMetatheoryReadout
    evaluatorSound
    certExtraction
    srOk
    termTranslates

theorem sr_ok_justified_of_gate_soundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (admissionSound :
      DIndGRawAdmissionGateSoundness
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    evaluator.srOk sig rawTerm ∧
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
            ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  sr_ok_justified
    (ofGateSoundness gateSucceeds translation admissionSound)
    evaluatorSound
    readout

theorem public_sr_ok_justified_of_gate_soundness
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (admissionSound :
      DIndGRawAdmissionGateSoundness
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  public_sr_ok_justified
    (ofGateSoundness gateSucceeds translation admissionSound)
    evaluatorSound
    certExtraction
    srOk
    termTranslates

/-- Raw-gate theorem for the strict per-run artifact transcript.  Admission
plus translation plus the observed `nf`/`infer`/`conv` readout and its local
Lean soundness imply the full SR/convertibility conclusion for that artifact
term, without a global evaluator-soundness or extraction assumption. -/
theorem typed_generated_iota_sr_of_gate
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer)
    (localSound :
      DIndGArtifactSRKernelReadout.LocalSoundness readout) :
    evaluator.srOk sig rawTerm ∧
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
            ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  exact
    DIndGArtifactSRKernelReadout.sr_ok_justified_of_sig_admitted_local
      gateSucceeds metatheory readout localSound

/-- Public raw-gate theorem with the canonical admission readout derived from
the structured `sig-admitted-with-elims` certificate.  The remaining external
obligation is the exact certificate-indexed extraction of the executable
`sr-ok` readouts, not a separate raw-admission oracle. -/
theorem public_sr_ok_justified_of_gate
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  public_sr_ok_justified
    (ofGate gateSucceeds translation)
    evaluatorSound
    certExtraction
    srOk
    termTranslates

/-- Public raw-gate theorem through the executable lowering seam.  This is the
artifact theorem's intended next interface: the admission gate is discharged by
the structured raw signature, while the remaining executable obligation is the
typed generated-iota transcript extracted from the real `sr-ok` run. -/
theorem public_sr_ok_justified_of_gate_lowering
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExecutableSRLowering evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  exact
    DIndGArtifactExecutableSRLowering.typed_generated_iota_sr_of_sig_admitted
      gateSucceeds metatheory lowering cert termTranslates

/-- Public raw-gate theorem in the artifact's propositional `sr-ok` shape.
This is the closest bridge statement to the kernel predicate: the only
remaining non-Lean contract is the executable lowering that turns the real
`nf`/`infer`/`conv` readouts hidden in `sr-ok` into a typed generated-iota
transcript. -/
theorem public_sr_ok_justified_of_gate_lowering_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExecutableSRLowering evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  exact
    DIndGArtifactExecutableSRLowering.typed_generated_iota_sr_of_sig_admitted_sr_ok
      gateSucceeds metatheory lowering srOk termTranslates

/-- Certificate-indexed raw-gate theorem through the exact extraction seam.
This is the data-facing companion to the public `sr-ok` theorem below: because
the certificate exposes the observed `nf`/`infer`/`conv` witnesses, the result
keeps those witnesses fixed and only existentially returns their Lean
translations. -/
theorem cert_justified_of_gate_cert_extraction
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
              ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  exact
    DIndGArtifactSROKExtractionSoundness.cert_justified_of_sig_admitted
      gateSucceeds metatheory evaluatorSound
      certExtraction cert termTranslates

/-- Public raw-gate theorem through the certificate-indexed extraction seam.
Compared with the older public extractor, this states the next non-Lean
obligation on the exact `sr-ok` witnesses opened by the proof, so the artifact
lowering cannot silently swap in different intermediate readouts. -/
theorem public_sr_ok_justified_of_gate_cert_extraction
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let cert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  rcases cert_justified_of_gate_cert_extraction
      gateSucceeds translation evaluatorSound
      certExtraction cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, justified⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, justified⟩

/-- Public raw-gate theorem with executable evaluator soundness/transport in
the artifact's propositional `sr-ok` shape.  This removes the evidence-carrying
certificate from the transport-facing theorem boundary; the hidden readouts are
opened only inside the proof. -/
theorem public_sr_ok_justified_of_gate_transport_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  public_sr_ok_justified_of_gate_lowering_sr_ok
    gateSucceeds translation
    (DIndGArtifactExecutableSRLowering.ofEvaluatorSoundnessTransport
      evaluatorSound transport)
    srOk termTranslates

/-- Certificate-indexed transport theorem.  This keeps the concrete
`nf`/`infer`/`conv` observations fixed while using evaluator transport to lower
them into the Lean declaration calculus. -/
theorem cert_justified_of_gate_transport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
              ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  cert_justified_of_gate_cert_extraction
    gateSucceeds translation evaluatorSound
    (DIndGArtifactSROKExtractionSoundness.ofEvaluatorSoundnessTransport
      evaluatorSound transport)
    cert termTranslates

/-- Public raw-gate theorem with `sr-ok` evidence transported directly.  This
removes the standalone extraction-soundness hypothesis: the remaining external
contract is the concrete transport of artifact `infer` and generated-iota `nf`
readouts into the Lean declaration calculus. -/
theorem public_sr_ok_justified_of_gate_transport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ _rawNf : DIndGArtifactTerm,
      ∃ _rawSourceInfer : DIndGArtifactTerm,
        ∃ _rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
            HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
              HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
                ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases cert_justified_of_gate_transport
      gateSucceeds translation evaluatorSound transport
      cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, justified⟩
  exact
    ⟨cert.rawNf, cert.rawSourceInfer, cert.rawTargetInfer,
      nfT, sourceInfer, targetInfer, justified⟩

/-- Conv-free raw-gate preservation theorem for the observable SR core:
from `sig-admitted-with-elims`, source-term translation, and the executable
`nf`/`infer` transcript transported into Lean, normalization preserves the
source inferred type.  The target `infer` result is also justified as a Lean
typing judgment; comparing the two inferred types as convertible remains the
separate `conv`/`sr-ok` layer. -/
theorem nf_infer_cert_preserves_source_infer_of_gate_transport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
        evaluator.nf sig rawTerm cert.rawNf ∧
        evaluator.infer sig rawTerm cert.rawSourceInfer ∧
        evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer :=
by
  rcases DIndGArtifactNFInferCert.to_nf_infer_readout
      evaluatorSound transport cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, readout, sourceTyped⟩
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  let corr :=
    DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds metatheory
  have preserved :
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer :=
    DIndGArtifactNFInferReadout.source_infer_preserved_of_source_typing
      corr readout sourceTyped.down
  have targetTyped :
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer :=
    evaluatorSound.infer_sound
      readout.target_infer_readout
      readout.nf_translates
      readout.target_infer_translates
  exact
    ⟨nfT, sourceInfer, targetInfer,
      readout.nf_translates,
      readout.source_infer_translates,
      readout.target_infer_translates,
      readout.nf_readout,
      readout.source_infer_readout,
      readout.target_infer_readout,
      sourceTyped.down,
      preserved,
      targetTyped⟩

/-- `sr-ok` certificates contain the conv-free SR-core transcript as a
subcertificate, so the preservation half can be read off before using the final
artifact `conv` result. -/
theorem sr_ok_cert_preserves_source_infer_of_gate_transport
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
        evaluator.nf sig rawTerm cert.rawNf ∧
        evaluator.infer sig rawTerm cert.rawSourceInfer ∧
        evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer :=
  nf_infer_cert_preserves_source_infer_of_gate_transport
    gateSucceeds translation evaluatorSound transport
    (DIndGArtifactNFInferCert.ofSROKCert cert)
    termTranslates

/-- Type-uniqueness variant of the conv-free SR theorem.  If the translated
declaration calculus has type uniqueness, the observable `nf`/`infer`
transcript alone proves that the two artifact `infer` outputs translate to
convertible Lean types; the artifact's final `conv` readout is not used. -/
theorem nf_infer_cert_convertible_of_gate_transport_type_unique
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (typeUnique :
      DeclTypeUniqueness (envOfSpecs sig.translatedSpecs))
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
        evaluator.nf sig rawTerm cert.rawNf ∧
        evaluator.infer sig rawTerm cert.rawSourceInfer ∧
        evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
        ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases nf_infer_cert_preserves_source_infer_of_gate_transport
      gateSucceeds translation evaluatorSound transport
      cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hNfReadout, hSourceReadout, hTargetReadout,
      hSourceTyped, hPreserved, hTargetTyped⟩
  exact
    ⟨nfT, sourceInfer, targetInfer,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hNfReadout,
      hSourceReadout,
      hTargetReadout,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      typeUnique hPreserved hTargetTyped⟩

/-- `sr-ok` certificate wrapper for the type-uniqueness route.  This is only a
sufficient fallback: for the executable artifact theorem, the intended route is
the algorithmic-`infer` completeness contract below rather than global
declaration type uniqueness. -/
theorem sr_ok_cert_convertible_of_gate_transport_type_unique
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (typeUnique :
      DeclTypeUniqueness (envOfSpecs sig.translatedSpecs))
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
        evaluator.nf sig rawTerm cert.rawNf ∧
        evaluator.infer sig rawTerm cert.rawSourceInfer ∧
        evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
        ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  nf_infer_cert_convertible_of_gate_transport_type_unique
    gateSucceeds translation evaluatorSound transport typeUnique
    (DIndGArtifactNFInferCert.ofSROKCert cert)
    termTranslates

/-- Algorithmic-infer route for the conv-free SR theorem.  Preservation proves
that the observed normal form still has the source inferred type; completeness
of the executable `infer` readout for that same normal form then converts the
source inferred type to the target inferred type.  No artifact `conv` readout
is used. -/
theorem nf_infer_cert_convertible_of_gate_transport_infer_complete
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
        evaluator.nf sig rawTerm cert.rawNf ∧
        evaluator.infer sig rawTerm cert.rawSourceInfer ∧
        evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
        ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases nf_infer_cert_preserves_source_infer_of_gate_transport
      gateSucceeds translation evaluatorSound transport
      cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hNfReadout, hSourceReadout, hTargetReadout,
      hSourceTyped, hPreserved, hTargetTyped⟩
  have hConv :
      ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
    inferComplete.infer_complete
      hTargetReadout hNfTranslates hTargetTranslates hPreserved
  exact
    ⟨nfT, sourceInfer, targetInfer,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hNfReadout,
      hSourceReadout,
      hTargetReadout,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- `sr-ok` certificate wrapper for the algorithmic-infer route.  The final
convertibility conclusion is obtained from preservation plus `infer`
completeness, not from the artifact's final `conv` readout. -/
theorem sr_ok_cert_convertible_of_gate_transport_infer_complete
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
        evaluator.nf sig rawTerm cert.rawNf ∧
        evaluator.infer sig rawTerm cert.rawSourceInfer ∧
        evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
        ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  nf_infer_cert_convertible_of_gate_transport_infer_complete
    gateSucceeds translation evaluatorSound transport inferComplete
    (DIndGArtifactNFInferCert.ofSROKCert cert)
    termTranslates

/-- Public `sr-ok` form of the algorithmic-infer route.  The proof opens the
hidden `nf`/`infer` observations from `sr-ok`, but the final declaration-side
convertibility is obtained from `infer` completeness for the target normal
form rather than from the artifact's final `conv` observation. -/
theorem public_sr_ok_justified_of_gate_transport_infer_complete
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawTargetInfer targetInfer ∧
        evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
        ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let cert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  rcases sr_ok_cert_convertible_of_gate_transport_infer_complete
      gateSucceeds translation evaluatorSound transport
      inferComplete cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      _hNfReadout, _hSourceReadout, _hTargetReadout,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      cert.to_sr_ok,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Observation-only preservation theorem for
`kernel_signature_lf_indexed_v0.metta`'s `sr-ok` equation.  It uses the
observed `nf` and `infer` readouts plus source-infer typing to prove that
normalization preserves the source inferred type; it does not assume or inspect
the artifact's final `conv` readout. -/
theorem kernel_signature_lf_indexed_nf_preserves_source_infer_of_observation
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactNFInferReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer)
    (sourceTyped :
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer) :
    ∃ contract : FamilyRecursorDeclContract,
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawTargetInfer targetInfer ∧
        contract ∈ sig.translatedContracts ∧
        DIndGArtifactResolvedIotaStep contract t nfT ∧
        DIndGArtifactNFJustification
          (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
        evaluator.nf sig rawTerm rawNf ∧
        evaluator.infer sig rawTerm rawSourceInfer ∧
        evaluator.infer sig rawNf rawTargetInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer :=
by
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  let corr :=
    DIndGArtifactCorrespondence.ofGateAndReadout
      gateSucceeds metatheory
  have hPreserved :
      HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer :=
    DIndGArtifactNFInferReadout.source_infer_preserved_of_source_typing
      corr readout sourceTyped
  exact
    ⟨readout.contract,
      readout.nf_translates,
      readout.source_infer_translates,
      readout.target_infer_translates,
      readout.contract_mem,
      readout.generated_iota_step,
      readout.nf_justification,
      readout.nf_readout,
      readout.source_infer_readout,
      readout.target_infer_readout,
      sourceTyped,
      hPreserved⟩

/-- Exact-lowering theorem boundary for `kernel_signature_lf_indexed_v0.metta`'s
conv-free observable SR core.  The executable side must lower the exact
`nf`/two-`infer` certificate; Lean then uses the admission gate's
declaration-side SR package plus local target-`infer` coherence to justify the
two inferred types as convertible. -/
theorem kernel_signature_lf_indexed_infer_nf_convertible_of_exact_nf_infer_lowering
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExactNFInferLowering evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (targetCoherence :
      DIndGArtifactNFInferCert.TargetInferCoherence cert)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  exact
    DIndGArtifactExactNFInferLowering.infer_nf_convertible_of_sig_admitted
      gateSucceeds metatheory lowering cert targetCoherence termTranslates

/-- Data-facing theorem for the artifact's explicit `SRCoreReadout` transcript.
This is the preferred boundary after `kernel_signature_lf_indexed_v0.metta`
exposes `sr-core-readout`: Lean justifies the exact `nf`/source-`infer`/
target-`infer` observations from that transcript, not merely some hidden
witnesses opened from the Boolean `srOk`. -/
theorem kernel_signature_lf_indexed_sr_core_readout_justified_of_exact_sr_core_extractor
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (extractor :
      DIndGArtifactExactSRCoreExtractor evaluator sig)
    (readout :
      DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 readout.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 readout.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 readout.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm readout.rawNf
            readout.rawSourceInfer readout.rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  let nfCert : DIndGArtifactNFInferCert evaluator sig rawTerm :=
    DIndGArtifactNFInferCert.ofSROKCert readout.toSROKCert
  rcases kernel_signature_lf_indexed_infer_nf_convertible_of_exact_nf_infer_lowering
      gateSucceeds translation extractor.nf_infer_lowering nfCert
      (extractor.target_coherence.target_coherence nfCert)
      termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      _hNfReadout, _hSourceInferReadout, _hTargetInferReadout,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      readout.to_sr_ok_with_readouts,
      readout.to_sr_ok,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Data-facing theorem through the canonical evaluator obligations.  This
removes the packaged-extractor ceremony from the public SR-core boundary:
evaluator soundness plus transport lower the exact executable readouts, and
algorithmic-`infer` completeness supplies target-readout coherence. -/
theorem kernel_signature_lf_indexed_sr_core_readout_justified_of_evaluator_transport_infer_complete
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (readout :
      DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 readout.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 readout.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 readout.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm readout.rawNf
            readout.rawSourceInfer readout.rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_sr_core_readout_justified_of_exact_sr_core_extractor
    gateSucceeds translation
    (DIndGArtifactExactSRCoreExtractor.ofEvaluatorSoundnessTransportInferCompleteness
        evaluatorSound transport inferComplete)
    readout termTranslates

/-- Provenance-enriched data-facing theorem: the justified generated-iota
contract is not merely a Lean-side contract in the translated list; it is
connected back to a raw DIndG declaration in the runtime artifact signature. -/
theorem kernel_signature_lf_indexed_sr_core_readout_justified_with_contract_source
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (readout :
      DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
      ∃ rawDecl : DIndGArtifactDecl,
        contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 readout.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 readout.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 readout.rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm readout.rawNf
            readout.rawSourceInfer readout.rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases kernel_signature_lf_indexed_sr_core_readout_justified_of_evaluator_transport_infer_complete
      gateSucceeds translation evaluatorSound transport inferComplete
      readout termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  rcases translation.contract_sources contract hContractMem with
    ⟨rawDecl, hRawDeclMem, hSupports⟩
  exact
    ⟨nfT, sourceInfer, targetInfer, contract, rawDecl,
      hContractMem,
      hRawDeclMem,
      hSupports,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Public theorem through the single exact SR-core extractor.  This is the
preferred final seam for `kernel_signature_lf_indexed_v0.metta`: the artifact
extractor must lower the exact `nf`/two-`infer` readouts and provide local
target-`infer` coherence for those readouts; Lean supplies admission-derived
subject reduction and declaration-side convertibility. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_sr_core_extractor
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (extractor :
      DIndGArtifactExactSRCoreExtractor evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let readout : DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_success := convReadout }
  rcases kernel_signature_lf_indexed_sr_core_readout_justified_of_exact_sr_core_extractor
      gateSucceeds translation extractor readout termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Public `sr-ok` theorem through the exact conv-free NF/infer spine.  The
hidden readouts opened from `sr-ok` are converted to the exact `NFInferCert`;
declaration-side convertibility is then justified by subject reduction plus
the target-`infer` coherence provider, not by replaying the final artifact
`conv` readout. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_nf_infer_lowering_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExactNFInferLowering evaluator sig)
    (targetCoherence :
      DIndGArtifactExactTargetInferCoherence evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_sr_core_extractor
    gateSucceeds translation
    { nf_infer_lowering := lowering
      target_coherence := targetCoherence }
    srOk termTranslates

/-- Public `sr-ok` theorem through exact NF/infer lowering plus global
algorithmic-`infer` completeness.  This is the preferred conv-free route when
the executable `infer` readout has a completeness/coherence proof. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_nf_infer_infer_complete
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExactNFInferLowering evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_sr_core_extractor
    gateSucceeds translation
    { nf_infer_lowering := lowering
      target_coherence :=
        DIndGArtifactExactTargetInferCoherence.ofInferCompleteness
          inferComplete }
    srOk termTranslates

/-- Public `sr-ok` theorem through canonical evaluator obligations.  This is
the Boolean companion to the explicit `SRCoreReadout` theorem: the proof opens
the public `srOk` existential, but the exact extractor itself is derived from
evaluator soundness, artifact transport, and algorithmic-`infer` completeness. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_evaluator_transport_infer_complete
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_sr_core_extractor
    gateSucceeds translation
    (DIndGArtifactExactSRCoreExtractor.ofEvaluatorSoundnessTransportInferCompleteness
      evaluatorSound transport inferComplete)
    srOk termTranslates

/-- Provenance-enriched public `sr-ok` theorem.  In addition to the usual
Lean SR/convertibility conclusion, this returns the raw DIndG declaration that
supports the generated-recursor contract used by the artifact `nf` readout. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_with_contract_source
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
        ∃ rawDecl : DIndGArtifactDecl,
          contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let readout : DIndGArtifactSRCoreReadoutCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_success := convReadout }
  rcases kernel_signature_lf_indexed_sr_core_readout_justified_with_contract_source
      gateSucceeds translation evaluatorSound transport inferComplete
      readout termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract, rawDecl,
      hContractMem, hRawDeclMem, hSupports,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract, rawDecl,
      hContractMem,
      hRawDeclMem,
      hSupports,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Compatibility theorem: route public `sr-ok` through the exact NF/infer
spine, but obtain the local target-`infer` coherence from the final artifact
`conv` readout.  This keeps the witness discipline of the conv-free theorem
while preserving the older evaluator-soundness interface. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_nf_infer_conv_sound
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (lowering :
      DIndGArtifactExactNFInferLowering evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let srCert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  let nfCert : DIndGArtifactNFInferCert evaluator sig rawTerm :=
    DIndGArtifactNFInferCert.ofSROKCert srCert
  rcases kernel_signature_lf_indexed_infer_nf_convertible_of_exact_nf_infer_lowering
      gateSucceeds translation lowering nfCert
      (DIndGArtifactSROKCert.targetInferCoherenceOfConvSoundness
        srCert evaluatorSound)
      termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hNfReadout, hSourceInferReadout, hTargetInferReadout,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  have hSrOkWithReadouts :
      evaluator.srOkWithReadouts
        sig rawTerm rawNf rawSourceInfer rawTargetInfer :=
    ⟨hNfReadout, hSourceInferReadout, hTargetInferReadout, convReadout⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      ⟨rawNf, rawSourceInfer, rawTargetInfer, hSrOkWithReadouts⟩,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Local-coherence theorem boundary for `kernel_signature_lf_indexed_v0.metta`'s
observable SR core:

`nft = nf sig t; a = infer sig [] t; b = infer sig [] nft`.

The theorem starts from those three executable observations, not from the final
artifact `conv` readout.  Subject reduction preserves the source inferred type
across the observed `nf`; the only remaining target-`infer` obligation is the
local coherence of this generated-iota transcript. -/
theorem kernel_signature_lf_indexed_infer_nf_convertible_of_observation_local_coherence
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (targetCoherence :
      DIndGArtifactNFInferCert.TargetInferCoherence cert)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_infer_nf_convertible_of_exact_nf_infer_lowering
    gateSucceeds translation
    (DIndGArtifactExactNFInferLowering.ofEvaluatorSoundnessTransport
      evaluatorSound transport)
    cert targetCoherence termTranslates

/-- Global algorithmic-`infer` completeness wrapper for the local-coherence
theorem.  This is a sufficient route to the kernel theorem, but the theorem
above is the sharper obligation for generated-iota artifacts. -/
theorem kernel_signature_lf_indexed_infer_nf_convertible_of_observation_infer_complete
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_infer_nf_convertible_of_observation_local_coherence
    gateSucceeds translation evaluatorSound transport cert
    (DIndGArtifactNFInferCert.TargetInferCoherence.ofInferCompleteness
      cert inferComplete)
    termTranslates

/-- Provenance-enriched conv-free SR-core theorem.  This is the artifact
normalization theorem before the final `sr-ok`/`conv` wrapper: the observed
`nf` and two `infer` readouts are lowered to Lean, subject reduction preserves
the source inferred type across the generated-iota normal form, algorithmic
`infer` completeness compares the target readout with that preserved type, and
the generated-recursor contract is traced back to the raw DIndG declaration
that supplied it. -/
theorem kernel_signature_lf_indexed_infer_nf_convertible_of_observation_infer_complete_with_contract_source
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (inferComplete :
      DIndGArtifactInferCompleteness evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
      ∃ rawDecl : DIndGArtifactDecl,
        contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases kernel_signature_lf_indexed_infer_nf_convertible_of_observation_infer_complete
      gateSucceeds translation evaluatorSound transport inferComplete
      cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hNfReadout, hSourceInferReadout, hTargetInferReadout,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  rcases translation.contract_sources contract hContractMem with
    ⟨rawDecl, hRawDeclMem, hSupports⟩
  exact
    ⟨nfT, sourceInfer, targetInfer, contract, rawDecl,
      hContractMem,
      hRawDeclMem,
      hSupports,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hIota,
      hNfJustification,
      hNfReadout,
      hSourceInferReadout,
      hTargetInferReadout,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- The admission mirror used by the artifact SR theorem is derived from the
raw `sig-admitted-with-elims` gate plus the signature translation relation; it
is not an independently assumed Stage-3 mirror. -/
theorem kernel_signature_lf_indexed_admitted_mirror_of_raw_gate
    {sig : DIndGArtifactSig}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts) :
    DIndGAdmitted sig.translatedSpecs sig.translatedContracts :=
  (DIndGRawArtifactCorrespondence.ofGate
    gateSucceeds translation).toGeneric.toAdmitted

/-- Universal conv-free generated-iota SR theorem for the indexed kernel
artifact.

For any raw DIndG artifact signature whose
`sig-admitted-with-elims` gate succeeds, and for any executable
`nf`/source-`infer`/target-`infer` transcript that the canonical extractor
lowers as a generated-iota observation, Lean proves that normalization
preserves the source inferred type and that the two artifact `infer` readouts
are declaration-side convertible.  The mirror admission is derived from the raw
gate and translation relation; the final artifact `conv`/`sr-ok` wrapper is not
used. -/
theorem kernel_signature_lf_indexed_universal_generated_iota_infer_nf_convertible
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (live :
      DIndGArtifactLiveSRCoreObligations evaluator sig)
    (cert :
      DIndGArtifactNFInferCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
      ∃ rawDecl : DIndGArtifactDecl,
        contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_infer_nf_convertible_of_observation_infer_complete_with_contract_source
    gateSucceeds translation live.evaluator_sound live.transport
    live.infer_complete cert termTranslates

/-- Readout-expanded form of the universal generated-iota theorem.  This spells
out the exact executable observations named by the kernel artifact:
`rawNf = nf sig rawTerm`, `rawSourceInfer = infer sig [] rawTerm`, and
`rawTargetInfer = infer sig [] rawNf`.  The proof immediately packages those
observations as the canonical conv-free certificate and enters the universal
theorem above. -/
theorem kernel_signature_lf_indexed_universal_generated_iota_infer_nf_convertible_of_readouts
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (live :
      DIndGArtifactLiveSRCoreObligations evaluator sig)
    (nfReadout :
      evaluator.nf sig rawTerm rawNf)
    (sourceInferReadout :
      evaluator.infer sig rawTerm rawSourceInfer)
    (targetInferReadout :
      evaluator.infer sig rawNf rawTargetInfer)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
      ∃ rawDecl : DIndGArtifactDecl,
        contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm rawNf ∧
          evaluator.infer sig rawTerm rawSourceInfer ∧
          evaluator.infer sig rawNf rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  let cert : DIndGArtifactNFInferCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout }
  exact
    kernel_signature_lf_indexed_universal_generated_iota_infer_nf_convertible
      gateSucceeds translation live cert termTranslates

/-- Public `sr-ok` theorem through the live conv-free SR-core obligations.
The proof opens the artifact's hidden `nf`/two-`infer` readouts from `sr-ok`,
then obtains declaration-side convertibility from subject reduction plus
algorithmic-`infer` completeness.  The final artifact `conv` readout is kept
only to reconstruct the original `sr-ok` transcript; it is not the source of
the Lean convertibility conclusion. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_live_sr_core_with_contract_source
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (live :
      DIndGArtifactLiveSRCoreObligations evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
        ∃ rawDecl : DIndGArtifactDecl,
          contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let srCert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  let nfCert : DIndGArtifactNFInferCert evaluator sig rawTerm :=
    DIndGArtifactNFInferCert.ofSROKCert srCert
  rcases kernel_signature_lf_indexed_infer_nf_convertible_of_observation_infer_complete_with_contract_source
      gateSucceeds translation live.evaluator_sound live.transport live.infer_complete
      nfCert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract, rawDecl,
      hContractMem, hRawDeclMem, hSupports,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hIota, hNfJustification,
      hNfReadout, hSourceInferReadout, hTargetInferReadout,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  have hSrOkWithReadouts :
      evaluator.srOkWithReadouts
        sig rawTerm rawNf rawSourceInfer rawTargetInfer :=
    ⟨hNfReadout, hSourceInferReadout, hTargetInferReadout, convReadout⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract, rawDecl,
      hContractMem,
      hRawDeclMem,
      hSupports,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      ⟨rawNf, rawSourceInfer, rawTargetInfer, hSrOkWithReadouts⟩,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- `sr-ok` certificate wrapper for the local-coherence theorem.  This routes an
already extracted final artifact `conv` readout through `conv_sound`; it is
therefore a replay adapter, not the primary conv-free SR core. -/
theorem kernel_signature_lf_indexed_infer_nf_convertible_of_sr_ok_cert_conv_sound
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.nf sig rawTerm cert.rawNf ∧
          evaluator.infer sig rawTerm cert.rawSourceInfer ∧
          evaluator.infer sig cert.rawNf cert.rawTargetInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_infer_nf_convertible_of_observation_local_coherence
    gateSucceeds translation evaluatorSound transport
    (DIndGArtifactNFInferCert.ofSROKCert cert)
    (DIndGArtifactSROKCert.targetInferCoherenceOfConvSoundness
      cert evaluatorSound)
    termTranslates

/-- Local readout form of `kernel_signature_lf_indexed_v0.metta`'s `sr-ok`
equation.  This is the exact per-run artifact object the runtime-generic extractor
must produce: observed `nf`/`infer`/`conv` facts, translations of those
observations, and the resolved generated-iota classification of the observed
normal form. -/
theorem kernel_signature_lf_indexed_sr_ok_readout_justified_of_local_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer)
    (localSound :
      DIndGArtifactSRKernelReadout.LocalSoundness readout) :
    ∃ contract : FamilyRecursorDeclContract,
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawTargetInfer targetInfer ∧
        contract ∈ sig.translatedContracts ∧
        DIndGArtifactResolvedIotaStep contract t nfT ∧
        DIndGArtifactNFJustification
          (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
        evaluator.srOkWithReadouts
          sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
        evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
        ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases
      kernel_signature_lf_indexed_nf_preserves_source_infer_of_observation
        gateSucceeds translation
        (DIndGArtifactNFInferReadout.ofSRKernelReadout readout)
        localSound.source_infer_typed with
    ⟨contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hNfReadout, hSourceInferReadout, hTargetInferReadout,
      hSourceTyped, hPreserved⟩
  exact
    ⟨contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      ⟨hNfReadout, hSourceInferReadout, hTargetInferReadout,
        readout.conv_readout⟩,
      readout.raw_sr_ok,
      hSourceTyped,
      hPreserved,
      localSound.target_infer_typed,
      localSound.inferred_types_convertible⟩

/-- Evaluator-soundness wrapper for the local readout theorem.  The proof
derives the per-run soundness object from the global evaluator contract, then
uses the strictly local theorem above. -/
theorem kernel_signature_lf_indexed_sr_ok_readout_justified_of_readout
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm}
    {t nfT sourceInfer targetInfer : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (readout :
      DIndGArtifactSRKernelReadout evaluator sig
        rawTerm rawNf rawSourceInfer rawTargetInfer
        t nfT sourceInfer targetInfer) :
    ∃ contract : FamilyRecursorDeclContract,
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
        DIndGArtifactTermTranslates
          sig.nameTranslates 0 rawTargetInfer targetInfer ∧
        contract ∈ sig.translatedContracts ∧
        DIndGArtifactResolvedIotaStep contract t nfT ∧
        DIndGArtifactNFJustification
          (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
        evaluator.srOkWithReadouts
          sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
        evaluator.srOk sig rawTerm ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
        HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
        ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_sr_ok_readout_justified_of_local_readout
    gateSucceeds translation readout
    (DIndGArtifactSRKernelReadout.localSoundnessOfEvaluatorSoundness
      evaluatorSound readout)

/-- Direct theorem boundary for `kernel_signature_lf_indexed_v0.metta`'s
`sr-ok` equation:

`nft = nf sig t; a = infer sig [] t; b = infer sig [] nft; conv sig a b`.

The raw readouts are fixed by the evidence-producing certificate.  The theorem
returns their Lean translations, the resolved generated-iota classification of
the observed `nf`, the public `sr-ok` proposition, source typing, preservation
for `nf`, target typing, and declaration-side convertibility of the two
artifact `infer` outputs. -/
theorem kernel_signature_lf_indexed_sr_ok_readout_justified
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases DIndGArtifactSROKCert.to_kernel_readout
      evaluatorSound transport cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, readout⟩
  rcases kernel_signature_lf_indexed_sr_ok_readout_justified_of_readout
      gateSucceeds translation evaluatorSound readout with
    ⟨contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Public theorem boundary for the `sr-ok` equation using the exact extraction
contract.  This is the preferred statement of the remaining artifact seam:
once the runtime-generic run is extracted into a strict `SRKernelReadout` plus local
soundness, admission and translation are enough to justify normalization
preserving inference. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_extraction
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (extraction :
      DIndGArtifactSRKernelExtraction evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases extraction.kernel_readout_of_sr_ok srOk termTranslates with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, readout, localSound⟩
  rcases kernel_signature_lf_indexed_sr_ok_readout_justified_of_local_readout
      gateSucceeds translation readout localSound with
    ⟨contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Kernel theorem through the stricter certificate-indexed extractor.  This
variant opens the public `sr-ok` proposition, forms the exact certificate from
those witnesses, and asks the extractor to lower that same certificate.  This
prevents the artifact bridge from proving the public theorem with different
hidden `nf`/`infer` witnesses than the ones exposed by `sr-ok`. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_cert_extraction
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let cert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  rcases certExtraction.kernel_readout_of_cert
      cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, readout⟩
  rcases kernel_signature_lf_indexed_sr_ok_readout_justified_of_readout
      gateSucceeds translation evaluatorSound readout with
    ⟨contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Provenance-enriched theorem through the strict certificate-indexed
extractor.  This is the sharpest public boundary for the artifact `sr-ok`
equation: the public proposition is opened once, the extractor must lower that
same certificate, and the generated-recursor contract is traced back to the raw
DIndG declaration that supplied it. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_cert_extraction_with_contract_source
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (certExtraction :
      DIndGArtifactSROKExtractionSoundness evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
        ∃ rawDecl : DIndGArtifactDecl,
          contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases kernel_signature_lf_indexed_sr_ok_equation_justified_of_cert_extraction
      gateSucceeds translation evaluatorSound certExtraction
      srOk termTranslates with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  rcases translation.contract_sources contract hContractMem with
    ⟨rawDecl, hRawDeclMem, hSupports⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract, rawDecl,
      hContractMem,
      hRawDeclMem,
      hSupports,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Kernel theorem through the exact executable-lowering seam.  Unlike the
older executable-lowering wrapper, the transcript produced here is indexed by
the same certificate opened from `sr-ok`, so the proof cannot justify one set of
hidden `nf`/`infer` witnesses and return another. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_lowering_cert
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExactExecutableSRLowering evaluator sig)
    (cert :
      DIndGArtifactSROKCert evaluator sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ nfT sourceInfer targetInfer : PureTm 0,
      ∃ contract : FamilyRecursorDeclContract,
        DIndGArtifactTermTranslates sig.nameTranslates 0 cert.rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 cert.rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm cert.rawNf cert.rawSourceInfer cert.rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  have metatheory :
      DIndGArtifactMetatheoryReadout
        dindgRawArtifactGate sig
        sig.translatedSpecs sig.translatedContracts :=
    (DIndGRawAdmissionGateSoundness.canonical
      sig sig.translatedSpecs sig.translatedContracts).metatheory_of_gate
        gateSucceeds translation
  exact
    DIndGArtifactExactExecutableSRLowering.typed_generated_iota_sr_of_sig_admitted
      gateSucceeds metatheory lowering cert termTranslates

/-- Public kernel theorem through exact executable lowering.  The public
`sr-ok` proposition is opened inside the proof, converted to a certificate, and
the exact lowering must justify that same certificate. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_lowering_sr_ok
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (lowering :
      DIndGArtifactExactExecutableSRLowering evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
by
  rcases srOk with
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfReadout, sourceInferReadout, targetInferReadout, convReadout⟩
  let cert : DIndGArtifactSROKCert evaluator sig rawTerm :=
    { rawNf := rawNf
      rawSourceInfer := rawSourceInfer
      rawTargetInfer := rawTargetInfer
      nf_readout := nfReadout
      source_infer_readout := sourceInferReadout
      target_infer_readout := targetInferReadout
      conv_readout := convReadout }
  rcases kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_lowering_cert
      gateSucceeds translation lowering cert termTranslates with
    ⟨nfT, sourceInfer, targetInfer, contract,
      hNfTranslates, hSourceTranslates, hTargetTranslates,
      hContractMem, hIota, hNfJustification,
      hSrOkWithReadouts, hSrOk,
      hSourceTyped, hPreserved, hTargetTyped, hConv⟩
  exact
    ⟨rawNf, rawSourceInfer, rawTargetInfer,
      nfT, sourceInfer, targetInfer, contract,
      hNfTranslates,
      hSourceTranslates,
      hTargetTranslates,
      hContractMem,
      hIota,
      hNfJustification,
      hSrOkWithReadouts,
      hSrOk,
      hSourceTyped,
      hPreserved,
      hTargetTyped,
      hConv⟩

/-- Compatibility boundary for `kernel_signature_lf_indexed_v0.metta`'s
propositional `sr-ok` equation using the older final-`conv` replay route:

`nft = nf sig t; a = infer sig [] t; b = infer sig [] nft; conv sig a b`.

This form matches the artifact predicate with the intermediate readouts hidden.
The proof opens those readouts only internally, then returns the exact raw
witnesses, their Lean translations, the generated-iota contract classification,
source typing, preservation across `nf`, target typing, and declaration-side
convertibility.  New callers should use
`kernel_signature_lf_indexed_sr_ok_equation_justified`, which routes through
the live conv-free SR core and returns raw declaration provenance. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified_compat_conv_sound
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (evaluatorSound :
      DIndGArtifactEvaluatorSoundness evaluator sig)
    (transport :
      DIndGArtifactEvaluatorTransport evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          contract ∈ sig.translatedContracts ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_sr_ok_equation_justified_of_exact_nf_infer_conv_sound
    gateSucceeds translation evaluatorSound
    (DIndGArtifactExactNFInferLowering.ofEvaluatorSoundnessTransport
      evaluatorSound transport)
    srOk termTranslates

/-- Preferred public theorem boundary for
`kernel_signature_lf_indexed_v0.metta`'s propositional `sr-ok` equation.

For any raw DIndG artifact signature whose `sig-admitted-with-elims`
gate succeeds, the explicit signature translation plus the live executable
SR-core obligations justify the two runtime-side `infer` readouts
`infer sig CtxNil t` and `infer sig CtxNil (nf sig t)` as declaration-side
convertible Lean types.  The proof routes through subject reduction and
algorithmic-`infer` completeness; the artifact's final `conv` readout is kept
only as part of the public `sr-ok` transcript.  The generated-recursor contract
is also traced back to the raw DIndG declaration that supplied it. -/
theorem kernel_signature_lf_indexed_sr_ok_equation_justified
    {evaluator : DIndGArtifactEvaluator}
    {sig : DIndGArtifactSig}
    {rawTerm : DIndGArtifactTerm}
    {t : PureTm 0}
    (gateSucceeds : dindgRawArtifactGate.sigAdmittedWithElims sig)
    (translation :
      DIndGArtifactSignatureTranslation
        sig sig.translatedSpecs sig.translatedContracts)
    (live :
      DIndGArtifactLiveSRCoreObligations evaluator sig)
    (srOk : evaluator.srOk sig rawTerm)
    (termTranslates :
      DIndGArtifactTermTranslates sig.nameTranslates 0 rawTerm t) :
    ∃ rawNf rawSourceInfer rawTargetInfer : DIndGArtifactTerm,
      ∃ nfT sourceInfer targetInfer : PureTm 0,
        ∃ contract : FamilyRecursorDeclContract,
        ∃ rawDecl : DIndGArtifactDecl,
          contract ∈ sig.translatedContracts ∧
          rawDecl ∈ sig.decls ∧
          DIndGArtifactDecl.supportsContract
            sig.nameTranslates rawDecl contract ∧
          DIndGArtifactTermTranslates sig.nameTranslates 0 rawNf nfT ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawSourceInfer sourceInfer ∧
          DIndGArtifactTermTranslates
            sig.nameTranslates 0 rawTargetInfer targetInfer ∧
          DIndGArtifactResolvedIotaStep contract t nfT ∧
          DIndGArtifactNFJustification
            (envOfSpecs sig.translatedSpecs) t nfT sourceInfer ∧
          evaluator.srOkWithReadouts
            sig rawTerm rawNf rawSourceInfer rawTargetInfer ∧
          evaluator.srOk sig rawTerm ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil t sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT sourceInfer ∧
          HasTypeDecl (envOfSpecs sig.translatedSpecs) .nil nfT targetInfer ∧
          ConvDecl (envOfSpecs sig.translatedSpecs) sourceInfer targetInfer :=
  kernel_signature_lf_indexed_sr_ok_equation_justified_of_live_sr_core_with_contract_source
    gateSucceeds translation live srOk termTranslates

end DIndGRawArtifactCorrespondence

def cicStage3RawNatZeroCtor : DIndGArtifactCtor :=
  { name := `z
    argTel := []
    resultIdx := [] }

def cicStage3RawNatSuccCtor : DIndGArtifactCtor :=
  { name := `s
    argTel := [.con `nat]
    resultIdx := [] }

def cicStage3RawNatDecl : DIndGArtifactDecl :=
  .dindg `nat [] [] [cicStage3RawNatZeroCtor, cicStage3RawNatSuccCtor]

/-- Explicit name bridge between the raw DIndG artifact spelling and the current
Lean declaration/recursor names. -/
def cicStage3RawNameTranslates (raw lean : DeclName) : Prop :=
  (raw = `nat ∧ lean = natRecContract.familyName) ∨
    (raw = `nat.rec ∧ lean = natRecContract.recursorName) ∨
    (raw = `z ∧ lean = natRecZeroIotaObligation.ctorName) ∨
    (raw = `s ∧ lean = natRecSuccIotaObligation.ctorName)

def cicStage3RawArtifactDecls : List DIndGArtifactDecl :=
  [cicStage3RawNatDecl]

theorem cicStage3RawNatDecl_supports_natRecContract :
    DIndGArtifactDecl.supportsContract
      cicStage3RawNameTranslates
      cicStage3RawNatDecl
      natRecContract := by
  refine ⟨?_, ?_, ?_⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact ⟨`nat.rec, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · intro pilot hpilot obligation hobligation
    have hpilot :
        pilot =
          { contract := natRecContract
            obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
            value? := none } := by
      have hsome :
          some pilot =
            some
              { contract := natRecContract
                obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
                value? := none } := by
        rw [← hpilot, generatedRecursorPilot_nat_obligations_no_value]
      cases hsome
      rfl
    subst pilot
    have hobligation :
        obligation = natRecZeroIotaObligation ∨
          obligation = natRecSuccIotaObligation := by
      simpa using hobligation
    rcases hobligation with hzero | hsucc
    · subst obligation
      refine ⟨cicStage3RawNatZeroCtor, ?_, ?_⟩
      · simp
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · subst obligation
      refine ⟨cicStage3RawNatSuccCtor, ?_, ?_⟩
      · simp
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem cicStage3RawArtifactContractSources :
    ∀ contract, contract ∈ [natRecContract] →
      ∃ decl, decl ∈ cicStage3RawArtifactDecls ∧
        DIndGArtifactDecl.supportsContract
          cicStage3RawNameTranslates decl contract := by
  intro contract hmem
  simp at hmem
  subst contract
  exact ⟨cicStage3RawNatDecl, by simp [cicStage3RawArtifactDecls],
    cicStage3RawNatDecl_supports_natRecContract⟩

def cicStage3RawArtifactSig : DIndGArtifactSig :=
  { decls := cicStage3RawArtifactDecls
    nameTranslates := cicStage3RawNameTranslates
    translatedSpecs := cicStage3Specs
    translatedContracts := [natRecContract] }

def cicStage3RawArtifactSignatureTranslation :
    DIndGArtifactSignatureTranslation
      cicStage3RawArtifactSig
      cicStage3Specs
      [natRecContract] where
  specs_eq := rfl
  contracts_eq := rfl
  contract_sources := cicStage3RawArtifactContractSources

def cicStage3RawArtifactGateSucceeds :
    dindgRawArtifactGate.sigAdmittedWithElims
      cicStage3RawArtifactSig :=
  ⟨cicStage3SignatureWellFormed,
    cicStage3RawArtifactContractSources,
    by
      intro contract hmem
      simp [cicStage3RawArtifactSig] at hmem
      subst contract
      exact natRecContract_admitted,
    by
      intro contract hmem
      simp [cicStage3RawArtifactSig] at hmem
      subst contract
      exact cicStage3Type0Type0ResolvedFrontier⟩

/-- Stage-3 instance of the canonical raw admission-gate soundness theorem. -/
def cicStage3RawAdmissionGateSoundness :
    DIndGRawAdmissionGateSoundness
      cicStage3RawArtifactSig
      cicStage3Specs
      [natRecContract] :=
  DIndGRawAdmissionGateSoundness.canonical
    cicStage3RawArtifactSig
    cicStage3Specs
    [natRecContract]

/-- The current Stage-3 raw correspondence obtained through the same admission
gate-soundness seam required by the generic artifact theorem. -/
def cicStage3RawArtifactCorrespondenceViaGateSoundness :
    DIndGRawArtifactCorrespondence
      cicStage3RawArtifactSig
      cicStage3Specs
      [natRecContract] :=
  DIndGRawArtifactCorrespondence.ofGate
    cicStage3RawArtifactGateSucceeds
    cicStage3RawArtifactSignatureTranslation

/-- Current Stage-3 raw artifact correspondence, derived from the raw gate and
signature translation rather than hand-packing the mirror fields. -/
def cicStage3RawArtifactCorrespondence :
    DIndGRawArtifactCorrespondence
      cicStage3RawArtifactSig
      cicStage3Specs
      [natRecContract] :=
  cicStage3RawArtifactCorrespondenceViaGateSoundness

/-- Current Stage-3 artifact correspondence, exposed in the generic form used by
the universal artifact theorem. -/
def cicStage3ArtifactCorrespondence :
    DIndGArtifactCorrespondence
      dindgRawArtifactGate
      cicStage3RawArtifactSig
      cicStage3Specs
      [natRecContract] :=
  cicStage3RawArtifactCorrespondence.toGeneric

/-- Stage-3 CIC guest instantiation of the DIndG artifact admission mirror. -/
def cicStage3SRAdmissionMirror :
    DIndGSRAdmissionMirror cicStage3Specs :=
  DIndGSRAdmissionMirror.ofSignatureWellFormed
    cicStage3SignatureWellFormed

/-- Stage-3 CIC guest instantiation of the full DIndG admission gate for
the currently active generated-recursion contract. -/
def cicStage3DIndGAdmitted :
    DIndGAdmitted cicStage3Specs [natRecContract] :=
  cicStage3ArtifactCorrespondence.toAdmitted

/-- The same Stage-3 admission mirror, produced from the raw admission gate
soundness seam rather than a hand-packed generic correspondence. -/
def cicStage3DIndGAdmittedViaRawGateSoundness :
    DIndGAdmitted cicStage3Specs [natRecContract] :=
  cicStage3RawArtifactCorrespondenceViaGateSoundness.toGeneric.toAdmitted

/-- Clear Stage-3 readout for build-order item 2: the admission mirror is
produced by the raw gate and signature translation, not assumed separately. -/
def cicStage3DIndGAdmittedFromRawGate :
    DIndGAdmitted cicStage3Specs [natRecContract] :=
  cicStage3RawArtifactCorrespondence.toGeneric.toAdmitted

/-- Concrete Stage-3 form of the artifact-level SR conclusion.  This is the
Lean theorem statement that turns a runtime-style `sr-ok` normalization witness
into declaration-side subject reduction for the hosted Stage-3 target
signature. -/
theorem cicStage3_sr_ok_via_declChurchRosser
    {t nfT A : PureTm 0}
    (ht : HasTypeDecl cicStage3DeclEnv .nil t A)
    (hnf : RedStarDecl cicStage3DeclEnv t nfT) :
    HasTypeDecl cicStage3DeclEnv .nil nfT A := by
  have ht' : HasTypeDecl (envOfSpecs cicStage3Specs) .nil t A := by
    simpa [cicStage3DeclEnv] using ht
  have hnf' : RedStarDecl (envOfSpecs cicStage3Specs) t nfT := by
    simpa [cicStage3DeclEnv] using hnf
  have hResult :
      HasTypeDecl (envOfSpecs cicStage3Specs) .nil nfT A :=
    DIndGSRAdmissionMirror.sr_ok_via_declChurchRosser
      cicStage3SRAdmissionMirror
      { source_typed := ht'
        normalizes := hnf' }
  simpa [cicStage3DeclEnv] using hResult

/-- Concrete Stage-3 confluence readout for two runtime-style normalization
paths. -/
theorem cicStage3_normalization_joinable_via_declChurchRosser
    {t nf₁ nf₂ : PureTm 0}
    (h₁ : RedStarDecl cicStage3DeclEnv t nf₁)
    (h₂ : RedStarDecl cicStage3DeclEnv t nf₂) :
    ∃ u : PureTm 0,
      RedStarDecl cicStage3DeclEnv nf₁ u ∧
      RedStarDecl cicStage3DeclEnv nf₂ u := by
  have h₁' : RedStarDecl (envOfSpecs cicStage3Specs) t nf₁ := by
    simpa [cicStage3DeclEnv] using h₁
  have h₂' : RedStarDecl (envOfSpecs cicStage3Specs) t nf₂ := by
    simpa [cicStage3DeclEnv] using h₂
  rcases DIndGSRAdmissionMirror.normalization_joinable_via_declChurchRosser
      cicStage3SRAdmissionMirror h₁' h₂' with ⟨u, hu₁, hu₂⟩
  exact ⟨u, by simpa [cicStage3DeclEnv] using hu₁,
    by simpa [cicStage3DeclEnv] using hu₂⟩

/-- Concrete Stage-3 theorem matching the DIndG `sr-ok` admission gate:
a generated-iota artifact witness under the active Stage-3 admission gate has
its source inferred type preserved by the Lean declaration metatheory. -/
theorem cicStage3_generated_iota_sr_ok_via_artifact_gate
    {t nfT A : PureTm 0}
    (witness :
      DIndGGeneratedIotaArtifactWitness
        cicStage3Specs [natRecContract] t nfT A) :
    HasTypeDecl (envOfSpecs cicStage3Specs) .nil nfT A :=
  DIndGGeneratedIotaArtifactWitness.sr_ok_via_artifact_gate
    cicStage3DIndGAdmitted
    witness

/-- The Stage-3 generated-iota witness always sees the resolved recursor
frontier carried by the DIndG admission gate. -/
theorem cicStage3_generated_iota_frontier_for_witness
    {t nfT A : PureTm 0}
    (witness :
      DIndGGeneratedIotaArtifactWitness
        cicStage3Specs [natRecContract] t nfT A) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage witness.contract :=
  DIndGGeneratedIotaArtifactWitness.frontier_available
    cicStage3DIndGAdmitted
    witness

/-- The Nat/open-successor status is now a named theorem obligation:
the current Stage-3 slice has the resolved generated-recursion frontier, while
the remaining Nat limitation is explicitly isolated rather than hidden inside
the artifact correspondence. -/
theorem cicStage3_nat_open_successor_residual_isolated :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage natRecContract ∧
      natRecContract.recursorName = natRecName ∧
      generatedRecursorContractResolvedIotaObligations natRecContract = [] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A :=
  cicStage3HostedMetatheoryTheoremSlice
    |>.max_type0_type0_resolved_frontier_and_nat_limitation

/-- The Nat/open-successor residual is not a subject-reduction gap: the open
source and target are already typed at a common type. What remains is exactly
the closed declaration-realization boundary recorded by the negated
`ClosedIotaRealizedIn` conjunct. -/
theorem cicStage3_nat_open_successor_preservation_safe_residual :
    (∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract := by
  rcases cicStage3_nat_open_successor_residual_isolated with
    ⟨_hFrontier, _hName, _hResolved, hNotRealized, hTyped⟩
  exact ⟨hTyped, hNotRealized⟩

end Mettapedia.Languages.MeTTa.PureKernel.CICGuestBridge
