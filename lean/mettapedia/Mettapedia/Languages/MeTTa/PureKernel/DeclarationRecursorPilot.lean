import Mettapedia.Languages.MeTTa.PureKernel.DeclarationUnitPilot
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationBoolPilot
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationNatPilot

namespace Mettapedia.Languages.MeTTa.PureKernel.DeclarationRecursorPilot

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationPilotScaffold
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationUnitPilot
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationBoolPilot
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationNatPilot

/-- Minimal declaration-level recursor contract record for the current kernel pilot layer. -/
structure FamilyRecursorDeclContract where
  familyName : DeclName
  recursorName : DeclName
  recursorType : PureTm 0
deriving Repr

def unitRecName : DeclName := `Unit.rec
def boolRecName : DeclName := `Bool.rec
def natRecName : DeclName := `Nat.rec

/-- Pilot executable body for non-dependent `Unit.rec`: `fun _R r _u => r`. -/
def unitRecValue : PureTm 0 :=
  .lam (.lam (.lam (.var (1 : Fin 3))))

/-- Non-dependent Unit recursor shape: `∀ R : U0, R → Unit → R`. -/
def unitRecType : PureTm 0 :=
  .pi .u0
    (.pi (.var 0)
      (.pi (.const unitTyName) (.var 2)))

/-- Non-dependent Bool recursor shape: `∀ R : U0, R → R → Bool → R`. -/
def boolRecType : PureTm 0 :=
  .pi .u0
    (.pi (.var 0)
      (.pi (.var 1)
        (.pi (.const boolTyName) (.var 3))))

/-- Non-dependent Nat step premise shape in context `(R : U0), (base : R)`. -/
def natStepType : PureTm 2 :=
  .pi (.const natTyName)
    (.pi (.var 2) (.var 3))

/-- Non-dependent Nat recursor shape: `∀ R : U0, R → (Nat → R → R) → Nat → R`. -/
def natRecType : PureTm 0 :=
  .pi .u0
    (.pi (.var 0)
      (.pi natStepType
        (.pi (.const natTyName) (.var 3))))

def unitRecContract : FamilyRecursorDeclContract :=
  { familyName := unitTyName, recursorName := unitRecName, recursorType := unitRecType }

def boolRecContract : FamilyRecursorDeclContract :=
  { familyName := boolTyName, recursorName := boolRecName, recursorType := boolRecType }

def natRecContract : FamilyRecursorDeclContract :=
  { familyName := natTyName, recursorName := natRecName, recursorType := natRecType }

theorem unitRecContract_name : unitRecContract.recursorName = `Unit.rec := rfl
theorem boolRecContract_name : boolRecContract.recursorName = `Bool.rec := rfl
theorem natRecContract_name : natRecContract.recursorName = `Nat.rec := rfl

def unitRecSpec : DeclSpec :=
  { name := unitRecName, type := unitRecType, value? := some unitRecValue }

def boolRecSpec : DeclSpec :=
  { name := boolRecName, type := boolRecType }

def natRecSpec : DeclSpec :=
  { name := natRecName, type := natRecType }

def unitRecSpecs : List DeclSpec :=
  unitSpecs ++ [unitRecSpec]

def boolRecSpecs : List DeclSpec :=
  boolSpecs ++ [boolRecSpec]

def natRecSpecs : List DeclSpec :=
  natSpecs ++ [natRecSpec]

def unitRecDeclEnv : DeclEnv := envOfSpecs unitRecSpecs
def boolRecDeclEnv : DeclEnv := envOfSpecs boolRecSpecs
def natRecDeclEnv : DeclEnv := envOfSpecs natRecSpecs

@[simp] theorem typeOf_unitRec :
    typeOf? unitRecDeclEnv unitRecName = some unitRecType := by
  decide

@[simp] theorem typeOf_boolRec :
    typeOf? boolRecDeclEnv boolRecName = some boolRecType := by
  decide

@[simp] theorem typeOf_natRec :
    typeOf? natRecDeclEnv natRecName = some natRecType := by
  decide

theorem hasType_unitRec :
    HasTypeDecl unitRecDeclEnv .nil ((.const unitRecName : PureTm 0)) unitRecType :=
  hasType_const_from_lookup (E := unitRecDeclEnv) (Γ := .nil) (c := unitRecName) (A0 := unitRecType) (by
    simp)

theorem hasType_boolRec :
    HasTypeDecl boolRecDeclEnv .nil ((.const boolRecName : PureTm 0)) boolRecType :=
  hasType_const_from_lookup (E := boolRecDeclEnv) (Γ := .nil) (c := boolRecName) (A0 := boolRecType) (by
    simp)

theorem hasType_natRec :
    HasTypeDecl natRecDeclEnv .nil ((.const natRecName : PureTm 0)) natRecType :=
  hasType_const_from_lookup (E := natRecDeclEnv) (Γ := .nil) (c := natRecName) (A0 := natRecType) (by
    simp)

private theorem boolRecSpecs_hTyped :
    ∀ s ∈ boolRecSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      HasTypeDecl (envOfSpecs boolRecSpecs) .nil (liftClosed v0) (liftClosed s.type) := by
  intro s hs v0 hVal
  simp [boolRecSpecs] at hs
  rcases hs with hs | rfl
  · exact
      boolSpecs_hTyped_in
        (E := envOfSpecs boolRecSpecs)
        (hTrueType := by decide)
        s hs v0 hVal
  · simp [boolRecSpec] at hVal

private theorem boolRecSpecs_hNoSelf :
    ∀ s ∈ boolRecSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      v0 ≠ (.const s.name) := by
  intro s hs v0 hVal
  simp [boolRecSpecs] at hs
  rcases hs with hs | rfl
  · exact boolSpecs_hNoSelf s hs v0 hVal
  · simp [boolRecSpec] at hVal

private def boolRecSpecs_obligations : DeclSpecObligations boolRecSpecs where
  valuesWellTyped := boolRecSpecs_hTyped
  noSelfDelta := boolRecSpecs_hNoSelf

private def boolRecSpecs_signatureWellFormed : SignatureWellFormed boolRecSpecs where
  noShadowing := by decide
  obligations := boolRecSpecs_obligations

theorem boolRecDeclEnv_wellFormed : DeclEnvWellFormed boolRecDeclEnv := by
  unfold boolRecDeclEnv
  exact boolRecSpecs_signatureWellFormed.toDeclEnvWellFormed

theorem boolRecSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible boolSpecs boolRecSpec where
  fresh := by
    simp [boolSpecs, boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec,
      boolRecSpec, boolTyName, boolTrueName, boolFalseName, boolAliasName, boolRecName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, boolRecSpec, boolRecType,
      boolSpecs, boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec,
      boolTyName, boolTrueName, boolFalseName, boolAliasName, boolRecName]
  valueUsesEarlier := by
    intro v0 hVal
    simp [boolRecSpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [boolRecSpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [boolRecSpec] at hVal

theorem boolRecSpecs_prefixWellFormed :
    SignatureWellFormedPrefix boolRecSpecs := by
  refine And.intro boolTySpec_prefixAdmissible ?_
  refine And.intro ?_ ?_
  · simpa [boolRecSpecs, boolSpecs, boolTySpec, boolTrueSpec]
      using boolTrueSpec_prefixAdmissible
  · refine And.intro ?_ ?_
    · simpa [PrefixSignatureWellFormed, boolRecSpecs, boolSpecs, boolTySpec, boolTrueSpec, boolFalseSpec]
        using boolFalseSpec_prefixAdmissible
    · refine And.intro ?_ ?_
      · simpa [PrefixSignatureWellFormed, boolRecSpecs, boolSpecs,
          boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec]
          using boolAliasSpec_prefixAdmissible
      · refine And.intro ?_ trivial
        simpa [PrefixSignatureWellFormed, boolRecSpecs, boolSpecs,
          boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec, boolRecSpec]
          using boolRecSpec_prefixAdmissible

private theorem boolRecSpecs_signatureWellFormed_fromPrefix :
    SignatureWellFormed boolRecSpecs :=
  SignatureWellFormed.ofPrefix boolRecSpecs_prefixWellFormed boolRecSpecs_obligations

private theorem natRecSpecs_hTyped :
    ∀ s ∈ natRecSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      HasTypeDecl (envOfSpecs natRecSpecs) .nil (liftClosed v0) (liftClosed s.type) := by
  intro s hs v0 hVal
  simp [natRecSpecs] at hs
  rcases hs with hs | rfl
  · exact
      natSpecs_hTyped_in
        (E := envOfSpecs natRecSpecs)
        (hZeroType := by decide)
        s hs v0 hVal
  · simp [natRecSpec] at hVal

private theorem natRecSpecs_hNoSelf :
    ∀ s ∈ natRecSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      v0 ≠ (.const s.name) := by
  intro s hs v0 hVal
  simp [natRecSpecs] at hs
  rcases hs with hs | rfl
  · exact natSpecs_hNoSelf s hs v0 hVal
  · simp [natRecSpec] at hVal

private def natRecSpecs_obligations : DeclSpecObligations natRecSpecs where
  valuesWellTyped := natRecSpecs_hTyped
  noSelfDelta := natRecSpecs_hNoSelf

private def natRecSpecs_signatureWellFormed : SignatureWellFormed natRecSpecs where
  noShadowing := by decide
  obligations := natRecSpecs_obligations

theorem natRecDeclEnv_wellFormed : DeclEnvWellFormed natRecDeclEnv := by
  unfold natRecDeclEnv
  exact natRecSpecs_signatureWellFormed.toDeclEnvWellFormed

theorem natRecSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible natSpecs natRecSpec where
  fresh := by
    simp [natSpecs, natTySpec, natZeroSpec, natSuccSpec, natAliasSpec,
      natRecSpec, natTyName, natZeroName, natSuccName, natAliasName, natRecName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, natRecSpec, natRecType, natStepType,
      natSpecs, natTySpec, natZeroSpec, natSuccSpec, natAliasSpec,
      natTyName, natZeroName, natSuccName, natAliasName, natRecName]
  valueUsesEarlier := by
    intro v0 hVal
    simp [natRecSpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [natRecSpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [natRecSpec] at hVal

theorem natRecSpecs_prefixWellFormed :
    SignatureWellFormedPrefix natRecSpecs := by
  refine And.intro natTySpec_prefixAdmissible ?_
  refine And.intro ?_ ?_
  · simpa [natRecSpecs, natSpecs, natTySpec, natZeroSpec]
      using natZeroSpec_prefixAdmissible
  · refine And.intro ?_ ?_
    · simpa [PrefixSignatureWellFormed, natRecSpecs, natSpecs, natTySpec, natZeroSpec, natSuccSpec]
        using natSuccSpec_prefixAdmissible
    · refine And.intro ?_ ?_
      · simpa [PrefixSignatureWellFormed, natRecSpecs, natSpecs,
          natTySpec, natZeroSpec, natSuccSpec, natAliasSpec]
          using natAliasSpec_prefixAdmissible
      · refine And.intro ?_ trivial
        simpa [PrefixSignatureWellFormed, natRecSpecs, natSpecs,
          natTySpec, natZeroSpec, natSuccSpec, natAliasSpec, natRecSpec]
          using natRecSpec_prefixAdmissible

private theorem natRecSpecs_signatureWellFormed_fromPrefix :
    SignatureWellFormed natRecSpecs :=
  SignatureWellFormed.ofPrefix natRecSpecs_prefixWellFormed natRecSpecs_obligations

@[simp] theorem valueOf_unitRec :
    valueOf? unitRecDeclEnv unitRecName = some unitRecValue := by
  decide

/-- `Unit.rec` executable body is well-typed at its declaration type. -/
theorem hasType_unitRecValue :
    HasTypeDecl unitRecDeclEnv .nil unitRecValue unitRecType := by
  unfold unitRecValue unitRecType
  refine .lam_intro ?_
  refine .lam_intro ?_
  refine .lam_intro ?_
  exact .var (i := (1 : Fin 3))

theorem hasType_unitRecValue_inUnitPrefix :
    HasTypeDecl (envOfSpecs unitSpecs) .nil unitRecValue unitRecType := by
  unfold unitRecValue unitRecType
  refine .lam_intro ?_
  refine .lam_intro ?_
  refine .lam_intro ?_
  exact .var (i := (1 : Fin 3))

/-- Generic closed checked-step for unfolding `Unit.rec` via declaration semantics. -/
theorem unitRec_checked_delta :
    ∃ A : PureTm 0,
      HasTypeDecl unitRecDeclEnv .nil ((.const unitRecName : PureTm 0)) A ∧
      RedDecl unitRecDeclEnv ((.const unitRecName : PureTm 0)) unitRecValue ∧
      HasTypeDecl unitRecDeclEnv .nil unitRecValue A := by
  simpa using
    (checked_delta_step_closed_of_typed_value
      (E := unitRecDeclEnv)
      (c := unitRecName)
      (A0 := unitRecType)
      (v0 := unitRecValue)
      (by simp)
      (by simp)
      hasType_unitRecValue)

@[simp] theorem typeOf_unitTy_inRecEnv :
    typeOf? unitRecDeclEnv unitTyName = some .u0 := by
  decide

@[simp] theorem typeOf_unitCtor_inRecEnv :
    typeOf? unitRecDeclEnv unitCtorName = some (.const unitTyName) := by
  decide

@[simp] theorem typeOf_unitAlias_inRecEnv :
    typeOf? unitRecDeclEnv unitAliasName = some (.const unitTyName) := by
  decide

@[simp] theorem valueOf_unitAlias_inRecEnv :
    valueOf? unitRecDeclEnv unitAliasName = some (.const unitCtorName) := by
  decide

theorem hasType_unitTy_inRecEnv :
    HasTypeDecl unitRecDeclEnv .nil ((.const unitTyName : PureTm 0)) .u0 :=
  hasType_const_from_lookup (E := unitRecDeclEnv) (Γ := .nil) (c := unitTyName) (A0 := .u0) (by
    simp)

theorem hasType_unitCtor_inRecEnv :
    HasTypeDecl unitRecDeclEnv .nil ((.const unitCtorName : PureTm 0)) (.const unitTyName) :=
  hasType_const_from_lookup (E := unitRecDeclEnv) (Γ := .nil) (c := unitCtorName) (A0 := .const unitTyName) (by
    simp)

theorem hasType_unitAlias_inRecEnv :
    HasTypeDecl unitRecDeclEnv .nil ((.const unitAliasName : PureTm 0)) (.const unitTyName) :=
  hasType_const_from_lookup (E := unitRecDeclEnv) (Γ := .nil) (c := unitAliasName) (A0 := .const unitTyName) (by
    simp)

private theorem unitRecSpecs_hTyped :
    ∀ s ∈ unitRecSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      HasTypeDecl (envOfSpecs unitRecSpecs) .nil (liftClosed v0) (liftClosed s.type) := by
  intro s hs v0 hVal
  simp [unitRecSpecs] at hs
  rcases hs with hs | rfl
  · exact
      unitSpecs_hTyped_in
        (E := envOfSpecs unitRecSpecs)
        (hCtorType := by decide)
        s hs v0 hVal
  · have hv : v0 = unitRecValue := by
      simpa [unitRecSpec] using hVal.symm
    subst hv
    simpa [liftClosed_zero] using hasType_unitRecValue

private theorem unitRecSpecs_hNoSelf :
    ∀ s ∈ unitRecSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      v0 ≠ (.const s.name) := by
  intro s hs v0 hVal
  simp [unitRecSpecs] at hs
  rcases hs with hs | rfl
  · exact unitSpecs_hNoSelf s hs v0 hVal
  · have hv : v0 = unitRecValue := by
      simpa [unitRecSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : unitRecValue ≠ (.const unitRecName) := by
      decide
    exact hNe hEq

private def unitRecSpecs_obligations : DeclSpecObligations unitRecSpecs where
  valuesWellTyped := unitRecSpecs_hTyped
  noSelfDelta := unitRecSpecs_hNoSelf

private def unitRecSpecs_signatureWellFormed : SignatureWellFormed unitRecSpecs where
  noShadowing := by decide
  obligations := unitRecSpecs_obligations

theorem unitRecDeclEnv_wellFormed : DeclEnvWellFormed unitRecDeclEnv := by
  unfold unitRecDeclEnv
  exact unitRecSpecs_signatureWellFormed.toDeclEnvWellFormed

theorem unitRecSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible unitSpecs unitRecSpec where
  fresh := by
    simp [unitSpecs, unitTySpec, unitCtorSpec, unitAliasSpec,
      unitRecSpec, unitTyName, unitCtorName, unitAliasName, unitRecName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, unitRecSpec, unitRecType,
      unitSpecs, unitTySpec, unitCtorSpec, unitAliasSpec,
      unitTyName, unitCtorName, unitAliasName, unitRecName]
  valueUsesEarlier := by
    intro v0 hVal
    have hv : v0 = unitRecValue := by
      simpa [unitRecSpec] using hVal.symm
    subst hv
    simp [UsesOnlyDeclNamesFrom, prefixNames, unitRecValue, unitSpecs,
      unitTySpec, unitCtorSpec, unitAliasSpec]
  valueWellTyped := by
    intro v0 hVal
    have hv : v0 = unitRecValue := by
      simpa [unitRecSpec] using hVal.symm
    subst hv
    simpa [liftClosed_zero] using hasType_unitRecValue_inUnitPrefix
  noSelfDelta := by
    intro v0 hVal
    have hv : v0 = unitRecValue := by
      simpa [unitRecSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : unitRecValue ≠ (.const unitRecName) := by
      decide
    exact hNe hEq

theorem unitRecSpecs_prefixWellFormed :
    SignatureWellFormedPrefix unitRecSpecs := by
  refine And.intro unitTySpec_prefixAdmissible ?_
  refine And.intro ?_ ?_
  · simpa [unitRecSpecs, unitSpecs, unitTySpec, unitCtorSpec]
      using unitCtorSpec_prefixAdmissible
  · refine And.intro ?_ ?_
    · simpa [PrefixSignatureWellFormed, unitRecSpecs, unitSpecs, unitTySpec, unitCtorSpec, unitAliasSpec]
        using unitAliasSpec_prefixAdmissible
    · refine And.intro ?_ trivial
      simpa [PrefixSignatureWellFormed, unitRecSpecs, unitSpecs,
        unitTySpec, unitCtorSpec, unitAliasSpec, unitRecSpec]
        using unitRecSpec_prefixAdmissible

private theorem unitRecSpecs_signatureWellFormed_fromPrefix :
    SignatureWellFormed unitRecSpecs :=
  SignatureWellFormed.ofPrefix unitRecSpecs_prefixWellFormed unitRecSpecs_obligations

def unitRecTerm : PureTm 0 := .const unitRecName
def unitTyTerm : PureTm 0 := .const unitTyName
def unitCtorTerm : PureTm 0 := .const unitCtorName

/-- Closed Unit recursor application used for the first iota-style pilot witness:
`((Unit.rec Unit) Unit.unit) Unit.unit`. -/
def unitRecOnCtor : PureTm 0 :=
  .app (.app (.app unitRecTerm unitTyTerm) unitCtorTerm) unitCtorTerm

def unitRecAfterTy : PureTm 0 := .lam (.lam (.var (1 : Fin 2)))
def unitRecAfterTyCtor : PureTm 0 := .lam (.const unitCtorName)

private theorem redDecl_to_star {E : DeclEnv} {t u : PureTm n} (h : RedDecl E t u) :
    RedStarDecl E t u :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl h

/-- First iota-style computation witness in the declaration-aware layer:
`((Unit.rec Unit) Unit.unit) Unit.unit ↠ Unit.unit`
via δ-unfolding of `Unit.rec` plus β-reduction. -/
theorem unitRecOnCtor_iota :
    RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm := by
  let t0 : PureTm 0 := unitRecOnCtor
  let t1 : PureTm 0 := .app (.app (.app unitRecValue unitTyTerm) unitCtorTerm) unitCtorTerm
  let t2 : PureTm 0 := .app (.app unitRecAfterTy unitCtorTerm) unitCtorTerm
  let t3 : PureTm 0 := .app unitRecAfterTyCtor unitCtorTerm
  let t4 : PureTm 0 := unitCtorTerm

  have h01 : RedDecl unitRecDeclEnv t0 t1 := by
    exact .congAppFun (.congAppFun (.congAppFun (.deltaConst (E := unitRecDeclEnv) (c := unitRecName)
      (v := unitRecValue) valueOf_unitRec)))
  have h12 : RedDecl unitRecDeclEnv t1 t2 := by
    exact .congAppFun (.congAppFun (.core (.betaPi (.lam (.lam (.var (1 : Fin 3)))) unitTyTerm)))
  have h23 : RedDecl unitRecDeclEnv t2 t3 := by
    exact .congAppFun (.core (.betaPi (.lam (.var (1 : Fin 2))) unitCtorTerm))
  have h34 : RedDecl unitRecDeclEnv t3 t4 := by
    exact .core (.betaPi (.const unitCtorName) unitCtorTerm)

  have hs01 : RedStarDecl unitRecDeclEnv t0 t1 := redDecl_to_star h01
  have hs12 : RedStarDecl unitRecDeclEnv t1 t2 := redDecl_to_star h12
  have hs23 : RedStarDecl unitRecDeclEnv t2 t3 := redDecl_to_star h23
  have hs34 : RedStarDecl unitRecDeclEnv t3 t4 := redDecl_to_star h34
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans
      (Relation.ReflTransGen.trans hs01 hs12)
      hs23)
    hs34

theorem hasType_unitRecOnCtor :
    HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName) := by
  unfold unitRecOnCtor unitRecTerm unitTyTerm unitCtorTerm
  exact .app_elim
    (.app_elim
      (.app_elim hasType_unitRec hasType_unitTy_inRecEnv)
      hasType_unitCtor_inRecEnv)
    hasType_unitCtor_inRecEnv

/-- The Unit pilot run is now wired through the generic declaration-aware
star-preservation service boundary from `DeclarationSemantics`. -/
theorem hasType_unitRecOnCtor_result_of_preservation
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName) := by
  exact redStarDecl_preserves_type_of_injective
    (E := unitRecDeclEnv)
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (hWf := unitRecDeclEnv_wellFormed)
    (ht := hasType_unitRecOnCtor)
    (hs := unitRecOnCtor_iota)

/-- Preservation-backed pilot package: the target typing is obtained through
the generic declaration-aware star-preservation service. -/
theorem unitRecOnCtor_preserves_type_to_result_of_preservation
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName) ∧
      RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm ∧
      HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName) := by
  exact
    ⟨hasType_unitRecOnCtor, unitRecOnCtor_iota,
      hasType_unitRecOnCtor_result_of_preservation
        (piInjective := piInjective)
        (sigmaInjective := sigmaInjective)⟩

/-- Minimal env-aware preservation witness for the first iota-style recursor run. -/
theorem unitRecOnCtor_preserves_type_to_result :
    HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName) ∧
      RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm ∧
      HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName) := by
  exact ⟨hasType_unitRecOnCtor, unitRecOnCtor_iota, hasType_unitCtor_inRecEnv⟩

end Mettapedia.Languages.MeTTa.PureKernel.DeclarationRecursorPilot
