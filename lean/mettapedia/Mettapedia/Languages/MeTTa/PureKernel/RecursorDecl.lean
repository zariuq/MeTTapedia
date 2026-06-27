import Mettapedia.Languages.MeTTa.PureKernel.UnitDecl
import Mettapedia.Languages.MeTTa.PureKernel.BoolDecl
import Mettapedia.Languages.MeTTa.PureKernel.NatDecl

namespace Mettapedia.Languages.MeTTa.PureKernel.RecursorDecl

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec
open Mettapedia.Languages.MeTTa.PureKernel.UnitDecl
open Mettapedia.Languages.MeTTa.PureKernel.BoolDecl
open Mettapedia.Languages.MeTTa.PureKernel.NatDecl

/-- Minimal declaration-level recursor contract record for the current kernel pilot layer. -/
structure FamilyRecursorDeclContract where
  familyName : DeclName
  recursorName : DeclName
  recursorType : PureTm 0
deriving DecidableEq, Repr

structure RecursorIotaObligation where
  familyName : DeclName
  recursorName : DeclName
  ctorName : DeclName
  generatedFrom : List DeclName
  sourceShape : String
  targetShape : String
deriving DecidableEq, Repr

structure GeneratedRecursorPilot where
  contract : FamilyRecursorDeclContract
  obligations : List RecursorIotaObligation
  value? : Option (PureTm 0)
deriving DecidableEq, Repr

structure GeneratedClosedIotaRule where
  obligation : RecursorIotaObligation
  source : PureTm 0
  target : PureTm 0
deriving DecidableEq, Repr

/-- Smallest generic extension beyond closed rules: a one-binder iota rule
that can be instantiated into a family of closed steps. The current live
frontier (`Nat.rec` successor) is exactly of this shape. -/
structure GeneratedUnaryOpenIotaRule where
  obligation : RecursorIotaObligation
  ctx : Ctx 1
  source : PureTm 1
  target : PureTm 1
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

@[simp] theorem typeOf_natTy_inRecEnv :
    typeOf? natRecDeclEnv natTyName = some .u0 := by
  decide

@[simp] theorem typeOf_natZero_inRecEnv :
    typeOf? natRecDeclEnv natZeroName = some (.const natTyName) := by
  decide

@[simp] theorem typeOf_natSucc_inRecEnv :
    typeOf? natRecDeclEnv natSuccName = some (.pi (.const natTyName) (.const natTyName)) := by
  decide

@[simp] theorem typeOf_natAlias_inRecEnv :
    typeOf? natRecDeclEnv natAliasName = some (.const natTyName) := by
  decide

@[simp] theorem valueOf_natTy_inRecEnv :
    valueOf? natRecDeclEnv natTyName = none := by
  decide

@[simp] theorem valueOf_natZero_inRecEnv :
    valueOf? natRecDeclEnv natZeroName = none := by
  decide

@[simp] theorem valueOf_natSucc_inRecEnv :
    valueOf? natRecDeclEnv natSuccName = none := by
  decide

@[simp] theorem valueOf_natRec_inRecEnv :
    valueOf? natRecDeclEnv natRecName = none := by
  decide

@[simp] theorem valueOf_natAlias_inRecEnv :
    valueOf? natRecDeclEnv natAliasName = some (.const natZeroName) := by
  decide

@[simp] theorem hasType_natTy_inRecEnv :
    HasTypeDecl natRecDeclEnv .nil ((.const natTyName : PureTm 0)) .u0 :=
  hasType_const_from_lookup (E := natRecDeclEnv) (Γ := .nil) (c := natTyName) (A0 := .u0) (by
    simp)

@[simp] theorem hasType_natZero_inRecEnv :
    HasTypeDecl natRecDeclEnv .nil ((.const natZeroName : PureTm 0)) (.const natTyName) :=
  hasType_const_from_lookup (E := natRecDeclEnv) (Γ := .nil) (c := natZeroName) (A0 := .const natTyName) (by
    simp)

@[simp] theorem hasType_natSucc_inRecEnv :
    HasTypeDecl natRecDeclEnv .nil
      ((.const natSuccName : PureTm 0))
      (.pi (.const natTyName) (.const natTyName)) :=
  hasType_const_from_lookup
    (E := natRecDeclEnv) (Γ := .nil) (c := natSuccName) (A0 := .pi (.const natTyName) (.const natTyName)) (by
      simp)

@[simp] theorem hasType_natAlias_inRecEnv :
    HasTypeDecl natRecDeclEnv .nil ((.const natAliasName : PureTm 0)) (.const natTyName) :=
  hasType_const_from_lookup (E := natRecDeclEnv) (Γ := .nil) (c := natAliasName) (A0 := .const natTyName) (by
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

theorem natRecSpecs_signatureWellFormed_current_gate :
    SignatureWellFormed natRecSpecs :=
  natRecSpecs_signatureWellFormed_fromPrefix

/-- The current Nat recursor declaration pilot lies in the checked signature
fragment. Once declaration-aware `Pi`/`Sigma` injectivity is supplied for this
environment, the generic star-preservation service proves typing preservation
for every declaration-aware reduction sequence. This keeps the current theorem
honest while the stronger global injectivity/confluence story remains open. -/
theorem natRecDeclEnv_redStarDecl_preserves_type_of_injective
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl natRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl natRecDeclEnv A A' ∧ ConvDecl natRecDeclEnv B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl natRecDeclEnv (.sigma A B) (.sigma A' B') →
          ConvDecl natRecDeclEnv A A' ∧ ConvDecl natRecDeclEnv B B')
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl natRecDeclEnv Γ t A)
    (hs : RedStarDecl natRecDeclEnv t u) :
    HasTypeDecl natRecDeclEnv Γ u A := by
  unfold natRecDeclEnv
  exact natRecSpecs_signatureWellFormed.redStarDecl_preserves_type_of_injective
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (ht := ht)
    (hs := hs)

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
    simpa [liftClosed_zero, unitRecSpec, unitRecDeclEnv] using hasType_unitRecValue

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
    simpa [liftClosed_zero, unitRecSpec] using hasType_unitRecValue_inUnitPrefix
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

theorem unitRecSpecs_signatureWellFormed_current_gate :
    SignatureWellFormed unitRecSpecs :=
  unitRecSpecs_signatureWellFormed_fromPrefix

def unitRecTerm : PureTm 0 := .const unitRecName
def unitTyTerm : PureTm 0 := .const unitTyName
def unitCtorTerm : PureTm 0 := .const unitCtorName

@[simp] theorem inst0_unitTy_unitRecTypeCod :
    inst0 unitTyTerm (.pi (.var 0) (.pi (.const unitTyName) (.var 2))) =
      (.pi (.const unitTyName) (.pi (.const unitTyName) (.const unitTyName))) := by
  rfl

@[simp] theorem liftSub_liftSub_subst0_unitTy_two :
    liftSub (liftSub (subst0 unitTyTerm)) 2 = (.const unitTyName) := by
  rfl

@[simp] theorem inst0_unitCtor_unitRecBaseCod :
    inst0 unitCtorTerm (.pi (.const unitTyName) (.const unitTyName)) =
      (.pi (.const unitTyName) (.const unitTyName)) := by
  rfl

@[simp] theorem inst0_unitCtor_unitTy :
    inst0 unitCtorTerm (.const unitTyName) = (.const unitTyName) := by
  rfl

/-- Closed Unit recursor application used for the first iota-style pilot witness:
`((Unit.rec Unit) Unit.unit) Unit.unit`. -/
def unitRecOnCtor : PureTm 0 :=
  .app (.app (.app unitRecTerm unitTyTerm) unitCtorTerm) unitCtorTerm

def natZeroTerm : PureTm 0 := .const natZeroName
def natSuccTerm : PureTm 0 := .const natSuccName
def natRecTerm : PureTm 0 := .const natRecName

def natRecStepSuccValue : PureTm 0 :=
  .lam (.lam (.app (.const natSuccName) (.var (0 : Fin 2))))

def natRecZeroClosedSource : PureTm 0 :=
  .app (.app (.app (.app natRecTerm (.const natTyName)) natZeroTerm) natRecStepSuccValue) natZeroTerm

def natRecZeroClosedTarget : PureTm 0 :=
  natZeroTerm

def natRecSuccOpenCtx : Ctx 1 :=
  .snoc .nil (.const natTyName)

def natRecSuccOpenArg : PureTm 1 :=
  .app (.const natSuccName) (.var (0 : Fin 1))

def natRecSuccOpenSource : PureTm 1 :=
  .app
    (.app
      (.app
        (.app (.const natRecName) (.const natTyName))
        (.const natZeroName))
      (rename wk natRecStepSuccValue))
    natRecSuccOpenArg

def natRecSuccOpenTarget : PureTm 1 :=
  .app (.const natSuccName)
    (.app
      (.app
        (.app
          (.app (.const natRecName) (.const natTyName))
          (.const natZeroName))
        (rename wk natRecStepSuccValue))
      (.var (0 : Fin 1)))

theorem hasType_natRecStepSuccValue :
    HasTypeDecl natRecDeclEnv .nil natRecStepSuccValue
      (.pi (.const natTyName) (.pi (.const natTyName) (.const natTyName))) := by
  unfold natRecStepSuccValue
  refine .lam_intro ?_
  refine .lam_intro ?_
  have hSucc :
      HasTypeDecl natRecDeclEnv
        (.snoc (.snoc .nil (.const natTyName)) (.const natTyName))
        (.const natSuccName)
        (.pi (.const natTyName) (.const natTyName)) :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := .snoc (.snoc .nil (.const natTyName)) (.const natTyName))
      (c := natSuccName)
      (A0 := .pi (.const natTyName) (.const natTyName))
      (by simp)
  have hVar :
      HasTypeDecl natRecDeclEnv
        (.snoc (.snoc .nil (.const natTyName)) (.const natTyName))
        (.var (0 : Fin 2))
        (.const natTyName) := by
    simpa [Context.lookup_snoc_zero, Renaming.rename] using
      (HasTypeDecl.var
        (E := natRecDeclEnv)
        (Γ := .snoc (.snoc .nil (.const natTyName)) (.const natTyName))
        (i := (0 : Fin 2)))
  simpa [inst0, subst] using
    (HasTypeDecl.app_elim
      (Γ := (.snoc (.snoc .nil (.const natTyName)) (.const natTyName)))
      (f := (.const natSuccName))
      (a := (.var (0 : Fin 2)))
      (A := (.const natTyName))
      (B := (.const natTyName))
      hSucc
      hVar)

theorem hasType_natRecZeroClosedSource :
    HasTypeDecl natRecDeclEnv .nil natRecZeroClosedSource (.const natTyName) := by
  unfold natRecZeroClosedSource natRecTerm natZeroTerm
  exact .app_elim
    (.app_elim
      (.app_elim
        (.app_elim hasType_natRec hasType_natTy_inRecEnv)
        hasType_natZero_inRecEnv)
      hasType_natRecStepSuccValue)
    hasType_natZero_inRecEnv

theorem hasType_natRecSuccOpenArg :
    HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenArg (.const natTyName) := by
  unfold natRecSuccOpenArg natRecSuccOpenCtx
  have hSucc :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natSuccName)
        (.pi (.const natTyName) (.const natTyName)) :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natSuccName)
      (A0 := .pi (.const natTyName) (.const natTyName))
      (by simp)
  have hVar :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.var (0 : Fin 1))
        (.const natTyName) := by
    simpa [Context.lookup_snoc_zero, Renaming.rename] using
      (HasTypeDecl.var
        (E := natRecDeclEnv)
        (Γ := (.snoc .nil (.const natTyName)))
        (i := (0 : Fin 1)))
  simpa [inst0, subst] using
    (HasTypeDecl.app_elim
      (Γ := (.snoc .nil (.const natTyName)))
      (f := (.const natSuccName))
      (a := (.var (0 : Fin 1)))
      (A := (.const natTyName))
      (B := (.const natTyName))
      hSucc
      hVar)

theorem hasType_natRecSuccOpenSource :
    HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource (.const natTyName) := by
  unfold natRecSuccOpenSource natRecSuccOpenCtx
  have hRec :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natRecName)
        (liftClosed natRecType) :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natRecName)
      (A0 := natRecType)
      (by simp)
  have hTy :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natTyName)
        .u0 :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natTyName)
      (A0 := .u0)
      (by simp)
  have hZero :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natZeroName)
        (.const natTyName) :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natZeroName)
      (A0 := .const natTyName)
      (by simp)
  have hStep :=
    weakening_decl
      (E := natRecDeclEnv)
      (Γ := .nil)
      (U := (.const natTyName))
      (ht := hasType_natRecStepSuccValue)
  exact .app_elim
    (.app_elim
      (.app_elim
        (.app_elim hRec hTy)
        hZero)
      hStep)
    hasType_natRecSuccOpenArg

theorem hasType_natRecSuccOpenTarget :
    HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget (.const natTyName) := by
  unfold natRecSuccOpenTarget natRecSuccOpenCtx
  have hSucc :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natSuccName)
        (.pi (.const natTyName) (.const natTyName)) :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natSuccName)
      (A0 := .pi (.const natTyName) (.const natTyName))
      (by simp)
  have hRec :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natRecName)
        (liftClosed natRecType) :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natRecName)
      (A0 := natRecType)
      (by simp)
  have hTy :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natTyName)
        .u0 :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natTyName)
      (A0 := .u0)
      (by simp)
  have hZero :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.const natZeroName)
        (.const natTyName) :=
    hasType_const_from_lookup
      (E := natRecDeclEnv)
      (Γ := (.snoc .nil (.const natTyName)))
      (c := natZeroName)
      (A0 := .const natTyName)
      (by simp)
  have hStep :=
    weakening_decl
      (E := natRecDeclEnv)
      (Γ := .nil)
      (U := (.const natTyName))
      (ht := hasType_natRecStepSuccValue)
  have hVar :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.var (0 : Fin 1))
        (.const natTyName) := by
    simpa [Context.lookup_snoc_zero, Renaming.rename] using
      (HasTypeDecl.var
        (E := natRecDeclEnv)
        (Γ := (.snoc .nil (.const natTyName)))
        (i := (0 : Fin 1)))
  have hRecCall :
      HasTypeDecl natRecDeclEnv
        (.snoc .nil (.const natTyName))
        (.app
          (.app
            (.app
              (.app (.const natRecName) (.const natTyName))
              (.const natZeroName))
            (rename wk natRecStepSuccValue))
          (.var (0 : Fin 1)))
        (.const natTyName) :=
    .app_elim
      (.app_elim
        (.app_elim
          (.app_elim hRec hTy)
          hZero)
        hStep)
      hVar
  simpa [inst0, subst] using
    (HasTypeDecl.app_elim
      (Γ := (.snoc .nil (.const natTyName)))
      (f := (.const natSuccName))
      (a := (.app
          (.app
            (.app
              (.app (.const natRecName) (.const natTyName))
              (.const natZeroName))
          (rename wk natRecStepSuccValue))
        (.var (0 : Fin 1))))
      (A := (.const natTyName))
      (B := (.const natTyName))
      hSucc
      hRecCall)

theorem natRecSuccOpenIotaRule_checked :
    ∃ A : PureTm 1,
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  exact ⟨.const natTyName, hasType_natRecSuccOpenSource, hasType_natRecSuccOpenTarget⟩

def natRecSuccClosedSource (a : PureTm 0) : PureTm 0 :=
  inst0 a natRecSuccOpenSource

def natRecSuccClosedTarget (a : PureTm 0) : PureTm 0 :=
  inst0 a natRecSuccOpenTarget

theorem natRecSuccClosedSource_injective {a b : PureTm 0}
    (h : natRecSuccClosedSource a = natRecSuccClosedSource b) : a = b := by
  unfold natRecSuccClosedSource natRecSuccOpenSource natRecSuccOpenArg inst0 at h
  simp [Substitution.subst] at h
  exact h.2

theorem natRecSuccClosedTarget_ne_closedSource (a b : PureTm 0) :
    natRecSuccClosedTarget a ≠ natRecSuccClosedSource b := by
  intro h
  unfold natRecSuccClosedTarget natRecSuccClosedSource natRecSuccOpenSource
    natRecSuccOpenTarget natRecSuccOpenArg inst0 at h
  simp [Substitution.subst] at h

private theorem ctxMorDecl_natRec_subst0 {a : PureTm 0}
    (ha : HasTypeDecl natRecDeclEnv .nil a (.const NatDecl.natTyName)) :
    CtxMorDecl natRecDeclEnv natRecSuccOpenCtx .nil (subst0 a) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [CtxMorDecl, natRecSuccOpenCtx, lookup_snoc_zero, Substitution.subst,
      Renaming.rename] using ha
  · intro j
    exact Fin.elim0 j

theorem hasType_natRecSuccClosedSource {a : PureTm 0}
    (ha : HasTypeDecl natRecDeclEnv .nil a (.const NatDecl.natTyName)) :
    HasTypeDecl natRecDeclEnv .nil (natRecSuccClosedSource a) (.const NatDecl.natTyName) := by
  unfold natRecSuccClosedSource
  simpa [inst0, Substitution.subst] using
    (typing_subst_decl (E := natRecDeclEnv)
      (Γ := natRecSuccOpenCtx) (Δ := .nil) (σ := subst0 a)
      hasType_natRecSuccOpenSource
      (ctxMorDecl_natRec_subst0 ha))

theorem hasType_natRecSuccClosedTarget {a : PureTm 0}
    (ha : HasTypeDecl natRecDeclEnv .nil a (.const NatDecl.natTyName)) :
    HasTypeDecl natRecDeclEnv .nil (natRecSuccClosedTarget a) (.const NatDecl.natTyName) := by
  unfold natRecSuccClosedTarget
  simpa [inst0, Substitution.subst] using
    (typing_subst_decl (E := natRecDeclEnv)
      (Γ := natRecSuccOpenCtx) (Δ := .nil) (σ := subst0 a)
      hasType_natRecSuccOpenTarget
      (ctxMorDecl_natRec_subst0 ha))

theorem natRecZeroClosedIotaRule_preserves_type_to_result :
    HasTypeDecl natRecDeclEnv .nil natRecZeroClosedSource (.const natTyName) ∧
      HasTypeDecl natRecDeclEnv .nil natRecZeroClosedTarget (.const natTyName) := by
  refine ⟨hasType_natRecZeroClosedSource, ?_⟩
  unfold natRecZeroClosedTarget natZeroTerm
  exact hasType_natZero_inRecEnv

def unitRecAfterTy : PureTm 0 := .lam (.lam (.var (1 : Fin 2)))
def unitRecAfterTyCtor : PureTm 0 := .lam (.const unitCtorName)
def unitRecAfterDelta : PureTm 0 :=
  .app (.app (.app unitRecValue unitTyTerm) unitCtorTerm) unitCtorTerm
def unitRecAfterMotive : PureTm 0 :=
  .app (.app unitRecAfterTy unitCtorTerm) unitCtorTerm
def unitRecAfterBase : PureTm 0 :=
  .app unitRecAfterTyCtor unitCtorTerm

def unitRecOracleTraceTerms : List (PureTm 0) :=
  [unitRecOnCtor, unitRecAfterDelta, unitRecAfterMotive, unitRecAfterBase, unitCtorTerm]

theorem unitRecOracleTraceTerms_length :
    unitRecOracleTraceTerms.length = 5 := rfl

private theorem redDecl_to_star {E : DeclEnv} {t u : PureTm n} (h : RedDecl E t u) :
    RedStarDecl E t u :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl h

private theorem reflTransGen_map
    {α : Sort _} {R S : α → α → Prop}
    (hRS : ∀ {x y : α}, R x y → S x y)
    {x y : α} :
    Relation.ReflTransGen R x y → Relation.ReflTransGen S x y := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih (hRS hyz)

/-- First iota-style computation witness in the declaration-aware layer:
`((Unit.rec Unit) Unit.unit) Unit.unit ↠ Unit.unit`
via δ-unfolding of `Unit.rec` plus β-reduction. -/
theorem unitRecOnCtor_iota :
    RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm := by
  let t0 : PureTm 0 := unitRecOnCtor
  let t1 : PureTm 0 := unitRecAfterDelta
  let t2 : PureTm 0 := unitRecAfterMotive
  let t3 : PureTm 0 := unitRecAfterBase
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

theorem unitTyTerm_type_unique
    {C : PureTm 0}
    (ht : HasTypeDecl unitRecDeclEnv .nil unitTyTerm C) :
    ConvDecl unitRecDeclEnv .u0 C := by
  rcases const_generation ht with ⟨A0, hType, hConv⟩
  have hEq : (.u0 : PureTm 0) = A0 := by
    simpa [unitTyTerm] using hType
  simpa [hEq] using hConv

theorem unitCtorTerm_type_unique
    {C : PureTm 0}
    (ht : HasTypeDecl unitRecDeclEnv .nil unitCtorTerm C) :
    ConvDecl unitRecDeclEnv (.const unitTyName) C := by
  rcases const_generation ht with ⟨A0, hType, hConv⟩
  have hEq : (.const unitTyName : PureTm 0) = A0 := by
    simpa [unitCtorTerm] using hType
  simpa [hEq] using hConv

theorem unitRecTerm_type_unique
    {C : PureTm 0}
    (ht : HasTypeDecl unitRecDeclEnv .nil unitRecTerm C) :
    ConvDecl unitRecDeclEnv unitRecType C := by
  rcases const_generation ht with ⟨A0, hType, hConv⟩
  have hEq : unitRecType = A0 := by
    simpa [unitRecTerm] using hType
  simpa [hEq] using hConv

theorem unitRecOnCtor_type_unique_of_piInjective
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B')
    {C : PureTm 0}
    (ht : HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor C) :
    ConvDecl unitRecDeclEnv (.const unitTyName) C := by
  rcases app_generation_decl ht with ⟨A4, B4, hFun4, _hArg4, hConv4⟩
  rcases app_generation_decl hFun4 with ⟨A3, B3, hFun3, _hArg3, hConv3⟩
  rcases app_generation_decl hFun3 with ⟨A2, B2, hFun2, _hArg2, hConv2⟩
  have hRecConv :
      ConvDecl unitRecDeclEnv unitRecType (.pi A2 B2) :=
    unitRecTerm_type_unique hFun2
  have hB2 :
      ConvDecl unitRecDeclEnv
        (.pi (.var 0) (.pi (.const unitTyName) (.var 2)))
        B2 :=
    (piInjective hRecConv).2
  have hB2inst :
      ConvDecl unitRecDeclEnv
        (inst0 unitTyTerm (.pi (.var 0) (.pi (.const unitTyName) (.var 2))))
        (inst0 unitTyTerm B2) := by
    exact convDecl_subst (E := unitRecDeclEnv) (σ := subst0 unitTyTerm) hB2
  have hPi3' :
      ConvDecl unitRecDeclEnv
        (inst0 unitTyTerm (.pi (.var 0) (.pi (.const unitTyName) (.var 2))))
        (.pi A3 B3) := by
    exact Relation.EqvGen.trans _ _ _ hB2inst hConv2
  have hPi3 :
      ConvDecl unitRecDeclEnv
        (.pi (.const unitTyName) (.pi (.const unitTyName) (.const unitTyName)))
        (.pi A3 B3) :=
    by
      simpa using hPi3'
  have hB3 :
      ConvDecl unitRecDeclEnv
        (.pi (.const unitTyName) (.const unitTyName))
        B3 :=
    (piInjective hPi3).2
  have hB3inst :
      ConvDecl unitRecDeclEnv
        (inst0 unitCtorTerm (.pi (.const unitTyName) (.const unitTyName)))
        (inst0 unitCtorTerm B3) := by
    exact convDecl_subst (E := unitRecDeclEnv) (σ := subst0 unitCtorTerm) hB3
  have hPi4' :
      ConvDecl unitRecDeclEnv
        (inst0 unitCtorTerm (.pi (.const unitTyName) (.const unitTyName)))
        (.pi A4 B4) := by
    exact Relation.EqvGen.trans _ _ _ hB3inst hConv3
  have hPi4 :
      ConvDecl unitRecDeclEnv
        (.pi (.const unitTyName) (.const unitTyName))
        (.pi A4 B4) :=
    by
      simpa using hPi4'
  have hB4 :
      ConvDecl unitRecDeclEnv
        (.const unitTyName)
        B4 :=
    (piInjective hPi4).2
  have hB4inst :
      ConvDecl unitRecDeclEnv
        (inst0 unitCtorTerm (.const unitTyName))
        (inst0 unitCtorTerm B4) := by
    exact convDecl_subst (E := unitRecDeclEnv) (σ := subst0 unitCtorTerm) hB4
  have hRes' :
      ConvDecl unitRecDeclEnv
        (inst0 unitCtorTerm (.const unitTyName))
        C := by
    exact Relation.EqvGen.trans _ _ _ hB4inst hConv4
  simpa using hRes'

theorem hasType_unitRecOnCtor_result_of_pi_only
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B')
    {A : PureTm 0}
    (ht : HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor A) :
    HasTypeDecl unitRecDeclEnv .nil unitCtorTerm A := by
  exact .conv hasType_unitCtor_inRecEnv
    (unitRecOnCtor_type_unique_of_piInjective piInjective ht)

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
  exact unitRecSpecs_signatureWellFormed.redStarDecl_preserves_type_of_injective
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
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

def unitRecCtorIotaObligation : RecursorIotaObligation :=
  { familyName := unitTyName
    recursorName := unitRecName
    ctorName := unitCtorName
    generatedFrom := [unitTyName, unitCtorName, unitRecName]
    sourceShape := "((Unit.rec R) base) Unit.unit"
    targetShape := "base" }

def natRecZeroIotaObligation : RecursorIotaObligation :=
  { familyName := natTyName
    recursorName := natRecName
    ctorName := natZeroName
    generatedFrom := [natTyName, natZeroName, natRecName]
    sourceShape := "(((Nat.rec P) z) step) Nat.zero"
    targetShape := "z" }

def natRecSuccIotaObligation : RecursorIotaObligation :=
  { familyName := natTyName
    recursorName := natRecName
    ctorName := natSuccName
    generatedFrom := [natTyName, natSuccName, natRecName]
    sourceShape := "(((Nat.rec P) z) step) (Nat.succ n)"
    targetShape := "step n ((((Nat.rec P) z) step) n)" }

def natRecSuccUnaryOpenIotaRule : GeneratedUnaryOpenIotaRule :=
  { obligation := natRecSuccIotaObligation
    ctx := natRecSuccOpenCtx
    source := natRecSuccOpenSource
    target := natRecSuccOpenTarget }

def unitRecCtorClosedIotaRule : GeneratedClosedIotaRule :=
  { obligation := unitRecCtorIotaObligation
    source := unitRecOnCtor
    target := unitCtorTerm }

def natRecZeroClosedIotaRule : GeneratedClosedIotaRule :=
  { obligation := natRecZeroIotaObligation
    source := natRecZeroClosedSource
    target := natRecZeroClosedTarget }

theorem unitRecCtorClosedIotaRule_checked :
    ∃ A : PureTm 0,
      HasTypeDecl unitRecDeclEnv .nil unitRecCtorClosedIotaRule.source A ∧
      HasTypeDecl unitRecDeclEnv .nil unitRecCtorClosedIotaRule.target A := by
  refine ⟨.const unitTyName, ?_, ?_⟩
  · simpa [unitRecCtorClosedIotaRule] using unitRecOnCtor_preserves_type_to_result.1
  · simpa [unitRecCtorClosedIotaRule] using unitRecOnCtor_preserves_type_to_result.2.2

theorem unitRecCtorClosedIotaRule_realizes_redStarDecl :
    RedStarDecl unitRecDeclEnv
      unitRecCtorClosedIotaRule.source
      unitRecCtorClosedIotaRule.target := by
  simpa [unitRecCtorClosedIotaRule] using unitRecOnCtor_iota

def generateClosedIotaRule? (obligation : RecursorIotaObligation) :
    Option GeneratedClosedIotaRule :=
  if obligation = unitRecCtorIotaObligation then
    some unitRecCtorClosedIotaRule
  else if obligation = natRecZeroIotaObligation then
    some natRecZeroClosedIotaRule
  else
    none

def generateUnaryOpenIotaRule? (obligation : RecursorIotaObligation) :
    Option GeneratedUnaryOpenIotaRule :=
  if obligation = natRecSuccIotaObligation then
    some natRecSuccUnaryOpenIotaRule
  else
    none

def generatedRecursorPilot (contract : FamilyRecursorDeclContract) : Option GeneratedRecursorPilot :=
  if contract.recursorName == unitRecName then
    some
      { contract := contract
        obligations := [unitRecCtorIotaObligation]
        value? := some unitRecValue }
  else if contract.recursorName == natRecName then
    some
      { contract := contract
        obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
        value? := none }
  else
    none

def generatedClosedIotaRules (pilot : GeneratedRecursorPilot) : List GeneratedClosedIotaRule :=
  pilot.obligations.filterMap generateClosedIotaRule?

def generatedUnaryOpenIotaRules
    (pilot : GeneratedRecursorPilot) : List GeneratedUnaryOpenIotaRule :=
  pilot.obligations.filterMap generateUnaryOpenIotaRule?

def GeneratedClosedIotaStep (pilot : GeneratedRecursorPilot) : PureTm 0 → PureTm 0 → Prop :=
  fun t u => ∃ rule ∈ generatedClosedIotaRules pilot, t = rule.source ∧ u = rule.target

def GeneratedUnaryOpenIotaStep
    (pilot : GeneratedRecursorPilot) : PureTm 0 → PureTm 0 → Prop :=
  fun t u =>
    ∃ rule ∈ generatedUnaryOpenIotaRules pilot,
      ∃ a : PureTm 0,
        HasTypeDecl natRecDeclEnv .nil a (.const NatDecl.natTyName) ∧
        t = inst0 a rule.source ∧
        u = inst0 a rule.target

def generatedRecursorContractClosedIotaRules
    (contract : FamilyRecursorDeclContract) : List GeneratedClosedIotaRule :=
  match generatedRecursorPilot contract with
  | some pilot => generatedClosedIotaRules pilot
  | none => []

def GeneratedRecursorContractClosedIotaStep
    (contract : FamilyRecursorDeclContract) : PureTm 0 → PureTm 0 → Prop :=
  fun t u =>
    ∃ rule ∈ generatedRecursorContractClosedIotaRules contract,
      t = rule.source ∧ u = rule.target

def generatedClosedIotaTargetFromRules? :
    List GeneratedClosedIotaRule → PureTm 0 → Option (PureTm 0)
  | [], _ => none
  | rule :: rules, t =>
      if rule.source = t then
        some rule.target
      else
        generatedClosedIotaTargetFromRules? rules t

def generatedRecursorContractClosedIotaTarget?
    (contract : FamilyRecursorDeclContract) (t : PureTm 0) : Option (PureTm 0) :=
  generatedClosedIotaTargetFromRules? (generatedRecursorContractClosedIotaRules contract) t

def generatedRecursorContractClosedIotaNormalize
    (contract : FamilyRecursorDeclContract) (t : PureTm 0) : PureTm 0 :=
  match generatedRecursorContractClosedIotaTarget? contract t with
  | some u => u
  | none => t

abbrev GeneratedRecursorContractClosedIotaJoinable
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) : Prop :=
  ∃ v : PureTm 0,
    Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t v ∧
    Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u v

structure GeneratedRecursorContractClosedIotaJoinWitness
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) : Type where
  joinable : GeneratedRecursorContractClosedIotaJoinable contract t u

abbrev GeneratedRecursorContractClosedIotaConv
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) : Prop :=
  Relation.EqvGen (GeneratedRecursorContractClosedIotaStep contract) t u

structure GeneratedRecursorContractClosedIotaConvWitness
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) : Type where
  conv : GeneratedRecursorContractClosedIotaConv contract t u

def GeneratedRecursorContractClosedIotaRealizedIn
    (E : DeclEnv) (contract : FamilyRecursorDeclContract) : Prop :=
  ∀ {t u : PureTm 0},
    GeneratedRecursorContractClosedIotaStep contract t u →
      RedStarDecl E t u

def generatedOpenIotaObligations (pilot : GeneratedRecursorPilot) : List RecursorIotaObligation :=
  pilot.obligations.filter (fun obligation => generateClosedIotaRule? obligation = none)

def generatedResolvedIotaObligations
    (pilot : GeneratedRecursorPilot) : List RecursorIotaObligation :=
  pilot.obligations.filter fun obligation =>
    match generateClosedIotaRule? obligation, generateUnaryOpenIotaRule? obligation with
    | none, none => true
    | _, _ => false

def generatedRecursorContractOpenIotaObligations
    (contract : FamilyRecursorDeclContract) : List RecursorIotaObligation :=
  match generatedRecursorPilot contract with
  | some pilot => generatedOpenIotaObligations pilot
  | none => []

def generatedRecursorContractResolvedIotaObligations
    (contract : FamilyRecursorDeclContract) : List RecursorIotaObligation :=
  match generatedRecursorPilot contract with
  | some pilot => generatedResolvedIotaObligations pilot
  | none => []

abbrev GeneratedRecursorContractAdmitted
    (contract : FamilyRecursorDeclContract) : Prop :=
  ∃ pilot : GeneratedRecursorPilot, generatedRecursorPilot contract = some pilot

abbrev GeneratedRecursorContractFullyClosed
    (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorContractAdmitted contract ∧
    generatedRecursorContractOpenIotaObligations contract = []

theorem generatedRecursorPilot_unit :
    generatedRecursorPilot unitRecContract =
      some
        { contract := unitRecContract
          obligations := [unitRecCtorIotaObligation]
          value? := some unitRecValue } := by
  decide

theorem generatedRecursorPilot_nat_obligations_no_value :
    generatedRecursorPilot natRecContract =
      some
        { contract := natRecContract
          obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
          value? := none } := by
  decide

theorem generateClosedIotaRule_unit :
    generateClosedIotaRule? unitRecCtorIotaObligation =
      some unitRecCtorClosedIotaRule := by
  decide

theorem generateClosedIotaRule_nat_zero :
    generateClosedIotaRule? natRecZeroIotaObligation =
      some natRecZeroClosedIotaRule := by
  simp [generateClosedIotaRule?, unitRecCtorIotaObligation, natRecZeroIotaObligation]

theorem generateClosedIotaRule_nat_succ_still_open :
    generateClosedIotaRule? natRecSuccIotaObligation = none := by
  decide

theorem generateUnaryOpenIotaRule_nat_succ :
    generateUnaryOpenIotaRule? natRecSuccIotaObligation = some natRecSuccUnaryOpenIotaRule := by
  simp [generateUnaryOpenIotaRule?, natRecSuccUnaryOpenIotaRule]

theorem natRecSuccIotaObligation_open_not_closed :
    generateClosedIotaRule? natRecSuccIotaObligation = none ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  exact ⟨generateClosedIotaRule_nat_succ_still_open, natRecSuccOpenIotaRule_checked⟩

theorem generatedUnaryOpenIotaRules_nat :
    generatedUnaryOpenIotaRules
      { contract := natRecContract
        obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
        value? := none } =
      [natRecSuccUnaryOpenIotaRule] := by
  simp [generatedUnaryOpenIotaRules, generateUnaryOpenIotaRule?,
    natRecZeroIotaObligation, natRecSuccIotaObligation, natRecSuccUnaryOpenIotaRule]

theorem generatedUnaryOpenIotaStep_deterministic
    {pilot : GeneratedRecursorPilot} {t u₁ u₂ : PureTm 0}
    (h₁ : GeneratedUnaryOpenIotaStep pilot t u₁)
    (h₂ : GeneratedUnaryOpenIotaStep pilot t u₂) :
    u₁ = u₂ := by
  rcases h₁ with ⟨rule₁, hMem₁, a₁, ha₁, ht₁, hu₁⟩
  rcases h₂ with ⟨rule₂, hMem₂, a₂, ha₂, ht₂, hu₂⟩
  unfold generatedUnaryOpenIotaRules at hMem₁ hMem₂
  rw [List.mem_filterMap] at hMem₁ hMem₂
  rcases hMem₁ with ⟨ob₁, hOb₁, hRule₁⟩
  rcases hMem₂ with ⟨ob₂, hOb₂, hRule₂⟩
  have hr₁ : ob₁ = natRecSuccIotaObligation ∧ rule₁ = natRecSuccUnaryOpenIotaRule := by
    simpa [generateUnaryOpenIotaRule?, natRecSuccUnaryOpenIotaRule] using hRule₁.symm
  have hr₂ : ob₂ = natRecSuccIotaObligation ∧ rule₂ = natRecSuccUnaryOpenIotaRule := by
    simpa [generateUnaryOpenIotaRule?, natRecSuccUnaryOpenIotaRule] using hRule₂.symm
  rcases hr₁ with ⟨_, hr₁eq⟩
  rcases hr₂ with ⟨_, hr₂eq⟩
  subst hr₁eq
  subst hr₂eq
  subst ht₁
  subst hu₁
  subst hu₂
  have hArg : a₁ = a₂ :=
    natRecSuccClosedSource_injective
      (by simpa [natRecSuccClosedSource, natRecSuccUnaryOpenIotaRule] using ht₂)
  subst hArg
  rfl

theorem generatedUnaryOpenIotaStep_preserves_type
    {pilot : GeneratedRecursorPilot} {t u : PureTm 0}
    (h : GeneratedUnaryOpenIotaStep pilot t u) :
    HasTypeDecl natRecDeclEnv .nil t (.const NatDecl.natTyName) ∧
      HasTypeDecl natRecDeclEnv .nil u (.const NatDecl.natTyName) := by
  rcases h with ⟨rule, hMem, a, ha, rfl, rfl⟩
  unfold generatedUnaryOpenIotaRules at hMem
  rw [List.mem_filterMap] at hMem
  rcases hMem with ⟨ob, hOb, hRule⟩
  have hrule : ob = natRecSuccIotaObligation ∧ rule = natRecSuccUnaryOpenIotaRule := by
    simpa [generateUnaryOpenIotaRule?, natRecSuccUnaryOpenIotaRule] using hRule.symm
  rcases hrule with ⟨_, hruleEq⟩
  subst hruleEq
  exact ⟨hasType_natRecSuccClosedSource ha, hasType_natRecSuccClosedTarget ha⟩

theorem generatedResolvedIotaObligations_nat_pilot :
    generatedResolvedIotaObligations
      { contract := natRecContract
        obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
        value? := none } = [] := by
  simp [generatedResolvedIotaObligations, generateClosedIotaRule_nat_zero,
    generateUnaryOpenIotaRule?, natRecSuccIotaObligation]

theorem generatedResolvedIotaObligations_unit_pilot :
    generatedResolvedIotaObligations
      { contract := unitRecContract
        obligations := [unitRecCtorIotaObligation]
        value? := some unitRecValue } = [] := by
  simp [generatedResolvedIotaObligations, generateClosedIotaRule_unit,
    generateUnaryOpenIotaRule?]

theorem natRecZeroClosedIotaRule_source_target :
    natRecZeroClosedIotaRule.source = natRecZeroClosedSource ∧
      natRecZeroClosedIotaRule.target = natZeroTerm :=
  ⟨rfl, rfl⟩

theorem natRecZeroClosedIotaRule_checked :
    ∃ A : PureTm 0,
      HasTypeDecl natRecDeclEnv .nil natRecZeroClosedIotaRule.source A ∧
      generateClosedIotaRule? natRecZeroIotaObligation = some natRecZeroClosedIotaRule ∧
      HasTypeDecl natRecDeclEnv .nil natRecZeroClosedIotaRule.target A := by
  refine ⟨.const natTyName, ?_, ?_, ?_⟩
  · simpa [natRecZeroClosedIotaRule] using hasType_natRecZeroClosedSource
  · exact generateClosedIotaRule_nat_zero
  · unfold natRecZeroClosedIotaRule natRecZeroClosedTarget natZeroTerm
    exact hasType_natZero_inRecEnv

private theorem natRecDecl_const_irreducible
    {n : Nat} {c : DeclName} {u : PureTm n}
    (hNone : valueOf? natRecDeclEnv c = none) :
    ¬ RedDecl natRecDeclEnv ((.const c : PureTm n)) u := by
  intro h
  cases h with
  | core hred =>
      cases hred
  | deltaConst hVal =>
      simp [hNone] at hVal

private theorem natRecDecl_var_irreducible
    {n : Nat} {i : Fin n} {u : PureTm n} :
    ¬ RedDecl natRecDeclEnv (.var i) u := by
  intro h
  cases h with
  | core hred =>
      cases hred

private theorem natRecStepSuccBody_irreducible
    {u : PureTm 2} :
    ¬ RedDecl natRecDeclEnv (.app (.const natSuccName) (.var (0 : Fin 2))) u := by
  intro h
  cases h with
  | core hred =>
      cases hred with
      | congAppFun hFun =>
          exact natRecDecl_const_irreducible (c := natSuccName) (u := _) (by simp) (.core hFun)
      | congAppArg hArg =>
          exact natRecDecl_var_irreducible (i := (0 : Fin 2)) (.core hArg)
  | congAppFun hFun =>
      exact natRecDecl_const_irreducible (c := natSuccName) (u := _) (by simp) hFun
  | congAppArg hArg =>
      exact natRecDecl_var_irreducible (i := (0 : Fin 2)) hArg

private theorem natRecStepSuccInner_irreducible
    {u : PureTm 1} :
    ¬ RedDecl natRecDeclEnv (.lam (.app (.const natSuccName) (.var (0 : Fin 2)))) u := by
  intro h
  cases h with
  | core hred =>
      cases hred with
      | congLam hBody =>
          exact natRecStepSuccBody_irreducible (.core hBody)
  | congLam hBody =>
      exact natRecStepSuccBody_irreducible hBody

private theorem natRecStepSuccValue_irreducible
    {u : PureTm 0} :
    ¬ RedDecl natRecDeclEnv natRecStepSuccValue u := by
  intro h
  unfold natRecStepSuccValue at h
  cases h with
  | core hred =>
      cases hred with
      | congLam hBody =>
          exact natRecStepSuccInner_irreducible (.core hBody)
  | congLam hBody =>
      exact natRecStepSuccInner_irreducible hBody

private theorem natRecAppTy_irreducible
    {u : PureTm 0} :
    ¬ RedDecl natRecDeclEnv (.app natRecTerm (.const natTyName)) u := by
  intro h
  unfold natRecTerm at h
  cases h with
  | core hred =>
      cases hred with
      | congAppFun hFun =>
          exact natRecDecl_const_irreducible (c := natRecName) (u := _) (by simp) (.core hFun)
      | congAppArg hArg =>
          exact natRecDecl_const_irreducible (c := natTyName) (u := _) (by simp) (.core hArg)
  | congAppFun hFun =>
      exact natRecDecl_const_irreducible (c := natRecName) (u := _) (by simp) hFun
  | congAppArg hArg =>
      exact natRecDecl_const_irreducible (c := natTyName) (u := _) (by simp) hArg

private theorem natRecAppZero_irreducible
    {u : PureTm 0} :
    ¬ RedDecl natRecDeclEnv (.app (.app natRecTerm (.const natTyName)) natZeroTerm) u := by
  intro h
  unfold natZeroTerm at h
  cases h with
  | core hred =>
      cases hred with
      | congAppFun hFun =>
          exact natRecAppTy_irreducible (.core hFun)
      | congAppArg hArg =>
          exact natRecDecl_const_irreducible (c := natZeroName) (u := _) (by simp) (.core hArg)
  | congAppFun hFun =>
      exact natRecAppTy_irreducible hFun
  | congAppArg hArg =>
      exact natRecDecl_const_irreducible (c := natZeroName) (u := _) (by simp) hArg

private theorem natRecAppStep_irreducible
    {u : PureTm 0} :
    ¬ RedDecl natRecDeclEnv
      (.app (.app (.app natRecTerm (.const natTyName)) natZeroTerm) natRecStepSuccValue) u := by
  intro h
  cases h with
  | core hred =>
      cases hred with
      | congAppFun hFun =>
          exact natRecAppZero_irreducible (.core hFun)
      | congAppArg hArg =>
          exact natRecStepSuccValue_irreducible (.core hArg)
  | congAppFun hFun =>
      exact natRecAppZero_irreducible hFun
  | congAppArg hArg =>
      exact natRecStepSuccValue_irreducible hArg

theorem natRecZeroClosedSource_irreducible
    {u : PureTm 0} :
    ¬ RedDecl natRecDeclEnv natRecZeroClosedSource u := by
  intro h
  unfold natRecZeroClosedSource natZeroTerm at h
  cases h with
  | core hred =>
      cases hred with
      | congAppFun hFun =>
          exact natRecAppStep_irreducible (.core hFun)
      | congAppArg hArg =>
          exact natRecDecl_const_irreducible (c := natZeroName) (u := _) (by simp) (.core hArg)
  | congAppFun hFun =>
      exact natRecAppStep_irreducible hFun
  | congAppArg hArg =>
      exact natRecDecl_const_irreducible (c := natZeroName) (u := _) (by simp) hArg

theorem natRecZeroClosedIotaRule_not_realized_in_current_decl_env :
    ¬ RedStarDecl natRecDeclEnv
      natRecZeroClosedIotaRule.source
      natRecZeroClosedIotaRule.target := by
  intro hStar
  rcases Relation.ReflTransGen.cases_head hStar with hEq | ⟨_, hStep, _⟩
  · have hNe :
        natRecZeroClosedIotaRule.source ≠ natRecZeroClosedIotaRule.target := by
        decide
    exact hNe hEq
  · exact natRecZeroClosedSource_irreducible (by simpa [natRecZeroClosedIotaRule] using hStep)

theorem natRecContract_closed_slice_not_realized_in_current_decl_env :
    ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv natRecContract := by
  intro hReal
  apply natRecZeroClosedIotaRule_not_realized_in_current_decl_env
  have hStep :
      GeneratedRecursorContractClosedIotaStep
        natRecContract
        natRecZeroClosedIotaRule.source
        natRecZeroClosedIotaRule.target := by
    refine ⟨natRecZeroClosedIotaRule, ?_, rfl, rfl⟩
    simp [generatedRecursorContractClosedIotaRules,
      generatedRecursorPilot_nat_obligations_no_value,
      generatedClosedIotaRules,
      generateClosedIotaRule_nat_zero,
      generateClosedIotaRule_nat_succ_still_open]
  exact hReal hStep

theorem generateClosedIotaRule_checked_preserves_type
    {obligation : RecursorIotaObligation} {rule : GeneratedClosedIotaRule}
    (hRule : generateClosedIotaRule? obligation = some rule) :
    ∃ (E : DeclEnv) (A : PureTm 0),
      HasTypeDecl E .nil rule.source A ∧
      HasTypeDecl E .nil rule.target A := by
  by_cases hUnit : obligation = unitRecCtorIotaObligation
  · subst hUnit
    have hrule : rule = unitRecCtorClosedIotaRule := by
      simpa [generateClosedIotaRule_unit] using hRule.symm
    subst hrule
    rcases unitRecCtorClosedIotaRule_checked with ⟨A, hSrc, hTgt⟩
    exact ⟨unitRecDeclEnv, A, hSrc, hTgt⟩
  · by_cases hNatZero : obligation = natRecZeroIotaObligation
    · subst hNatZero
      have hrule : rule = natRecZeroClosedIotaRule := by
        simpa [generateClosedIotaRule_nat_zero] using hRule.symm
      subst hrule
      rcases natRecZeroClosedIotaRule_checked with ⟨A, hSrc, _, hTgt⟩
      exact ⟨natRecDeclEnv, A, hSrc, hTgt⟩
    · simp [generateClosedIotaRule?, hUnit, hNatZero] at hRule

theorem generatedRecursorPilot_checked_rules_preserve_type
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    {obligation : RecursorIotaObligation} {rule : GeneratedClosedIotaRule}
    (hPilot : generatedRecursorPilot contract = some pilot)
    (hMem : obligation ∈ pilot.obligations)
    (hRule : generateClosedIotaRule? obligation = some rule) :
    ∃ (E : DeclEnv) (A : PureTm 0),
      HasTypeDecl E .nil rule.source A ∧
      HasTypeDecl E .nil rule.target A := by
  by_cases hUnit : contract.recursorName == unitRecName
  · have hp :
        some pilot =
          some
            { contract := contract
              obligations := [unitRecCtorIotaObligation]
              value? := some unitRecValue } := by
        simpa [generatedRecursorPilot, hUnit] using hPilot.symm
    injection hp with hpilot
    subst hpilot
    simp at hMem
    subst hMem
    have hrule : rule = unitRecCtorClosedIotaRule := by
      simpa [generateClosedIotaRule_unit] using hRule.symm
    subst hrule
    rcases unitRecCtorClosedIotaRule_checked with ⟨A, hSrc, hTgt⟩
    exact ⟨unitRecDeclEnv, A, hSrc, hTgt⟩
  · by_cases hNat : contract.recursorName == natRecName
    · have hp :
          some pilot =
            some
              { contract := contract
                obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
                value? := none } := by
          simpa [generatedRecursorPilot, hUnit, hNat] using hPilot.symm
      injection hp with hpilot
      subst hpilot
      simp at hMem
      rcases hMem with rfl | rfl
      · have hrule : rule = natRecZeroClosedIotaRule := by
          simpa [generateClosedIotaRule_nat_zero] using hRule.symm
        subst hrule
        rcases natRecZeroClosedIotaRule_checked with ⟨A, hSrc, _, hTgt⟩
        exact ⟨natRecDeclEnv, A, hSrc, hTgt⟩
      · exfalso
        simp [generateClosedIotaRule_nat_succ_still_open] at hRule
    · simp [generatedRecursorPilot, hUnit, hNat] at hPilot

theorem generatedRecursorPilot_checked_rules_preserve_type_in_wellFormed_env
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    {obligation : RecursorIotaObligation} {rule : GeneratedClosedIotaRule}
    (hPilot : generatedRecursorPilot contract = some pilot)
    (hMem : obligation ∈ pilot.obligations)
    (hRule : generateClosedIotaRule? obligation = some rule) :
    ∃ (E : DeclEnv) (A : PureTm 0),
      DeclEnvWellFormed E ∧
      HasTypeDecl E .nil rule.source A ∧
      HasTypeDecl E .nil rule.target A := by
  by_cases hUnit : contract.recursorName == unitRecName
  · have hp :
        some pilot =
          some
            { contract := contract
              obligations := [unitRecCtorIotaObligation]
              value? := some unitRecValue } := by
        simpa [generatedRecursorPilot, hUnit] using hPilot.symm
    injection hp with hpilot
    subst hpilot
    simp at hMem
    subst hMem
    have hrule : rule = unitRecCtorClosedIotaRule := by
      simpa [generateClosedIotaRule_unit] using hRule.symm
    subst hrule
    rcases unitRecCtorClosedIotaRule_checked with ⟨A, hSrc, hTgt⟩
    exact ⟨unitRecDeclEnv, A, unitRecDeclEnv_wellFormed, hSrc, hTgt⟩
  · by_cases hNat : contract.recursorName == natRecName
    · have hp :
          some pilot =
            some
              { contract := contract
                obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
                value? := none } := by
          simpa [generatedRecursorPilot, hUnit, hNat] using hPilot.symm
      injection hp with hpilot
      subst hpilot
      simp at hMem
      rcases hMem with rfl | rfl
      · have hrule : rule = natRecZeroClosedIotaRule := by
          simpa [generateClosedIotaRule_nat_zero] using hRule.symm
        subst hrule
        rcases natRecZeroClosedIotaRule_checked with ⟨A, hSrc, _, hTgt⟩
        exact ⟨natRecDeclEnv, A, natRecDeclEnv_wellFormed, hSrc, hTgt⟩
      · exfalso
        simp [generateClosedIotaRule_nat_succ_still_open] at hRule
    · simp [generatedRecursorPilot, hUnit, hNat] at hPilot

theorem generatedClosedIotaRules_mem_preserve_type_in_wellFormed_env
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    {rule : GeneratedClosedIotaRule}
    (hPilot : generatedRecursorPilot contract = some pilot)
    (hMem : rule ∈ generatedClosedIotaRules pilot) :
    ∃ (E : DeclEnv) (A : PureTm 0),
      DeclEnvWellFormed E ∧
      HasTypeDecl E .nil rule.source A ∧
      HasTypeDecl E .nil rule.target A := by
  unfold generatedClosedIotaRules at hMem
  rw [List.mem_filterMap] at hMem
  rcases hMem with ⟨obligation, hObMem, hRule⟩
  exact generatedRecursorPilot_checked_rules_preserve_type_in_wellFormed_env hPilot hObMem hRule

theorem generatedClosedIotaStep_preserves_type_in_wellFormed_env
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    {t u : PureTm 0}
    (hPilot : generatedRecursorPilot contract = some pilot)
    (hStep : GeneratedClosedIotaStep pilot t u) :
    ∃ (E : DeclEnv) (A : PureTm 0),
      DeclEnvWellFormed E ∧
      HasTypeDecl E .nil t A ∧
      HasTypeDecl E .nil u A := by
  rcases hStep with ⟨rule, hMem, rfl, rfl⟩
  exact generatedClosedIotaRules_mem_preserve_type_in_wellFormed_env hPilot hMem

theorem generatedClosedIotaRules_unit :
    generatedClosedIotaRules
      { contract := unitRecContract
        obligations := [unitRecCtorIotaObligation]
        value? := some unitRecValue } =
      [unitRecCtorClosedIotaRule] := by
  simp [generatedClosedIotaRules, generateClosedIotaRule_unit]

theorem generatedClosedIotaRules_nat :
    generatedClosedIotaRules
      { contract := natRecContract
        obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
        value? := none } =
      [natRecZeroClosedIotaRule] := by
  simp [generatedClosedIotaRules, generateClosedIotaRule_nat_zero,
    generateClosedIotaRule_nat_succ_still_open]

theorem generatedRecursorPilot_generatedClosedIotaRules_cases
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    generatedClosedIotaRules pilot = [unitRecCtorClosedIotaRule] ∨
      generatedClosedIotaRules pilot = [natRecZeroClosedIotaRule] := by
  by_cases hUnit : contract.recursorName == unitRecName
  · have hp :
        some pilot =
          some
            { contract := contract
              obligations := [unitRecCtorIotaObligation]
              value? := some unitRecValue } := by
        simpa [generatedRecursorPilot, hUnit] using hPilot.symm
    injection hp with hpilot
    subst hpilot
    left
    simp [generatedClosedIotaRules, generateClosedIotaRule_unit]
  · by_cases hNat : contract.recursorName == natRecName
    · have hp :
          some pilot =
            some
              { contract := contract
                obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
                value? := none } := by
          simpa [generatedRecursorPilot, hUnit, hNat] using hPilot.symm
      injection hp with hpilot
      subst hpilot
      right
      simp [generatedClosedIotaRules, generateClosedIotaRule_nat_zero,
        generateClosedIotaRule_nat_succ_still_open]
    · simp [generatedRecursorPilot, hUnit, hNat] at hPilot

theorem generatedRecursorPilot_generatedClosedIotaRules_pairwise
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (R : GeneratedClosedIotaRule → GeneratedClosedIotaRule → Prop)
    (hPilot : generatedRecursorPilot contract = some pilot) :
    (generatedClosedIotaRules pilot).Pairwise R := by
  rcases generatedRecursorPilot_generatedClosedIotaRules_cases hPilot with hUnit | hNat
  · rw [hUnit]
    simp
  · rw [hNat]
    simp

theorem generatedRecursorPilot_obligation_closed_or_open
    {pilot : GeneratedRecursorPilot}
    {obligation : RecursorIotaObligation}
    (hMem : obligation ∈ pilot.obligations) :
    obligation ∈ generatedOpenIotaObligations pilot ∨
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedClosedIotaRules pilot ∧
        generateClosedIotaRule? obligation = some rule := by
  cases hRule : generateClosedIotaRule? obligation with
  | none =>
      left
      simp [generatedOpenIotaObligations, hMem, hRule]
  | some rule =>
      right
      refine ⟨rule, ?_, rfl⟩
      unfold generatedClosedIotaRules
      exact List.mem_filterMap.2 ⟨obligation, hMem, hRule⟩

theorem generatedRecursorPilot_open_obligations_cases
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    generatedOpenIotaObligations pilot = [] ∨
      generatedOpenIotaObligations pilot = [natRecSuccIotaObligation] := by
  by_cases hUnit : contract.recursorName == unitRecName
  · have hp :
        some pilot =
          some
            { contract := contract
              obligations := [unitRecCtorIotaObligation]
              value? := some unitRecValue } := by
        simpa [generatedRecursorPilot, hUnit] using hPilot.symm
    injection hp with hpilot
    subst hpilot
    left
    simp [generatedOpenIotaObligations, generateClosedIotaRule_unit]
  · by_cases hNat : contract.recursorName == natRecName
    · have hp :
          some pilot =
            some
              { contract := contract
                obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
                value? := none } := by
          simpa [generatedRecursorPilot, hUnit, hNat] using hPilot.symm
      injection hp with hpilot
      subst hpilot
      right
      simp [generatedOpenIotaObligations, generateClosedIotaRule_nat_zero,
        generateClosedIotaRule_nat_succ_still_open]
    · simp [generatedRecursorPilot, hUnit, hNat] at hPilot

theorem generatedRecursorPilot_open_obligation_checked
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    {obligation : RecursorIotaObligation}
    (hPilot : generatedRecursorPilot contract = some pilot)
    (hOpen : obligation ∈ generatedOpenIotaObligations pilot) :
    obligation = natRecSuccIotaObligation ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A := by
  rcases generatedRecursorPilot_open_obligations_cases hPilot with hNil | hSucc
  · rw [hNil] at hOpen
    simp at hOpen
  · rw [hSucc] at hOpen
    simp at hOpen
    exact ⟨hOpen, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorPilot_obligations_preserve_type_current_gate
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    {obligation : RecursorIotaObligation}
    (hPilot : generatedRecursorPilot contract = some pilot)
    (hMem : obligation ∈ pilot.obligations) :
    (∃ rule : GeneratedClosedIotaRule, ∃ E : DeclEnv, ∃ A : PureTm 0,
      generateClosedIotaRule? obligation = some rule ∧
      DeclEnvWellFormed E ∧
      HasTypeDecl E .nil rule.source A ∧
      HasTypeDecl E .nil rule.target A)
    ∨
    (obligation = natRecSuccIotaObligation ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorPilot_obligation_closed_or_open (pilot := pilot) hMem with hOpen | hClosed
  · right
    exact generatedRecursorPilot_open_obligation_checked hPilot hOpen
  · rcases hClosed with ⟨rule, hRuleMem, hRuleEq⟩
    rcases generatedClosedIotaRules_mem_preserve_type_in_wellFormed_env hPilot hRuleMem with
      ⟨E, A, hWf, hSrc, hTgt⟩
    left
    exact ⟨rule, E, A, hRuleEq, hWf, hSrc, hTgt⟩

theorem generatedRecursorContract_admitted_obligations_preserve_type_current_gate
    {contract : FamilyRecursorDeclContract}
    (_hAdm : GeneratedRecursorContractAdmitted contract) :
    ∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      (∃ rule : GeneratedClosedIotaRule, ∃ E : DeclEnv, ∃ A : PureTm 0,
        generateClosedIotaRule? obligation = some rule ∧
        DeclEnvWellFormed E ∧
        HasTypeDecl E .nil rule.source A ∧
        HasTypeDecl E .nil rule.target A)
      ∨
      (obligation = natRecSuccIotaObligation ∧
        ∃ A : PureTm 1,
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  intro pilot obligation hPilot hMem
  exact generatedRecursorPilot_obligations_preserve_type_current_gate hPilot hMem

theorem generatedRecursorPilot_generatedClosedIotaRules_nonoverlapping
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    (generatedClosedIotaRules pilot).Pairwise
      (fun rule₁ rule₂ => rule₁.source ≠ rule₂.source) := by
  exact generatedRecursorPilot_generatedClosedIotaRules_pairwise
    (R := fun rule₁ rule₂ => rule₁.source ≠ rule₂.source)
    hPilot

theorem generatedRecursorPilot_generatedClosedIotaStep_deterministic
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∀ {t u₁ u₂ : PureTm 0},
      GeneratedClosedIotaStep pilot t u₁ →
      GeneratedClosedIotaStep pilot t u₂ →
      u₁ = u₂ := by
  intro t u₁ u₂ hStep₁ hStep₂
  rcases generatedRecursorPilot_generatedClosedIotaRules_cases hPilot with hUnit | hNat
  · unfold GeneratedClosedIotaStep at hStep₁ hStep₂
    rw [hUnit] at hStep₁ hStep₂
    simp at hStep₁ hStep₂
    rcases hStep₁ with ⟨hSrc₁, hTgt₁⟩
    rcases hStep₂ with ⟨hSrc₂, hTgt₂⟩
    exact hTgt₁.trans hTgt₂.symm
  · unfold GeneratedClosedIotaStep at hStep₁ hStep₂
    rw [hNat] at hStep₁ hStep₂
    simp at hStep₁ hStep₂
    rcases hStep₁ with ⟨hSrc₁, hTgt₁⟩
    rcases hStep₂ with ⟨hSrc₂, hTgt₂⟩
    exact hTgt₁.trans hTgt₂.symm

theorem generatedRecursorPilot_generatedClosedIotaStep_locally_confluent
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∀ {t u₁ u₂ : PureTm 0},
      GeneratedClosedIotaStep pilot t u₁ →
      GeneratedClosedIotaStep pilot t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedClosedIotaStep pilot) u₁ v ∧
        Relation.ReflTransGen (GeneratedClosedIotaStep pilot) u₂ v := by
  intro t u₁ u₂ hStep₁ hStep₂
  have hEq :
      u₁ = u₂ :=
    generatedRecursorPilot_generatedClosedIotaStep_deterministic hPilot hStep₁ hStep₂
  refine ⟨u₁, Relation.ReflTransGen.refl, ?_⟩
  subst hEq
  exact Relation.ReflTransGen.refl

theorem generatedRecursorPilot_generatedClosedIotaStep_target_irreducible
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∀ {t u v : PureTm 0},
      GeneratedClosedIotaStep pilot t u →
      ¬ GeneratedClosedIotaStep pilot u v := by
  intro t u v hStep
  rcases generatedRecursorPilot_generatedClosedIotaRules_cases hPilot with hUnit | hNat
  · unfold GeneratedClosedIotaStep at hStep
    rw [hUnit] at hStep
    simp at hStep
    rcases hStep with ⟨_, hTgt⟩
    subst hTgt
    intro hNext
    unfold GeneratedClosedIotaStep at hNext
    rw [hUnit] at hNext
    simp at hNext
    rcases hNext with ⟨hSrc, _⟩
    exact (by decide : unitCtorTerm ≠ unitRecOnCtor) hSrc
  · unfold GeneratedClosedIotaStep at hStep
    rw [hNat] at hStep
    simp at hStep
    rcases hStep with ⟨_, hTgt⟩
    subst hTgt
    intro hNext
    unfold GeneratedClosedIotaStep at hNext
    rw [hNat] at hNext
    simp at hNext
    rcases hNext with ⟨hSrc, _⟩
    exact (by decide : natZeroTerm ≠ natRecZeroClosedSource) hSrc

theorem generatedRecursorPilot_generatedClosedIotaStep_normalizes
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot)
    (t : PureTm 0) :
    ∃ u : PureTm 0,
      Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u ∧
      ¬ ∃ v : PureTm 0, GeneratedClosedIotaStep pilot u v := by
  classical
  by_cases hStep : ∃ u : PureTm 0, GeneratedClosedIotaStep pilot t u
  · rcases hStep with ⟨u, htu⟩
    refine ⟨u, Relation.ReflTransGen.tail Relation.ReflTransGen.refl htu, ?_⟩
    intro hNext
    rcases hNext with ⟨v, huv⟩
    exact generatedRecursorPilot_generatedClosedIotaStep_target_irreducible hPilot htu huv
  · exact ⟨t, Relation.ReflTransGen.refl, hStep⟩

theorem generatedRecursorPilot_generatedClosedIotaStep_star_cases
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u →
      u = t ∨ GeneratedClosedIotaStep pilot t u := by
  intro t u hStar
  induction hStar with
  | refl =>
      exact Or.inl rfl
  | tail hxy hyz ih =>
      rcases ih with rfl | hStep
      · exact Or.inr hyz
      · exact False.elim
          (generatedRecursorPilot_generatedClosedIotaStep_target_irreducible
            hPilot hStep hyz)

theorem generatedRecursorPilot_generatedClosedIotaStep_confluent
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u₁ →
      Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedClosedIotaStep pilot) u₁ v ∧
        Relation.ReflTransGen (GeneratedClosedIotaStep pilot) u₂ v := by
  intro t u₁ u₂ hStar₁ hStar₂
  rcases generatedRecursorPilot_generatedClosedIotaStep_star_cases hPilot hStar₁ with rfl | hStep₁
  · exact ⟨u₂, hStar₂, Relation.ReflTransGen.refl⟩
  · rcases generatedRecursorPilot_generatedClosedIotaStep_star_cases hPilot hStar₂ with rfl | hStep₂
    · exact ⟨u₁, Relation.ReflTransGen.refl, hStar₁⟩
    · have hEq :
          u₁ = u₂ :=
        generatedRecursorPilot_generatedClosedIotaStep_deterministic hPilot hStep₁ hStep₂
      subst hEq
      exact ⟨u₁, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem generatedRecursorPilot_generatedClosedIotaStep_irreducible_star_eq
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot)
    {t u : PureTm 0}
    (hIrred : ¬ ∃ v : PureTm 0, GeneratedClosedIotaStep pilot t v)
    (hStar : Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u) :
    u = t := by
  rcases generatedRecursorPilot_generatedClosedIotaStep_star_cases hPilot hStar with
    hEq | hStep
  · exact hEq
  · exfalso
    exact hIrred ⟨u, hStep⟩

theorem generatedRecursorPilot_generatedClosedIotaStep_unique_normal_form
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u₁ →
      Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u₂ →
      (¬ ∃ v : PureTm 0, GeneratedClosedIotaStep pilot u₁ v) →
      (¬ ∃ v : PureTm 0, GeneratedClosedIotaStep pilot u₂ v) →
      u₁ = u₂ := by
  intro t u₁ u₂ hStar₁ hStar₂ hIrred₁ hIrred₂
  rcases generatedRecursorPilot_generatedClosedIotaStep_confluent hPilot hStar₁ hStar₂ with
    ⟨v, hJoin₁, hJoin₂⟩
  have h₁ : v = u₁ :=
    generatedRecursorPilot_generatedClosedIotaStep_irreducible_star_eq
      hPilot hIrred₁ hJoin₁
  have h₂ : v = u₂ :=
    generatedRecursorPilot_generatedClosedIotaStep_irreducible_star_eq
      hPilot hIrred₂ hJoin₂
  exact h₁.symm.trans h₂

theorem generatedRecursorPilot_generatedClosedIotaRules_checked_in_wellFormed_env
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      ∀ rule ∈ generatedClosedIotaRules pilot,
        ∃ A : PureTm 0,
          HasTypeDecl E .nil rule.source A ∧
          HasTypeDecl E .nil rule.target A := by
  by_cases hUnit : contract.recursorName == unitRecName
  · have hp :
        some pilot =
          some
            { contract := contract
              obligations := [unitRecCtorIotaObligation]
              value? := some unitRecValue } := by
        simpa [generatedRecursorPilot, hUnit] using hPilot.symm
    injection hp with hpilot
    subst hpilot
    refine ⟨unitRecDeclEnv, unitRecDeclEnv_wellFormed, ?_⟩
    intro rule hMem
    simp [generatedClosedIotaRules, generateClosedIotaRule_unit] at hMem
    subst hMem
    rcases unitRecCtorClosedIotaRule_checked with ⟨A, hSrc, hTgt⟩
    exact ⟨A, hSrc, hTgt⟩
  · by_cases hNat : contract.recursorName == natRecName
    · have hp :
          some pilot =
            some
              { contract := contract
                obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
                value? := none } := by
          simpa [generatedRecursorPilot, hUnit, hNat] using hPilot.symm
      injection hp with hpilot
      subst hpilot
      refine ⟨natRecDeclEnv, natRecDeclEnv_wellFormed, ?_⟩
      intro rule hMem
      simp [generatedClosedIotaRules, generateClosedIotaRule_nat_zero,
        generateClosedIotaRule_nat_succ_still_open] at hMem
      subst hMem
      rcases natRecZeroClosedIotaRule_checked with ⟨A, hSrc, _, hTgt⟩
      exact ⟨A, hSrc, hTgt⟩
    · simp [generatedRecursorPilot, hUnit, hNat] at hPilot

theorem generatedRecursorPilot_generatedClosedIotaStep_sound_slice
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedClosedIotaStep pilot t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedClosedIotaStep pilot t u₁ →
        GeneratedClosedIotaStep pilot t u₂ →
        u₁ = u₂) := by
  rcases generatedRecursorPilot_generatedClosedIotaRules_checked_in_wellFormed_env hPilot with
    ⟨E, hWf, hTyped⟩
  refine ⟨E, hWf, ?_, ?_⟩
  · intro t u hStep
    rcases hStep with ⟨rule, hMem, rfl, rfl⟩
    exact hTyped rule hMem
  · exact generatedRecursorPilot_generatedClosedIotaStep_deterministic hPilot

theorem generatedRecursorPilot_generatedClosedIotaStep_sound_and_locally_confluent
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedClosedIotaStep pilot t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedClosedIotaStep pilot t u₁ →
        GeneratedClosedIotaStep pilot t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedClosedIotaStep pilot) u₁ v ∧
          Relation.ReflTransGen (GeneratedClosedIotaStep pilot) u₂ v) := by
  rcases generatedRecursorPilot_generatedClosedIotaStep_sound_slice hPilot with
    ⟨E, hWf, hTyped, _hDet⟩
  refine ⟨E, hWf, hTyped, ?_⟩
  intro t u₁ u₂ hStep₁ hStep₂
  exact generatedRecursorPilot_generatedClosedIotaStep_locally_confluent hPilot hStep₁ hStep₂

theorem generatedRecursorContractClosedIotaRules_eq_of_pilot
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    generatedRecursorContractClosedIotaRules contract = generatedClosedIotaRules pilot := by
  simp [generatedRecursorContractClosedIotaRules, hPilot]

theorem generatedRecursorContractOpenIotaObligations_eq_of_pilot
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    generatedRecursorContractOpenIotaObligations contract = generatedOpenIotaObligations pilot := by
  simp [generatedRecursorContractOpenIotaObligations, hPilot]

theorem generatedRecursorContractResolvedIotaObligations_eq_of_pilot
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    generatedRecursorContractResolvedIotaObligations contract =
      generatedResolvedIotaObligations pilot := by
  simp [generatedRecursorContractResolvedIotaObligations, hPilot]

theorem generatedRecursorPilot_resolved_obligations_nil
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    generatedResolvedIotaObligations pilot = [] := by
  by_cases hUnit : contract.recursorName == unitRecName
  · have hp :
        some pilot =
          some
            { contract := contract
              obligations := [unitRecCtorIotaObligation]
              value? := some unitRecValue } := by
        simpa [generatedRecursorPilot, hUnit] using hPilot.symm
    injection hp with hpilot
    subst hpilot
    exact generatedResolvedIotaObligations_unit_pilot
  · by_cases hNat : contract.recursorName == natRecName
    · have hp :
          some pilot =
            some
              { contract := contract
                obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
                value? := none } := by
          simpa [generatedRecursorPilot, hUnit, hNat] using hPilot.symm
      injection hp with hpilot
      subst hpilot
      exact generatedResolvedIotaObligations_nat_pilot
    · simp [generatedRecursorPilot, hUnit, hNat] at hPilot

theorem generatedRecursorContract_admitted_resolved_boundary
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    generatedRecursorContractResolvedIotaObligations contract = [] := by
  rcases hAdm with ⟨pilot, hPilot⟩
  rw [generatedRecursorContractResolvedIotaObligations_eq_of_pilot hPilot]
  exact generatedRecursorPilot_resolved_obligations_nil hPilot

theorem generatedRecursorContractClosedIotaStep_iff_pilot
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot)
    {t u : PureTm 0} :
    GeneratedRecursorContractClosedIotaStep contract t u ↔
      GeneratedClosedIotaStep pilot t u := by
  simp [GeneratedRecursorContractClosedIotaStep, GeneratedClosedIotaStep,
    generatedRecursorContractClosedIotaRules, hPilot]

theorem generatedRecursorContractClosedIotaRules_nonoverlapping
    (contract : FamilyRecursorDeclContract) :
    (generatedRecursorContractClosedIotaRules contract).Pairwise
      (fun rule₁ rule₂ => rule₁.source ≠ rule₂.source) := by
  cases hPilot : generatedRecursorPilot contract with
  | none =>
      simp [generatedRecursorContractClosedIotaRules, hPilot]
  | some pilot =>
      simpa [generatedRecursorContractClosedIotaRules, hPilot] using
        (generatedRecursorPilot_generatedClosedIotaRules_nonoverlapping
          (contract := contract) (pilot := pilot) hPilot)

theorem generatedClosedIotaTargetFromRules?_sound
    {rules : List GeneratedClosedIotaRule} {t u : PureTm 0}
    (h : generatedClosedIotaTargetFromRules? rules t = some u) :
    ∃ rule ∈ rules, t = rule.source ∧ u = rule.target := by
  induction rules with
  | nil =>
      simp [generatedClosedIotaTargetFromRules?] at h
  | cons rule rules ih =>
      by_cases hEq : rule.source = t
      · simp [generatedClosedIotaTargetFromRules?, hEq] at h
        cases h
        exact ⟨rule, by simp, hEq.symm, rfl⟩
      · simp [generatedClosedIotaTargetFromRules?, hEq] at h
        rcases ih h with ⟨rule', hMem, hSrc, hTgt⟩
        exact ⟨rule', by simp [hMem], hSrc, hTgt⟩

theorem generatedClosedIotaTargetFromRules?_complete
    {rules : List GeneratedClosedIotaRule} {t u : PureTm 0}
    (hPair : rules.Pairwise (fun rule₁ rule₂ => rule₁.source ≠ rule₂.source))
    (hStep : ∃ rule ∈ rules, t = rule.source ∧ u = rule.target) :
    generatedClosedIotaTargetFromRules? rules t = some u := by
  induction hPair with
  | nil =>
      rcases hStep with ⟨rule, hMem, _, _⟩
      simp at hMem
  | @cons rule rules hForall hTail ih =>
      rcases hStep with ⟨rule', hMem, hSrc, hTgt⟩
      simp at hMem
      rcases hMem with rfl | hMemTail
      · simp [generatedClosedIotaTargetFromRules?, hSrc.symm, hTgt]
      · have hNe : rule.source ≠ t := by
          intro hEq
          exact hForall rule' hMemTail (hEq.trans hSrc)
        simp [generatedClosedIotaTargetFromRules?, hNe]
        exact ih ⟨rule', hMemTail, hSrc, hTgt⟩

theorem generatedRecursorContractClosedIotaTarget?_sound
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (h : generatedRecursorContractClosedIotaTarget? contract t = some u) :
    GeneratedRecursorContractClosedIotaStep contract t u := by
  rcases generatedClosedIotaTargetFromRules?_sound h with ⟨rule, hMem, hSrc, hTgt⟩
  exact ⟨rule, hMem, hSrc, hTgt⟩

theorem generatedRecursorContractClosedIotaTarget?_complete
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hStep : GeneratedRecursorContractClosedIotaStep contract t u) :
    generatedRecursorContractClosedIotaTarget? contract t = some u := by
  exact generatedClosedIotaTargetFromRules?_complete
    (generatedRecursorContractClosedIotaRules_nonoverlapping contract)
    hStep

theorem generatedRecursorContractClosedIotaTarget?_eq_none_iff
    {contract : FamilyRecursorDeclContract} {t : PureTm 0} :
    generatedRecursorContractClosedIotaTarget? contract t = none ↔
      ¬ ∃ u : PureTm 0, GeneratedRecursorContractClosedIotaStep contract t u := by
  constructor
  · intro hNone hStep
    rcases hStep with ⟨u, hu⟩
    have hSome := generatedRecursorContractClosedIotaTarget?_complete hu
    rw [hNone] at hSome
    simp at hSome
  · intro hNo
    cases hTarget : generatedRecursorContractClosedIotaTarget? contract t with
    | none =>
        rfl
    | some u =>
        exfalso
        exact hNo ⟨u, generatedRecursorContractClosedIotaTarget?_sound hTarget⟩

theorem generatedRecursorContractOpenIotaObligations_unit :
    generatedRecursorContractOpenIotaObligations unitRecContract = [] := by
  simp [generatedRecursorContractOpenIotaObligations, generatedRecursorPilot_unit,
    generatedOpenIotaObligations, generateClosedIotaRule_unit]

theorem generatedRecursorContractOpenIotaObligations_nat :
    generatedRecursorContractOpenIotaObligations natRecContract = [natRecSuccIotaObligation] := by
  simp [generatedRecursorContractOpenIotaObligations,
    generatedRecursorPilot_nat_obligations_no_value, generatedOpenIotaObligations,
    generateClosedIotaRule_nat_zero, generateClosedIotaRule_nat_succ_still_open]

theorem generatedRecursorContractResolvedIotaObligations_nat :
    generatedRecursorContractResolvedIotaObligations natRecContract = [] := by
  simp [generatedRecursorContractResolvedIotaObligations,
    generatedRecursorPilot_nat_obligations_no_value,
    generatedResolvedIotaObligations, generateClosedIotaRule_nat_zero,
    generateUnaryOpenIotaRule?, natRecSuccIotaObligation]

theorem generatedRecursorContractClosedIotaStep_deterministic
    (contract : FamilyRecursorDeclContract) :
    ∀ {t u₁ u₂ : PureTm 0},
      GeneratedRecursorContractClosedIotaStep contract t u₁ →
      GeneratedRecursorContractClosedIotaStep contract t u₂ →
      u₁ = u₂ := by
  cases hPilot : generatedRecursorPilot contract with
  | none =>
      intro t u₁ u₂ hStep₁ hStep₂
      unfold GeneratedRecursorContractClosedIotaStep
        generatedRecursorContractClosedIotaRules at hStep₁
      simp [hPilot] at hStep₁
  | some pilot =>
      intro t u₁ u₂ hStep₁ hStep₂
      have hStep₁' :
          GeneratedClosedIotaStep pilot t u₁ := by
        rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
        exact hStep₁
      have hStep₂' :
          GeneratedClosedIotaStep pilot t u₂ := by
        rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
        exact hStep₂
      exact generatedRecursorPilot_generatedClosedIotaStep_deterministic hPilot hStep₁' hStep₂'

theorem generatedRecursorContractClosedIotaStep_locally_confluent
    (contract : FamilyRecursorDeclContract) :
    ∀ {t u₁ u₂ : PureTm 0},
      GeneratedRecursorContractClosedIotaStep contract t u₁ →
      GeneratedRecursorContractClosedIotaStep contract t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v := by
  cases hPilot : generatedRecursorPilot contract with
  | none =>
      intro t u₁ u₂ hStep₁ hStep₂
      unfold GeneratedRecursorContractClosedIotaStep
        generatedRecursorContractClosedIotaRules at hStep₁
      simp [hPilot] at hStep₁
  | some pilot =>
      intro t u₁ u₂ hStep₁ hStep₂
      have hStep₁' :
          GeneratedClosedIotaStep pilot t u₁ := by
        rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
        exact hStep₁
      have hStep₂' :
          GeneratedClosedIotaStep pilot t u₂ := by
        rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
        exact hStep₂
      rcases generatedRecursorPilot_generatedClosedIotaStep_locally_confluent hPilot hStep₁' hStep₂' with
        ⟨v, h₁, h₂⟩
      refine ⟨v, ?_, ?_⟩
      · exact reflTransGen_map
          (hRS := fun {x y} hyz =>
            (generatedRecursorContractClosedIotaStep_iff_pilot hPilot).2 hyz)
          h₁
      · exact reflTransGen_map
          (hRS := fun {x y} hyz =>
            (generatedRecursorContractClosedIotaStep_iff_pilot hPilot).2 hyz)
          h₂

theorem generatedRecursorContractClosedIotaStep_normalizes
    (contract : FamilyRecursorDeclContract)
    (t : PureTm 0) :
    ∃ u : PureTm 0,
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
      ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v := by
  classical
  cases hPilot : generatedRecursorPilot contract with
  | none =>
      refine ⟨t, Relation.ReflTransGen.refl, ?_⟩
      intro hNext
      rcases hNext with ⟨v, hStep⟩
      unfold GeneratedRecursorContractClosedIotaStep
        generatedRecursorContractClosedIotaRules at hStep
      simp [hPilot] at hStep
  | some pilot =>
      rcases generatedRecursorPilot_generatedClosedIotaStep_normalizes hPilot t with ⟨u, hStar, hIrred⟩
      refine ⟨u, ?_, ?_⟩
      · exact reflTransGen_map
          (hRS := fun {x y} hyz =>
            (generatedRecursorContractClosedIotaStep_iff_pilot hPilot).2 hyz)
          hStar
      · intro hNext
        rcases hNext with ⟨v, hStep⟩
        exact hIrred ⟨v, (generatedRecursorContractClosedIotaStep_iff_pilot hPilot).1 hStep⟩

theorem generatedRecursorContractClosedIotaStep_star_cases
    (contract : FamilyRecursorDeclContract) :
    ∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      u = t ∨ GeneratedRecursorContractClosedIotaStep contract t u := by
  cases hPilot : generatedRecursorPilot contract with
  | none =>
      intro t u hStar
      induction hStar with
      | refl =>
          exact Or.inl rfl
      | tail hxy hyz ih =>
          unfold GeneratedRecursorContractClosedIotaStep
            generatedRecursorContractClosedIotaRules at hyz
          simp [hPilot] at hyz
  | some pilot =>
      intro t u hStar
      have hStar' :
          Relation.ReflTransGen (GeneratedClosedIotaStep pilot) t u := by
        exact reflTransGen_map
          (hRS := fun {x y} hyz =>
            (generatedRecursorContractClosedIotaStep_iff_pilot hPilot).1 hyz)
          hStar
      rcases generatedRecursorPilot_generatedClosedIotaStep_star_cases hPilot hStar' with
        hEq | hStep
      · exact Or.inl hEq
      · exact Or.inr
          ((generatedRecursorContractClosedIotaStep_iff_pilot hPilot).2 hStep)

theorem generatedRecursorContractClosedIotaStep_confluent
    (contract : FamilyRecursorDeclContract) :
    ∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v := by
  intro t u₁ u₂ hStar₁ hStar₂
  rcases generatedRecursorContractClosedIotaStep_star_cases contract hStar₁ with rfl | hStep₁
  · exact ⟨u₂, hStar₂, Relation.ReflTransGen.refl⟩
  · rcases generatedRecursorContractClosedIotaStep_star_cases contract hStar₂ with rfl | hStep₂
    · exact ⟨u₁, Relation.ReflTransGen.refl, hStar₁⟩
    · have hEq :
          u₁ = u₂ :=
        generatedRecursorContractClosedIotaStep_deterministic contract hStep₁ hStep₂
      subst hEq
      exact ⟨u₁, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem generatedRecursorContractClosedIotaStep_irreducible_star_eq
    (contract : FamilyRecursorDeclContract)
    {t u : PureTm 0}
    (hIrred : ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract t v)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    u = t := by
  rcases generatedRecursorContractClosedIotaStep_star_cases contract hStar with hEq | hStep
  · exact hEq
  · exfalso
    exact hIrred ⟨u, hStep⟩

theorem generatedRecursorContractClosedIotaStep_unique_normal_form
    (contract : FamilyRecursorDeclContract) :
    ∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      (¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u₁ v) →
      (¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u₂ v) →
      u₁ = u₂ := by
  intro t u₁ u₂ hStar₁ hStar₂ hIrred₁ hIrred₂
  rcases generatedRecursorContractClosedIotaStep_confluent contract hStar₁ hStar₂ with
    ⟨v, hJoin₁, hJoin₂⟩
  have h₁ : v = u₁ :=
    generatedRecursorContractClosedIotaStep_irreducible_star_eq
      contract hIrred₁ hJoin₁
  have h₂ : v = u₂ :=
    generatedRecursorContractClosedIotaStep_irreducible_star_eq
      contract hIrred₂ hJoin₂
  exact h₁.symm.trans h₂

theorem generatedRecursorContractClosedIotaStep_target_irreducible
    {contract : FamilyRecursorDeclContract} {t u v : PureTm 0}
    (hStep : GeneratedRecursorContractClosedIotaStep contract t u) :
    ¬ GeneratedRecursorContractClosedIotaStep contract u v := by
  cases hPilot : generatedRecursorPilot contract with
  | none =>
      unfold GeneratedRecursorContractClosedIotaStep
        generatedRecursorContractClosedIotaRules at hStep
      simp [hPilot] at hStep
  | some pilot =>
      have hStep' :
          GeneratedClosedIotaStep pilot t u := by
        rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
        exact hStep
      intro hNext
      have hNext' :
          GeneratedClosedIotaStep pilot u v := by
        rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
        exact hNext
      exact generatedRecursorPilot_generatedClosedIotaStep_target_irreducible
        hPilot hStep' hNext'

theorem generatedRecursorContractClosedIotaNormalize_sound
    (contract : FamilyRecursorDeclContract) (t : PureTm 0) :
    Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t
      (generatedRecursorContractClosedIotaNormalize contract t) := by
  unfold generatedRecursorContractClosedIotaNormalize
  cases hTarget : generatedRecursorContractClosedIotaTarget? contract t with
  | none =>
      exact Relation.ReflTransGen.refl
  | some u =>
      exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        (generatedRecursorContractClosedIotaTarget?_sound hTarget)

theorem generatedRecursorContractClosedIotaNormalize_irreducible
    (contract : FamilyRecursorDeclContract) (t : PureTm 0) :
    ¬ ∃ v : PureTm 0,
      GeneratedRecursorContractClosedIotaStep contract
        (generatedRecursorContractClosedIotaNormalize contract t) v := by
  unfold generatedRecursorContractClosedIotaNormalize
  cases hTarget : generatedRecursorContractClosedIotaTarget? contract t with
  | none =>
      simpa [hTarget] using
        (generatedRecursorContractClosedIotaTarget?_eq_none_iff
          (contract := contract) (t := t)).1 hTarget
  | some u =>
      have hStep :
          GeneratedRecursorContractClosedIotaStep contract t u :=
        generatedRecursorContractClosedIotaTarget?_sound hTarget
      intro hNext
      rcases hNext with ⟨v, hv⟩
      exact generatedRecursorContractClosedIotaStep_target_irreducible hStep hv

theorem generatedRecursorContractClosedIotaNormalize_complete
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u)
    (hIrred : ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) :
    generatedRecursorContractClosedIotaNormalize contract t = u := by
  exact generatedRecursorContractClosedIotaStep_unique_normal_form contract
    (generatedRecursorContractClosedIotaNormalize_sound contract t)
    hStar
    (generatedRecursorContractClosedIotaNormalize_irreducible contract t)
    hIrred

theorem generatedRecursorContractClosedIotaJoinable_iff_normalize_eq
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0} :
    GeneratedRecursorContractClosedIotaJoinable contract t u ↔
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u := by
  constructor
  · intro hJoin
    rcases hJoin with ⟨v, htv, huv⟩
    rcases generatedRecursorContractClosedIotaStep_normalizes contract v with
      ⟨n, hvn, hIrred⟩
    have htn :
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t n :=
      Relation.ReflTransGen.trans htv hvn
    have hun :
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u n :=
      Relation.ReflTransGen.trans huv hvn
    have htEq :
        generatedRecursorContractClosedIotaNormalize contract t = n :=
      generatedRecursorContractClosedIotaNormalize_complete htn hIrred
    have huEq :
        generatedRecursorContractClosedIotaNormalize contract u = n :=
      generatedRecursorContractClosedIotaNormalize_complete hun hIrred
    exact htEq.trans huEq.symm
  · intro hEq
    refine ⟨generatedRecursorContractClosedIotaNormalize contract u, ?_,
      generatedRecursorContractClosedIotaNormalize_sound contract u⟩
    simpa [hEq] using generatedRecursorContractClosedIotaNormalize_sound contract t

instance instDecidableGeneratedRecursorContractClosedIotaJoinable
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) :
    Decidable (GeneratedRecursorContractClosedIotaJoinable contract t u) :=
  decidable_of_iff' _
    (generatedRecursorContractClosedIotaJoinable_iff_normalize_eq
      (contract := contract) (t := t) (u := u))

def generatedRecursorContractClosedIotaJoinByNormalization?
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) :
    Option (GeneratedRecursorContractClosedIotaJoinWitness contract t u) :=
  if h :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u then
    some ⟨(generatedRecursorContractClosedIotaJoinable_iff_normalize_eq).2 h⟩
  else
    none

theorem generatedRecursorContractClosedIotaJoinByNormalization?_sound
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    {w : GeneratedRecursorContractClosedIotaJoinWitness contract t u}
    (h : generatedRecursorContractClosedIotaJoinByNormalization? contract t u = some w) :
    GeneratedRecursorContractClosedIotaJoinable contract t u := by
  by_cases hDef :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u
  · simp [generatedRecursorContractClosedIotaJoinByNormalization?, hDef] at h
    cases h
    exact w.joinable
  · simp [generatedRecursorContractClosedIotaJoinByNormalization?, hDef] at h

theorem generatedRecursorContractClosedIotaJoinByNormalization?_complete
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hJoin : GeneratedRecursorContractClosedIotaJoinable contract t u) :
    ∃ w : GeneratedRecursorContractClosedIotaJoinWitness contract t u,
      generatedRecursorContractClosedIotaJoinByNormalization? contract t u = some w := by
  let w : GeneratedRecursorContractClosedIotaJoinWitness contract t u := ⟨hJoin⟩
  refine ⟨w, ?_⟩
  have hEq :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u :=
    (generatedRecursorContractClosedIotaJoinable_iff_normalize_eq).1 hJoin
  simp [generatedRecursorContractClosedIotaJoinByNormalization?, hEq, w]

theorem generatedRecursorContractClosedIotaStep_implies_conv
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (h : GeneratedRecursorContractClosedIotaStep contract t u) :
    GeneratedRecursorContractClosedIotaConv contract t u :=
  Relation.EqvGen.rel _ _ h

theorem generatedRecursorContractClosedIotaStep_to_star
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (h : GeneratedRecursorContractClosedIotaStep contract t u) :
    Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl h

theorem generatedRecursorContractClosedIotaStar_implies_conv
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (h : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    GeneratedRecursorContractClosedIotaConv contract t u := by
  induction h with
  | refl =>
      exact Relation.EqvGen.refl _
  | tail hxy hyz ih =>
      exact Relation.EqvGen.trans _ _ _ ih
        (generatedRecursorContractClosedIotaStep_implies_conv hyz)

theorem generatedRecursorContractClosedIotaConv_implies_joinable
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (h : GeneratedRecursorContractClosedIotaConv contract t u) :
    GeneratedRecursorContractClosedIotaJoinable contract t u := by
  refine Relation.EqvGen.rec ?hrel ?hrefl ?hsymm ?htrans h
  · intro a b hab
    exact ⟨b, generatedRecursorContractClosedIotaStep_to_star hab, Relation.ReflTransGen.refl⟩
  · intro a
    exact ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  · intro a b hab ih
    rcases ih with ⟨v, hav, hbv⟩
    exact ⟨v, hbv, hav⟩
  · intro a b c hab hbc ihab ihbc
    rcases ihab with ⟨u₁, ha_u₁, hb_u₁⟩
    rcases ihbc with ⟨u₂, hb_u₂, hc_u₂⟩
    rcases generatedRecursorContractClosedIotaStep_confluent contract hb_u₁ hb_u₂ with
      ⟨w, hu₁_w, hu₂_w⟩
    exact ⟨w, Relation.ReflTransGen.trans ha_u₁ hu₁_w,
      Relation.ReflTransGen.trans hc_u₂ hu₂_w⟩

theorem generatedRecursorContractClosedIotaJoinable_implies_conv
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hJoin : GeneratedRecursorContractClosedIotaJoinable contract t u) :
    GeneratedRecursorContractClosedIotaConv contract t u := by
  rcases hJoin with ⟨v, htv, huv⟩
  exact Relation.EqvGen.trans _ _ _
    (generatedRecursorContractClosedIotaStar_implies_conv htv)
    (Relation.EqvGen.symm _ _ (generatedRecursorContractClosedIotaStar_implies_conv huv))

theorem generatedRecursorContractClosedIotaConv_iff_normalize_eq
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0} :
    GeneratedRecursorContractClosedIotaConv contract t u ↔
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u := by
  constructor
  · intro hConv
    exact (generatedRecursorContractClosedIotaJoinable_iff_normalize_eq).1
      (generatedRecursorContractClosedIotaConv_implies_joinable hConv)
  · intro hEq
    exact generatedRecursorContractClosedIotaJoinable_implies_conv
      ((generatedRecursorContractClosedIotaJoinable_iff_normalize_eq).2 hEq)

instance instDecidableGeneratedRecursorContractClosedIotaConv
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) :
    Decidable (GeneratedRecursorContractClosedIotaConv contract t u) :=
  decidable_of_iff' _
    (generatedRecursorContractClosedIotaConv_iff_normalize_eq
      (contract := contract) (t := t) (u := u))

def generatedRecursorContractClosedIotaConvByNormalization?
    (contract : FamilyRecursorDeclContract) (t u : PureTm 0) :
    Option (GeneratedRecursorContractClosedIotaConvWitness contract t u) :=
  if h :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u then
    some ⟨(generatedRecursorContractClosedIotaConv_iff_normalize_eq).2 h⟩
  else
    none

theorem generatedRecursorContractClosedIotaConvByNormalization?_sound
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    {w : GeneratedRecursorContractClosedIotaConvWitness contract t u}
    (h : generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w) :
    GeneratedRecursorContractClosedIotaConv contract t u := by
  by_cases hDef :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u
  · simp [generatedRecursorContractClosedIotaConvByNormalization?, hDef] at h
    cases h
    exact w.conv
  · simp [generatedRecursorContractClosedIotaConvByNormalization?, hDef] at h

theorem generatedRecursorContractClosedIotaConvByNormalization?_complete
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hConv : GeneratedRecursorContractClosedIotaConv contract t u) :
    ∃ w : GeneratedRecursorContractClosedIotaConvWitness contract t u,
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w := by
  let w : GeneratedRecursorContractClosedIotaConvWitness contract t u := ⟨hConv⟩
  refine ⟨w, ?_⟩
  have hEq :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u :=
    (generatedRecursorContractClosedIotaConv_iff_normalize_eq).1 hConv
  simp [generatedRecursorContractClosedIotaConvByNormalization?, hEq, w]

theorem generatedRecursorContractClosedIotaConvByNormalization?_eq_some_iff
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0} :
    (∃ w : GeneratedRecursorContractClosedIotaConvWitness contract t u,
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w) ↔
        GeneratedRecursorContractClosedIotaConv contract t u := by
  constructor
  · rintro ⟨w, hw⟩
    exact generatedRecursorContractClosedIotaConvByNormalization?_sound hw
  · intro hConv
    exact generatedRecursorContractClosedIotaConvByNormalization?_complete hConv

theorem generatedRecursorContractClosedIotaConvByNormalization?_eq_none_iff
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0} :
    generatedRecursorContractClosedIotaConvByNormalization? contract t u = none ↔
      ¬ GeneratedRecursorContractClosedIotaConv contract t u := by
  by_cases hEq :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u
  · have hConv : GeneratedRecursorContractClosedIotaConv contract t u :=
      (generatedRecursorContractClosedIotaConv_iff_normalize_eq).2 hEq
    simp [generatedRecursorContractClosedIotaConvByNormalization?, hEq, hConv]
  · have hNotConv : ¬ GeneratedRecursorContractClosedIotaConv contract t u := by
      intro hConv
      exact hEq ((generatedRecursorContractClosedIotaConv_iff_normalize_eq).1 hConv)
    simp [generatedRecursorContractClosedIotaConvByNormalization?, hEq, hNotConv]

theorem generatedRecursorContractClosedIotaConvByNormalization?_ne_none_iff
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0} :
    generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none ↔
      GeneratedRecursorContractClosedIotaConv contract t u := by
  constructor
  · intro hSome
    cases hCheck : generatedRecursorContractClosedIotaConvByNormalization? contract t u with
    | none =>
        contradiction
    | some w =>
        exact generatedRecursorContractClosedIotaConvByNormalization?_sound hCheck
  · intro hConv
    rcases generatedRecursorContractClosedIotaConvByNormalization?_complete hConv with ⟨w, hw⟩
    simp [hw]

theorem generatedRecursorContractClosedIotaStep_sound_and_locally_confluent
    {contract : FamilyRecursorDeclContract} {pilot : GeneratedRecursorPilot}
    (hPilot : generatedRecursorPilot contract = some pilot) :
    ∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) := by
  rcases generatedRecursorPilot_generatedClosedIotaStep_sound_and_locally_confluent hPilot with
    ⟨E, hWf, hTyped, hLC⟩
  refine ⟨E, hWf, ?_, ?_⟩
  · intro t u hStep
    have hStep' :
        GeneratedClosedIotaStep pilot t u := by
      rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
      exact hStep
    exact hTyped hStep'
  · intro t u₁ u₂ hStep₁ hStep₂
    have hStep₁' :
        GeneratedClosedIotaStep pilot t u₁ := by
      rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
      exact hStep₁
    have hStep₂' :
        GeneratedClosedIotaStep pilot t u₂ := by
      rw [← generatedRecursorContractClosedIotaStep_iff_pilot hPilot]
      exact hStep₂
    rcases hLC hStep₁' hStep₂' with ⟨v, h₁, h₂⟩
    refine ⟨v, ?_, ?_⟩
    · exact reflTransGen_map
        (hRS := fun {x y} hyz =>
          (generatedRecursorContractClosedIotaStep_iff_pilot hPilot).2 hyz)
        h₁
    · exact reflTransGen_map
        (hRS := fun {x y} hyz =>
          (generatedRecursorContractClosedIotaStep_iff_pilot hPilot).2 hyz)
        h₂

theorem generatedRecursorContract_admitted_sound_and_locally_confluent
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    ∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) := by
  rcases hAdm with ⟨pilot, hPilot⟩
  exact generatedRecursorContractClosedIotaStep_sound_and_locally_confluent hPilot

theorem generatedRecursorContract_admitted_sound_confluent_and_normalizing
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A)) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  rcases generatedRecursorContract_admitted_sound_and_locally_confluent hAdm with
    ⟨E, hWf, hTyped, _hLC⟩
  exact ⟨⟨E, hWf, hTyped⟩,
    generatedRecursorContractClosedIotaStep_confluent contract,
    generatedRecursorContractClosedIotaStep_normalizes contract⟩

theorem generatedRecursorContract_admitted_open_boundary
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    generatedRecursorContractOpenIotaObligations contract = [] ∨
      (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
        ∃ A : PureTm 1,
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  by_cases hUnitName : contract.recursorName == unitRecName
  · left
    simp [generatedRecursorContractOpenIotaObligations, generatedRecursorPilot, hUnitName,
      generatedOpenIotaObligations, generateClosedIotaRule_unit]
  · by_cases hNatName : contract.recursorName == natRecName
    · right
      refine ⟨?_, natRecSuccOpenIotaRule_checked⟩
      simp [generatedRecursorContractOpenIotaObligations, generatedRecursorPilot, hUnitName, hNatName,
        generatedOpenIotaObligations, generateClosedIotaRule_nat_zero,
        generateClosedIotaRule_nat_succ_still_open]
    · simp [GeneratedRecursorContractAdmitted, generatedRecursorPilot, hUnitName, hNatName] at hAdm

theorem generatedRecursorContract_admitted_current_boundary
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (generatedRecursorContractOpenIotaObligations contract = [] ∨
      (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
        ∃ A : PureTm 1,
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)) := by
  exact ⟨generatedRecursorContract_admitted_sound_and_locally_confluent hAdm,
    generatedRecursorContract_admitted_open_boundary hAdm⟩

abbrev GeneratedRecursorCurrentGateWitness
    (contract : FamilyRecursorDeclContract) : Prop :=
  ∃ E : DeclEnv,
    DeclEnvWellFormed E ∧
    (∀ {t u : PureTm 0},
      GeneratedRecursorContractClosedIotaStep contract t u →
        ∃ A : PureTm 0,
          HasTypeDecl E .nil t A ∧
          HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      GeneratedRecursorContractClosedIotaStep contract t u₁ →
      GeneratedRecursorContractClosedIotaStep contract t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)

abbrev GeneratedRecursorAdmittedOpenBoundary
    (contract : FamilyRecursorDeclContract) : Prop :=
  generatedRecursorContractOpenIotaObligations contract = [] ∨
    (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)

abbrev GeneratedRecursorDeclStarPreservationPackage
    (E : DeclEnv) : Prop :=
  DeclarationSemantics.DeclStarPreservationPackage E

abbrev GeneratedRecursorDeclStarConfluencePackage
    (E : DeclEnv) : Prop :=
  DeclarationSemantics.DeclStarConfluencePackage E

abbrev GeneratedRecursorDeclPiInjectivityPackage
    (E : DeclEnv) : Prop :=
  DeclarationSemantics.DeclPiInjectivityPackage E

abbrev GeneratedRecursorDeclSigmaInjectivityPackage
    (E : DeclEnv) : Prop :=
  DeclarationSemantics.DeclSigmaInjectivityPackage E

abbrev GeneratedRecursorDeclChurchRosserPackage
    (E : DeclEnv) : Prop :=
  DeclarationSemantics.DeclChurchRosserFrontierPackage E

abbrev GeneratedRecursorClosedSliceChurchRosserPackage
    (E : DeclEnv) (contract : FamilyRecursorDeclContract) : Prop :=
  (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl E t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl E t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl E t u)

abbrev GeneratedRecursorDeclAndSliceChurchRosserPackage
    (E : DeclEnv) (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorDeclChurchRosserPackage E ∧
    GeneratedRecursorClosedSliceChurchRosserPackage E contract

abbrev GeneratedRecursorDeclNoValuesNormalizationPackage
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none) : Prop :=
  DeclarationSemantics.DeclNoValuesNormalizationPackage E hNone

abbrev GeneratedRecursorDeclAndSliceNoValuesPackage
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none)
    (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorDeclAndSliceChurchRosserPackage E contract ∧
    GeneratedRecursorDeclNoValuesNormalizationPackage E hNone

abbrev GeneratedRecursorCurrentGatePackage
    (contract : FamilyRecursorDeclContract) : Prop :=
  ∃ E : DeclEnv,
    DeclEnvWellFormed E ∧
    (∀ {t u : PureTm 0},
      GeneratedRecursorContractClosedIotaStep contract t u →
        ∃ A : PureTm 0,
          HasTypeDecl E .nil t A ∧
          HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      GeneratedRecursorContractClosedIotaStep contract t u₁ →
      GeneratedRecursorContractClosedIotaStep contract t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)

abbrev GeneratedRecursorPilotCoveragePackage
    (contract : FamilyRecursorDeclContract) : Prop :=
  ∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
    generatedRecursorPilot contract = some pilot →
    obligation ∈ pilot.obligations →
    ∃ rule : GeneratedClosedIotaRule,
      rule ∈ generatedRecursorContractClosedIotaRules contract ∧
      generateClosedIotaRule? obligation = some rule

abbrev GeneratedRecursorConditionalDeclFrontierPackage
    (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorCurrentGatePackage contract ∧
    GeneratedRecursorClosedSliceChurchRosserPackage unitRecDeclEnv contract ∧
    GeneratedRecursorPilotCoveragePackage contract

abbrev GeneratedRecursorAdmittedExactConditionalFrontierPackage
    (contract : FamilyRecursorDeclContract) : Prop :=
  (contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
    GeneratedRecursorConditionalDeclFrontierPackage contract)
  ∨
  (contract.recursorName = natRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
    ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
    ∃ A : PureTm 1,
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)

abbrev GeneratedRecursorCurrentBoundaryConditionalFrontierPackage
    (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorCurrentGateWitness contract ∧
    GeneratedRecursorAdmittedOpenBoundary contract ∧
    GeneratedRecursorAdmittedExactConditionalFrontierPackage contract

/-- Exact admitted frontier package after resolving generator obligations
through either closed rules or the generic unary-open realization path. The
Unit branch remains fully closed; the Nat branch now records an empty resolved
generator boundary while honestly preserving the fact that the current
declaration-side closed slice does not realize the successor rule as a closed
`δ`-step. -/
abbrev GeneratedRecursorAdmittedExactResolvedFrontierPackage
    (contract : FamilyRecursorDeclContract) : Prop :=
  (contract.recursorName = unitRecName ∧
    generatedRecursorContractResolvedIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
    GeneratedRecursorConditionalDeclFrontierPackage contract)
  ∨
  (contract.recursorName = natRecName ∧
    generatedRecursorContractResolvedIotaObligations contract = [] ∧
    ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
    ∃ A : PureTm 1,
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)

/-- Active current-boundary package for the recursor lane once the generator
frontier has been resolved. This replaces the older "open nat exception"
language in consumers that only need the live boundary, while still allowing
the exact Nat declaration-side limitation to be recovered from the stronger
resolved package above. -/
abbrev GeneratedRecursorCurrentBoundaryResolvedFrontierPackage
    (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorCurrentGateWitness contract ∧
    generatedRecursorContractResolvedIotaObligations contract = [] ∧
    GeneratedRecursorAdmittedExactResolvedFrontierPackage contract

/-- Generic current-boundary package for declaration environments whose
declaration-side frontier is known up to Church-Rosser/injectivity. This is
the exact forgetful target of the stronger no-values package below. -/
abbrev GeneratedRecursorCurrentBoundaryChurchRosserFrontierPackage
    (E : DeclEnv) (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorCurrentGateWitness contract ∧
    GeneratedRecursorAdmittedOpenBoundary contract ∧
    GeneratedRecursorDeclAndSliceChurchRosserPackage E contract

/-- Strongest current-boundary package on the declaration side: the admitted
recursor boundary paired with the assumption-free all-none declaration
frontier, including normalization-sound conversion. -/
abbrev GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none)
    (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorCurrentGateWitness contract ∧
    GeneratedRecursorAdmittedOpenBoundary contract ∧
    GeneratedRecursorDeclAndSliceNoValuesPackage E hNone contract

/-- Exact admitted frontier package when the declaration side is known up to
Church-Rosser/injectivity. The closed Unit branch carries the full
declaration-side slice package; the Nat branch remains the open typed witness
for the still-unclosed successor rule. -/
abbrev GeneratedRecursorAdmittedExactChurchRosserFrontierPackage
    (E : DeclEnv) (contract : FamilyRecursorDeclContract) : Prop :=
  (contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn E contract ∧
    GeneratedRecursorCurrentBoundaryChurchRosserFrontierPackage E contract)
  ∨
  (contract.recursorName = natRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
    ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
    ∃ A : PureTm 1,
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)

/-- Exact admitted frontier package on the assumption-free all-none slice.
This is strictly stronger than the Church-Rosser package because it also
packages normalization-sound conversion on the declaration side. -/
abbrev GeneratedRecursorAdmittedExactNoValuesFrontierPackage
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none)
    (contract : FamilyRecursorDeclContract) : Prop :=
  (contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn E contract ∧
    GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage E hNone contract)
  ∨
  (contract.recursorName = natRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
    ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
    ∃ A : PureTm 1,
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
      HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)

theorem GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage.asChurchRosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    {hNone : ∀ c : DeclName, valueOf? E c = none}
    (hPkg : GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage E hNone contract) :
    GeneratedRecursorCurrentBoundaryChurchRosserFrontierPackage E contract := by
  exact ⟨hPkg.1, hPkg.2.1, hPkg.2.2.1⟩

theorem GeneratedRecursorAdmittedExactNoValuesFrontierPackage.asChurchRosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    {hNone : ∀ c : DeclName, valueOf? E c = none}
    (hPkg : GeneratedRecursorAdmittedExactNoValuesFrontierPackage E hNone contract) :
    GeneratedRecursorAdmittedExactChurchRosserFrontierPackage E contract := by
  rcases hPkg with hUnit | hNat
  · left
    exact
      ⟨ hUnit.1
      , hUnit.2.1
      , hUnit.2.2.1
      , hUnit.2.2.2.1
      , GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage.asChurchRosser
          hUnit.2.2.2.2
      ⟩
  · right
    exact hNat

/-- Fully-closed recursor frontier on the declaration side when we know only
Church-Rosser/injectivity. This is the value-bearing shape: enough for SR,
confluence, and conversion transport, but not the stronger all-none
normalization witness. -/
abbrev GeneratedRecursorChurchRosserDeclFrontierPackage
    (E : DeclEnv) (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorCurrentGatePackage contract ∧
    GeneratedRecursorDeclAndSliceChurchRosserPackage E contract ∧
    GeneratedRecursorPilotCoveragePackage contract

/-- Strongest fully-closed declaration-side recursor frontier: the current gate,
the declaration/slice package, and pilot coverage, all on the assumption-free
all-none slice. -/
abbrev GeneratedRecursorNoValuesDeclFrontierPackage
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none)
    (contract : FamilyRecursorDeclContract) : Prop :=
  GeneratedRecursorCurrentGatePackage contract ∧
    GeneratedRecursorDeclAndSliceNoValuesPackage E hNone contract ∧
    GeneratedRecursorPilotCoveragePackage contract

/-- Exact closed Unit branch packaged on the declaration-side Church-Rosser
frontier. -/
abbrev GeneratedRecursorExactClosedChurchRosserDeclFrontierPackage
    (E : DeclEnv) (contract : FamilyRecursorDeclContract) : Prop :=
  contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn E contract ∧
    GeneratedRecursorChurchRosserDeclFrontierPackage E contract

/-- Exact closed Unit branch packaged on the strongest all-none declaration
frontier. -/
abbrev GeneratedRecursorExactClosedNoValuesDeclFrontierPackage
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none)
    (contract : FamilyRecursorDeclContract) : Prop :=
  contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn E contract ∧
    GeneratedRecursorNoValuesDeclFrontierPackage E hNone contract

theorem GeneratedRecursorNoValuesDeclFrontierPackage.asChurchRosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    {hNone : ∀ c : DeclName, valueOf? E c = none}
    (hPkg : GeneratedRecursorNoValuesDeclFrontierPackage E hNone contract) :
    GeneratedRecursorChurchRosserDeclFrontierPackage E contract := by
  exact ⟨hPkg.1, hPkg.2.1.1, hPkg.2.2⟩

theorem GeneratedRecursorExactClosedNoValuesDeclFrontierPackage.asChurchRosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    {hNone : ∀ c : DeclName, valueOf? E c = none}
    (hPkg : GeneratedRecursorExactClosedNoValuesDeclFrontierPackage E hNone contract) :
    GeneratedRecursorExactClosedChurchRosserDeclFrontierPackage E contract := by
  exact
    ⟨ hPkg.1
    , hPkg.2.1
    , hPkg.2.2.1
    , hPkg.2.2.2.1
    , GeneratedRecursorNoValuesDeclFrontierPackage.asChurchRosser hPkg.2.2.2.2
    ⟩

theorem generatedRecursorContract_unit_named_fullyClosed
    {contract : FamilyRecursorDeclContract}
    (hUnit : contract.recursorName = unitRecName) :
    GeneratedRecursorContractFullyClosed contract := by
  refine ⟨?_, ?_⟩
  · exact ⟨{ contract := contract
             obligations := [unitRecCtorIotaObligation]
             value? := some unitRecValue },
      by simp [generatedRecursorPilot, hUnit]⟩
  · simp [generatedRecursorContractOpenIotaObligations, generatedRecursorPilot, hUnit,
      generatedOpenIotaObligations, generateClosedIotaRule_unit]

theorem generatedRecursorContract_nat_named_open_boundary
    {contract : FamilyRecursorDeclContract}
    (hNat : contract.recursorName = natRecName) :
    generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] := by
  have hNeUnitNat : natRecName ≠ unitRecName := by decide
  have hPilot :
      generatedRecursorPilot contract =
        some
          { contract := contract
            obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
            value? := none } := by
    simp [generatedRecursorPilot, hNat, hNeUnitNat]
  simp [generatedRecursorContractOpenIotaObligations, hPilot, generatedOpenIotaObligations,
    generateClosedIotaRule_nat_zero, generateClosedIotaRule_nat_succ_still_open]

theorem generatedRecursorContract_nat_named_closed_slice_not_realized_in_current_decl_env
    {contract : FamilyRecursorDeclContract}
    (hNat : contract.recursorName = natRecName) :
    ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract := by
  intro hReal
  apply natRecZeroClosedIotaRule_not_realized_in_current_decl_env
  have hNeUnitNat : natRecName ≠ unitRecName := by decide
  have hPilot :
      generatedRecursorPilot contract =
        some
          { contract := contract
            obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
            value? := none } := by
    simp [generatedRecursorPilot, hNat, hNeUnitNat]
  have hStep :
      GeneratedRecursorContractClosedIotaStep
        contract
        natRecZeroClosedIotaRule.source
        natRecZeroClosedIotaRule.target := by
    refine ⟨natRecZeroClosedIotaRule, ?_, rfl, rfl⟩
    simp [generatedRecursorContractClosedIotaRules, hPilot, generatedClosedIotaRules,
      generateClosedIotaRule_nat_zero,
      generateClosedIotaRule_nat_succ_still_open]
  exact hReal hStep

theorem generatedRecursorContract_fullyClosed_covers_all_obligations
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract) :
    ∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule := by
  intro pilot obligation hPilot hMem
  rcases generatedRecursorPilot_obligation_closed_or_open (pilot := pilot) hMem with hOpen | hClosed
  · have hOpenEq :
        generatedOpenIotaObligations pilot = [] := by
      rw [← generatedRecursorContractOpenIotaObligations_eq_of_pilot hPilot]
      exact hFull.2
    simp [hOpenEq] at hOpen
  · rcases hClosed with ⟨rule, hRuleMem, hRuleEq⟩
    refine ⟨rule, ?_, hRuleEq⟩
    rw [generatedRecursorContractClosedIotaRules_eq_of_pilot hPilot]
    exact hRuleMem

theorem generatedRecursorContract_fullyClosed_sound_and_complete_current_gate
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  exact ⟨generatedRecursorContract_admitted_sound_and_locally_confluent hFull.1,
    generatedRecursorContract_fullyClosed_covers_all_obligations hFull⟩

theorem unitRecContract_fullyClosed :
    GeneratedRecursorContractFullyClosed unitRecContract := by
  refine ⟨?_, generatedRecursorContractOpenIotaObligations_unit⟩
  exact ⟨_, generatedRecursorPilot_unit⟩

theorem natRecContract_not_fullyClosed :
    ¬ GeneratedRecursorContractFullyClosed natRecContract := by
  intro hFull
  rcases hFull with ⟨_, hOpen⟩
  rw [generatedRecursorContractOpenIotaObligations_nat] at hOpen
  simp at hOpen

theorem generatedRecursorContract_fullyClosed_is_unit
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract) :
    contract.recursorName = unitRecName := by
  by_cases hUnit : contract.recursorName = unitRecName
  · exact hUnit
  · by_cases hNat : contract.recursorName = natRecName
    · exfalso
      have hOpen := hFull.2
      have hNeUnitNat : natRecName ≠ unitRecName := by decide
      simp [generatedRecursorContractOpenIotaObligations, generatedRecursorPilot,
        hNat, hNeUnitNat, generatedOpenIotaObligations, generateClosedIotaRule_nat_zero,
        generateClosedIotaRule_nat_succ_still_open] at hOpen
    · exfalso
      have hAdm := hFull.1
      simp [GeneratedRecursorContractAdmitted, generatedRecursorPilot, hUnit, hNat] at hAdm

theorem generatedRecursorContract_fullyClosed_rules_eq_unit
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract) :
    generatedRecursorContractClosedIotaRules contract = [unitRecCtorClosedIotaRule] := by
  have hUnit : contract.recursorName = unitRecName :=
    generatedRecursorContract_fullyClosed_is_unit hFull
  simp [generatedRecursorContractClosedIotaRules, generatedRecursorPilot, hUnit,
    generatedClosedIotaRules, generateClosedIotaRule_unit]

theorem generatedRecursorContract_fullyClosed_step_realizes_redStarDecl
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hStep : GeneratedRecursorContractClosedIotaStep contract t u) :
    RedStarDecl unitRecDeclEnv t u := by
  have hRules :
      generatedRecursorContractClosedIotaRules contract = [unitRecCtorClosedIotaRule] :=
    generatedRecursorContract_fullyClosed_rules_eq_unit hFull
  unfold GeneratedRecursorContractClosedIotaStep at hStep
  rw [hRules] at hStep
  simp at hStep
  rcases hStep with ⟨hSrc, hTgt⟩
  subst hSrc
  subst hTgt
  exact unitRecCtorClosedIotaRule_realizes_redStarDecl

theorem generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv} {t u : PureTm 0}
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    RedStarDecl E t u := by
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.trans ih (hReal hyz)

theorem generatedRecursorContract_fullyClosed_star_realizes_redStarDecl
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    RedStarDecl unitRecDeclEnv t u := by
  induction hStar with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.trans ih
        (generatedRecursorContract_fullyClosed_step_realizes_redStarDecl hFull hyz)

theorem generatedRecursorContract_declSR_bridge_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') :
    ∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      GeneratedRecursorContractClosedIotaStep contract t u →
      HasTypeDecl E .nil u A := by
  intro t u A hTy hStep
  have hRed : RedStarDecl E t u := hReal hStep
  exact DeclarationSemantics.redStarDecl_preserves_type_of_injective
    (E := E)
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (hWf := hWf)
    (ht := hTy)
    (hs := hRed)

theorem generatedRecursorContract_fullyClosed_realized_in_unit
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract) :
    GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract := by
  intro t u hStep
  exact generatedRecursorContract_fullyClosed_step_realizes_redStarDecl hFull hStep

theorem generatedRecursorContractClosedIotaConvDecl_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv} {t u : PureTm 0}
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hConv : GeneratedRecursorContractClosedIotaConv contract t u) :
    ConvDecl E t u := by
  refine Relation.EqvGen.rec ?hrel ?hrefl ?hsymm ?htrans hConv
  · intro a b hab
    exact DeclarationSemantics.redStarDecl_implies_conv (hReal hab)
  · intro a
    exact Relation.EqvGen.refl _
  · intro a b hab ih
    exact Relation.EqvGen.symm _ _ ih
  · intro a b c hab hbc ihab ihbc
    exact Relation.EqvGen.trans _ _ _ ihab ihbc

theorem generatedRecursorContractClosedIotaConvByNormalization?_sound_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv} {t u : PureTm 0}
    {w : GeneratedRecursorContractClosedIotaConvWitness contract t u}
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (h :
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w) :
    ConvDecl E t u := by
  exact generatedRecursorContractClosedIotaConvDecl_of_realization hReal
    (generatedRecursorContractClosedIotaConvByNormalization?_sound h)

theorem generatedRecursorContractClosedIotaNormalize_convDecl_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv} (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (t : PureTm 0) :
    ConvDecl E t (generatedRecursorContractClosedIotaNormalize contract t) := by
  exact DeclarationSemantics.redStarDecl_implies_conv
    (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
      hReal (generatedRecursorContractClosedIotaNormalize_sound contract t))

theorem generatedRecursorContractClosedIotaNormalize_eq_implies_convDecl_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv} (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    {t u : PureTm 0}
    (hEq :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u) :
    ConvDecl E t u := by
  have ht :
      ConvDecl E t (generatedRecursorContractClosedIotaNormalize contract t) :=
    generatedRecursorContractClosedIotaNormalize_convDecl_of_realization hReal t
  have hu :
      ConvDecl E u (generatedRecursorContractClosedIotaNormalize contract u) :=
    generatedRecursorContractClosedIotaNormalize_convDecl_of_realization hReal u
  have hu' :
      ConvDecl E u (generatedRecursorContractClosedIotaNormalize contract t) := by
    simpa [hEq] using hu
  exact Relation.EqvGen.trans _ _ _ ht (Relation.EqvGen.symm _ _ hu')

theorem generatedRecursorContract_unit_named_realized_in_unit
    {contract : FamilyRecursorDeclContract}
    (hUnit : contract.recursorName = unitRecName) :
    GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract := by
  exact generatedRecursorContract_fullyClosed_realized_in_unit
    (generatedRecursorContract_unit_named_fullyClosed hUnit)

theorem generatedRecursorContract_admitted_realization_boundary
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (contract.recursorName = unitRecName ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract)
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract) := by
  by_cases hUnit : contract.recursorName = unitRecName
  · left
    exact ⟨hUnit,
      generatedRecursorContract_unit_named_fullyClosed hUnit,
      generatedRecursorContract_unit_named_realized_in_unit hUnit⟩
  · by_cases hNat : contract.recursorName = natRecName
    · right
      exact ⟨hNat,
        generatedRecursorContract_nat_named_open_boundary hNat,
        generatedRecursorContract_nat_named_closed_slice_not_realized_in_current_decl_env hNat⟩
    · exfalso
      simp [GeneratedRecursorContractAdmitted, generatedRecursorPilot, hUnit, hNat] at hAdm

theorem generatedRecursorContract_admitted_exact_current_gate_frontier
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    exact ⟨hName, hFull.2, hFull, hReal,
      generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_no_open_is_unit
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = []) :
    contract.recursorName = unitRecName := by
  exact generatedRecursorContract_fullyClosed_is_unit ⟨hAdm, hClosed⟩

theorem generatedRecursorContract_admitted_realized_in_unit_of_no_open
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = []) :
    GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract := by
  exact generatedRecursorContract_fullyClosed_realized_in_unit ⟨hAdm, hClosed⟩

theorem generatedRecursorContract_admitted_step_SR_of_no_open_pi_only
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B')
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStep : GeneratedRecursorContractClosedIotaStep contract t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  have hFull : GeneratedRecursorContractFullyClosed contract := ⟨hAdm, hClosed⟩
  have hRules :
      generatedRecursorContractClosedIotaRules contract = [unitRecCtorClosedIotaRule] :=
    generatedRecursorContract_fullyClosed_rules_eq_unit hFull
  unfold GeneratedRecursorContractClosedIotaStep at hStep
  rw [hRules] at hStep
  simp at hStep
  rcases hStep with ⟨hSrc, hTgt⟩
  subst hSrc
  subst hTgt
  exact hasType_unitRecOnCtor_result_of_pi_only piInjective hTy

theorem generatedRecursorContract_admitted_step_SR_of_no_open_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStep : GeneratedRecursorContractClosedIotaStep contract t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  exact DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
    (E := unitRecDeclEnv)
    (hCR := hCR)
    unitRecDeclEnv_wellFormed
    hTy
    (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed)
      (Relation.ReflTransGen.single hStep))

theorem generatedRecursorContract_admitted_step_SR_of_no_open_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStep : GeneratedRecursorContractClosedIotaStep contract t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  exact generatedRecursorContract_admitted_step_SR_of_no_open_of_church_rosser
    hAdm
    hClosed
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)
    hTy
    hStep

theorem generatedRecursorContract_admitted_step_SR_of_no_open
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStep : GeneratedRecursorContractClosedIotaStep contract t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  exact generatedRecursorContract_admitted_step_SR_of_no_open_of_church_rosser
    hAdm
    hClosed
    DeclarationSemantics.declChurchRosser
    hTy
    hStep

theorem generatedRecursorContract_admitted_star_SR_of_no_open_pi_only
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B')
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  rcases generatedRecursorContractClosedIotaStep_star_cases contract hStar with rfl | hStep
  · simpa using hTy
  · exact generatedRecursorContract_admitted_step_SR_of_no_open_pi_only
      hAdm hClosed piInjective hTy hStep

theorem generatedRecursorContract_admitted_star_SR_of_no_open_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  exact DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
    (E := unitRecDeclEnv)
    (hCR := hCR)
    unitRecDeclEnv_wellFormed
    hTy
    (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hStar)

theorem generatedRecursorContract_admitted_star_SR_of_no_open_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  exact generatedRecursorContract_admitted_star_SR_of_no_open_of_church_rosser
    hAdm
    hClosed
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)
    hTy
    hStar

theorem generatedRecursorContract_admitted_star_SR_of_no_open
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    {t u A : PureTm 0}
    (hTy : HasTypeDecl unitRecDeclEnv .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl unitRecDeclEnv .nil u A := by
  exact generatedRecursorContract_admitted_star_SR_of_no_open_of_church_rosser
    hAdm
    hClosed
    DeclarationSemantics.declChurchRosser
    hTy
    hStar

theorem generatedRecursorContract_declStarSR_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    {t u A : PureTm 0}
    (hTy : HasTypeDecl E .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl E .nil u A := by
  exact DeclarationSemantics.redStarDecl_preserves_type_of_injective
    (E := E)
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (hWf := hWf)
    (ht := hTy)
    (hs := generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar)

theorem generatedRecursorContract_declStarSR_of_realization_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl E .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl E .nil u A := by
  exact DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
    (E := E)
    (hCR := hCR)
    hWf
    hTy
    (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar)

theorem generatedRecursorContract_declStarSR_of_realization_of_decl_package
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hDeclPkg : DeclarationSemantics.DeclChurchRosserFrontierPackage E)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl E .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl E .nil u A := by
  exact generatedRecursorContract_declStarSR_of_realization_of_church_rosser
    (contract := contract)
    (E := E)
    hDeclPkg.1
    hReal
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)
    hTy
    hStar

theorem generatedRecursorContract_declStarSR_of_realization_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl E .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl E .nil u A := by
  exact generatedRecursorContract_declStarSR_of_realization_of_church_rosser
    (contract := contract)
    (E := E)
    hWf
    hReal
    (hCR := DeclarationSemantics.declChurchRosser_of_no_values hNone)
    hTy
    hStar

theorem generatedRecursorContract_declStarSR_of_realization_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract)
    {t u A : PureTm 0}
    (hTy : HasTypeDecl (envOfSpecs specs) .nil t A)
    (hStar : Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl (envOfSpecs specs) .nil u A := by
  exact generatedRecursorContract_declStarSR_of_realization_of_church_rosser
    (contract := contract)
    (E := envOfSpecs specs)
    (hWf := envOfSpecs_wellFormed_of_all_none specs hNone)
    hReal
    (hCR := hSig.declChurchRosser_of_all_none hNone)
    hTy
    hStar

theorem generatedRecursorContract_fullyClosed_declSR_bridge
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    ∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        GeneratedRecursorContractClosedIotaStep contract t u →
        HasTypeDecl E .nil u A) := by
  refine ⟨unitRecDeclEnv, unitRecDeclEnv_wellFormed, ?_⟩
  intro t u A hTy hStep
  exact generatedRecursorContract_admitted_step_SR_of_no_open_pi_only
    hFull.1 hFull.2 piInjective hTy hStep

theorem generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl E s t →
        ∃ u, RedStarDecl E s u ∧ RedStarDecl E t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl E (.pi A B) (.pi A' B') →
        ConvDecl E A A' ∧ ConvDecl E B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl E (.sigma A B) (.sigma A' B') →
        ConvDecl E A A' ∧ ConvDecl E B B') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u hStar
    exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar
  · intro t u A hTy hStar
    exact generatedRecursorContract_declStarSR_of_realization_of_church_rosser
      (contract := contract)
      (E := E)
      hWf
      hReal
      hCR
      hTy
      hStar
  · exact generatedRecursorContractClosedIotaStep_confluent contract
  · exact hCR
  · intro k A A' B B' hConv
    exact DeclarationSemantics.pi_injectivity_decl_of_church_rosser hCR hConv
  · intro k A A' B B' hConv
    exact DeclarationSemantics.sigma_injectivity_decl_of_church_rosser hCR hConv

theorem generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_decl_package
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hDeclPkg : DeclarationSemantics.DeclChurchRosserFrontierPackage E) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl E s t →
        ∃ u, RedStarDecl E s u ∧ RedStarDecl E t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl E (.pi A B) (.pi A' B') →
        ConvDecl E A A' ∧ ConvDecl E B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl E (.sigma A B) (.sigma A' B') →
        ConvDecl E A A' ∧ ConvDecl E B B') := by
  exact generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_church_rosser
    (contract := contract)
    (E := E)
    hDeclPkg.1
    hReal
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl E s t →
        ∃ u, RedStarDecl E s u ∧ RedStarDecl E t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl E (.pi A B) (.pi A' B') →
        ConvDecl E A A' ∧ ConvDecl E B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl E (.sigma A B) (.sigma A' B') →
        ConvDecl E A A' ∧ ConvDecl E B B') := by
  exact generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_church_rosser
    (contract := contract)
    (E := E)
    hWf
    hReal
    (hCR := DeclarationSemantics.declChurchRosser_of_no_values hNone)

theorem generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl (envOfSpecs specs) .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl (envOfSpecs specs) .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl (envOfSpecs specs) s t →
        ∃ u,
          RedStarDecl (envOfSpecs specs) s u ∧
          RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') := by
  exact generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_church_rosser
    (contract := contract)
    (E := envOfSpecs specs)
    (hWf := envOfSpecs_wellFormed_of_all_none specs hNone)
    hReal
    (hCR := hSig.declChurchRosser_of_all_none hNone)

theorem generatedRecursorContract_admitted_decl_sound_confluent_and_injectivity_of_no_open_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') := by
  exact generatedRecursorContract_decl_sound_confluent_and_injectivity_of_realization_of_church_rosser
    (contract := contract)
    (E := unitRecDeclEnv)
    unitRecDeclEnv_wellFormed
    (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed)
    hCR

theorem generatedRecursorContract_admitted_decl_sound_confluent_and_injectivity_of_no_open_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_and_injectivity_of_no_open_of_church_rosser
    hAdm
    hClosed
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_decl_sound_confluent_and_injectivity_of_no_open
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = []) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_and_injectivity_of_no_open_of_church_rosser
    hAdm
    hClosed
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_fullyClosed_decl_sound_confluent_and_injectivity_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_and_injectivity_of_no_open_of_church_rosser
    hFull.1 hFull.2 hCR

theorem generatedRecursorContract_fullyClosed_decl_sound_confluent_and_injectivity_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') := by
  exact generatedRecursorContract_fullyClosed_decl_sound_confluent_and_injectivity_of_church_rosser
    hFull
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_fullyClosed_current_gate_and_decl_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hCR :
      ∀ {k : Nat} {s t : PureTm k},
        ConvDecl unitRecDeclEnv s t →
          ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  rcases generatedRecursorContract_fullyClosed_decl_sound_confluent_and_injectivity_of_church_rosser
      hFull hCR with
    ⟨hRealizes, hSR, hConfluent, hCR', hPi, hSigma⟩
  exact ⟨hGate, hRealizes, hSR, hConfluent, hCR', hPi, hSigma, hCover⟩

theorem generatedRecursorContract_fullyClosed_current_gate_and_decl_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  exact generatedRecursorContract_fullyClosed_current_gate_and_decl_frontier_of_church_rosser
    hFull
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_fullyClosed_current_gate_and_decl_frontier_sealed
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ {k : Nat} {s t : PureTm k},
      ConvDecl unitRecDeclEnv s t →
        ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
      ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
        ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  exact generatedRecursorContract_fullyClosed_current_gate_and_decl_frontier_of_church_rosser
    hFull
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_exact_current_gate_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR :
      ∀ {k : Nat} {s t : PureTm k},
        ConvDecl unitRecDeclEnv s t →
          ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ {k : Nat} {s t : PureTm k},
        ConvDecl unitRecDeclEnv s t →
          ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
      (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    rcases generatedRecursorContract_fullyClosed_current_gate_and_decl_frontier_of_church_rosser
        hFull hCR with
      ⟨hGate, hRealizes, hSR, hConfluent, hCR', hPi, hSigma, hCover⟩
    exact ⟨hName, hFull.2, hFull, hReal, hGate, hRealizes, hSR, hConfluent, hCR', hPi, hSigma, hCover⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_current_gate_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ {k : Nat} {s t : PureTm k},
        ConvDecl unitRecDeclEnv s t →
          ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
      (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_exact_current_gate_frontier_of_church_rosser
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_exact_current_gate_frontier_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ {k : Nat} {s t : PureTm k},
        ConvDecl unitRecDeclEnv s t →
          ∃ u, RedStarDecl unitRecDeclEnv s u ∧ RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
      (∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.sigma A B) (.sigma A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_exact_current_gate_frontier_of_church_rosser
    hAdm
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_decl_sound_confluent_and_normalizing_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  refine ⟨?_, ?_, generatedRecursorContractClosedIotaStep_confluent contract,
    generatedRecursorContractClosedIotaStep_normalizes contract⟩
  · intro t u hStar
    exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar
  · intro t u A hTy hStar
    exact generatedRecursorContract_declStarSR_of_realization
      (contract := contract)
      (E := E)
      hWf
      hReal
      (piInjective := piInjective)
      (sigmaInjective := sigmaInjective)
      hTy
      hStar

theorem generatedRecursorContract_decl_sound_confluent_and_normalizing_of_realization_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  refine ⟨?_, ?_, generatedRecursorContractClosedIotaStep_confluent contract,
    generatedRecursorContractClosedIotaStep_normalizes contract⟩
  · intro t u hStar
    exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar
  · intro t u A hTy hStar
    exact DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
      (E := E)
      (hCR := hCR)
      hWf
      hTy
      (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar)

theorem generatedRecursorContract_decl_sound_confluent_and_normalizing_of_realization_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  exact generatedRecursorContract_decl_sound_confluent_and_normalizing_of_realization_of_church_rosser
    (contract := contract)
    (E := E)
    hWf
    hReal
    (hCR := DeclarationSemantics.declChurchRosser_of_no_values hNone)

theorem generatedRecursorContract_decl_sound_confluent_and_normalizing_of_realization_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl (envOfSpecs specs) .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl (envOfSpecs specs) .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  exact generatedRecursorContract_decl_sound_confluent_and_normalizing_of_realization_of_church_rosser
    (contract := contract)
    (E := envOfSpecs specs)
    (hWf := envOfSpecs_wellFormed_of_all_none specs hNone)
    hReal
    (hCR := hSig.declChurchRosser_of_all_none hNone)

theorem generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl E t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl E t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl E t u) := by
  rcases generatedRecursorContract_decl_sound_confluent_and_normalizing_of_realization
      (contract := contract)
      (E := E)
      hWf
      hReal
      (piInjective := piInjective)
      (sigmaInjective := sigmaInjective) with
    ⟨hRealizes, hSR, hConfluent, hNormalizes⟩
  refine ⟨hRealizes, hSR, hConfluent, hNormalizes, ?_, ?_, ?_⟩
  · intro t u hEq
    exact generatedRecursorContractClosedIotaNormalize_eq_implies_convDecl_of_realization hReal hEq
  · intro t u w hSome
    exact generatedRecursorContractClosedIotaConvByNormalization?_sound_of_realization hReal hSome
  · intro t u hSome
    exact generatedRecursorContractClosedIotaConvDecl_of_realization hReal
      ((generatedRecursorContractClosedIotaConvByNormalization?_ne_none_iff).1 hSome)

theorem generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl E t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl E t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl E t u) := by
  refine ⟨?_, ?_, generatedRecursorContractClosedIotaStep_confluent contract,
    generatedRecursorContractClosedIotaStep_normalizes contract, ?_, ?_, ?_⟩
  · intro t u hStar
    exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar
  · intro t u A hTy hStar
    exact DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
      (E := E)
      (hCR := hCR)
      hWf
      hTy
      (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization hReal hStar)
  · intro t u hEq
    exact generatedRecursorContractClosedIotaNormalize_eq_implies_convDecl_of_realization hReal hEq
  · intro t u w hSome
    exact generatedRecursorContractClosedIotaConvByNormalization?_sound_of_realization hReal hSome
  · intro t u hSome
    exact generatedRecursorContractClosedIotaConvDecl_of_realization hReal
      ((generatedRecursorContractClosedIotaConvByNormalization?_ne_none_iff).1 hSome)

theorem generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) := by
  refine ⟨hWf, ?_, ?_⟩
  · exact DeclarationSemantics.decl_sound_confluent_and_injectivity_of_church_rosser
      (E := E)
      hCR hWf
  · exact generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_church_rosser
      (contract := contract)
      (E := E)
      hWf hReal hCR

theorem generatedRecursorContract_decl_and_slice_package_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    GeneratedRecursorDeclAndSliceChurchRosserPackage E contract := by
  have hDeclPkg : GeneratedRecursorDeclChurchRosserPackage E := by
    exact
      DeclarationSemantics.decl_sound_confluent_and_injectivity_of_church_rosser_package
        (E := E) hCR hWf
  have hSlice : GeneratedRecursorClosedSliceChurchRosserPackage E contract := by
    exact generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_church_rosser
      (contract := contract)
      (E := E)
      hWf hReal hCR
  exact ⟨hDeclPkg, hSlice⟩

theorem generatedRecursorContract_fullyClosed_current_gate_and_decl_slice_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    (∃ E' : DeclEnv,
      DeclEnvWellFormed E' ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E' .nil t A ∧
            HasTypeDecl E' .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  rcases generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_church_rosser
      (contract := contract) (E := E) hWf hReal hCR with
    ⟨hWf', hDecl, hSlice⟩
  exact ⟨hGate, hWf', hDecl, hSlice, hCover⟩

theorem generatedRecursorContract_admitted_exact_closed_decl_slice_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn E contract ∧
    (∃ E' : DeclEnv,
      DeclEnvWellFormed E' ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E' .nil t A ∧
            HasTypeDecl E' .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  let hFull : GeneratedRecursorContractFullyClosed contract := ⟨hAdm, hClosed⟩
  have hName : contract.recursorName = unitRecName :=
    generatedRecursorContract_fullyClosed_is_unit hFull
  rcases generatedRecursorContract_fullyClosed_current_gate_and_decl_slice_frontier_of_church_rosser
      (contract := contract) (E := E) hFull hWf hReal hCR with
    ⟨hGate, hWf', hDecl, hSlice, hCover⟩
  exact ⟨hName, hClosed, hFull, hReal, hGate, hWf', hDecl, hSlice, hCover⟩

theorem generatedRecursorContract_admitted_current_boundary_and_decl_slice_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    (∃ E' : DeclEnv,
      DeclEnvWellFormed E' ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E' .nil t A ∧
            HasTypeDecl E' .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (generatedRecursorContractOpenIotaObligations contract = [] ∨
      (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
        ∃ A : PureTm 1,
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)) ∧
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B')) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  rcases generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_church_rosser
      (contract := contract) (E := E) hWf hReal hCR with
    ⟨hWf', hDecl, hSlice⟩
  exact ⟨hGate, hBoundary, hWf', hDecl, hSlice⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    GeneratedRecursorCurrentGateWitness contract ∧
    GeneratedRecursorAdmittedOpenBoundary contract ∧
    GeneratedRecursorDeclAndSliceChurchRosserPackage E contract := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  have hPkg :
      GeneratedRecursorDeclAndSliceChurchRosserPackage E contract :=
    generatedRecursorContract_decl_and_slice_package_of_church_rosser
      (contract := contract) (E := E) hWf hReal hCR
  exact ⟨hGate, hBoundary, hPkg⟩

theorem generatedRecursorContract_admitted_exact_current_boundary_and_decl_slice_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (hCR : DeclarationSemantics.DeclChurchRosser E) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn E contract ∧
      (∃ E' : DeclEnv,
        DeclEnvWellFormed E' ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E' .nil t A ∧
              HasTypeDecl E' .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      DeclEnvWellFormed E ∧
      ((∀ {Γ : Ctx n} {t u A : PureTm n},
          HasTypeDecl E Γ t A →
          RedStarDecl E t u →
          HasTypeDecl E Γ u A) ∧
        (∀ {s t₁ t₂ : PureTm n},
          RedStarDecl E s t₁ →
          RedStarDecl E s t₂ →
          ∃ u,
            RedStarDecl E t₁ u ∧
            RedStarDecl E t₂ u) ∧
        (∀ {s t : PureTm n},
          ConvDecl E s t →
          ∃ u,
            RedStarDecl E s u ∧
            RedStarDecl E t u) ∧
        (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
          ConvDecl E (.pi A B) (.pi A' B') →
            ConvDecl E A A' ∧ ConvDecl E B B') ∧
        (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
          ConvDecl E (.sigma A B) (.sigma A' B') →
            ConvDecl E A A' ∧ ConvDecl E B B')) ∧
      ((∀ {t u : PureTm 0},
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
            RedStarDecl E t u) ∧
        (∀ {t u A : PureTm 0},
          HasTypeDecl E .nil t A →
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
        (∀ t : PureTm 0,
          ∃ u : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
            ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
        (∀ {t u : PureTm 0},
          generatedRecursorContractClosedIotaNormalize contract t =
            generatedRecursorContractClosedIotaNormalize contract u →
              ConvDecl E t u) ∧
        (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
          generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
            ConvDecl E t u) ∧
        (∀ {t u : PureTm 0},
          generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
            ConvDecl E t u)) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases generatedRecursorContract_admitted_exact_closed_decl_slice_frontier_of_church_rosser
        (contract := contract) (E := E) hAdm
        ((generatedRecursorContract_unit_named_fullyClosed hUnit.1).2) hWf hReal hCR with
      ⟨hName, hClosed, hFull, hReal', hGate, hWf', hDecl, hSlice, hCover⟩
    exact ⟨hName, hClosed, hFull, hReal', hGate, hWf', hDecl, hSlice, hCover⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl E t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl E .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl E .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl E t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl E t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl E t u) := by
  exact generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_church_rosser
    (contract := contract)
    (E := E)
    hWf
    hReal
    (hCR := DeclarationSemantics.declChurchRosser_of_no_values hNone)

theorem generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl (envOfSpecs specs) .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl (envOfSpecs specs) .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl (envOfSpecs specs) t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl (envOfSpecs specs) t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl (envOfSpecs specs) t u) := by
  exact generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_church_rosser
    (contract := contract)
    (E := envOfSpecs specs)
    (hWf := envOfSpecs_wellFormed_of_all_none specs hNone)
    hReal
    (hCR := hSig.declChurchRosser_of_all_none hNone)

theorem generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A B : PureTm n} {w : DeclarationSemantics.DefEqDeclWitness E A B},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B = some w →
        ConvDecl E A B) ∧
      (∀ {A B : PureTm n},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B ≠ none →
        ConvDecl E A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) := by
  refine ⟨hWf, ?_, ?_⟩
  · exact DeclarationSemantics.decl_sound_confluent_and_conversion_of_no_values
      (E := E)
      hNone hWf
  · exact generatedRecursorContract_decl_sound_confluent_normalizing_and_conversion_of_realization_of_no_values
      (contract := contract)
      (E := E)
      hNone hWf hReal

theorem generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    DeclEnvWellFormed (envOfSpecs specs) ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl (envOfSpecs specs) Γ t A →
        RedStarDecl (envOfSpecs specs) t u →
        HasTypeDecl (envOfSpecs specs) Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl (envOfSpecs specs) s t₁ →
        RedStarDecl (envOfSpecs specs) s t₂ →
        ∃ u,
          RedStarDecl (envOfSpecs specs) t₁ u ∧
          RedStarDecl (envOfSpecs specs) t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl (envOfSpecs specs) s t →
        ∃ u,
          RedStarDecl (envOfSpecs specs) s u ∧
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w →
        ConvDecl (envOfSpecs specs) A B) ∧
      (∀ {A B : PureTm n},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none →
        ConvDecl (envOfSpecs specs) A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl (envOfSpecs specs) .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl (envOfSpecs specs) .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl (envOfSpecs specs) t u)) := by
  exact generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_no_values
    (contract := contract)
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    (hWf := envOfSpecs_wellFormed_of_all_none specs hNone)
    hReal

theorem generatedRecursorContract_decl_and_slice_package_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorDeclAndSliceNoValuesPackage E hNone contract := by
  have hDeclNoValuesPkg :
      DeclarationSemantics.DeclNoValuesFrontierPackage E hNone :=
    DeclarationSemantics.decl_sound_confluent_and_conversion_of_no_values_package
      (E := E) hNone hWf
  have hDeclSlicePkg :
      GeneratedRecursorDeclAndSliceChurchRosserPackage E contract :=
    generatedRecursorContract_decl_and_slice_package_of_church_rosser
      (contract := contract) (E := E) hWf hReal
      (DeclarationSemantics.declChurchRosser_of_no_values hNone)
  exact
    ⟨ hDeclSlicePkg
    , DeclarationSemantics.DeclNoValuesFrontierPackage.normalization
        hDeclNoValuesPkg
    ⟩

theorem generatedRecursorContract_decl_and_slice_package_of_no_values_as_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorDeclAndSliceChurchRosserPackage E contract := by
  exact
    (generatedRecursorContract_decl_and_slice_package_of_no_values
      (contract := contract) (E := E) hNone hWf hReal).1

theorem generatedRecursorContract_decl_and_slice_package_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorDeclAndSliceNoValuesPackage
      (envOfSpecs specs)
      (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
      contract := by
  rcases hSig.declSpecAndNoValuesPackage_of_all_none hNone with
    ⟨hDeclPkg, hNormPkg⟩
  rcases hDeclPkg with ⟨hWf, _hPres, _hConfl, hCR, _hPi, _hSigma⟩
  have hDeclSlicePkg :
      GeneratedRecursorDeclAndSliceChurchRosserPackage
        (envOfSpecs specs) contract :=
    generatedRecursorContract_decl_and_slice_package_of_church_rosser
      (contract := contract)
      (E := envOfSpecs specs)
      hWf hReal hCR
  exact ⟨hDeclSlicePkg, hNormPkg⟩

theorem generatedRecursorContract_decl_and_slice_package_of_all_none_specs_as_church_rosser
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorDeclAndSliceChurchRosserPackage
      (envOfSpecs specs) contract := by
  exact
    (generatedRecursorContract_decl_and_slice_package_of_all_none_specs
      (contract := contract) (specs := specs) hSig hNone hReal).1

theorem generatedRecursorContract_fullyClosed_current_gate_and_decl_slice_frontier_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    (∃ E' : DeclEnv,
      DeclEnvWellFormed E' ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E' .nil t A ∧
            HasTypeDecl E' .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A B : PureTm n} {w : DeclarationSemantics.DefEqDeclWitness E A B},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B = some w →
        ConvDecl E A B) ∧
      (∀ {A B : PureTm n},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B ≠ none →
        ConvDecl E A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  rcases generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_no_values
      (contract := contract) (E := E) hNone hWf hReal with
    ⟨hWf', hDecl, hSlice⟩
  exact ⟨hGate, hWf', hDecl, hSlice, hCover⟩

theorem generatedRecursorContract_fullyClosed_no_values_decl_frontier_package
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorNoValuesDeclFrontierPackage E hNone contract := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  have hPkg :
      GeneratedRecursorDeclAndSliceNoValuesPackage E hNone contract :=
    generatedRecursorContract_decl_and_slice_package_of_no_values
      (contract := contract) (E := E) hNone hWf hReal
  exact ⟨hGate, hPkg, hCover⟩

theorem generatedRecursorContract_fullyClosed_no_values_decl_frontier_package_as_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorChurchRosserDeclFrontierPackage E contract := by
  exact
    GeneratedRecursorNoValuesDeclFrontierPackage.asChurchRosser
      (generatedRecursorContract_fullyClosed_no_values_decl_frontier_package
        (contract := contract) (E := E) hFull hNone hWf hReal)

theorem generatedRecursorContract_admitted_exact_closed_decl_slice_frontier_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn E contract ∧
    (∃ E' : DeclEnv,
      DeclEnvWellFormed E' ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E' .nil t A ∧
            HasTypeDecl E' .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A B : PureTm n} {w : DeclarationSemantics.DefEqDeclWitness E A B},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B = some w →
        ConvDecl E A B) ∧
      (∀ {A B : PureTm n},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B ≠ none →
        ConvDecl E A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  let hFull : GeneratedRecursorContractFullyClosed contract := ⟨hAdm, hClosed⟩
  have hName : contract.recursorName = unitRecName :=
    generatedRecursorContract_fullyClosed_is_unit hFull
  rcases generatedRecursorContract_fullyClosed_current_gate_and_decl_slice_frontier_of_no_values
      (contract := contract) (E := E) hFull hNone hWf hReal with
    ⟨hGate, hWf', hDecl, hSlice, hCover⟩
  exact ⟨hName, hClosed, hFull, hReal, hGate, hWf', hDecl, hSlice, hCover⟩

theorem generatedRecursorContract_admitted_exact_closed_no_values_decl_frontier_package
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorExactClosedNoValuesDeclFrontierPackage E hNone contract := by
  let hFull : GeneratedRecursorContractFullyClosed contract := ⟨hAdm, hClosed⟩
  have hName : contract.recursorName = unitRecName :=
    generatedRecursorContract_fullyClosed_is_unit hFull
  have hPkg :
      GeneratedRecursorNoValuesDeclFrontierPackage E hNone contract :=
    generatedRecursorContract_fullyClosed_no_values_decl_frontier_package
      (contract := contract) (E := E) hFull hNone hWf hReal
  exact ⟨hName, hClosed, hFull, hReal, hPkg⟩

theorem generatedRecursorContract_admitted_exact_closed_no_values_decl_frontier_package_as_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorExactClosedChurchRosserDeclFrontierPackage E contract := by
  exact
    GeneratedRecursorExactClosedNoValuesDeclFrontierPackage.asChurchRosser
      (generatedRecursorContract_admitted_exact_closed_no_values_decl_frontier_package
        (contract := contract) (E := E) hAdm hClosed hNone hWf hReal)

theorem generatedRecursorContract_admitted_current_boundary_and_decl_slice_frontier_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    (∃ E' : DeclEnv,
      DeclEnvWellFormed E' ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E' .nil t A ∧
            HasTypeDecl E' .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (generatedRecursorContractOpenIotaObligations contract = [] ∨
      (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
        ∃ A : PureTm 1,
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)) ∧
    DeclEnvWellFormed E ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl E Γ t A →
        RedStarDecl E t u →
        HasTypeDecl E Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl E s t₁ →
        RedStarDecl E s t₂ →
        ∃ u,
          RedStarDecl E t₁ u ∧
          RedStarDecl E t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl E s t →
        ∃ u,
          RedStarDecl E s u ∧
          RedStarDecl E t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.pi A B) (.pi A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl E (.sigma A B) (.sigma A' B') →
          ConvDecl E A A' ∧ ConvDecl E B B') ∧
      (∀ {A B : PureTm n} {w : DeclarationSemantics.DefEqDeclWitness E A B},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B = some w →
        ConvDecl E A B) ∧
      (∀ {A B : PureTm n},
        DeclarationSemantics.defEqByNormalizationDeclOfNoValues? E hNone A B ≠ none →
        ConvDecl E A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl E t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl E .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl E t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl E t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl E t u)) := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  rcases generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_no_values
      (contract := contract) (E := E) hNone hWf hReal with
    ⟨hWf', hDecl, hSlice⟩
  exact ⟨hGate, hBoundary, hWf', hDecl, hSlice⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage E hNone contract := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  have hPkg :
      GeneratedRecursorDeclAndSliceNoValuesPackage E hNone contract :=
    generatedRecursorContract_decl_and_slice_package_of_no_values
      (contract := contract) (E := E) hNone hWf hReal
  exact ⟨hGate, hBoundary, hPkg⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_no_values_as_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorCurrentBoundaryChurchRosserFrontierPackage E contract := by
  exact
    GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage.asChurchRosser
      (generatedRecursorContract_admitted_current_boundary_package_of_no_values
        (contract := contract) (E := E) hAdm hNone hWf hReal)

theorem generatedRecursorContract_admitted_exact_current_boundary_and_decl_slice_frontier_of_no_values
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorAdmittedExactNoValuesFrontierPackage E hNone contract := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    have hFull : GeneratedRecursorContractFullyClosed contract :=
      generatedRecursorContract_unit_named_fullyClosed hUnit.1
    have hPkg :
        GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage E hNone contract :=
      generatedRecursorContract_admitted_current_boundary_package_of_no_values
        (contract := contract) (E := E) hAdm hNone hWf hReal
    exact ⟨hUnit.1, hFull.2, hFull, hReal, hPkg⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_current_boundary_and_decl_slice_frontier_of_no_values_as_church_rosser
    {contract : FamilyRecursorDeclContract} {E : DeclEnv}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hNone : ∀ c : DeclName, valueOf? E c = none)
    (hWf : DeclEnvWellFormed E)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract) :
    GeneratedRecursorAdmittedExactChurchRosserFrontierPackage E contract := by
  exact
    GeneratedRecursorAdmittedExactNoValuesFrontierPackage.asChurchRosser
      (generatedRecursorContract_admitted_exact_current_boundary_and_decl_slice_frontier_of_no_values
        (contract := contract) (E := E) hAdm hNone hWf hReal)

theorem generatedRecursorContract_fullyClosed_current_gate_and_decl_slice_frontier_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    DeclEnvWellFormed (envOfSpecs specs) ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl (envOfSpecs specs) Γ t A →
        RedStarDecl (envOfSpecs specs) t u →
        HasTypeDecl (envOfSpecs specs) Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl (envOfSpecs specs) s t₁ →
        RedStarDecl (envOfSpecs specs) s t₂ →
        ∃ u,
          RedStarDecl (envOfSpecs specs) t₁ u ∧
          RedStarDecl (envOfSpecs specs) t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl (envOfSpecs specs) s t →
        ∃ u,
          RedStarDecl (envOfSpecs specs) s u ∧
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w →
        ConvDecl (envOfSpecs specs) A B) ∧
      (∀ {A B : PureTm n},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none →
        ConvDecl (envOfSpecs specs) A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl (envOfSpecs specs) .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl (envOfSpecs specs) .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl (envOfSpecs specs) t u)) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  rcases generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_all_none_specs
      (contract := contract) (specs := specs) hSig hNone hReal with
    ⟨hWf, hDecl, hSlice⟩
  exact ⟨hGate, hWf, hDecl, hSlice, hCover⟩

theorem generatedRecursorContract_fullyClosed_no_values_decl_frontier_package_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorNoValuesDeclFrontierPackage
      (envOfSpecs specs)
      (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
      contract := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  have hPkg :
      GeneratedRecursorDeclAndSliceNoValuesPackage
        (envOfSpecs specs)
        (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
        contract :=
    generatedRecursorContract_decl_and_slice_package_of_all_none_specs
      (contract := contract) (specs := specs) hSig hNone hReal
  exact ⟨hGate, hPkg, hCover⟩

theorem generatedRecursorContract_fullyClosed_no_values_decl_frontier_package_of_all_none_specs_as_church_rosser
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorChurchRosserDeclFrontierPackage
      (envOfSpecs specs) contract := by
  exact
    GeneratedRecursorNoValuesDeclFrontierPackage.asChurchRosser
      (generatedRecursorContract_fullyClosed_no_values_decl_frontier_package_of_all_none_specs
        (contract := contract) (specs := specs) hFull hSig hNone hReal)

theorem generatedRecursorContract_admitted_exact_closed_decl_slice_frontier_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    contract.recursorName = unitRecName ∧
    generatedRecursorContractOpenIotaObligations contract = [] ∧
    GeneratedRecursorContractFullyClosed contract ∧
    GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract ∧
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    DeclEnvWellFormed (envOfSpecs specs) ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl (envOfSpecs specs) Γ t A →
        RedStarDecl (envOfSpecs specs) t u →
        HasTypeDecl (envOfSpecs specs) Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl (envOfSpecs specs) s t₁ →
        RedStarDecl (envOfSpecs specs) s t₂ →
        ∃ u,
          RedStarDecl (envOfSpecs specs) t₁ u ∧
          RedStarDecl (envOfSpecs specs) t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl (envOfSpecs specs) s t →
        ∃ u,
          RedStarDecl (envOfSpecs specs) s u ∧
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w →
        ConvDecl (envOfSpecs specs) A B) ∧
      (∀ {A B : PureTm n},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none →
        ConvDecl (envOfSpecs specs) A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl (envOfSpecs specs) .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl (envOfSpecs specs) .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl (envOfSpecs specs) t u)) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  let hFull : GeneratedRecursorContractFullyClosed contract := ⟨hAdm, hClosed⟩
  have hName : contract.recursorName = unitRecName :=
    generatedRecursorContract_fullyClosed_is_unit hFull
  rcases generatedRecursorContract_fullyClosed_current_gate_and_decl_slice_frontier_of_all_none_specs
      (contract := contract) (specs := specs) hFull hSig hNone hReal with
    ⟨hGate, hWf, hDecl, hSlice, hCover⟩
  exact ⟨hName, hClosed, hFull, hReal, hGate, hWf, hDecl, hSlice, hCover⟩

theorem generatedRecursorContract_admitted_exact_closed_no_values_decl_frontier_package_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorExactClosedNoValuesDeclFrontierPackage
      (envOfSpecs specs)
      (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
      contract := by
  let hFull : GeneratedRecursorContractFullyClosed contract := ⟨hAdm, hClosed⟩
  have hName : contract.recursorName = unitRecName :=
    generatedRecursorContract_fullyClosed_is_unit hFull
  have hPkg :
      GeneratedRecursorNoValuesDeclFrontierPackage
        (envOfSpecs specs)
        (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
        contract :=
    generatedRecursorContract_fullyClosed_no_values_decl_frontier_package_of_all_none_specs
      (contract := contract) (specs := specs) hFull hSig hNone hReal
  exact ⟨hName, hClosed, hFull, hReal, hPkg⟩

theorem generatedRecursorContract_admitted_exact_closed_no_values_decl_frontier_package_of_all_none_specs_as_church_rosser
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorExactClosedChurchRosserDeclFrontierPackage
      (envOfSpecs specs) contract := by
  exact
    GeneratedRecursorExactClosedNoValuesDeclFrontierPackage.asChurchRosser
      (generatedRecursorContract_admitted_exact_closed_no_values_decl_frontier_package_of_all_none_specs
        (contract := contract) (specs := specs) hAdm hClosed hSig hNone hReal)

theorem generatedRecursorContract_admitted_current_boundary_and_decl_slice_frontier_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (generatedRecursorContractOpenIotaObligations contract = [] ∨
      (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
        ∃ A : PureTm 1,
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
          HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A)) ∧
    DeclEnvWellFormed (envOfSpecs specs) ∧
    ((∀ {Γ : Ctx n} {t u A : PureTm n},
        HasTypeDecl (envOfSpecs specs) Γ t A →
        RedStarDecl (envOfSpecs specs) t u →
        HasTypeDecl (envOfSpecs specs) Γ u A) ∧
      (∀ {s t₁ t₂ : PureTm n},
        RedStarDecl (envOfSpecs specs) s t₁ →
        RedStarDecl (envOfSpecs specs) s t₂ →
        ∃ u,
          RedStarDecl (envOfSpecs specs) t₁ u ∧
          RedStarDecl (envOfSpecs specs) t₂ u) ∧
      (∀ {s t : PureTm n},
        ConvDecl (envOfSpecs specs) s t →
        ∃ u,
          RedStarDecl (envOfSpecs specs) s u ∧
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
      (∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w →
        ConvDecl (envOfSpecs specs) A B) ∧
      (∀ {A B : PureTm n},
        hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none →
        ConvDecl (envOfSpecs specs) A B)) ∧
    ((∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl (envOfSpecs specs) t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl (envOfSpecs specs) .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl (envOfSpecs specs) .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl (envOfSpecs specs) t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl (envOfSpecs specs) t u)) := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  rcases generatedRecursorContract_decl_and_slice_sound_confluent_normalizing_and_conversion_of_all_none_specs
      (contract := contract) (specs := specs) hSig hNone hReal with
    ⟨hWf, hDecl, hSlice⟩
  exact ⟨hGate, hBoundary, hWf, hDecl, hSlice⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage
      (envOfSpecs specs)
      (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
      contract := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  have hPkg :
      GeneratedRecursorDeclAndSliceNoValuesPackage
        (envOfSpecs specs)
        (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
        contract :=
    generatedRecursorContract_decl_and_slice_package_of_all_none_specs
      (contract := contract) (specs := specs) hSig hNone hReal
  exact ⟨hGate, hBoundary, hPkg⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_all_none_specs_as_church_rosser
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorCurrentBoundaryChurchRosserFrontierPackage
      (envOfSpecs specs) contract := by
  exact
    GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage.asChurchRosser
      (generatedRecursorContract_admitted_current_boundary_package_of_all_none_specs
        (contract := contract) (specs := specs) hAdm hSig hNone hReal)

theorem generatedRecursorContract_admitted_exact_current_boundary_and_decl_slice_frontier_of_all_none_specs
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorAdmittedExactNoValuesFrontierPackage
      (envOfSpecs specs)
      (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
      contract := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    have hFull : GeneratedRecursorContractFullyClosed contract :=
      generatedRecursorContract_unit_named_fullyClosed hUnit.1
    have hPkg :
        GeneratedRecursorCurrentBoundaryNoValuesFrontierPackage
          (envOfSpecs specs)
          (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
          contract :=
      generatedRecursorContract_admitted_current_boundary_package_of_all_none_specs
        (contract := contract) (specs := specs) hAdm hSig hNone hReal
    exact ⟨hUnit.1, hFull.2, hFull, hReal, hPkg⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_current_boundary_and_decl_slice_frontier_of_all_none_specs_as_church_rosser
    {contract : FamilyRecursorDeclContract} {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorAdmittedExactChurchRosserFrontierPackage
      (envOfSpecs specs) contract := by
  exact
    GeneratedRecursorAdmittedExactNoValuesFrontierPackage.asChurchRosser
      (generatedRecursorContract_admitted_exact_current_boundary_and_decl_slice_frontier_of_all_none_specs
        (contract := contract) (specs := specs) hAdm hSig hNone hReal)

theorem generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  refine ⟨?_, ?_, generatedRecursorContractClosedIotaStep_confluent contract,
    generatedRecursorContractClosedIotaStep_normalizes contract⟩
  · intro t u hStar
    exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hStar
  · intro t u A hTy hStar
    exact generatedRecursorContract_admitted_star_SR_of_no_open_pi_only
      hAdm hClosed piInjective hTy hStar

theorem generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  refine ⟨?_, ?_, generatedRecursorContractClosedIotaStep_confluent contract,
    generatedRecursorContractClosedIotaStep_normalizes contract⟩
  · intro t u hStar
    exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hStar
  · intro t u A hTy hStar
    exact DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
      (E := unitRecDeclEnv)
      (hCR := hCR)
      unitRecDeclEnv_wellFormed
      hTy
      (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
        (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hStar)

theorem generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open_of_church_rosser
    hAdm
    hClosed
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = []) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open_of_church_rosser
    hAdm
    hClosed
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) := by
  rcases generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open
      (contract := contract)
      hAdm hClosed piInjective with
    ⟨hRealizes, hSR, hConfluent, hNormalizes⟩
  refine ⟨hRealizes, hSR, hConfluent, hNormalizes, ?_, ?_, ?_⟩
  · intro t u hEq
    exact generatedRecursorContractClosedIotaNormalize_eq_implies_convDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hEq
  · intro t u w hSome
    exact generatedRecursorContractClosedIotaConvByNormalization?_sound_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hSome
  · intro t u hSome
    exact generatedRecursorContractClosedIotaConvDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed)
      ((generatedRecursorContractClosedIotaConvByNormalization?_ne_none_iff).1 hSome)

theorem generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) := by
  refine ⟨?_, ?_, generatedRecursorContractClosedIotaStep_confluent contract,
    generatedRecursorContractClosedIotaStep_normalizes contract, ?_, ?_, ?_⟩
  · intro t u hStar
    exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hStar
  · intro t u A hTy hStar
    exact DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
      (E := unitRecDeclEnv)
      (hCR := hCR)
      unitRecDeclEnv_wellFormed
      hTy
      (generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
        (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hStar)
  · intro t u hEq
    exact generatedRecursorContractClosedIotaNormalize_eq_implies_convDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hEq
  · intro t u w hSome
    exact generatedRecursorContractClosedIotaConvByNormalization?_sound_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hSome
  · intro t u hSome
    exact generatedRecursorContractClosedIotaConvDecl_of_realization
      (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed)
      ((generatedRecursorContractClosedIotaConvByNormalization?_ne_none_iff).1 hSome)

theorem generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open_of_church_rosser
    hAdm
    hClosed
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = []) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open_of_church_rosser
    hAdm
    hClosed
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_fullyClosed_decl_sound_confluent_and_normalizing
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_and_normalizing_of_no_open
    hFull.1 hFull.2 piInjective

theorem generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open
    hFull.1 hFull.2 piInjective

theorem generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) := by
  exact generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open_of_church_rosser
    hFull.1 hFull.2 hCR

theorem generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) := by
  exact generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion_of_church_rosser
    hFull
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_fullyClosed_convDecl_of_slice_conv
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hConv : GeneratedRecursorContractClosedIotaConv contract t u) :
    ConvDecl unitRecDeclEnv t u := by
  exact generatedRecursorContractClosedIotaConvDecl_of_realization
    (generatedRecursorContract_fullyClosed_realized_in_unit hFull) hConv

theorem generatedRecursorContract_fullyClosed_normalize_eq_implies_convDecl
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hEq :
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u) :
    ConvDecl unitRecDeclEnv t u := by
  exact generatedRecursorContractClosedIotaNormalize_eq_implies_convDecl_of_realization
    (generatedRecursorContract_fullyClosed_realized_in_unit hFull) hEq

theorem generatedRecursorContract_fullyClosed_convByNormalization?_sound
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    {w : GeneratedRecursorContractClosedIotaConvWitness contract t u}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (h :
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w) :
    ConvDecl unitRecDeclEnv t u := by
  exact generatedRecursorContractClosedIotaConvByNormalization?_sound_of_realization
    (generatedRecursorContract_fullyClosed_realized_in_unit hFull) h

theorem generatedRecursorContract_admitted_convByNormalization?_sound_of_no_open
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    {w : GeneratedRecursorContractClosedIotaConvWitness contract t u}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (h :
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w) :
    ConvDecl unitRecDeclEnv t u := by
  exact generatedRecursorContractClosedIotaConvByNormalization?_sound_of_realization
    (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) h

theorem generatedRecursorContractClosedIotaConvByNormalization?_ne_none_implies_convDecl_of_realization
    {contract : FamilyRecursorDeclContract} {E : DeclEnv} {t u : PureTm 0}
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn E contract)
    (h :
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none) :
    ConvDecl E t u := by
  exact generatedRecursorContractClosedIotaConvDecl_of_realization hReal
    ((generatedRecursorContractClosedIotaConvByNormalization?_ne_none_iff).1 h)

theorem generatedRecursorContract_fullyClosed_convByNormalization?_ne_none_implies_convDecl
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (h :
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none) :
    ConvDecl unitRecDeclEnv t u := by
  exact generatedRecursorContractClosedIotaConvByNormalization?_ne_none_implies_convDecl_of_realization
    (generatedRecursorContract_fullyClosed_realized_in_unit hFull) h

theorem generatedRecursorContract_admitted_convByNormalization?_ne_none_implies_convDecl_of_no_open
    {contract : FamilyRecursorDeclContract} {t u : PureTm 0}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hClosed : generatedRecursorContractOpenIotaObligations contract = [])
    (h :
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none) :
    ConvDecl unitRecDeclEnv t u := by
  exact generatedRecursorContractClosedIotaConvByNormalization?_ne_none_implies_convDecl_of_realization
    (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) h

theorem generatedRecursorContract_admitted_decl_boundary_current_frontier
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (generatedRecursorContractOpenIotaObligations contract = [] ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u))
    ∨
    (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_open_boundary hAdm with hClosed | hOpen
  · left
    refine ⟨hClosed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t u hStar
      exact generatedRecursorContractClosedIotaStar_realizes_redStarDecl_of_realization
        (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hStar
    · intro t u A hTy hStar
      exact generatedRecursorContract_admitted_star_SR_of_no_open_pi_only
        hAdm hClosed piInjective hTy hStar
    · exact generatedRecursorContractClosedIotaStep_confluent contract
    · exact generatedRecursorContractClosedIotaStep_normalizes contract
    · intro t u hEq
      exact generatedRecursorContractClosedIotaNormalize_eq_implies_convDecl_of_realization
        (generatedRecursorContract_admitted_realized_in_unit_of_no_open hAdm hClosed) hEq
    · intro t u w hSome
      exact generatedRecursorContract_admitted_convByNormalization?_sound_of_no_open
        hAdm hClosed hSome
    · intro t u hSome
      exact generatedRecursorContract_admitted_convByNormalization?_ne_none_implies_convDecl_of_no_open
        hAdm hClosed hSome
  · right
    exact hOpen

theorem generatedRecursorContract_admitted_decl_boundary_current_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (generatedRecursorContractOpenIotaObligations contract = [] ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u))
    ∨
    (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨_, hFull, _⟩
    rcases
        generatedRecursorContract_admitted_decl_sound_confluent_normalizing_and_conversion_of_no_open_of_church_rosser
          (contract := contract) hAdm hFull.2 hCR with
      ⟨hStepToDecl, hSR, hConfluent, hNormalizes, hNormEq, hConvSome, hConvNeNone⟩
    exact ⟨hFull.2, hStepToDecl, hSR, hConfluent, hNormalizes, hNormEq, hConvSome, hConvNeNone⟩
  · right
    rcases hNat with ⟨_, hOpen, _⟩
    exact ⟨hOpen, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_decl_boundary_current_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (generatedRecursorContractOpenIotaObligations contract = [] ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u))
    ∨
    (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_decl_boundary_current_frontier_of_church_rosser
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_decl_boundary_current_frontier_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (generatedRecursorContractOpenIotaObligations contract = [] ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u))
    ∨
    (generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_decl_boundary_current_frontier_of_church_rosser
    hAdm
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_exact_decl_boundary_current_frontier
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    rcases generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion
        (contract := contract) hFull piInjective with
      ⟨hRealizes, hSR, hConfluent, hNormalizes, hNormEq, hConvSome, hConvNeNone⟩
    exact ⟨hName, hFull.2, hFull, hReal, hRealizes, hSR, hConfluent, hNormalizes,
      hNormEq, hConvSome, hConvNeNone,
      generatedRecursorContract_fullyClosed_covers_all_obligations hFull⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_decl_boundary_current_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    rcases
        generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion_of_church_rosser
          (contract := contract) hFull hCR with
      ⟨hStepToDecl, hSR, hConfluent, hNormalizes, hNormEq, hConvSome, hConvNeNone⟩
    exact ⟨hName, hFull.2, hFull, hReal, hStepToDecl, hSR, hConfluent, hNormalizes,
      hNormEq, hConvSome, hConvNeNone,
      generatedRecursorContract_fullyClosed_covers_all_obligations hFull⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_decl_boundary_current_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_exact_decl_boundary_current_frontier_of_church_rosser
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_exact_decl_boundary_current_frontier_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_exact_decl_boundary_current_frontier_of_church_rosser
    hAdm
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  rcases generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion
      (contract := contract) hFull piInjective with
    ⟨hRealizes, hSR, hConfluent, hNormalizes, hNormEq, hConvSome, hConvNeNone⟩
  exact ⟨hGate, hRealizes, hSR, hConfluent, hNormalizes, hNormEq, hConvSome,
    hConvNeNone, hCover⟩

theorem generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  rcases generatedRecursorContract_fullyClosed_sound_and_complete_current_gate hFull with
    ⟨hGate, hCover⟩
  rcases
      generatedRecursorContract_fullyClosed_decl_sound_confluent_normalizing_and_conversion_of_church_rosser
        (contract := contract) hFull hCR with
    ⟨hStepToDecl, hSR, hConfluent, hNormalizes, hNormEq, hConvSome, hConvNeNone⟩
  exact ⟨hGate, hStepToDecl, hSR, hConfluent, hNormalizes, hNormEq, hConvSome,
    hConvNeNone, hCover⟩

theorem generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (∃ E : DeclEnv,
      DeclEnvWellFormed E ∧
      (∀ {t u : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u →
          ∃ A : PureTm 0,
            HasTypeDecl E .nil t A ∧
            HasTypeDecl E .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        GeneratedRecursorContractClosedIotaStep contract t u₁ →
        GeneratedRecursorContractClosedIotaStep contract t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
    (∀ {t u : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        RedStarDecl unitRecDeclEnv t u) ∧
    (∀ {t u A : PureTm 0},
      HasTypeDecl unitRecDeclEnv .nil t A →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
      HasTypeDecl unitRecDeclEnv .nil u A) ∧
    (∀ {t u₁ u₂ : PureTm 0},
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
      ∃ v : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
    (∀ t : PureTm 0,
      ∃ u : PureTm 0,
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
        ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaNormalize contract t =
        generatedRecursorContractClosedIotaNormalize contract u →
          ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {t u : PureTm 0},
      generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
        ConvDecl unitRecDeclEnv t u) ∧
    (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
      generatedRecursorPilot contract = some pilot →
      obligation ∈ pilot.obligations →
      ∃ rule : GeneratedClosedIotaRule,
        rule ∈ generatedRecursorContractClosedIotaRules contract ∧
        generateClosedIotaRule? obligation = some rule) := by
  exact generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier_of_church_rosser
    (contract := contract)
    hFull
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_fullyClosed_conditional_decl_frontier_package
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    GeneratedRecursorConditionalDeclFrontierPackage contract := by
  rcases generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier
      (contract := contract) hFull piInjective with
    ⟨hGate, hStepToDecl, hSR, hConfl, hNorm, hNormEq, hConvSome, hConvNeNone, hCover⟩
  exact ⟨hGate, ⟨hStepToDecl, hSR, hConfl, hNorm, hNormEq, hConvSome, hConvNeNone⟩, hCover⟩

theorem generatedRecursorContract_fullyClosed_conditional_decl_frontier_package_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    GeneratedRecursorConditionalDeclFrontierPackage contract := by
  rcases generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier_of_church_rosser
      (contract := contract) hFull hCR with
    ⟨hGate, hStepToDecl, hSR, hConfl, hNorm, hNormEq, hConvSome, hConvNeNone, hCover⟩
  exact ⟨hGate, ⟨hStepToDecl, hSR, hConfl, hNorm, hNormEq, hConvSome, hConvNeNone⟩, hCover⟩

theorem generatedRecursorContract_fullyClosed_conditional_decl_frontier_package_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    GeneratedRecursorConditionalDeclFrontierPackage contract := by
  exact generatedRecursorContract_fullyClosed_conditional_decl_frontier_package_of_church_rosser
    (contract := contract)
    hFull
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_fullyClosed_conditional_decl_frontier_package_sealed
    {contract : FamilyRecursorDeclContract}
    (hFull : GeneratedRecursorContractFullyClosed contract) :
    GeneratedRecursorConditionalDeclFrontierPackage contract := by
  exact generatedRecursorContract_fullyClosed_conditional_decl_frontier_package_of_church_rosser
    (contract := contract)
    hFull
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_exact_current_gate_conditional_frontier
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    rcases generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier
        (contract := contract) hFull piInjective with
      ⟨hGate, hRealizes, hSR, hConfluent, hNormalizes, hNormEq, hConvSome,
        hConvNeNone, hCover⟩
    exact ⟨hName, hFull.2, hFull, hReal, hGate, hRealizes, hSR, hConfluent,
      hNormalizes, hNormEq, hConvSome, hConvNeNone, hCover⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_conditional_frontier_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    GeneratedRecursorAdmittedExactConditionalFrontierPackage contract := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    have hPkg :
        GeneratedRecursorConditionalDeclFrontierPackage contract :=
      generatedRecursorContract_fullyClosed_conditional_decl_frontier_package
        (contract := contract) hFull piInjective
    exact ⟨hName, hFull.2, hFull, hReal, hPkg⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage contract := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  have hPkg :
      GeneratedRecursorAdmittedExactConditionalFrontierPackage contract :=
    generatedRecursorContract_admitted_exact_conditional_frontier_package
      (contract := contract) hAdm piInjective
  exact ⟨hGate, hBoundary, hPkg⟩

theorem generatedRecursorContract_admitted_exact_current_gate_conditional_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    rcases
        generatedRecursorContract_fullyClosed_current_gate_and_conditional_decl_frontier_of_church_rosser
          (contract := contract) hFull hCR with
      ⟨hGate, hStepToDecl, hSR, hConfluent, hNormalizes, hNormEq, hConvSome,
        hConvNeNone, hCover⟩
    exact ⟨hName, hFull.2, hFull, hReal, hGate, hStepToDecl, hSR, hConfluent,
      hNormalizes, hNormEq, hConvSome, hConvNeNone, hCover⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_current_gate_conditional_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_exact_current_gate_conditional_frontier_of_church_rosser
    (contract := contract)
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_exact_current_gate_conditional_frontier_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    (contract.recursorName = unitRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [] ∧
      GeneratedRecursorContractFullyClosed contract ∧
      GeneratedRecursorContractClosedIotaRealizedIn unitRecDeclEnv contract ∧
      (∃ E : DeclEnv,
        DeclEnvWellFormed E ∧
        (∀ {t u : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u →
            ∃ A : PureTm 0,
              HasTypeDecl E .nil t A ∧
              HasTypeDecl E .nil u A) ∧
        (∀ {t u₁ u₂ : PureTm 0},
          GeneratedRecursorContractClosedIotaStep contract t u₁ →
          GeneratedRecursorContractClosedIotaStep contract t u₂ →
          ∃ v : PureTm 0,
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
            Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v)) ∧
      (∀ {t u : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl unitRecDeclEnv t u) ∧
      (∀ {t u A : PureTm 0},
        HasTypeDecl unitRecDeclEnv .nil t A →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
        HasTypeDecl unitRecDeclEnv .nil u A) ∧
      (∀ {t u₁ u₂ : PureTm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₁ →
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u₂ →
        ∃ v : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₁ v ∧
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) u₂ v) ∧
      (∀ t : PureTm 0,
        ∃ u : PureTm 0,
          Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u ∧
          ¬ ∃ v : PureTm 0, GeneratedRecursorContractClosedIotaStep contract u v) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaNormalize contract t =
          generatedRecursorContractClosedIotaNormalize contract u →
            ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0} {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {t u : PureTm 0},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u ≠ none →
          ConvDecl unitRecDeclEnv t u) ∧
      (∀ {pilot : GeneratedRecursorPilot} {obligation : RecursorIotaObligation},
        generatedRecursorPilot contract = some pilot →
        obligation ∈ pilot.obligations →
        ∃ rule : GeneratedClosedIotaRule,
          rule ∈ generatedRecursorContractClosedIotaRules contract ∧
          generateClosedIotaRule? obligation = some rule))
    ∨
    (contract.recursorName = natRecName ∧
      generatedRecursorContractOpenIotaObligations contract = [natRecSuccIotaObligation] ∧
      ¬ GeneratedRecursorContractClosedIotaRealizedIn natRecDeclEnv contract ∧
      ∃ A : PureTm 1,
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenSource A ∧
        HasTypeDecl natRecDeclEnv natRecSuccOpenCtx natRecSuccOpenTarget A) := by
  exact generatedRecursorContract_admitted_exact_current_gate_conditional_frontier_of_church_rosser
    (contract := contract)
    hAdm
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_exact_conditional_frontier_package_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    GeneratedRecursorAdmittedExactConditionalFrontierPackage contract := by
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    have hPkg :
        GeneratedRecursorConditionalDeclFrontierPackage contract :=
      generatedRecursorContract_fullyClosed_conditional_decl_frontier_package_of_church_rosser
        (contract := contract) hFull hCR
    exact ⟨hName, hFull.2, hFull, hReal, hPkg⟩
  · right
    rcases hNat with ⟨hName, hOpen, hNotReal⟩
    exact ⟨hName, hOpen, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_conditional_frontier_package_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    GeneratedRecursorAdmittedExactConditionalFrontierPackage contract := by
  exact generatedRecursorContract_admitted_exact_conditional_frontier_package_of_church_rosser
    (contract := contract)
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_exact_conditional_frontier_package_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    GeneratedRecursorAdmittedExactConditionalFrontierPackage contract := by
  exact generatedRecursorContract_admitted_exact_conditional_frontier_package_of_church_rosser
    (contract := contract)
    hAdm
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage contract := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, hBoundary⟩
  have hPkg :
      GeneratedRecursorAdmittedExactConditionalFrontierPackage contract :=
    generatedRecursorContract_admitted_exact_conditional_frontier_package_of_church_rosser
      (contract := contract) hAdm hCR
  exact ⟨hGate, hBoundary, hPkg⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage contract := by
  exact generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_of_church_rosser
    (contract := contract)
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage contract := by
  exact generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_of_church_rosser
    (contract := contract)
    hAdm
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_exact_resolved_frontier_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage contract := by
  have hResolved :
      generatedRecursorContractResolvedIotaObligations contract = [] :=
    generatedRecursorContract_admitted_resolved_boundary hAdm
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    have hPkg :
        GeneratedRecursorConditionalDeclFrontierPackage contract :=
      generatedRecursorContract_fullyClosed_conditional_decl_frontier_package
        (contract := contract) hFull piInjective
    exact ⟨hName, hResolved, hFull, hReal, hPkg⟩
  · right
    rcases hNat with ⟨hName, _hOpen, hNotReal⟩
    exact ⟨hName, hResolved, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_resolved_frontier_package_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage contract := by
  have hResolved :
      generatedRecursorContractResolvedIotaObligations contract = [] :=
    generatedRecursorContract_admitted_resolved_boundary hAdm
  rcases generatedRecursorContract_admitted_realization_boundary hAdm with hUnit | hNat
  · left
    rcases hUnit with ⟨hName, hFull, hReal⟩
    have hPkg :
        GeneratedRecursorConditionalDeclFrontierPackage contract :=
      generatedRecursorContract_fullyClosed_conditional_decl_frontier_package_of_church_rosser
        (contract := contract) hFull hCR
    exact ⟨hName, hResolved, hFull, hReal, hPkg⟩
  · right
    rcases hNat with ⟨hName, _hOpen, hNotReal⟩
    exact ⟨hName, hResolved, hNotReal, natRecSuccOpenIotaRule_checked⟩

theorem generatedRecursorContract_admitted_exact_resolved_frontier_package_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage contract := by
  exact generatedRecursorContract_admitted_exact_resolved_frontier_package_of_church_rosser
    (contract := contract)
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_exact_resolved_frontier_package_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    GeneratedRecursorAdmittedExactResolvedFrontierPackage contract := by
  exact generatedRecursorContract_admitted_exact_resolved_frontier_package_of_church_rosser
    (contract := contract)
    hAdm
    DeclarationSemantics.declChurchRosser

theorem generatedRecursorContract_admitted_current_boundary_package_of_resolved_frontier
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl unitRecDeclEnv (.pi A B) (.pi A' B') →
          ConvDecl unitRecDeclEnv A A' ∧ ConvDecl unitRecDeclEnv B B') :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, _hOpenBoundary⟩
  have hResolved :
      generatedRecursorContractResolvedIotaObligations contract = [] :=
    generatedRecursorContract_admitted_resolved_boundary hAdm
  have hPkg :
      GeneratedRecursorAdmittedExactResolvedFrontierPackage contract :=
    generatedRecursorContract_admitted_exact_resolved_frontier_package
      (contract := contract) hAdm piInjective
  exact ⟨hGate, hResolved, hPkg⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_resolved_frontier_of_church_rosser
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hCR : DeclarationSemantics.DeclChurchRosser unitRecDeclEnv) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract := by
  rcases generatedRecursorContract_admitted_current_boundary hAdm with
    ⟨hGate, _hOpenBoundary⟩
  have hResolved :
      generatedRecursorContractResolvedIotaObligations contract = [] :=
    generatedRecursorContract_admitted_resolved_boundary hAdm
  have hPkg :
      GeneratedRecursorAdmittedExactResolvedFrontierPackage contract :=
    generatedRecursorContract_admitted_exact_resolved_frontier_package_of_church_rosser
      (contract := contract) hAdm hCR
  exact ⟨hGate, hResolved, hPkg⟩

theorem generatedRecursorContract_admitted_current_boundary_package_of_resolved_frontier_of_decl_package
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hDeclPkg :
      DeclarationSemantics.DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract := by
  exact generatedRecursorContract_admitted_current_boundary_package_of_resolved_frontier_of_church_rosser
    (contract := contract)
    hAdm
    (DeclarationSemantics.DeclChurchRosserFrontierPackage.declChurchRosser hDeclPkg)

theorem generatedRecursorContract_admitted_current_boundary_package_of_resolved_frontier_sealed
    {contract : FamilyRecursorDeclContract}
    (hAdm : GeneratedRecursorContractAdmitted contract) :
    GeneratedRecursorCurrentBoundaryResolvedFrontierPackage contract := by
  exact generatedRecursorContract_admitted_current_boundary_package_of_resolved_frontier_of_church_rosser
    (contract := contract)
    hAdm
    DeclarationSemantics.declChurchRosser

end Mettapedia.Languages.MeTTa.PureKernel.RecursorDecl
