import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

namespace Mettapedia.Languages.MeTTa.PureKernel.BoolDecl

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

/-- Pilot family/type constant name for Bool in the declaration environment. -/
def boolTyName : DeclName := `Bool

/-- Pilot constructor constant names for Bool. -/
def boolTrueName : DeclName := `Bool.true
def boolFalseName : DeclName := `Bool.false

/-- Pilot alias constant used to witness declaration-aware unfolding (`δ`). -/
def boolAliasName : DeclName := `Bool.alias

/-- `Bool` family/type declaration spec. -/
def boolTySpec : DeclSpec :=
  { name := boolTyName, type := .u0 }

/-- `Bool.true` constructor declaration spec. -/
def boolTrueSpec : DeclSpec :=
  { name := boolTrueName, type := .const boolTyName }

/-- `Bool.false` constructor declaration spec. -/
def boolFalseSpec : DeclSpec :=
  { name := boolFalseName, type := .const boolTyName }

/-- `Bool.alias` declaration spec used for the first `δ` witness. -/
def boolAliasSpec : DeclSpec :=
  { name := boolAliasName, type := .const boolTyName, value? := some (.const boolTrueName) }

/-- `Bool` pilot declarations expressed through the shared scaffold. -/
def boolSpecs : List DeclSpec :=
  [boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec]

/-- Minimal declaration environment for the Bool pilot.
`Bool`, `Bool.true`, and `Bool.false` are declared; `Bool.alias` unfolds to `Bool.true`. -/
def boolDeclEnv : DeclEnv := envOfSpecs boolSpecs

@[simp] theorem typeOf_boolTy :
    typeOf? boolDeclEnv boolTyName = some .u0 := by
  decide

@[simp] theorem typeOf_boolTrue :
    typeOf? boolDeclEnv boolTrueName = some (.const boolTyName) := by
  decide

@[simp] theorem typeOf_boolFalse :
    typeOf? boolDeclEnv boolFalseName = some (.const boolTyName) := by
  decide

@[simp] theorem typeOf_boolAlias :
    typeOf? boolDeclEnv boolAliasName = some (.const boolTyName) := by
  decide

@[simp] theorem valueOf_boolAlias :
    valueOf? boolDeclEnv boolAliasName = some (.const boolTrueName) := by
  decide

/-- Typed declaration witness: `⊢ Bool : U0`. -/
theorem hasType_boolTy :
    HasTypeDecl boolDeclEnv .nil ((.const boolTyName : PureTm 0)) .u0 :=
  hasType_const_from_lookup (E := boolDeclEnv) (Γ := .nil) (c := boolTyName) (A0 := .u0) (by
    simp)

/-- Typed declaration witness: `⊢ Bool.true : Bool`. -/
theorem hasType_boolTrue :
    HasTypeDecl boolDeclEnv .nil ((.const boolTrueName : PureTm 0)) (.const boolTyName) :=
  hasType_const_from_lookup (E := boolDeclEnv) (Γ := .nil) (c := boolTrueName) (A0 := .const boolTyName) (by
    simp)

/-- Typed declaration witness: `⊢ Bool.false : Bool`. -/
theorem hasType_boolFalse :
    HasTypeDecl boolDeclEnv .nil ((.const boolFalseName : PureTm 0)) (.const boolTyName) :=
  hasType_const_from_lookup (E := boolDeclEnv) (Γ := .nil) (c := boolFalseName) (A0 := .const boolTyName) (by
    simp)

/-- Typed declaration witness: `⊢ Bool.alias : Bool`. -/
theorem hasType_boolAlias :
    HasTypeDecl boolDeclEnv .nil ((.const boolAliasName : PureTm 0)) (.const boolTyName) :=
  hasType_const_from_lookup (E := boolDeclEnv) (Γ := .nil) (c := boolAliasName) (A0 := .const boolTyName) (by
    simp)

/-- Reduction witness: `Bool.alias` unfolds to `Bool.true`. -/
theorem red_boolAlias_to_true :
    RedDecl boolDeclEnv
      ((.const boolAliasName : PureTm 0))
      ((.const boolTrueName : PureTm 0)) := by
  simpa using
    red_const_from_unfold0 (E := boolDeclEnv) (c := boolAliasName) (v := (.const boolTrueName)) (by
      simp)

/-- Small checked pilot package: typed source, one declaration-aware step, typed target. -/
theorem boolAlias_checked_step :
    ∃ A : PureTm 0,
      HasTypeDecl boolDeclEnv .nil ((.const boolAliasName : PureTm 0)) A ∧
      RedDecl boolDeclEnv ((.const boolAliasName : PureTm 0)) ((.const boolTrueName : PureTm 0)) ∧
      HasTypeDecl boolDeclEnv .nil ((.const boolTrueName : PureTm 0)) A := by
  simpa using
    (checked_delta_step_closed_of_typed_value
      (E := boolDeclEnv)
      (c := boolAliasName)
      (A0 := (.const boolTyName))
      (v0 := (.const boolTrueName))
      (by simp)
      (by simp)
      (by simpa using hasType_boolTrue))

/-- Reusable typed-value obligations for `boolSpecs` in any declaration
environment where `Bool.true : Bool` is available. -/
theorem boolSpecs_hTyped_in
    (E : DeclEnv)
    (hTrueType : typeOf? E boolTrueName = some (.const boolTyName)) :
    ∀ s ∈ boolSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      HasTypeDecl E .nil (liftClosed v0) (liftClosed s.type) := by
  intro s hs v0 hVal
  simp [boolSpecs, boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simp at hVal
  · simp at hVal
  · simp at hVal
  · have hv : v0 = (.const boolTrueName) := by
      simpa [boolAliasSpec] using hVal.symm
    subst hv
    simpa [liftClosed_zero] using
      (hasType_const_from_lookup
        (E := E)
        (Γ := .nil)
        (c := boolTrueName)
        (A0 := (.const boolTyName))
        hTrueType)

/-- Reusable no-self-unfolding obligations for `boolSpecs`. -/
theorem boolSpecs_hNoSelf :
    ∀ s ∈ boolSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      v0 ≠ (.const s.name) := by
  intro s hs v0 hVal
  simp [boolSpecs, boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simp at hVal
  · simp at hVal
  · simp at hVal
  · have hv : v0 = (.const boolTrueName) := by
      simpa [boolAliasSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : ((.const boolTrueName : PureTm 0)) ≠ (.const boolAliasName) := by
      decide
    exact hNe hEq

def boolSpecs_obligations : DeclSpecObligations boolSpecs where
  valuesWellTyped :=
    boolSpecs_hTyped_in
      (E := envOfSpecs boolSpecs)
      (hTrueType := by decide)
  noSelfDelta := boolSpecs_hNoSelf

def boolSpecs_signatureWellFormed : SignatureWellFormed boolSpecs where
  noShadowing := by decide
  obligations := boolSpecs_obligations

theorem boolTySpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [] boolTySpec where
  fresh := by simp [boolTySpec]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, boolTySpec]
  valueUsesEarlier := by
    intro v0 hVal
    simp [boolTySpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [boolTySpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [boolTySpec] at hVal

theorem boolTrueSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [boolTySpec] boolTrueSpec where
  fresh := by simp [boolTySpec, boolTrueSpec, boolTyName, boolTrueName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, boolTySpec, boolTrueSpec, boolTyName, boolTrueName]
  valueUsesEarlier := by
    intro v0 hVal
    simp [boolTrueSpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [boolTrueSpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [boolTrueSpec] at hVal

theorem boolFalseSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [boolTySpec, boolTrueSpec] boolFalseSpec where
  fresh := by
    simp [boolTySpec, boolTrueSpec, boolFalseSpec, boolTyName, boolTrueName, boolFalseName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames,
      boolTySpec, boolTrueSpec, boolFalseSpec, boolTyName, boolTrueName, boolFalseName]
  valueUsesEarlier := by
    intro v0 hVal
    simp [boolFalseSpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [boolFalseSpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [boolFalseSpec] at hVal

theorem boolAliasSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [boolTySpec, boolTrueSpec, boolFalseSpec] boolAliasSpec where
  fresh := by
    simp [boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec,
      boolTyName, boolTrueName, boolFalseName, boolAliasName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames,
      boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec,
      boolTyName, boolTrueName, boolFalseName, boolAliasName]
  valueUsesEarlier := by
    intro v0 hVal
    have hv : v0 = (.const boolTrueName) := by
      simpa [boolAliasSpec] using hVal.symm
    subst hv
    simp [UsesOnlyDeclNamesFrom, prefixNames,
      boolTySpec, boolTrueSpec, boolFalseSpec, boolTrueName]
  valueWellTyped := by
    intro v0 hVal
    have hv : v0 = (.const boolTrueName) := by
      simpa [boolAliasSpec] using hVal.symm
    subst hv
    have hLookup :
        typeOf? (envOfSpecs [boolTySpec, boolTrueSpec, boolFalseSpec]) boolTrueName =
          some (.const boolTyName) :=
      typeOf_envOfSpecs_eq_of_mem_of_nodup
        (specs := [boolTySpec, boolTrueSpec, boolFalseSpec])
        (s := boolTrueSpec)
        (hNodup := by decide)
        (hs := by simp [boolTySpec, boolTrueSpec, boolFalseSpec])
    simpa [liftClosed_zero] using
      (hasType_const_from_lookup
        (E := envOfSpecs [boolTySpec, boolTrueSpec, boolFalseSpec])
        (Γ := .nil)
        (c := boolTrueName)
        (A0 := (.const boolTyName))
        hLookup)
  noSelfDelta := by
    intro v0 hVal
    have hv : v0 = (.const boolTrueName) := by
      simpa [boolAliasSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : ((.const boolTrueName : PureTm 0)) ≠ (.const boolAliasName) := by
      decide
    exact hNe hEq

theorem boolSpecs_prefixWellFormed :
    SignatureWellFormedPrefix boolSpecs := by
  refine And.intro boolTySpec_prefixAdmissible ?_
  refine And.intro ?_ ?_
  · simpa [boolSpecs, boolTySpec, boolTrueSpec]
      using boolTrueSpec_prefixAdmissible
  · refine And.intro ?_ ?_
    · simpa [PrefixSignatureWellFormed, boolSpecs, boolTySpec, boolTrueSpec, boolFalseSpec]
        using boolFalseSpec_prefixAdmissible
    · refine And.intro ?_ trivial
      simpa [PrefixSignatureWellFormed, boolSpecs, boolTySpec, boolTrueSpec, boolFalseSpec, boolAliasSpec]
        using boolAliasSpec_prefixAdmissible

theorem boolSpecs_signatureWellFormed_fromPrefix :
    SignatureWellFormed boolSpecs :=
  SignatureWellFormed.ofPrefix boolSpecs_prefixWellFormed boolSpecs_obligations

theorem boolDeclEnv_wellFormed : DeclEnvWellFormed boolDeclEnv := by
  unfold boolDeclEnv
  exact boolSpecs_signatureWellFormed.toDeclEnvWellFormed

end Mettapedia.Languages.MeTTa.PureKernel.BoolDecl
