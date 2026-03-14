import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

namespace Mettapedia.Languages.MeTTa.PureKernel.UnitDecl

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

/-- Pilot family/type constant name for Unit in the declaration environment. -/
def unitTyName : DeclName := `Unit

/-- Pilot constructor constant name for Unit (Lean-style naming). -/
def unitCtorName : DeclName := `Unit.unit

/-- Pilot alias constant used to witness declaration-aware unfolding (`δ`). -/
def unitAliasName : DeclName := `Unit.alias

/-- `Unit` family/type declaration spec. -/
def unitTySpec : DeclSpec :=
  { name := unitTyName, type := .u0 }

/-- `Unit.unit` constructor declaration spec. -/
def unitCtorSpec : DeclSpec :=
  { name := unitCtorName, type := .const unitTyName }

/-- `Unit.alias` declaration spec used for the first `δ` witness. -/
def unitAliasSpec : DeclSpec :=
  { name := unitAliasName, type := .const unitTyName, value? := some (.const unitCtorName) }

/-- `Unit` pilot declarations expressed through the shared scaffold. -/
def unitSpecs : List DeclSpec :=
  [unitTySpec, unitCtorSpec, unitAliasSpec]

/-- Minimal declaration environment for the Unit pilot.
`Unit` and `Unit.unit` are declared; `Unit.alias` unfolds to `Unit.unit`. -/
def unitDeclEnv : DeclEnv := envOfSpecs unitSpecs

@[simp] theorem typeOf_unitTy : typeOf? unitDeclEnv unitTyName = some .u0 := by
  decide

@[simp] theorem typeOf_unitCtor :
    typeOf? unitDeclEnv unitCtorName = some (.const unitTyName) := by
  decide

@[simp] theorem typeOf_unitAlias :
    typeOf? unitDeclEnv unitAliasName = some (.const unitTyName) := by
  decide

@[simp] theorem valueOf_unitAlias :
    valueOf? unitDeclEnv unitAliasName = some (.const unitCtorName) := by
  decide

/-- Typed declaration witness: `⊢ Unit : U0`. -/
theorem hasType_unitTy :
    HasTypeDecl unitDeclEnv .nil (.const unitTyName) .u0 :=
  hasType_const_from_lookup (E := unitDeclEnv) (Γ := .nil) (c := unitTyName) (A0 := .u0) (by
    simp)

/-- Typed declaration witness: `⊢ Unit.unit : Unit`. -/
theorem hasType_unitCtor :
    HasTypeDecl unitDeclEnv .nil (.const unitCtorName) (.const unitTyName) :=
  hasType_const_from_lookup (E := unitDeclEnv) (Γ := .nil) (c := unitCtorName) (A0 := .const unitTyName) (by
    simp)

/-- Typed declaration witness: `⊢ Unit.alias : Unit`. -/
theorem hasType_unitAlias :
    HasTypeDecl unitDeclEnv .nil (.const unitAliasName) (.const unitTyName) :=
  hasType_const_from_lookup (E := unitDeclEnv) (Γ := .nil) (c := unitAliasName) (A0 := .const unitTyName) (by
    simp)

/-- Reduction witness: `Unit.alias` unfolds to `Unit.unit`. -/
theorem red_unitAlias_to_ctor :
    RedDecl unitDeclEnv
      ((.const unitAliasName : PureTm 0))
      ((.const unitCtorName : PureTm 0)) := by
  simpa using
    red_const_from_unfold0 (E := unitDeclEnv) (c := unitAliasName) (v := (.const unitCtorName)) (by
      simp)

/-- Small checked pilot package: typed source, one declaration-aware step, typed target. -/
theorem unitAlias_checked_step :
    ∃ A : PureTm 0,
      HasTypeDecl unitDeclEnv .nil ((.const unitAliasName : PureTm 0)) A ∧
      RedDecl unitDeclEnv ((.const unitAliasName : PureTm 0)) ((.const unitCtorName : PureTm 0)) ∧
      HasTypeDecl unitDeclEnv .nil ((.const unitCtorName : PureTm 0)) A := by
  simpa using
    (checked_delta_step_closed_of_typed_value
      (E := unitDeclEnv)
      (c := unitAliasName)
      (A0 := (.const unitTyName))
      (v0 := (.const unitCtorName))
      (by simp)
      (by simp)
      (by simpa using hasType_unitCtor))

/-- Reusable typed-value obligations for `unitSpecs` in any declaration
environment where `Unit.unit : Unit` is available. -/
theorem unitSpecs_hTyped_in
    (E : DeclEnv)
    (hCtorType : typeOf? E unitCtorName = some (.const unitTyName)) :
    ∀ s ∈ unitSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      HasTypeDecl E .nil (liftClosed v0) (liftClosed s.type) := by
  intro s hs v0 hVal
  simp [unitSpecs, unitTySpec, unitCtorSpec, unitAliasSpec] at hs
  rcases hs with rfl | rfl | rfl
  · simp at hVal
  · simp at hVal
  · have hv : v0 = (.const unitCtorName) := by
      simpa [unitAliasSpec] using hVal.symm
    subst hv
    simpa [liftClosed_zero] using
      (hasType_const_from_lookup
        (E := E)
        (Γ := .nil)
        (c := unitCtorName)
        (A0 := (.const unitTyName))
        hCtorType)

/-- Reusable no-self-unfolding obligations for `unitSpecs`. -/
theorem unitSpecs_hNoSelf :
    ∀ s ∈ unitSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      v0 ≠ (.const s.name) := by
  intro s hs v0 hVal
  simp [unitSpecs, unitTySpec, unitCtorSpec, unitAliasSpec] at hs
  rcases hs with rfl | rfl | rfl
  · simp at hVal
  · simp at hVal
  · have hv : v0 = (.const unitCtorName) := by
      simpa [unitAliasSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : ((.const unitCtorName : PureTm 0)) ≠ (.const unitAliasName) := by
      decide
    exact hNe hEq

def unitSpecs_obligations : DeclSpecObligations unitSpecs where
  valuesWellTyped :=
    unitSpecs_hTyped_in
      (E := envOfSpecs unitSpecs)
      (hCtorType := by decide)
  noSelfDelta := unitSpecs_hNoSelf

def unitSpecs_signatureWellFormed : SignatureWellFormed unitSpecs where
  noShadowing := by decide
  obligations := unitSpecs_obligations

theorem unitTySpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [] unitTySpec where
  fresh := by simp [unitTySpec]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, unitTySpec]
  valueUsesEarlier := by
    intro v0 hVal
    simp [unitTySpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [unitTySpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [unitTySpec] at hVal

theorem unitCtorSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [unitTySpec] unitCtorSpec where
  fresh := by simp [unitTySpec, unitCtorSpec, unitTyName, unitCtorName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, unitTySpec, unitCtorSpec, unitTyName, unitCtorName]
  valueUsesEarlier := by
    intro v0 hVal
    simp [unitCtorSpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [unitCtorSpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [unitCtorSpec] at hVal

theorem unitAliasSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [unitTySpec, unitCtorSpec] unitAliasSpec where
  fresh := by
    simp [unitTySpec, unitCtorSpec, unitAliasSpec, unitTyName, unitCtorName, unitAliasName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames,
      unitTySpec, unitCtorSpec, unitAliasSpec, unitTyName, unitCtorName, unitAliasName]
  valueUsesEarlier := by
    intro v0 hVal
    have hv : v0 = (.const unitCtorName) := by
      simpa [unitAliasSpec] using hVal.symm
    subst hv
    simp [UsesOnlyDeclNamesFrom, prefixNames, unitTySpec, unitCtorSpec, unitCtorName]
  valueWellTyped := by
    intro v0 hVal
    have hv : v0 = (.const unitCtorName) := by
      simpa [unitAliasSpec] using hVal.symm
    subst hv
    have hLookup :
        typeOf? (envOfSpecs [unitTySpec, unitCtorSpec]) unitCtorName = some (.const unitTyName) :=
      typeOf_envOfSpecs_eq_of_mem_of_nodup
        (specs := [unitTySpec, unitCtorSpec])
        (s := unitCtorSpec)
        (hNodup := by decide)
        (hs := by simp [unitTySpec, unitCtorSpec])
    simpa [liftClosed_zero] using
      (hasType_const_from_lookup
        (E := envOfSpecs [unitTySpec, unitCtorSpec])
        (Γ := .nil)
        (c := unitCtorName)
        (A0 := (.const unitTyName))
        hLookup)
  noSelfDelta := by
    intro v0 hVal
    have hv : v0 = (.const unitCtorName) := by
      simpa [unitAliasSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : ((.const unitCtorName : PureTm 0)) ≠ (.const unitAliasName) := by
      decide
    exact hNe hEq

theorem unitSpecs_prefixWellFormed :
    SignatureWellFormedPrefix unitSpecs := by
  refine And.intro unitTySpec_prefixAdmissible ?_
  refine And.intro ?_ ?_
  · simpa [unitSpecs, unitTySpec, unitCtorSpec]
      using unitCtorSpec_prefixAdmissible
  · refine And.intro ?_ trivial
    simpa [PrefixSignatureWellFormed, unitSpecs, unitTySpec, unitCtorSpec, unitAliasSpec]
      using unitAliasSpec_prefixAdmissible

theorem unitSpecs_signatureWellFormed_fromPrefix :
    SignatureWellFormed unitSpecs :=
  SignatureWellFormed.ofPrefix unitSpecs_prefixWellFormed unitSpecs_obligations

theorem unitDeclEnv_wellFormed : DeclEnvWellFormed unitDeclEnv := by
  unfold unitDeclEnv
  exact unitSpecs_signatureWellFormed.toDeclEnvWellFormed

end Mettapedia.Languages.MeTTa.PureKernel.UnitDecl
