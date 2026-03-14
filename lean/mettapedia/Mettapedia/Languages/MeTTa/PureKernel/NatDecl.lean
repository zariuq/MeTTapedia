import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

namespace Mettapedia.Languages.MeTTa.PureKernel.NatDecl

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

/-- Pilot family/type constant name for Nat in the declaration environment. -/
def natTyName : DeclName := `Nat

/-- Pilot constructor names for Nat (Lean-style naming). -/
def natZeroName : DeclName := `Nat.zero
def natSuccName : DeclName := `Nat.succ

/-- Pilot alias constant used to witness declaration-aware unfolding (`δ`). -/
def natAliasName : DeclName := `Nat.alias

/-- `Nat` family/type declaration spec. -/
def natTySpec : DeclSpec :=
  { name := natTyName, type := .u0 }

/-- `Nat.zero` constructor declaration spec. -/
def natZeroSpec : DeclSpec :=
  { name := natZeroName, type := .const natTyName }

/-- `Nat.succ` constructor declaration spec. -/
def natSuccSpec : DeclSpec :=
  { name := natSuccName, type := .pi (.const natTyName) (.const natTyName) }

/-- `Nat.alias` declaration spec used for the first `δ` witness. -/
def natAliasSpec : DeclSpec :=
  { name := natAliasName, type := .const natTyName, value? := some (.const natZeroName) }

/-- `Nat` pilot declarations expressed through the shared scaffold. -/
def natSpecs : List DeclSpec :=
  [natTySpec, natZeroSpec, natSuccSpec, natAliasSpec]

/-- Minimal declaration environment for the Nat pilot.
`Nat`, `Nat.zero`, and `Nat.succ` are declared; `Nat.alias` unfolds to `Nat.zero`. -/
def natDeclEnv : DeclEnv := envOfSpecs natSpecs

@[simp] theorem typeOf_natTy :
    typeOf? natDeclEnv natTyName = some .u0 := by
  decide

@[simp] theorem typeOf_natZero :
    typeOf? natDeclEnv natZeroName = some (.const natTyName) := by
  decide

@[simp] theorem typeOf_natSucc :
    typeOf? natDeclEnv natSuccName = some (.pi (.const natTyName) (.const natTyName)) := by
  decide

@[simp] theorem typeOf_natAlias :
    typeOf? natDeclEnv natAliasName = some (.const natTyName) := by
  decide

@[simp] theorem valueOf_natAlias :
    valueOf? natDeclEnv natAliasName = some (.const natZeroName) := by
  decide

/-- Typed declaration witness: `⊢ Nat : U0`. -/
theorem hasType_natTy :
    HasTypeDecl natDeclEnv .nil ((.const natTyName : PureTm 0)) .u0 :=
  hasType_const_from_lookup (E := natDeclEnv) (Γ := .nil) (c := natTyName) (A0 := .u0) (by
    simp)

/-- Typed declaration witness: `⊢ Nat.zero : Nat`. -/
theorem hasType_natZero :
    HasTypeDecl natDeclEnv .nil ((.const natZeroName : PureTm 0)) (.const natTyName) :=
  hasType_const_from_lookup (E := natDeclEnv) (Γ := .nil) (c := natZeroName) (A0 := .const natTyName) (by
    simp)

/-- Typed declaration witness: `⊢ Nat.succ : Nat → Nat`. -/
theorem hasType_natSucc :
    HasTypeDecl natDeclEnv .nil
      ((.const natSuccName : PureTm 0))
      (.pi (.const natTyName) (.const natTyName)) :=
  hasType_const_from_lookup
    (E := natDeclEnv) (Γ := .nil) (c := natSuccName) (A0 := .pi (.const natTyName) (.const natTyName)) (by
      simp)

/-- Typed declaration witness: `⊢ Nat.alias : Nat`. -/
theorem hasType_natAlias :
    HasTypeDecl natDeclEnv .nil ((.const natAliasName : PureTm 0)) (.const natTyName) :=
  hasType_const_from_lookup (E := natDeclEnv) (Γ := .nil) (c := natAliasName) (A0 := .const natTyName) (by
    simp)

/-- Reduction witness: `Nat.alias` unfolds to `Nat.zero`. -/
theorem red_natAlias_to_zero :
    RedDecl natDeclEnv
      ((.const natAliasName : PureTm 0))
      ((.const natZeroName : PureTm 0)) := by
  simpa using
    red_const_from_unfold0 (E := natDeclEnv) (c := natAliasName) (v := (.const natZeroName)) (by
      simp)

/-- Small checked pilot package: typed source, one declaration-aware step, typed target. -/
theorem natAlias_checked_step :
    ∃ A : PureTm 0,
      HasTypeDecl natDeclEnv .nil ((.const natAliasName : PureTm 0)) A ∧
      RedDecl natDeclEnv ((.const natAliasName : PureTm 0)) ((.const natZeroName : PureTm 0)) ∧
      HasTypeDecl natDeclEnv .nil ((.const natZeroName : PureTm 0)) A := by
  simpa using
    (checked_delta_step_closed_of_typed_value
      (E := natDeclEnv)
      (c := natAliasName)
      (A0 := (.const natTyName))
      (v0 := (.const natZeroName))
      (by simp)
      (by simp)
      (by simpa using hasType_natZero))

/-- Reusable typed-value obligations for `natSpecs` in any declaration
environment where `Nat.zero : Nat` is available. -/
theorem natSpecs_hTyped_in
    (E : DeclEnv)
    (hZeroType : typeOf? E natZeroName = some (.const natTyName)) :
    ∀ s ∈ natSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      HasTypeDecl E .nil (liftClosed v0) (liftClosed s.type) := by
  intro s hs v0 hVal
  simp [natSpecs, natTySpec, natZeroSpec, natSuccSpec, natAliasSpec] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simp at hVal
  · simp at hVal
  · simp at hVal
  · have hv : v0 = (.const natZeroName) := by
      simpa [natAliasSpec] using hVal.symm
    subst hv
    simpa [liftClosed_zero] using
      (hasType_const_from_lookup
        (E := E)
        (Γ := .nil)
        (c := natZeroName)
        (A0 := (.const natTyName))
        hZeroType)

/-- Reusable no-self-unfolding obligations for `natSpecs`. -/
theorem natSpecs_hNoSelf :
    ∀ s ∈ natSpecs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      v0 ≠ (.const s.name) := by
  intro s hs v0 hVal
  simp [natSpecs, natTySpec, natZeroSpec, natSuccSpec, natAliasSpec] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simp at hVal
  · simp at hVal
  · simp at hVal
  · have hv : v0 = (.const natZeroName) := by
      simpa [natAliasSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : ((.const natZeroName : PureTm 0)) ≠ (.const natAliasName) := by
      decide
    exact hNe hEq

def natSpecs_obligations : DeclSpecObligations natSpecs where
  valuesWellTyped :=
    natSpecs_hTyped_in
      (E := envOfSpecs natSpecs)
      (hZeroType := by decide)
  noSelfDelta := natSpecs_hNoSelf

def natSpecs_signatureWellFormed : SignatureWellFormed natSpecs where
  noShadowing := by decide
  obligations := natSpecs_obligations

theorem natTySpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [] natTySpec where
  fresh := by simp [natTySpec]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, natTySpec]
  valueUsesEarlier := by
    intro v0 hVal
    simp [natTySpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [natTySpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [natTySpec] at hVal

theorem natZeroSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [natTySpec] natZeroSpec where
  fresh := by simp [natTySpec, natZeroSpec, natTyName, natZeroName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames, natTySpec, natZeroSpec, natTyName, natZeroName]
  valueUsesEarlier := by
    intro v0 hVal
    simp [natZeroSpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [natZeroSpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [natZeroSpec] at hVal

theorem natSuccSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [natTySpec, natZeroSpec] natSuccSpec where
  fresh := by
    simp [natTySpec, natZeroSpec, natSuccSpec, natTyName, natZeroName, natSuccName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames,
      natTySpec, natZeroSpec, natSuccSpec, natTyName, natZeroName, natSuccName]
  valueUsesEarlier := by
    intro v0 hVal
    simp [natSuccSpec] at hVal
  valueWellTyped := by
    intro v0 hVal
    simp [natSuccSpec] at hVal
  noSelfDelta := by
    intro v0 hVal
    simp [natSuccSpec] at hVal

theorem natAliasSpec_prefixAdmissible :
    PrefixDeclSpecAdmissible [natTySpec, natZeroSpec, natSuccSpec] natAliasSpec where
  fresh := by
    simp [natTySpec, natZeroSpec, natSuccSpec, natAliasSpec,
      natTyName, natZeroName, natSuccName, natAliasName]
  typeUsesEarlier := by
    simp [UsesOnlyDeclNamesFrom, prefixNames,
      natTySpec, natZeroSpec, natSuccSpec, natAliasSpec,
      natTyName, natZeroName, natSuccName, natAliasName]
  valueUsesEarlier := by
    intro v0 hVal
    have hv : v0 = (.const natZeroName) := by
      simpa [natAliasSpec] using hVal.symm
    subst hv
    simp [UsesOnlyDeclNamesFrom, prefixNames,
      natTySpec, natZeroSpec, natSuccSpec, natZeroName]
  valueWellTyped := by
    intro v0 hVal
    have hv : v0 = (.const natZeroName) := by
      simpa [natAliasSpec] using hVal.symm
    subst hv
    have hLookup :
        typeOf? (envOfSpecs [natTySpec, natZeroSpec, natSuccSpec]) natZeroName =
          some (.const natTyName) :=
      typeOf_envOfSpecs_eq_of_mem_of_nodup
        (specs := [natTySpec, natZeroSpec, natSuccSpec])
        (s := natZeroSpec)
        (hNodup := by decide)
        (hs := by simp [natTySpec, natZeroSpec, natSuccSpec])
    simpa [liftClosed_zero] using
      (hasType_const_from_lookup
        (E := envOfSpecs [natTySpec, natZeroSpec, natSuccSpec])
        (Γ := .nil)
        (c := natZeroName)
        (A0 := (.const natTyName))
        hLookup)
  noSelfDelta := by
    intro v0 hVal
    have hv : v0 = (.const natZeroName) := by
      simpa [natAliasSpec] using hVal.symm
    subst hv
    intro hEq
    have hNe : ((.const natZeroName : PureTm 0)) ≠ (.const natAliasName) := by
      decide
    exact hNe hEq

theorem natSpecs_prefixWellFormed :
    SignatureWellFormedPrefix natSpecs := by
  refine And.intro natTySpec_prefixAdmissible ?_
  refine And.intro ?_ ?_
  · simpa [natSpecs, natTySpec, natZeroSpec]
      using natZeroSpec_prefixAdmissible
  · refine And.intro ?_ ?_
    · simpa [PrefixSignatureWellFormed, natSpecs, natTySpec, natZeroSpec, natSuccSpec]
        using natSuccSpec_prefixAdmissible
    · refine And.intro ?_ trivial
      simpa [PrefixSignatureWellFormed, natSpecs, natTySpec, natZeroSpec, natSuccSpec, natAliasSpec]
        using natAliasSpec_prefixAdmissible

theorem natSpecs_signatureWellFormed_fromPrefix :
    SignatureWellFormed natSpecs :=
  SignatureWellFormed.ofPrefix natSpecs_prefixWellFormed natSpecs_obligations

theorem natDeclEnv_wellFormed : DeclEnvWellFormed natDeclEnv := by
  unfold natDeclEnv
  exact natSpecs_signatureWellFormed.toDeclEnvWellFormed

end Mettapedia.Languages.MeTTa.PureKernel.NatDecl
