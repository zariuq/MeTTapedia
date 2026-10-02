import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.CheckedDefinitionalExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDelta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationSensitiveRestrictionExamples

/-!
# A nonempty transparent signature and its conversion boundary

The package contains a ground alias, a second alias referencing the first,
an opaque value at the second alias, and the previously formed polymorphic
identity definition. It uses the existing declaration-signature machinery,
not a separate evaluator. The dependency-order check supplies a proved finite
expansion budget, including the transitive alias dependency.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstantExpansion.Examples

open Declaration FormationSensitive
open FormationSensitive.Dependencies.Examples (aliasName valueName extraName ground extraBody)

variable {n : Nat}

def secondAliasName : DeclName := `ExpansionExample.SecondAlias

def entries : List (DeclName × Entry Tower.Head) :=
  [ (aliasName, ⟨sortTm Tower.zero, some ground⟩),
    (secondAliasName, ⟨sortTm Tower.zero, some (.const aliasName)⟩),
    (valueName, ⟨.const secondAliasName, none⟩),
    (extraName, ⟨FormationSensitive.Examples.polymorphicIdentityType Tower.zero,
      some extraBody⟩) ]

def signature : Signature Tower.Head := Signature.ofList entries

def rules : Rules Tower.Head := extendRules Tower.rules signature

def bodies : Bodies Tower.Head := Checked.bodies signature (entries.length + 1)

theorem entries_ordered : Checked.Ordered.check entries = true := by decide +kernel

/-- One unfolding round has not yet resolved the transitive alias. -/
theorem one_round_incomplete : Checked.check entries 1 = false := by decide +kernel

theorem two_rounds_checked : Checked.check entries 2 = true := by decide +kernel

/-- The automatic budget computes the same bodies as the smaller accepted
budget. Its bound is sufficient, not a claimed optimum. -/
theorem automatic_bodies_agree : Checked.bodies signature 2 = bodies := by
  exact (Checked.bodies_stable entries 2 two_rounds_checked 3).symm

theorem second_alias_computed : bodies secondAliasName = ground := by decide +kernel

theorem opaque_value_retained : bodies valueName = .const valueName := by decide +kernel

theorem identity_body_computed : bodies extraName = extraBody := by decide +kernel

private theorem alias_lookup : signature.valueOf? aliasName = some ground := by
  simp [signature, entries, Signature.ofList, Signature.insert, Signature.empty,
    Signature.valueOf?, aliasName, secondAliasName, valueName, extraName]

private theorem second_lookup : signature.valueOf? secondAliasName = some (.const aliasName) := by
  simp [signature, entries, Signature.ofList, Signature.insert, Signature.empty,
    Signature.valueOf?, aliasName, secondAliasName, valueName, extraName]

private theorem identity_lookup : signature.valueOf? extraName = some extraBody := by
  simp [signature, entries, Signature.ofList, Signature.insert, Signature.empty,
    Signature.valueOf?, aliasName, secondAliasName, valueName, extraName]

/-- Dependency ordering supplies the expansion budget and qualification;
there are no example-specific conversion proofs or guessed rounds here. -/
def qualification : Qualification rules :=
  Checked.Ordered.qualification Tower.rules rfl entries entries_ordered

/-- The executable entry point returns this very qualification. -/
theorem qualification_computed :
    Checked.Ordered.qualify? Tower.rules rfl entries = some qualification := by
  simp only [Checked.Ordered.qualify?, entries_ordered, dite_true, qualification]
  rfl

theorem insufficient_rounds_return_none :
    Checked.qualify? Tower.rules rfl entries 1 = none := by
  simp only [Checked.qualify?, one_round_incomplete, Bool.false_eq_true, dite_false]

/-- A shadowed declaration must not change the first-match signature's
qualification. Its unselected body is deliberately not expansion-compatible. -/
theorem shadowed_body_ignored :
    Checked.check (entries ++ [(aliasName, ⟨sortTm Tower.zero,
      some (.app (.const aliasName) (.const aliasName))⟩)]) 2 = true := by decide +kernel

/-- Moving that same declaration before the selected definition changes the
signature and makes this bounded check fail. -/
theorem selected_recursive_body_rejected :
    Checked.check ((aliasName, ⟨sortTm Tower.zero,
      some (.app (.const aliasName) (.const aliasName))⟩) :: entries) 2 = false := by
  decide +kernel

/-- The order check also follows first-match selection rather than inspecting
the deliberately cyclic, shadowed body. -/
theorem shadowed_body_ordered :
    Checked.Ordered.check (entries ++ [(aliasName, ⟨sortTm Tower.zero,
      some (.app (.const aliasName) (.const aliasName))⟩)]) = true := by decide +kernel

theorem selected_recursive_body_not_ordered :
    Checked.Ordered.check ((aliasName, ⟨sortTm Tower.zero,
      some (.app (.const aliasName) (.const aliasName))⟩) :: entries) = false := by decide +kernel

/-- A forward transparent reference fails this sufficient order test, even
though the same signature admits the original bounded qualification. -/
theorem forward_transparent_reference_not_ordered :
    Checked.Ordered.check entries.reverse = false ∧
      Checked.check entries.reverse 2 = true := by decide +kernel

/-- Opaque references need not occur earlier: their expansion is constant. -/
theorem forward_opaque_reference_ordered :
    Checked.Ordered.check
      [(secondAliasName, ⟨ground, some (.const valueName)⟩),
        (valueName, ⟨ground, none⟩)] = true := by decide +kernel

/-- A dependency below binders is inspected too, not just an alias head. -/
theorem nested_forward_reference_not_ordered :
    Checked.Ordered.check
      [(extraName, ⟨FormationSensitive.Examples.polymorphicIdentityType Tower.zero,
          some (.lam (.lam (.const aliasName)))⟩),
        (aliasName, ⟨sortTm Tower.zero, some ground⟩)] = false := by decide +kernel

/-- Complete unfolding of constants is not beta normalization. This raw,
untyped self-application has no constants and still takes a beta self-step. -/
theorem ordered_expansion_does_not_normalize_beta :
    let loopBody : Tower.Tm 1 := .app (.var 0) (.var 0)
    let loop : Tower.Tm 0 := .app (.lam loopBody) (.lam loopBody)
    expand bodies loop = loop ∧ Step rules.headEq loop loop rules.computation := by
  exact ⟨rfl, .betaPi (.app (.var 0) (.var 0)) (.lam (.app (.var 0) (.var 0)))⟩

/-- Conversion of arbitrary open terms is exactly pure conversion after
the certified transitive expansion; no bounded corpus stands in for this law. -/
theorem conversion_iff (left right : Tower.Tm n) :
    Conv rules.headEq left right rules.computation ↔
      Conv Tower.HeadEq (expand bodies left) (expand bodies right) :=
  qualification.conversion_iff left right

theorem pi_boundary : PiConversionBoundary rules :=
  qualification.piConversionBoundary LevelTower.headEq_symmetric

theorem universes : UniverseRegularity rules where
  head_target := towerUniverseRegularity.head_target
  join_target := towerUniverseRegularity.join_target
  cumulative_target := towerUniverseRegularity.cumulative_target
  universe_typed := towerUniverseRegularity.universe_typed

/-- Nonempty definitions no longer leave an assumed Pi-boundary premise in
the beta-preservation result. -/
theorem beta_preserves {Γ : Tower.Ctx n} {body : Tower.Tm (n + 1)}
    {argument displayed : Tower.Tm n}
    (judgment : Judgment rules Γ (.app (.lam body) argument) displayed) :
    Judgment rules Γ (inst0 argument body) displayed :=
  qualification.betaPi LevelTower.headEq_symmetric universes judgment

private theorem base_typed {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Typing Tower.rules Γ term type) : Typing rules Γ term type := by
  apply Dependencies.typing_transfer ?_ typing
  intro requirement valid
  cases requirement with
  | constantType name type => cases valid
  | rootStep n left right => exact valid.elim
  | _ => exact valid

theorem alias_conversion :
    Conv rules.headEq (.const secondAliasName : Tower.Tm n) ground rules.computation :=
  .trans _ _ _ (.rel _ _ (.root (.delta second_lookup)))
    (.rel _ _ (.root (.delta alias_lookup)))

theorem alias_formed (Γ : Tower.Ctx n) :
    Typing rules Γ (.const secondAliasName) (sortTm Tower.zero) := by
  have known : rules.constantType secondAliasName = some (sortTm Tower.zero) := by decide
  exact .const known (.headType (LevelTower.HeadTyping.sort Tower.zero))
    (LevelTower.IsUniverse.sort _)

theorem value_at_alias (Γ : Tower.Ctx n) :
    Typing rules Γ (.const valueName) (.const secondAliasName) :=
  .const (by decide) (alias_formed .nil) (.sort _)

theorem value_at_ground (Γ : Tower.Ctx n) :
    Typing rules Γ (.const valueName) ground :=
  .conv (value_at_alias Γ) (.headType .legacyGround) (.sort _) alias_conversion

private theorem identity_declared : rules.constantType extraName =
    some (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) := by decide

theorem identity_body_typed (Γ : Tower.Ctx n) :
    Typing rules Γ extraBody
      (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) :=
  base_typed (FormationSensitive.Examples.polymorphicIdentity_typed Γ Tower.zero)

theorem identity_constant_typed (Γ : Tower.Ctx n) :
    Typing rules Γ (.const extraName)
      (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) :=
  .const identity_declared
    (base_typed (FormationSensitive.Examples.polymorphicIdentityType_formed .nil Tower.zero))
    (.sort _)

/-- The declaration's actual delta reduction preserves the checked dependent
function type, using the independent body derivation. -/
theorem identity_delta_checked :
    Step rules.headEq (.const extraName : Tower.Tm 0) extraBody rules.computation ∧
      Judgment rules .nil extraBody
        (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) := by
  exact (Judgment.delta ⟨.nil, identity_constant_typed .nil⟩ identity_lookup
    identity_declared (identity_body_typed .nil))

def specialize (function : Tower.Tm n) : Tower.Tm n :=
  .app (.app function (.const secondAliasName)) (.const valueName)

theorem specialize_typed {Γ : Tower.Ctx n} {function : Tower.Tm n}
    (typed : Typing rules Γ function
      (FormationSensitive.Examples.polymorphicIdentityType Tower.zero)) :
    Typing rules Γ (specialize function) ground := by
  have first := Typing.appElim typed (alias_formed Γ)
  have functionTyped : Typing rules Γ (.app function (.const secondAliasName))
      (.pi (.const secondAliasName) (.const secondAliasName)) := first
  have result := Typing.appElim functionTyped (value_at_alias Γ)
  exact .conv result (.headType .legacyGround) (.sort _) alias_conversion

/-- Unfolding the named dependent identity and then performing two beta
steps returns the original opaque value. Every intermediate has refined
typing at the displayed ground type. -/
theorem specialized_identity_run (Γ : Tower.Ctx n) :
    Typing rules Γ (specialize (.const extraName)) ground ∧
    Typing rules Γ (specialize extraBody) ground ∧
    Typing rules Γ (.app (.lam (.var 0)) (.const valueName)) ground ∧
    Typing rules Γ (.const valueName) ground ∧
    Step rules.headEq (specialize (.const extraName) : Tower.Tm n) (specialize extraBody)
      rules.computation ∧
    Step rules.headEq (specialize extraBody : Tower.Tm n) (.app (.lam (.var 0)) (.const valueName))
      rules.computation ∧
    Step rules.headEq (.app (.lam (.var 0)) (.const valueName) : Tower.Tm n) (.const valueName)
      rules.computation := by
  refine ⟨specialize_typed (identity_constant_typed Γ),
    specialize_typed (identity_body_typed Γ), ?_, value_at_ground Γ,
    .congAppFun (.congAppFun (.root (.delta identity_lookup))), ?_, ?_⟩
  · have piFormed : Typing rules Γ (.pi ground ground)
        (sortTm (.max Tower.zero Tower.zero)) :=
      .piForm (.headType .legacyGround) (.sort _) (.headType .legacyGround)
        (.sort _) (.sorts _ _)
    have functionTyped : Typing rules Γ (.lam (.var 0)) (.pi ground ground) :=
      .lamIntro piFormed (.sort _) (.var 0)
    exact .appElim functionTyped (value_at_ground Γ)
  · apply Step.congAppFun
    exact Step.betaPi (.lam (.var 0)) (.const secondAliasName)
  · exact Step.betaPi (.var 0) (.const valueName)

/-- Aliasing a ground type does not let it serve as a function type. -/
theorem alias_not_pi (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) :
    ¬ Conv rules.headEq (.const secondAliasName) (.pi domain codomain) rules.computation := by
  intro conversion
  exact pi_boundary.headDisjoint
    (.trans _ _ _ (.symm _ _ conversion) alias_conversion)

/-- The earlier well-formed Pi/head collapse cannot pass this qualification,
for any proposed constant bodies. -/
theorem collapse_has_no_qualification :
    ¬ Nonempty (Qualification FormationSensitive.Examples.ConversionCollapse.rules) :=
  no_qualification_of_pi_head LevelTower.headEq_symmetric
    (Relation.EqvGen.symm _ _
      (FormationSensitive.Examples.ConversionCollapse.ground_converts_endomorphism (n := 0)))

namespace CyclicDefinition

def name : DeclName := `ExpansionExample.loop

/-- This intentionally cyclic signature is only a negative control. -/
def signature : Signature Tower.Head :=
  Signature.ofList [(name, ⟨ground, some (.const name)⟩)]

def rules : Rules Tower.Head := extendRules Tower.rules signature

/-- Even the executable qualifier accepts a self-loop: conversion qualification
is not a termination test. -/
def qualification : Qualification rules :=
  Checked.qualification Tower.rules rfl [(name, ⟨ground, some (.const name)⟩)] 0
    (by decide +kernel)

/-- The stronger order test rejects the self-loop accepted by the fixed-point
conversion test. The two checks intentionally establish different properties. -/
theorem ordered_qualifier_rejects_loop :
    Checked.Ordered.qualify? Tower.rules rfl [(name, ⟨ground, some (.const name)⟩)] = none := by
  simp [Checked.Ordered.qualify?, Checked.Ordered.check, Checked.Ordered.rank,
    constantNames, Signature.ofList, Signature.insert, Signature.empty, Signature.valueOf?]

theorem loop_typed : Judgment rules (.nil : Tower.Ctx 0) (.const name) ground := by
  have known : rules.constantType name = some ground := by decide
  exact ⟨.nil, .const known (.headType LevelTower.HeadTyping.legacyGround) (.sort _)⟩

theorem loop_step :
    Step rules.headEq (.const name : Tower.Tm 0) (.const name) rules.computation := by
  have lookup : signature.valueOf? name = some (.const name) := by decide
  exact .root (RootStep.delta (base := Tower.rules) (n := 0) lookup)

/-- Qualification and refined typing do not imply strong normalization of
the operational unfolding relation. A termination check remains separate. -/
theorem loop_not_accessible :
    ¬ Acc (fun reduct source : Tower.Tm 0 =>
      Step rules.headEq source reduct rules.computation) (.const name) := by
  intro accessible
  have noSelf : ∀ term : Tower.Tm 0,
      Acc (fun reduct source => Step rules.headEq source reduct rules.computation) term →
        ¬ Step rules.headEq term term rules.computation := by
    intro term witness
    induction witness with
    | intro term predecessors ih =>
        intro self
        exact ih term self self
  exact noSelf _ accessible loop_step

end CyclicDefinition

#print axioms qualification
#print axioms qualification_computed
#print axioms entries_ordered
#print axioms automatic_bodies_agree
#print axioms forward_transparent_reference_not_ordered
#print axioms forward_opaque_reference_ordered
#print axioms nested_forward_reference_not_ordered
#print axioms ordered_expansion_does_not_normalize_beta
#print axioms CyclicDefinition.ordered_qualifier_rejects_loop
#print axioms one_round_incomplete
#print axioms two_rounds_checked
#print axioms shadowed_body_ignored
#print axioms selected_recursive_body_rejected
#print axioms conversion_iff
#print axioms pi_boundary
#print axioms universes
#print axioms beta_preserves
#print axioms alias_conversion
#print axioms alias_formed
#print axioms value_at_alias
#print axioms value_at_ground
#print axioms identity_body_typed
#print axioms identity_constant_typed
#print axioms identity_delta_checked
#print axioms specialize_typed
#print axioms specialized_identity_run
#print axioms alias_not_pi
#print axioms collapse_has_no_qualification
#print axioms CyclicDefinition.qualification
#print axioms CyclicDefinition.loop_typed
#print axioms CyclicDefinition.loop_step
#print axioms CyclicDefinition.loop_not_accessible

end ConstantExpansion.Examples
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
