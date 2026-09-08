import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DefinitionalExpansion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDelta
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRestrictionExamples

/-!
# A nonempty transparent signature and its conversion boundary

The package contains a ground alias, a second alias referencing the first,
an opaque value at the second alias, and the previously formed polymorphic
identity definition. It uses the existing declaration-signature machinery,
not a separate evaluator. Fully expanded bodies discharge both local
qualification clauses, including the transitive alias dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ConstantExpansion.Examples

open Declaration FormationSensitive
open FormationSensitive.Dependencies.Examples (aliasName valueName extraName ground extraBody)

variable {n : Nat}

def secondAliasName : DeclName := `ExpansionExample.SecondAlias

def signature : Signature Tower.Head := Signature.ofList
  [ (aliasName, ⟨sortTm Tower.zero, some ground⟩),
    (secondAliasName, ⟨sortTm Tower.zero, some (.const aliasName)⟩),
    (valueName, ⟨.const secondAliasName, none⟩),
    (extraName, ⟨FormationSensitive.Examples.polymorphicIdentityType Tower.zero,
      some extraBody⟩) ]

def rules : Rules Tower.Head := extendRules Tower.rules signature

def bodies : Bodies Tower.Head := fun name =>
  if name = aliasName then ground
  else if name = secondAliasName then ground
  else if name = extraName then extraBody
  else .const name

private theorem alias_lookup : signature.valueOf? aliasName = some ground := by
  simp [signature, Signature.ofList, Signature.insert, Signature.empty,
    Signature.valueOf?, aliasName, secondAliasName, valueName, extraName]

private theorem second_lookup : signature.valueOf? secondAliasName = some (.const aliasName) := by
  simp [signature, Signature.ofList, Signature.insert, Signature.empty,
    Signature.valueOf?, aliasName, secondAliasName, valueName, extraName]

private theorem identity_lookup : signature.valueOf? extraName = some extraBody := by
  simp [signature, Signature.ofList, Signature.insert, Signature.empty,
    Signature.valueOf?, aliasName, secondAliasName, valueName, extraName]

private theorem constants (name : DeclName) :
    Conv Tower.HeadEq (.const name) (bodies name) rules.computation := by
  by_cases first : name = aliasName
  · subst name
    simpa only [bodies, if_pos rfl, liftClosed, ground, rename] using
      (Relation.EqvGen.rel _ _ (Step.root
        (RootStep.delta (base := Tower.rules) (n := 0) alias_lookup)))
  by_cases second : name = secondAliasName
  · subst name
    have toFirst : Conv rules.headEq (.const secondAliasName : Tower.Tm 0)
        (.const aliasName) rules.computation := .rel _ _ (.root (.delta second_lookup))
    have toGround : Conv rules.headEq (.const aliasName : Tower.Tm 0)
        ground rules.computation := .rel _ _ (.root (.delta alias_lookup))
    change Conv rules.headEq (.const secondAliasName) ground rules.computation
    exact .trans _ _ _ toFirst toGround
  by_cases identity : name = extraName
  · subst name
    simpa only [bodies, if_neg first, if_neg second, if_pos rfl,
      liftClosed, extraBody, rename, liftRen, Fin.cases_zero] using
      (Relation.EqvGen.rel _ _ (Step.root
        (RootStep.delta (base := Tower.rules) (n := 0) identity_lookup)))
  · simp only [bodies, if_neg first, if_neg second, if_neg identity]
    exact .refl _

private theorem definitions (name : DeclName) (value : Tower.Tm 0)
    (lookup : signature.valueOf? name = some value) :
    Conv Tower.HeadEq (bodies name) (expand bodies value) := by
  simp only [signature, Signature.ofList, List.foldr, Signature.insert,
    Signature.empty, Signature.valueOf?] at lookup
  split at lookup
  · next same =>
      subst name
      cases lookup
      simp only [bodies, expand, ground]
      exact .refl _
  · next first =>
      split at lookup
      · next same =>
          subst name
          cases lookup
          simp [bodies, secondAliasName, aliasName, expand, ground, liftClosed, rename]
          exact .refl _
      · next second =>
          split at lookup
          · simp at lookup
          · split at lookup
            · next same =>
                subst name
                cases lookup
                simp only [bodies, if_neg first, if_neg second,
                  extraBody, expand]
                exact .refl _
            · simp at lookup

/-- Both primitive obligations are proved for the authored nonempty package. -/
def qualification : Qualification rules :=
  Qualification.ofSignature Tower.rules signature rfl bodies constants definitions
    (by intro k left right impossible; exact impossible.elim)

/-- Conversion of arbitrary open terms is exactly pure conversion after
the certified transitive expansion; no bounded corpus stands in for this law. -/
theorem conversion_iff (left right : Tower.Tm n) :
    Conv rules.headEq left right rules.computation ↔
      Conv Tower.HeadEq (expand bodies left) (expand bodies right) :=
  qualification.conversion_iff left right

theorem pi_boundary : PiConversionBoundary rules :=
  qualification.piConversionBoundary Tower.headEq_symmetric

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
  qualification.betaPi Tower.headEq_symmetric universes judgment

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
  exact .const known (.headType (Tower.HeadTyping.sort Tower.zero))
    (Tower.IsUniverse.sort _)

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
  no_qualification_of_pi_head Tower.headEq_symmetric
    (Relation.EqvGen.symm _ _
      (FormationSensitive.Examples.ConversionCollapse.ground_converts_endomorphism (n := 0)))

namespace CyclicDefinition

def name : DeclName := `ExpansionExample.loop

/-- This intentionally cyclic signature is only a negative control. -/
def signature : Signature Tower.Head :=
  Signature.ofList [(name, ⟨ground, some (.const name)⟩)]

def rules : Rules Tower.Head := extendRules Tower.rules signature

/-- A self-loop preserves conversion classes, despite not terminating. -/
def qualification : Qualification rules :=
  Qualification.ofSignature Tower.rules signature rfl (fun c => .const c)
    (fun _ => .refl _)
    (by
      intro c value lookup
      by_cases same : c = name
      · subst c
        have valueEq : value = .const name := by
          simpa [signature, Signature.ofList, Signature.valueOf?, Signature.insert,
            Signature.empty] using lookup.symm
        subst value
        exact .refl _
      · simp [signature, Signature.ofList, Signature.valueOf?, Signature.insert,
          Signature.empty, same] at lookup)
    (by intro k left right impossible; exact impossible.elim)

theorem loop_typed : Judgment rules (.nil : Tower.Ctx 0) (.const name) ground := by
  have known : rules.constantType name = some ground := by decide
  exact ⟨.nil, .const known (.headType Tower.HeadTyping.legacyGround) (.sort _)⟩

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
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
