import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRestriction
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveExamples

/-!
# Restriction retains hidden declaration and conversion dependencies

The displayed judgment is a constant at the ordinary ground type. Its proof
nevertheless needs formation of an intermediate named type and an equation
unfolding that type. A finite retained manifest removes an unused polymorphic
declaration and its computation while preserving the full refined judgment.
Deleting only the hidden type declaration keeps the displayed constant lookup
and a raw proof, but destroys every refined typing of that constant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.Dependencies.Examples

variable {n : Nat}

def aliasName : DeclName := `RestrictionExample.GroundAlias
def valueName : DeclName := `RestrictionExample.value
def extraName : DeclName := `RestrictionExample.polymorphicIdentity

def ground : Tower.Tm n := .head .legacyGround
def extraBody : Tower.Tm n := .lam (.lam (.var 0))

inductive Equations : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | typeAlias {n : Nat} : Equations (.const aliasName : Tower.Tm n) ground
  | extra {n : Nat} : Equations (.const extraName : Tower.Tm n) extraBody

def computation : RootComputation Tower.Head where
  step := Equations
  rename := by
    intro n m rho left right step
    cases step <;> constructor
  substitute := by
    intro n m sigma left right step
    cases step <;> constructor

def source : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = aliasName then some (sortTm Tower.zero)
      else if name = valueName then some (.const aliasName)
      else if name = extraName then
        some (FormationSensitive.Examples.polymorphicIdentityType Tower.zero)
      else none
    computation := computation }

/-- The manifest names exact declaration types and the actually used root
equation. No request mentions the unused polymorphic identity. -/
def manifest : List (Requirement Tower.Head) :=
  [ .constantType aliasName (sortTm Tower.zero),
    .headTyping (.sort Tower.zero) (.sort (.succ Tower.zero)),
    .isUniverse (.sort (.succ Tower.zero)),
    .isUniverse (.sort Tower.zero),
    .constantType valueName (.const aliasName),
    .headTyping .legacyGround (.sort Tower.zero),
    .rootStep 0 (.const aliasName) ground ]

theorem manifest_valid : HoldsAll source manifest := by
  simp only [manifest, holdsAll_cons, holdsAll_nil, and_true, Requirement.Holds]
  exact ⟨rfl, .sort _, .sort _, .sort _, rfl, .legacyGround, .typeAlias⟩

/-- Primitive requirements reconstruct a real refined derivation, including
the declaration-type derivation hidden behind the displayed ground type. -/
theorem replay_manifest {target : Rules Tower.Head} (valid : HoldsAll target manifest) :
    Judgment target (.nil : Tower.Ctx 0) (.const valueName) ground := by
  simp only [manifest, holdsAll_cons, holdsAll_nil, and_true, Requirement.Holds] at valid
  obtain ⟨aliasLookup, sortTyping, sortUniverse, zeroUniverse, valueLookup,
    groundTyping, aliasEquation⟩ := valid
  have aliasFormed : Typing target (.nil : Tower.Ctx 0) (.const aliasName)
      (sortTm Tower.zero) :=
    .const aliasLookup (.headType sortTyping) sortUniverse
  have valueTyped : Typing target (.nil : Tower.Ctx 0) (.const valueName)
      (.const aliasName) := .const valueLookup aliasFormed zeroUniverse
  exact ⟨.nil, .conv valueTyped (.headType groundTyping) zeroUniverse
    (.rel _ _ (.root aliasEquation))⟩

theorem source_judgment : Judgment source (.nil : Tower.Ctx 0) (.const valueName) ground :=
  replay_manifest manifest_valid

def selected : Rules Tower.Head := restrict source manifest

theorem restricted_judgment :
    Judgment selected (.nil : Tower.Ctx 0) (.const valueName) ground :=
  replay_manifest (restrict_satisfies manifest_valid)

theorem unused_declaration_removed :
    source.constantType extraName =
      some (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) ∧
      selected.constantType extraName = none := by
  simp [source, selected, restrict, constantNames, manifest, extraName, aliasName, valueName]

private theorem baseRequirements_preserved (requirement : Requirement Tower.Head)
    (valid : requirement.Holds Tower.rules) : requirement.Holds source := by
  cases requirement with
  | constantType name type => cases valid
  | rootStep n left right => exact valid.elim
  | _ => exact valid

/-- The discarded feature has a real dependent type and an admitted body;
it is not malformed data inserted solely to make the table larger. -/
theorem unused_polymorphic_feature_admitted :
    Judgment source (.nil : Tower.Ctx 0) (.const extraName)
      (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) ∧
    Judgment source (.nil : Tower.Ctx 0) extraBody
      (FormationSensitive.Examples.polymorphicIdentityType Tower.zero) := by
  have formed := typing_transfer baseRequirements_preserved
    (FormationSensitive.Examples.polymorphicIdentityType_formed .nil Tower.zero)
  have body := typing_transfer baseRequirements_preserved
    (FormationSensitive.Examples.polymorphicIdentity_typed .nil Tower.zero)
  exact ⟨⟨.nil, .const unused_declaration_removed.1 formed (.sort _)⟩, ⟨.nil, body⟩⟩

private theorem retained_shape {left right : Tower.Tm n}
    (step : RetainedRoot manifest left right) :
    left = .const aliasName ∧ right = ground := by
  induction step with
  | seed member =>
      simp only [manifest, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member | member | member | member | member | member
      all_goals cases member
      exact ⟨rfl, rfl⟩
  | rename rho _ ih =>
      rcases ih with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | substitute sigma _ ih =>
      rcases ih with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/-- The restriction removes a real unused computation rule as well as its
declaration; it is not just a different manifest over an unchanged package. -/
theorem unused_computation_removed :
    source.computation.step (.const extraName : Tower.Tm 0) extraBody ∧
      ¬ selected.computation.step (.const extraName : Tower.Tm 0) extraBody := by
  refine ⟨.extra, ?_⟩
  intro retained
  have impossible := (retained_shape retained).1
  have distinct : (Tm.const extraName : Tower.Tm 0) ≠ .const aliasName := by decide
  exact distinct impossible

/-- Only the hidden declaration request is deleted. The visible value's
lookup, universe policy, and its used conversion equation are retained. -/
def shallow : Rules Tower.Head := restrict source manifest.tail

theorem shallow_lookups :
    shallow.constantType valueName = source.constantType valueName ∧
      shallow.constantType aliasName = none := by
  simp [shallow, restrict, constantNames, manifest, aliasName, valueName]

theorem raw_shallow_accepts_surface :
    HasType shallow (.nil : Tower.Ctx 0) (.const valueName) ground := by
  have lookup : shallow.constantType valueName = some (.const aliasName) := by
    rw [shallow_lookups.1]
    rfl
  have raw : HasType shallow (.nil : Tower.Ctx 0) (.const valueName)
      (.const aliasName) := .const lookup
  exact .conv raw (.rel _ _ (.root (RetainedRoot.seed (by simp [manifest]))))

/-- No alternate conversion or cumulative tail repairs the missing recursive
formation dependency, even though the displayed constant lookup agrees. -/
theorem shallow_rejects_refined {Γ : Tower.Ctx n} {type : Tower.Tm n} :
    ¬ Typing shallow Γ (.const valueName) type := by
  intro typing
  obtain ⟨declaredType, u, lookup, formed, _⟩ := typing.constFormation
  have same : declaredType = .const aliasName := by
    rw [shallow_lookups.1] at lookup
    change some (.const aliasName) = some declaredType at lookup
    exact Option.some.inj lookup.symm
  subst declaredType
  obtain ⟨_, _, aliasLookup, _, _⟩ := formed.constFormation
  rw [shallow_lookups.2] at aliasLookup
  cases aliasLookup

/-- The retained package has both real removal and whole-judgment reflection. -/
theorem restriction_with_no_invention :
    Judgment selected (.nil : Tower.Ctx 0) (.const valueName) ground ∧
      ∀ {m : Nat} {Γ : Tower.Ctx m} {term type : Tower.Tm m},
        Judgment selected Γ term type → Judgment source Γ term type :=
  ⟨restricted_judgment, fun judgment => restrict_judgment_reflects manifest_valid judgment⟩

#print axioms manifest_valid
#print axioms replay_manifest
#print axioms source_judgment
#print axioms restricted_judgment
#print axioms unused_declaration_removed
#print axioms unused_polymorphic_feature_admitted
#print axioms unused_computation_removed
#print axioms shallow_lookups
#print axioms raw_shallow_accepts_surface
#print axioms shallow_rejects_refined
#print axioms restriction_with_no_invention

end FormationSensitive.Dependencies.Examples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
