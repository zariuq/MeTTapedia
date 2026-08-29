import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationComputation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RussellTarskiBoundary

/-!
# Universe-level instantiation of declaration signatures

A level-polymorphic declaration is a schema, not one permanently fixed
calculus.  This module substitutes universe parameters through declaration
entries while requiring an explicit transport for the declaration's root
computation.  The resulting rule morphism transports ordinary typing proofs
to the instantiated signature.

The construction is generic in the declaration signature.  It neither grants
computation preservation nor assumes that level substitution is injective.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace Presentation
namespace Declaration

open RussellTarski

/-- Substitute universe parameters through a closed declaration entry. -/
def Entry.instantiateLevels (theta : Nat → LevelExpr)
    (entry : Entry Tower.Head) : Entry Tower.Head where
  type := substLevelsTm theta entry.type
  value? := entry.value?.map (substLevelsTm theta)

/-- Substitute universe parameters through all declaration entries.  Root
computation is supplied separately because its evidence may carry more
structure than endpoint syntax. -/
def Signature.instantiateLevels (theta : Nat → LevelExpr)
    (source : Signature Tower.Head)
    (computation : RootComputation Tower.Head) : Signature Tower.Head where
  entries := fun name =>
    (source.entries name).map (Entry.instantiateLevels theta)
  computation := computation

@[simp] theorem Signature.typeOf_instantiateLevels
    (theta : Nat → LevelExpr) (source : Signature Tower.Head)
    (computation : RootComputation Tower.Head) (name : DeclName) :
    (source.instantiateLevels theta computation).typeOf? name =
      (source.typeOf? name).map (substLevelsTm theta) := by
  unfold Signature.typeOf? Signature.instantiateLevels
    Entry.instantiateLevels
  cases lookup : source.entries name <;> simp [lookup]

@[simp] theorem Signature.valueOf_instantiateLevels
    (theta : Nat → LevelExpr) (source : Signature Tower.Head)
    (computation : RootComputation Tower.Head) (name : DeclName) :
    (source.instantiateLevels theta computation).valueOf? name =
      (source.valueOf? name).map (substLevelsTm theta) := by
  unfold Signature.valueOf? Signature.instantiateLevels
    Entry.instantiateLevels
  cases lookup : source.entries name with
  | none => simp [lookup]
  | some entry =>
      cases valueLookup : entry.value? <;> simp [lookup, valueLookup]

theorem Signature.typeOf_instantiateLevels_iff
    (theta : Nat → LevelExpr) (source : Signature Tower.Head)
    (computation : RootComputation Tower.Head) (name : DeclName)
    (targetType : Tower.Tm 0) :
    (source.instantiateLevels theta computation).typeOf? name =
        some targetType ↔
      ∃ sourceType,
        source.typeOf? name = some sourceType ∧
        substLevelsTm theta sourceType = targetType := by
  rw [Signature.typeOf_instantiateLevels]
  cases sourceLookup : source.typeOf? name with
  | none => simp
  | some sourceType => simp

theorem Signature.valueOf_instantiateLevels_iff
    (theta : Nat → LevelExpr) (source : Signature Tower.Head)
    (computation : RootComputation Tower.Head) (name : DeclName)
    (targetValue : Tower.Tm 0) :
    (source.instantiateLevels theta computation).valueOf? name =
        some targetValue ↔
      ∃ sourceValue,
        source.valueOf? name = some sourceValue ∧
        substLevelsTm theta sourceValue = targetValue := by
  rw [Signature.valueOf_instantiateLevels]
  cases sourceLookup : source.valueOf? name with
  | none => simp
  | some sourceValue => simp

/-- Data required to instantiate a declaration schema.  Endpoint support is
not reconstructed from a proposition: the caller supplies the exact map from
source root steps to steps of the instantiated computation. -/
structure LevelInstance (source : Signature Tower.Head)
    (theta : Nat → LevelExpr) where
  computation : RootComputation Tower.Head
  computationMap : ∀ {n : Nat} {left right : Tower.Tm n},
    source.computation.step left right →
      computation.step (substLevelsTm theta left)
        (substLevelsTm theta right)

namespace LevelInstance

variable {source : Signature Tower.Head} {theta : Nat → LevelExpr}

/-- The instantiated declaration signature. -/
def signature (instantiation : LevelInstance source theta) :
    Signature Tower.Head :=
  source.instantiateLevels theta instantiation.computation

/-- The rules obtained by installing the instantiated declarations in the
ordinary cumulative tower. -/
def rules (instantiation : LevelInstance source theta) : Rules Tower.Head :=
  extendRules Tower.rules instantiation.signature

/-- Level instantiation transports the complete declaration-aware typing
spine.  It does not claim a converse because a level substitution may
intentionally identify distinct parameters. -/
def morphism (instantiation : LevelInstance source theta) :
    (extendRules Tower.rules source).Morphism instantiation.rules
      (substLevelsHead theta) where
  headTyping := (levelSubstMorphism theta).headTyping
  isUniverse := (levelSubstMorphism theta).isUniverse
  join := (levelSubstMorphism theta).join
  cumulative := (levelSubstMorphism theta).cumulative
  headEq := (levelSubstMorphism theta).headEq
  constantType := by
    intro name type typing
    change combinedType Tower.rules source name = some type at typing
    change combinedType Tower.rules instantiation.signature name =
      some (substLevelsTm theta type)
    simp only [combinedType]
    change (match Tower.rules.constantType name with
      | some inherited => some inherited
      | none => source.typeOf? name) = some type at typing
    change (match Tower.rules.constantType name with
      | some inherited => some inherited
      | none => instantiation.signature.typeOf? name) =
        some (substLevelsTm theta type)
    simp [Tower.rules] at typing ⊢
    simpa [signature] using congrArg
      (Option.map (substLevelsTm theta)) typing
  computation := by
    intro n left right step
    change RootStep Tower.rules source n left right at step
    change RootStep Tower.rules instantiation.signature n
      (substLevelsTm theta left) (substLevelsTm theta right)
    cases step with
    | inherited inherited => exact inherited.elim
    | @delta name value unfolding =>
        have targetUnfolding :
            instantiation.signature.valueOf? name =
              some (substLevelsTm theta value) := by
          simpa [signature] using congrArg
            (Option.map (substLevelsTm theta)) unfolding
        simpa [substLevelsTm, Tm.mapHead] using
          (RootStep.delta (n := n) targetUnfolding)
    | declared declared =>
        exact RootStep.declared (instantiation.computationMap declared)

/-- Direct transport of a declaration-aware typing derivation. -/
theorem hasType (instantiation : LevelInstance source theta)
    {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : HasType (extendRules Tower.rules source) context term type) :
    HasType instantiation.rules
      (substLevelsCtx theta context)
      (substLevelsTm theta term) (substLevelsTm theta type) := by
  simpa [substLevelsCtx, substLevelsTm] using
    typing.mapHead instantiation.morphism

private theorem substLevelsTm_eq_const
    (theta : Nat → LevelExpr) {term : Tower.Tm n} {name : DeclName}
    (equality : substLevelsTm theta term = .const name) :
    term = .const name := by
  cases term <;> simp [substLevelsTm, Tm.mapHead] at equality ⊢
  assumption

/-- Formation and freshness survive level instantiation.  Computation
preservation remains deliberately separate, just as it is for the source
signature. -/
def formed (instantiation : LevelInstance source theta)
    (sourceFormed : source.Formed Tower.rules) :
    instantiation.signature.Formed Tower.rules where
  fresh := by
    intro name entry _lookup
    rfl
  types := by
    intro name targetType targetLookup
    rcases (Signature.typeOf_instantiateLevels_iff theta source
      instantiation.computation name targetType).mp targetLookup with
      ⟨sourceType, sourceLookup, rfl⟩
    rcases sourceFormed.types sourceLookup with
      ⟨level, levelIsUniverse, sourceTyping⟩
    refine ⟨substLevelsHead theta level,
      (levelSubstMorphism theta).isUniverse levelIsUniverse, ?_⟩
    change HasType instantiation.rules (.nil : Tower.Ctx 0)
      (substLevelsTm theta sourceType)
      (.head (substLevelsHead theta level))
    simpa [substLevelsCtx, Ctx.mapHead, substLevelsTm, Tm.mapHead] using
      instantiation.hasType sourceTyping
  values := by
    intro name targetType targetValue targetTypeLookup targetValueLookup
    rcases (Signature.typeOf_instantiateLevels_iff theta source
      instantiation.computation name targetType).mp targetTypeLookup with
      ⟨sourceType, sourceTypeLookup, rfl⟩
    rcases (Signature.valueOf_instantiateLevels_iff theta source
      instantiation.computation name targetValue).mp targetValueLookup with
      ⟨sourceValue, sourceValueLookup, rfl⟩
    change HasType instantiation.rules (.nil : Tower.Ctx 0)
      (substLevelsTm theta sourceValue)
      (substLevelsTm theta sourceType)
    simpa [substLevelsCtx, Ctx.mapHead] using instantiation.hasType
      (sourceFormed.values sourceTypeLookup sourceValueLookup)
  noSelfDelta := by
    intro name targetValue targetLookup targetEquality
    rcases (Signature.valueOf_instantiateLevels_iff theta source
      instantiation.computation name targetValue).mp targetLookup with
      ⟨sourceValue, sourceLookup, sourceMaps⟩
    apply sourceFormed.noSelfDelta sourceLookup
    apply substLevelsTm_eq_const theta
    exact sourceMaps.trans targetEquality

end LevelInstance

/-! ## Positive and negative controls -/

/-- Identity level substitution leaves declaration type lookup unchanged. -/
theorem Signature.typeOf_instantiateLevels_param
    (source : Signature Tower.Head) (computation : RootComputation Tower.Head)
    (name : DeclName) :
    (source.instantiateLevels LevelExpr.param computation).typeOf? name =
      source.typeOf? name := by
  rw [Signature.typeOf_instantiateLevels]
  cases source.typeOf? name <;> simp

/-- Level instantiation need not be injective: choosing one level for every
parameter intentionally identifies two distinct schematic universe heads. -/
theorem constantLevelInstantiation_collapses_parameters
    (level : LevelExpr) :
    substLevelsTm (fun _ => level)
        (sortTm (.param 0) : Tower.Tm 0) =
      substLevelsTm (fun _ => level) (sortTm (.param 1)) := by
  rfl

theorem schematic_parameter_sorts_distinct :
    (sortTm (.param 0) : Tower.Tm 0) ≠ sortTm (.param 1) := by
  decide

/-! ## Axiom audit -/

#print axioms LevelInstance.morphism
#print axioms LevelInstance.hasType
#print axioms LevelInstance.formed
#print axioms constantLevelInstantiation_collapses_parameters
#print axioms schematic_parameter_sorts_distinct

end Declaration
end Presentation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
