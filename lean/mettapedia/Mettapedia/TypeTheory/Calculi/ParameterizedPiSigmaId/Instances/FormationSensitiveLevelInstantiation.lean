import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveHeadMap
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.DeclarationLevelInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity

/-!
# Formation-sensitive transport across level-instantiated declarations

A rule morphism transports the retained formation premises as well as raw
typing. Level instantiation therefore changes the context and the declaration
environment explicitly. Its square with ordinary capture-avoiding substitution
uses the existing head-map/substitution law.

Extending a morphism by another signature requires exact base lookup transport:
otherwise a new target-base entry could shadow an instantiated extension entry.
No formation, computation-preservation, or same-signature polymorphism principle
is postulated here.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation


namespace Declaration.LevelInstance

open RussellTarski

variable {theta : Nat → LevelExpr} {signature : Signature Tower.Head} {n m : Nat}

theorem refinedTyping (instantiation : LevelInstance signature theta)
    {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : FormationSensitive.Typing (extendRules Tower.rules signature) context term type) :
    FormationSensitive.Typing instantiation.rules (substLevelsCtx theta context)
      (substLevelsTm theta term) (substLevelsTm theta type) :=
  typed.mapHead instantiation.morphism

theorem refinedContext (instantiation : LevelInstance signature theta)
    {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation (extendRules Tower.rules signature) context) :
    FormationSensitive.ContextFormation instantiation.rules (substLevelsCtx theta context) :=
  formed.mapHead instantiation.morphism

theorem refinedJudgment (instantiation : LevelInstance signature theta)
    {context : Tower.Ctx n} {term type : Tower.Tm n}
    (judgment : FormationSensitive.Judgment (extendRules Tower.rules signature) context term type) :
    FormationSensitive.Judgment instantiation.rules (substLevelsCtx theta context)
      (substLevelsTm theta term) (substLevelsTm theta type) :=
  judgment.mapHead instantiation.morphism

theorem refinedSubstitution (instantiation : LevelInstance signature theta)
    {context : Tower.Ctx n} {replacement : Tower.Ctx m}
    {substitution : Sub Tower.Head n m}
    (typed : FormationSensitive.CtxMor (extendRules Tower.rules signature)
      context replacement substitution) :
    FormationSensitive.CtxMor instantiation.rules (substLevelsCtx theta context)
      (substLevelsCtx theta replacement) (fun index => substLevelsTm theta (substitution index)) :=
  typed.mapHead instantiation.morphism

/-- Exact lookup transport prevents a new target-base declaration from
shadowing the newly instantiated extension. Computation is mapped separately
by the supplied, already defined level instance. -/
theorem extendMorphism {source target : Rules Tower.Head}
    (base : source.Morphism target (substLevelsHead theta))
    (baseLookup : ∀ name, target.constantType name =
      (source.constantType name).map (substLevelsTm theta))
    (instantiation : LevelInstance signature theta) :
    (extendRules source signature).Morphism (extendRules target instantiation.signature)
      (substLevelsHead theta) where
  headTyping := base.headTyping
  isUniverse := base.isUniverse
  join := base.join
  cumulative := base.cumulative
  headEq := base.headEq
  constantType := by
    intro name type known
    change combinedType source signature name = some type at known
    change combinedType target instantiation.signature name = some (substLevelsTm theta type)
    unfold combinedType at known ⊢
    rw [baseLookup]
    cases sourceKnown : source.constantType name with
    | none =>
        simp only [sourceKnown, Option.map_none] at known ⊢
        rw [LevelInstance.signature, Signature.typeOf_instantiateLevels, known]
        rfl
    | some sourceType =>
        simp only [sourceKnown, Option.some.injEq] at known
        simp only [Option.map_some]
        exact congrArg some (congrArg (substLevelsTm theta) known)
  computation := by
    intro k left right root
    cases root with
    | inherited prior => exact .inherited (base.computation prior)
    | @delta name value known =>
        change RootStep target instantiation.signature k _ _
        simp only [Tm.mapHead, Tm.mapHead_liftClosed]
        apply RootStep.delta
        change instantiation.signature.valueOf? name = some (substLevelsTm theta value)
        rw [LevelInstance.signature, Signature.valueOf_instantiateLevels, known]
        rfl
    | declared prior => exact .declared (instantiation.computationMap prior)

end Declaration.LevelInstance
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
