import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation

/-!
# Universe formation for cumulative replay interpretation

The actual cumulative head rules are interpreted by the existing internal
universe hierarchy. Ground typing requires its stated membership in the
bottom universe. Product and sum formation use maximum-level closure;
identity codes are small at every level. Cumulativity gives inclusion, not
equality of universe sets. These are the primitive/formation cases, not a
global conversion or whole-derivation soundness assumption.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseFormation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProducts (tracePiSet)
open ZFSetDependentProducts (sigmaSet)

universe u
variable {L : Type} [LevelOrder L]
variable (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → L)

theorem headTyping_membership {head level : LevelTower.Head L}
    (groundTyped : ground ∈ universeSet h seed (LevelOrder.bot : L)) (typed : LevelTower.HeadTyping head level) :
    interpretHead h seed ground valuation head ∈ interpretHead h seed ground valuation level := by
  cases typed with
  | legacyGround => exact groundTyped
  | sort level => exact universeSet_mem_succ h seed (level.eval valuation)

theorem cumulative_subset {lower upper : LevelTower.Head L} (below : LevelTower.Cumulative lower upper) :
    interpretHead h seed ground valuation lower ⊆ interpretHead h seed ground valuation upper := by
  cases lower <;> cases upper <;> simp only [LevelTower.Cumulative] at below
  exact universeSet_mono h seed (below valuation)

theorem headEq_values {left right : LevelTower.Head L} (equal : LevelTower.HeadEq left right) :
    interpretHead h seed ground valuation left = interpretHead h seed ground valuation right := by
  cases left <;> cases right <;> simp only [LevelTower.HeadEq] at equal
  · rfl
  · exact congrArg (universeSet h seed) (equal valuation)

variable {ConversionCode : Nat → Type} {n : Nat} (constants : DeclName → ZFSet.{u})

theorem pi_formation_membership (A : LevelTower.Tm L n) (B : LevelTower.Tm L (n + 1))
    (domainCode : Code (LevelTower.Head L) ConversionCode n) (bodyCode : Code (LevelTower.Head L) ConversionCode (n + 1))
    (domainLevel bodyLevel level : LevelTower.Head L) (domain result : Meaning.{u} n)
    (body : Meaning.{u} (n + 1))
    (joined : LevelTower.Join domainLevel bodyLevel level)
    (atDomain : assemble (interpretHead h seed ground valuation) constants domainCode A
      (.head domainLevel) = some domain)
    (atBody : assemble (interpretHead h seed ground valuation) constants bodyCode B
      (.head bodyLevel) = some body)
    (atResult : assemble (interpretHead h seed ground valuation) constants
      (.piForm domainLevel bodyLevel domainCode bodyCode) (.pi A B) (.head level) = some result)
    (env : Environment.{u} n)
    (domainTyped : domain.value env ∈ interpretHead h seed ground valuation domainLevel)
    (bodyTyped : ∀ x ∈ domain.value env,
      body.value (extend env x) ∈ interpretHead h seed ground valuation bodyLevel) :
    result.value env ∈ interpretHead h seed ground valuation level := by
  simp [assemble, atDomain, atBody] at atResult
  subst result
  cases joined with
  | sorts left right =>
    change tracePiSet (domain.value env) (fun x => body.value (extend env x)) ∈
      universeSet h seed (max (left.eval valuation) (right.eval valuation))
    exact (universeSet_closed h seed _).tracePiSet_mem
      (universeSet_mono h seed (le_max_left _ _) domainTyped) _
      (fun x inside => universeSet_mono h seed (le_max_right _ _) (bodyTyped x inside))

theorem sigma_formation_membership (A : LevelTower.Tm L n) (B : LevelTower.Tm L (n + 1))
    (domainCode : Code (LevelTower.Head L) ConversionCode n) (bodyCode : Code (LevelTower.Head L) ConversionCode (n + 1))
    (domainLevel bodyLevel level : LevelTower.Head L) (domain result : Meaning.{u} n)
    (body : Meaning.{u} (n + 1))
    (joined : LevelTower.Join domainLevel bodyLevel level)
    (atDomain : assemble (interpretHead h seed ground valuation) constants domainCode A
      (.head domainLevel) = some domain)
    (atBody : assemble (interpretHead h seed ground valuation) constants bodyCode B
      (.head bodyLevel) = some body)
    (atResult : assemble (interpretHead h seed ground valuation) constants
      (.sigmaForm domainLevel bodyLevel domainCode bodyCode) (.sigma A B) (.head level) = some result)
    (env : Environment.{u} n)
    (domainTyped : domain.value env ∈ interpretHead h seed ground valuation domainLevel)
    (bodyTyped : ∀ x ∈ domain.value env,
      body.value (extend env x) ∈ interpretHead h seed ground valuation bodyLevel) :
    result.value env ∈ interpretHead h seed ground valuation level := by
  simp [assemble, atDomain, atBody] at atResult
  subst result
  cases joined with
  | sorts left right =>
    change sigmaSet (domain.value env) (fun x => body.value (extend env x)) ∈
      universeSet h seed (max (left.eval valuation) (right.eval valuation))
    exact (universeSet_closed h seed _).sigmaSet_mem
      (universeSet_mono h seed (le_max_left _ _) domainTyped) _
      (fun x inside => universeSet_mono h seed (le_max_right _ _) (bodyTyped x inside))

theorem identity_formation_membership (A x y : LevelTower.Tm L n)
    (formation leftCode rightCode : Code (LevelTower.Head L) ConversionCode n) (level : LevelTower.Head L)
    (left right result : Meaning.{u} n) (isUniverse : LevelTower.IsUniverse level)
    (atLeft : assemble (interpretHead h seed ground valuation) constants leftCode x A = some left)
    (atRight : assemble (interpretHead h seed ground valuation) constants rightCode y A = some right)
    (atResult : assemble (interpretHead h seed ground valuation) constants
      (.idForm level formation leftCode rightCode) (.id A x y) (.head level) = some result)
    (env : Environment.{u} n) : result.value env ∈ interpretHead h seed ground valuation level := by
  simp [assemble, atLeft, atRight] at atResult
  subst result
  cases isUniverse with
  | sort level => exact ZFSetTraceUniverseInterpretation.truthCode_mem h seed _ _

theorem cumulative_membership (term : LevelTower.Tm L n) (sourceCode : Code (LevelTower.Head L) ConversionCode n)
    (lower upper : LevelTower.Head L) (source result : Meaning.{u} n) (below : LevelTower.Cumulative lower upper)
    (atSource : assemble (interpretHead h seed ground valuation) constants sourceCode term
      (.head lower) = some source)
    (atResult : assemble (interpretHead h seed ground valuation) constants (.cumul lower sourceCode) term
      (.head upper) = some result)
    (env : Environment.{u} n)
    (typed : source.value env ∈ interpretHead h seed ground valuation lower) :
    result.value env ∈ interpretHead h seed ground valuation upper := by
  change assemble _ constants sourceCode term (.head lower) = some result at atResult
  rw [atSource] at atResult
  cases Option.some.inj atResult
  exact cumulative_subset h seed ground valuation below typed

#print axioms headTyping_membership
#print axioms cumulative_subset
#print axioms headEq_values
#print axioms pi_formation_membership
#print axioms sigma_formation_membership
#print axioms identity_formation_membership
#print axioms cumulative_membership

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseFormation
