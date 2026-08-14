import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics

/-!
# Immutable ground-subterm caching for compiled plans

The admitted plan is immutable.  A structural term containing no variable
slot therefore has the same value under every substitution and may be
materialized once in the persistent program region.  This module proves that
the exact typed-plan semantics is unchanged and counts the constructors
removed from repeated dynamic materialization.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanGroundCacheCompilation

open CompiledPlanAdmission
open CompiledPlanTermSemantics

mutual

/-- Recognize and evaluate a substitution-independent plan term. -/
def groundTerm? : Term -> Option GroundTerm
  | .symbol name => some (.symbol name)
  | .variable _ => none
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .application head arguments => do
      let grounded <- groundTerms? arguments
      some (.application head grounded)

def groundTerms? : Terms -> Option GroundTerms
  | .nil => some .nil
  | .cons head tail => do
      let groundedHead <- groundTerm? head
      let groundedTail <- groundTerms? tail
      some (.cons groundedHead groundedTail)

end

mutual

/-- Groundness recognition computes the same value as arbitrary
instantiation. -/
theorem instantiateTerm_groundTerm?
    (term : Term) (grounded : GroundTerm) (substitution : Substitution)
    (recognized : groundTerm? term = some grounded) :
    instantiateTerm substitution term = some grounded := by
  cases term with
  | symbol name => simp [groundTerm?] at recognized; subst grounded; rfl
  | «variable» slot => simp [groundTerm?] at recognized
  | «string» value => simp [groundTerm?] at recognized; subst grounded; rfl
  | integer value => simp [groundTerm?] at recognized; subst grounded; rfl
  | application head arguments =>
      cases argumentsGround : groundTerms? arguments with
      | none => simp [groundTerm?, argumentsGround] at recognized
      | some groundedArguments =>
          simp [groundTerm?, argumentsGround] at recognized
          subst grounded
          simp only [instantiateTerm, Option.bind_eq_bind]
          rw [instantiateTerms_groundTerms? arguments groundedArguments
            substitution argumentsGround]
          rfl

theorem instantiateTerms_groundTerms?
    (terms : Terms) (grounded : GroundTerms) (substitution : Substitution)
    (recognized : groundTerms? terms = some grounded) :
    instantiateTerms substitution terms = some grounded := by
  cases terms with
  | nil => simp [groundTerms?] at recognized; subst grounded; rfl
  | cons head tail =>
      cases headGround : groundTerm? head with
      | none => simp [groundTerms?, headGround] at recognized
      | some groundedHead =>
          cases tailGround : groundTerms? tail with
          | none => simp [groundTerms?, headGround, tailGround] at recognized
          | some groundedTail =>
              simp [groundTerms?, headGround, tailGround] at recognized
              subst grounded
              simp only [instantiateTerms, Option.bind_eq_bind]
              rw [instantiateTerm_groundTerm? head groundedHead substitution
                  headGround,
                instantiateTerms_groundTerms? tail groundedTail substitution
                  tailGround]
              rfl

end

mutual

/-- Residual term after maximal ground subtrees become persistent values. -/
inductive CachedTerm where
  | variable (slot : UInt32)
  | ground (value : GroundTerm)
  | application (head : List UInt8) (arguments : CachedTerms)
  deriving DecidableEq, Repr

inductive CachedTerms where
  | nil
  | cons (head : CachedTerm) (tail : CachedTerms)
  deriving DecidableEq, Repr

end

mutual

def compileTerm : Term -> CachedTerm
  | .symbol name => .ground (.symbol name)
  | .variable slot => .variable slot
  | .string value => .ground (.string value)
  | .integer value => .ground (.integer value)
  | .application head arguments =>
      match groundTerms? arguments with
      | some grounded => .ground (.application head grounded)
      | none => .application head (compileTerms arguments)

def compileTerms : Terms -> CachedTerms
  | .nil => .nil
  | .cons head tail => .cons (compileTerm head) (compileTerms tail)

end

mutual

def executeTerm (substitution : Substitution) :
    CachedTerm -> Option GroundTerm
  | .variable slot => substitution slot
  | .ground value => some value
  | .application head arguments => do
      let grounded <- executeTerms substitution arguments
      some (.application head grounded)

def executeTerms (substitution : Substitution) :
    CachedTerms -> Option GroundTerms
  | .nil => some .nil
  | .cons head tail => do
      let groundedHead <- executeTerm substitution head
      let groundedTail <- executeTerms substitution tail
      some (.cons groundedHead groundedTail)

end

mutual

/-- Cached execution is exactly ordinary typed-plan instantiation. -/
theorem executeTerm_compileTerm (term : Term)
    (substitution : Substitution) :
    executeTerm substitution (compileTerm term) =
      instantiateTerm substitution term := by
  cases term with
  | symbol name => rfl
  | «variable» slot => rfl
  | «string» value => rfl
  | integer value => rfl
  | application head arguments =>
      cases argumentsGround : groundTerms? arguments with
      | none =>
          simp only [compileTerm, argumentsGround, executeTerm,
            instantiateTerm, Option.bind_eq_bind]
          rw [executeTerms_compileTerms arguments substitution]
      | some groundedArguments =>
          simp only [compileTerm, argumentsGround, executeTerm,
            instantiateTerm, Option.bind_eq_bind]
          rw [instantiateTerms_groundTerms? arguments groundedArguments
            substitution argumentsGround]
          rfl

theorem executeTerms_compileTerms (terms : Terms)
    (substitution : Substitution) :
    executeTerms substitution (compileTerms terms) =
      instantiateTerms substitution terms := by
  cases terms with
  | nil => rfl
  | cons head tail =>
      simp only [compileTerms, executeTerms, instantiateTerms,
        Option.bind_eq_bind]
      rw [executeTerm_compileTerm head substitution,
        executeTerms_compileTerms tail substitution]

end

/-! ## Dynamic-construction accounting -/

mutual

def sourceNodeCount : Term -> Nat
  | .symbol _ | .variable _ | .string _ | .integer _ => 1
  | .application _ arguments => 1 + sourceNodesCount arguments

def sourceNodesCount : Terms -> Nat
  | .nil => 0
  | .cons head tail => sourceNodeCount head + sourceNodesCount tail

end

mutual

def dynamicNodeCount : CachedTerm -> Nat
  | .variable _ => 1
  | .ground _ => 0
  | .application _ arguments => 1 + dynamicNodesCount arguments

def dynamicNodesCount : CachedTerms -> Nat
  | .nil => 0
  | .cons head tail => dynamicNodeCount head + dynamicNodesCount tail

end

mutual

theorem dynamicNodeCount_compile_le (term : Term) :
    dynamicNodeCount (compileTerm term) <= sourceNodeCount term := by
  cases term with
  | symbol name => simp [compileTerm, dynamicNodeCount, sourceNodeCount]
  | «variable» slot => simp [compileTerm, dynamicNodeCount, sourceNodeCount]
  | «string» value => simp [compileTerm, dynamicNodeCount, sourceNodeCount]
  | integer value => simp [compileTerm, dynamicNodeCount, sourceNodeCount]
  | application head arguments =>
      cases argumentsGround : groundTerms? arguments with
      | none =>
          simp only [compileTerm, argumentsGround, dynamicNodeCount,
            sourceNodeCount, Nat.add_le_add_iff_left]
          exact dynamicNodesCount_compile_le arguments
      | some groundedArguments =>
          simp [compileTerm, argumentsGround, dynamicNodeCount,
            sourceNodeCount]

theorem dynamicNodesCount_compile_le (terms : Terms) :
    dynamicNodesCount (compileTerms terms) <= sourceNodesCount terms := by
  cases terms with
  | nil => rfl
  | cons head tail =>
      simpa [compileTerms, dynamicNodesCount, sourceNodesCount] using
        Nat.add_le_add (dynamicNodeCount_compile_le head)
          (dynamicNodesCount_compile_le tail)

end

def sourceRuntimeCost (uses : Nat) (term : Term) : Nat :=
  uses * sourceNodeCount term

def cachedRuntimeCost (uses : Nat) (term : Term) : Nat :=
  uses * dynamicNodeCount (compileTerm term)

theorem cachedRuntimeCost_le_source (uses : Nat) (term : Term) :
    cachedRuntimeCost uses term <= sourceRuntimeCost uses term :=
  Nat.mul_le_mul_left uses (dynamicNodeCount_compile_le term)

theorem sourceNodeCount_positive (term : Term) :
    0 < sourceNodeCount term := by
  cases term <;> simp only [sourceNodeCount] <;> omega

theorem dynamicNodeCount_compile_eq_zero_of_ground
    (term : Term) (grounded : GroundTerm)
    (recognized : groundTerm? term = some grounded) :
    dynamicNodeCount (compileTerm term) = 0 := by
  cases term with
  | symbol name => simp [compileTerm, dynamicNodeCount]
  | «variable» slot => simp [groundTerm?] at recognized
  | «string» value => simp [compileTerm, dynamicNodeCount]
  | integer value => simp [compileTerm, dynamicNodeCount]
  | application head arguments =>
      cases argumentsGround : groundTerms? arguments with
      | none => simp [groundTerm?, argumentsGround] at recognized
      | some groundedArguments =>
          simp [compileTerm, argumentsGround, dynamicNodeCount]

/-- A repeatedly used fully ground body performs strictly less dynamic
construction work after the structural recognizer caches it. -/
theorem cachedRuntimeCost_lt_source_of_ground
    (uses : Nat) (positiveUses : 0 < uses)
    (term : Term) (grounded : GroundTerm)
    (recognized : groundTerm? term = some grounded) :
    cachedRuntimeCost uses term < sourceRuntimeCost uses term := by
  rw [cachedRuntimeCost, sourceRuntimeCost,
    dynamicNodeCount_compile_eq_zero_of_ground term grounded recognized]
  simp only [Nat.mul_zero]
  exact Nat.mul_pos positiveUses (sourceNodeCount_positive term)

/-- Ground caching as a composable realization of the exact plan-term
semantics. -/
def groundCacheRealization :
    Mettapedia.GSLT.SimpleRealization
      Term CachedTerm (Substitution -> Option GroundTerm) where
  compile := fun _ source => compileTerm source
  observeSource := fun _ source substitution =>
    instantiateTerm substitution source
  observeArtifact := fun _ artifact substitution =>
    executeTerm substitution artifact
  adequate := by
    intro _ source
    funext substitution
    exact executeTerm_compileTerm source substitution

/-! ## Independent witnesses and rejection boundary -/

private def parserShape : Term :=
  .application [1]
    (.cons (.string [2])
      (.cons (.variable 0)
        (.cons (.application [3] (.cons (.integer 4) .nil)) .nil)))

/-- A parser-like template caches both literals and a nested closed subtree. -/
example : compileTerm parserShape =
    .application [1]
      (.cons (.ground (.string [2]))
        (.cons (.variable 0)
          (.cons
            (.ground (.application [3] (.cons (.integer 4) .nil)))
            .nil))) := by
  rfl

private def proofShape : Term :=
  .application [10]
    (.cons (.variable 0)
      (.cons (.application [11] (.cons (.symbol [12]) .nil)) .nil))

/-- A proof-like template independently caches an immutable label subtree. -/
example : dynamicNodeCount (compileTerm proofShape) <
    sourceNodeCount proofShape := by
  decide

/-- A variable-bearing application remains a residual application. -/
example : compileTerm
    (.application [20] (.cons (.variable 0) .nil)) =
      .application [20] (.cons (.variable 0) .nil) := by
  rfl

end Mettapedia.GSLT.LanguageDef.CompiledPlanGroundCacheCompilation
