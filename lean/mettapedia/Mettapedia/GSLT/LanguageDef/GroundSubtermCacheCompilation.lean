import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Parsing.HornCertificate

/-!
# Certified caching of immutable ground subterms

A generated rule plan is immutable after admission. Any plan node with no
variable descendants therefore denotes the same value under every execution
environment. This module compiles maximal ground subtrees to cached values and
leaves only variable-bearing structure for dynamic materialization.

The recognizer is structural and language-neutral. Source execution rebuilds
the complete term under a substitution; compiled execution returns cached
ground values directly and recursively builds only the remaining structure.
The refinement theorem proves exact value equality, while the cost theorem
counts the dynamic constructors eliminated by the cache.
-/

namespace Mettapedia.GSLT.LanguageDef.GroundSubtermCacheCompilation

open Mettapedia.GSLT.Parsing.HornCertificate

mutual
  /-- Decide whether a source term is independent of every substitution. -/
  def groundTerm? : Term -> Option GroundTerm
    | .var _ => none
    | .atom name => some (.atom name)
    | .integer value => some (.integer value)
    | .app constructor arguments => do
        let grounded <- groundTerms? arguments
        pure (.app constructor grounded)

  def groundTerms? : Terms -> Option GroundTerms
    | .nil => some .nil
    | .cons head tail => do
        let groundedHead <- groundTerm? head
        let groundedTail <- groundTerms? tail
        pure (.cons groundedHead groundedTail)
end

mutual
  /-- Structural groundness implies environment-independent instantiation. -/
  theorem instantiateTerm_groundTerm?
      (term : Term) (grounded : GroundTerm)
      (substitution : Substitution)
      (recognized : groundTerm? term = some grounded) :
      instantiateTerm substitution term = some grounded := by
    cases term with
    | var identifier => simp [groundTerm?] at recognized
    | atom name =>
        simp [groundTerm?] at recognized
        subst grounded
        rfl
    | integer value =>
        simp [groundTerm?] at recognized
        subst grounded
        rfl
    | app constructor arguments =>
        cases argumentsEq : groundTerms? arguments with
        | none => simp [groundTerm?, argumentsEq] at recognized
        | some groundedArguments =>
            simp [groundTerm?, argumentsEq] at recognized
            subst grounded
            simp only [instantiateTerm, Option.bind_eq_bind]
            rw [instantiateTerms_groundTerms? arguments groundedArguments
              substitution argumentsEq]
            rfl

  theorem instantiateTerms_groundTerms?
      (terms : Terms) (grounded : GroundTerms)
      (substitution : Substitution)
      (recognized : groundTerms? terms = some grounded) :
      instantiateTerms substitution terms = some grounded := by
    cases terms with
    | nil =>
        simp [groundTerms?] at recognized
        subst grounded
        rfl
    | cons head tail =>
        cases headEq : groundTerm? head with
        | none => simp [groundTerms?, headEq] at recognized
        | some groundedHead =>
            cases tailEq : groundTerms? tail with
            | none => simp [groundTerms?, headEq, tailEq] at recognized
            | some groundedTail =>
                simp [groundTerms?, headEq, tailEq] at recognized
                subst grounded
                simp only [instantiateTerms, Option.bind_eq_bind]
                rw [instantiateTerm_groundTerm? head groundedHead substitution
                    headEq,
                  instantiateTerms_groundTerms? tail groundedTail substitution
                    tailEq]
                rfl
end

mutual
  /-- A generated term plan with maximal ground subtrees cached by value. -/
  inductive CachedTerm where
    | variable (identifier : Nat)
    | ground (value : GroundTerm)
    | app (constructor : String) (arguments : CachedTerms)
    deriving DecidableEq, Repr

  inductive CachedTerms where
    | nil
    | cons (head : CachedTerm) (tail : CachedTerms)
    deriving DecidableEq, Repr
end

def CachedTerms.ofList : List CachedTerm -> CachedTerms
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

mutual
  /-- Cache every maximal ground subtree discovered by the recognizer. -/
  def compileTerm : Term -> CachedTerm
    | .var identifier => .variable identifier
    | .atom name => .ground (.atom name)
    | .integer value => .ground (.integer value)
    | .app constructor arguments =>
        match groundTerms? arguments with
        | some grounded => .ground (.app constructor grounded)
        | none => .app constructor (compileTerms arguments)

  def compileTerms : Terms -> CachedTerms
    | .nil => .nil
    | .cons head tail => .cons (compileTerm head) (compileTerms tail)
end

mutual
  /-- Execute a cached plan. Cached values bypass dynamic construction. -/
  def executeTerm (substitution : Substitution) :
      CachedTerm -> Option GroundTerm
    | .variable identifier => instantiateTerm substitution (.var identifier)
    | .ground value => some value
    | .app constructor arguments => do
        let grounded <- executeTerms substitution arguments
        pure (.app constructor grounded)

  def executeTerms (substitution : Substitution) :
      CachedTerms -> Option GroundTerms
    | .nil => some .nil
    | .cons head tail => do
        let groundedHead <- executeTerm substitution head
        let groundedTail <- executeTerms substitution tail
        pure (.cons groundedHead groundedTail)
end

mutual
  /-- Compiled execution is exactly source instantiation. -/
  theorem executeTerm_compileTerm
      (term : Term) (substitution : Substitution) :
      executeTerm substitution (compileTerm term) =
        instantiateTerm substitution term := by
    cases term with
    | var identifier => rfl
    | atom name => rfl
    | integer value => rfl
    | app constructor arguments =>
        cases argumentsEq : groundTerms? arguments with
        | none =>
            simp only [compileTerm, argumentsEq, executeTerm,
              instantiateTerm, Option.bind_eq_bind]
            rw [executeTerms_compileTerms arguments substitution]
        | some groundedArguments =>
            simp only [compileTerm, argumentsEq, executeTerm,
              instantiateTerm, Option.bind_eq_bind]
            rw [instantiateTerms_groundTerms? arguments groundedArguments
              substitution argumentsEq]
            rfl

  theorem executeTerms_compileTerms
      (terms : Terms) (substitution : Substitution) :
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

/-! ## Dynamic construction cost -/

mutual
  /-- Number of value nodes rebuilt by source instantiation. -/
  def sourceNodeCount : Term -> Nat
    | .var _ => 1
    | .atom _ => 1
    | .integer _ => 1
    | .app _ arguments => 1 + sourceNodesCount arguments

  def sourceNodesCount : Terms -> Nat
    | .nil => 0
    | .cons head tail => sourceNodeCount head + sourceNodesCount tail
end

mutual
  /-- Number of value nodes still built dynamically after caching. -/
  def dynamicNodeCount : CachedTerm -> Nat
    | .variable _ => 1
    | .ground _ => 0
    | .app _ arguments => 1 + dynamicNodesCount arguments

  def dynamicNodesCount : CachedTerms -> Nat
    | .nil => 0
    | .cons head tail => dynamicNodeCount head + dynamicNodesCount tail
end

mutual
  /-- Caching never increases dynamic constructor work. -/
  theorem dynamicNodeCount_compile_le (term : Term) :
      dynamicNodeCount (compileTerm term) <= sourceNodeCount term := by
    cases term with
    | var identifier => simp [compileTerm, dynamicNodeCount, sourceNodeCount]
    | atom name => simp [compileTerm, dynamicNodeCount, sourceNodeCount]
    | integer value => simp [compileTerm, dynamicNodeCount, sourceNodeCount]
    | app constructor arguments =>
        cases argumentsEq : groundTerms? arguments with
        | none =>
            simp only [compileTerm, argumentsEq, dynamicNodeCount,
              sourceNodeCount, Nat.add_le_add_iff_left]
            exact dynamicNodesCount_compile_le arguments
        | some groundedArguments =>
            simp [compileTerm, argumentsEq, dynamicNodeCount,
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

theorem sourceNodeCount_positive (term : Term) : 0 < sourceNodeCount term := by
  cases term with
  | var identifier => simp [sourceNodeCount]
  | atom name => simp [sourceNodeCount]
  | integer value => simp [sourceNodeCount]
  | app constructor arguments =>
      simp only [sourceNodeCount]
      omega

theorem dynamicNodeCount_compile_eq_zero_of_ground
    (term : Term) (grounded : GroundTerm)
    (recognized : groundTerm? term = some grounded) :
    dynamicNodeCount (compileTerm term) = 0 := by
  cases term with
  | var identifier => simp [groundTerm?] at recognized
  | atom name => simp [compileTerm, dynamicNodeCount]
  | integer value => simp [compileTerm, dynamicNodeCount]
  | app constructor arguments =>
      cases argumentsEq : groundTerms? arguments with
      | none => simp [groundTerm?, argumentsEq] at recognized
      | some groundedArguments =>
          simp [compileTerm, argumentsEq, dynamicNodeCount]

def sourceRuntimeCost (uses : Nat) (term : Term) : Nat :=
  uses * sourceNodeCount term

def cachedRuntimeCost (uses : Nat) (term : Term) : Nat :=
  uses * dynamicNodeCount (compileTerm term)

theorem cachedRuntimeCost_le_source (uses : Nat) (term : Term) :
    cachedRuntimeCost uses term <= sourceRuntimeCost uses term := by
  exact Nat.mul_le_mul_left uses (dynamicNodeCount_compile_le term)

theorem cachedRuntimeCost_lt_source_of_ground
    (uses : Nat) (positiveUses : 0 < uses)
    (term : Term) (grounded : GroundTerm)
    (recognized : groundTerm? term = some grounded) :
    cachedRuntimeCost uses term < sourceRuntimeCost uses term := by
  rw [cachedRuntimeCost, sourceRuntimeCost,
    dynamicNodeCount_compile_eq_zero_of_ground term grounded recognized]
  simp only [Nat.mul_zero]
  exact Nat.mul_pos positiveUses (sourceNodeCount_positive term)

/-! ## Composable realization -/

/-- Ground-subterm caching as a distinct generated artifact realization. -/
def groundSubtermCacheRealization :
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

/-! ## Independent witnesses and a rejection boundary -/

private def parserTemplate : Term :=
  .app "token" (.ofList [.atom "left", .var 0, .atom "right"])

/-- Parser delimiters become cached values around a dynamic semantic hole. -/
example : compileTerm parserTemplate =
    .app "token" (.ofList [
      .ground (.atom "left"), .variable 0, .ground (.atom "right")]) := by
  rfl

private def proofTemplate : Term :=
  .app "step" (.ofList [
    .app "claim" (.ofList [.atom "turnstile", .var 0]),
    .app "label" (.ofList [.atom "axiom-1"])])

/-- A proof-like plan independently caches its fully ground label subtree. -/
example : compileTerm proofTemplate =
    .app "step" (.ofList [
      .app "claim" (.ofList [
        .ground (.atom "turnstile"), .variable 0]),
      .ground (.app "label" (.ofList [.atom "axiom-1"]))]) := by
  rfl

/-- A variable-bearing subtree is not falsely admitted as a cached value. -/
example : compileTerm (.app "pair" (.ofList [.var 0, .var 1])) =
    .app "pair" (.ofList [.variable 0, .variable 1]) := by
  rfl

/-- A repeated immutable subtree yields a strict runtime construction saving. -/
example :
    cachedRuntimeCost 3 (.app "tag" (.ofList [.atom "fixed"])) <
      sourceRuntimeCost 3 (.app "tag" (.ofList [.atom "fixed"])) := by
  decide

end Mettapedia.GSLT.LanguageDef.GroundSubtermCacheCompilation
