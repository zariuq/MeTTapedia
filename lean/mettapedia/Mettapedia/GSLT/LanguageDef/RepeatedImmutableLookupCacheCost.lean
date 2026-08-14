import Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation

/-!
# Cost qualification for repetition-admitted lookup caching

Semantic preservation does not imply that caching is profitable.  This module
adds an executable, platform-parameterized cost gate over the counters already
produced by the generic cache machine.  It charges every classification,
source lookup, cache hit, promotion, and retained value.  A workload is
qualified only when that complete symbolic cost is no greater than resolving
every occurrence from the source.

The cost model is intentionally separate from semantic authority.  Empirical
profiling may calibrate its weights, but cannot change the cache refinement
theorem or manufacture a semantic admission.
-/

namespace Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCost

open Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation

variable {Key Value : Type} [DecidableEq Key]

structure Model where
  classification : Nat
  sourceLookup : Nat
  cacheHit : Nat
  promotion : Nat
  retainedValue : Nat
  deriving DecidableEq, Repr

/-- Symbolic cost of a successful cached execution.  Classification occurs
once per admitted occurrence; every promotion also retains one owned value. -/
def cachedCost (model : Model) (stats : Stats) : Nat :=
  (stats.sourceLookups + stats.cacheHits) * model.classification +
  stats.sourceLookups * model.sourceLookup +
  stats.cacheHits * model.cacheHit +
  stats.promotions * (model.promotion + model.retainedValue)

/-- Source execution performs one source lookup per occurrence and retains no
cache state. -/
def freshCost (model : Model) (occurrences : Nat) : Nat :=
  occurrences * model.sourceLookup

/-- Execute the admitted cache semantics and return a result only when the
complete symbolic cost is no worse than fresh lookup. -/
def qualify?
    (environment : Environment Key Value)
    (keys : List Key) (model : Model) :
    Option (List Value × State Key Value × Stats) :=
  match run environment initial {} keys with
  | none => none
  | some (values, state, stats) =>
      if cachedCost model stats ≤ freshCost model keys.length then
        some (values, state, stats)
      else
        none

theorem qualify?_sound
    {environment : Environment Key Value}
    {keys : List Key} {model : Model}
    {values : List Value} {state : State Key Value} {stats : Stats}
    (accepted : qualify? environment keys model =
      some (values, state, stats)) :
    executeFresh environment keys = some values ∧
      cachedCost model stats ≤ freshCost model keys.length ∧
      stats.sourceLookups + stats.cacheHits = keys.length := by
  unfold qualify? at accepted
  cases executed : run environment initial {} keys with
  | none => simp [executed] at accepted
  | some result =>
      rcases result with ⟨resultValues, resultState, resultStats⟩
      simp only [executed] at accepted
      split at accepted
      · rename_i costDominates
        simp only [Option.some.injEq, Prod.mk.injEq] at accepted
        rcases accepted with ⟨rfl, rfl, rfl⟩
        refine ⟨run_refines (initial_valid environment) executed,
          costDominates, ?_⟩
        simpa using run_accounting executed
      · simp at accepted

/-- A compiler promotion requires strictly lower symbolic cost and at least one
real cache hit.  Cost non-regression alone remains useful for refinement, but
cannot select an optimization on an empty or tied workload. -/
def promote?
    (environment : Environment Key Value)
    (keys : List Key) (model : Model) :
    Option (List Value × State Key Value × Stats) :=
  match qualify? environment keys model with
  | none => none
  | some result@(_, _, stats) =>
      if 0 < stats.cacheHits ∧
          cachedCost model stats < freshCost model keys.length then
        some result
      else
        none

theorem promote?_sound
    {environment : Environment Key Value}
    {keys : List Key} {model : Model}
    {values : List Value} {state : State Key Value} {stats : Stats}
    (accepted : promote? environment keys model =
      some (values, state, stats)) :
    executeFresh environment keys = some values ∧
      cachedCost model stats < freshCost model keys.length ∧
      0 < stats.cacheHits ∧
      stats.sourceLookups + stats.cacheHits = keys.length := by
  unfold promote? at accepted
  cases qualified : qualify? environment keys model with
  | none => simp [qualified] at accepted
  | some result =>
      rcases result with ⟨resultValues, resultState, resultStats⟩
      simp only [qualified] at accepted
      split at accepted
      · rename_i profitable
        simp only [Option.some.injEq, Prod.mk.injEq] at accepted
        rcases accepted with ⟨rfl, rfl, rfl⟩
        have refined := qualify?_sound qualified
        exact ⟨refined.1, profitable.2, profitable.1, refined.2.2⟩
      · simp at accepted

private def profitableModel : Model :=
  { classification := 1
    sourceLookup := 100
    cacheHit := 2
    promotion := 20
    retainedValue := 10 }

private def losingModel : Model :=
  { classification := 4
    sourceLookup := 10
    cacheHit := 5
    promotion := 20
    retainedValue := 10 }

example : qualify? sampleEnvironment [7, 7, 7] profitableModel =
    some ([70, 70, 70],
      { seen := [7], resolved := [(7, 70)] },
      { sourceLookups := 2, cacheHits := 1, promotions := 1 }) := by
  rfl

example : qualify? sampleEnvironment [7, 7, 7] losingModel = none := by
  rfl

example : qualify? sampleEnvironment [7] profitableModel = none := by
  rfl

example : promote? sampleEnvironment [7, 7, 7] profitableModel =
    some ([70, 70, 70],
      { seen := [7], resolved := [(7, 70)] },
      { sourceLookups := 2, cacheHits := 1, promotions := 1 }) := by
  rfl

example : promote? sampleEnvironment [] profitableModel = none := by
  rfl

#print axioms qualify?_sound
#print axioms promote?_sound

end Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCost
