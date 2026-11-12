import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepBound

/-!
# The sweep at full width: every universe position, and rows without thinning

The generator writes `U0` and `U1` at every universe position of a code (`gen`). This module adds what the sweep
needs to look where the thinned, one-universe sweep did not.

* **Universes of a problem** (`Raw.level`, `Problem.level`): the largest universe a problem writes. Tallies are kept
  apart by it (`LevelTally`), so a count is always a count at a stated universe.
* **Raising chosen universe positions** (`Raw.raiseAt`, `Problem.raiseAt`, `Problem.variants`): a problem written by
  hand at `U0` gives, for every choice of its universe positions, the problem with those positions one universe up.
  Ill-typed choices are rejected by the checker when the store is built. Raising twice reaches `U2`.
* **Rows without thinning** (`allSidesOf`, `Raw.isPattern`, `sweepWide`): for every annotation, the ordered pairs of
  its thinned typed sides as before, and, for its first pattern sides, the pattern against **every** typed side of
  the annotation, in both orders.

The sweep takes the verdict as a function, so the same tiers run under every family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPatternFiring.Controls

namespace Raw

/-- **The largest universe a code writes**: `0` when it writes none, or only `U0`. -/
def level : Raw → Nat
  | .var _ | .u0 => 0
  | .u1 => 1
  | .u2 => 2
  | .pi a b | .sigma a b | .app a b | .pair a b => max (level a) (level b)
  | .id a b c => max (level a) (max (level b) (level c))
  | .lam a | .fst a | .snd a | .refl a => level a

/-- The number of universe positions of a code. -/
def sortCount : Raw → Nat
  | .var _ => 0
  | .u0 | .u1 | .u2 => 1
  | .pi a b | .sigma a b | .app a b | .pair a b => sortCount a + sortCount b
  | .id a b c => sortCount a + sortCount b + sortCount c
  | .lam a | .fst a | .snd a | .refl a => sortCount a

/-- **Raise chosen universe positions by one universe.** Positions are counted left to right from `position`;
position `i` is raised when bit `i` of `mask` is set. `U2` stays. The result is the code and the next position. -/
def raiseAt (mask : Nat) : Nat → Raw → Raw × Nat
  | position, .var index => (.var index, position)
  | position, .u0 => (if mask.testBit position then .u1 else .u0, position + 1)
  | position, .u1 => (if mask.testBit position then .u2 else .u1, position + 1)
  | position, .u2 => (.u2, position + 1)
  | position, .pi a b =>
      let first := raiseAt mask position a
      let second := raiseAt mask first.2 b
      (.pi first.1 second.1, second.2)
  | position, .sigma a b =>
      let first := raiseAt mask position a
      let second := raiseAt mask first.2 b
      (.sigma first.1 second.1, second.2)
  | position, .app a b =>
      let first := raiseAt mask position a
      let second := raiseAt mask first.2 b
      (.app first.1 second.1, second.2)
  | position, .pair a b =>
      let first := raiseAt mask position a
      let second := raiseAt mask first.2 b
      (.pair first.1 second.1, second.2)
  | position, .id a b c =>
      let first := raiseAt mask position a
      let second := raiseAt mask first.2 b
      let third := raiseAt mask second.2 c
      (.id first.1 second.1 third.1, third.2)
  | position, .lam a => let inner := raiseAt mask position a; (.lam inner.1, inner.2)
  | position, .fst a => let inner := raiseAt mask position a; (.fst inner.1, inner.2)
  | position, .snd a => let inner := raiseAt mask position a; (.snd inner.1, inner.2)
  | position, .refl a => let inner := raiseAt mask position a; (.refl inner.1, inner.2)

/-- Under `binders` bound variables: an unknown applied to distinct bound variables. -/
def patternBody (binders : Nat) : Raw → List Nat → Bool
  | .var index, _ => decide (binders ≤ index)
  | .app function (.var index), seen =>
      decide (index < binders) && !seen.contains index && patternBody binders function (index :: seen)
  | _, _ => false

/-- **A pattern side**: under its abstractions, an unknown applied to distinct bound variables. -/
def isPattern (side : Raw) : Bool := patternBody side.lamCount side.lamBody []

/-- **The codes one universe lower at one result position**: the end of the telescope, through the components of a
Σ type. Binder types are left as they are. -/
def lowerings : Raw → List Raw
  | .u1 => [.u0]
  | .u2 => [.u1]
  | .pi domain codomain => (lowerings codomain).map fun lower => .pi domain lower
  | .sigma first second =>
      ((lowerings first).map fun lower => .sigma lower second) ++
        ((lowerings second).map fun lower => .sigma first lower)
  | _ => []

end Raw

/-- An annotation one universe lower at one result position, at which both sides are still typed. -/
def lowerStep? (Γ : Context setting.R) (equation : Raw × Raw × Raw) : Option (Raw × Raw × Raw) :=
  (equation.1.lowerings.find? fun lower => (equationOf? Γ (lower, equation.2.1, equation.2.2)).isSome).map
    fun lower => (lower, equation.2.1, equation.2.2)

/-- **The equation at its least annotation**: result universes lowered while both sides stay typed. -/
def leastAnnotation (Γ : Context setting.R) : Nat → Raw × Raw × Raw → Raw × Raw × Raw
  | 0, equation => equation
  | fuel + 1, equation =>
      match lowerStep? Γ equation with
      | some lower => leastAnnotation Γ fuel lower
      | none => equation

/-- **A problem with every equation at its least annotation.** The checker decides what is typed; that the lowered
store has the same solutions is `ContextualDependentUniverseInjective`, not this definition. -/
def Problem.lowered (problem : Problem) : Problem :=
  match contextFrom (empty setting.R) problem.unknowns with
  | none => problem
  | some Γ => { problem with equations := problem.equations.map (leastAnnotation Γ 8) }

/-- The largest universe a problem writes, in its declarations, annotations and sides. -/
def Problem.level (problem : Problem) : Nat :=
  (problem.unknowns.foldl (fun top raw => max top raw.level) 0) |>
    problem.equations.foldl fun top equation =>
      max top (max equation.1.level (max equation.2.1.level equation.2.2.level))

/-- The number of universe positions of a problem. -/
def Problem.sortCount (problem : Problem) : Nat :=
  (problem.unknowns.foldl (fun total raw => total + raw.sortCount) 0) |>
    problem.equations.foldl fun total equation =>
      total + equation.1.sortCount + equation.2.1.sortCount + equation.2.2.sortCount

/-- Raise chosen universe positions of a list of codes, threading the position. -/
def raiseList (mask : Nat) : Nat → List Raw → List Raw × Nat
  | position, [] => ([], position)
  | position, raw :: rest =>
      let first := raw.raiseAt mask position
      let others := raiseList mask first.2 rest
      (first.1 :: others.1, others.2)

/-- Raise chosen universe positions of a list of equations, threading the position. -/
def raiseEquations (mask : Nat) : Nat → List (Raw × Raw × Raw) → List (Raw × Raw × Raw) × Nat
  | position, [] => ([], position)
  | position, equation :: rest =>
      let annotation := equation.1.raiseAt mask position
      let left := equation.2.1.raiseAt mask annotation.2
      let right := equation.2.2.raiseAt mask left.2
      let others := raiseEquations mask right.2 rest
      ((annotation.1, left.1, right.1) :: others.1, others.2)

/-- **A problem with chosen universe positions one universe up**: positions run through the declarations, then
through each equation's annotation, left side and right side. -/
def Problem.raiseAt (mask : Nat) (problem : Problem) : Problem :=
  let unknowns := raiseList mask 0 problem.unknowns
  { unknowns := unknowns.1, equations := (raiseEquations mask unknowns.2 problem.equations).1 }

/-- **The universe variants of a problem**: every choice of universe positions raised, when there are at most `cap`
choices; otherwise `cap` choices, spread deterministically, with no position raised and every position raised
among them. -/
def Problem.variants (cap : Nat) (problem : Problem) : List Problem :=
  let choices := 2 ^ problem.sortCount
  if choices ≤ cap then (List.range choices).map fun mask => problem.raiseAt mask
  else
    ((List.range cap).map fun index =>
      if index = 0 then 0 else if index = 1 then choices - 1 else (index * 2654435761 + 12345) % choices).map
      fun mask => problem.raiseAt mask

/-! ## Tallies by universe -/

/-- **Tallies kept apart by the largest universe of the problem.** -/
structure LevelTally where
  at0 : Tally := {}
  at1 : Tally := {}
  at2 : Tally := {}
  deriving Inhabited

/-- Count one verdict at the problem's universe. -/
def LevelTally.count (tally : LevelTally) (problem : Problem) (verdict : Verdict) : LevelTally :=
  match problem.level with
  | 0 => { tally with at0 := tally.at0.count problem verdict }
  | 1 => { tally with at1 := tally.at1.count problem verdict }
  | _ => { tally with at2 := tally.at2.count problem verdict }

/-- The number of problems counted, at all universes. -/
def LevelTally.total (tally : LevelTally) : Nat := tally.at0.total + tally.at1.total + tally.at2.total

/-- The number of stuck problems, at all universes. -/
def LevelTally.stuck (tally : LevelTally) : Nat := tally.at0.stuck + tally.at1.stuck + tally.at2.stuck

/-- One line of counts. -/
def Tally.counts (tally : Tally) : String :=
  s!"{tally.total} problems: ill-typed {tally.illTyped}, outside {tally.outside}, committed {tally.committed}, " ++
    s!"refuted {tally.refuted}, stuck {tally.stuck}, cutoff {tally.cutoff}"

/-- A reading of the tallies: the counts at each universe, then the stuck families with one witness each. -/
def LevelTally.toText (tally : LevelTally) : String :=
  let families := fun (name : String) (part : Tally) =>
    part.families.reverse.map fun entry => s!"    {name} [{entry.2.1}] {entry.1} :: {entry.2.2.toText}"
  s!"  U0: {tally.at0.counts}\n  U1: {tally.at1.counts}\n  U2: {tally.at2.counts}" ++
    "\n".intercalate ("" :: (families "U0" tally.at0 ++ families "U1" tally.at1 ++ families "U2" tally.at2))

/-- **Sweep a list of problems under a verdict**, by universe. -/
def sweepLevels (verdict : Problem → Verdict) (problems : List Problem) (tally : LevelTally := {}) : LevelTally :=
  problems.foldl (init := tally) fun tally problem => tally.count problem (verdict problem)

/-- **Tallies with the stuck problems read a second time at their least annotations.** `first` counts every
problem; `least` counts only the problems stuck in `first`, by the verdict of the same sides at their least
annotations (and at the universe of the problem as given). A problem stuck in `least` is stuck where no annotation
is raised. -/
structure SplitTally where
  first : LevelTally := {}
  least : LevelTally := {}
  deriving Inhabited

/-- Count one problem, and, when it is stuck, the same sides at their least annotations. -/
def SplitTally.count (verdict : Problem → Verdict) (tally : SplitTally) (problem : Problem) : SplitTally :=
  let read := verdict problem
  let first := tally.first.count problem read
  if read = .ended .stuck then
    { first := first, least := tally.least.count problem (verdict problem.lowered) }
  else { tally with first := first }

/-- **Sweep a list of problems**, the stuck ones read a second time at their least annotations. -/
def sweepSplit (verdict : Problem → Verdict) (problems : List Problem) (tally : SplitTally := {}) : SplitTally :=
  problems.foldl (init := tally) (SplitTally.count verdict)

/-- A reading of split tallies. -/
def SplitTally.toText (tally : SplitTally) : String :=
  s!" as given ({tally.first.total} problems, stuck {tally.first.stuck})\n{tally.first.toText}\n" ++
    s!" the stuck ones at their least annotations (still stuck {tally.least.stuck})\n{tally.least.toText}"

/-! ## Rows without thinning -/

/-- **Every typed side of an annotation**: the abstractions of β-normal raw codes that check against it, with no
thinning. Bodies under as many abstractions as the annotation has Π binders have at most `bodySize` constructors;
bodies under fewer, at most `shortSize`. -/
def allSidesOf (Γ : Context setting.R) (annotation : Raw) (bodySize shortSize : Nat) : List Raw :=
  match typeOf? Γ annotation with
  | none => []
  | some type =>
      let binders := annotation.piCount
      let candidates := (List.range (binders + 1)).reverse.flatMap fun depth =>
        (genUpTo (Γ.arity + depth) (if depth = binders then bodySize else shortSize)).filterMap fun body =>
          if body.lamCount = 0 then some (Raw.lams depth body) else none
      candidates.filter fun side => (termOf? Γ type side).isSome

/-- **The tallies of a sweep at full width.** -/
structure Wide where
  /-- The ordered pairs of thinned sides. -/
  pairs : SplitTally := {}
  /-- Pattern sides against every typed side, in both orders. -/
  rows : SplitTally := {}
  annotations : Nat := 0
  /-- The annotations that have a pattern side. -/
  withPattern : Nat := 0
  /-- The typed sides, before thinning, over all annotations. -/
  sides : Nat := 0
  deriving Inhabited

/-- **Sweep annotations at full width**: for every annotation, every ordered pair of its typed sides thinned to
`perForm` per head form and `cap` in all; and, for its first `patterns` pattern sides, the pattern against every
typed side, in both orders, with no thinning. -/
def sweepWide (verdict : Problem → Verdict) (unknowns : List Raw) (Γ : Context setting.R)
    (annotations : List Raw) (bodySize shortSize perForm cap patterns : Nat) (start : Wide := {}) : Wide :=
  annotations.foldl (init := start) fun wide annotation =>
    let all := allSidesOf Γ annotation bodySize shortSize
    let thinned := thin (fun side => s!"{side.lamCount}:{(side.lamBody).headForm side.lamCount}") perForm cap all
    let chosen := (all.filter Raw.isPattern).take patterns
    let pairs := thinned.foldl (init := wide.pairs) fun tally left =>
      thinned.foldl (init := tally) fun tally right =>
        tally.count verdict { unknowns := unknowns, equations := [(annotation, left, right)] }
    let rows := chosen.foldl (init := wide.rows) fun tally pattern =>
      all.foldl (init := tally) fun tally side =>
        (tally.count verdict { unknowns := unknowns, equations := [(annotation, pattern, side)] }).count verdict
          { unknowns := unknowns, equations := [(annotation, side, pattern)] }
    { pairs := pairs, rows := rows, annotations := wide.annotations + 1,
      withPattern := wide.withPattern + (if chosen.isEmpty then 0 else 1), sides := wide.sides + all.length }

/-- A reading of a sweep at full width. -/
def Wide.toText (wide : Wide) : String :=
  s!"{wide.annotations} annotations ({wide.withPattern} with a pattern side), {wide.sides} typed sides\n" ++
    s!"PAIRS of thinned sides\n{wide.pairs.toText}\nROWS without thinning\n{wide.rows.toText}"

end ContextualDependentSweep
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
