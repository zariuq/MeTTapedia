import Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

/-!
# Certified two-phase compilation of first-order frames

An ordered rule frame need not place every binder before every matching
hypothesis.  The more general first-order execution discipline is simultaneous:
first collect binder images from their corresponding inputs, then check every
matching hypothesis under the completed environment.

This module compiles arbitrary role-resolved frames into a compact instruction
sequence.  The source interpreter materializes substituted matches; the
compiled interpreter fuses substitution with comparison.  The main theorem
proves equality of the entire partial stack transformer for every frame and
input, including interleaved frames outside the stricter binder-prefix
fragment.
-/

namespace Mettapedia.GSLT.LanguageDef.TwoPhaseFrameCompilation

open FirstOrderFrameCompilation

universe u v

/-! ## Compiled instruction layout -/

/-- The two generated roles after source-table decoding. -/
inductive FrameInstruction (Token : Type u) (Var : Type v) where
  | bind (specification : Binder Token Var)
  | check (template : Template Token Var)
deriving DecidableEq, Repr

/-- A compact, role-resolved frame.  The instruction order retains the exact
stack-slot correspondence of the authored frame. -/
structure TwoPhaseFrame (Token : Type u) (Var : Type v) where
  instructions : List (FrameInstruction Token Var)
  conclusion : Template Token Var
deriving DecidableEq, Repr

def lowerHypothesis :
    Hypothesis Token Var → FrameInstruction Token Var
  | .binder specification => .bind specification
  | .matching template => .check template

/-- Total lowering after the generated decoder has classified every
hypothesis role. -/
def compileFrame (source : SourceFrame Token Var) :
    TwoPhaseFrame Token Var where
  instructions := source.hypotheses.map lowerHypothesis
  conclusion := source.conclusion

/-! ## Independent simultaneous source semantics -/

/-- First source pass: inspect every stack position but extend the environment
only at binder hypotheses. -/
def runSourceBinders [DecidableEq Token] [DecidableEq Var] :
    List (Hypothesis Token Var) → List (Formula Token) →
      Substitution Var Token → Option (Substitution Var Token)
  | [], [], substitution => some substitution
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | .binder specification :: hypotheses, input :: stack, substitution => do
      let next ← bindOne substitution specification input
      runSourceBinders hypotheses stack next
  | .matching _ :: hypotheses, _ :: stack, substitution =>
      runSourceBinders hypotheses stack substitution

/-- Second source pass: materialize and compare matching hypotheses while
retaining exact stack-slot correspondence. -/
def runSourceMatches [DecidableEq Token]
    (substitution : Substitution Var Token) :
    List (Hypothesis Token Var) → List (Formula Token) → Option Unit
  | [], [] => some ()
  | [], _ :: _ => none
  | _ :: _, [] => none
  | .binder _ :: hypotheses, _ :: stack =>
      runSourceMatches substitution hypotheses stack
  | .matching template :: hypotheses, input :: stack => do
      let _ ← materializedMatch substitution template input
      runSourceMatches substitution hypotheses stack

/-- Declarative simultaneous-substitution meaning of an arbitrary
role-resolved frame. -/
def runSourceFrame [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var) (stack : List (Formula Token)) :
    Option (Formula Token) := do
  let substitution ← runSourceBinders
    source.hypotheses stack emptySubstitution
  let _ ← runSourceMatches substitution source.hypotheses stack
  instantiate substitution source.conclusion

/-! ## Compiled two-phase execution -/

def runCompiledBinders [DecidableEq Token] [DecidableEq Var] :
    List (FrameInstruction Token Var) → List (Formula Token) →
      Substitution Var Token → Option (Substitution Var Token)
  | [], [], substitution => some substitution
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | .bind specification :: instructions, input :: stack, substitution => do
      let next ← bindOne substitution specification input
      runCompiledBinders instructions stack next
  | .check _ :: instructions, _ :: stack, substitution =>
      runCompiledBinders instructions stack substitution

def runCompiledMatches [DecidableEq Token]
    (substitution : Substitution Var Token) :
    List (FrameInstruction Token Var) →
      List (Formula Token) → Option Unit
  | [], [] => some ()
  | [], _ :: _ => none
  | _ :: _, [] => none
  | .bind _ :: instructions, _ :: stack =>
      runCompiledMatches substitution instructions stack
  | .check template :: instructions, input :: stack => do
      let _ ← fusedMatch substitution template input
      runCompiledMatches substitution instructions stack

def runCompiledFrame [DecidableEq Token] [DecidableEq Var]
    (compiled : TwoPhaseFrame Token Var)
    (stack : List (Formula Token)) : Option (Formula Token) := do
  let substitution ← runCompiledBinders
    compiled.instructions stack emptySubstitution
  let _ ← runCompiledMatches substitution compiled.instructions stack
  instantiate substitution compiled.conclusion

/-! ## Refinement proof -/

theorem runCompiledBinders_map_lowerHypothesis
    [DecidableEq Token] [DecidableEq Var]
    (hypotheses : List (Hypothesis Token Var))
    (stack : List (Formula Token))
    (substitution : Substitution Var Token) :
    runCompiledBinders
        (hypotheses.map lowerHypothesis) stack substitution =
      runSourceBinders hypotheses stack substitution := by
  induction hypotheses generalizing stack substitution with
  | nil => cases stack <;> rfl
  | cons hypothesis hypotheses ih =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          cases hypothesis with
          | binder specification =>
              simp only [List.map_cons, lowerHypothesis,
                runCompiledBinders, runSourceBinders]
              cases bindOne substitution specification input <;>
                simp [ih]
          | matching template =>
              simp [lowerHypothesis, runCompiledBinders,
                runSourceBinders, ih]

theorem runCompiledMatches_map_lowerHypothesis
    [DecidableEq Token]
    (substitution : Substitution Var Token)
    (hypotheses : List (Hypothesis Token Var))
    (stack : List (Formula Token)) :
    runCompiledMatches substitution
        (hypotheses.map lowerHypothesis) stack =
      runSourceMatches substitution hypotheses stack := by
  induction hypotheses generalizing stack with
  | nil => cases stack <;> rfl
  | cons hypothesis hypotheses ih =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          cases hypothesis with
          | binder specification =>
              simp [lowerHypothesis, runCompiledMatches,
                runSourceMatches, ih]
          | matching template =>
              simp only [List.map_cons, lowerHypothesis,
                runCompiledMatches, runSourceMatches]
              rw [fusedMatch_eq_materializedMatch]
              cases materializedMatch substitution template input <;>
                simp [ih]

/-- Total two-phase lowering preserves the independent simultaneous source
semantics for every role-resolved frame and every stack. -/
theorem runCompiledFrame_compileFrame
    [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var)
    (stack : List (Formula Token)) :
    runCompiledFrame (compileFrame source) stack =
      runSourceFrame source stack := by
  unfold runCompiledFrame runSourceFrame compileFrame
  rw [runCompiledBinders_map_lowerHypothesis]
  cases bindersEq : runSourceBinders
      source.hypotheses stack emptySubstitution with
  | none => simp
  | some substitution =>
      change
        (runCompiledMatches substitution
            (source.hypotheses.map lowerHypothesis) stack).bind
              (fun _ => instantiate substitution source.conclusion) =
          (runSourceMatches substitution
            source.hypotheses stack).bind
              (fun _ => instantiate substitution source.conclusion)
      rw [runCompiledMatches_map_lowerHypothesis]

/-! ## Certified-realization packaging -/

/-- Arbitrary role-resolved frames have a certified two-phase realization.
The observation is the complete partial stack transformer. -/
def twoPhaseFrameRealization [DecidableEq Token] [DecidableEq Var] :
    Mettapedia.GSLT.SimpleRealization
      (SourceFrame Token Var)
      (TwoPhaseFrame Token Var)
      (List (Formula Token) → Option (Formula Token)) where
  compile := fun _ source => compileFrame source
  observeSource := fun _ source => runSourceFrame source
  observeArtifact := fun _ compiled => runCompiledFrame compiled
  adequate := by
    intro _ source
    funext stack
    exact runCompiledFrame_compileFrame source stack

/-! ## Non-vacuity canaries -/

private def interleavedSource : SourceFrame Nat Nat where
  hypotheses :=
    [ .binder { head := 10, holeId := 0 }
    , .matching [.literal 20, .hole 0]
    , .binder { head := 11, holeId := 1 } ]
  conclusion := [.literal 30, .hole 1]

/-- The stricter binder-prefix compiler rejects this valid interleaving. -/
example :
    FirstOrderFrameCompilation.compileFrame interleavedSource = none := by
  decide

/-- The total two-phase compiler accepts the same frame and performs both a
real match and a conclusion substitution. -/
example :
    runCompiledFrame (compileFrame interleavedSource)
        [[10, 7], [20, 7], [11, 8]] =
      some [30, 8] := by
  decide

/-- A matching hypothesis with an unbound hole still fails closed. -/
example :
    runCompiledFrame
      (compileFrame
        { hypotheses := [.matching [.literal 20, .hole 9]]
          conclusion := [.literal 30] })
      [[20, 7]] = none := by
  decide

/-- Conflicting duplicate binder images are rejected. -/
example :
    runCompiledFrame
      (compileFrame
        { hypotheses :=
            [ .binder { head := 10, holeId := 0 }
            , .binder { head := 10, holeId := 0 } ]
          conclusion := [.hole 0] })
      [[10, 7], [10, 8]] = none := by
  decide

end Mettapedia.GSLT.LanguageDef.TwoPhaseFrameCompilation
