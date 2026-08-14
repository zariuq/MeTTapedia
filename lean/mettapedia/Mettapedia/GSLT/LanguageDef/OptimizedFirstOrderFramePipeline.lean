import Mettapedia.GSLT.LanguageDef.LiteralHeadSeparationCompilation
import Mettapedia.GSLT.LanguageDef.TwoPhaseFrameCompilation

/-!
# Composed optimized first-order frame pipeline

This module composes three independently justified transformations already
implemented by the generic native frame machine:

* binder collection precedes simultaneous hypothesis checking;
* adjacent immutable literals form compact runs around substitution holes;
* a value-local leading literal moves out of the tagged residual stream.

The source observation is the complete partial frame transformer.  Empty and
leading-hole templates retain the preceding representation, repeated holes
and empty images keep their occurrence semantics, and interleaved bind/check
instructions preserve their original stack coordinates.
-/

namespace Mettapedia.GSLT.LanguageDef.OptimizedFirstOrderFramePipeline

open FirstOrderFrameCompilation

universe uToken uVar

abbrev CompiledTemplate (Token : Type uToken) (Var : Type uVar) :=
  LiteralHeadSeparationCompilation.Representation Token Var

/-- The two role-resolved instruction classes of the generic frame machine. -/
inductive Instruction (Token : Type uToken) (Var : Type uVar) where
  | bind (specification : Binder Token Var)
  | check (template : CompiledTemplate Token Var)
deriving DecidableEq, Repr

structure Frame (Token : Type uToken) (Var : Type uVar) where
  instructions : List (Instruction Token Var)
  conclusion : CompiledTemplate Token Var
deriving DecidableEq, Repr

def lowerHypothesis : Hypothesis Token Var → Instruction Token Var
  | .binder specification => .bind specification
  | .matching template =>
      .check (LiteralHeadSeparationCompilation.lower template)

/-- Total semantic pipeline after flat-carrier admission.  Value-local passes
retain their exact predecessor representation when they do not apply. -/
def compileFrame (source : SourceFrame Token Var) : Frame Token Var where
  instructions := source.hypotheses.map lowerHypothesis
  conclusion := LiteralHeadSeparationCompilation.lower source.conclusion

/-! ## Independent compiled execution -/

def runBinders [DecidableEq Token] [DecidableEq Var] :
    List (Instruction Token Var) → List (Formula Token) →
      Substitution Var Token → Option (Substitution Var Token)
  | [], [], substitution => some substitution
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | .bind specification :: instructions, input :: stack, substitution => do
      let next ← bindOne substitution specification input
      runBinders instructions stack next
  | .check _ :: instructions, _ :: stack, substitution =>
      runBinders instructions stack substitution

def runMatches [DecidableEq Token]
    (substitution : Substitution Var Token) :
    List (Instruction Token Var) → List (Formula Token) → Option Unit
  | [], [] => some ()
  | [], _ :: _ => none
  | _ :: _, [] => none
  | .bind _ :: instructions, _ :: stack =>
      runMatches substitution instructions stack
  | .check template :: instructions, input :: stack => do
      let _ ← LiteralHeadSeparationCompilation.matchRepresentation
        substitution template input
      runMatches substitution instructions stack

def runFrame [DecidableEq Token] [DecidableEq Var]
    (compiled : Frame Token Var)
    (stack : List (Formula Token)) : Option (Formula Token) := do
  let substitution ← runBinders
    compiled.instructions stack emptySubstitution
  let _ ← runMatches substitution compiled.instructions stack
  LiteralHeadSeparationCompilation.instantiateRepresentation
    substitution compiled.conclusion

/-! ## Composed refinement -/

theorem runBinders_map_lowerHypothesis
    [DecidableEq Token] [DecidableEq Var]
    (hypotheses : List (Hypothesis Token Var))
    (stack : List (Formula Token))
    (substitution : Substitution Var Token) :
    runBinders (hypotheses.map lowerHypothesis) stack substitution =
      TwoPhaseFrameCompilation.runSourceBinders
        hypotheses stack substitution := by
  induction hypotheses generalizing stack substitution with
  | nil => cases stack <;> rfl
  | cons hypothesis hypotheses inductionHypothesis =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          cases hypothesis with
          | binder specification =>
              simp only [List.map_cons, lowerHypothesis, runBinders,
                TwoPhaseFrameCompilation.runSourceBinders]
              cases bindOne substitution specification input <;>
                simp [inductionHypothesis]
          | matching template =>
              simp [lowerHypothesis, runBinders,
                TwoPhaseFrameCompilation.runSourceBinders,
                inductionHypothesis]

theorem runMatches_map_lowerHypothesis
    [DecidableEq Token]
    (substitution : Substitution Var Token)
    (hypotheses : List (Hypothesis Token Var))
    (stack : List (Formula Token)) :
    runMatches substitution
        (hypotheses.map lowerHypothesis) stack =
      TwoPhaseFrameCompilation.runSourceMatches
        substitution hypotheses stack := by
  induction hypotheses generalizing stack with
  | nil => cases stack <;> rfl
  | cons hypothesis hypotheses inductionHypothesis =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          cases hypothesis with
          | binder specification =>
              simp [lowerHypothesis, runMatches,
                TwoPhaseFrameCompilation.runSourceMatches,
                inductionHypothesis]
          | matching template =>
              simp only [List.map_cons, lowerHypothesis, runMatches,
                TwoPhaseFrameCompilation.runSourceMatches]
              rw [LiteralHeadSeparationCompilation.matchRepresentation_lower_eq_materializedMatch]
              cases materializedMatch substitution template input <;>
                simp [inductionHypothesis]

/-- The composed machine preserves the full simultaneous first-order frame
semantics, including all failures. -/
theorem runFrame_compileFrame
    [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var)
    (stack : List (Formula Token)) :
    runFrame (compileFrame source) stack =
      TwoPhaseFrameCompilation.runSourceFrame source stack := by
  unfold runFrame TwoPhaseFrameCompilation.runSourceFrame compileFrame
  rw [runBinders_map_lowerHypothesis]
  cases bindersEq : TwoPhaseFrameCompilation.runSourceBinders
      source.hypotheses stack emptySubstitution with
  | none => simp
  | some substitution =>
      change
        (runMatches substitution
            (source.hypotheses.map lowerHypothesis) stack).bind
              (fun _ =>
                LiteralHeadSeparationCompilation.instantiateRepresentation
                  substitution
                  (LiteralHeadSeparationCompilation.lower
                    source.conclusion)) =
          (TwoPhaseFrameCompilation.runSourceMatches
            substitution source.hypotheses stack).bind
              (fun _ => instantiate substitution source.conclusion)
      rw [runMatches_map_lowerHypothesis,
        LiteralHeadSeparationCompilation.instantiateRepresentation_lower]

/-- The complete optimization pipeline is a composable certified
realization, not a collection of independently quoted equalities. -/
def optimizedFrameRealization [DecidableEq Token] [DecidableEq Var] :
    Mettapedia.GSLT.SimpleRealization
      (SourceFrame Token Var) (Frame Token Var)
      (List (Formula Token) → Option (Formula Token)) where
  compile := fun _ source => compileFrame source
  observeSource := fun _ source =>
    TwoPhaseFrameCompilation.runSourceFrame source
  observeArtifact := fun _ compiled => runFrame compiled
  adequate := by
    intro _ source
    funext stack
    exact runFrame_compileFrame source stack

/-! ## Composed cost refinement -/

def sourceTemplateTagCost (template : Template Token Var) : Nat :=
  LiteralHoleRunCompilation.compiledDispatchCost template

def compiledTemplateTagCost (template : Template Token Var) : Nat :=
  LiteralHeadSeparationCompilation.tagDispatchCost
    (LiteralHeadSeparationCompilation.lower template)

def sourceHypothesisTagCost : Hypothesis Token Var → Nat
  | .binder _ => 0
  | .matching template => sourceTemplateTagCost template

def compiledHypothesisTagCost : Hypothesis Token Var → Nat
  | .binder _ => 0
  | .matching template => compiledTemplateTagCost template

def sourceFrameTagCost (source : SourceFrame Token Var) : Nat :=
  (source.hypotheses.map sourceHypothesisTagCost).sum +
    sourceTemplateTagCost source.conclusion

def compiledFrameTagCost (source : SourceFrame Token Var) : Nat :=
  (source.hypotheses.map compiledHypothesisTagCost).sum +
    compiledTemplateTagCost source.conclusion

theorem compiledHypothesisTagCost_le
    (hypothesis : Hypothesis Token Var) :
    compiledHypothesisTagCost hypothesis ≤
      sourceHypothesisTagCost hypothesis := by
  cases hypothesis with
  | binder specification =>
      simp [compiledHypothesisTagCost, sourceHypothesisTagCost]
  | matching template =>
      exact LiteralHeadSeparationCompilation.tagDispatchCost_lower_le_prior
        template

theorem compiledHypothesisTagCosts_le
    (hypotheses : List (Hypothesis Token Var)) :
    (hypotheses.map compiledHypothesisTagCost).sum ≤
      (hypotheses.map sourceHypothesisTagCost).sum := by
  induction hypotheses with
  | nil => simp
  | cons hypothesis hypotheses inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (compiledHypothesisTagCost_le hypothesis) inductionHypothesis

/-- Composing the value-local head pass over every matching hypothesis and
the conclusion cannot increase dynamic tag dispatches for the complete
frame. -/
theorem compiledFrameTagCost_le_sourceFrameTagCost
    (source : SourceFrame Token Var) :
    compiledFrameTagCost source ≤ sourceFrameTagCost source := by
  unfold compiledFrameTagCost sourceFrameTagCost
  exact Nat.add_le_add
    (compiledHypothesisTagCosts_le source.hypotheses)
    (LiteralHeadSeparationCompilation.tagDispatchCost_lower_le_prior
      source.conclusion)

def sourceTemplateWordCost (template : Template Token Var) : Nat :=
  LiteralHoleRunCompilation.compiledWordCost
    (LiteralHoleRunCompilation.compile template)

def compiledTemplateWordCost (template : Template Token Var) : Nat :=
  LiteralHeadSeparationCompilation.physicalWordCost
    (LiteralHeadSeparationCompilation.lower template)

def sourceHypothesisWordCost : Hypothesis Token Var → Nat
  | .binder _ => 2
  | .matching template => sourceTemplateWordCost template

def compiledHypothesisWordCost : Hypothesis Token Var → Nat
  | .binder _ => 2
  | .matching template => compiledTemplateWordCost template

def sourceFrameWordCost (source : SourceFrame Token Var) : Nat :=
  (source.hypotheses.map sourceHypothesisWordCost).sum +
    sourceTemplateWordCost source.conclusion

def compiledFrameWordCost (source : SourceFrame Token Var) : Nat :=
  (source.hypotheses.map compiledHypothesisWordCost).sum +
    compiledTemplateWordCost source.conclusion

theorem compiledHypothesisWordCost_le
    (hypothesis : Hypothesis Token Var) :
    compiledHypothesisWordCost hypothesis ≤
      sourceHypothesisWordCost hypothesis := by
  cases hypothesis with
  | binder specification =>
      simp [compiledHypothesisWordCost, sourceHypothesisWordCost]
  | matching template =>
      exact LiteralHeadSeparationCompilation.physicalWordCost_lower_le_prior
        template

theorem compiledHypothesisWordCosts_le
    (hypotheses : List (Hypothesis Token Var)) :
    (hypotheses.map compiledHypothesisWordCost).sum ≤
      (hypotheses.map sourceHypothesisWordCost).sum := by
  induction hypotheses with
  | nil => simp
  | cons hypothesis hypotheses inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (compiledHypothesisWordCost_le hypothesis) inductionHypothesis

/-- The composed template carrier is representation-nonincreasing across the
entire frame, including the conclusion. -/
theorem compiledFrameWordCost_le_sourceFrameWordCost
    (source : SourceFrame Token Var) :
    compiledFrameWordCost source ≤ sourceFrameWordCost source := by
  unfold compiledFrameWordCost sourceFrameWordCost
  exact Nat.add_le_add
    (compiledHypothesisWordCosts_le source.hypotheses)
    (LiteralHeadSeparationCompilation.physicalWordCost_lower_le_prior
      source.conclusion)

/-! ## Independent witnesses and negative behavior -/

private def proofFrame : SourceFrame Nat Nat where
  hypotheses :=
    [ .binder { head := 1, holeId := 0 }
    , .matching [.literal 2, .literal 3, .hole 0, .literal 4] ]
  conclusion := [.literal 5, .hole 0]

/-- Proof-like execution performs binder collection, fused checking, and
headed conclusion construction through the composed artifact. -/
example : runFrame (compileFrame proofFrame)
    [[1, 8, 9], [2, 3, 8, 9, 4]] = some [5, 8, 9] := by
  decide

private def parserFrame : SourceFrame String Nat where
  hypotheses :=
    [ .binder { head := "value", holeId := 0 }
    , .matching [.literal "node", .hole 0] ]
  conclusion := [.literal "accepted", .hole 0]

/-- A parser/evaluator-shaped frame independently uses the same machine. -/
example : runFrame (compileFrame parserFrame)
    [["value", "x"], ["node", "x"]] = some ["accepted", "x"] := by
  decide

private def interleavedFrame : SourceFrame Nat Nat where
  hypotheses :=
    [ .matching [.literal 20, .hole 0]
    , .binder { head := 10, holeId := 0 } ]
  conclusion := [.hole 0]

/-- Stack coordinates survive interleaving even though binders execute before
matches. -/
example : runFrame (compileFrame interleavedFrame)
    [[20, 7], [10, 7]] = some [7] := by
  decide

/-- A missing binding remains rejection rather than an empty image. -/
example : runFrame
    (compileFrame
      { hypotheses := [.matching [.literal 20, .hole 9]]
        conclusion := [.literal 30] })
    [[20]] = none := by
  decide

/-- Leading-hole and empty templates do not enter head separation. -/
example :
    LiteralHeadSeparationCompilation.recognize
        ([.hole 0, .literal 1] : Template Nat Nat) = none ∧
      LiteralHeadSeparationCompilation.recognize
        ([] : Template Nat Nat) = none := by
  decide

end Mettapedia.GSLT.LanguageDef.OptimizedFirstOrderFramePipeline
