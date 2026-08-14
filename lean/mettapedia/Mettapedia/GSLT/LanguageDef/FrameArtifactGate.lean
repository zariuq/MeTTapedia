/-
# Typed first-order frame compilation check

This module packages the existing executable first-order frame compiler as a
Boolean equality check between a source frame and an already-decoded claimed
frame, with a semantic adequacy theorem.

This is deliberately one layer narrower than a serialized-artifact gate.  It
does not parse the generated `.answers` carrier, authenticate its provenance,
or prove correspondence with the C loader.  Those byte/term decoding and
loader-refinement obligations remain separate.  The check here becomes useful
at that boundary once both decoded values have been obtained independently.

The typed-value check pattern is:

* `check… : Source → ClaimedArtifact → Bool` — executable;
* `check…_correct` — acceptance ↔ the admission relation;
* `check…_adequate` — acceptance implies the artifact observes exactly as
  its source (inheriting the module's adequacy theorem);
* a positive witness, a tampered-artifact rejection, and an
  inadmissible-source rejection.

This file instantiates the pattern for the first-order frame compilation
level, using the existing executable scheduling compiler `compileFrame`.
Other mechanism modules already expose executable `Bool`/`Option` admissions;
their remaining task is not to duplicate this wrapper mechanically, but to
connect the canonical serialized carrier, typed admission, and runtime loader
with checked correspondence.
-/
import Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

namespace Mettapedia.GSLT.LanguageDef.FrameArtifactGate

open Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

variable {Token Var : Type}

/-- Executable typed-value check: the already-decoded claimed frame must be
exactly the scheduling compiler's output on the source. -/
def checkFrameArtifact [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var)
    (claimed : CompiledFrame Token Var) : Bool :=
  decide (compileFrame source = some claimed)

/-- Check correctness: acceptance is exactly the compilation relation. -/
theorem checkFrameArtifact_correct [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var) (claimed : CompiledFrame Token Var) :
    checkFrameArtifact source claimed = true ↔
      compileFrame source = some claimed := by
  simp [checkFrameArtifact]

/-- An accepted typed frame observes exactly as its source.  This is semantic
adequacy after decoding, not a claim about serialized formatting or the C
loader. -/
theorem checkFrameArtifact_adequate [DecidableEq Token] [DecidableEq Var]
    (source : SourceFrame Token Var) (claimed : CompiledFrame Token Var)
    (accepted : checkFrameArtifact source claimed = true)
    (stack : List (Formula Token)) :
    runCompiledFrame claimed stack = runSourceFrame source stack :=
  runCompiledFrame_eq_runSourceFrame source claimed
    ((checkFrameArtifact_correct source claimed).1 accepted) stack

/-! ## Witnesses (Token = Var = Nat) -/

/-- A small admissible source frame: one binder hypothesis, one matching
hypothesis. -/
def sampleSource : SourceFrame Nat Nat where
  hypotheses :=
    [ .binder { head := 0, holeId := 0 }
    , .matching [.literal 1, .hole 0] ]
  conclusion := [.literal 2, .hole 0]

/-- The artifact the scheduling compiler actually produces for
`sampleSource`. -/
def sampleCompiled : CompiledFrame Nat Nat where
  binders := [{ head := 0, holeId := 0 }]
  patterns := [[.literal 1, .hole 0]]
  conclusion := [.literal 2, .hole 0]

/-- Positive witness: the genuine artifact passes the gate. -/
theorem sample_accepted :
    checkFrameArtifact sampleSource sampleCompiled = true := by decide

/-- A tampered artifact: same binders and patterns, altered conclusion. -/
def tamperedCompiled : CompiledFrame Nat Nat :=
  { sampleCompiled with conclusion := [.literal 3, .hole 0] }

/-- Negative witness: tampering is rejected — the gate is not a formatting
check. -/
theorem tampered_rejected :
    checkFrameArtifact sampleSource tamperedCompiled = false := by decide

/-- An inadmissible source: a binder hypothesis after a matching
hypothesis violates the scheduling discipline. -/
def inadmissibleSource : SourceFrame Nat Nat where
  hypotheses :=
    [ .matching [.literal 1]
    , .binder { head := 0, holeId := 0 } ]
  conclusion := [.literal 2]

/-- Negative witness: an inadmissible source has NO accepted artifact — the
gate rejects every claim about it, fail-closed. -/
theorem inadmissible_rejected (claimed : CompiledFrame Nat Nat) :
    checkFrameArtifact inadmissibleSource claimed = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  have h := (checkFrameArtifact_correct inadmissibleSource claimed).1 accepted
  have hnone : compileFrame inadmissibleSource =
      (none : Option (CompiledFrame Nat Nat)) := by decide
  rw [hnone] at h
  simp at h

end Mettapedia.GSLT.LanguageDef.FrameArtifactGate
