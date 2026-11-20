import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaReadoutControls

/-! Executable consumer of open-answer sharing and branch-transport controls. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaReadoutControls

def describe (label : String) (result : Unifying.Outcome) : IO Unit := do
  match Unifying.observed result with
  | .answers answers => IO.println s!"{label}: {reprStr (answers.map Atom.toString)}"
  | .fault reason => throw (IO.userError s!"{label}: {reprStr reason}")
  | .other => throw (IO.userError s!"{label}: unfinished source computation")

def main : IO Unit := do
  IO.println s!"per-answer-equal: {decide (VariantReadout.each shared = VariantReadout.each independent)}"
  IO.println s!"joint-equal: {decide (VariantReadout.joint shared = VariantReadout.joint independent)}"
  describe "inverse-alias" (Unifying.run registry 100 transported)
  describe "display-alias" (Unifying.run registry 100 displayOnly)
  describe "branch-bindings" (Unifying.run registry 100 branchTransported)
  describe "erased-bindings" (Unifying.run registry 100 branchBindingsErased)
  describe "collect-alternatives"
    (Unifying.run registry 100 (ScopedSource.enter 0 [] Effects.empty copiedAlternatives))
  describe "collect-pair"
    (Unifying.run registry 100 (ScopedSource.enter 0 [] Effects.empty copiedPair))
