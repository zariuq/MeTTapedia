import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUEquationCompilation

/-! Separate E normalization from primitive R transitions. The R reduct is
explicit and retains the signature and rule table; it is not presented as
the full source theory. The source, E stage and R stage stay together for
composition. Equality coherence and normalization certificates are not
manufactured by constructing this pair.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUStagePair

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def rTheory (source : Maude.Theory) : Maude.Theory :=
  {source with name := source.name ++ ":R-reduct", equations := []}

def rOperation {source : Maude.Theory} (operation : Maude.ACUOperation source []) :
    Maude.ACUOperation (rTheory source) [] where
  declaration := operation.declaration
  declared := operation.declared
  arguments := operation.arguments
  associative := operation.associative
  commutative := operation.commutative
  unit := operation.unit
  identity := operation.identity
  unit_sorted := operation.unit_sorted

structure Prepared where
  source : Maude.Theory
  equations : ACUEquationCompilation.Prepared
  transitions : LanguageDef

def prepare {source : Maude.Theory} (operation : Maude.ACUOperation source []) : Except String Prepared := do
  let equations ← ACUEquationCompilation.prepare operation
  let transitions ← ACUBagCompilation.prepare (rOperation operation)
  pure ⟨source, equations, transitions⟩

theorem source_retained {source : Maude.Theory} (operation : Maude.ACUOperation source [])
    {prepared : Prepared} (accepted : prepare operation = .ok prepared) : prepared.source = source := by
  unfold prepare at accepted
  cases equations : ACUEquationCompilation.prepare operation with
  | error message =>
    simp [equations] at accepted
    change Except.error _ = Except.ok prepared at accepted
    cases accepted
  | ok equationStage =>
    cases transitions : ACUBagCompilation.prepare (rOperation operation) with
    | error message =>
      simp [equations, transitions] at accepted
      change Except.error _ = Except.ok prepared at accepted
      cases accepted
    | ok transitionStage =>
      simp [equations, transitions] at accepted
      cases accepted
      rfl

#print axioms source_retained

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUStagePair
