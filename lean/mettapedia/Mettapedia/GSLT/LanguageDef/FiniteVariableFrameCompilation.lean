import Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
import Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

/-!
# Certified finite-variable lowering for first-order frames

The ordered-frame compiler identifies a first-order rule-machine fragment, but
its semantic substitution still uses authored variable keys.  This module adds
the next independent lowering pass.  Given a duplicate-free finite inventory,
it resolves every binder and template hole to `Fin inventory.length` and
rejects frames containing an undeclared variable.

The refinement theorem relates the two complete frame transformers.  It uses
the finite-environment result to show that direct slot writes decode to the
same authored substitution, then transports template instantiation, fused
matching, binder execution, and the conclusion through that relation.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteVariableFrameCompilation

open FirstOrderFrameCompilation
open FiniteEnvironmentCompilation

variable {Token Var : Type}

/-! ## Resolving frame syntax -/

/-- Resolve every hole in a flat template to a dense slot. -/
def compileTemplate? [DecidableEq Var] (inventory : Inventory Var) :
    Template Token Var → Option (Template Token inventory.Slot)
  | [] => some []
  | .literal token :: rest => do
      let tail : Template Token inventory.Slot ←
        compileTemplate? inventory rest
      pure ((.literal token :: tail) : Template Token inventory.Slot)
  | .hole holeId :: rest =>
      match inventory.resolve? holeId with
      | none => none
      | some slot =>
          match compileTemplate? inventory rest with
          | none => none
          | some tail => some
              ((@TemplateAtom.hole Token inventory.Slot slot :: tail) :
                Template Token inventory.Slot)

/-- Resolve one binder key while preserving its generated type head. -/
def compileBinder? [DecidableEq Var] (inventory : Inventory Var)
    (binder : Binder Token Var) : Option (Binder Token inventory.Slot) :=
  match inventory.resolve? binder.holeId with
  | none => none
  | some slot => some { head := binder.head, holeId := slot }

def compileBinders? [DecidableEq Var] (inventory : Inventory Var) :
    List (Binder Token Var) → Option (List (Binder Token inventory.Slot))
  | [] => some []
  | binder :: binders => do
      let compiled ← compileBinder? inventory binder
      let tail ← compileBinders? inventory binders
      pure (compiled :: tail)

def compileTemplates? [DecidableEq Var] (inventory : Inventory Var) :
    List (Template Token Var) →
      Option (List (Template Token inventory.Slot))
  | [] => some []
  | template :: templates => do
      let compiled ← compileTemplate? inventory template
      let tail ← compileTemplates? inventory templates
      pure (compiled :: tail)

/-- Compile every variable-bearing component of an admitted ordered frame. -/
def compileFrame? [DecidableEq Var] (inventory : Inventory Var)
    (frame : CompiledFrame Token Var) :
    Option (CompiledFrame Token inventory.Slot) := do
  let binders ← compileBinders? inventory frame.binders
  let patterns ← compileTemplates? inventory frame.patterns
  let conclusion ← compileTemplate? inventory frame.conclusion
  pure { binders, patterns, conclusion }

/-! ## Exact finite-support recognizer -/

/-- Syntactic support check for one template.  Each hole must resolve through
the generated finite inventory; literals impose no support requirement. -/
def templateSupported? [DecidableEq Var] (inventory : Inventory Var) :
    Template Token Var → Bool
  | [] => true
  | .literal _ :: rest => templateSupported? inventory rest
  | .hole holeId :: rest =>
      (inventory.resolve? holeId).isSome &&
        templateSupported? inventory rest

def binderSupported? [DecidableEq Var] (inventory : Inventory Var)
    (binder : Binder Token Var) : Bool :=
  (inventory.resolve? binder.holeId).isSome

def bindersSupported? [DecidableEq Var] (inventory : Inventory Var) :
    List (Binder Token Var) → Bool
  | [] => true
  | binder :: binders =>
      binderSupported? inventory binder &&
        bindersSupported? inventory binders

def templatesSupported? [DecidableEq Var] (inventory : Inventory Var) :
    List (Template Token Var) → Bool
  | [] => true
  | template :: templates =>
      templateSupported? inventory template &&
        templatesSupported? inventory templates

/-- The local property licensing dense-variable lowering for a whole frame. -/
def frameSupported? [DecidableEq Var] (inventory : Inventory Var)
    (frame : CompiledFrame Token Var) : Bool :=
  bindersSupported? inventory frame.binders &&
    templatesSupported? inventory frame.patterns &&
      templateSupported? inventory frame.conclusion

theorem compileTemplate?_isSome_eq_templateSupported?
    [DecidableEq Var] (inventory : Inventory Var)
    (template : Template Token Var) :
    (compileTemplate? inventory template).isSome =
      templateSupported? inventory template := by
  induction template with
  | nil => rfl
  | cons atom rest ih =>
      cases atom with
      | literal token =>
          unfold compileTemplate? templateSupported?
          rw [← ih]
          cases compileTemplate? inventory rest <;> rfl
      | hole holeId =>
          unfold compileTemplate? templateSupported?
          rw [← ih]
          cases inventory.resolve? holeId <;>
            cases compileTemplate? inventory rest <;> rfl

theorem compileBinder?_isSome_eq_binderSupported?
    [DecidableEq Var] (inventory : Inventory Var)
    (binder : Binder Token Var) :
    (compileBinder? inventory binder).isSome =
      binderSupported? inventory binder := by
  unfold compileBinder? binderSupported?
  cases inventory.resolve? binder.holeId <;> rfl

theorem compileBinders?_isSome_eq_bindersSupported?
    [DecidableEq Var] (inventory : Inventory Var)
    (binders : List (Binder Token Var)) :
    (compileBinders? inventory binders).isSome =
      bindersSupported? inventory binders := by
  induction binders with
  | nil => rfl
  | cons binder binders ih =>
      unfold bindersSupported?
      rw [← compileBinder?_isSome_eq_binderSupported? inventory binder,
        ← ih]
      change ((do
          let compiled ← compileBinder? inventory binder
          let tail ← compileBinders? inventory binders
          pure (compiled :: tail)).isSome =
        ((compileBinder? inventory binder).isSome &&
          (compileBinders? inventory binders).isSome))
      cases compileBinder? inventory binder <;>
        cases compileBinders? inventory binders <;> rfl

theorem compileTemplates?_isSome_eq_templatesSupported?
    [DecidableEq Var] (inventory : Inventory Var)
    (templates : List (Template Token Var)) :
    (compileTemplates? inventory templates).isSome =
      templatesSupported? inventory templates := by
  induction templates with
  | nil => rfl
  | cons template templates ih =>
      unfold templatesSupported?
      rw [← compileTemplate?_isSome_eq_templateSupported? inventory template,
        ← ih]
      change ((do
          let compiled ← compileTemplate? inventory template
          let tail ← compileTemplates? inventory templates
          pure (compiled :: tail)).isSome =
        ((compileTemplate? inventory template).isSome &&
          (compileTemplates? inventory templates).isSome))
      cases compileTemplate? inventory template <;>
        cases compileTemplates? inventory templates <;> rfl

/-- Dense frame compilation succeeds exactly when the locally computed
finite-support recognizer accepts. -/
theorem compileFrame?_isSome_eq_frameSupported?
    [DecidableEq Var] (inventory : Inventory Var)
    (frame : CompiledFrame Token Var) :
    (compileFrame? inventory frame).isSome =
      frameSupported? inventory frame := by
  unfold frameSupported?
  rw [← compileBinders?_isSome_eq_bindersSupported? inventory frame.binders,
    ← compileTemplates?_isSome_eq_templatesSupported? inventory frame.patterns,
    ← compileTemplate?_isSome_eq_templateSupported? inventory frame.conclusion]
  change ((do
      let binders ← compileBinders? inventory frame.binders
      let patterns ← compileTemplates? inventory frame.patterns
      let conclusion ← compileTemplate? inventory frame.conclusion
      pure ({ binders, patterns, conclusion } :
        CompiledFrame Token inventory.Slot)).isSome =
    ((compileBinders? inventory frame.binders).isSome &&
      (compileTemplates? inventory frame.patterns).isSome &&
        (compileTemplate? inventory frame.conclusion).isSome))
  cases compileBinders? inventory frame.binders <;>
    cases compileTemplates? inventory frame.patterns <;>
      cases compileTemplate? inventory frame.conclusion <;> rfl

/-! ## Template refinement -/

/-- Resolving template holes preserves instantiation under related source and
dense environments. -/
theorem instantiate_compileTemplate?
    [DecidableEq Var]
    (inventory : Inventory Var)
    (source : Template Token Var)
    (compiled : Template Token inventory.Slot)
    (accepted : compileTemplate? inventory source = some compiled)
    (sourceEnvironment : Substitution Var Token)
    (denseEnvironment : Substitution inventory.Slot Token)
    (related : decodeDense inventory denseEnvironment = sourceEnvironment) :
    instantiate denseEnvironment compiled =
      instantiate sourceEnvironment source := by
  induction source generalizing compiled with
  | nil =>
      simp [compileTemplate?] at accepted
      subst compiled
      rfl
  | cons atom rest ih =>
      cases atom with
      | literal token =>
          unfold compileTemplate? at accepted
          cases tailEq : compileTemplate? inventory rest with
          | none => simp [tailEq] at accepted
          | some tail =>
              simp [tailEq] at accepted
              subst compiled
              simp only [instantiate, Option.bind_eq_bind]
              rw [ih tail tailEq]
      | hole holeId =>
          unfold compileTemplate? at accepted
          cases selected : inventory.resolve? holeId with
          | none => simp [selected] at accepted
          | some slot =>
              cases tailEq : compileTemplate? inventory rest with
              | none => simp [selected, tailEq] at accepted
              | some tail =>
                  simp [selected, tailEq] at accepted
                  subst compiled
                  have lookupEq :
                      denseEnvironment slot = sourceEnvironment holeId := by
                    have pointwise := congrFun related holeId
                    simpa [decodeDense, selected] using pointwise
                  simp only [instantiate, lookupEq, Option.bind_eq_bind]
                  rw [ih tail tailEq]

/-- Dense-hole fused matching has exactly the authored-hole result. -/
theorem fusedMatch_compileTemplate?
    [DecidableEq Token] [DecidableEq Var]
    (inventory : Inventory Var)
    (source : Template Token Var)
    (compiled : Template Token inventory.Slot)
    (accepted : compileTemplate? inventory source = some compiled)
    (sourceEnvironment : Substitution Var Token)
    (denseEnvironment : Substitution inventory.Slot Token)
    (related : decodeDense inventory denseEnvironment = sourceEnvironment)
    (input : Formula Token) :
    fusedMatch denseEnvironment compiled input =
      fusedMatch sourceEnvironment source input := by
  rw [fusedMatch_eq_materializedMatch, fusedMatch_eq_materializedMatch]
  unfold materializedMatch
  rw [instantiate_compileTemplate? inventory source compiled accepted
    sourceEnvironment denseEnvironment related]

theorem runFusedMatches_compileTemplates?
    [DecidableEq Token] [DecidableEq Var]
    (inventory : Inventory Var)
    (source : List (Template Token Var))
    (compiled : List (Template Token inventory.Slot))
    (accepted : compileTemplates? inventory source = some compiled)
    (sourceEnvironment : Substitution Var Token)
    (denseEnvironment : Substitution inventory.Slot Token)
    (related : decodeDense inventory denseEnvironment = sourceEnvironment)
    (stack : List (Formula Token)) :
    runFusedMatches denseEnvironment compiled stack =
      runFusedMatches sourceEnvironment source stack := by
  induction source generalizing compiled stack with
  | nil =>
      simp [compileTemplates?] at accepted
      subst compiled
      cases stack <;> rfl
  | cons template templates ih =>
      unfold compileTemplates? at accepted
      cases headEq : compileTemplate? inventory template with
      | none => simp [headEq] at accepted
      | some compiledTemplate =>
          cases tailEq : compileTemplates? inventory templates with
          | none => simp [headEq, tailEq] at accepted
          | some compiledTail =>
              simp [headEq, tailEq] at accepted
              subst compiled
              cases stack with
              | nil => rfl
              | cons input stack =>
                  simp only [runFusedMatches]
                  rw [fusedMatch_compileTemplate? inventory template
                    compiledTemplate headEq sourceEnvironment denseEnvironment
                    related input]
                  cases fusedMatch sourceEnvironment template input
                  <;> simp [ih compiledTail tailEq]

/-! ## Binder refinement -/

/-- A compiled binder updates a direct slot exactly when the authored binder
updates its key. -/
theorem bindOne_compileBinder?
    [DecidableEq Token] [DecidableEq Var]
    (inventory : Inventory Var)
    (source : Binder Token Var)
    (compiled : Binder Token inventory.Slot)
    (accepted : compileBinder? inventory source = some compiled)
    (sourceEnvironment : Substitution Var Token)
    (denseEnvironment : Substitution inventory.Slot Token)
    (related : decodeDense inventory denseEnvironment = sourceEnvironment)
    (input : Formula Token) :
    Option.map (decodeDense inventory)
        (bindOne denseEnvironment compiled input) =
      bindOne sourceEnvironment source input := by
  unfold compileBinder? at accepted
  cases selected : inventory.resolve? source.holeId with
  | none => simp [selected] at accepted
  | some slot =>
      simp [selected] at accepted
      subst compiled
      have lookupEq :
          denseEnvironment slot = sourceEnvironment source.holeId := by
        have pointwise := congrFun related source.holeId
        simpa [decodeDense, selected] using pointwise
      cases input with
      | nil => rfl
      | cons actual image =>
          by_cases headEq : actual = source.head
          · cases denseLookup : denseEnvironment slot with
            | none =>
                have sourceLookup :
                    sourceEnvironment source.holeId = none := by
                  rw [← lookupEq, denseLookup]
                have updateEq :
                    decodeDense inventory
                        (insertSubstitution denseEnvironment slot image) =
                      insertSubstitution sourceEnvironment
                        source.holeId image := by
                  have direct := decodeDense_writeDense inventory
                    denseEnvironment source.holeId image slot selected
                  calc
                    decodeDense inventory
                        (insertSubstitution denseEnvironment slot image) =
                        decodeDense inventory
                          (writeDense inventory denseEnvironment
                            (slot, image)) := rfl
                    _ = writeSource (decodeDense inventory denseEnvironment)
                        (source.holeId, image) := direct
                    _ = insertSubstitution sourceEnvironment
                        source.holeId image := by
                      rw [related]
                      rfl
                simp [bindOne, headEq, denseLookup, sourceLookup, updateEq]
            | some previous =>
                have sourceLookup :
                    sourceEnvironment source.holeId = some previous := by
                  rw [← lookupEq, denseLookup]
                by_cases sameImage : previous = image
                · simp [bindOne, headEq, denseLookup, sourceLookup,
                    sameImage, related]
                · simp [bindOne, headEq, denseLookup, sourceLookup,
                    sameImage]
          · simp [bindOne, headEq]

theorem runBinders_compileBinders?
    [DecidableEq Token] [DecidableEq Var]
    (inventory : Inventory Var)
    (source : List (Binder Token Var))
    (compiled : List (Binder Token inventory.Slot))
    (accepted : compileBinders? inventory source = some compiled)
    (sourceEnvironment : Substitution Var Token)
    (denseEnvironment : Substitution inventory.Slot Token)
    (related : decodeDense inventory denseEnvironment = sourceEnvironment)
    (stack : List (Formula Token)) :
    Option.map (fun result => (result.1,
        decodeDense inventory result.2))
        (runBinders compiled stack denseEnvironment) =
      runBinders source stack sourceEnvironment := by
  induction source generalizing compiled stack sourceEnvironment denseEnvironment with
  | nil =>
      simp [compileBinders?] at accepted
      subst compiled
      simp [runBinders, related]
  | cons binder binders ih =>
      unfold compileBinders? at accepted
      cases headEq : compileBinder? inventory binder with
      | none => simp [headEq] at accepted
      | some compiledBinder =>
          cases tailEq : compileBinders? inventory binders with
          | none => simp [headEq, tailEq] at accepted
          | some compiledTail =>
              simp [headEq, tailEq] at accepted
              subst compiled
              cases stack with
              | nil => rfl
              | cons input stack =>
                  have stepEq := bindOne_compileBinder? inventory binder
                    compiledBinder headEq sourceEnvironment denseEnvironment
                    related input
                  cases denseStepEq : bindOne denseEnvironment
                      compiledBinder input with
                  | none =>
                      rw [denseStepEq] at stepEq
                      simp only [Option.map_none] at stepEq
                      simp only [runBinders, denseStepEq]
                      rw [← stepEq]
                      rfl
                  | some nextDense =>
                      rw [denseStepEq] at stepEq
                      simp only [Option.map_some] at stepEq
                      simp only [runBinders, denseStepEq]
                      rw [← stepEq]
                      exact ih compiledTail tailEq
                        (decodeDense inventory nextDense) nextDense rfl stack

/-! ## Complete frame refinement -/

/-- Every admitted finite-variable frame has the same stack-transformer
observation before and after dense-slot lowering. -/
theorem runCompiledFrame_compileFrame?
    [DecidableEq Token] [DecidableEq Var]
    (inventory : Inventory Var)
    (source : CompiledFrame Token Var)
    (compiled : CompiledFrame Token inventory.Slot)
    (accepted : compileFrame? inventory source = some compiled)
    (stack : List (Formula Token)) :
    runCompiledFrame compiled stack = runCompiledFrame source stack := by
  unfold compileFrame? at accepted
  cases bindersEq : compileBinders? inventory source.binders with
  | none => simp [bindersEq] at accepted
  | some binders =>
      cases patternsEq : compileTemplates? inventory source.patterns with
      | none => simp [bindersEq, patternsEq] at accepted
      | some patterns =>
          cases conclusionEq : compileTemplate? inventory source.conclusion with
          | none => simp [bindersEq, patternsEq, conclusionEq] at accepted
          | some conclusion =>
              simp [bindersEq, patternsEq, conclusionEq] at accepted
              subst compiled
              have initialRelated :
                  decodeDense inventory
                      (emptySubstitution : Substitution inventory.Slot Token) =
                    (emptySubstitution : Substitution Var Token) := by
                exact decodeDense_empty inventory
              have binderRuns := runBinders_compileBinders? inventory
                source.binders binders bindersEq
                (emptySubstitution : Substitution Var Token)
                (emptySubstitution : Substitution inventory.Slot Token)
                initialRelated stack
              unfold runCompiledFrame
              cases denseBindersEq : runBinders binders stack
                  (emptySubstitution : Substitution inventory.Slot Token) with
              | none =>
                  rw [denseBindersEq] at binderRuns
                  simp only [Option.map_none] at binderRuns
                  rw [← binderRuns]
                  rfl
              | some result =>
                  obtain ⟨remaining, denseEnvironment⟩ := result
                  rw [denseBindersEq] at binderRuns
                  simp only [Option.map_some] at binderRuns
                  rw [← binderRuns]
                  simp
                  rw [runFusedMatches_compileTemplates? inventory
                    source.patterns patterns patternsEq
                    (decodeDense inventory denseEnvironment) denseEnvironment
                    rfl remaining]
                  cases matchesEq : runFusedMatches
                      (decodeDense inventory denseEnvironment)
                      source.patterns remaining with
                  | none => rfl
                  | some matched =>
                      exact instantiate_compileTemplate? inventory
                        source.conclusion conclusion conclusionEq
                        (decodeDense inventory denseEnvironment)
                        denseEnvironment rfl

/-! ## Composable staged realization -/

/-- A compiled ordered frame paired with the exact output of finite-variable
admission. -/
structure DenseAdmittedFrame [DecidableEq Var]
    (inventory : Inventory Var) (Token : Type) where
  source : CompiledFrame Token Var
  compiled : CompiledFrame Token inventory.Slot
  compile_eq : compileFrame? inventory source = some compiled

def admitDenseFrame [DecidableEq Var] (inventory : Inventory Var)
    (source : CompiledFrame Token Var) :
    Option (DenseAdmittedFrame (Var := Var) inventory Token) :=
  match accepted : compileFrame? inventory source with
  | none => none
  | some compiled => some
      { source, compiled, compile_eq := accepted }

def denseFrameRealization
    [DecidableEq Token] [DecidableEq Var] (inventory : Inventory Var) :
    Mettapedia.GSLT.SimpleRealization
      (DenseAdmittedFrame (Var := Var) inventory Token)
      (CompiledFrame Token inventory.Slot)
      (List (Formula Token) → Option (Formula Token)) where
  compile := fun _ admitted => admitted.compiled
  observeSource := fun _ admitted => runCompiledFrame admitted.source
  observeArtifact := fun _ compiled => runCompiledFrame compiled
  adequate := by
    intro _ admitted
    funext stack
    exact runCompiledFrame_compileFrame? inventory admitted.source
      admitted.compiled admitted.compile_eq stack

/-- Joint admission packages the already-computed ordered-frame stage and
the finite-variable stage without weakening either compiler equation. -/
structure OrderedDenseAdmittedFrame
    [DecidableEq Var] (inventory : Inventory Var) (Token : Type) where
  ordered : AdmittedFrame Token Var
  dense : CompiledFrame Token inventory.Slot
  dense_compile_eq : compileFrame? inventory ordered.compiled = some dense

/-- First stage of the joint realization: preserve the ordered-frame
observation while packaging the dense-admission equation for the next
stage. -/
def orderedAdmissionRealization
    [DecidableEq Token] [DecidableEq Var] (inventory : Inventory Var) :
    Mettapedia.GSLT.SimpleRealization
      (OrderedDenseAdmittedFrame (Var := Var) inventory Token)
      (DenseAdmittedFrame (Var := Var) inventory Token)
      (List (Formula Token) → Option (Formula Token)) where
  compile := fun _ admitted =>
    { source := admitted.ordered.compiled
      compiled := admitted.dense
      compile_eq := admitted.dense_compile_eq }
  observeSource := fun _ admitted => runSourceFrame admitted.ordered.source
  observeArtifact := fun _ admitted => runCompiledFrame admitted.source
  adequate := by
    intro _ admitted
    funext stack
    exact runCompiledFrame_eq_runSourceFrame
      admitted.ordered.source admitted.ordered.compiled
      admitted.ordered.compile_eq stack

/-- Ordered scheduling followed by finite-variable lowering is a normal
composition in the shared realization calculus. -/
def orderedDenseRealization
    [DecidableEq Token] [DecidableEq Var] (inventory : Inventory Var) :
    Mettapedia.GSLT.SimpleRealization
      (OrderedDenseAdmittedFrame (Var := Var) inventory Token)
      (CompiledFrame Token inventory.Slot)
      (List (Formula Token) → Option (Formula Token)) :=
  (orderedAdmissionRealization (Token := Token) inventory).trans
    (denseFrameRealization (Token := Token) inventory) (by
      intro _ _
      simp [denseFrameRealization, orderedAdmissionRealization])

/-! ## Positive and negative recognizer canaries -/

private def variableInventory : Inventory Nat where
  keys := [7, 9]
  nodup := by decide

private def sourceFrame : CompiledFrame Nat Nat where
  binders := [{ head := 10, holeId := 7 }]
  patterns := [[.literal 20, .hole 7]]
  conclusion := [.literal 30, .hole 7]

private def denseFrame : CompiledFrame Nat variableInventory.Slot where
  binders := [{ head := 10, holeId := ⟨0, by decide⟩ }]
  patterns := [[.literal 20, .hole ⟨0, by decide⟩]]
  conclusion := [.literal 30, .hole ⟨0, by decide⟩]

/-- A fully supported frame compiles and executes with the same result. -/
example :
    compileFrame? variableInventory sourceFrame = some denseFrame ∧
      runCompiledFrame denseFrame [[10, 4, 5], [20, 4, 5]] =
        some [30, 4, 5] := by
  constructor <;> decide

/-- A hole absent from the generated inventory is rejected. -/
example :
    compileFrame? variableInventory
      { binders := [{ head := 10, holeId := 8 }]
        patterns := []
        conclusion := [.hole 8] } = none := by
  decide

/-- Repeated occurrences of one declared variable preserve equality checks. -/
example :
    runCompiledFrame denseFrame [[10, 4, 5], [20, 4, 6]] = none := by
  decide

end Mettapedia.GSLT.LanguageDef.FiniteVariableFrameCompilation
