import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Completed transport blocks of indexed GSLT commands

The functional command fragment is compared with the existing Grothendieck
construction of execution paths. The semantic quotient is first made
functorial, so this comparison uses the same equation classes as commands.
A completed request exists exactly when the total category has a morphism
with the requested base arrow. This is an existence comparison on completed
blocks; occurrence identity and equality of entire command paths remain
separate observations.

Returned commands compute within their own fibre. A subsequent transport
requires a new explicit request. Completed requests compose through the
standard categorical composition without adding an implicit scheduling rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.Command

open CategoryTheory Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite

universe uTerm uIndex vIndex

variable {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)

/-- An execution path in the existing equation-quotiented fibre. -/
abbrev FibrePath (stage : Index)
    (source target : SemanticTerm (diagram.obj stage).theory) :=
  ExecutionPath (semanticTheory (diagram.obj stage).theory) source target

/-- Lift a complete fibre execution into returned-command execution. -/
def atPath {stage : Index}
    {source target : SemanticTerm (diagram.obj stage).theory} :
    FibrePath diagram stage source target →
      Route (Step diagram) (.at stage source) (.at stage target)
  | .refl state => .refl (Command.at stage state)
  | .cons step rest => .cons (.fibre step.down) (atPath rest)

/-- Every path from a returned command retains its stage and comes from a fibre path. -/
theorem path_from_at {start finish : Command diagram}
    (path : Route (Step diagram) start finish) :
    ∀ (stage : Index) (state : SemanticTerm (diagram.obj stage).theory),
      start = .at stage state →
        ∃ next, finish = .at stage next ∧
          Nonempty (FibrePath diagram stage state next) := by
  induction path with
  | refl object =>
      intro stage state same
      exact ⟨state, same, ⟨.refl state⟩⟩
  | cons event rest inductionHypothesis =>
      intro stage state same
      subst same
      cases event with
      | fibre step =>
          obtain ⟨next, endpoint, ⟨tail⟩⟩ := inductionHypothesis _ _ rfl
          exact ⟨next, endpoint, ⟨.cons ⟨step⟩ tail⟩⟩

/-- Returned-command reachability preserves and reflects complete fibre execution. -/
theorem at_path_iff {stage : Index}
    {source target : SemanticTerm (diagram.obj stage).theory} :
    Nonempty (Route (Step diagram) (.at stage source) (.at stage target)) ↔
      Nonempty (FibrePath diagram stage source target) := by
  constructor
  · rintro ⟨path⟩
    obtain ⟨next, endpoint, tail⟩ := path_from_at diagram path stage source rfl
    have same : target = next := by simpa using endpoint
    subst next
    exact tail
  · rintro ⟨path⟩
    exact ⟨atPath diagram path⟩

/-- A returned state cannot autonomously initiate a new transport request. -/
theorem no_at_path_to_via (stage : Index)
    (state : SemanticTerm (diagram.obj stage).theory)
    {source target : Index} (route : source ⟶ target)
    (pending : SemanticTerm (diagram.obj source).theory) :
    ¬ Nonempty (Route (Step diagram) (.at stage state) (.via route pending)) := by
  rintro ⟨path⟩
  obtain ⟨_, impossible, _⟩ := path_from_at diagram path stage state rfl
  cases impossible

/-- A pending request either remains pending or returns in its declared target fibre. -/
theorem path_from_via {start finish : Command diagram}
    (path : Route (Step diagram) start finish) :
    ∀ {source target : Index} (route : source ⟶ target)
      (state : SemanticTerm (diagram.obj source).theory),
      start = .via route state →
        (∃ next, finish = .via route next ∧
          Nonempty (FibrePath diagram source state next)) ∨
        (∃ next, finish = .at target next ∧
          Nonempty (FibrePath diagram target
            (transportTerm diagram route state) next)) := by
  induction path with
  | refl object =>
      intro source target route state same
      exact Or.inl ⟨state, same, ⟨.refl state⟩⟩
  | cons event rest inductionHypothesis =>
      intro source target route state same
      subst same
      cases event with
      | underVia route step =>
          rcases inductionHypothesis route _ rfl with pending | returned
          · obtain ⟨next, endpoint, ⟨tail⟩⟩ := pending
            exact Or.inl ⟨next, endpoint, ⟨.cons ⟨step⟩ tail⟩⟩
          · obtain ⟨next, endpoint, ⟨tail⟩⟩ := returned
            exact Or.inr ⟨next, endpoint,
              ⟨.cons ⟨transported_fibre_step diagram route step⟩ tail⟩⟩
      | applyVia route state =>
          exact Or.inr (path_from_at diagram rest _ _ rfl)

/-- Completing a request is exactly transport followed by target-fibre execution. -/
theorem completed_block_iff {source target : Index} (route : source ⟶ target)
    (state : SemanticTerm (diagram.obj source).theory)
    (result : SemanticTerm (diagram.obj target).theory) :
    Nonempty (Route (Step diagram) (.via route state) (.at target result)) ↔
      Nonempty (FibrePath diagram target
        (transportTerm diagram route state) result) := by
  constructor
  · rintro ⟨path⟩
    rcases path_from_via diagram path route state rfl with pending | returned
    · obtain ⟨_, impossible, _⟩ := pending
      cases impossible
    · obtain ⟨next, endpoint, tail⟩ := returned
      have same : result = next := by simpa using endpoint
      subst next
      exact tail
  · rintro ⟨path⟩
    exact ⟨.cons (.applyVia route state) (atPath diagram path)⟩

end Mettapedia.GSLT.IndexedOperational.Command

namespace Mettapedia.GSLT.IndexedOperational

open CategoryTheory Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite

universe uTerm uIndex vIndex

/-- The existing path category and finite-step closure express the same
reachability, with path data hidden only by Nonempty. -/
theorem executionPath_nonempty_iff_multiStep (system : GSLT.{uTerm})
    (source target : ExecutionObject system) :
    Nonempty (ExecutionPath system source target) ↔ system.MultiStep source target := by
  constructor
  · rintro ⟨path⟩
    induction path with
    | refl state => exact .refl state
    | cons step rest inductionHypothesis => exact .step step.down inductionHypothesis
  · intro path
    induction path with
    | refl state => exact ⟨.refl state⟩
    | step step rest inductionHypothesis =>
        obtain ⟨tail⟩ := inductionHypothesis
        exact ⟨.cons ⟨step⟩ tail⟩

/-- Local target-step coverage descends to the equation-quotiented theories,
so passing to semantic states preserves the operational reflection contract. -/
def CoveredTranslation.onSemanticTheories {source target : GSLT.{uTerm}}
    (translation : CoveredTranslation source target) :
    CoveredTranslation (semanticTheory source) (semanticTheory target) where
  mapTerm := translation.toOperational.mapSemantic
  mapEquiv := fun same => congrArg translation.toOperational.mapSemantic same
  cover :=
    { mapStep := translation.toOperational.mapSemanticStep
      liftStep := by
        intro sourceClass targetClass step
        induction sourceClass using Quotient.inductionOn with
        | _ sourceTerm =>
          induction targetClass using Quotient.inductionOn with
          | _ targetTerm =>
            have actual := (semanticStep_mk_iff_step target
              (translation.mapTerm sourceTerm) targetTerm).mp step
            obtain ⟨next, sourceStep, same⟩ := translation.cover.liftStep actual
            refine ⟨Quotient.mk source.equations next, semanticStep_mk sourceStep, ?_⟩
            change Quotient.mk target.equations (translation.mapTerm next) =
              Quotient.mk target.equations targetTerm
            rw [same] }

/-- Equation quotienting acts functorially on operational theories and translations. -/
def semanticQuotientFunctor : OperationalTheory.{uTerm} ⥤ OperationalTheory.{uTerm} where
  obj theory := ⟨semanticTheory theory.theory⟩
  map translation := translation.onSemanticTheories
  map_id theory := by
    apply OperationalTranslation.ext
    funext state
    exact OperationalTranslation.mapSemantic_id theory.theory state
  map_comp earlier later := by
    apply OperationalTranslation.ext
    funext state
    exact OperationalTranslation.mapSemantic_comp earlier later state

variable {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)

/-- Reuse the execution-path index on the diagram's equation-quotiented fibres. -/
def semanticExecutionIndex : Index ⥤ CategoryTheory.Cat.{uTerm, uTerm} :=
  (diagram ⋙ semanticQuotientFunctor) ⋙ executionIndex

/-- The standard Grothendieck category of semantic fibre executions. -/
abbrev SemanticExecutionTotal := CategoryTheory.Grothendieck (semanticExecutionIndex diagram)

/-- A language stage together with one equation class of states. -/
def semanticTotalObject (stage : Index)
    (state : SemanticTerm (diagram.obj stage).theory) : SemanticExecutionTotal diagram :=
  ⟨stage, state⟩

/-- A completed command block corresponds to a total-category arrow over its chosen route. -/
theorem completed_block_iff_total_morphism {source target : Index}
    (route : source ⟶ target)
    (state : SemanticTerm (diagram.obj source).theory)
    (result : SemanticTerm (diagram.obj target).theory) :
    Nonempty (Route (Command.Step diagram) (.via route state) (.at target result)) ↔
      ∃ arrow : semanticTotalObject diagram source state ⟶
          semanticTotalObject diagram target result,
        arrow.base = route := by
  rw [Command.completed_block_iff]
  constructor
  · rintro ⟨path⟩
    exact ⟨⟨route, path⟩, rfl⟩
  · rintro ⟨⟨selected, path⟩, same⟩
    change selected = route at same
    subst selected
    exact ⟨path⟩

/-- Two successive explicit requests compose to a completed block over the composed route. -/
theorem composed_block_of_blocks {first middle last : Index}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (source : SemanticTerm (diagram.obj first).theory)
    (intermediate : SemanticTerm (diagram.obj middle).theory)
    (target : SemanticTerm (diagram.obj last).theory)
    (firstBlock : Nonempty (Route (Command.Step diagram)
      (.via earlier source) (.at middle intermediate)))
    (secondBlock : Nonempty (Route (Command.Step diagram)
      (.via later intermediate) (.at last target))) :
    Nonempty (Route (Command.Step diagram)
      (.via (earlier ≫ later) source) (.at last target)) := by
  obtain ⟨firstArrow, firstBase⟩ :=
    (completed_block_iff_total_morphism diagram earlier source intermediate).mp firstBlock
  obtain ⟨secondArrow, secondBase⟩ :=
    (completed_block_iff_total_morphism diagram later intermediate target).mp secondBlock
  apply (completed_block_iff_total_morphism diagram (earlier ≫ later) source target).mpr
  exact ⟨firstArrow ≫ secondArrow, by
    rw [Grothendieck.comp_base, firstBase, secondBase]
    rfl⟩

/-- Under covered transport every completed target block lifts to an actual
source-fibre execution and its exact encoded endpoint, and conversely. -/
theorem covered_completed_block_iff_source_path
    (covered : CoveredDiagram.{uTerm, uIndex, vIndex} Index)
    {source target : Index} (route : source ⟶ target)
    (state : SemanticTerm (covered.toOperational.obj source).theory)
    (result : SemanticTerm (covered.toOperational.obj target).theory) :
    Nonempty (Route (Command.Step covered.toOperational)
      (.via route state) (.at target result)) ↔
      ∃ endpoint,
        Nonempty (Command.FibrePath covered.toOperational source state endpoint) ∧
          transportTerm covered.toOperational route endpoint = result := by
  rw [Command.completed_block_iff]
  constructor
  · intro path
    have targetRun := (executionPath_nonempty_iff_multiStep
      (semanticTheory (covered.obj target).theory) _ _).mp path
    obtain ⟨endpoint, same, sourceRun⟩ :=
      (covered.map route).onSemanticTheories.cover.liftMultiStep targetRun
    exact ⟨endpoint, (executionPath_nonempty_iff_multiStep
      (semanticTheory (covered.obj source).theory) _ _).mpr sourceRun, same⟩
  · rintro ⟨endpoint, ⟨path⟩, same⟩
    change Nonempty (ExecutionPath (semanticTheory (covered.obj target).theory)
      ((covered.map route).toOperational.mapSemantic state) result)
    change (covered.map route).toOperational.mapSemantic endpoint = result at same
    rw [← same]
    exact ⟨(covered.map route).toOperational.onSemanticTheories.mapRoute path⟩

end Mettapedia.GSLT.IndexedOperational
