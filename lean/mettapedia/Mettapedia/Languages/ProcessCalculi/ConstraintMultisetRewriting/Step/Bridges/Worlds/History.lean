import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.OriginSupport
import Mettapedia.GSLT.Core.CoveredExecutionPaths

/-!
# Exact world histories of persistent rule executions

The supplied singleton-world path is recovered as a whole path, including
every intermediate world state. Choosing a held origin for each base firing
then gives an actual admitted persistent-rule run whose projected world
history is that same path. Neither construction identifies counted runs
after erasing their events or origins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.History

open RuleSyntax RuleSyntax.Worlds RuleSyntax.RuleOccurrences
open LiveRules.Origins
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite

universe uO uT uH uE uOcc uR uZ uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O]
  {X : Frames Tm Hom}

/-- Recovering an admitted run from a successor path retains every supplied
intermediate state, rather than only its final state and length. -/
theorem run_of_path_exact {S : Type uS} {F : S → Type uF}
    (primitive : Step X O S F) {first last : S}
    (path : ExecutionPath (Execution.theory primitive) first last) :
    ∃ run : primitive.Run first, run.last = last ∧
      HEq (Execution.toPath primitive run) path ∧ run.word.length = path.length := by
  induction path with
  | refl => exact ⟨.nil _, rfl, HEq.rfl, rfl⟩
  | cons edge rest ih =>
      obtain ⟨firing, admitted, same⟩ := edge.down
      subst same
      obtain ⟨run, endpoint, exactRest, length⟩ := ih
      refine ⟨.cons firing admitted run, endpoint, ?_, congrArg (· + 1) length⟩
      cases endpoint
      change HEq (Route.cons _ (Execution.toPath primitive run)) (Route.cons edge rest)
      rw [eq_of_heq exactRest]
      cases edge
      rfl

variable (X : Frames Tm Hom) (E : Extensions.{uO,uH,uE} Hom)

/-- Exact readback uses the existing covered-path lifting theorem. The
roundtrip retains all intermediate worlds of the given path. -/
theorem singletonPathRun_exact (program shared : Program Tm)
    {first last : Bag Tm O} (path : ExecutionPath (firings X E) first last)
    (state : State Tm O) (same : singleton program shared state = first) :
    ∃ run : (step X O E (program ∪ shared)).toStep.Run state,
      singleton program shared run.last = last ∧
        HEq (singletonRunPath X E program shared run) path ∧
        run.word.length = path.length := by
  cases same
  let translation := singletonTranslation (O := O) X E program shared
  let comparison := one_world_bisimulation (X := X) (E := E) (O := O) program shared
  let cover : StepCover (Execution.theory (step X O E (program ∪ shared)).toStep)
      (firings X E) translation.mapTerm := ⟨comparison.zig, comparison.zag⟩
  obtain ⟨endpoint, actual, final, exactPath, length⟩ :=
    StepCover.liftExecutionPath_exact translation cover path
  obtain ⟨run, runLast, exactRun, count⟩ := run_of_path_exact _ actual
  refine ⟨run, (congrArg (singleton program shared) runLast).trans final, ?_, count.trans length⟩
  cases runLast
  change HEq (translation.mapRoute (Execution.toPath _ run)) path
  rw [eq_of_heq exactRun]
  exact exactPath

variable {P Q : Program Tm} {R : Type uR} [DecidableEq R] {Z : Type uZ}
  {ids : Finset R} {code : R → Rule Tm} (zone : R → Z) (offers : Offers Q ids code)

include offers

omit [DecidableEq R] in
/-- The exact support licence supplies an origin at every event of any
specified base execution. Duplicate origins are not identified. -/
theorem decorations_nonempty : ∀ {count : Nat} {state : State Tm O}
    (base : (baseEvents X E (P := P) (Q := Q)).Execution count state),
    Nonempty (Decorations X E (ids := ids) (code := code) zone base)
  | 0, _, _ => ⟨PUnit.unit⟩
  | _ + 1, state, ⟨firing, rest⟩ => by
      obtain ⟨use, available, aligned⟩ := available_of_mem offers state zone firing.val.member
      obtain ⟨origins⟩ := decorations_nonempty rest
      exact ⟨⟨⟨use, available, aligned⟩, origins⟩⟩

/-- Selecting available origins recovers the entire supplied world path.
The origin decoration remains separate from that erased path. -/
theorem worldPath_lifts_exact {state : State Tm O} {last : Bag Tm O}
    (path : ExecutionPath (firings X E) (singleton P Q state) last) :
    ∃ run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state path.length,
      singleton P Q (projectRun X E zone offers state path.length run).val.last = last ∧
        HEq (OriginSupport.worldPath X E zone offers run) path := by
  obtain ⟨base, endpoint, exactBase, count⟩ := singletonPathRun_exact X E P Q path state rfl
  let fixed : BaseRuns X E (P := P) (Q := Q) state path.length := ⟨base, count⟩
  let execution := ((step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
    (fun {_} firing => (firing.rule, firing.selection)) state path.length).symm fixed
  obtain ⟨origins⟩ := decorations_nonempty X E zone offers execution
  let run := liftOrigins X E zone offers execution origins
  have projected : projectRun X E zone offers state path.length run = fixed := by
    exact (project_liftOrigins X E zone offers execution origins).trans
      (((step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
        (fun {_} firing => (firing.rule, firing.selection)) state path.length).apply_symm_apply fixed)
  refine ⟨run, ?_, ?_⟩
  · rw [projected]
    exact endpoint
  · unfold OriginSupport.worldPath
    rw [projected]
    exact exactBase

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.History
