import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeWitness
import Mettapedia.GSLT.Core.OperationalRealizationOSLF

/-!
# Completing the actual private work of a mixed tuple registry

Each committed occurrence completes through its existing private communications.
Combining those paths leaves offered senders and the idle frame untouched. The
result is structurally the unary lowering of the retained source readout, with
exactly the registry's outstanding communication debt. Source continuations are
not executed while completing this administrative work.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeDrain

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Ownership RuntimeState RuntimeWitness ScopedActiveFrontier

def leftPath {Γ : Ctx sig} {before after : Proc Γ}
    (path : ExecutionPath (NativeTypes.operationalTheory Γ) before after) (frame : Proc Γ) :
    ExecutionPath (NativeTypes.operationalTheory Γ) (par before frame) (par after frame) :=
  match path with
  | .refl _ => .refl _
  | .cons first rest => .cons ⟨modulo_add_parallel first.down frame⟩ (leftPath rest frame)

theorem leftPath_length {Γ : Ctx sig} {before after : Proc Γ}
    (path : ExecutionPath (NativeTypes.operationalTheory Γ) before after) (frame : Proc Γ) :
    (leftPath path frame).length = path.length := by
  induction path with
  | refl => rfl
  | cons _ _ ih => exact congrArg (fun count => count + 1) ih

def rightPath {Γ : Ctx sig} {before after : Proc Γ}
    (path : ExecutionPath (NativeTypes.operationalTheory Γ) before after) (frame : Proc Γ) :
    ExecutionPath (NativeTypes.operationalTheory Γ) (par frame before) (par frame after) :=
  match path with
  | .refl _ => .refl _
  | .cons first rest => .cons ⟨modulo_add_parallel_right first.down frame⟩ (rightPath rest frame)

theorem rightPath_length {Γ : Ctx sig} {before after : Proc Γ}
    (path : ExecutionPath (NativeTypes.operationalTheory Γ) before after) (frame : Proc Γ) :
    (rightPath path frame).length = path.length := by
  induction path with
  | refl => rfl
  | cons _ _ ih => exact congrArg (fun count => count + 1) ih

def scopePath : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) {before after : Proc Δ},
    ExecutionPath (NativeTypes.operationalTheory Δ) before after →
      ExecutionPath (NativeTypes.operationalTheory Γ) (scope.close before) (scope.close after)
  | _, _, .nil, _, _, path => path
  | _, _, .bind rest, _, _, path =>
      rewritePathToExecutionPath (privatePath (executionPathToRewritePath (scopePath rest path)))

private theorem conversion_length {Γ : Ctx sig} {before after : Proc Γ}
    (path : ExecutionPath (NativeTypes.operationalTheory Γ) before after) :
    (executionPathToRewritePath path).length = path.length := by
  induction path with
  | refl => rfl
  | cons _ _ ih =>
      simpa only [executionPathToRewritePath, Mettapedia.GSLT.GSLT.RewritePath.length,
        Route.length, Nat.add_comm] using congrArg (fun count => 1 + count) ih

theorem scopePath_length : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) {before after : Proc Δ}
    (path : ExecutionPath (NativeTypes.operationalTheory Δ) before after),
    (scopePath scope path).length = path.length
  | _, _, .nil, _, _, _ => rfl
  | _, _, .bind rest, _, _, path => by
      exact (rewritePathToExecutionPath_length
        (privatePath (executionPathToRewritePath (scopePath rest path)))).trans
          ((privatePath_length (executionPathToRewritePath (scopePath rest path))).trans
            ((conversion_length (scopePath rest path)).trans (scopePath_length rest path)))

/-- An actual execution ends at a supplied structural representative of its
goal. A zero-event block uses only a proved structural equation. -/
structure Block {Γ : Ctx sig} (start goal : Proc Γ) (work : Nat) where
  endpoint : Proc Γ
  path : ExecutionPath (NativeTypes.operationalTheory Γ) start endpoint
  equal : StructuralEq endpoint goal
  counted : path.length = work

def Block.empty {Γ : Ctx sig} {start goal : Proc Γ} (equal : StructuralEq start goal) :
    Block start goal 0 := ⟨start, .refl start, equal, rfl⟩

def Block.changeStart {Γ : Ctx sig} {start actual goal : Proc Γ} {work : Nat}
    (block : Block start goal work) (equal : StructuralEq actual start) :
    Block actual goal work := by
  rcases block with ⟨endpoint, path, compared, counted⟩
  cases path with
  | refl => exact ⟨actual, .refl _, equal.trans compared, counted⟩
  | cons first rest =>
      exact ⟨endpoint, .cons ⟨modulo_source_equation equal first.down⟩ rest, compared, counted⟩

def Block.changeGoal {Γ : Ctx sig} {start goal goal' : Proc Γ} {work : Nat}
    (block : Block start goal work) (equal : StructuralEq goal goal') :
    Block start goal' work := { block with equal := block.equal.trans equal }

def Block.parallel {Γ : Ctx sig} {first first' second second' : Proc Γ}
    {firstWork secondWork : Nat} (head : Block first first' firstWork)
    (tail : Block second second' secondWork) :
    Block (par first second) (par first' second') (firstWork + secondWork) := by
  let path := (leftPath head.path second).append (rightPath tail.path head.endpoint)
  refine ⟨par head.endpoint tail.endpoint, path, .par head.equal tail.equal, ?_⟩
  change ((leftPath head.path second).append (rightPath tail.path head.endpoint)).length = _
  erw [Route.length_append, leftPath_length, rightPath_length, head.counted, tail.counted]

def Block.close {Γ Δ : Ctx sig} {start goal : Proc Δ} {work : Nat}
    (block : Block start goal work) (scope : Scope Γ Δ) :
    Block (scope.close start) (scope.close goal) work :=
  ⟨scope.close block.endpoint, scopePath scope block.path, scope.congr block.equal,
    (scopePath_length scope block.path).trans block.counted⟩

def pendingPath {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    ExecutionPath (NativeTypes.operationalTheory Γ)
      (Slot.closed (.pending phase call)) (lower (readback call)) := by
  cases phase with
  | callback =>
      exact .cons ⟨callback_fires call.first call.second (lower call.body)⟩
        (.cons ⟨first_field_fires call.first call.second (lower call.body)⟩
          (.cons ⟨lower_second_field_fires call.first call.second call.body⟩ (.refl _)))
  | first =>
      exact .cons ⟨first_field_fires call.first call.second (lower call.body)⟩
        (.cons ⟨lower_second_field_fires call.first call.second call.body⟩ (.refl _))
  | second => exact .cons ⟨lower_second_field_fires call.first call.second call.body⟩ (.refl _)

theorem pendingPath_length {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    (pendingPath phase call).length = phase.remaining := by cases phase <;> rfl

def slotBlock {Γ : Ctx sig} (slot : Slot Γ) :
    Block slot.closed (lower slot.source) slot.remaining := by
  cases slot with
  | offered channel first second =>
      rw [Slot.source, lower_out2]
      exact .empty (offered_entry channel first second)
  | released call => exact .empty (released_entry call)
  | pending phase call => exact ⟨_, pendingPath phase call, .refl _, pendingPath_length phase call⟩

def listBlock {Γ : Ctx sig} (slots : List (Slot Γ)) :
    Block (parallel (slots.map Slot.closed))
      (lower (parallel (slots.map Slot.source))) ((slots.map Slot.remaining).sum) := by
  induction slots with
  | nil =>
      simp only [List.map_nil, parallel, lower_nil, List.sum_nil]
      exact .empty (.refl _)
  | cons first rest ih =>
      simpa only [List.map_cons, parallel, lower_par, List.sum_cons] using
        (slotBlock first).parallel ih

def registryBlock {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ) :
    Block ((privateScope n).close (registryTarget registry frame))
      (lower (registrySource registry frame)) (registryRemaining registry) := by
  let slots := (List.finRange n).map registry
  have block := (listBlock slots).parallel (Block.empty (.refl (lower frame)))
  simp only [slots, List.map_map, Function.comp_def, Nat.add_zero] at block
  simpa only [registrySource, registryRemaining, lower_par] using
    block.changeStart (Initialization.registry_closed n registry frame)

/-- The supplied runtime representative completes precisely its existing
private debt. No source continuation is run during this selected completion. -/
def drain {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) :
    Block target (lower source) witness.debt := by
  have block := (registryBlock witness.registry (parallel witness.frame)).close witness.scope
  rw [← Initialization.lower_scope] at block
  exact (block.changeStart witness.target).changeGoal (lower_structural witness.source).symm

theorem exists_drain {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target) :
    ∃ endpoint, ∃ path : ExecutionPath (NativeTypes.operationalTheory Γ) target endpoint,
      StructuralEq endpoint (lower source) ∧ path.length = witness.debt :=
  ⟨(drain witness).endpoint, (drain witness).path, (drain witness).equal, (drain witness).counted⟩

/-- Positive private debt is witnessed by a real enabled communication at
the supplied target, rather than by an assumed fair scheduling policy. -/
theorem owed_progress {Γ : Ctx sig} {source target : Proc Γ} (witness : Witness source target)
    (owed : 0 < witness.debt) : ∃ after, StepModulo target after := by
  obtain ⟨endpoint, path, _, counted⟩ := exists_drain witness
  cases path with
  | refl => simp only [Route.length] at counted; omega
  | cons first _ => exact ⟨_, first.down⟩

/-- At zero debt the actual target already represents the source lowering;
no empty execution is used to smuggle in a different endpoint. -/
theorem stable_equation {Γ : Ctx sig} {source target : Proc Γ}
    (witness : Witness source target) (stable : witness.debt = 0) :
    StructuralEq target (lower source) := by
  obtain ⟨endpoint, path, equal, counted⟩ := exists_drain witness
  cases path with
  | refl => exact equal
  | cons _ rest => simp only [Route.length] at counted; omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeDrain
