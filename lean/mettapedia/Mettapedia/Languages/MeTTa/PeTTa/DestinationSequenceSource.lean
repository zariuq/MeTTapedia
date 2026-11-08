import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource

/-!
# Source-owned sequence lowering and missing-else entry

Well-formed binding pairs are the syntax admission used by the native
SEQUENCE_MANY scan. The independently implemented nestedLets lowering is
available exactly on those lists. Actual Destination entry installs that
lowered source and retains the caller, siblings and reached world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.SequenceSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The binding-list shape inspected by contract_bindings: each occurrence
is exactly a pattern/producer pair, independently of either operand's code. -/
def bindingPairs : List Atom → Bool
  | [] => true
  | .expression [_, _] :: rest => bindingPairs rest
  | _ => false

theorem bindingPairs_iff_lowering (pairs : List Atom) (body : Atom) :
    bindingPairs pairs = true ↔ ∃ nested, Eval.nestedLets pairs body = some nested := by
  induction pairs with
  | nil => exact ⟨fun _ => ⟨body, rfl⟩, fun _ => rfl⟩
  | cons pair rest ih =>
      cases pair with
      | var | symbol | grounded => simp [bindingPairs, Eval.nestedLets]
      | expression fields =>
          cases fields with
          | nil => simp [bindingPairs, Eval.nestedLets]
          | cons pattern tail =>
              cases tail with
              | nil => simp [bindingPairs, Eval.nestedLets]
              | cons producer extra =>
                  cases extra with
                  | cons => simp [bindingPairs, Eval.nestedLets]
                  | nil =>
                      simp only [bindingPairs, Eval.nestedLets]
                      rw [ih]
                      constructor
                      · rintro ⟨nested, lowered⟩
                        exact ⟨.expression [.symbol "let", pattern, producer, nested], by simp [lowered]⟩
                      · rintro ⟨nested, lowered⟩
                        obtain ⟨inside, computed, _⟩ := Option.map_eq_some_iff.mp lowered
                        exact ⟨inside, computed⟩

theorem malformed_binding_list_has_no_lowering (pairs : List Atom) (body : Atom)
    (malformed : bindingPairs pairs = false) : Eval.nestedLets pairs body = none := by
  cases lowered : Eval.nestedLets pairs body with
  | none => rfl
  | some nested =>
      have accepted := (bindingPairs_iff_lowering pairs body).mpr ⟨nested, lowered⟩
      rw [malformed] at accepted
      cases accepted

theorem admitted_sequence_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (pairs : List Atom) (body destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (admitted : bindingPairs pairs = true) :
    ∃ nested, Eval.nestedLets pairs body = some nested ∧
      (Bridges.ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
        some (.silent (allocator, ⟨world, {scope with frontier :=
          (replace control (.evaluate nested destination :: older), context, origins) :: pending} :: parents⟩)) := by
  obtain ⟨nested, lowered⟩ := (bindingPairs_iff_lowering pairs body).mp admitted
  exact ⟨nested, lowered, Bridges.ScopedQuerySource.sequence_entry policy program allocator world scope parents
    control context origins pending pairs body nested destination older frontier atGoal lowered⟩

theorem missing_else_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (condition yes destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .evaluate (.expression [.symbol "if", condition, yes]) destination :: older) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world, {scope with frontier :=
        (replace control (.evaluate condition (.var (freshName control 0)) ::
          .branch (.var (freshName control 0)) yes (.expression [.symbol "empty"]) destination :: older),
          context, origins) :: pending} :: parents⟩) := by
  have localStep : Source.Step policy program (⟨world, control, context⟩ : Cursor Context)
      (.silent ⟨world, replace control (.evaluate condition (.var (freshName control 0)) ::
        .branch (.var (freshName control 0)) yes (.expression [.symbol "empty"]) destination :: older), context⟩) :=
    .expanded _ destination older _ atGoal (by simp [Source.scopedForm])
      (.conditionalWithoutElse condition yes)
  exact Source.source_step_scope policy program allocator world scope parents control context origins pending
    frontier _ localStep

namespace Controls

theorem ordered_binding_lowering :
    Eval.nestedLets
      [.expression [.var "x", .symbol "first"], .expression [.var "y", .symbol "second"]]
      (.var "x") =
      some (.expression [.symbol "let", .var "x", .symbol "first",
        .expression [.symbol "let", .var "y", .symbol "second", .var "x"]]) := rfl

theorem malformed_pair_is_not_an_admitted_sequence :
    bindingPairs [.expression [.var "x"]] = false ∧
      Eval.nestedLets [.expression [.var "x"]] (.var "x") = none := ⟨rfl, rfl⟩

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.SequenceSource
