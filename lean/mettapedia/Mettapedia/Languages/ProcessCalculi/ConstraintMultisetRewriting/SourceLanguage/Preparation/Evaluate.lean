import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Services

/-!
# Direct evaluation of one source alternative

An accepted reduction produces the next world and an ordered list of
replies. Its certificate is a move of the source semantics. Empty
replies and unavailable reductions have distinct meanings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Storage : Type}

namespace Evaluation

structure Evaluator (κ : Keys S) {Γ : Ctx S} {star : S.Srt} (D : Discipline S Γ star) (Storage : Type) where
  solver : Solver κ Γ star
  checks : TypeChecks κ D
  spaces : Spaces κ Γ star Storage
  program : Program κ Γ star D.Ty
  supply : Nat → Term S Γ star

variable {D : Discipline S Γ star} (machine : Evaluator κ D Storage)

structure Reply (world : ExecutionWorld Storage) (branch : Branch κ Γ star D.Ty) where
  world' : ExecutionWorld Storage
  branches : List (Branch κ Γ star D.Ty)
  sound : Move D machine.program machine.supply (world.source machine.spaces) branch
    (world'.source machine.spaces) (branches : Multiset _)

/-- Following a successful value uses the next source frame. The remaining
frames, and any still pending cells, stay with the branch. -/
def resume (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (value : Data κ Γ star) (frame : Frame κ Γ star D.Ty) (outer : List (Frame κ Γ star D.Ty))
    (cells : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    Option (Reply machine world ⟨knowledge, .value value, frame :: outer, cells⟩) :=
  match frame with
  | .bindTo site pattern body =>
    let opening := openAt κ site world.scope
    some ⟨world.fresh,
      [⟨knowledge ++ [(instantiate opening pattern, value)], .eval (body.inst opening), outer, cells⟩],
      .letBind _ _ _ _ _ _ _ _⟩
  | .checkAt kind =>
    match machine.checks.admits knowledge value kind with
    | .isTrue admitted =>
      some ⟨world, [⟨knowledge, .value value, outer, cells⟩], .admitted _ _ _ _ _ _ admitted⟩
    | .isFalse _ =>
      match machine.checks.refuses knowledge value kind with
      | .isTrue refused =>
        some ⟨world, [⟨knowledge, .refused value kind, [], cells⟩], .refused _ _ _ _ _ _ refused⟩
      | .isFalse _ => none
  | .memo cell =>
    some ⟨world, [⟨knowledge ++ [(cell, value)], .value value, outer, cells⟩], .memo _ _ _ _ _ _⟩

def evaluate (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star D.Ty)) (cells : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    (code : Comp κ Γ star D.Ty) → Option (Reply machine world ⟨knowledge, .eval code, frames, cells⟩)
  | .ret datum => some ⟨world, [⟨knowledge, .value datum, frames, cells⟩], .ret _ _ _ _ _⟩
  | .fail => some ⟨world, [], .fail _ _ _ _⟩
  | .choice left right =>
    some ⟨world, [⟨knowledge, .eval left, frames, cells⟩, ⟨knowledge, .eval right, frames, cells⟩],
      .choice _ _ _ _ _ _⟩
  | .let_ site pattern bound body =>
    some ⟨world, [⟨knowledge, .eval bound, .bindTo site pattern body :: frames, cells⟩],
      .letStart _ _ _ _ _ _ _ _⟩
  | .apply call =>
    let candidates := machine.program.equations
    let satisfiable := fun equation : Equation κ Γ star D.Ty =>
      machine.solver.satisfiable (knowledge ++ [(instantiate (copyAt κ world.scope) equation.lhs, call)])
    if found : candidates.any satisfiable = true then
      some ⟨world.fresh, candidates.map (callBranch D world.scope knowledge call frames cells), by
        obtain ⟨equation, member, accepted⟩ := List.any_eq_true.mp found
        exact .apply _ _ _ _ _ ⟨equation, member, (machine.solver.satisfiable_iff _).mp accepted⟩⟩
    else
      some ⟨world, [⟨knowledge, .value call, frames, cells⟩], by
        apply Move.unmatched
        intro equation member solved
        exact found (List.any_eq_true.mpr ⟨equation, member, (machine.solver.satisfiable_iff _).mpr solved⟩)⟩
  | .run text =>
    match machine.solver.principal knowledge with
    | .found θ principal =>
      some ⟨world, [⟨knowledge, .eval (machine.program.reflect (instantiate θ text)), frames, cells⟩],
        .run _ _ _ _ _ θ principal⟩
    | .absent _ => none
  | .query space pattern body =>
    match machine.solver.address knowledge space with
    | .found handle determined =>
      some ⟨world.fresh, (machine.spaces.rows world.storage handle).map fun row =>
        ⟨knowledge ++ rowUse world.scope row pattern, .eval body, frames, cells⟩, by
        rw [← Multiset.map_coe, machine.spaces.rows_exact]
        exact .query _ _ _ _ _ _ _ handle determined⟩
    | .absent _ => none
  | .add space datum body =>
    match machine.solver.address knowledge space with
    | .found handle determined =>
      let next := {world with storage := machine.spaces.insert world.storage handle ⟨datum, knowledge⟩}
      some ⟨next, [⟨knowledge, .eval body, frames, cells⟩], by
        simp only [next, ExecutionWorld.source, machine.spaces.insert_exact]
        exact .add _ _ _ _ _ _ _ handle determined⟩
    | .absent _ => none
  | .remove space datum body =>
    match machine.solver.address knowledge space with
    | .found handle determined =>
      let accepts := fun row : Row κ Γ star =>
        machine.solver.satisfiable (knowledge ++ rowUse world.scope row datum)
      have erasure := machine.spaces.erase_exact world.storage handle accepts
      match result : machine.spaces.erase world.storage handle accepts with
      | some (row, storage) =>
        let next := {world.fresh with storage}
        some ⟨next, [⟨knowledge ++ rowUse world.scope row datum, .eval body, frames, cells⟩], by
          rw [result] at erasure
          obtain ⟨accepted, rest, split, newView⟩ := erasure
          simp only [next, ExecutionWorld.source, ExecutionWorld.fresh, newView]
          exact .remove _ _ _ _ _ _ _ handle determined row rest split
            ((machine.solver.satisfiable_iff _).mp accepted)⟩
      | none =>
        some ⟨world, [⟨knowledge, .eval body, frames, cells⟩], by
          rw [result] at erasure
          apply Move.removeMissing _ _ _ _ _ _ _ handle determined
          intro row member solved
          have rejected := erasure row member
          change machine.solver.satisfiable (knowledge ++ rowUse world.scope row datum) = false at rejected
          change Solvable (knowledge ++ rowUse world.scope row datum) at solved
          rw [(machine.solver.satisfiable_iff _).mpr solved] at rejected
          cases rejected⟩
    | .absent _ => none
  | .new site handle body =>
    let opening := openAt κ site world.scope
    some ⟨world.allocate,
      [⟨knowledge ++ [(instantiate opening handle, Rigid.includeTerm (fam κ) (machine.supply world.handles))],
        .eval (body.inst opening), frames, cells⟩], .new _ _ _ _ _ _ _⟩
  | .check kind code =>
    some ⟨world, [⟨knowledge, .eval code, .checkAt kind :: frames, cells⟩], .checkStart _ _ _ _ _ _⟩
  | .delay site cell suspended body =>
    let opening := openAt κ site world.scope
    some ⟨world.fresh,
      [⟨knowledge, .eval (body.inst opening), frames, (instantiate opening cell, suspended) :: cells⟩],
      .delay _ _ _ _ _ _ _ _⟩
  | .force datum =>
    let selects := fun entry : Data κ Γ star × Comp κ Γ star D.Ty =>
      machine.solver.impliesEquality knowledge datum entry.1
    match findFirst selects cells with
    | .found before (cell, code) after decomposed chosen =>
      some ⟨world, [⟨knowledge, .eval code, .memo cell :: frames, before ++ after⟩], by
        rw [decomposed]
        exact .forcePending _ _ _ _ _ _ _ _ ((machine.solver.impliesEquality_iff _ _ _).mp chosen)⟩
    | .absent missing =>
      some ⟨world, [⟨knowledge, .value datum, frames, cells⟩], by
        apply Move.forceDone
        intro entry member equal
        have rejected := missing entry member
        change machine.solver.impliesEquality knowledge datum entry.1 = false at rejected
        rw [(machine.solver.impliesEquality_iff _ _ _).mpr equal] at rejected
        cases rejected⟩

def reduce (world : ExecutionWorld Storage) :
    (branch : Branch κ Γ star D.Ty) → Option (Reply machine world branch)
  | ⟨knowledge, .eval code, frames, cells⟩ => evaluate machine world knowledge frames cells code
  | ⟨knowledge, .value value, frame :: outer, cells⟩ => resume machine world knowledge value frame outer cells
  | ⟨_, .value _, [], _⟩ | ⟨_, .refused .., _, _⟩ => none

/-- Exact primitive decisions make every source-enabled alternative
reducible. The evaluator may choose a particular legal witness for
reflection, removal, forcing or a type decision. -/
theorem available_of_move {world : ExecutionWorld Storage} {branch : Branch κ Γ star D.Ty}
    {next : World κ Γ star} {branches : Multiset (Branch κ Γ star D.Ty)}
    (moved : Move D machine.program machine.supply (world.source machine.spaces) branch next branches) :
    (reduce machine world branch).isSome = true := by
  generalize world.source machine.spaces = original at moved
  cases moved with
  | ret => rfl
  | apply =>
    simp only [reduce, evaluate]
    split <;> rfl
  | unmatched =>
    simp only [reduce, evaluate]
    split <;> rfl
  | run knowledge _ _ _ θ principal =>
    simp only [reduce, evaluate]
    cases machine.solver.principal knowledge with
    | found => rfl
    | absent missing => exact (missing θ principal).elim
  | letStart => rfl
  | letBind => rfl
  | choice => rfl
  | fail => rfl
  | query knowledge space _ _ _ _ handle determined =>
    simp only [reduce, evaluate]
    cases machine.solver.address knowledge space with
    | found => rfl
    | absent missing => exact (missing handle determined).elim
  | add knowledge space _ _ _ _ handle determined =>
    simp only [reduce, evaluate]
    cases machine.solver.address knowledge space with
    | found => rfl
    | absent missing => exact (missing handle determined).elim
  | remove knowledge space datum _ _ _ handle determined _ _ _ _ =>
    simp only [reduce, evaluate]
    cases machine.solver.address knowledge space with
    | found =>
      dsimp only
      split <;> rfl
    | absent missing => exact (missing handle determined).elim
  | removeMissing knowledge space datum _ _ _ handle determined _ =>
    simp only [reduce, evaluate]
    cases machine.solver.address knowledge space with
    | found =>
      dsimp only
      split <;> rfl
    | absent missing => exact (missing handle determined).elim
  | new => rfl
  | checkStart => rfl
  | admitted knowledge value kind _ _ all =>
    simp only [reduce, resume]
    cases machine.checks.admits knowledge value kind with
    | isTrue => rfl
    | isFalse impossible => exact (impossible all).elim
  | refused knowledge value kind _ _ none =>
    simp only [reduce, resume]
    cases machine.checks.admits knowledge value kind with
    | isTrue => rfl
    | isFalse =>
      cases machine.checks.refuses knowledge value kind with
      | isTrue => rfl
      | isFalse impossible => exact (impossible none).elim
  | delay => rfl
  | forcePending =>
    simp only [reduce, evaluate]
    split <;> rfl
  | forceDone =>
    simp only [reduce, evaluate]
    split <;> rfl
  | memo => rfl

theorem reduce_none_iff {world : ExecutionWorld Storage} {branch : Branch κ Γ star D.Ty} :
    reduce machine world branch = none ↔
      ¬ ∃ next branches, Move D machine.program machine.supply (world.source machine.spaces) branch next branches := by
  constructor
  · intro stopped
    rintro ⟨_, _, moved⟩
    have proceeds := available_of_move machine moved
    rw [stopped] at proceeds
    cases proceeds
  · intro refuses
    cases found : reduce machine world branch with
    | none => rfl
    | some reply => exact (refuses ⟨_, _, reply.sound⟩).elim

end Evaluation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation
