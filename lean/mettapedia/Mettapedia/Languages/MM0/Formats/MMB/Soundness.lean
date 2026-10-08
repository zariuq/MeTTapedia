import Mettapedia.Languages.MM0.Formats.MMB.Statements
import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# Soundness of the MMB machine: expressions

An allocated expression decodes to a kernel preterm: a variable to the
variable at its context position, an application of a term to the curried
application of the term to its decoded arguments. Arguments are allocated
before the application that uses them, so decoding follows strictly smaller
positions; a store violating this decodes to nothing.

A bound variable's rank names it among the bound binders of the statement's
context, which lists the arguments and then the dummies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.Soundness

open Mettapedia.Languages.MM0.Kernel

/-- Decode the expression at a position of the store. -/
def decode (store : List Alloc) (position : Nat) : Option Preterm :=
  match _h : store[position]? with
  | none => none
  | some alloc =>
      match alloc.node with
      | .var index => some (.var index)
      | .app t args =>
          if earlier : ∀ a ∈ args, a < position then
            (args.attach.mapM fun (arg : {a // a ∈ args}) =>
              have : arg.1 < position := earlier arg.1 arg.2
              decode store arg.1).map (Preterm.applyArgs (.term t))
          else none
termination_by position

/-- A successfully decoded application retains its ordered child vector and
the strict pointer decrease used by the retained decoder. -/
theorem decode_application (store : List Alloc) (position term : Nat)
    (arguments : List Nat) (type : ExprType) (expression : Preterm)
    (found : store[position]? = some ⟨.app term arguments, type⟩)
    (decoded : decode store position = some expression) :
    ∃ expressions, arguments.mapM (decode store) = some expressions ∧
      expression = Preterm.applyArgs (.term term) expressions ∧
      ∀ argument ∈ arguments, argument < position := by
  rw [decode, found] at decoded
  dsimp only at decoded
  split at decoded
  · rename_i earlier
    rw [List.mapM_subtype (g := decode store)] at decoded
    · obtain ⟨expressions, argumentsRead, same⟩ := Option.map_eq_some_iff.mp decoded
      exact ⟨expressions, by simpa using argumentsRead, same.symm, earlier⟩
    · intros
      rfl
  · cases decoded

mutual

/-- Decoding one actual source expression preserves all preceding slots and
consumes exactly a command prefix. Saved applications fill their own new
reservation; they do not overwrite an earlier source binding. -/
theorem decodeExpr_source_order (arity : Nat → Option Nat) (arguments fuel : Nat)
    (before after : Statements.Decoding) (commands rest : List UnifyCmd) (expression : Preterm)
    (decoded : Statements.decodeExpr arity arguments fuel before commands = some (expression, after, rest)) :
    ∃ slots consumed, after.slots = before.slots ++ slots ∧ commands = consumed ++ rest ∧ consumed ≠ [] := by
  cases fuel with
  | zero => simp [Statements.decodeExpr] at decoded
  | succ fuel =>
      cases commands with
      | nil => simp [Statements.decodeExpr] at decoded
      | cons command commands =>
          cases command with
          | hyp => simp [Statements.decodeExpr] at decoded
          | ref index =>
              change ((before.slots[index]?).bind id).bind (fun source => some (source, before, commands)) =
                some (expression, after, rest) at decoded
              cases sourceRead : (before.slots[index]?).bind id with
              | none =>
                  rw [sourceRead] at decoded
                  cases decoded
              | some source =>
                  rw [sourceRead, Option.bind_some] at decoded
                  have same := Option.some.inj decoded
                  cases same
                  exact ⟨[], [.ref index], by simp, rfl, by simp⟩
          | dummy sort =>
              have same : (.var (arguments + before.dummies.length),
                  ⟨before.slots ++ [some (.var (arguments + before.dummies.length))], before.dummies ++ [sort]⟩,
                  commands) = (expression, after, rest) := by
                simpa [Statements.decodeExpr] using decoded
              cases same
              exact ⟨[some (.var (arguments + before.dummies.length))], [.dummy sort], rfl, rfl, by simp⟩
          | term term =>
              cases countRead : arity term with
              | none => simp [Statements.decodeExpr, countRead] at decoded
              | some count =>
                  cases children : Statements.decodeExprs arity arguments fuel count before commands with
                  | none => simp [Statements.decodeExpr, countRead, children] at decoded
                  | some value =>
                      rcases value with ⟨expressions, next, remaining⟩
                      have same : (Preterm.applyArgs (.term term) expressions, next, remaining) =
                          (expression, after, rest) := by
                        simpa [Statements.decodeExpr, countRead, children] using decoded
                      obtain ⟨slots, consumed, slotsRead, commandsRead, _⟩ :=
                        decodeExprs_source_order arity arguments fuel count before next commands remaining expressions children
                      cases same
                      exact ⟨slots, .term term :: consumed, slotsRead, by rw [commandsRead]; rfl, by simp⟩
          | termSave term =>
              cases countRead : arity term with
              | none => simp [Statements.decodeExpr, countRead] at decoded
              | some count =>
                  let reserved : Statements.Decoding := { before with slots := before.slots ++ [none] }
                  cases children : Statements.decodeExprs arity arguments fuel count reserved commands with
                  | none => simp [Statements.decodeExpr, countRead, reserved, children] at decoded
                  | some value =>
                      rcases value with ⟨expressions, next, remaining⟩
                      let body := Preterm.applyArgs (.term term) expressions
                      have same : body = expression ∧
                          { next with slots := next.slots.set before.slots.length (some body) } = after ∧
                          remaining = rest := by
                        simpa [Statements.decodeExpr, countRead, reserved, body, children] using decoded
                      obtain ⟨slots, consumed, slotsRead, commandsRead, _⟩ :=
                        decodeExprs_source_order arity arguments fuel count reserved next commands remaining expressions children
                      rcases same with ⟨sameExpression, sameState, sameRest⟩
                      subst expression
                      subst after
                      subst rest
                      refine ⟨some body :: slots, .termSave term :: consumed, ?_, by rw [commandsRead]; rfl, by simp⟩
                      change next.slots.set before.slots.length (some body) = before.slots ++ (some body :: slots)
                      rw [slotsRead]
                      change ((before.slots ++ [none]) ++ slots).set before.slots.length (some body) = _
                      rw [List.append_assoc, List.set_append_right _ _ (Nat.le_refl _)]
                      simp
termination_by fuel

/-- Consecutive source children retain their exact order and preceding
bindings. The prefix is derived from the actual recursive decoder. -/
theorem decodeExprs_source_order (arity : Nat → Option Nat) (arguments fuel count : Nat)
    (before after : Statements.Decoding) (commands rest : List UnifyCmd) (expressions : List Preterm)
    (decoded : Statements.decodeExprs arity arguments fuel count before commands = some (expressions, after, rest)) :
    ∃ slots consumed, after.slots = before.slots ++ slots ∧ commands = consumed ++ rest ∧ count ≤ consumed.length := by
  cases count with
  | zero =>
      have same : ([], before, commands) = (expressions, after, rest) := by
        simpa [Statements.decodeExprs] using decoded
      cases same
      exact ⟨[], [], by simp, rfl, by simp⟩
  | succ count =>
      cases fuel with
      | zero => simp [Statements.decodeExprs] at decoded
      | succ fuel =>
          cases first : Statements.decodeExpr arity arguments fuel before commands with
          | none => simp [Statements.decodeExprs, first] at decoded
          | some value =>
              rcases value with ⟨expression, middle, remaining⟩
              cases others : Statements.decodeExprs arity arguments fuel count middle remaining with
              | none => simp [Statements.decodeExprs, first, others] at decoded
              | some value =>
                  rcases value with ⟨earlier, finish, following⟩
                  have same : (expression :: earlier, finish, following) = (expressions, after, rest) := by
                    simpa [Statements.decodeExprs, first, others] using decoded
                  obtain ⟨firstSlots, firstCommands, firstSlotsRead, firstCommandsRead, firstNonempty⟩ :=
                    decodeExpr_source_order arity arguments fuel before middle commands remaining expression first
                  obtain ⟨otherSlots, otherCommands, otherSlotsRead, otherCommandsRead, countBound⟩ :=
                    decodeExprs_source_order arity arguments fuel count middle finish remaining following earlier others
                  cases same
                  refine ⟨firstSlots ++ otherSlots, firstCommands ++ otherCommands,
                    by rw [otherSlotsRead, firstSlotsRead, List.append_assoc],
                    by rw [firstCommandsRead, otherCommandsRead, List.append_assoc], ?_⟩
                  have firstPositive : 0 < firstCommands.length := List.length_pos_iff.mpr firstNonempty
                  simp only [List.length_append]
                  omega
termination_by fuel

end

/-- Context positions of the bound binders, in rank order. -/
def rankPositions (context : Context) : List Nat :=
  (context.zipIdx.filter fun (binder, _) => match binder with
    | .bound _ => true
    | .regular _ _ => false).map (·.2)

/-- The dependencies of a type, by context position. -/
def positionsOf (context : Context) (deps : Finset Nat) : Finset Nat :=
  deps.image fun rank => (rankPositions context).getD rank rank

end Mettapedia.Languages.MM0.Formats.MMB.Soundness
