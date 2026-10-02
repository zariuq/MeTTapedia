import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Free operations and bounded resumptions

An operation has its own response type. The free computation is Mathlib's
W-type for return leaves and operation nodes; no equation identifies duplicate
choices. Handlers are folds, and sequencing substitutes return leaves.

Recursive execution is a coalgebra, not a purported finite tree containing an
infinite run. Its finite unfolding retains the complete state at open leaves.
The substitution law for two budgets preserves those leaves and every pending
response continuation. A state may include a heap, shared choices and receipts;
this algebra does not erase or duplicate those components.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ResumptionAlgebra

universe uOp uResponse uAnswer uOther uResult uState

abbrev signature (Operation : Type uOp) (Response : Operation → Type uResponse)
    (Answer : Type uAnswer) : PFunctor where
  A := Answer ⊕ Operation
  B := fun shape => match shape with
    | .inl _ => PEmpty
    | .inr operation => Response operation

/-- The existing polynomial W-construction, with return and operation shapes. -/
abbrev Computation (Operation : Type uOp) (Response : Operation → Type uResponse)
    (Answer : Type uAnswer) := (signature Operation Response Answer).W

variable {Operation : Type uOp} {Response : Operation → Type uResponse}
  {Answer : Type uAnswer} {Other : Type uOther} {Result : Type uResult}

def pure (answer : Answer) : Computation Operation Response Answer :=
  WType.mk (.inl answer) PEmpty.elim

def perform (operation : Operation)
    (next : Response operation → Computation Operation Response Answer) :
    Computation Operation Response Answer := WType.mk (.inr operation) next

/-- Interpret the free construction by a return map and an operation algebra. -/
def fold (onReturn : Answer → Result)
    (onOperation : (operation : Operation) → (Response operation → Result) → Result) :
    Computation Operation Response Answer → Result :=
  WType.elim Result fun node =>
    match node with
    | ⟨.inl answer, _⟩ => onReturn answer
    | ⟨.inr operation, next⟩ => onOperation operation next

@[simp] theorem fold_pure (onReturn : Answer → Result)
    (onOperation : (operation : Operation) → (Response operation → Result) → Result)
    (answer : Answer) :
    fold onReturn onOperation (pure answer) = onReturn answer := rfl

@[simp] theorem fold_perform (onReturn : Answer → Result)
    (onOperation : (operation : Operation) → (Response operation → Result) → Result)
    (operation : Operation)
    (next : Response operation → Computation Operation Response Answer) :
    fold onReturn onOperation (perform operation next) =
      onOperation operation (fun response => fold onReturn onOperation (next response)) := rfl

/-- The algebra equations determine the handler on every free computation. -/
theorem fold_unique (onReturn : Answer → Result)
    (onOperation : (operation : Operation) → (Response operation → Result) → Result)
    (handler : Computation Operation Response Answer → Result)
    (returns : ∀ answer, handler (pure answer) = onReturn answer)
    (operations : ∀ operation next, handler (perform operation next) =
      onOperation operation (fun response => handler (next response)))
    (computation : Computation Operation Response Answer) :
    handler computation = fold onReturn onOperation computation := by
  induction computation with
  | mk shape next ih =>
      cases shape with
      | inl answer =>
          have empty : next = PEmpty.elim := by funext response; exact response.elim
          subst next
          exact returns answer
      | inr operation =>
          change handler (perform operation next) =
            onOperation operation (fun response => fold onReturn onOperation (next response))
          exact (operations operation next).trans
            (congrArg (onOperation operation) (funext ih))

def bind (computation : Computation Operation Response Answer)
    (next : Answer → Computation Operation Response Other) :
    Computation Operation Response Other := fold next perform computation

@[simp] theorem pure_bind (answer : Answer)
    (next : Answer → Computation Operation Response Other) :
    bind (pure answer) next = next answer := rfl

@[simp] theorem perform_bind (operation : Operation)
    (response : Response operation → Computation Operation Response Answer)
    (next : Answer → Computation Operation Response Other) :
    bind (perform operation response) next =
      perform operation (fun value => bind (response value) next) := rfl

@[simp] theorem bind_pure (computation : Computation Operation Response Answer) :
    bind computation pure = computation := by
  induction computation with
  | mk shape next ih =>
      cases shape with
      | inl answer =>
          have empty : next = PEmpty.elim := by funext response; exact response.elim
          subst next
          rfl
      | inr operation =>
          change perform operation (fun response => bind (next response) pure) =
            perform operation next
          congr 1
          funext response
          exact ih response

theorem bind_assoc {Final : Type*} (computation : Computation Operation Response Answer)
    (first : Answer → Computation Operation Response Other)
    (second : Other → Computation Operation Response Final) :
    bind (bind computation first) second =
      bind computation (fun answer => bind (first answer) second) := by
  induction computation with
  | mk shape next ih =>
      cases shape with
      | inl answer => rfl
      | inr operation =>
          change perform operation (fun response => bind (bind (next response) first) second) =
            perform operation (fun response => bind (next response)
              (fun answer => bind (first answer) second))
          congr 1
          funext response
          exact ih response

/-- Handler fusion needs precisely preservation of the operation algebra. -/
theorem fold_fusion {Target : Type*} (onReturn : Answer → Result)
    (onOperation : (operation : Operation) → (Response operation → Result) → Result)
    (onTarget : (operation : Operation) → (Response operation → Target) → Target)
    (readout : Result → Target)
    (preserves : ∀ operation next,
      readout (onOperation operation next) =
        onTarget operation (fun response => readout (next response)))
    (computation : Computation Operation Response Answer) :
    readout (fold onReturn onOperation computation) =
      fold (fun answer => readout (onReturn answer)) onTarget computation := by
  apply fold_unique _ _ (fun tree => readout (fold onReturn onOperation tree))
  · intro answer; rfl
  · intro operation next
    exact preserves operation (fun response => fold onReturn onOperation (next response))

/-- One recursive observation: a returned answer, or an operation whose response
determines the next full state. Zero-response operations express failure. -/
inductive View (Operation : Type uOp) (Response : Operation → Type uResponse)
    (Answer : Type uAnswer) (State : Type uState) where
  | returned (answer : Answer)
  | request (operation : Operation) (next : Response operation → State)

variable {State : Type uState}

/-- Each open leaf retains its state; recursive or silent work is not discarded. -/
def unfold (observe : State → View Operation Response Answer State) :
    Nat → State → Computation Operation Response (Answer ⊕ State)
  | 0, state => pure (.inr state)
  | fuel + 1, state =>
      match observe state with
      | .returned answer => pure (.inl answer)
      | .request operation next =>
          perform operation (fun response => unfold observe fuel (next response))

/-- Continue only open leaves, without restarting completed leaves. -/
def resume (observe : State → View Operation Response Answer State) (fuel : Nat) :
    Answer ⊕ State → Computation Operation Response (Answer ⊕ State)
  | .inl answer => pure (.inl answer)
  | .inr state => unfold observe fuel state

/-- Exact residual substitution is the resumption law of the free construction. -/
theorem unfold_add (observe : State → View Operation Response Answer State)
    (first second : Nat) (state : State) :
    unfold observe (first + second) state =
      bind (unfold observe first state) (resume observe second) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, unfold, pure_bind, resume]
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [unfold]
      cases observed : observe state with
      | returned answer => rfl
      | request operation next =>
          simp only [perform_bind]
          congr 1
          funext response
          exact ih (next response)

end Mettapedia.GSLT.Dynamics.ResumptionAlgebra
