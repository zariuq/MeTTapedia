import Mettapedia.TypeTheory.IndexedPolynomialInterpretation

/-!
# An indexed method expanded into two work steps

One source constructor advances the index twice. Its implementation is two
target constructors, with the same outstanding child at its original index.
Reconstruction into bounded naturals agrees for every plan. A type-correct
target algebra that forgets the increments fails the semantic comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.InterpretationControls

inductive ProofMethod : Nat → Type
  | advanceTwo (n : Nat) : ProofMethod (n + 2)

inductive WorkStep : Nat → Type
  | advanceOne (n : Nat) : WorkStep (n + 1)

abbrev proofMethods : IndexedPolynomial Unit (fun _ => Nat) where
  Shape := fun _ n => ProofMethod n
  Position := fun _ => Unit
  next := fun s _ => match s with | .advanceTwo n => n

abbrev workSteps : IndexedPolynomial Unit (fun _ => Nat) where
  Shape := fun _ n => WorkStep n
  Position := fun _ => Unit
  next := fun s _ => match s with | .advanceOne n => n

/-- A concrete two-step template with one hole at its source child's index. -/
def expansionTemplate : MethodTemplates proofMethods workSteps := by
  intro b i s
  cases s with
  | advanceTwo n =>
      exact Free.node workSteps (.advanceOne (n + 1)) (fun _ =>
        Free.node workSteps (index := n + 1) (.advanceOne n)
          (fun _ => Free.pure workSteps ⟨(), rfl⟩))

/-- Substitution compatibility is derived from the template construction. -/
noncomputable def expand : PlanInterpretation proofMethods workSteps :=
  MethodTemplates.interpretation expansionTemplate

theorem expands_to_two_steps {H : Unit → Nat → Type} (n : Nat)
    (child : proofMethods.Free H () n) :
    expand.run () (n + 2) (Free.node proofMethods (.advanceTwo n) (fun _ => child)) =
      Free.node workSteps (.advanceOne (n + 1)) (fun _ =>
        Free.node workSteps (index := n + 1) (.advanceOne n)
          (fun _ => expand.run () n child)) := rfl

abbrev Result (_ : Unit) (n : Nat) := Fin (n + 1)

def proofResult : proofMethods.Algebra Result where
  act := by
    intro b i input
    rcases input with ⟨s, children⟩
    cases s
    exact (children ()).succ.succ

def workResult : workSteps.Algebra Result where
  act := by
    intro b i input
    rcases input with ⟨s, children⟩
    cases s
    exact (children ()).succ

/-- Semantic agreement is proved for arbitrary source plans and typed holes. -/
theorem reconstruct_expansion {H : Unit → Nat → Type}
    (fill : ∀ b n, H b n → Result b n) {b : Unit} {n : Nat}
    (plan : proofMethods.Free H b n) :
    Free.fold workSteps fill workResult b n (expand.run b n plan) =
      Free.fold proofMethods fill proofResult b n plan := by
  apply expand.reconstruct proofResult workResult (fun _ _ value => value) fill fill
  · intros; rfl
  · intro b i s values plans ih
    cases s with
    | advanceTwo n =>
        change (Free.fold workSteps fill workResult b n (plans ())).succ.succ =
          (values ()).succ.succ
        rw [ih ()]

/-- A real outstanding obligation at index two, not a closed constant tree. -/
def examplePlan (input : Fin 3) : proofMethods.Free Result () 4 :=
  Free.node proofMethods (.advanceTwo 2) (fun _ => Free.pure proofMethods input)

theorem first_result :
    (Free.fold workSteps (fun _ _ value => value) workResult () 4
      (expand.run () 4 (examplePlan 0))).val = 2 := rfl

theorem second_result :
    (Free.fold workSteps (fun _ _ value => value) workResult () 4
      (expand.run () 4 (examplePlan 1))).val = 3 := rfl

theorem different_inputs_remain_different :
    Free.fold workSteps (fun _ _ value => value) workResult () 4
      (expand.run () 4 (examplePlan 0)) ≠
    Free.fold workSteps (fun _ _ value => value) workResult () 4
      (expand.run () 4 (examplePlan 1)) := by
  intro same
  have values := congrArg Fin.val same
  change 2 = 3 at values
  contradiction

/-- Enlarging a bound without incrementing the value is well typed but wrong
for this source method's meaning. Typing alone cannot discharge reconstruction. -/
def wrongWorkResult : workSteps.Algebra Result where
  act := by
    intro b i input
    rcases input with ⟨s, children⟩
    cases s
    exact (children ()).castSucc

theorem wrong_reconstruction_rejected :
    Free.fold workSteps (fun _ _ value => value) wrongWorkResult () 4
      (expand.run () 4 (examplePlan 0)) ≠
    Free.fold proofMethods (fun _ _ value => value) proofResult () 4
      (examplePlan 0) := by
  intro same
  have values := congrArg Fin.val same
  change 0 = 2 at values
  contradiction

#print axioms reconstruct_expansion
#print axioms different_inputs_remain_different
#print axioms wrong_reconstruction_rejected

end Mettapedia.TypeTheory.IndexedPolynomial.InterpretationControls
