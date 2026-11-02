import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Crossing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SafetyControls

/-!
# Local rebinding and shared output arguments use the same unifier

The controls start after expression evaluation: the outer argument is 5 and
the computed value is 6. Lexical identity permits a fresh local to hold 6;
crossing asks whether the already constrained outer variable can also be 6.
The latter fails without changing the unification mechanism.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CrossingControls

open Mettapedia.Logic.LP

abbrev signature := Controls.signature.withVars (ScopedVar Nat ⊕ Nat)
abbrev A := FirstOrder.action signature

def caller : signature.vars := .inr 0
def localName : signature.vars := Crossing.nameAt 7 none [0] 0
def crossedName : signature.vars := Crossing.nameAt 7 (some [0]) [0] 0

def lexicalEquations : EquationStore (Term signature) :=
  [(.var caller, .const 5), (.var localName, .const 6)]

def crossingEquations : EquationStore (Term signature) :=
  [(.var caller, .const 5), (.var crossedName, .const 6)]

def lexicalAnswer : Subst signature
  | .inr 0 => .const 5
  | .inl ⟨7, 0⟩ => .const 6
  | name => .var name

theorem lexical_rebinding_is_consistent : A.Consistent lexicalEquations := by
  refine ⟨lexicalAnswer, ?_⟩
  intro equation member
  simp only [lexicalEquations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem lexical_rebinding_keeps_outer_and_inner_distinct :
    lexicalAnswer.applyTerm (.var caller) = .const 5 ∧
    lexicalAnswer.applyTerm (.var localName) = .const 6 := ⟨rfl, rfl⟩

theorem crossed_rebinding_refuses_conflicting_values : ¬ A.Consistent crossingEquations := by
  rintro ⟨answer, solves⟩
  have first : answer caller = .const 5 := solves (.var caller, .const 5) (by simp [crossingEquations])
  have second : answer caller = .const 6 := by
    have same : crossedName = caller := rfl
    exact same ▸ solves (.var crossedName, .const 6) (by simp [crossingEquations])
  have impossible : (Term.const (σ := signature) 5) = .const 6 := first.symm.trans second
  cases impossible

theorem same_unifier_accepts_lexical_rebinding : ∃ answer, unifyTotal lexicalEquations = some answer :=
  (FirstOrder.accepted_iff_consistent (signature := signature) _).mpr lexical_rebinding_is_consistent

theorem same_unifier_refuses_crossed_rebinding : unifyTotal crossingEquations = none :=
  (FirstOrder.refused_iff_inconsistent (signature := signature) _).mpr
    crossed_rebinding_refuses_conflicting_values

def outputAnswer : Subst signature := Subst.single caller (.const 7)

theorem crossed_unbound_output_is_consistent :
    A.Consistent [(Term.var crossedName, .const 7)] := by
  refine ⟨outputAnswer, ?_⟩
  intro equation member
  have same : equation = (Term.var (σ := signature) crossedName, Term.const (σ := signature) 7) := by
    simpa using member
  subst equation
  rfl

theorem output_binding_reaches_the_caller :
    outputAnswer.applyTerm (.var caller) = .const 7 := by
  exact Subst.single_eq caller (.const 7)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CrossingControls
