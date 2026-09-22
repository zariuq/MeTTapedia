import Mettapedia.Logic.HOL.Embedding.GroundUnaryEquationalChart
import Mettapedia.Logic.HOL.UniformListInduction

/-!
# Equational replay inside the uniform HOL list-induction proof

The base normalizes a mapped empty list's length to zero. The cons step uses
four locally licensed equations and successor congruence. The original HOL
predicate, quantified function, and induction principle remain available.
-/

namespace Mettapedia.Logic.HOL.UniformListInductionChart

open UniformListInduction
open GroundUnaryEquationalChart

local instance : DecidableEq BaseSort
  | .element, .element | .sequence, .sequence | .count, .count => .isTrue rfl
  | .element, .sequence | .element, .count | .sequence, .element
  | .sequence, .count | .count, .element | .count, .sequence =>
      .isFalse (by intro h; cases h)

local instance (τ : Ty BaseSort) : DecidableEq (Symbol τ) := by
  intro a b
  cases a <;> cases b <;> exact .isTrue rfl

variable (Γ : Ctx BaseSort)

abbrev baseChart : Chart Symbol (mapping :: Γ) count where
  atomCount := 3
  unaryCount := 0
  atoms := ![length (map (.var .vz) nil), length nil, .const .zero]
  unary := Fin.elim0

def baseAssumptions : List (Formula Symbol (mapping :: Γ)) :=
  [.eq (length (map (.var .vz) nil)) (length nil), lengthNil]

def baseGoal : Formula Symbol (mapping :: Γ) :=
  .eq (length (map (.var .vz) nil)) (.const .zero)

def baseSystem : UniversalAlgebra.EquationSystem (baseChart Γ).signature :=
  ⟨[(atom (baseChart Γ) 0, atom (baseChart Γ) 1),
    (atom (baseChart Γ) 1, atom (baseChart Γ) 2)]⟩

def baseCertificate : Certificate (baseChart Γ) (baseSystem Γ) :=
  .node (atom (baseChart Γ) 0, atom (baseChart Γ) 2)
    (.trans (atom (baseChart Γ) 0) (atom (baseChart Γ) 1) (atom (baseChart Γ) 2)) 2
    ![.node (atom (baseChart Γ) 0, atom (baseChart Γ) 1)
        (.systemInstance ⟨0, by change 0 < 2; decide⟩ .var) 0 Fin.elim0,
      .node (atom (baseChart Γ) 1, atom (baseChart Γ) 2)
        (.systemInstance ⟨1, by change 1 < 2; decide⟩ .var) 0 Fin.elim0]

theorem base_eligible : eligible (baseChart Γ) 1 (baseGoal Γ) = true :=
  eligible_complete (baseChart Γ) (.atom 0) (.atom 2) (by decide) (by decide)

theorem base_accepted :
    accepts (baseChart Γ) 1 (baseAssumptions Γ) (baseGoal Γ)
      (baseSystem Γ) (baseCertificate Γ) = true := by rfl

theorem base_certificate_nodes : certificateNodes (baseChart Γ) (baseCertificate Γ) = 3 :=
  by rfl

abbrev stepContext := sequence :: element :: mapping :: Γ

def stepFunction : UniformListInduction.Expr (stepContext Γ) mapping :=
  .var (.vs (.vs .vz))

def stepElement : UniformListInduction.Expr (stepContext Γ) element := .var (.vs .vz)
def stepSequence : UniformListInduction.Expr (stepContext Γ) sequence := .var .vz

abbrev stepChart : Chart Symbol (stepContext Γ) count where
  atomCount := 5
  unaryCount := 1
  atoms := ![length (map (stepFunction Γ) (cons (stepElement Γ) (stepSequence Γ))),
    length (cons (.app (stepFunction Γ) (stepElement Γ))
      (map (stepFunction Γ) (stepSequence Γ))),
    length (map (stepFunction Γ) (stepSequence Γ)),
    length (stepSequence Γ), length (cons (stepElement Γ) (stepSequence Γ))]
  unary := fun _ => .const .succ

def stepAssumptions : List (Formula Symbol (stepContext Γ)) :=
  [.eq ((stepChart Γ).atoms 0) ((stepChart Γ).atoms 1),
    .eq ((stepChart Γ).atoms 1) (succ ((stepChart Γ).atoms 2)),
    .eq ((stepChart Γ).atoms 2) ((stepChart Γ).atoms 3),
    .eq ((stepChart Γ).atoms 4) (succ ((stepChart Γ).atoms 3))]

def stepGoal : Formula Symbol (stepContext Γ) :=
  preservesLength (stepFunction Γ) (cons (stepElement Γ) (stepSequence Γ))

def stepSystem : UniversalAlgebra.EquationSystem (stepChart Γ).signature :=
  ⟨[(atom (stepChart Γ) 0, atom (stepChart Γ) 1),
    (atom (stepChart Γ) 1, unary (stepChart Γ) 0 (atom (stepChart Γ) 2)),
    (atom (stepChart Γ) 2, atom (stepChart Γ) 3),
    (atom (stepChart Γ) 4, unary (stepChart Γ) 0 (atom (stepChart Γ) 3))]⟩

private def stepGiven (i : Fin 4) : Certificate (stepChart Γ) (stepSystem Γ) :=
  .node ((stepSystem Γ).equations.get i) (.systemInstance i .var) 0 Fin.elim0

def stepCertificate : Certificate (stepChart Γ) (stepSystem Γ) :=
  let a := atom (stepChart Γ)
  let s := unary (stepChart Γ) 0
  .node (a 0, a 4) (.trans (a 0) (a 1) (a 4)) 2
    ![stepGiven Γ 0,
      .node (a 1, a 4) (.trans (a 1) (s (a 2)) (a 4)) 2
        ![stepGiven Γ 1,
          .node (s (a 2), a 4) (.trans (s (a 2)) (s (a 3)) (a 4)) 2
            ![.node (s (a 2), s (a 3))
                (.congruence (.inr 0) (fun _ => a 2) (fun _ => a 3)) 1
                (fun _ => stepGiven Γ 2),
              .node (s (a 3), a 4) (.symm (a 4) (s (a 3))) 1
                (fun _ => stepGiven Γ 3)]]]

theorem step_eligible : eligible (stepChart Γ) 2 (stepGoal Γ) = true :=
  eligible_complete (stepChart Γ) (.atom 0) (.atom 4) (by decide) (by decide)

/-- Every actual cons-step premise belongs to the independently declared
grammar, including the two successor spines. -/
theorem step_assumptions_eligible (φ : Formula Symbol (stepContext Γ))
    (member : φ ∈ stepAssumptions Γ) : eligible (stepChart Γ) 2 φ = true := by
  simp only [stepAssumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact eligible_complete (stepChart Γ) (.atom 0) (.atom 1) (by decide) (by decide)
  · exact eligible_complete (stepChart Γ) (.atom 1) (.unary 0 (.atom 2))
      (by decide) (by decide)
  · exact eligible_complete (stepChart Γ) (.atom 2) (.atom 3) (by decide) (by decide)
  · exact eligible_complete (stepChart Γ) (.atom 4) (.unary 0 (.atom 3))
      (by decide) (by decide)

theorem step_accepted :
    accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) (stepCertificate Γ) = true := by rfl

theorem step_certificate_nodes : certificateNodes (stepChart Γ) (stepCertificate Γ) = 9 :=
  by rfl

theorem base_reconstruction :
    ExtDerivation Symbol equations (baseGoal Γ) := by
  apply accepts_reconstruct_licensed (baseChart Γ) 1 (baseAssumptions Γ)
    (baseGoal Γ) (baseSystem Γ) (baseCertificate Γ) (base_accepted Γ)
    (ν := fun _ => .const .zero)
  intro φ member
  simp only [baseAssumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact base_obligation (.var .vz)
  · exact .hyp (by simp [equations])

/-- Each backend assumption is derived from a displayed source equation, or is
the actual induction hypothesis. In particular, the cons goal is not supplied
as an assumption to the checker. -/
theorem step_reconstruction :
    ExtDerivation Symbol (preservesLength (stepFunction Γ) (stepSequence Γ) :: equations)
      (stepGoal Γ) := by
  apply accepts_reconstruct_licensed (stepChart Γ) 2 (stepAssumptions Γ)
    (stepGoal Γ) (stepSystem Γ) (stepCertificate Γ) (step_accepted Γ)
    (ν := fun _ => .const .zero)
  have liftEquation {φ : Formula Symbol (stepContext Γ)}
      (h : ExtDerivation Symbol equations φ) :
      ExtDerivation Symbol
        (preservesLength (stepFunction Γ) (stepSequence Γ) :: equations) φ :=
    ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ) h
  intro φ member
  simp only [stepAssumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact liftEquation (.eqAppArg (.const Symbol.length)
      (map_cons_equation (stepFunction Γ) (stepElement Γ) (stepSequence Γ)))
  · exact liftEquation (length_cons_equation
      (.app (stepFunction Γ) (stepElement Γ)) (map (stepFunction Γ) (stepSequence Γ)))
  · exact .hyp (by simp [preservesLength])
  · exact liftEquation (length_cons_equation (stepElement Γ) (stepSequence Γ))

private theorem predicate_step_reconstruction :
    ExtDerivation Symbol equations
      (inductionStep (lengthPredicate (.var .vz :
        UniformListInduction.Expr (mapping :: Γ) mapping))) := by
  apply ExtDerivation.allI
  apply ExtDerivation.allI
  apply ExtDerivation.impI
  simp only [weaken_equations, weaken_lengthPredicate]
  apply predicate_of_equation
  change ExtDerivation Symbol
    (.app (lengthPredicate (stepFunction Γ)) (stepSequence Γ) :: equations) (stepGoal Γ)
  have ih : ExtDerivation Symbol
      (.app (lengthPredicate (stepFunction Γ)) (stepSequence Γ) :: equations)
      (preservesLength (stepFunction Γ) (stepSequence Γ)) :=
    equation_of_predicate (.hyp (by simp))
  exact .impE
    (ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ)
      (.impI (step_reconstruction Γ))) ih

/-- The chart leaves reconstruct the original HOL theorem through the single
predicate-quantified induction principle. The chart does not prove induction. -/
theorem mapLength_via_chart : ExtDerivation Symbol (theory (Γ := Γ)) mapLength := by
  apply ExtDerivation.allI
  simp only [weaken_theory]
  have liftEquation {φ : Formula Symbol (mapping :: Γ)}
      (h : ExtDerivation Symbol equations φ) : ExtDerivation Symbol theory φ :=
    ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ) h
  have base : ExtDerivation Symbol (equations (Γ := mapping :: Γ))
      (preservesLength (.var .vz) nil) :=
    .eqTrans (base_reconstruction Γ) (.eqSymm (.hyp (by simp [equations, lengthNil])))
  have predicateAll := induction_reconstruction (lengthPredicate (.var .vz))
    (Δ := theory) (.hyp (by simp [theory]))
    (predicate_of_equation (liftEquation base))
    (liftEquation (predicate_step_reconstruction Γ))
  apply ExtDerivation.allI
  simp only [weaken_theory]
  apply equation_of_predicate
  have weakened := ExtDerivation.rename (Rename.weaken (σ := sequence)) predicateAll
  have atSequence := ExtDerivation.allE (.var .vz) weakened
  simpa [weakenHyps, weaken, rename, Rename.lift, Rename.weaken, instantiate,
    subst, Subst.single, Subst.lift, lengthPredicate, preservesLength, length, map,
    theory, equations, inductionPrinciple, inductionStep, mapNil, mapCons,
    lengthNil, lengthCons, cons, nil, succ] using atSequence

def alteredStepAssumptions : List (Formula Symbol (stepContext Γ)) :=
  [.eq ((stepChart Γ).atoms 0) ((stepChart Γ).atoms 1),
    .eq ((stepChart Γ).atoms 1) (succ ((stepChart Γ).atoms 2)),
    .eq ((stepChart Γ).atoms 2) ((stepChart Γ).atoms 2),
    .eq ((stepChart Γ).atoms 4) (succ ((stepChart Γ).atoms 3))]

def missingStepAssumptions : List (Formula Symbol (stepContext Γ)) :=
  [.eq ((stepChart Γ).atoms 0) ((stepChart Γ).atoms 1),
    .eq ((stepChart Γ).atoms 1) (succ ((stepChart Γ).atoms 2)),
    .eq ((stepChart Γ).atoms 4) (succ ((stepChart Γ).atoms 3))]

theorem step_backend_valid :
    (stepCertificate Γ).valid (UniversalAlgebra.equationalRuleInterface (stepSystem Γ)) = true :=
  by rfl

/-- An independently valid backend certificate cannot be reused under a
changed induction hypothesis: the source assumption binding fails. -/
theorem altered_assumption_rejected :
    accepts (stepChart Γ) 2 (alteredStepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) (stepCertificate Γ) = false := by rfl

theorem missing_assumption_rejected :
    accepts (stepChart Γ) 2 (missingStepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) (stepCertificate Γ) = false := by rfl

def malformedCertificate : Certificate (stepChart Γ) (stepSystem Γ) :=
  .node (atom (stepChart Γ) 0, atom (stepChart Γ) 4)
    (.refl (atom (stepChart Γ) 0)) 0 Fin.elim0

theorem malformed_certificate_rejected :
    accepts (stepChart Γ) 2 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) (malformedCertificate Γ) = false := by rfl

theorem changed_goal_rejected :
    accepts (stepChart Γ) 2 (stepAssumptions Γ)
      (.eq ((stepChart Γ).atoms 0) ((stepChart Γ).atoms 3))
      (stepSystem Γ) (stepCertificate Γ) = false := by rfl

theorem insufficient_budget_rejected :
    accepts (stepChart Γ) 1 (stepAssumptions Γ) (stepGoal Γ)
      (stepSystem Γ) (stepCertificate Γ) = false := by rfl

theorem induction_outside_chart :
    eligible (stepChart Γ) 2 inductionPrinciple = false := rfl

theorem other_sort_outside_chart :
    eligible (stepChart Γ) 2 (.eq nil nil) = false := rfl

/-- Successful local charts do not remove the induction assumption. This
negative uses the source junk model, whose count sort has only the displayed
equations; it asserts no independence result for stronger count theories. -/
theorem chart_leaves_do_not_replace_induction :
    accepts (baseChart []) 1 (baseAssumptions []) (baseGoal [])
        (baseSystem []) (baseCertificate []) = true ∧
    accepts (stepChart []) 2 (stepAssumptions []) (stepGoal [])
        (stepSystem []) (stepCertificate []) = true ∧
    ¬ ExtDerivation Symbol (equations (Γ := [])) mapLength :=
  ⟨base_accepted [], step_accepted [], equations_do_not_derive_mapLength⟩

#print axioms base_reconstruction
#print axioms step_reconstruction
#print axioms mapLength_via_chart
#print axioms chart_leaves_do_not_replace_induction
#print axioms altered_assumption_rejected
#print axioms malformed_certificate_rejected

end Mettapedia.Logic.HOL.UniformListInductionChart
