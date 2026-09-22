import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLRetainedInputTransport
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLRetainedInputsControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLRetainedCompilationControls

/-!
# Actual binder routing and distinct whole-plan substitutions

The selected introduction and elimination refinements are existing clients.
The primitive equations inspect actual compiler input functions. Whole-tree
transport retains a proof hypothesis through two binders and substitutes it
differently; no claim about typing arbitrary native substitutions is made.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputTransportControls

open Mettapedia.Logic Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler ProofSearch ProofObligations
open Mettapedia.TypeTheory.IndexedPolynomial
open HOL.UniformListInduction PolynomialHOLRetainedInputs
open PolynomialHOLRetainedInputTransport

namespace Introductions

open PolynomialHOLRetainedInputsControls

def childSubstitution : ChildSubstitution methods routing := by
  intro index route target sigma
  rcases index with ⟨goal, scope, objects, hypotheses⟩
  cases route <;> exact fun _ => ⟨target + 1, liftSub sigma⟩

theorem routing_square : RoutingSquare methods routing childSubstitution := by
  intro index route target sigma premiseIndex
  rcases index with ⟨goal, scope, objects, hypotheses⟩
  cases route with
  | implication antecedent conclusion code represented =>
      apply Sigma.ext
      · rfl
      apply heq_of_eq
      apply Prod.ext
      · funext index
        exact subst_liftSub_wk sigma (objects index)
      · funext index
        refine Fin.cases ?_ (fun prior => ?_) index
        · rfl
        · exact subst_liftSub_wk sigma (hypotheses prior)
  | universal body =>
      apply Sigma.ext
      · rfl
      apply heq_of_eq
      apply Prod.ext
      · funext index
        refine Fin.cases ?_ (fun prior => ?_) index
        · rfl
        · exact subst_liftSub_wk sigma (objects prior)
      · funext index
        exact subst_liftSub_wk sigma _

def root : Index BaseSort Symbol :=
  ⟨⟨[], [premise], .all (σ := count) (.imp premise premise)⟩,
    1, Fin.elim0, fun _ => .var 0⟩

def outer : Method root.1 := .universal (.imp premise premise)
def middle := (inputMethods methods routing root outer).query ⟨0⟩
def inner : Method middle.1 := .implication premise premise _ rfl
def leafIndex := (inputMethods methods routing middle inner).query ⟨0⟩

def older : Receipt signature proofName operations leafIndex :=
  ⟨HOL.ProofSyntax.hyp (Const := Symbol) (Δ := [premise, premise]) 1,
    (.var 2 : Tower.Tm 3), rfl⟩

def plan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes () root :=
  Free.node _ outer (fun _ => Free.node _ inner (fun _ => Free.pure _ older))

def first : Sub Tower.Head 1 2 := fun _ => .var 0
def second : Sub Tower.Head 1 2 := fun _ => .var 1

noncomputable def moved (sigma : Sub Tower.Head 1 2) :=
  transport methods routing childSubstitution routing_square
    (receiptAction signature proofName operations UniformList.rawOperations_natural)
    () root plan 2 sigma

noncomputable def result (sigma : Sub Tower.Head 1 2) :=
  assemblePlan methods routing signature proofName operations assembly
    (fun _ _ receipt => receipt) () (moveIndex root sigma) (moved sigma)

theorem actual_substitution_square (sigma : Sub Tower.Head 1 2) :
    (result sigma).2.1 = subst sigma (.lam (.lam (.var 2)) : Tower.Tm 1) :=
  assembly_substitution methods routing childSubstitution routing_square
    signature proofName operations UniformList.rawOperations_natural assembly plan 2 sigma

theorem first_output : (result first).2.1 = (.lam (.lam (.var 2)) : Tower.Tm 2) := by
  rw [actual_substitution_square]
  rfl

theorem second_output : (result second).2.1 = (.lam (.lam (.var 3)) : Tower.Tm 2) := by
  rw [actual_substitution_square]
  rfl

theorem outputs_differ : (result first).2.1 ≠ (result second).2.1 := by
  rw [first_output, second_output]
  intro impossible
  cases impossible

theorem entire_source_tree_preserved (sigma : Sub Tower.Head 1 2) :
    sourceTree methods routing (fun _ _ receipt => receipt.1) () (moveIndex root sigma)
      (moved sigma) = sourceTree methods routing (fun _ _ receipt => receipt.1) () root plan :=
  receipt_source_tree methods routing childSubstitution routing_square
    signature proofName operations UniformList.rawOperations_natural plan 2 sigma

/-- A real method node contains a retained inner method plan as its hole. -/
def nestedPlan : (PolynomialPlans.polynomial (inputMethods methods routing)).Free
    ((PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes) () root :=
  Free.node _ outer (fun _ => Free.pure _
    (Free.node _ inner (fun _ => Free.pure _ older)))

theorem nested_join_is_original : Free.join _ nestedPlan = plan := rfl

theorem actual_nested_filling_square (sigma : Sub Tower.Head 1 2) :
    moved sigma = Free.join _
      (transport methods routing childSubstitution routing_square
        (fun base index target childSigma innerPlan =>
          transport methods routing childSubstitution routing_square
            (receiptAction signature proofName operations UniformList.rawOperations_natural)
            base index innerPlan target childSigma)
        () root nestedPlan 2 sigma) :=
  transport_join methods routing childSubstitution routing_square
    (receiptAction signature proofName operations UniformList.rawOperations_natural)
    nestedPlan 2 sigma

theorem new_binders_are_not_substituted (sigma : Sub Tower.Head 1 2) :
    liftSub (liftSub sigma) (0 : Fin 3) = (.var 0 : Tower.Tm 4) ∧
      liftSub (liftSub sigma) (1 : Fin 3) = (.var 1 : Tower.Tm 4) := ⟨rfl, rfl⟩

theorem old_input_follows_actual_substitution :
    liftSub (liftSub first) (2 : Fin 3) = (.var 2 : Tower.Tm 4) ∧
      liftSub (liftSub second) (2 : Fin 3) = (.var 3 : Tower.Tm 4) := ⟨rfl, rfl⟩

theorem wrong_context_output_rejected :
    compile signature proofName operations (result first).1
      (moveIndex root second).2.2.1 (moveIndex root second).2.2.2 ≠
      some (.lam (.lam (.var 2)) : Tower.Tm 2) := by
  have sourceSame : (result first).1 =
      HOL.ProofSyntax.allI (HOL.ProofSyntax.impI
        (HOL.ProofSyntax.hyp (Const := Symbol) (Δ := [premise, premise]) 1)) := by
    have firstTree := entire_source_tree_preserved first
    have assembled := assemble_source methods routing signature proofName operations assembly
      (fun _ _ receipt => receipt) (moved first)
    have projected := congrArg
      (Free.fold (PolynomialPlans.polynomial methods) (fun _ _ proof => proof)
        (PolynomialPlans.reconstruction methods) () root.1) firstTree
    exact assembled.trans ((reconstruct_sourceTree methods routing
      (Holes := Holes)
      (fun _ _ receipt => receipt.1) (moved first)).symm.trans
      (projected.trans (reconstruct_sourceTree methods routing
        (Holes := Holes)
        (fun _ _ receipt => receipt.1) plan)))
  rw [sourceSame]
  intro impossible
  cases impossible

end Introductions

namespace Eliminations

open PolynomialHOLRetainedCompilationControls

/-- Existing elimination methods retain all parent inputs at each child. -/
def routing : Routing methods := by
  intro goal route input
  cases route with
  | implication antecedent conclusion =>
      rintro ⟨position⟩
      refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail)
        position <;> exact input
  | universal body argument code represented => exact fun _ => input

def childSubstitution : ChildSubstitution methods routing := by
  intro index route target sigma
  rcases index with ⟨goal, scope, objects, hypotheses⟩
  cases route with
  | implication antecedent conclusion =>
      rintro ⟨position⟩
      refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail)
        position <;> exact ⟨target, sigma⟩
  | universal body argument code represented => exact fun _ => ⟨target, sigma⟩

theorem routing_square : RoutingSquare methods routing childSubstitution := by
  intro index route target sigma premiseIndex
  rcases index with ⟨goal, scope, objects, hypotheses⟩
  cases route with
  | implication antecedent conclusion =>
      rcases premiseIndex with ⟨position⟩
      refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail)
        position <;> rfl
  | universal body argument code represented => rfl

end Eliminations

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputTransportControls
