import Mettapedia.Logic.CertificateConservativeExtension
import Mettapedia.UniversalAlgebra.Certificate
import Mettapedia.UniversalAlgebra.ConservativeExtension

/-!
# Simultaneous substitution on equational replay certificates

Simultaneous term substitution acts structurally on explicit equational rule
witnesses and their derivation trees.  The action preserves successful replay,
the physical tree shape, and node count while substituting the root
conclusion.  Failed replay is not reflected: substitution may identify terms
that were previously distinct.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Mettapedia.Logic

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]
variable {system : EquationSystem S}

namespace EquationalRuleWitness

/-- Simultaneously substitute every term carried by one explicit rule
witness.  For an equation-system instance, substitutions compose. -/
def instantiate (substitution : Nat → Term S) :
    EquationalRuleWitness system → EquationalRuleWitness system
  | .systemInstance occurrence instanceSubstitution =>
      .systemInstance occurrence
        (fun index => (instanceSubstitution index).subst substitution)
  | .refl term =>
      .refl (term.subst substitution)
  | .symm left right =>
      .symm (left.subst substitution) (right.subst substitution)
  | .trans left middle right =>
      .trans (left.subst substitution) (middle.subst substitution)
        (right.subst substitution)
  | .congruence operation left right =>
      .congruence operation
        (fun position => (left position).subst substitution)
        (fun position => (right position).subst substitution)

/-- A successfully recognized rule instance remains recognized after
simultaneous substitution of its premises and conclusion. -/
theorem isInstance_instantiate_of_true
    (substitution : Nat → Term S)
    (witness : EquationalRuleWitness system)
    (premises : List (Equation S)) (conclusion : Equation S)
    (accepted : witness.isInstance premises conclusion = true) :
    (witness.instantiate substitution).isInstance
      (premises.map fun equation => equation.subst substitution)
      (conclusion.subst substitution) = true := by
  cases witness with
  | systemInstance occurrence instanceSubstitution =>
      simp only [instantiate, isInstance, decide_eq_true_eq] at accepted ⊢
      rcases accepted with ⟨rfl, rfl⟩
      constructor
      · rfl
      · simp only [Equation.subst, Term.subst_subst]
  | refl term =>
      simp only [instantiate, isInstance, decide_eq_true_eq] at accepted ⊢
      rcases accepted with ⟨rfl, rfl⟩
      simp [Equation.subst]
  | symm left right =>
      simp only [instantiate, isInstance, decide_eq_true_eq] at accepted ⊢
      rcases accepted with ⟨rfl, rfl⟩
      simp [Equation.subst]
  | trans left middle right =>
      simp only [instantiate, isInstance, decide_eq_true_eq] at accepted ⊢
      rcases accepted with ⟨rfl, rfl⟩
      simp [Equation.subst]
  | congruence operation left right =>
      simp only [instantiate, isInstance, decide_eq_true_eq] at accepted ⊢
      rcases accepted with ⟨rfl, rfl⟩
      constructor
      · rw [List.map_ofFn]
        congr 1
      · simp [Equation.subst]

end EquationalRuleWitness

namespace EquationalCertificate

/-- Apply simultaneous term substitution to every conclusion and explicit
rule witness in an equational derivation tree. -/
def instantiate (substitution : Nat → Term S) :
    Derivation (Equation S) (EquationalRuleWitness system) →
      Derivation (Equation S) (EquationalRuleWitness system)
  | .node conclusion witness n children =>
      .node (conclusion.subst substitution)
        (witness.instantiate substitution) n
        (fun position => instantiate substitution (children position))

omit [DecidableEq S.Operation] in
@[simp] theorem instantiate_concl
    (substitution : Nat → Term S)
    (certificate : Derivation (Equation S) (EquationalRuleWitness system)) :
    (instantiate substitution certificate).concl =
      certificate.concl.subst substitution := by
  cases certificate
  rfl

omit [DecidableEq S.Operation] in
@[simp] theorem instantiate_nodeCount
    (substitution : Nat → Term S)
    (certificate : Derivation (Equation S) (EquationalRuleWitness system)) :
    (instantiate substitution certificate).nodeCount = certificate.nodeCount := by
  induction certificate with
  | node conclusion witness n children ih =>
      simp only [instantiate, Derivation.nodeCount_node]
      congr 1
      exact Finset.sum_congr rfl fun position _member => ih position

/-- Structural substitution preserves every successful replay. -/
theorem instantiate_valid_of_valid
    (substitution : Nat → Term S) :
    ∀ certificate :
        Derivation (Equation S) (EquationalRuleWitness system),
      certificate.valid (equationalRuleInterface system) = true →
        (instantiate substitution certificate).valid
          (equationalRuleInterface system) = true := by
  intro certificate
  induction certificate with
  | node conclusion witness n children ih =>
      intro accepted
      simp only [instantiate, Derivation.valid, Bool.and_eq_true, List.all_eq_true,
        List.forall_mem_ofFn_iff, id] at accepted ⊢
      constructor
      · have root := witness.isInstance_instantiate_of_true substitution
          (List.ofFn fun position => (children position).concl)
          conclusion accepted.1
        change (witness.instantiate substitution).isInstance
          (List.ofFn fun position =>
            (instantiate substitution (children position)).concl)
          (conclusion.subst substitution) = true
        have premiseListsEqual :
            (List.ofFn fun position =>
              (instantiate substitution (children position)).concl) =
              (List.ofFn fun position => (children position).concl).map
                (fun equation => equation.subst substitution) := by
          rw [List.map_ofFn]
          congr 1
          funext position
          exact instantiate_concl substitution (children position)
        rw [premiseListsEqual]
        exact root
      · intro position
        exact ih position (accepted.2 position)

/-- Substitute an already accepted certificate while retaining its replay
evidence and its exact resulting conclusion. -/
def instantiateAccepted
    (substitution : Nat → Term S) {equation : Equation S}
    (certificate : AcceptedCertificate
      (equationalRuleInterface system) equation) :
    AcceptedCertificate (equationalRuleInterface system)
      (equation.subst substitution) := by
  let raw : Derivation (Equation S) (EquationalRuleWitness system) :=
    certificate.certificate
  have rawAccepted : raw.valid (equationalRuleInterface system) = true :=
    certificate.accepted
  have rawConcludes : raw.concl = equation := certificate.concludes
  exact
    { certificate := instantiate substitution raw
      accepted := instantiate_valid_of_valid substitution raw rawAccepted
      concludes := (instantiate_concl substitution raw).trans
        (congrArg (fun result => result.subst substitution) rawConcludes) }

@[simp] theorem instantiateAccepted_nodeCount
    (substitution : Nat → Term S) {equation : Equation S}
    (certificate : AcceptedCertificate
      (equationalRuleInterface system) equation) :
    (instantiateAccepted substitution certificate).nodeCount =
      certificate.nodeCount :=
  instantiate_nodeCount substitution certificate.certificate

end EquationalCertificate

end Mettapedia.UniversalAlgebra
