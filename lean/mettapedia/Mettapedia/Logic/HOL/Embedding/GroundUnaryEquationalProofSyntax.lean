import Mettapedia.Logic.HOL.Embedding.GroundUnaryEquationalChart
import Mettapedia.Logic.HOL.ProofSyntax

/-!
# Retained reconstruction of an accepted equational chart certificate

Reconstruction recurses on the submitted certificate, not its proposition-valued
soundness theorem. Every selected child is bound to its actual premise position.
Indexed equation-system leaves expand independently supplied proofs of those
equations; symmetry, transitivity and unary congruence become the corresponding
HOL proof constructors. The existing chart checker remains unchanged.
This is structural elaboration, not an injective serialization of every backend
witness field: indexed source leaves expand and nullary congruence is reflexivity.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.GroundUnaryEquationalChart

universe u v

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {τ : Ty Base}

/-- A direct structural interpreter of the actual accepted replay tree. The
license concerns each indexed source equation, not the requested conclusion. -/
def reconstructCertificate (c : Chart Const Γ τ)
    (system : UniversalAlgebra.EquationSystem c.signature) {Δ : List (Formula Const Γ)}
    (licensed : ∀ (i : Fin system.equations.length) ν,
      ProofSyntax Const Δ (formula c ν (system.equations.get i)))
    (certificate : Certificate c system)
    (accepted : certificate.valid (UniversalAlgebra.equationalRuleInterface system) = true)
    (ν : Nat → Term Const Γ τ) : ProofSyntax Const Δ (formula c ν certificate.concl) :=
  match certificate with
  | .node conclusion witness n children => by
      simp only [Derivation.valid, Bool.and_eq_true, List.all_eq_true,
        List.forall_mem_ofFn_iff, id] at accepted
      have ruleAccepted := accepted.1
      have childrenAccepted := accepted.2
      change witness.isInstance (List.ofFn fun i => (children i).concl) conclusion = true
        at ruleAccepted
      change ProofSyntax Const Δ (formula c ν conclusion)
      have childProof (premises : List (Equation c))
          (binding : (List.ofFn fun i => (children i).concl) = premises)
          (i : Fin premises.length) : ProofSyntax Const Δ (formula c ν (premises.get i)) := by
        have count : n = premises.length := by simpa using congrArg List.length binding
        let j : Fin n := Fin.cast count.symm i
        have goalEq : (children j).concl = premises.get i := by
          have selected := congrArg (fun es : List (Equation c) => es[i.val]?) binding
          have selected' : ∃ (h : i.val < n),
              (children ⟨i.val, h⟩).concl = premises[i.val] := by simpa using selected
          obtain ⟨_, equal⟩ := selected'
          exact equal
        exact goalEq ▸ reconstructCertificate c system licensed (children j) (childrenAccepted j) ν
      cases witness with
      | systemInstance occurrence substitution =>
          simp only [UniversalAlgebra.EquationalRuleWitness.isInstance,
            decide_eq_true_eq] at ruleAccepted
          rw [ruleAccepted.2]
          simpa only [formula, translate, UniversalAlgebra.Term.evaluate_subst] using
            licensed occurrence (fun n => translate c ν (substitution n))
      | refl term =>
          simp only [UniversalAlgebra.EquationalRuleWitness.isInstance,
            decide_eq_true_eq] at ruleAccepted
          rw [ruleAccepted.2]
          exact .eqRefl _
      | symm left right =>
          simp only [UniversalAlgebra.EquationalRuleWitness.isInstance,
            decide_eq_true_eq] at ruleAccepted
          rw [ruleAccepted.2]
          exact .eqSymm (childProof _ ruleAccepted.1 0)
      | trans left middle right =>
          simp only [UniversalAlgebra.EquationalRuleWitness.isInstance,
            decide_eq_true_eq] at ruleAccepted
          rw [ruleAccepted.2]
          exact .eqTrans (childProof _ ruleAccepted.1 0) (childProof _ ruleAccepted.1 1)
      | congruence operation left right =>
          simp only [UniversalAlgebra.EquationalRuleWitness.isInstance,
            decide_eq_true_eq] at ruleAccepted
          rw [ruleAccepted.2]
          cases operation with
          | inl i => exact .eqRefl _
          | inr i =>
              exact .eqAppArg (c.unary i)
                (childProof _ ruleAccepted.1 ⟨0, by simp [Chart.signature]⟩)

variable [DecidableEq Base] [∀ σ, DecidableEq (Const σ)]

/-- The unchanged executable checker binds the retained result to the requested
HOL formula. Source-equation proofs remain explicitly and independently given. -/
def reconstructAccepted (c : Chart Const Γ τ) (fuel : Nat)
    (assumptions : List (Formula Const Γ)) (φ : Formula Const Γ)
    (system : UniversalAlgebra.EquationSystem c.signature) (certificate : Certificate c system)
    (accepted : accepts c fuel assumptions φ system certificate = true)
    {Δ : List (Formula Const Γ)}
    (licensed : ∀ (i : Fin system.equations.length) ν,
      ProofSyntax Const Δ (formula c ν (system.equations.get i)))
    (ν : Nat → Term Const Γ τ) : ProofSyntax Const Δ φ := by
  unfold accepts at accepted
  split at accepted <;> try contradiction
  rename_i hs goal _ _
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  have goalEq := accepted.1.2
  have valid := accepted.2
  have source := reconstructCertificate c system licensed certificate valid ν
  have binding : formula c ν certificate.concl = φ :=
    (congrArg (formula c ν) goalEq.symm).trans (goal.roundtrip ν)
  exact binding ▸ source

theorem reconstructAccepted_erasure (c : Chart Const Γ τ) (fuel : Nat)
    (assumptions : List (Formula Const Γ)) (φ : Formula Const Γ)
    (system : UniversalAlgebra.EquationSystem c.signature) (certificate : Certificate c system)
    (accepted : accepts c fuel assumptions φ system certificate = true)
    {Δ : List (Formula Const Γ)}
    (licensed : ∀ (i : Fin system.equations.length) ν,
      ProofSyntax Const Δ (formula c ν (system.equations.get i)))
    (ν : Nat → Term Const Γ τ) : ExtDerivation Const Δ φ :=
  (reconstructAccepted c fuel assumptions φ system certificate accepted licensed ν).erase

end Mettapedia.Logic.HOL.GroundUnaryEquationalChart
