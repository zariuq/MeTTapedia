import Mettapedia.Languages.MM0.Kernel.SpecificationAdmission

/-!
# Complete checking against a resolved MM0 specification

Acceptance consumes every specification declaration. The admitted axiom list
is exactly the specification's axiom list, in order and with its full payloads.
Auxiliary definitions and proved theorems cannot add assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.SpecificationAdmission

inductive Runs : State → List ProofDeclaration → State → Prop where
  | nil (state : State) : Runs state [] state
  | cons {before middle after : State} {head : ProofDeclaration} {tail : List ProofDeclaration} :
      Step before head middle → Runs middle tail after → Runs before (head :: tail) after

def run? : State → List ProofDeclaration → Option State
  | state, [] => some state
  | state, declaration :: remaining => do
      let next ← step? state declaration
      run? next remaining

theorem run_eq_some_iff (before after : State) (declarations : List ProofDeclaration) :
    run? before declarations = some after ↔ Runs before declarations after := by
  induction declarations generalizing before with
  | nil =>
      constructor
      · intro same
        have same := Option.some.inj same
        subst before
        exact .nil _
      · intro runs
        cases runs
        rfl
  | cons head tail ih =>
      constructor
      · intro success
        cases step : step? before head with
        | none => simp [run?, step] at success
        | some middle =>
            have rest : run? middle tail = some after := by simpa [run?, step] using success
            exact .cons ((step_eq_some_iff _ _ _).mp step) ((ih middle).mp rest)
      · intro runs
        cases runs with
        | cons first rest =>
            simp [run?, (step_eq_some_iff _ _ _).mpr first, (ih _).mpr rest]

theorem Runs.theory_run {before after : State} {declarations : List ProofDeclaration}
    (runs : Runs before declarations after) :
    Theory.Runs before.theory (declarations.map ProofDeclaration.admission) after.theory := by
  induction runs with
  | nil state => exact .nil state.theory
  | cons step _ ih => exact .cons step.theory_step ih

def specificationAxioms : List SpecificationEntry → List (Nat × TheoremDecl)
  | [] => []
  | .axiomDecl index declaration :: remaining => (index, declaration) :: specificationAxioms remaining
  | _ :: remaining => specificationAxioms remaining

def declarationAxioms : List ProofDeclaration → List (Nat × TheoremDecl)
  | [] => []
  | ⟨.axiomDecl index declaration, _⟩ :: remaining => (index, declaration) :: declarationAxioms remaining
  | _ :: remaining => declarationAxioms remaining

theorem Step.axioms {before after : State} {declaration : ProofDeclaration}
    (step : Step before declaration after) :
    specificationAxioms before.pending =
      declarationAxioms [declaration] ++ specificationAxioms after.pending := by
  cases step with
  | auxiliary allowed _ => cases allowed <;> rfl
  | publicDecl matched _ => cases matched <;> rfl

theorem Runs.axioms {before after : State} {declarations : List ProofDeclaration}
    (runs : Runs before declarations after) :
    specificationAxioms before.pending =
      declarationAxioms declarations ++ specificationAxioms after.pending := by
  induction runs with
  | nil state => rfl
  | cons step rest ih =>
      rw [step.axioms, ih, ← List.append_assoc]
      congr 1
      rename_i head tail
      rcases head with ⟨admission, localFlag⟩
      cases admission <;> rfl

def verify? (specification : List SpecificationEntry) (declarations : List ProofDeclaration) :
    Option Theory := do
  let state ← run? ⟨{}, specification⟩ declarations
  if state.pending.isEmpty then some state.theory else none

theorem verify_eq_some_iff (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) (theory : Theory) :
    verify? specification declarations = some theory ↔
      Runs ⟨{}, specification⟩ declarations ⟨theory, []⟩ := by
  constructor
  · intro accepted
    cases computed : run? ⟨{}, specification⟩ declarations with
    | none => simp [verify?, computed] at accepted
    | some state =>
        rcases state with ⟨nextTheory, pending⟩
        cases pending with
        | nil =>
            have same : nextTheory = theory := by simpa [verify?, computed] using accepted
            subst nextTheory
            exact (run_eq_some_iff _ _ _).mp computed
        | cons entry remaining => simp [verify?, computed] at accepted
  · intro checked
    simp [verify?, (run_eq_some_iff _ _ _).mpr checked]

theorem verified_wellFormed {specification : List SpecificationEntry}
    {declarations : List ProofDeclaration} {theory : Theory}
    (accepted : verify? specification declarations = some theory) : Theory.WellFormed theory :=
  ((verify_eq_some_iff _ _ _).mp accepted).theory_run.wellFormed Theory.empty_wellFormed

/-- The proof file has neither added nor omitted any declared axiom. This
statement counts complete payloads and multiplicity, not just identifier sets. -/
theorem verified_axioms_exact {specification : List SpecificationEntry}
    {declarations : List ProofDeclaration} {theory : Theory}
    (accepted : verify? specification declarations = some theory) :
    declarationAxioms declarations = specificationAxioms specification := by
  have exactAxioms := ((verify_eq_some_iff _ _ _).mp accepted).axioms
  simpa [specificationAxioms] using exactAxioms.symm

end Mettapedia.Languages.MM0.Kernel.SpecificationAdmission
