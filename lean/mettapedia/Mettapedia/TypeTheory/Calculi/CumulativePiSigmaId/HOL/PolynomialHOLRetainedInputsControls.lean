import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.PolynomialHOLRetainedInputs

/-!
# Binder-changing plans retain their actual child environments

Both orders of an object binder and a proof binder reach the same HOL child
goal and scope size. The retained compiler inputs, leaf terms, and assembled
outputs differ. The plans reuse the original introduction refinements and the
native abstraction actions, with no recursive compilation of retained leaves.
-/

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputsControls

open Mettapedia.Logic Presentation FormationSensitiveHOLInterface
open HOLNativeGenericProofCompiler ProofSearch ProofObligations
open Mettapedia.TypeTheory.IndexedPolynomial
open HOL.UniformListInduction
open PolynomialHOLRetainedInputs

abbrev Goal := HOLAdapter.Goal BaseSort Symbol
abbrev signature := FormationSensitiveHOLLeibnizInterface.signature
abbrev operations := UniformList.operations
abbrev proofName := UniformList.proofName

/-- This client selects existing source methods; the input-indexed machinery
does not install an authoring inventory in the language core. -/
inductive Method : Goal → Type
  | implication {gamma : HOL.Ctx BaseSort} {delta : List (HOL.Formula Symbol gamma)}
      (antecedent conclusion : HOL.Formula Symbol gamma) (code : Tower.Tm gamma.length)
      (represented : represent signature antecedent = some code) :
      Method ⟨gamma, delta, .imp antecedent conclusion⟩
  | universal {gamma : HOL.Ctx BaseSort} {delta : List (HOL.Formula Symbol gamma)}
      {type : HOL.Ty BaseSort} (body : HOL.Formula Symbol (type :: gamma)) :
      Method ⟨gamma, delta, .all body⟩

def methods : ∀ goal, Method goal → Refinement HOLAdapter.Solution goal
  | _, .implication antecedent conclusion _ _ => ProofObligations.HOL.impI antecedent conclusion
  | _, .universal body => ProofObligations.HOL.allI body

def routing : Routing methods := by
  intro goal method input
  rcases input with ⟨scope, objects, hypotheses⟩
  cases method with
  | implication antecedent conclusion code represented =>
      exact fun _ => ⟨scope + 1, (fun index => rename wk (objects index)),
        Fin.cases (.var 0) (fun index => rename wk (hypotheses index))⟩
  | universal body =>
      exact fun _ => ⟨scope + 1, liftSub objects,
        fun index => rename wk (hypotheses (index.cast (by
          simp [methods, ProofObligations.HOL.allI, ProofObligations.HOL.unary,
            HOL.weakenHyps])))⟩

def assembly : LocalAssembly methods routing signature proofName operations := by
  intro index method children
  rcases index with ⟨goal, scope, objects, hypotheses⟩
  cases method with
  | implication antecedent conclusion code represented =>
      exact (PolynomialHOLRetainedCompilation.implicationAbstraction
        signature proofName operations represented (children ⟨0⟩)).2
  | universal body =>
      exact (PolynomialHOLRetainedCompilation.universalAbstraction
        signature proofName operations (children ⟨0⟩)).2

def premise {gamma : HOL.Ctx BaseSort} : HOL.Formula Symbol gamma :=
  .eq (.const Symbol.zero) (.const Symbol.zero)

def childGoal : Goal := ⟨[count], [premise], premise⟩

def allThenImpRoot : Index BaseSort Symbol :=
  ⟨⟨[], [], .all (σ := count) (.imp premise premise)⟩, 0, Fin.elim0, Fin.elim0⟩

def impThenAllRoot : Index BaseSort Symbol :=
  ⟨⟨[], [], .imp premise (.all (σ := count) premise)⟩, 0, Fin.elim0, Fin.elim0⟩

def outerAll : Method allThenImpRoot.1 := .universal (.imp premise premise)
def outerImp : Method impThenAllRoot.1 :=
  .implication premise (.all (σ := count) premise) _ rfl

def afterAll := (inputMethods methods routing allThenImpRoot outerAll).query ⟨0⟩
def afterImp := (inputMethods methods routing impThenAllRoot outerImp).query ⟨0⟩
def innerImp : Method afterAll.1 := .implication premise premise _ rfl
def innerAll : Method afterImp.1 := .universal premise

def objectThenProof : Input childGoal :=
  routing afterAll.1 innerImp afterAll.2 ⟨0⟩

def proofThenObject : Input childGoal :=
  routing afterImp.1 innerAll afterImp.2 ⟨0⟩

def objectThenProofLeaf : Receipt signature proofName operations
    ⟨childGoal, objectThenProof⟩ :=
  ⟨HOL.ProofSyntax.hyp (Const := Symbol) (Δ := [premise]) 0, (.var 0 : Tower.Tm 2), rfl⟩

def proofThenObjectLeaf : Receipt signature proofName operations
    ⟨childGoal, proofThenObject⟩ :=
  ⟨HOL.ProofSyntax.hyp (Const := Symbol) (Δ := [premise]) 0, (.var 1 : Tower.Tm 2), rfl⟩

abbrev Holes (_ : Unit) := Receipt signature proofName operations

def allThenImpPlan :
    (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes () allThenImpRoot :=
  Free.node _ outerAll (fun _ =>
    Free.node _ innerImp (fun _ =>
      Free.pure _ objectThenProofLeaf))

def impThenAllPlan :
    (PolynomialPlans.polynomial (inputMethods methods routing)).Free Holes () impThenAllRoot :=
  Free.node _ outerImp (fun _ =>
    Free.node _ innerAll (fun _ =>
      Free.pure _ proofThenObjectLeaf))

noncomputable def allThenImpResult :=
  assemblePlan methods routing signature proofName operations assembly
    (fun _ _ receipt => receipt) () allThenImpRoot allThenImpPlan

noncomputable def impThenAllResult :=
  assemblePlan methods routing signature proofName operations assembly
    (fun _ _ receipt => receipt) () impThenAllRoot impThenAllPlan

theorem same_source_child : objectThenProofLeaf.1 = proofThenObjectLeaf.1 := rfl

theorem same_scope : objectThenProof.1 = proofThenObject.1 := rfl

theorem object_then_proof_roles :
    objectThenProof.2.1 (0 : Fin 1) = (.var 1 : Tower.Tm 2) ∧
      objectThenProof.2.2 (0 : Fin 1) = (.var 0 : Tower.Tm 2) := ⟨rfl, rfl⟩

theorem proof_then_object_roles :
    proofThenObject.2.1 (0 : Fin 1) = (.var 0 : Tower.Tm 2) ∧
      proofThenObject.2.2 (0 : Fin 1) = (.var 1 : Tower.Tm 2) := ⟨rfl, rfl⟩

theorem child_outputs_differ : objectThenProofLeaf.2.1 ≠ proofThenObjectLeaf.2.1 := by
  intro impossible
  cases impossible

theorem all_then_imp_output :
    allThenImpResult.2.1 = (.lam (.lam (.var 0)) : Tower.Tm 0) := rfl

theorem imp_then_all_output :
    impThenAllResult.2.1 = (.lam (.lam (.var 1)) : Tower.Tm 0) := rfl

theorem complete_outputs_differ : allThenImpResult.2.1 ≠ impThenAllResult.2.1 := by
  rw [all_then_imp_output, imp_then_all_output]
  intro impossible
  cases impossible

theorem wrong_input_receipt_rejected :
    compile signature proofName operations objectThenProofLeaf.1
      proofThenObject.2.1 proofThenObject.2.2 ≠ some objectThenProofLeaf.2.1 := by
  intro impossible
  cases impossible

/-- The original compiler equation is retained by the assembled tree. -/
theorem actual_all_then_imp_compilation :
    compile signature proofName operations allThenImpResult.1
      allThenImpRoot.2.2.1 allThenImpRoot.2.2.2 = some (.lam (.lam (.var 0))) :=
  allThenImpResult.2.2

theorem actual_imp_then_all_compilation :
    compile signature proofName operations impThenAllResult.1
      impThenAllRoot.2.2.1 impThenAllRoot.2.2.2 = some (.lam (.lam (.var 1))) :=
  impThenAllResult.2.2

def firstTag : ErasedHole Holes () childGoal := ⟨objectThenProof, objectThenProofLeaf⟩
def secondTag : ErasedHole Holes () childGoal := ⟨proofThenObject, proofThenObjectLeaf⟩

/-- Erasure keeps the environment-tagged occurrences, although their source
proofs, source goals, and scope sizes agree. -/
theorem erased_holes_distinct : firstTag ≠ secondTag := by
  intro equal
  have outputs := congrArg (fun tag : ErasedHole Holes () childGoal =>
    (⟨tag.1.1, tag.2.2.1⟩ : Σ scope, Tower.Tm scope)) equal
  have wrong : (⟨2, .var 0⟩ : Σ scope, Tower.Tm scope) = ⟨2, .var 1⟩ := outputs
  have wrongTerms : (.var 0 : Tower.Tm 2) = .var 1 := eq_of_heq (Sigma.mk.inj wrong).2
  cases wrongTerms

theorem actual_source_erasure_square :
    allThenImpResult.1 =
    Free.fold (PolynomialPlans.polynomial methods)
      (fun _ _ (tag : ErasedHole Holes _ _) => tag.2.1)
      (PolynomialPlans.reconstruction methods) () allThenImpRoot.1
      (erase methods routing () allThenImpRoot allThenImpPlan) :=
  assembled_erasure methods routing signature proofName operations assembly
    (fun _ _ receipt => receipt) allThenImpPlan

abbrev PartialHoles (_ : Unit) (index : Index BaseSort Symbol) :=
  Option (Receipt signature proofName operations index)

def unresolvedInner :
    (PolynomialPlans.polynomial (inputMethods methods routing)).Free PartialHoles () afterAll :=
  Free.node _ innerImp (fun _ => Free.pure _ none)

theorem unresolved_inner_has_no_receipt :
    Free.fold _ (fun _ _ candidate => candidate)
      (partialAlgebra methods routing signature proofName operations assembly)
      () afterAll unresolvedInner = none :=
  missing_child_no_receipt methods routing signature proofName operations assembly
    innerImp (fun _ => none) ⟨⟨0⟩, rfl⟩

def unresolvedRoot :
    (PolynomialPlans.polynomial (inputMethods methods routing)).Free
      PartialHoles () allThenImpRoot :=
  Free.node _ outerAll (fun _ => unresolvedInner)

/-- The open exact-input obligation propagates through both actual binders.
This says no receipt was reconstructed, not refutation or search exhaustion. -/
theorem unresolved_root_has_no_receipt :
    Free.fold _ (fun _ _ candidate => candidate)
      (partialAlgebra methods routing signature proofName operations assembly)
      () allThenImpRoot unresolvedRoot = none := by
  apply missing_child_no_receipt methods routing signature proofName operations assembly
  exact ⟨⟨0⟩, unresolved_inner_has_no_receipt⟩

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PolynomialHOLRetainedInputsControls
