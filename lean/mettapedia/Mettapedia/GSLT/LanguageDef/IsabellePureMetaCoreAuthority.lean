import Mettapedia.GSLT.LanguageDef.IsabellePureMetaCore
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Independent semantics and NIK authority for the selected Pure meta-core

The executable replay in `IsabellePureMetaCore` establishes structural
derivability.  This module supplies a separate Tarskian interpretation and
proves every selected proof-term constructor sound for it before attaching a
NIK authority.  Thus checker acceptance does not define semantic meaning.

The model has an arbitrary carrier, constants, binary application, and
relations.  Meta-universal quantification ranges over the carrier;
meta-implication is ordinary implication.  De Bruijn lifting and substitution
are proved to commute with interpretation, including beneath nested binders.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IsabellePureMetaCoreAuthority

open Mettapedia.GSLT.LanguageDef.IsabellePureMetaCore
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe u

/-! ## Tarskian structures -/

/-- A one-sorted interpretation of the selected object-term and atom syntax. -/
structure Interpretation where
  Carrier : Type u
  constant : Nat -> Carrier
  application : Carrier -> Carrier -> Carrier
  relation : Nat -> List Carrier -> Prop

namespace Interpretation

abbrev Environment (interpretation : Interpretation.{u}) :=
  Nat -> interpretation.Carrier

/-- Add a new innermost object-variable value. -/
def extend {interpretation : Interpretation.{u}}
    (value : interpretation.Carrier)
    (environment : Environment interpretation) : Environment interpretation
  | 0 => value
  | index + 1 => environment index

/-- Insert a value at a de Bruijn cutoff, shifting older values upward. -/
def insertAt {interpretation : Interpretation.{u}} (cutoff : Nat)
    (value : interpretation.Carrier)
    (environment : Environment interpretation) : Environment interpretation :=
  fun index =>
    if index < cutoff then environment index
    else if index = cutoff then value
    else environment (index - 1)

@[simp] theorem extend_zero {interpretation : Interpretation.{u}}
    (value : interpretation.Carrier) (environment : Environment interpretation) :
    extend value environment 0 = value := rfl

@[simp] theorem extend_succ {interpretation : Interpretation.{u}}
    (value : interpretation.Carrier) (environment : Environment interpretation)
    (index : Nat) :
    extend value environment (index + 1) = environment index := rfl

theorem insertAt_zero {interpretation : Interpretation.{u}}
    (value : interpretation.Carrier) (environment : Environment interpretation) :
    insertAt 0 value environment = extend value environment := by
  funext index
  cases index <;> simp [insertAt, extend]

/-- Extending an environment commutes with insertion after incrementing the
cutoff.  This is the binder case of both lift and substitution. -/
theorem extend_insertAt {interpretation : Interpretation.{u}}
    (newValue insertedValue : interpretation.Carrier)
    (environment : Environment interpretation) (cutoff : Nat) :
    extend newValue (insertAt cutoff insertedValue environment) =
      insertAt (cutoff + 1) insertedValue (extend newValue environment) := by
  funext index
  cases index with
  | zero => simp [insertAt, extend]
  | succ index =>
      by_cases below : index < cutoff
      · simp [insertAt, extend, below]
      · by_cases equal : index = cutoff
        · subst index
          simp [insertAt, extend]
        · have above : cutoff < index := by omega
          have positive : 0 < index := by omega
          cases index with
          | zero => omega
          | succ predecessor =>
              simp [insertAt, extend, below, equal]

/-- Interpret an object term under a total de Bruijn environment. -/
def eval (interpretation : Interpretation.{u})
    (environment : Environment interpretation) : Term -> interpretation.Carrier
  | .bvar index => environment index
  | .constant name => interpretation.constant name
  | .app function argument =>
      interpretation.application (eval interpretation environment function)
        (eval interpretation environment argument)

/-- Lifting syntax is exactly insertion of an unused semantic value. -/
theorem eval_lift (interpretation : Interpretation.{u})
    (environment : Environment interpretation) (insertedValue : interpretation.Carrier)
    (cutoff : Nat) (term : Term) :
    eval interpretation (insertAt cutoff insertedValue environment)
        (term.lift 1 cutoff) =
      eval interpretation environment term := by
  induction term with
  | bvar index =>
      by_cases below : index < cutoff
      · simp [Term.lift, eval, insertAt, below]
      · have liftedNotBelow : ¬ index + 1 < cutoff := by omega
        have liftedNotEqual : index + 1 ≠ cutoff := by omega
        simp [Term.lift, eval, insertAt, below, liftedNotBelow,
          liftedNotEqual]
  | constant name => simp [Term.lift, eval]
  | app function argument functionIH argumentIH =>
      simp [Term.lift, eval, functionIH, argumentIH]

/-- Syntactic substitution is semantic environment insertion. -/
theorem eval_subst (interpretation : Interpretation.{u})
    (environment : Environment interpretation) (index : Nat)
    (replacement term : Term) :
    eval interpretation environment (Term.subst index replacement term) =
      eval interpretation
        (insertAt index (eval interpretation environment replacement) environment)
        term := by
  induction term with
  | bvar current =>
      by_cases equal : current = index
      · subst current
        simp [Term.subst, eval, insertAt]
      · by_cases above : index < current
        · have notBelow : ¬ current < index := by omega
          simp [Term.subst, eval, insertAt, equal, above, notBelow]
        · have below : current < index := by omega
          simp [Term.subst, eval, insertAt, equal, above, below]
  | constant name => simp [Term.subst, eval]
  | app function argument functionIH argumentIH =>
      simp [Term.subst, eval, functionIH, argumentIH]

/-- Tarskian semantics of selected Pure meta-propositions. -/
def Sem (interpretation : Interpretation.{u})
    (environment : Environment interpretation) : Proposition -> Prop
  | .atom relation arguments =>
      interpretation.relation relation
        (arguments.map (eval interpretation environment))
  | .imp premise conclusion =>
      Sem interpretation environment premise ->
        Sem interpretation environment conclusion
  | .all body =>
      forall value, Sem interpretation (extend value environment) body

/-- Proposition lifting preserves meaning under environment insertion. -/
theorem sem_lift (interpretation : Interpretation.{u})
    (environment : Environment interpretation) (insertedValue : interpretation.Carrier)
    (cutoff : Nat) (proposition : Proposition) :
    Sem interpretation (insertAt cutoff insertedValue environment)
        (proposition.lift 1 cutoff) <->
      Sem interpretation environment proposition := by
  induction proposition generalizing cutoff environment with
  | atom relation arguments =>
      simp only [Proposition.lift, Sem, List.map_map]
      have argumentsEqual :
          List.map
              (eval interpretation
                (insertAt cutoff insertedValue environment) ∘
                  Term.lift 1 cutoff)
              arguments =
            List.map (eval interpretation environment) arguments := by
        apply List.map_congr_left
        intro term member
        exact eval_lift interpretation environment insertedValue cutoff term
      rw [argumentsEqual]
  | imp premise conclusion premiseIH conclusionIH =>
      simp only [Proposition.lift, Sem]
      rw [premiseIH, conclusionIH]
  | all body bodyIH =>
      simp only [Proposition.lift, Sem]
      constructor
      · intro holds value
        have bodyHolds := holds value
        rw [extend_insertAt, bodyIH] at bodyHolds
        exact bodyHolds
      · intro holds value
        rw [extend_insertAt, bodyIH]
        exact holds value

/-- Proposition substitution is semantic environment insertion. -/
theorem sem_subst (interpretation : Interpretation.{u})
    (environment : Environment interpretation) (index : Nat)
    (replacement : Term) (proposition : Proposition) :
    Sem interpretation environment (proposition.subst index replacement) <->
      Sem interpretation
        (insertAt index (eval interpretation environment replacement) environment)
        proposition := by
  induction proposition generalizing index replacement environment with
  | atom relation arguments =>
      simp only [Proposition.subst, Sem, List.map_map]
      have argumentsEqual :
          List.map
              (eval interpretation environment ∘ Term.subst index replacement)
              arguments =
            List.map
              (eval interpretation
                (insertAt index (eval interpretation environment replacement)
                  environment))
              arguments := by
        apply List.map_congr_left
        intro term member
        exact eval_subst interpretation environment index replacement term
      rw [argumentsEqual]
  | imp premise conclusion premiseIH conclusionIH =>
      simp only [Proposition.subst, Sem]
      rw [premiseIH, conclusionIH]
  | all body bodyIH =>
      simp only [Proposition.subst, Sem]
      constructor
      · intro holds value
        have bodyHolds :=
          (bodyIH (environment := extend value environment)
            (index := index + 1) (replacement := replacement.lift 1 0)).mp
            (holds value)
        have replacementEval :
            eval interpretation (extend value environment)
                (replacement.lift 1 0) =
              eval interpretation environment replacement := by
          rw [← insertAt_zero]
          exact eval_lift interpretation environment value 0 replacement
        rw [replacementEval] at bodyHolds
        rw [extend_insertAt]
        exact bodyHolds
      · intro holds value
        apply (bodyIH (environment := extend value environment)
          (index := index + 1) (replacement := replacement.lift 1 0)).mpr
        have replacementEval :
            eval interpretation (extend value environment)
                (replacement.lift 1 0) =
              eval interpretation environment replacement := by
          rw [← insertAt_zero]
          exact eval_lift interpretation environment value 0 replacement
        rw [replacementEval]
        rw [← extend_insertAt]
        exact holds value

theorem sem_subst0 (interpretation : Interpretation.{u})
    (environment : Environment interpretation) (replacement : Term)
    (proposition : Proposition) :
    Sem interpretation environment (proposition.subst0 replacement) <->
      Sem interpretation
        (extend (eval interpretation environment replacement) environment)
        proposition := by
  rw [Proposition.subst0, sem_subst, insertAt_zero]

end Interpretation

/-! ## Independent validity and proof soundness -/

def SatisfiesList (interpretation : Interpretation.{u})
    (environment : interpretation.Environment)
    (propositions : List Proposition) : Prop :=
  forall proposition, proposition ∈ propositions ->
    interpretation.Sem environment proposition

/-- Every structural selected-Pure proof term preserves the independent
Tarskian interpretation. -/
theorem HasProof.sound
    {theory hypotheses proofBounds depth proof claim}
    (derivation : HasProof theory hypotheses proofBounds depth proof claim)
    (interpretation : Interpretation.{u})
    (environment : interpretation.Environment)
    (axiomsHold : SatisfiesList interpretation environment theory.axioms)
    (hypothesesHold : SatisfiesList interpretation environment hypotheses)
    (proofBoundsHold : SatisfiesList interpretation environment proofBounds) :
    interpretation.Sem environment claim := by
  induction derivation generalizing interpretation environment with
  | axiomRef lookup wellScoped =>
      exact axiomsHold _ (List.mem_of_getElem? lookup)
  | bound lookup wellScoped =>
      exact proofBoundsHold _ (List.mem_of_getElem? lookup)
  | hypothesis member wellScoped =>
      exact hypothesesHold _ member
  | abstractTerm bodyProof induction =>
      intro value
      apply induction interpretation (interpretation.extend value environment)
      · intro lifted member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        simpa only [Interpretation.insertAt_zero] using
          (interpretation.sem_lift environment value 0 original).mpr
            (axiomsHold original originalMember)
      · intro lifted member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        simpa only [Interpretation.insertAt_zero] using
          (interpretation.sem_lift environment value 0 original).mpr
            (hypothesesHold original originalMember)
      · intro lifted member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        simpa only [Interpretation.insertAt_zero] using
          (interpretation.sem_lift environment value 0 original).mpr
            (proofBoundsHold original originalMember)
  | abstractProof premiseScoped bodyProof induction =>
      intro premiseHolds
      apply induction interpretation environment axiomsHold hypothesesHold
      intro proposition member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact premiseHolds
      · exact proofBoundsHold proposition member
  | applyTerm functionProof argumentScoped induction =>
      apply (interpretation.sem_subst0 environment _ _).mpr
      exact induction interpretation environment axiomsHold hypothesesHold
        proofBoundsHold (interpretation.eval environment _)
  | applyProof functionProof argumentProof functionIH argumentIH =>
      exact functionIH interpretation environment axiomsHold hypothesesHold
        proofBoundsHold
        (argumentIH interpretation environment axiomsHold hypothesesHold
          proofBoundsHold)

/-- Semantic validity of a sequent is independent of proof-term existence. -/
def Valid (theory : TheoryContext) (hypotheses : List Proposition)
    (claim : Proposition) : Prop :=
  forall (interpretation : Interpretation.{0})
    (environment : interpretation.Environment),
    SatisfiesList interpretation environment theory.axioms ->
      SatisfiesList interpretation environment hypotheses ->
        interpretation.Sem environment claim

theorem derivable_valid {theory hypotheses claim}
    (derivable : Derivable theory hypotheses claim) :
    Valid theory hypotheses claim := by
  obtain ⟨proof, derivation⟩ := derivable
  intro interpretation environment axiomsHold hypothesesHold
  exact HasProof.sound derivation interpretation environment axiomsHold hypothesesHold
    (by intro proposition member; simp at member)

/-! ## NIK attachment -/

/-- Claims retain their ambient hypotheses rather than encoding them into a
flat implication chain. -/
structure Sequent where
  hypotheses : List Proposition
  conclusion : Proposition
  deriving DecidableEq, Repr

def theoryFamily (theory : TheoryContext) : TheoryFamily Unit where
  Signature := TheoryContext
  signatureOf := fun _kind => theory
  Claim := fun _kind => Sequent
  Scope := fun _kind sequent =>
    Derivable theory sequent.hypotheses sequent.conclusion
  Meaning := fun _kind sequent =>
    Valid theory sequent.hypotheses sequent.conclusion
  scope_sound := by
    intro kind sequent derivable
    exact derivable_valid derivable

/-- At this certificate-facing projection, the submitted evidence is the
selected calculus's own intrinsic proof term rather than a generic trace. -/
def contract (theory : TheoryContext) : AuthorityContract (theoryFamily theory) where
  Certificate := fun _kind => Proof
  checker := fun _kind =>
    { check := fun sequent proof =>
        check theory sequent.hypotheses sequent.conclusion proof }
  scopeAuthority := fun _kind =>
    { sound := by
        intro sequent proof accepted
        exact check_sound accepted
      complete := by
        intro sequent derivable
        exact check_complete derivable }

theorem accepted_valid (theory : TheoryContext) (sequent : Sequent)
    (proof : Proof)
    (accepted : ((contract theory).checker ()).check sequent proof = true) :
    Valid theory sequent.hypotheses sequent.conclusion :=
  (contract theory).projection () |>.sound sequent proof accepted

/-! ## Semantic controls -/

namespace Canary

open IsabellePureMetaCore.Canary

def emptyTheory : TheoryContext := ⟨[]⟩

def identitySequent : Sequent :=
  { hypotheses := []
    conclusion := .imp p p }

theorem identity_certificate_accepted :
    ((contract emptyTheory).checker ()).check identitySequent identityProof = true := by
  decide

theorem identity_semantically_valid :
    Valid emptyTheory [] (.imp p p) :=
  accepted_valid emptyTheory identitySequent identityProof
    identity_certificate_accepted

/-- A concrete Boolean interpretation refutes the bare atom `p`. -/
def booleanInterpretation : Interpretation.{0} where
  Carrier := Bool
  constant := fun index => index % 2 == 1
  application := Bool.and
  relation := fun relation _arguments => relation != 0

theorem p_not_valid : ¬ Valid emptyTheory [] p := by
  intro valid
  let environment : booleanInterpretation.Environment :=
    fun _index => false
  have falseAtom := valid booleanInterpretation environment
    (by simp [SatisfiesList, emptyTheory])
    (by simp [SatisfiesList])
  simp [p, Interpretation.Sem, booleanInterpretation] at falseAtom

/-- Negative semantic control: no certificate can establish the independently
refutable bare atom. -/
theorem no_certificate_accepts_p :
    ¬ (∃ proof,
      ((contract emptyTheory).checker ()).check
        { hypotheses := []
          conclusion := p } proof = true) := by
  rintro ⟨proof, accepted⟩
  exact p_not_valid
    (accepted_valid emptyTheory
      { hypotheses := []
        conclusion := p }
      proof accepted)

end Canary

#print axioms Interpretation.sem_lift
#print axioms Interpretation.sem_subst
#print axioms HasProof.sound
#print axioms derivable_valid
#print axioms contract
#print axioms Canary.identity_semantically_valid
#print axioms Canary.p_not_valid
#print axioms Canary.no_certificate_accepts_p

end Mettapedia.GSLT.LanguageDef.IsabellePureMetaCoreAuthority
