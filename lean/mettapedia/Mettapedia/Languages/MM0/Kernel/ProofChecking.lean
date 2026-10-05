import Mettapedia.Languages.MM0.Kernel.Proof

/-!
# Checking supplied MM0 proof witnesses

Each finite witness determines its own conclusion. The theorem case checks
the actual signature entry and computes simultaneous substitution; it accepts
exactly one child for each substituted hypothesis, in declaration order.
The conversion case requires the computed left endpoint to equal the child's
conclusion. It never searches for another proof or conversion witness.

`Checks` describes the submitted witness independently of the evaluator.
Soundness erases it to `Derives`; completeness constructs finite evidence
from any independent derivation. No execution fuel bounds the logical core.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

inductive ProofWitness where
  | hyp (index : Nat)
  | theoremApp (index : Nat) (arguments : List Preterm) (children : List ProofWitness)
  | conversion (witness : ConvWitness) (child : ProofWitness)
  deriving Repr

namespace ProofWitness

mutual

def proof? (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm) :
    ProofWitness → Option Preterm
  | .hyp index => hypotheses[index]?
  | .theoremApp index arguments children => do
      let declaration ← theorems index
      let instantiation ← declaration.instantiate? signature context arguments
      let premises ← children? signature definitions theorems context hypotheses children
      if premises = instantiation.hypotheses then some instantiation.conclusion else none
  | .conversion witness child => do
      let converted ← witness.conversion? signature definitions context
      let conclusion ← proof? signature definitions theorems context hypotheses child
      if conclusion = converted.left then some converted.right else none
termination_by witness => sizeOf witness

def children? (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm) :
    List ProofWitness → Option (List Preterm)
  | [] => some []
  | child :: children => do
      let conclusion ← proof? signature definitions theorems context hypotheses child
      let conclusions ← children? signature definitions theorems context hypotheses children
      pure (conclusion :: conclusions)
termination_by children => sizeOf children

end

mutual

inductive Checks (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm) :
    ProofWitness → Preterm → Prop where
  | hyp {index : Nat} {expression : Preterm} : hypotheses[index]? = some expression →
      Checks signature definitions theorems context hypotheses (.hyp index) expression
  | theoremApp {index : Nat} {declaration : TheoremDecl} {arguments : List Preterm}
      {children : List ProofWitness} {instantiation : TheoremInstance} :
      theorems index = some declaration →
      TheoremDecl.Instantiates signature context declaration arguments instantiation →
      ChecksList signature definitions theorems context hypotheses children instantiation.hypotheses →
      Checks signature definitions theorems context hypotheses
        (.theoremApp index arguments children) instantiation.conclusion
  | conversion {witness : ConvWitness} {child : ProofWitness} {left right : Preterm} {sort : Nat} :
      ConvWitness.Checks signature definitions context witness left right sort →
      Checks signature definitions theorems context hypotheses child left →
      Checks signature definitions theorems context hypotheses (.conversion witness child) right

inductive ChecksList (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm) :
    List ProofWitness → List Preterm → Prop where
  | nil : ChecksList signature definitions theorems context hypotheses [] []
  | cons {child : ProofWitness} {children : List ProofWitness} {expression : Preterm}
      {expressions : List Preterm} :
      Checks signature definitions theorems context hypotheses child expression →
      ChecksList signature definitions theorems context hypotheses children expressions →
      ChecksList signature definitions theorems context hypotheses
        (child :: children) (expression :: expressions)

end

theorem Checks.eval {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {expression : Preterm}
    (checked : Checks signature definitions theorems context hypotheses witness expression) :
    proof? signature definitions theorems context hypotheses witness = some expression := by
  induction checked using Checks.rec
      (motive_2 := fun children expressions _ =>
        children? signature definitions theorems context hypotheses children = some expressions) with
  | hyp lookup => simpa [proof?] using lookup
  | theoremApp lookup instantiated _ ih =>
      simp [proof?, lookup, instantiated.eval, ih]
  | conversion converted _ ih => simp [proof?, converted.eval, ih]
  | nil => simp [children?]
  | cons _ _ ihChild ihTail => simp [children?, ihChild, ihTail]

theorem ChecksList.eval {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {children : List ProofWitness} {expressions : List Preterm}
    (checked : ChecksList signature definitions theorems context hypotheses children expressions) :
    children? signature definitions theorems context hypotheses children = some expressions := by
  induction checked using ChecksList.rec
      (motive_1 := fun witness expression _ =>
        proof? signature definitions theorems context hypotheses witness = some expression) with
  | hyp lookup => simpa [proof?] using lookup
  | theoremApp lookup instantiated _ ih =>
      simp [proof?, lookup, instantiated.eval, ih]
  | conversion converted _ ih => simp [proof?, converted.eval, ih]
  | nil => simp [children?]
  | cons _ _ ihChild ihTail => simp [children?, ihChild, ihTail]

mutual

theorem proof_sound {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {expression : Preterm}
    (accepted : proof? signature definitions theorems context hypotheses witness = some expression) :
    Checks signature definitions theorems context hypotheses witness expression := by
  cases witness with
  | hyp index => exact .hyp (by simpa [proof?] using accepted)
  | theoremApp index arguments children =>
      cases lookup : theorems index with
      | none => simp [proof?, lookup] at accepted
      | some declaration =>
          cases computed : declaration.instantiate? signature context arguments with
          | none => simp [proof?, lookup, computed] at accepted
          | some instantiation =>
              cases premises : children? signature definitions theorems context hypotheses children with
              | none => simp [proof?, lookup, premises] at accepted
              | some expressions =>
                  by_cases same : expressions = instantiation.hypotheses
                  · have result : instantiation.conclusion = expression := by
                      simpa [proof?, lookup, computed, premises, same] using accepted
                    subst expression
                    have checked := children_sound premises
                    rw [same] at checked
                    exact .theoremApp lookup
                      ((TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp computed) checked
                  · simp [proof?, lookup, computed, premises, same] at accepted
  | conversion witness child =>
      cases converted : witness.conversion? signature definitions context with
      | none => simp [proof?, converted] at accepted
      | some endpoints =>
          cases childResult : proof? signature definitions theorems context hypotheses child with
          | none => simp [proof?, converted, childResult] at accepted
          | some conclusion =>
              by_cases same : conclusion = endpoints.left
              · have result : endpoints.right = expression := by
                  simpa [proof?, converted, childResult, same] using accepted
                subst expression
                have childChecked := proof_sound childResult
                rw [same] at childChecked
                exact .conversion (ConvWitness.conversion_sound converted) childChecked
              · simp [proof?, converted, childResult, same] at accepted
termination_by structural witness

theorem children_sound {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {children : List ProofWitness} {expressions : List Preterm}
    (accepted : children? signature definitions theorems context hypotheses children = some expressions) :
    ChecksList signature definitions theorems context hypotheses children expressions := by
  cases children with
  | nil =>
      have same : [] = expressions := by simpa [children?] using accepted
      subst expressions
      exact .nil
  | cons child children =>
      cases head : proof? signature definitions theorems context hypotheses child with
      | none => simp [children?, head] at accepted
      | some conclusion =>
          cases tail : children? signature definitions theorems context hypotheses children with
          | none => simp [children?, head, tail] at accepted
          | some conclusions =>
              have same : conclusion :: conclusions = expressions := by
                simpa [children?, head, tail] using accepted
              subst expressions
              exact .cons (proof_sound head) (children_sound tail)
termination_by structural children

end

theorem proof_eq_some_iff (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (expression : Preterm) :
    proof? signature definitions theorems context hypotheses witness = some expression ↔
      Checks signature definitions theorems context hypotheses witness expression :=
  ⟨proof_sound, Checks.eval⟩

theorem children_eq_some_iff (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (children : List ProofWitness) (expressions : List Preterm) :
    children? signature definitions theorems context hypotheses children = some expressions ↔
      ChecksList signature definitions theorems context hypotheses children expressions :=
  ⟨children_sound, ChecksList.eval⟩

theorem Checks.derives {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {expression : Preterm}
    (checked : Checks signature definitions theorems context hypotheses witness expression) :
    Derives signature definitions theorems context hypotheses expression := by
  induction checked using Checks.rec
      (motive_2 := fun _ expressions _ =>
        DerivesList signature definitions theorems context hypotheses expressions) with
  | hyp lookup => exact .hypothesis (List.mem_of_getElem? lookup)
  | theoremApp lookup instantiated _ ih => exact .theoremApp lookup instantiated ih
  | conversion converted _ ih => exact .conversion converted.derives ih
  | nil => exact .nil
  | cons _ _ ihChild ihTail => exact .cons ihChild ihTail

theorem ChecksList.derives {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {children : List ProofWitness} {expressions : List Preterm}
    (checked : ChecksList signature definitions theorems context hypotheses children expressions) :
    DerivesList signature definitions theorems context hypotheses expressions := by
  induction checked using ChecksList.rec
      (motive_1 := fun _ expression _ =>
        Derives signature definitions theorems context hypotheses expression) with
  | hyp lookup => exact .hypothesis (List.mem_of_getElem? lookup)
  | theoremApp lookup instantiated _ ih => exact .theoremApp lookup instantiated ih
  | conversion converted _ ih => exact .conversion converted.derives ih
  | nil => exact .nil
  | cons _ _ ihChild ihTail => exact .cons ihChild ihTail

theorem ChecksList.length_eq {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {children : List ProofWitness} {expressions : List Preterm}
    (checked : ChecksList signature definitions theorems context hypotheses children expressions) :
    children.length = expressions.length := by
  induction children generalizing expressions with
  | nil => cases checked; rfl
  | cons child children ih =>
      cases checked with
      | cons _ tail => exact congrArg Nat.succ (ih tail)

def check (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (expression : Preterm) : Bool :=
  decide (proof? signature definitions theorems context hypotheses witness = some expression)

theorem check_iff (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (expression : Preterm) :
    check signature definitions theorems context hypotheses witness expression = true ↔
      Checks signature definitions theorems context hypotheses witness expression := by
  simp only [check, decide_eq_true_eq, proof_eq_some_iff]

theorem check_sound {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {expression : Preterm}
    (accepted : check signature definitions theorems context hypotheses witness expression = true) :
    Derives signature definitions theorems context hypotheses expression :=
  ((check_iff _ _ _ _ _ _ _).mp accepted).derives

theorem proof_none_iff (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) :
    proof? signature definitions theorems context hypotheses witness = none ↔
      ¬ ∃ expression, Checks signature definitions theorems context hypotheses witness expression := by
  constructor
  · intro refused ⟨expression, checked⟩
    have success := checked.eval
    rw [refused] at success
    contradiction
  · intro impossible
    cases result : proof? signature definitions theorems context hypotheses witness with
    | none => rfl
    | some expression => exact False.elim (impossible ⟨expression, proof_sound result⟩)

theorem Checks.deterministic {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {first second : Preterm}
    (left : Checks signature definitions theorems context hypotheses witness first)
    (right : Checks signature definitions theorems context hypotheses witness second) : first = second :=
  Option.some.inj (left.eval.symm.trans right.eval)

end ProofWitness

theorem Derives.certificate_exists {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {expression : Preterm}
    (derived : Derives signature definitions theorems context hypotheses expression) :
    ∃ witness, ProofWitness.Checks signature definitions theorems context hypotheses witness expression := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ =>
        ∃ children, ProofWitness.ChecksList signature definitions theorems context hypotheses
          children expressions) with
  | hypothesis member =>
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
      exact ⟨.hyp index, .hyp lookup⟩
  | theoremApp lookup instantiated _ ih =>
      obtain ⟨children, checked⟩ := ih
      exact ⟨.theoremApp _ _ children, .theoremApp lookup instantiated checked⟩
  | conversion converted _ ih =>
      obtain ⟨conversionWitness, conversionChecked⟩ := converted.certificate_exists
      obtain ⟨child, childChecked⟩ := ih
      exact ⟨.conversion conversionWitness child, .conversion conversionChecked childChecked⟩
  | nil => exact ⟨[], .nil⟩
  | cons _ _ ihHead ihTail =>
      obtain ⟨child, checkedChild⟩ := ihHead
      obtain ⟨children, checkedChildren⟩ := ihTail
      exact ⟨child :: children, .cons checkedChild checkedChildren⟩

theorem derives_iff_checked (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (expression : Preterm) :
    Derives signature definitions theorems context hypotheses expression ↔
      ∃ witness, ProofWitness.check signature definitions theorems context hypotheses witness expression = true := by
  constructor
  · intro derived
    obtain ⟨witness, checked⟩ := derived.certificate_exists
    exact ⟨witness, (ProofWitness.check_iff _ _ _ _ _ _ _).mpr checked⟩
  · rintro ⟨witness, accepted⟩
    exact ProofWitness.check_sound accepted

end Mettapedia.Languages.MM0.Kernel
