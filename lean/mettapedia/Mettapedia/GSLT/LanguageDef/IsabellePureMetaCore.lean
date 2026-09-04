import Mathlib.Data.List.GetD

/-!
# A selected proof-term core of Isabelle/Pure

This module isolates the natural-deduction proof-term fragment needed before
embedding a finite NIK metatheory in Isabelle/Pure.  It is deliberately named
`IsabellePureMetaCore` to distinguish it from the existing unlevelled
dependent typed-hole language under `LanguageDef/Pure/`.

The selected fragment has one-sorted object terms, atomic propositions,
meta-implication, and meta-universal quantification.  Its proof terms mirror
the corresponding constructors of Pure proof terms:

* an authored axiom (`PAxm`);
* a de Bruijn proof variable (`PBound`);
* object-variable abstraction and application (`Abst`, `Appt`);
* proof abstraction and application (`AbsP`, `AppP`); and
* an explicit ambient hypothesis (`Hyp`).

Order-sorted types, schematic type/term instantiation, type-class evidence
(`OfClass`), and definitional equality are outside this selected fragment.
Consequently this is not advertised as full Isabelle/Pure.

The executable checker and the declarative proof judgment are defined
independently and proved equivalent.  Crossing an object binder lifts axioms,
hypotheses, and proof-bound propositions, so a convenient de Bruijn index
cannot capture an older assumption.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IsabellePureMetaCore

/-! ## One-sorted object terms and propositions -/

/-- Object terms for the selected first-order-shaped meta-core. -/
inductive Term where
  | bvar : Nat -> Term
  | constant : Nat -> Term
  | app : Term -> Term -> Term
  deriving DecidableEq, Repr

namespace Term

/-- Lift every de Bruijn variable at or above `cutoff`. -/
def lift (distance cutoff : Nat) : Term -> Term
  | .bvar index =>
      .bvar (if index < cutoff then index else index + distance)
  | .constant name => .constant name
  | .app function argument =>
      .app (lift distance cutoff function) (lift distance cutoff argument)

/-- Capture-avoiding substitution in the one-sorted object-term language. -/
def subst (index : Nat) (replacement : Term) : Term -> Term
  | .bvar current =>
      if current = index then replacement
      else if index < current then .bvar (current - 1)
      else .bvar current
  | .constant name => .constant name
  | .app function argument =>
      .app (subst index replacement function)
        (subst index replacement argument)

def subst0 (replacement term : Term) : Term :=
  subst 0 replacement term

/-- Syntactic scope at an object-variable depth. -/
def wellScoped (depth : Nat) : Term -> Bool
  | .bvar index => decide (index < depth)
  | .constant _ => true
  | .app function argument =>
      wellScoped depth function && wellScoped depth argument

end Term

/-- The selected Pure meta-propositions. -/
inductive Proposition where
  | atom : Nat -> List Term -> Proposition
  | imp : Proposition -> Proposition -> Proposition
  | all : Proposition -> Proposition
  deriving DecidableEq, Repr

namespace Proposition

/-- Lift object variables throughout a meta-proposition. -/
def lift (distance cutoff : Nat) : Proposition -> Proposition
  | .atom relation arguments =>
      .atom relation (arguments.map (Term.lift distance cutoff))
  | .imp premise conclusion =>
      .imp (lift distance cutoff premise) (lift distance cutoff conclusion)
  | .all body => .all (lift distance (cutoff + 1) body)

/-- Substitute an object term throughout a meta-proposition. -/
def subst (index : Nat) (replacement : Term) : Proposition -> Proposition
  | .atom relation arguments =>
      .atom relation (arguments.map (Term.subst index replacement))
  | .imp premise conclusion =>
      .imp (subst index replacement premise)
        (subst index replacement conclusion)
  | .all body =>
      .all (subst (index + 1) (replacement.lift 1 0) body)

def subst0 (replacement : Term) (proposition : Proposition) : Proposition :=
  subst 0 replacement proposition

/-- Executable object-variable scope check. -/
def wellScoped (depth : Nat) : Proposition -> Bool
  | .atom _ arguments => arguments.all (Term.wellScoped depth)
  | .imp premise conclusion =>
      wellScoped depth premise && wellScoped depth conclusion
  | .all body => wellScoped (depth + 1) body

end Proposition

/-! ## Theory contexts and proof terms -/

/-- The authored axiom context consulted by `PAxm`-shaped proof terms. -/
structure TheoryContext where
  axioms : List Proposition
  deriving DecidableEq, Repr

namespace TheoryContext

/-- Crossing an object binder lifts every older authored axiom. -/
def lift (context : TheoryContext) : TheoryContext :=
  { axioms := context.axioms.map (Proposition.lift 1 0) }

end TheoryContext

/-- Proof terms for the selected Pure meta-core. -/
inductive Proof where
  | axiomRef : Nat -> Proof
  | bound : Nat -> Proof
  | abstractTerm : Proof -> Proof
  | abstractProof : Proposition -> Proof -> Proof
  | applyTerm : Proof -> Term -> Proof
  | applyProof : Proof -> Proof -> Proof
  | hypothesis : Proposition -> Proof
  deriving DecidableEq, Repr

/-! ## Independent declarative proof judgment -/

/-- Structural natural-deduction meaning of a selected Pure proof term.

`hypotheses` are ambient named hypotheses addressed by proposition, while
`proofBounds` are de Bruijn proof variables introduced by `abstractProof`.
They remain distinct, as in Pure's `Hyp` and `PBound` constructors. -/
inductive HasProof :
    TheoryContext -> List Proposition -> List Proposition -> Nat ->
      Proof -> Proposition -> Prop where
  | axiomRef
      {theory hypotheses proofBounds depth index proposition}
      (lookup : theory.axioms[index]? = some proposition)
      (wellScoped : proposition.wellScoped depth = true) :
      HasProof theory hypotheses proofBounds depth (.axiomRef index) proposition
  | bound
      {theory hypotheses proofBounds depth index proposition}
      (lookup : proofBounds[index]? = some proposition)
      (wellScoped : proposition.wellScoped depth = true) :
      HasProof theory hypotheses proofBounds depth (.bound index) proposition
  | hypothesis
      {theory hypotheses proofBounds depth proposition}
      (member : proposition ∈ hypotheses)
      (wellScoped : proposition.wellScoped depth = true) :
      HasProof theory hypotheses proofBounds depth (.hypothesis proposition)
        proposition
  | abstractTerm
      {theory hypotheses proofBounds depth proof body}
      (bodyProof :
        HasProof theory.lift
          (hypotheses.map (Proposition.lift 1 0))
          (proofBounds.map (Proposition.lift 1 0))
          (depth + 1) proof body) :
      HasProof theory hypotheses proofBounds depth (.abstractTerm proof)
        (.all body)
  | abstractProof
      {theory hypotheses proofBounds depth premise proof conclusion}
      (premiseScoped : premise.wellScoped depth = true)
      (bodyProof :
        HasProof theory hypotheses (premise :: proofBounds) depth proof
          conclusion) :
      HasProof theory hypotheses proofBounds depth
        (.abstractProof premise proof) (.imp premise conclusion)
  | applyTerm
      {theory hypotheses proofBounds depth proof body argument}
      (functionProof :
        HasProof theory hypotheses proofBounds depth proof (.all body))
      (argumentScoped : argument.wellScoped depth = true) :
      HasProof theory hypotheses proofBounds depth (.applyTerm proof argument)
        (body.subst0 argument)
  | applyProof
      {theory hypotheses proofBounds depth function argument premise conclusion}
      (functionProof :
        HasProof theory hypotheses proofBounds depth function
          (.imp premise conclusion))
      (argumentProof :
        HasProof theory hypotheses proofBounds depth argument premise) :
      HasProof theory hypotheses proofBounds depth
        (.applyProof function argument) conclusion

/-! ## Executable replay -/

/-- Infer the proposition established by a proof term, rejecting malformed
indices, ill-scoped leaves and applications with mismatched premises. -/
def infer :
    TheoryContext -> List Proposition -> List Proposition -> Nat ->
      Proof -> Option Proposition
  | theory, _hypotheses, _proofBounds, depth, .axiomRef index => do
      let proposition <- theory.axioms[index]?
      if proposition.wellScoped depth then some proposition else none
  | _theory, _hypotheses, proofBounds, depth, .bound index => do
      let proposition <- proofBounds[index]?
      if proposition.wellScoped depth then some proposition else none
  | _theory, hypotheses, _proofBounds, depth, .hypothesis proposition =>
      if proposition ∈ hypotheses then
        if proposition.wellScoped depth then some proposition else none
      else none
  | theory, hypotheses, proofBounds, depth, .abstractTerm proof => do
      let body <- infer theory.lift
        (hypotheses.map (Proposition.lift 1 0))
        (proofBounds.map (Proposition.lift 1 0)) (depth + 1) proof
      some (.all body)
  | theory, hypotheses, proofBounds, depth,
      .abstractProof premise proof => do
      if premise.wellScoped depth then
        let conclusion <- infer theory hypotheses (premise :: proofBounds)
          depth proof
        some (.imp premise conclusion)
      else none
  | theory, hypotheses, proofBounds, depth, .applyTerm proof argument => do
      if argument.wellScoped depth then
        match <- infer theory hypotheses proofBounds depth proof with
        | .all body => some (body.subst0 argument)
        | _ => none
      else none
  | theory, hypotheses, proofBounds, depth,
      .applyProof function argument => do
      match <- infer theory hypotheses proofBounds depth function with
      | .imp premise conclusion =>
          let actual <- infer theory hypotheses proofBounds depth argument
          if actual = premise then some conclusion else none
      | _ => none

/-- Boolean replay at the closed proof-variable boundary. -/
def check (theory : TheoryContext) (hypotheses : List Proposition)
    (claim : Proposition) (proof : Proof) : Bool :=
  decide (infer theory hypotheses [] 0 proof = some claim)

/-! ## Exactness of executable replay -/

theorem infer_sound : forall {theory hypotheses proofBounds depth proof claim},
    infer theory hypotheses proofBounds depth proof = some claim ->
      HasProof theory hypotheses proofBounds depth proof claim := by
  intro theory hypotheses proofBounds depth proof
  induction proof generalizing theory hypotheses proofBounds depth with
  | axiomRef index =>
      intro claim accepted
      cases lookup : theory.axioms[index]? with
      | none => simp [infer, lookup] at accepted
      | some proposition =>
          by_cases wellScoped : proposition.wellScoped depth = true
          · simp [infer, lookup, wellScoped] at accepted
            subst claim
            exact HasProof.axiomRef lookup wellScoped
          · simp [infer, lookup, wellScoped] at accepted
  | bound index =>
      intro claim accepted
      cases lookup : proofBounds[index]? with
      | none => simp [infer, lookup] at accepted
      | some proposition =>
          by_cases wellScoped : proposition.wellScoped depth = true
          · simp [infer, lookup, wellScoped] at accepted
            subst claim
            exact HasProof.bound lookup wellScoped
          · simp [infer, lookup, wellScoped] at accepted
  | hypothesis proposition =>
      intro claim accepted
      by_cases member : proposition ∈ hypotheses
      · by_cases wellScoped : proposition.wellScoped depth = true
        · simp [infer, member, wellScoped] at accepted
          subst claim
          exact HasProof.hypothesis member wellScoped
        · simp [infer, member, wellScoped] at accepted
      · simp [infer, member] at accepted
  | abstractTerm proof induction =>
      intro claim accepted
      cases bodyAccepted : infer theory.lift
          (hypotheses.map (Proposition.lift 1 0))
          (proofBounds.map (Proposition.lift 1 0))
          (depth + 1) proof with
      | none => simp [infer, bodyAccepted] at accepted
      | some body =>
          simp [infer, bodyAccepted] at accepted
          subst claim
          exact HasProof.abstractTerm (induction bodyAccepted)
  | abstractProof premise proof induction =>
      intro claim accepted
      by_cases premiseScoped : premise.wellScoped depth = true
      · cases bodyAccepted :
          infer theory hypotheses (premise :: proofBounds) depth proof with
        | none => simp [infer, premiseScoped, bodyAccepted] at accepted
        | some conclusion =>
            simp [infer, premiseScoped, bodyAccepted] at accepted
            subst claim
            exact HasProof.abstractProof premiseScoped
              (induction bodyAccepted)
      · simp [infer, premiseScoped] at accepted
  | applyTerm proof argument induction =>
      intro claim accepted
      by_cases argumentScoped : argument.wellScoped depth = true
      · cases functionAccepted :
          infer theory hypotheses proofBounds depth proof with
        | none => simp [infer, argumentScoped, functionAccepted] at accepted
        | some inferred =>
            cases inferred with
            | atom relation arguments =>
                simp [infer, argumentScoped, functionAccepted] at accepted
            | imp premise conclusion =>
                simp [infer, argumentScoped, functionAccepted] at accepted
            | all body =>
                simp [infer, argumentScoped, functionAccepted] at accepted
                subst claim
                exact HasProof.applyTerm (induction functionAccepted)
                  argumentScoped
      · simp [infer, argumentScoped] at accepted
  | applyProof function argument functionIH argumentIH =>
      intro claim accepted
      cases functionAccepted :
          infer theory hypotheses proofBounds depth function with
      | none => simp [infer, functionAccepted] at accepted
      | some inferred =>
          cases inferred with
          | atom relation arguments =>
              simp [infer, functionAccepted] at accepted
          | all body =>
              simp [infer, functionAccepted] at accepted
          | imp premise conclusion =>
              cases argumentAccepted :
                  infer theory hypotheses proofBounds depth argument with
              | none =>
                  simp [infer, functionAccepted, argumentAccepted] at accepted
              | some actual =>
                  by_cases equality : actual = premise
                  · simp [infer, functionAccepted, argumentAccepted, equality]
                      at accepted
                    subst claim
                    exact HasProof.applyProof (functionIH functionAccepted)
                      (equality ▸ argumentIH argumentAccepted)
                  · simp [infer, functionAccepted, argumentAccepted, equality]
                      at accepted

theorem infer_complete
    {theory hypotheses proofBounds depth proof claim}
    (derivation : HasProof theory hypotheses proofBounds depth proof claim) :
    infer theory hypotheses proofBounds depth proof = some claim := by
  induction derivation with
  | axiomRef lookup wellScoped => simp [infer, lookup, wellScoped]
  | bound lookup wellScoped => simp [infer, lookup, wellScoped]
  | hypothesis member wellScoped => simp [infer, member, wellScoped]
  | abstractTerm bodyProof induction => simp [infer, induction]
  | abstractProof premiseScoped bodyProof induction =>
      simp [infer, premiseScoped, induction]
  | applyTerm functionProof argumentScoped induction =>
      simp [infer, argumentScoped, induction]
  | applyProof functionProof argumentProof functionIH argumentIH =>
      simp [infer, functionIH, argumentIH]

theorem infer_eq_some_iff
    {theory hypotheses proofBounds depth proof claim} :
    infer theory hypotheses proofBounds depth proof = some claim <->
      HasProof theory hypotheses proofBounds depth proof claim :=
  ⟨infer_sound, infer_complete⟩

theorem check_eq_true_iff
    {theory hypotheses claim proof} :
    check theory hypotheses claim proof = true <->
      HasProof theory hypotheses [] 0 proof claim := by
  simp only [check, decide_eq_true_eq]
  exact infer_eq_some_iff

/-- The closed theorem scope generated by the selected proof terms. -/
def Derivable (theory : TheoryContext) (hypotheses : List Proposition)
    (claim : Proposition) : Prop :=
  ∃ proof, HasProof theory hypotheses [] 0 proof claim

/-- Accepted certificates are sound for structural theorem scope. -/
theorem check_sound
    {theory hypotheses claim proof}
    (accepted : check theory hypotheses claim proof = true) :
    Derivable theory hypotheses claim :=
  ⟨proof, check_eq_true_iff.mp accepted⟩

/-- Every structurally derivable claim has an accepted certificate. -/
theorem check_complete
    {theory hypotheses claim}
    (derivable : Derivable theory hypotheses claim) :
    ∃ proof, check theory hypotheses claim proof = true := by
  obtain ⟨proof, derivation⟩ := derivable
  exact ⟨proof, check_eq_true_iff.mpr derivation⟩

/-- Exact replay characterizes least structural theorem scope without defining
any semantic meaning predicate. -/
theorem derivable_iff_exists_accepted
    {theory hypotheses claim} :
    Derivable theory hypotheses claim <->
      ∃ proof, check theory hypotheses claim proof = true :=
  ⟨check_complete, fun accepted => by
    obtain ⟨proof, accepted⟩ := accepted
    exact check_sound accepted⟩

/-! ## Positive and adversarial controls -/

namespace Canary

def p : Proposition := .atom 0 []
def q : Proposition := .atom 1 []

def identityProof : Proof := .abstractProof p (.bound 0)

theorem identity_accepted :
    check ⟨[]⟩ [] (.imp p p) identityProof = true := by
  decide

theorem identity_hasProof :
    HasProof ⟨[]⟩ [] [] 0 identityProof (.imp p p) :=
  check_eq_true_iff.mp identity_accepted

/-- Universal introduction and elimination use the object binder rather than
an untracked free name. -/
def universallyReflexive : Proposition :=
  .all (.imp (.atom 2 [.bvar 0]) (.atom 2 [.bvar 0]))

def universalIdentityProof : Proof :=
  .abstractTerm
    (.abstractProof (.atom 2 [.bvar 0]) (.bound 0))

theorem universal_identity_accepted :
    check ⟨[]⟩ [] universallyReflexive universalIdentityProof = true := by
  decide

def instantiateUniversalIdentity : Proof :=
  .applyTerm universalIdentityProof (.constant 7)

theorem universal_identity_instantiated :
    check ⟨[]⟩ []
      (.imp (.atom 2 [.constant 7]) (.atom 2 [.constant 7]))
      instantiateUniversalIdentity = true := by
  decide

/-- Negative control: modus ponens cannot splice an argument proving the wrong
premise. -/
def pImpliesQ : Proof := .axiomRef 0
def proofOfWrongPremise : Proof := .axiomRef 1

theorem wrong_premise_rejected :
    check ⟨[.imp p q, q]⟩ [] q
      (.applyProof pImpliesQ proofOfWrongPremise) = false := by
  decide

/-- Negative control: a term containing an unbound object variable cannot be
used for universal elimination at the closed boundary. -/
theorem unbound_term_rejected :
    check ⟨[]⟩ []
      (.imp (.atom 2 [.bvar 0]) (.atom 2 [.bvar 0]))
      (.applyTerm universalIdentityProof (.bvar 0)) = false := by
  decide

/-- Crossing a new object binder lifts an older proof-bound proposition.  It
therefore cannot be recovered under a freshly captured index zero. -/
def captureAttempt : Proof :=
  .abstractTerm (.hypothesis (.atom 3 [.bvar 0]))

theorem binder_capture_attempt_rejected :
    infer ⟨[]⟩ [.atom 3 [.bvar 0]] [] 1 captureAttempt = none := by
  decide

end Canary

#print axioms infer_sound
#print axioms infer_complete
#print axioms check_eq_true_iff
#print axioms derivable_iff_exists_accepted
#print axioms Canary.identity_hasProof
#print axioms Canary.wrong_premise_rejected
#print axioms Canary.unbound_term_rejected
#print axioms Canary.binder_capture_attempt_rejected

end Mettapedia.GSLT.LanguageDef.IsabellePureMetaCore
