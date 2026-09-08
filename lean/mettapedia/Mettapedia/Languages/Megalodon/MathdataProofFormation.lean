import Mettapedia.Languages.Megalodon.MathdataKernel
import Mettapedia.Languages.Megalodon.MathdataTypeFormation

/-!
# Ordinary hypotheses and prefix-polymorphic propositions

Megalodon's source `PLam` rule checks that its hypothesis has ordinary type
`Prop`. The prefix-polymorphic proposition check has a different role: it
admits a leading type-universal binder at a proposition boundary. These checks
must not be interchanged inside implication introduction.

The positive controls retain ordinary implication introduction and a genuine
type-polymorphic identity proof. The negative controls reject a prefix-bound
hypothesis and its malformed implication. No formation theorem for arbitrary
unvalidated environments or proof contexts is asserted.

Proof-level type application, unlike term-level type application, does not
check the replacement type in the source kernel. Consequently, even the empty
environment admits a raw proof whose inferred proposition is unformed. The
source document admission boundary separately checks its declared proposition;
these controls distinguish that boundary from raw proof comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.MathdataProofFormation

open MathdataKernel

/-- A prefix type-universal proposition is never an ordinary `Prop` term. -/
theorem inferTerm_typeAll (environment : Environment) (depth : Nat)
    (context : List Tp) (body : Tm) :
    inferTerm environment depth context (.typeAll body) = none := rfl

/-- Implication introduction rejects a prefix type binder before inspecting
its proof body, at every fuel, environment and context. -/
theorem inferProof_proofLam_typeAll (environment : Environment) (fuel depth : Nat)
    (termContext : List Tp) (proofContext : List Tm) (proposition : Tm) (proof : Pf) :
    inferProof environment fuel depth termContext proofContext
      (.proofLam (.typeAll proposition) proof) = none := by
  simp [inferProof, inferTerm]

def ordinary : Tm := .all .prop (.db 0)
def prefixFormula : Tm := .typeAll ordinary
def identity : Pf := .proofLam ordinary (.hyp 0)
def polymorphicIdentity : Pf := .typeLam identity
def malformed : Tm := .imp prefixFormula prefixFormula
def malformedProof : Pf := .proofLam prefixFormula (.hyp 0)

theorem ordinary_identity_accepted :
    checkProof {} 8 0 [] [] identity (.imp ordinary ordinary) = true := by
  simp [identity, ordinary, checkProof, checkNormalizedProof, inferProof, inferTerm,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tp.plainWellFormed]

/-- Legitimate type-polymorphic proof abstraction remains accepted. -/
theorem polymorphic_identity_accepted :
    checkProof {} 8 0 [] [] polymorphicIdentity (.typeAll (.imp ordinary ordinary)) = true := by
  simp [polymorphicIdentity, identity, ordinary, checkProof, checkNormalizedProof,
    inferProof, inferTerm, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Tp.plainWellFormed]

/-- Prefix propositions remain valid at their own formation boundary. -/
theorem prefix_proposition_formed : checkProposition {} 0 [] prefixFormula = true := by
  simp [prefixFormula, ordinary, checkProposition, inferTerm, Tp.plainWellFormed]

/-- The former raw acceptance path is closed, while the independently stated
proposition checker also rejects the malformed implication. -/
theorem malformed_implication_rejected :
    inferProof {} 8 0 [] [] malformedProof = none ∧
      checkProof {} 8 0 [] [] malformedProof malformed = false ∧
      checkProposition {} 0 [] malformed = false := by
  simp [malformedProof, malformed, prefixFormula, ordinary, checkProof, checkNormalizedProof,
    inferProof, checkProposition, inferTerm, normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne]

/-! ## Type specialization requires an independent formation boundary -/

/-- The body of the polymorphic predicate identity, with both the predicate
and its argument retained under their native term binders. -/
def predicateIdentityBody : Tm :=
  .all (.arr (.var 0) .prop)
    (.all (.var 0) (.imp (.app (.db 1) (.db 0)) (.app (.db 1) (.db 0))))

def predicateIdentityProof : Pf :=
  .typeLam (.termLam (.arr (.var 0) .prop)
    (.termLam (.var 0) (.proofLam (.app (.db 1) (.db 0)) (.hyp 0))))

/-- The source schematic theorem is proved without axioms or declarations. -/
theorem predicate_identity_inferred :
    inferProof {} 8 0 [] [] predicateIdentityProof = some (.typeAll predicateIdentityBody) := by
  simp [predicateIdentityProof, predicateIdentityBody, inferProof, inferTerm,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne, Tp.plainWellFormed]

/-- The inferred schema is independently well formed at the proposition boundary. -/
theorem predicate_identity_formed :
    checkProposition {} 0 [] (.typeAll predicateIdentityBody) = true := by decide

/-- Raw proof-level specialization accepts every replacement type. This records
the source rule faithfully; it does not assert that every instance is formed. -/
theorem predicate_identity_specialized (replacement : Tp) :
    inferProof {} 8 0 [] [] (.typeApp predicateIdentityProof replacement) =
      some (Tm.typeInstantiate replacement predicateIdentityBody) := by
  simp [inferProof, predicate_identity_inferred]

theorem predicate_identity_instance_normalized (replacement : Tp) :
    normalize {} 8 (Tm.typeInstantiate replacement predicateIdentityBody) =
      some (Tm.typeInstantiate replacement predicateIdentityBody) := by
  simp [predicateIdentityBody, Tm.typeInstantiate, Tm.typeInstantiateAt,
    Tp.instantiateAt, Tp.shift_zero, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne]

theorem predicate_identity_instance_checked (replacement : Tp) :
    checkProof {} 8 0 [] [] (.typeApp predicateIdentityProof replacement)
      (Tm.typeInstantiate replacement predicateIdentityBody) = true := by
  simp [checkProof, checkNormalizedProof, predicate_identity_instance_normalized,
    predicate_identity_specialized]

/-- A function type is a legitimate specialization: the resulting theorem
quantifies over predicates on functions and over their function arguments. -/
theorem higher_order_predicate_identity_accepted :
    let replacement := Tp.arr (.base 0) (.base 1)
    replacement.plainWellFormed 0 = true ∧
      checkProposition {} 0 [] (Tm.typeInstantiate replacement predicateIdentityBody) = true ∧
      checkProof {} 8 0 [] [] (.typeApp predicateIdentityProof replacement)
        (Tm.typeInstantiate replacement predicateIdentityBody) = true := by
  exact ⟨by decide, by decide, predicate_identity_instance_checked _⟩

/-- The raw proof checker accepts this out-of-scope specialization, whereas
the independently applied proposition-formation check rejects its goal. -/
theorem unscoped_specialization_accepted_but_unformed :
    Tp.plainWellFormed 0 (.var 0) = false ∧
      inferProof {} 8 0 [] [] (.typeApp predicateIdentityProof (.var 0)) =
        some (Tm.typeInstantiate (.var 0) predicateIdentityBody) ∧
      checkProof {} 8 0 [] [] (.typeApp predicateIdentityProof (.var 0))
        (Tm.typeInstantiate (.var 0) predicateIdentityBody) = true ∧
      checkProposition {} 0 [] (Tm.typeInstantiate (.var 0) predicateIdentityBody) = false := by
  exact ⟨by decide, predicate_identity_specialized _, predicate_identity_instance_checked _, by decide⟩

/-- Environment validity alone cannot supply a formation theorem for raw
proof inference: the counterexample already uses the empty environment. -/
theorem not_inferProof_implies_formation :
    ¬ (∀ (proof : Pf) (proposition : Tm), inferProof {} 8 0 [] [] proof = some proposition →
      checkProposition {} 0 [] proposition = true) := by
  intro formation
  have formed := formation _ _ (predicate_identity_specialized (.var 0))
  have rejected := unscoped_specialization_accepted_but_unformed.2.2.2
  rw [rejected] at formed
  cases formed

/-! ## A known schema can also escape its prefix position -/

def prefixKnownEnvironment : Environment :=
  { known := [⟨"predicate-identity", .typeAll predicateIdentityBody⟩] }

/-- The stored schema has a proof and an independent formation check in the
empty environment; the negative control does not insert an arbitrary axiom. -/
theorem stored_prefix_has_independent_proof :
    inferProof {} 8 0 [] [] predicateIdentityProof = some (.typeAll predicateIdentityBody) ∧
      checkProposition {} 0 [] (.typeAll predicateIdentityBody) = true :=
  ⟨predicate_identity_inferred, predicate_identity_formed⟩

/-- Checking type-application arguments alone is insufficient: this proof uses
no type application, but puts a known prefix schema inside an implication. -/
theorem known_prefix_in_implication_accepted_but_unformed :
    checkProof prefixKnownEnvironment 8 0 [] []
        (.proofLam ordinary (.known "predicate-identity"))
        (.imp ordinary (.typeAll predicateIdentityBody)) = true ∧
      checkProposition prefixKnownEnvironment 0 []
        (.imp ordinary (.typeAll predicateIdentityBody)) = false := by
  constructor
  · simp [prefixKnownEnvironment, ordinary, predicateIdentityBody, checkProof,
      checkNormalizedProof, inferProof, inferTerm, normalize, deltaNormalize,
      Tm.normalize, Tm.normalizeOne, Environment.lookupKnown?, lookupKnownList?,
      Tp.plainWellFormed]
  · decide

#print axioms inferProof_proofLam_typeAll
#print axioms ordinary_identity_accepted
#print axioms polymorphic_identity_accepted
#print axioms malformed_implication_rejected
#print axioms predicate_identity_inferred
#print axioms higher_order_predicate_identity_accepted
#print axioms unscoped_specialization_accepted_but_unformed
#print axioms not_inferProof_implies_formation
#print axioms known_prefix_in_implication_accepted_but_unformed

end Mettapedia.Languages.Megalodon.MathdataProofFormation
