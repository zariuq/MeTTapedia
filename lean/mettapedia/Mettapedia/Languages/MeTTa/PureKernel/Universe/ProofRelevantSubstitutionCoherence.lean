import Mettapedia.Languages.MeTTa.PureKernel.Universe.ProofRelevantStructuralComputation

/-!
# Coherence capability for proof-relevant root substitution

`ProofRelevantRootComputation` deliberately asks only that every renaming and
substitution maps authored root evidence.  Those operations need not yet form
a functor: preservation of identity and composition is additional structure.

This module makes that missing structure explicit.  The laws use
heterogeneous equality because the evidence fibres are indexed by term
endpoints whose substitution laws are propositional rather than definitional.
It also gives independent positive and negative computations.  Consequently,
no native-calculus host may infer coherent substitution merely from the
existence of a substitution function.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace Declaration

open ProofRelevantStructuralComputation

universe uEvidence

namespace ProofRelevantRootComputation

/-- Proof-relevant root substitution acts functorially on authored evidence.
The endpoint transports forced by `subst_ids` and `subst_comp` are retained
by `HEq`; consumers that choose explicit casts may derive their preferred
homogeneous presentation later. -/
structure SubstitutionCoherent
    {Head : Type}
    (computation : ProofRelevantRootComputation.{uEvidence} Head) : Prop where
  substitute_ids :
    ∀ {n : Nat} {left right : Tm Head n}
      (evidence : computation.Evidence left right),
      HEq (computation.substitute (ids : Sub Head n n) evidence) evidence
  substitute_comp :
    ∀ {n m k : Nat} (later : Sub Head m k) (earlier : Sub Head n m)
      {left right : Tm Head n}
      (evidence : computation.Evidence left right),
      HEq
        (computation.substitute later
          (computation.substitute earlier evidence))
        (computation.substitute
          (fun index => subst later (earlier index)) evidence)

end ProofRelevantRootComputation

/-! ## Positive and negative computations -/

namespace SubstitutionCoherenceCanary

/-- Constant evidence with identity renaming and substitution is coherent. -/
@[reducible] def coherentComputation : ProofRelevantRootComputation Unit where
  Evidence := fun _ _ => Nat
  rename := by
    intro n m renameMap left right evidence
    exact evidence
  substitute := by
    intro n m substitution left right evidence
    exact evidence

def coherentComputationSubstitution :
    coherentComputation.SubstitutionCoherent where
  substitute_ids := by
    intros
    rfl
  substitute_comp := by
    intros
    rfl

/-- This computation keeps identity substitutions inert but stamps every
arity-changing substitution.  It satisfies the original root-computation
interface while violating composition for a round trip through another
arity. -/
@[reducible] def arityChangingStampComputation :
    ProofRelevantRootComputation Unit where
  Evidence := fun _ _ => Nat
  rename := by
    intro n m renameMap left right evidence
    exact evidence
  substitute := by
    intro n m substitution left right evidence
    exact if n = m then evidence else evidence + 1

abbrev constantTerm {n : Nat} : Tm Unit n :=
  .const `Prime.SubstitutionCoherence.Canary

def emptyToOne : Sub Unit 0 1 := fun index => Fin.elim0 index

def oneToEmpty : Sub Unit 1 0 := fun _ => constantTerm

def rootEvidence :
    arityChangingStampComputation.Evidence
      (constantTerm : Tm Unit 0) constantTerm :=
  0

@[simp] theorem sequential_roundTrip_stamp :
    arityChangingStampComputation.substitute oneToEmpty
        (arityChangingStampComputation.substitute emptyToOne rootEvidence) =
      2 :=
  rfl

@[simp] theorem composed_roundTrip_stamp :
    arityChangingStampComputation.substitute
        (fun index => subst oneToEmpty (emptyToOne index)) rootEvidence =
      0 :=
  rfl

/-- The existing `ProofRelevantRootComputation` fields cannot entail
substitution coherence: this legal computation distinguishes sequential
substitution from its syntactic composite. -/
theorem arityChangingStamp_not_substitutionCoherent :
    ¬ arityChangingStampComputation.SubstitutionCoherent := by
  intro coherent
  have comparison := coherent.substitute_comp oneToEmpty emptyToOne rootEvidence
  have homogeneous :
      arityChangingStampComputation.substitute oneToEmpty
          (arityChangingStampComputation.substitute emptyToOne rootEvidence) =
        arityChangingStampComputation.substitute
          (fun index => subst oneToEmpty (emptyToOne index)) rootEvidence :=
    eq_of_heq comparison
  norm_num [arityChangingStampComputation, rootEvidence] at homogeneous

/-- Identity coherence alone does not repair the counterexample. -/
theorem arityChangingStamp_preserves_identity :
    ∀ {n : Nat} {left right : Tm Unit n}
      (evidence : arityChangingStampComputation.Evidence left right),
      HEq
        (arityChangingStampComputation.substitute
          (ids : Sub Unit n n) evidence)
        evidence := by
  intros
  simp [arityChangingStampComputation]

/-- The controls isolate composition: one computation satisfies both laws;
the other satisfies identity but refutes compositionality. -/
theorem substitutionCoherenceBoundary :
    Nonempty coherentComputation.SubstitutionCoherent ∧
      (∀ {n : Nat} {left right : Tm Unit n}
        (evidence : arityChangingStampComputation.Evidence left right),
        HEq
          (arityChangingStampComputation.substitute
            (ids : Sub Unit n n) evidence)
          evidence) ∧
      ¬ arityChangingStampComputation.SubstitutionCoherent :=
  ⟨⟨coherentComputationSubstitution⟩,
    arityChangingStamp_preserves_identity,
    arityChangingStamp_not_substitutionCoherent⟩

end SubstitutionCoherenceCanary

/-! ## Axiom audit -/

#print axioms SubstitutionCoherenceCanary.coherentComputationSubstitution
#print axioms SubstitutionCoherenceCanary.arityChangingStamp_not_substitutionCoherent
#print axioms SubstitutionCoherenceCanary.arityChangingStamp_preserves_identity
#print axioms SubstitutionCoherenceCanary.substitutionCoherenceBoundary

end Declaration
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
