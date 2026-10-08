import Mettapedia.Logic.HostingStyles.Universality
import Mettapedia.GSLT.Contexts.ReductionProfiles

/-!
# One class of sources: rule signatures with a reduction on their derivations

The theory of a proof system (`RuleSignature.proofTheory`) has no reduction,
so the two clauses of `Hosting` about transitions hold of every map out of it
for want of transitions.  A computational theory has reduction, and there the
two clauses carry the content.  This module puts both in one class.

## The class

`Reducing source`: the theory of a rule signature, read at a congruence on
its derivations and at a reduction on them
(`RuleSignature.reducingTheory`).

* A proof system is the case of no reduction (`proofTheory_reducing`).
* A proof system with a normalization step is a member: the worked logic with
  the contraction of the axiom `K` (`intReducing`).
* A calculus is a member through its formation rules: its terms are the
  derivations of the signature whose rules are its term formers, and its
  steps are the reduction.  This is done for the terms of the λΠ-calculus
  modulo in `TermsAsDerivations`.

## A host for every family in the class

For a family of members indexed by a type, at the identity congruence, the
union of the signatures with the reduction of each member on its own
judgments is again a member (`sumReducing_reducing`) and hosts every member
of the family (`sumReducing_hostsEvery`).  The inclusion is the existing
`injectMap`, read at the two reductions.  Now the three clauses of hosting
are each proved: the inclusion reflects identity of derivations, sends a step
of a member to a step of the union, and every step of an included derivation
is the inclusion of a step.

The class has members in every universe of judgments, so no theory hosts all
of it; the statement is for a family.

## Separation: the clauses on transitions have content

For the worked logic with the contraction of `K` (`detourProof φ` reduces to
`identityProof φ`):

* forgetting the reduction reflects the static equivalence and is not
  hosting: it does not preserve the transition
  (`forgetDiscard_not_hosting`);
* adding the reduction reflects the static equivalence and is not hosting:
  the image has a transition that the source does not account for
  (`adjoinDiscard_not_hosting`);
* no theory without reduction hosts it (`intReducing_not_hosted_by_static`):
  not the framework with rules as constants, which hosts the same logic
  without its reduction (`framework_not_hosting_intReducing`), and not the
  theory of a semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open LO
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Framework

/-! ## The class -/

namespace RuleSignature

variable {J : Type} (P : RuleSignature J)

/-- **The theory of a rule signature with a reduction on its derivations.** -/
noncomputable def reducingTheory (congruence : P.ProofCongruence)
    (reduction : (P.proofTheory congruence).Reduction) : ContextTheory.{0} :=
  (P.proofTheory congruence).reducing reduction

/-- When every derivation is kept apart, every relation on the derivations of
each judgment is a reduction. -/
noncomputable def reductionOfIdentity (step : {j : J} → P.Proof j → P.Proof j → Prop) :
    (P.proofTheory (ProofCongruence.identity P)).Reduction where
  step := step
  left := fun {_ term term' next} same reduces => by
    have equal : term = term' := same
    subst equal
    exact ⟨next, reduces, rfl⟩
  right := fun {_ term next next'} reduces same => by
    have equal : next = next' := same
    subst equal
    exact reduces

/-- With no reduction it is the theory of the proof system. -/
theorem reducingTheory_none (congruence : P.ProofCongruence) :
    P.reducingTheory congruence (ContextTheory.Reduction.none _) = P.proofTheory congruence :=
  rfl

end RuleSignature

/-- **The common class of sources**: the theories of rule signatures, each at
a congruence on its derivations and a reduction on them. -/
def Reducing (source : ContextTheory.{0}) : Prop :=
  ∃ (J : Type) (P : RuleSignature J) (congruence : P.ProofCongruence)
    (reduction : (P.proofTheory congruence).Reduction),
    source = P.reducingTheory congruence reduction

/-- Every proof system is in the class, at every congruence. -/
theorem proofTheory_reducing {J : Type} (P : RuleSignature J) (congruence : P.ProofCongruence) :
    Reducing (P.proofTheory congruence) :=
  ⟨J, P, congruence, ContextTheory.Reduction.none _, rfl⟩

/-! ## A host for a family -/

section Family

variable {Index : Type} {J : Index → Type} (P : (index : Index) → RuleSignature (J index))
  (step : (index : Index) → {j : J index} → (P index).Proof j → (P index).Proof j → Prop)

/-- A derivation of the union at a judgment of a member is the inclusion of a
derivation of the member. -/
theorem inject_project {judgment : Σ index, J index}
    (proof : (sumSignature P).Proof judgment) :
    inject P judgment.1 (project P proof) = proof := by
  induction proof using RuleSignature.Proof.induction with
  | @node judgment shape children ih =>
      change (sumSignature P).node (j := ⟨judgment.1, judgment.2⟩) shape
        (fun position => inject P judgment.1 (project P (children position))) = _
      exact congrArg ((sumSignature P).node shape) (funext ih)

/-- The reduction of the union: a derivation at a judgment of a member
reduces as the derivation of the member does. -/
def sumStep {judgment : Σ index, J index} (first second : (sumSignature P).Proof judgment) :
    Prop :=
  step judgment.1 (project P first) (project P second)

/-- On included derivations the reduction of the union is that of the
member. -/
theorem sumStep_inject_iff (index : Index) {j : J index} (first next : (P index).Proof j) :
    sumStep P step (inject P index first) (inject P index next) ↔ step index first next := by
  unfold sumStep
  rw [project_inject, project_inject]

theorem sumStep_inject_left (index : Index) {j : J index} (first : (P index).Proof j)
    (next : (sumSignature P).Proof ⟨index, j⟩) :
    sumStep P step (inject P index first) next ↔ step index first (project P next) := by
  unfold sumStep
  rw [project_inject]

/-- **The union of a family of members**, with the reduction of each member
on its own judgments. -/
noncomputable def sumReducing : ContextTheory.{0} :=
  (sumSignature P).reducingTheory (RuleSignature.ProofCongruence.identity _)
    ((sumSignature P).reductionOfIdentity (sumStep P step))

/-- A member of the family: a rule signature with its reduction, derivations
kept apart. -/
noncomputable def reducingMember (index : Index) : ContextTheory.{0} :=
  (P index).reducingTheory (RuleSignature.ProofCongruence.identity _)
    ((P index).reductionOfIdentity (step index))

/-- The inclusion of a member into the union, read at the two reductions. -/
noncomputable def injectReducingMap (index : Index) :
    ContextMap (reducingMember P step index) (sumReducing P step) :=
  (injectMap P index).atReductions _ _

/-- **The inclusion is hosting**, and each of the three clauses is proved: it
reflects identity of derivations, it sends a step of the member to a step of
the union, and every step of an included derivation is the inclusion of a
step of the member. -/
theorem injectReducingMap_hosting (index : Index) : (injectReducingMap P step index).Hosting := by
  refine ((injectMap P index).atReductions_hosting_iff _ _).mpr
    ⟨(injectMap P index).reflectsEquations_of_faithful (injectMap_hosting P index).faithful, ?_, ?_⟩
  · intro j first next reduces
    exact (sumStep_inject_iff P step index first next).mpr reduces
  · intro j first next reduces
    exact ⟨project P next, (sumStep_inject_left P step index first next).mp reduces,
      (inject_project P next).symm⟩

/-- The members of the family. -/
def ReducingMember (source : ContextTheory.{0}) : Prop :=
  ∃ index, source = reducingMember P step index

/-- **The union hosts every member of the family.** -/
theorem sumReducing_hostsEvery : HostsEvery (sumReducing P step) (ReducingMember P step) := by
  rintro source ⟨index, rfl⟩
  exact ⟨injectReducingMap P step index, injectReducingMap_hosting P step index⟩

/-- The members and their union are in the class. -/
theorem reducingMember_reducing (index : Index) : Reducing (reducingMember P step index) :=
  ⟨_, P index, _, _, rfl⟩

theorem sumReducing_reducing : Reducing (sumReducing P step) :=
  ⟨_, sumSignature P, _, _, rfl⟩

end Family

/-! ## A proof system with a normalization step -/

/-- **One discard step**: a derivation that uses the axiom `K` to discard a
derivation is contracted to the derivation it keeps. -/
inductive Discards : {φ : IntFormula} → IntProof φ → IntProof φ → Prop where
  | contract {φ ψ : IntFormula} (kept : IntProof φ) (discarded : IntProof ψ) :
      Discards (mdpProof (mdpProof (axiomProof (.implyK φ ψ)) kept) discarded) kept

/-- The longer derivation of `φ ➝ φ` contracts to the usual one. -/
theorem detour_discards (φ : IntFormula) : Discards (detourProof φ) (identityProof φ) :=
  .contract _ _

/-- **The worked logic with the contraction of `K` as its reduction.** -/
noncomputable def intReducing : ContextTheory.{0} :=
  intSignature.reducingTheory (RuleSignature.ProofCongruence.identity _)
    (intSignature.reductionOfIdentity Discards)

theorem intReducing_reducing : Reducing intReducing :=
  ⟨_, intSignature, _, _, rfl⟩

/-- **Positive**: it has a transition. -/
theorem intReducing_step (φ : IntFormula) :
    intReducing.rewrites (interface := (φ ➝ φ : IntFormula)) (detourProof φ) (identityProof φ) :=
  detour_discards φ

/-- **Negative**: the worked logic without the reduction has none. -/
theorem int_static :
    (intSignature.proofTheory (RuleSignature.ProofCongruence.identity _)).Static :=
  fun _ _ step => step

/-! ## Separation: the clauses on transitions have content -/

/-- **Forgetting the reduction is not hosting**: it does not preserve the
transition. -/
theorem forgetDiscard_not_hosting :
    ¬ ((ContextMap.id (intSignature.proofTheory (RuleSignature.ProofCongruence.identity _))).atReductions
        (intSignature.reductionOfIdentity Discards) (ContextTheory.Reduction.none _)).Hosting :=
  ContextMap.forget_not_hosting _ _ (detour_discards (.atom 0))

/-- **Adding the reduction is not hosting**: the image has a transition that
the source does not account for. -/
theorem adjoinDiscard_not_hosting :
    ¬ ((ContextMap.id (intSignature.proofTheory (RuleSignature.ProofCongruence.identity _))).atReductions
        (ContextTheory.Reduction.none _) (intSignature.reductionOfIdentity Discards)).Hosting :=
  ContextMap.adjoin_not_hosting _ _ (detour_discards (.atom 0))

/-- Both maps reflect the static equivalence: only the clauses on transitions
fail. -/
theorem discard_maps_reflectEquations :
    ((ContextMap.id (intSignature.proofTheory (RuleSignature.ProofCongruence.identity _))).atReductions
        (intSignature.reductionOfIdentity Discards)
        (ContextTheory.Reduction.none _)).ReflectsEquations ∧
      ((ContextMap.id (intSignature.proofTheory (RuleSignature.ProofCongruence.identity _))).atReductions
        (ContextTheory.Reduction.none _)
        (intSignature.reductionOfIdentity Discards)).ReflectsEquations :=
  ⟨ContextMap.id_atReductions_reflectsEquations _ _ _,
    ContextMap.id_atReductions_reflectsEquations _ _ _⟩

/-- **No theory without reduction hosts the worked logic with its
reduction.** -/
theorem intReducing_not_hosted_by_static {target : ContextTheory.{0}} (static : target.Static)
    (map : ContextMap intReducing target) : ¬ map.Hosting :=
  map.not_hosting_of_step_into_static static (intReducing_step (.atom 0))

/-- The framework with rules as constants has no reduction. -/
theorem frameworkTheory_static {B : Type} (signature : Signature B) :
    (frameworkTheory signature).Static :=
  fun _ _ step => step

/-- **The framework hosts the worked logic** (existing
`encodingMap_hosting`) **and not the worked logic with its reduction**: the
same map, read at the reduction, is not hosting. -/
theorem framework_not_hosting_intReducing
    (map : ContextMap intReducing (frameworkTheory intFinitary.signature)) : ¬ map.Hosting :=
  intReducing_not_hosted_by_static (frameworkTheory_static _) map

/-- Nor does the theory of any semantics. -/
theorem shallow_not_hosting_intReducing {Point : Type} (holds : Point → IntFormula → Prop)
    (map : ContextMap intReducing (shallowTheory holds)) : ¬ map.Hosting :=
  intReducing_not_hosted_by_static (fun _ _ step => step) map

#print axioms inject_project
#print axioms injectReducingMap_hosting
#print axioms sumReducing_hostsEvery
#print axioms forgetDiscard_not_hosting
#print axioms adjoinDiscard_not_hosting
#print axioms intReducing_not_hosted_by_static
#print axioms framework_not_hosting_intReducing

end Mettapedia.Logic.HostingStyles
