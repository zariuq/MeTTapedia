import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllPositionEvidence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistenceControls

/-!
# End-to-end positional witness controls

The original vector membership is constructed without a witnessed-element
predicate. A separate pointwise proof supplies position witnesses, after
which the new producer constructs actual All existence. The realizable
empty-head model refutes omitting the position-witness premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.PositionEvidenceControls
open Mettapedia.Logic
open EvidenceControls
open HOL.FiniteConstructorEncoding HOL.CurriedPredicates
open ExistenceControls (rawVector computation computation_free)
local infixr:60 " ⇒ " => HOL.Ty.arr

def originalMember : (values : List Bool) → HOL.ProofSyntax Const assumptions
    ((PositionEvidence.signature original).member A (numberCode values.length) (rawVector values))
  | [] => (PositionEvidence.signature original).nil_member A
  | value :: rest => (PositionEvidence.signature original).cons_member A (numberCode rest.length)
      (.const (.element value)) (rawVector rest) (Evidence.full_member _) (originalMember rest)

theorem originalMember_free (values : List Bool) : (originalMember values).FunctionExtensionalityFree := by
  induction values with
  | nil => exact HOL.IndexedVectorPredicate.Signature.nil_member_free _ _
  | cons value rest previous =>
      exact HOL.IndexedVectorPredicate.Signature.cons_member_free _ _ _ _ _ _ _ (Evidence.full_member_free _) previous

def boundWitness : HOL.ProofSyntax Const (HOL.weakenHyps assumptions)
    (.app (.app (HOL.weaken predicate) (.var .vz)) (HOL.weaken witness)) :=
  .impE (.eqPropER (.eqTrans
    (.eqApp (HOL.weaken witness) (.beta (.var .vz) (HOL.weaken (HOL.weaken pointPredicate))))
    (.beta (HOL.weaken witness) (.eq (.var .vz) (HOL.weaken (HOL.weaken witness)))))) (.eqRefl (HOL.weaken witness))

def pointwise : HOL.ClosedFormula Const := .all (existsValue [] (.app (HOL.weaken predicate) (.var .vz)))

def pointwiseProof : HOL.ProofSyntax Const assumptions pointwise :=
  .allI (existsValue_intro [] (.app (HOL.weaken predicate) (.var .vz)) PUnit.unit (HOL.weaken witness) boundWitness)

theorem pointwiseProof_free : pointwiseProof.FunctionExtensionalityFree := by
  unfold pointwiseProof
  apply existsValue_intro_free
  simp [boundWitness, HOL.ProofSyntax.FunctionExtensionalityFree]

def conditionBranch (index : HOL.ClosedTerm Const N) (vector : HOL.ClosedTerm Const V) :
    ArgumentProof assumptions (PositionEvidence.Fields original) (PositionEvidence.body original predicate index vector) := by
  intro Γ images fields
  have present : HOL.ProofSyntax Const (assumptions.map (HOL.subst images))
      (existsValue [] (.app (HOL.subst images predicate) fields.2.1)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.allE fields.2.1 (pointwiseProof.subst images))
    simp only [HOL.instantiate, HOL.subst, existsValue_subst, HOL.subst_weaken,
      HOL.Subst.lift, HOL.Subst.single, HOL.PredicateFixedPoint.subst_single_weaken]
    rfl
  exact .impI (present.prepend _)

theorem conditionBranch_free (index : HOL.ClosedTerm Const N) (vector : HOL.ClosedTerm Const V)
    {Γ : HOL.Ctx Base} (images : HOL.Subst Const [] Γ) (fields : Arguments Const Γ (PositionEvidence.Fields original)) :
    (conditionBranch index vector images fields).FunctionExtensionalityFree := by
  unfold conditionBranch
  simpa only [HOL.ProofSyntax.FunctionExtensionalityFree, HOL.ProofSyntax.prepend,
    HOL.ProofSyntax.functionExtensionalityFree_mono, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_subst] using pointwiseProof_free

def condition (index : HOL.ClosedTerm Const N) (vector : HOL.ClosedTerm Const V) :
    HOL.ProofSyntax Const assumptions (PositionEvidence.condition original predicate index vector) :=
  forallArguments_intro _ _ (conditionBranch index vector)

theorem condition_free (index : HOL.ClosedTerm Const N) (vector : HOL.ClosedTerm Const V) :
    (condition index vector).FunctionExtensionalityFree :=
  forallArguments_intro_free _ _ _ (conditionBranch_free index vector)

def produced (values : List Bool) : HOL.ProofSyntax Const assumptions
    (Existence.query original pairs witness selection A predicate (numberCode values.length) (rawVector values)) :=
  PositionEvidence.produce original pairs witness selection A predicate _ _ computation (originalMember values)
    (condition _ _)

theorem produced_free (values : List Bool) : (produced values).FunctionExtensionalityFree :=
  PositionEvidence.produce_free original pairs witness selection A predicate _ _ computation (originalMember values)
    (condition _ _) computation_free (originalMember_free values) (condition_free _ _)

theorem produced_holds (values : List Bool) :
    (model.denote (Existence.query original pairs witness selection A predicate
      (numberCode values.length) (rawVector values)) emptyValues).down :=
  HOL.Soundness.extDerivation_sound (produced values).erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable

def oneOriginal : HOL.ProofSyntax Const assumptions
    ((PositionEvidence.signature original).member A (numberCode 1) (vectorCode [true])) :=
  .impE (.eqPropEL (NativeVectorComputationRows.GuardedFamily.family_apply ops A (numberCode 1) (vectorCode [true])))
    (NativeVectorComputationRows.GuardedFamily.cons_member ops A (numberCode 0) (.const (.element true)) (vectorCode [])
      (Evidence.full_member _) (NativeVectorComputationRows.GuardedFamily.nil_member ops A))

theorem dropping_position_evidence_refused : ¬ Nonempty (HOL.ProofSyntax Const
    ((PositionEvidence.signature original).member A (numberCode 1) (vectorCode [true]) :: assumptions)
    (Existence.query original pairs witness selection A ExistenceControls.emptyPredicate (numberCode 1) (vectorCode [true]))) := by
  rintro ⟨claimed⟩
  exact ExistenceControls.deleting_head_existence_refused ⟨.impE (.impI claimed) oneOriginal⟩

#print axioms produced_free
#print axioms dropping_position_evidence_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.PositionEvidenceControls
