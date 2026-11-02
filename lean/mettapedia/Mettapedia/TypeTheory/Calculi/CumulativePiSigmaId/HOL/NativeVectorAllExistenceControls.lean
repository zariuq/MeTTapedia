import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllEvidenceControls

/-!
# Inhabited and empty fibres for actual All existence

Boolean lists supply lifted least-predicate membership independently of All
membership. The general producer constructs their bundle existence. An empty
head predicate makes a nonempty bundle impossible in the realizable profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ExistenceControls
open Mettapedia.Logic
open EvidenceControls
open HOL.CurriedPredicates
local infixr:60 " ⇒ " => HOL.Ty.arr

def computation : Existence.ComputationPremises original selection assumptions :=
  ⟨choice, recursion, headLaw, tailLaw⟩

theorem computation_free : computation.FunctionExtensionalityFree := ⟨True.intro, True.intro, True.intro, True.intro⟩

def rawVector : List Bool → HOL.ClosedTerm Const V
  | [] => original.nil
  | value :: rest => (NativeVectorComputationRows.GuardedFamily.algebra original).consValue
      (numberCode rest.length) (.const (.element value)) (rawVector rest)

def head_lifted (value : Bool) : HOL.ProofSyntax Const assumptions
    (.app (Existence.lifted original A predicate) (.const (.element value))) :=
  .impE (.eqPropER (Existence.lifted_apply original A predicate (.const (.element value))))
    (.andI (Evidence.full_member _) (existsValue_intro [] (.app predicate (.const (.element value))) PUnit.unit
      witness (head_member _)))

theorem head_lifted_free (value : Bool) : (head_lifted value).FunctionExtensionalityFree := by
  simp only [head_lifted, HOL.ProofSyntax.FunctionExtensionalityFree, Existence.lifted_apply_free,
    Evidence.full_member_free, existsValue_intro_free, head_member, true_and]

def lifted_member : (values : List Bool) → HOL.ProofSyntax Const assumptions
    ((NativeVectorComputationRows.GuardedFamily.algebra original).member
      (Existence.lifted original A predicate) (numberCode values.length) (rawVector values))
  | [] => (NativeVectorComputationRows.GuardedFamily.algebra original).nil_member _
  | value :: rest => (NativeVectorComputationRows.GuardedFamily.algebra original).cons_member _
      (numberCode rest.length) (.const (.element value)) (rawVector rest) (head_lifted value) (lifted_member rest)

theorem lifted_member_free (values : List Bool) : (lifted_member values).FunctionExtensionalityFree := by
  induction values with
  | nil => exact HOL.IndexedVectorPredicate.Signature.nil_member_free _ _
  | cons value rest previous =>
      exact HOL.IndexedVectorPredicate.Signature.cons_member_free _ _ _ _ _ _ _ (head_lifted_free value) previous

def bundle (values : List Bool) : HOL.ProofSyntax Const assumptions
    (Existence.query original pairs witness selection A predicate (numberCode values.length) (rawVector values)) :=
  Existence.produce original pairs witness selection A predicate _ _ computation (lifted_member values)

theorem bundle_free (values : List Bool) : (bundle values).FunctionExtensionalityFree :=
  Existence.produce_free original pairs witness selection A predicate _ _ computation (lifted_member values)
    computation_free (lifted_member_free values)

theorem bundle_holds (values : List Bool) :
    (model.denote (Existence.query original pairs witness selection A predicate
      (numberCode values.length) (rawVector values)) emptyValues).down :=
  HOL.Soundness.extDerivation_sound (bundle values).erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable

def emptyPredicate : HOL.ClosedTerm Const (E ⇒ W ⇒ .prop) := .lam (.lam .bot)

theorem empty_head_bundle_refused :
    ¬ (model.denote (Existence.query original pairs witness selection A emptyPredicate
      (numberCode 1) (vectorCode [true])) emptyValues).down := by
  rw [Existence.query, existsValue_nil_denote]
  rintro ⟨point, _, member⟩
  have interpreted := Interpretation.cons_denote original pairs witness selection A emptyPredicate choice recursion
    model emptyValues (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable (numberCode 0) (.const (.element true)) (vectorCode []) headLaw tailLaw
    point (model.base_mem .evidence point)
  obtain ⟨_, _, _, _, _, impossible, _⟩ := interpreted.mp member
  exact impossible

theorem deleting_head_existence_refused : ¬ Nonempty (HOL.ProofSyntax Const assumptions
    (Existence.query original pairs witness selection A emptyPredicate (numberCode 1) (vectorCode [true]))) := by
  rintro ⟨proof⟩
  exact empty_head_bundle_refused (HOL.Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable)

#print axioms bundle_free
#print axioms deleting_head_existence_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ExistenceControls
