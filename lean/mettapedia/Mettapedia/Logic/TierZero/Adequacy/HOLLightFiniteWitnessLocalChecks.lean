import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteWitnesses

/-!
# Original local declaration checks observe finite certificate support

These congruences refer to the original source admission functions. Only
actual constant annotations can query the certificate provider. Source
binding checks, declaration freshness, provenance and all other parameters
remain those of the original operation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteWitnessLocalChecks

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open HOLLightFiniteWitnesses

local instance : DecidableEq Const := SyntaxEncoding.constantCodec.decEq
local instance : DecidableEq Ty := SyntaxEncoding.tyCodec.decEq

universe uA
variable {A : Type uA}

def unionKeys (keys : A → Finset Key) : List A → Finset Key
  | [] => ∅
  | first :: rest => keys first ∪ unionKeys keys rest

theorem key_member_subset (keys : A → Finset Key) {values : List A} {value : A}
    (member : value ∈ values) : keys value ⊆ unionKeys keys values := by
  induction values with
  | nil => simp at member
  | cons first rest earlier =>
      rcases List.mem_cons.mp member with rfl | remaining
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (earlier remaining) Finset.subset_union_right

def sourceKeys (source : SourceTerm) : Finset Key := termKeys (source.toDB [])

private theorem source_checked_term (source : SourceTerm) (canonical : CanonicalTerm)
    (checked : source.check = some canonical) : canonical.term = source.toDB [] := by
  unfold SourceTerm.check at checked
  dsimp only at checked
  split at checked
  · cases Option.some.inj checked
    rfl
  · cases checked

theorem source_check_agree (signature : Signature) (first second : InstanceWitnesses)
    (source : SourceTerm) (agrees : Agree (sourceKeys source) first second) :
    checkSource signature first source = checkSource signature second source := by
  cases checked : source.check with
  | none => simp [checkSource, checked]
  | some canonical =>
      have same := annotations_agree signature first second canonical.term (by
        rw [source_checked_term source canonical checked]
        exact agrees)
      simp only [checkSource, checked]
      change (if annotationsFormedB signature first canonical.term then some canonical else none) =
        (if annotationsFormedB signature second canonical.term then some canonical else none)
      rw [same]

theorem constant_admission_agree (context : TheoryContext) (first second : InstanceWitnesses)
    (name : Name) (body : SourceTerm) (agrees : Agree (sourceKeys body) first second) :
    admitConstantInTheory context first name body = admitConstantInTheory context second name body := by
  unfold admitConstantInTheory
  rw [source_check_agree context.signature first second body agrees]

def typeInputKeys (request : TypeOperatorDefinitionRequest) : Finset Key :=
  match request.existence.sequent.concl.applicationView? with
  | none => ∅
  | some view => termKeys view.function.term ∪ termKeys view.argument.term

theorem type_application_admission_agree (context : TheoryContext) (first second : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (agrees : Agree (termKeys predicate.term ∪ termKeys witness.term) first second) :
    admitTypeInTheoryFromApplication context first request predicate witness application =
      admitTypeInTheoryFromApplication context second request predicate witness application := by
  unfold admitTypeInTheoryFromApplication
  rw [annotations_agree context.signature first second predicate.term (agrees.mono Finset.subset_union_left),
    annotations_agree context.signature first second witness.term (agrees.mono Finset.subset_union_right)]

theorem type_admission_agree (context : TheoryContext) (first second : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (agrees : Agree (typeInputKeys request) first second) :
    admitSourceTypeInTheory context first request = admitSourceTypeInTheory context second request := by
  cases viewed : request.existence.sequent.concl.applicationView? with
  | none => simp [admitSourceTypeInTheory, viewed]
  | some view =>
      have same := type_application_admission_agree context first second request view.function view.argument view.semantics
        (by simpa only [typeInputKeys, viewed] using agrees)
      simp only [admitSourceTypeInTheory, viewed, same]

def requestKeys : RuleRequest → Finset Key
  | .inference request => unionKeys termKeys (InferenceFormation.terms request)
  | .axiom _ => ∅

theorem request_check_agree (signature : Signature) (first second : InstanceWitnesses)
    (request : RuleRequest) (agrees : Agree (requestKeys request) first second) :
    ProofExecution.Registered.requestFormedB signature first request =
      ProofExecution.Registered.requestFormedB signature second request := by
  cases request with
  | inference request =>
      simp only [ProofExecution.Registered.requestFormedB, InferenceFormation.check]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro checked term member
        rw [← annotations_agree signature first second term (agrees.mono (key_member_subset termKeys member))]
        exact checked term member
      · intro checked term member
        rw [annotations_agree signature first second term (agrees.mono (key_member_subset termKeys member))]
        exact checked term member
  | «axiom» sequent => rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteWitnessLocalChecks
