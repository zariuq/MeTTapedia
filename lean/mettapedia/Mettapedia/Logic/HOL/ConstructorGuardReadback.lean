import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.FiniteConstructorProgramReadout
import Mettapedia.Logic.HOL.FiniteConstructorCaseProofs

/-!
# Retained readback of a guarded encoded constructor row

A guard at a known encoded payload recovers that occurrence's original
field predicate. Candidate occurrences and fields are compared by the
existing retained encoding readout, retaining the supplied hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {assumptions : List (Formula Const Γ)}

def restrictedPredicate_parts (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature))
    (arguments : Arguments Const Γ (signature.get occurrence))
    (present : ProofSyntax Const assumptions
      (applyArguments _ (restrictedPredicate signature occurrence condition payload) arguments)) :
    ProofSyntax Const assumptions
      (.and (applyArguments _ condition arguments) (.eq payload (encode signature occurrence arguments))) := by
  have beta := abstractArguments_beta (assumptions := assumptions) (signature.get occurrence)
    (restrictedBody signature occurrence condition payload)
    (restrictedBody_natural signature occurrence condition payload) arguments
  apply ProofSyntax.castIndices rfl ?_ (.impE (.eqPropEL beta) present)
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [restrictedBody, identityTerm]

theorem restrictedPredicate_parts_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature))
    (arguments : Arguments Const Γ (signature.get occurrence))
    (present : ProofSyntax Const assumptions
      (applyArguments _ (restrictedPredicate signature occurrence condition payload) arguments))
    (free : present.FunctionExtensionalityFree) :
    (restrictedPredicate_parts signature occurrence condition payload arguments present).FunctionExtensionalityFree := by
  unfold restrictedPredicate_parts
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨abstractArguments_beta_free _ _ _ _, free⟩

end Mettapedia.Logic.HOL.FiniteConstructorEncoding

namespace Mettapedia.Logic.HOL.CurriedPredicates

open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

theorem functionType_prop (fields : List (Ty Base)) : FunctionType fields .prop = handlerType fields := by
  induction fields with
  | nil => rfl
  | cons type rest previous => exact congrArg (Ty.arr type) previous

def predicateFunction (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields)) :
    Term Const Γ (FunctionType fields .prop) :=
  (functionType_prop fields).symm ▸ predicate

private theorem castFunction_apply {domain first last : Ty Base} (same : first = last)
    (function : Term Const Γ (domain ⇒ first)) (argument : Term Const Γ domain) :
    Term.app ((congrArg (Ty.arr domain) same) ▸ function) argument = same ▸ Term.app function argument := by
  cases same
  rfl

theorem apply_predicateFunction (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (arguments : Arguments Const Γ fields) :
    applyFields fields (predicateFunction fields predicate) arguments = applyArguments fields predicate arguments := by
  induction fields with
  | nil => rfl
  | cons type rest previous =>
      have move : Term.app (predicateFunction (type :: rest) predicate) arguments.1 =
          predicateFunction rest (.app predicate arguments.1) :=
        castFunction_apply (functionType_prop rest).symm predicate arguments.1
      change applyFields rest _ arguments.2 = _
      rw [move]
      exact previous (.app predicate arguments.1) arguments.2

end Mettapedia.Logic.HOL.CurriedPredicates

namespace Mettapedia.Logic.HOL.ConstructorDataPredicates

open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {assumptions : List (Formula Const Γ)}

def readOnEncoded (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (occurrence : Fin signature.length) (arguments : Arguments Const Γ (signature.get occurrence))
    (present : ProofSyntax Const assumptions (guard signature conditions (encode signature occurrence arguments))) :
    ProofSyntax Const assumptions (applyArguments _ (conditions occurrence) arguments) := by
  let target := applyArguments _ (conditions occurrence) arguments
  let formulas := List.ofFn (fun selected =>
    restrictedGuard signature selected (conditions selected) (encode signature occurrence arguments))
  apply any_elim formulas target present
  intro selected
  let candidate : Fin signature.length := ⟨selected.val, by simpa only [formulas, List.length_ofFn] using selected.isLt⟩
  let predicate := restrictedPredicate signature candidate (conditions candidate) (encode signature occurrence arguments)
  apply ProofSyntax.impI
  apply FieldCase.eliminate (signature.get candidate) predicate target
  · intro Ξ images candidateArguments
    let shifted := fun selected => HOL.subst images (conditions selected)
    let localAssumptions := applyArguments _ (HOL.subst images predicate) candidateArguments ::
      ((formulas.get selected) :: assumptions).map (HOL.subst images)
    have current : ProofSyntax Const localAssumptions
        (applyArguments _ (restrictedPredicate signature candidate (shifted candidate)
          (HOL.subst images (encode signature occurrence arguments))) candidateArguments) := by
      apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp 0)
      simp only [localAssumptions, List.get_cons_zero, predicate, restrictedPredicate_subst, shifted]
    have parts := restrictedPredicate_parts signature candidate (shifted candidate)
      (HOL.subst images (encode signature occurrence arguments)) candidateArguments current
    have payloads : ProofSyntax Const localAssumptions (.eq (encode signature candidate candidateArguments)
        (encode signature occurrence (substituteArguments images _ arguments))) := by
      apply ProofSyntax.castIndices rfl ?_ (.eqSymm (.andER parts))
      rw [encode_subst]
    have programs := program_equal_of_payload (result := .prop) signature
      (fun selected => predicateFunction _ (shifted selected)) candidate occurrence
      candidateArguments (substituteArguments images _ arguments) payloads
    have predicates : ProofSyntax Const localAssumptions
        (.eq (applyArguments _ (shifted candidate) candidateArguments)
          (applyArguments _ (shifted occurrence) (substituteArguments images _ arguments))) :=
      ProofSyntax.castIndices rfl
        (congrArg₂ Term.eq (apply_predicateFunction _ _ candidateArguments)
          (apply_predicateFunction _ _ (substituteArguments images _ arguments))) programs
    apply ProofSyntax.castIndices rfl ?_ (.impE (.eqPropEL predicates) (.andEL parts))
    exact (applyArguments_subst images _ (conditions occurrence) arguments).symm
  · apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp 0)
    simp [formulas, List.get_eq_getElem, predicate, candidate, restrictedGuard]

theorem readOnEncoded_free (signature : List (List (Ty Base))) (conditions : Conditions Const Γ signature)
    (occurrence : Fin signature.length) (arguments : Arguments Const Γ (signature.get occurrence))
    (present : ProofSyntax Const assumptions (guard signature conditions (encode signature occurrence arguments)))
    (free : present.FunctionExtensionalityFree) :
    (readOnEncoded signature conditions occurrence arguments present).FunctionExtensionalityFree := by
  unfold readOnEncoded
  apply any_elim_free
  · exact free
  · intro selected
    apply FieldCase.eliminate_free
    · intro Ξ images candidateArguments
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      refine ⟨?_, ?_⟩
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply program_equal_of_payload_free
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply restrictedPredicate_parts_free
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial
      · apply restrictedPredicate_parts_free
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial

#print axioms restrictedPredicate_parts_free
#print axioms readOnEncoded
#print axioms readOnEncoded_free

end Mettapedia.Logic.HOL.ConstructorDataPredicates
