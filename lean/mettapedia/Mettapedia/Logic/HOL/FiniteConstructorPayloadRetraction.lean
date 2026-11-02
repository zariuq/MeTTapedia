import Mettapedia.Logic.HOL.FiniteConstructorPayloadMapComputations
import Mettapedia.Logic.HOL.ConstructorDataPredicates
import Mettapedia.Logic.HOL.FiniteConstructorCaseProofs
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs

/-!
# Guarded recovery through actual finite payload programs

Recovery of every original row field yields recovery of an encoded payload.
The original constructor-data guard then exposes its actual row and fields,
extending that result to every admitted payload. Hypothesis occurrences and
typed substitution are retained. There is no inverse premise for the entire
payload function space or a whole-payload inverse among the inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {source target : List (List (Ty Base))} {Δ : List (Formula Const Γ)}

namespace InventoryMaps

theorem occurrence_roundtrip (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source) (index : Fin source.length) :
    raise.occurrence (lower.occurrence index) = index := by
  apply Fin.ext
  rfl

def returnedArguments (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source) (index : Fin source.length)
    (arguments : Arguments Const Γ (source.get index)) : Arguments Const Γ (source.get index) :=
  (congrArg (fun occurrence => Arguments Const Γ (source.get occurrence))
    (occurrence_roundtrip lower raise index)) ▸
      (raise.row (lower.occurrence index)).apply ((lower.row index).apply arguments)

private theorem encode_transport {first second : Fin source.length} (same : first = second)
    (arguments : Arguments Const Γ (source.get first)) :
    encode source first arguments = encode source second
      ((congrArg (fun occurrence => Arguments Const Γ (source.get occurrence)) same) ▸ arguments) := by
  cases same
  rfl

def encodedRoundtrip (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source) (index : Fin source.length)
    (arguments : Arguments Const Γ (source.get index))
    (fields : ∀ {type : Ty Base} (field : Var (source.get index) type),
      ProofSyntax Const Δ (.eq (argumentAt field (returnedArguments lower raise index arguments))
        (argumentAt field arguments))) :
    ProofSyntax Const Δ (.eq (raise.mapPayload (lower.mapPayload (encode source index arguments)))
      (encode source index arguments)) := by
  have forward := lower.mapPayload_encode (Δ := Δ) index arguments
  have backward := raise.mapPayload_encode (Δ := Δ) (lower.occurrence index) ((lower.row index).apply arguments)
  have transported : ProofSyntax Const Δ (.eq
      (raise.mapPayload (encode target (lower.occurrence index) ((lower.row index).apply arguments)))
      (encode source index (returnedArguments lower raise index arguments))) :=
    .castIndices rfl (congrArg (Term.eq _) (encode_transport (occurrence_roundtrip lower raise index) _)) backward
  exact .eqTrans (raise.mapPayload_congr _ _ forward)
    (.eqTrans transported (encode_congr source index _ arguments fields))

/-- Field recovery is supplied at each actual source row and under that row's
original condition, with explicit transport of the original hypotheses. -/
def RowRecovery (premises : List (Formula Const Γ))
    (lower : InventoryMaps Const Γ source target) (raise : InventoryMaps Const Γ target source)
    (conditions : ConstructorDataPredicates.Conditions Const Γ source) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (_transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (index : Fin source.length) (arguments : Arguments Const Ξ (source.get index)),
    ProofSyntax Const assumptions (applyArguments (source.get index) (HOL.subst images (conditions index)) arguments) →
    ∀ {type : Ty Base} (field : Var (source.get index) type),
      ProofSyntax Const assumptions (.eq
        (argumentAt field (returnedArguments (lower.subst images) (raise.subst images) index arguments))
        (argumentAt field arguments))

def RowRecovery.Free {premises : List (Formula Const Γ)}
    {lower : InventoryMaps Const Γ source target} {raise : InventoryMaps Const Γ target source}
    {conditions : ConstructorDataPredicates.Conditions Const Γ source}
    (recover : RowRecovery premises lower raise conditions) : Prop :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (index : Fin source.length) (arguments : Arguments Const Ξ (source.get index))
    (allowed : ProofSyntax Const assumptions
      (applyArguments (source.get index) (HOL.subst images (conditions index)) arguments)),
    allowed.FunctionExtensionalityFree →
    ∀ {type : Ty Base} (field : Var (source.get index) type),
      (recover images transport index arguments allowed field).FunctionExtensionalityFree

theorem encodedRoundtrip_free (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source) (index : Fin source.length)
    (arguments : Arguments Const Γ (source.get index))
    (fields : ∀ {type : Ty Base} (field : Var (source.get index) type),
      ProofSyntax Const Δ (.eq (argumentAt field (returnedArguments lower raise index arguments))
        (argumentAt field arguments)))
    (free : ∀ {type : Ty Base} (field : Var (source.get index) type), (fields field).FunctionExtensionalityFree) :
    (encodedRoundtrip lower raise index arguments fields).FunctionExtensionalityFree := by
  unfold encodedRoundtrip
  refine ⟨?_,?_,?_⟩
  · apply mapPayload_congr_free
    exact mapPayload_encode_free _ _ _
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      (mapPayload_encode_free _ _ _)
  · exact encode_congr_free _ _ _ _ _ free

def guardedRoundtrip (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source)
    (conditions : ConstructorDataPredicates.Conditions Const Γ source)
    (recover : RowRecovery Δ lower raise conditions) (payload : Term Const Γ (payloadType source))
    (present : ProofSyntax Const Δ (ConstructorDataPredicates.guard source conditions payload)) :
    ProofSyntax Const Δ (.eq (raise.mapPayload (lower.mapPayload payload)) payload) := by
  let wanted := Term.eq (raise.mapPayload (lower.mapPayload payload)) payload
  let formulas := List.ofFn (fun index => restrictedGuard source index (conditions index) payload)
  apply any_elim formulas wanted present
  intro selected
  let index : Fin source.length := ⟨selected.val,by simpa only [formulas,List.length_ofFn] using selected.isLt⟩
  let predicate := restrictedPredicate source index (conditions index) payload
  apply ProofSyntax.impI
  apply FieldCase.eliminate (source.get index) predicate wanted
  · intro Ξ images arguments
    let localHypotheses := applyArguments _ (HOL.subst images predicate) arguments ::
      ((formulas.get selected) :: Δ).map (HOL.subst images)
    have current : ProofSyntax Const localHypotheses (applyArguments _
        (restrictedPredicate source index (HOL.subst images (conditions index)) (HOL.subst images payload)) arguments) := by
      apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp 0)
      change applyArguments _
        (HOL.subst images (restrictedPredicate source index (conditions index) payload)) arguments = _
      rw [restrictedPredicate_subst]
    have parts := ProofSyntax.impE (.eqPropEL (restrictedPredicate_beta source index
      (HOL.subst images (conditions index)) (HOL.subst images payload) arguments)) current
    let transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) localHypotheses :=
      ⟨fun occurrence => occurrence.succ.succ,fun _ => rfl⟩
    have recovered := encodedRoundtrip (lower.subst images) (raise.subst images) index arguments
      (recover images transport index arguments (.andEL parts))
    have same : ProofSyntax Const localHypotheses (.eq (HOL.subst images payload) (encode source index arguments)) :=
      .andER parts
    have result := ProofSyntax.eqTrans
      ((raise.subst images).mapPayload_congr _ _ ((lower.subst images).mapPayload_congr _ _ same))
      (.eqTrans recovered (.eqSymm same))
    apply ProofSyntax.castIndices rfl ?_ result
    simp only [wanted,HOL.subst,mapPayload_subst]
  · apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp 0)
    simp [formulas,List.get_eq_getElem,predicate,index,restrictedGuard]

theorem guardedRoundtrip_free (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source)
    (conditions : ConstructorDataPredicates.Conditions Const Γ source)
    (recover : RowRecovery Δ lower raise conditions) (payload : Term Const Γ (payloadType source))
    (present : ProofSyntax Const Δ (ConstructorDataPredicates.guard source conditions payload))
    (recoverFree : recover.Free) (presentFree : present.FunctionExtensionalityFree) :
    (guardedRoundtrip lower raise conditions recover payload present).FunctionExtensionalityFree := by
  unfold guardedRoundtrip
  apply any_elim_free
  · exact presentFree
  · intro selected
    apply FieldCase.eliminate_free
    · intro Ξ images arguments
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      refine ⟨?_,?_,?_⟩
      · apply mapPayload_congr_free
        apply mapPayload_congr_free
        exact ⟨restrictedPredicate_beta_free _ _ _ _ _,
          (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩
      · apply encodedRoundtrip_free
        apply recoverFree
        exact ⟨restrictedPredicate_beta_free _ _ _ _ _,
          (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩
      · exact ⟨restrictedPredicate_beta_free _ _ _ _ _,
          (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩
    · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

/-- Equality after representation reflects to the original payloads only on
the original constructor-data guard. The raising program and its primitive
field recovery provide the reflection proof. -/
def guardedInjective (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source)
    (conditions : ConstructorDataPredicates.Conditions Const Γ source)
    (recover : RowRecovery Δ lower raise conditions)
    (first second : Term Const Γ (payloadType source))
    (firstPresent : ProofSyntax Const Δ (ConstructorDataPredicates.guard source conditions first))
    (secondPresent : ProofSyntax Const Δ (ConstructorDataPredicates.guard source conditions second))
    (same : ProofSyntax Const Δ (.eq (lower.mapPayload first) (lower.mapPayload second))) :
    ProofSyntax Const Δ (.eq first second) :=
  .eqTrans (.eqSymm (guardedRoundtrip lower raise conditions recover first firstPresent))
    (.eqTrans (raise.mapPayload_congr _ _ same)
      (guardedRoundtrip lower raise conditions recover second secondPresent))

theorem guardedInjective_free (lower : InventoryMaps Const Γ source target)
    (raise : InventoryMaps Const Γ target source)
    (conditions : ConstructorDataPredicates.Conditions Const Γ source)
    (recover : RowRecovery Δ lower raise conditions)
    (first second : Term Const Γ (payloadType source))
    (firstPresent : ProofSyntax Const Δ (ConstructorDataPredicates.guard source conditions first))
    (secondPresent : ProofSyntax Const Δ (ConstructorDataPredicates.guard source conditions second))
    (same : ProofSyntax Const Δ (.eq (lower.mapPayload first) (lower.mapPayload second)))
    (recoverFree : recover.Free)
    (firstFree : firstPresent.FunctionExtensionalityFree)
    (secondFree : secondPresent.FunctionExtensionalityFree)
    (sameFree : same.FunctionExtensionalityFree) :
    (guardedInjective lower raise conditions recover first second firstPresent secondPresent same).FunctionExtensionalityFree := by
  exact ⟨guardedRoundtrip_free lower raise conditions recover first firstPresent recoverFree firstFree,
    mapPayload_congr_free raise _ _ same sameFree,
    guardedRoundtrip_free lower raise conditions recover second secondPresent recoverFree secondFree⟩

#print axioms encodedRoundtrip
#print axioms guardedRoundtrip
#print axioms encodedRoundtrip_free
#print axioms guardedRoundtrip_free
#print axioms guardedInjective
#print axioms guardedInjective_free

end InventoryMaps
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
