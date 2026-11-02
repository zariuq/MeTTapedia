import Mettapedia.Logic.HOL.IndexedContainerFieldProofs
import Mettapedia.Logic.HOL.OrderedPositionSelection

/-!
# Direct recursive segment occurrences in original constructor descriptions

The flags follow the actual compiled segment order. Data binders preserve
ordinals, direct children contribute a marked unit segment, and registered
containers contribute an unmarked segment before their remaining fields.
Repeated child indices therefore retain distinct source occurrences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms.Reading

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open CurriedPredicates FiniteConstructorEncoding OrderedPositionPrograms
universe u v w
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
    {Const : Ty Base → Type w} {parameters : Nat} {reading : Reading I registry Const}
    {Γ Ξ : Ctx Base}

def directFlags : {context : List I.SortCode} → Code I registry parameters context → List Bool
  | _, .result _ => []
  | _, .data _ rest => directFlags rest
  | _, .recursive _ rest => true :: directFlags rest
  | _, .nested _ _ _ _ _ rest => false :: directFlags rest

theorem compile_length {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) :
    (reading.compile code rho).length = (directFlags code).length := by
  induction code generalizing Γ with
  | result _ => rfl
  | data _ _ previous => simpa only [compile, bindPlan, List.length_map, directFlags] using previous (Subst.lift rho)
  | recursive _ _ previous => simpa only [compile, directFlags, List.length_cons] using congrArg Nat.succ (previous rho)
  | nested _ _ _ _ _ _ previous =>
      simpa only [compile, bindPlan, List.length_map, directFlags, List.length_cons] using
        congrArg Nat.succ (previous (fun entry => weaken (rho entry)))

theorem ignoreFields_subst {result : Ty Base} (fields : List (Ty Base))
    (images : Subst Const Γ Ξ) (term : Term Const Γ result) :
    subst images (ignoreFields fields term) = ignoreFields fields (subst images term) := by
  induction fields generalizing Γ Ξ with
  | nil => rfl
  | cons first rest previous =>
      simp only [ignoreFields, subst, previous, subst_weaken]

def ignoreFields_beta {result : Ty Base} {hypotheses : List (Formula Const Γ)} :
    (fields : List (Ty Base)) → (term : Term Const Γ result) → (arguments : Arguments Const Γ fields) →
    ProofSyntax Const hypotheses (.eq (applyFields fields (ignoreFields fields term) arguments) term)
  | [], term, _ => .eqRefl term
  | first :: rest, term, arguments => by
      have body : instantiate arguments.1 (ignoreFields rest (weaken term)) = ignoreFields rest term := by
        rw [instantiate, ignoreFields_subst, PredicateFixedPoint.subst_single_weaken]
      have beta := applyFields_beta (assumptions := hypotheses) rest (ignoreFields rest (weaken term)) arguments.1 arguments.2
      have aligned := ProofSyntax.castIndices rfl
        (congrArg (Term.eq (applyFields (first :: rest) (ignoreFields (first :: rest) term) arguments))
          (congrArg (fun function => applyFields rest function arguments.2) body)) beta
      exact .eqTrans aligned (ignoreFields_beta rest term arguments.2)

theorem ignoreFields_beta_free {result : Ty Base} {hypotheses : List (Formula Const Γ)}
    (fields : List (Ty Base)) (term : Term Const Γ result) (arguments : Arguments Const Γ fields) :
    (ignoreFields_beta (hypotheses := hypotheses) fields term arguments).FunctionExtensionalityFree := by
  induction fields with
  | nil => trivial
  | cons _ _ previous =>
      constructor
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact applyFields_beta_free _ _ _ _
      · exact previous arguments.2

private theorem bindPlan_get {domain countType indexType : Ty Base} {fields : List (Ty Base)}
    (plan : FieldPlan Const (domain :: Γ) fields countType indexType) (ordinal : Nat)
    (segment : Term Const (domain :: Γ) (FunctionType fields countType) ×
      Term Const (domain :: Γ) (FunctionType fields indexType))
    (found : plan[ordinal]? = some segment) :
    (bindPlan plan)[ordinal]? = some (.lam segment.1, .lam segment.2) := by
  simp only [bindPlan, List.getElem?_map, found, Option.map_some]

theorem direct_count {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (ordinal : Nat) (segment : Term Const Γ (FunctionType (reading.fields code) reading.number) ×
      Term Const Γ (FunctionType (reading.fields code) reading.indices.index))
    (found : (reading.compile code rho)[ordinal]? = some segment)
    (direct : (directFlags code)[ordinal]? = some true) :
    segment.1 = ignoreFields (reading.fields code) (weakenCtx Γ reading.one) := by
  induction code generalizing Γ ordinal with
  | result _ => simp only [directFlags, List.getElem?_nil] at direct; contradiction
  | data sort rest previous =>
      cases selected : (reading.compile rest (Subst.lift rho))[ordinal]? with
      | none => simp only [compile, bindPlan, List.getElem?_map, selected, Option.map_none] at found; contradiction
      | some inner =>
          have value := bindPlan_get (reading.compile rest (Subst.lift rho)) ordinal inner selected
          have same : segment = (.lam inner.1, .lam inner.2) := Option.some.inj (found.symm.trans value)
          rw [same, previous (Subst.lift rho) ordinal inner selected direct]
          simp only [fields, ignoreFields, weakenCtx_cons]
  | recursive expression rest previous =>
      cases ordinal with
      | zero => cases Option.some.inj found.symm; rfl
      | succ ordinal => exact previous rho ordinal segment found direct
  | nested name entry registered output childIndex rest previous =>
      cases ordinal with
      | zero => simp only [directFlags, List.getElem?_cons_zero] at direct; contradiction
      | succ ordinal =>
          cases selected : (reading.compile rest (fun entry => weaken (rho entry)))[ordinal]? with
          | none =>
              simp only [compile, bindPlan, List.getElem?_map, List.getElem?_cons_succ] at found
              rw [selected] at found
              contradiction
          | some inner =>
              have value := bindPlan_get (reading.compile rest (fun entry => weaken (rho entry))) ordinal inner selected
              have same : segment = (.lam inner.1, .lam inner.2) := Option.some.inj (found.symm.trans value)
              rw [same, previous (fun entry => weaken (rho entry)) ordinal inner selected direct]
              simp only [fields, ignoreFields, weakenCtx_cons]

theorem direct_bound {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (ordinal : Nat) (direct : (directFlags code)[ordinal]? = some true) :
    ordinal < (reading.compile code rho).length := by
  rw [compile_length code rho]
  exact (List.getElem?_eq_some_iff.mp direct).1

def directProgram {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (ordinal : Nat) (direct : (directFlags code)[ordinal]? = some true) :
    Term Const Γ (FunctionType (reading.fields code) reading.number) ×
      Term Const Γ (FunctionType (reading.fields code) reading.indices.index) :=
  (reading.compile code rho).get ⟨ordinal, direct_bound code rho ordinal direct⟩

theorem directProgram_found {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (ordinal : Nat) (direct : (directFlags code)[ordinal]? = some true) :
    (reading.compile code rho)[ordinal]? = some (directProgram code rho ordinal direct) :=
  List.getElem?_eq_getElem (direct_bound code rho ordinal direct)

theorem directProgram_count {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (ordinal : Nat) (direct : (directFlags code)[ordinal]? = some true) :
    (directProgram code rho ordinal direct).1 = ignoreFields (reading.fields code) (weakenCtx Γ reading.one) :=
  direct_count code rho ordinal _ (directProgram_found code rho ordinal direct) direct

def directSegment {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true) : Segment Const Γ reading.number reading.indices.index :=
  let program := directProgram code rho ordinal direct
  (applyFields (reading.fields code) program.1 arguments, applyFields (reading.fields code) program.2 arguments)

theorem directSegment_found {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true) :
    (fieldTerms (reading.fields code) (reading.compile code rho) Subst.id arguments)[ordinal]? =
      some (directSegment code rho arguments ordinal direct) := by
  simp only [fieldTerms, List.getElem?_map, directProgram_found code rho ordinal direct,
    Option.map_some, subst_id, directSegment]

def directCountProof {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true) {hypotheses : List (Formula Const Γ)} :
    ProofSyntax Const hypotheses (.eq (directSegment code rho arguments ordinal direct).1 (weakenCtx Γ reading.one)) :=
  ProofSyntax.castIndices rfl
    (congrArg (fun function => Term.eq (applyFields (reading.fields code) function arguments) (weakenCtx Γ reading.one))
      (directProgram_count code rho ordinal direct).symm)
    (ignoreFields_beta (reading.fields code) (weakenCtx Γ reading.one) arguments)

theorem directCountProof_free {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true) {hypotheses : List (Formula Const Γ)} :
    (directCountProof code rho arguments ordinal direct (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  unfold directCountProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ignoreFields_beta_free _ _ _

def directSelectedExists {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true)
    (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
    {hypotheses : List (Formula Const Γ)}
    (principle : ProofSyntax Const hypotheses
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (onePositive : ProofSyntax Const hypotheses
      (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) (weakenCtx Γ zero)) (weakenCtx Γ reading.one))) :
    ProofSyntax Const hypotheses (selectedExists zero successor ordinal
      (fieldTerms (reading.fields code) (reading.compile code rho) Subst.id arguments) Subst.id
      (directSegment code rho arguments ordinal direct).2) := by
  let segment := directSegment code rho arguments ordinal direct
  let predicate := Term.app (weakenCtx Γ (SuccessorOrder.less successor)) (weakenCtx Γ zero)
  let positive : ProofSyntax Const hypotheses (.app predicate segment.1) :=
    .impE (.eqPropER (.eqAppArg predicate (directCountProof code rho arguments ordinal direct))) onePositive
  have atCount : ProofSyntax Const hypotheses (.app predicate (subst Subst.id segment.1)) :=
    ProofSyntax.castIndices rfl (congrArg (Term.app predicate) (subst_id segment.1).symm) positive
  have atIndex : ProofSyntax Const hypotheses (.eq segment.2 (subst Subst.id segment.2)) :=
    ProofSyntax.castIndices rfl (congrArg (Term.eq segment.2) (subst_id segment.2).symm) (.eqRefl segment.2)
  exact selectedExists_at zero successor _ ordinal segment (directSegment_found code rho arguments ordinal direct)
    Subst.id segment.2 principle atCount atIndex

theorem directSelectedExists_free {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true)
    (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
    {hypotheses : List (Formula Const Γ)}
    (principle : ProofSyntax Const hypotheses
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (onePositive : ProofSyntax Const hypotheses
      (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) (weakenCtx Γ zero)) (weakenCtx Γ reading.one)))
    (principleFree : principle.FunctionExtensionalityFree) (oneFree : onePositive.FunctionExtensionalityFree) :
    (directSelectedExists code rho arguments ordinal direct zero successor principle onePositive).FunctionExtensionalityFree := by
  unfold directSelectedExists
  apply selectedExists_at_free
  · exact principleFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact ⟨directCountProof_free code rho arguments ordinal direct, oneFree⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

#print axioms compile_length
#print axioms direct_count
#print axioms ignoreFields_beta_free
#print axioms directCountProof_free
#print axioms directSelectedExists_free

end Mettapedia.Logic.HOL.IndexedContainerPositionTerms.Reading
