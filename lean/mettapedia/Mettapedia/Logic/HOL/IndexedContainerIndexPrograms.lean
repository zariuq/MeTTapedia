import Mettapedia.Logic.HOL.IndexedContainerDirectPositions

/-!
# Exact source indices of compiled constructor segments

The original description evaluates each recursive or registered child's index
in its actual data environment. Data fields extend that environment; shape
fields do not. Retained beta proofs connect those indices to the curried
programs stored by the existing segment compiler.
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

theorem bindPlan_subst {domain countType indexType : Ty Base} {fields : List (Ty Base)}
    (images : Subst Const Γ Ξ) (plan : FieldPlan Const (domain :: Γ) fields countType indexType) :
    substitute images (bindPlan plan) = bindPlan (substitute (Subst.lift images) plan) := by
  simp only [substitute, bindPlan, List.map_map, Function.comp_def, subst]

theorem compile_subst {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (images : Subst Const Γ Ξ) :
    substitute images (reading.compile code rho) = reading.compile code (Subst.comp images rho) := by
  induction code generalizing Γ Ξ with
  | result _ => rfl
  | data _ _ previous =>
      simp only [compile]
      rw [bindPlan_subst, previous, Subst.lift_comp_eq]
  | recursive _ _ previous =>
      simp only [compile, substitute_cons, ignoreFields_subst, subst_weakenCtx, subst_comp, previous]
  | nested name entry registered output childIndex rest previous =>
      simp only [compile]
      rw [bindPlan_subst]
      simp only [substitute_cons, ignoreFields_subst, subst, subst_weaken, Subst.lift, subst_comp]
      congr 1
      rw [previous]
      congr 1
      apply congrArg (reading.compile rest)
      funext type index
      exact subst_weaken images (rho index)

def sourceIndexAt : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {ambient : Ctx Base} → Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) ambient →
    Arguments Const ambient (reading.fields code) → Nat → Option (Term Const ambient reading.indices.index)
  | _, .result _, _, _, _, _ => none
  | _, .data _ rest, _, rho, arguments, ordinal =>
      sourceIndexAt rest (Subst.cons arguments.1 rho) arguments.2 ordinal
  | _, .recursive expression _, _, rho, _, 0 => some (subst rho (reading.indices.term expression))
  | _, .recursive _ rest, _, rho, arguments, ordinal + 1 => sourceIndexAt rest rho arguments ordinal
  | _, .nested _ _ _ _ childIndex _, _, rho, _, 0 => some (subst rho (reading.indices.term childIndex))
  | _, .nested _ _ _ _ _ rest, _, rho, arguments, ordinal + 1 => sourceIndexAt rest rho arguments.2 ordinal

theorem sourceIndexAt_isSome {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (inside : ordinal < (directFlags code).length) : (sourceIndexAt code rho arguments ordinal).isSome := by
  induction code generalizing Γ ordinal with
  | result _ => simp only [directFlags, List.length_nil] at inside; omega
  | data _ _ previous => exact previous (Subst.cons arguments.1 rho) arguments.2 ordinal inside
  | recursive _ _ previous =>
      cases ordinal with
      | zero => rfl
      | succ ordinal => exact previous rho arguments ordinal (Nat.lt_of_succ_lt_succ inside)
  | nested _ _ _ _ _ _ previous =>
      cases ordinal with
      | zero => rfl
      | succ ordinal => exact previous rho arguments.2 ordinal (Nat.lt_of_succ_lt_succ inside)

def sourceIndex {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (inside : ordinal < (directFlags code).length) : Term Const Γ reading.indices.index :=
  (sourceIndexAt code rho arguments ordinal).get (sourceIndexAt_isSome code rho arguments ordinal inside)

theorem sourceIndexAt_sourceIndex {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (inside : ordinal < (directFlags code).length) :
    sourceIndexAt code rho arguments ordinal = some (sourceIndex code rho arguments ordinal inside) :=
  (Option.some_get _).symm

private theorem instantiate_compile_data {context : List I.SortCode} (sort : I.SortCode)
    (rest : Code I registry parameters (sort :: context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (argument : Term Const Γ (reading.indices.sort sort)) :
    substitute (Subst.single argument) (reading.compile rest (Subst.lift rho)) =
      reading.compile rest (Subst.cons argument rho) := by
  rw [compile_subst, Subst.single_lift_eq_cons]

private theorem instantiate_compile_shape {context : List I.SortCode} (rest : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    {domain : Ty Base} (argument : Term Const Γ domain) :
    substitute (Subst.single argument) (reading.compile rest (fun index => weaken (rho index))) =
      reading.compile rest rho := by
  rw [compile_subst]
  apply congrArg (reading.compile rest)
  funext type index
  exact instantiate_weaken argument (rho index)

def segmentIndexEvidence {hypotheses : List (Formula Const Γ)} :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) →
    (arguments : Arguments Const Γ (reading.fields code)) → (ordinal : Nat) →
    (segment : Term Const Γ (FunctionType (reading.fields code) reading.number) ×
      Term Const Γ (FunctionType (reading.fields code) reading.indices.index)) →
    (reading.compile code rho)[ordinal]? = some segment →
    (target : Term Const Γ reading.indices.index) →
    sourceIndexAt code rho arguments ordinal = some target →
    {proof : ProofSyntax Const hypotheses
      (.eq (applyFields (reading.fields code) segment.2 arguments) target) // proof.FunctionExtensionalityFree}
  | _, .result _, _, _, _, _, found, _, _ => by
      simp only [compile, List.getElem?_nil] at found
      contradiction
  | _, .data sort rest, rho, arguments, ordinal, _, found, target, source => by
      cases selected : (reading.compile rest (Subst.lift rho))[ordinal]? with
      | none => simp only [compile, bindPlan, List.getElem?_map, selected, Option.map_none] at found; contradiction
      | some inner =>
          have value : (reading.compile (.data sort rest) rho)[ordinal]? = some (.lam inner.1, .lam inner.2) := by
            simp only [compile, bindPlan, List.getElem?_map, selected, Option.map_some]
          cases Option.some.inj (found.symm.trans value)
          have remaining : (reading.compile rest (Subst.cons arguments.1 rho))[ordinal]? =
              some (instantiate arguments.1 inner.1, instantiate arguments.1 inner.2) := by
            rw [← instantiate_compile_data sort rest rho arguments.1]
            simp only [substitute, List.getElem?_map, selected, Option.map_some, instantiate]
          let tail := segmentIndexEvidence (hypotheses := hypotheses) rest
            (Subst.cons arguments.1 rho) arguments.2 ordinal _ remaining target source
          exact ⟨.eqTrans (applyFields_beta (reading.fields rest) inner.2 arguments.1 arguments.2) tail.val,
            ⟨applyFields_beta_free _ _ _ _, tail.property⟩⟩
  | _, .recursive expression rest, rho, arguments, ordinal, segment, found, target, source => by
      cases ordinal with
      | zero =>
          cases Option.some.inj found.symm
          cases Option.some.inj source
          exact ⟨ignoreFields_beta (reading.fields rest) (subst rho (reading.indices.term expression)) arguments,
            ignoreFields_beta_free _ _ _⟩
      | succ ordinal => exact segmentIndexEvidence rest rho arguments ordinal segment found target source
  | _, .nested name entry registered output childIndex rest, rho, arguments, ordinal, _, found, target, source => by
      cases ordinal with
      | zero =>
          cases Option.some.inj found.symm
          cases Option.some.inj source
          exact ⟨ignoreFields_beta (reading.fields (.nested name entry registered output childIndex rest))
            (subst rho (reading.indices.term childIndex)) arguments, ignoreFields_beta_free _ _ _⟩
      | succ ordinal =>
          cases selected : (reading.compile rest (fun entry => weaken (rho entry)))[ordinal]? with
          | none =>
              simp only [compile, bindPlan, List.getElem?_map, List.getElem?_cons_succ] at found
              rw [selected] at found
              contradiction
          | some inner =>
              have value : (reading.compile (.nested name entry registered output childIndex rest) rho)[ordinal + 1]? =
                  some (.lam inner.1, .lam inner.2) := by
                simp only [compile, bindPlan, List.getElem?_map, List.getElem?_cons_succ, selected, Option.map_some]
              cases Option.some.inj (found.symm.trans value)
              have remaining : (reading.compile rest rho)[ordinal]? =
                  some (instantiate arguments.1 inner.1, instantiate arguments.1 inner.2) := by
                rw [← instantiate_compile_shape rest rho arguments.1]
                simp only [substitute, List.getElem?_map, selected, Option.map_some, instantiate]
              let tail := segmentIndexEvidence (hypotheses := hypotheses) rest rho arguments.2 ordinal _ remaining target source
              exact ⟨.eqTrans (applyFields_beta (reading.fields rest) inner.2 arguments.1 arguments.2) tail.val,
                ⟨applyFields_beta_free _ _ _ _, tail.property⟩⟩

def directSourceIndex {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true) : Term Const Γ reading.indices.index :=
  sourceIndex code rho arguments ordinal (List.getElem?_eq_some_iff.mp direct).1

def directIndexProof {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true) {hypotheses : List (Formula Const Γ)} :
    ProofSyntax Const hypotheses (.eq (directSegment code rho arguments ordinal direct).2
      (directSourceIndex code rho arguments ordinal direct)) :=
  (segmentIndexEvidence code rho arguments ordinal _ (directProgram_found code rho ordinal direct)
    _ (sourceIndexAt_sourceIndex code rho arguments ordinal _)).val

theorem directIndexProof_free {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (ordinal : Nat)
    (direct : (directFlags code)[ordinal]? = some true) {hypotheses : List (Formula Const Γ)} :
    (directIndexProof code rho arguments ordinal direct (hypotheses := hypotheses)).FunctionExtensionalityFree :=
  (segmentIndexEvidence code rho arguments ordinal _ (directProgram_found code rho ordinal direct)
    _ (sourceIndexAt_sourceIndex code rho arguments ordinal _)).property

def directSourceSelectedExists {context : List I.SortCode} (code : Code I registry parameters context)
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
      (directSourceIndex code rho arguments ordinal direct)) := by
  let segment := directSegment code rho arguments ordinal direct
  let predicate := Term.app (weakenCtx Γ (SuccessorOrder.less successor)) (weakenCtx Γ zero)
  let positive : ProofSyntax Const hypotheses (.app predicate segment.1) :=
    .impE (.eqPropER (.eqAppArg predicate (directCountProof code rho arguments ordinal direct))) onePositive
  have atCount : ProofSyntax Const hypotheses (.app predicate (subst Subst.id segment.1)) :=
    ProofSyntax.castIndices rfl (congrArg (Term.app predicate) (subst_id segment.1).symm) positive
  have atIndex : ProofSyntax Const hypotheses
      (.eq (directSourceIndex code rho arguments ordinal direct) (subst Subst.id segment.2)) :=
    ProofSyntax.castIndices rfl
      (congrArg (Term.eq (directSourceIndex code rho arguments ordinal direct)) (subst_id segment.2).symm)
      (.eqSymm (directIndexProof code rho arguments ordinal direct))
  exact selectedExists_at zero successor _ ordinal segment (directSegment_found code rho arguments ordinal direct)
    Subst.id _ principle atCount atIndex

theorem directSourceSelectedExists_free {context : List I.SortCode} (code : Code I registry parameters context)
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
    (directSourceSelectedExists code rho arguments ordinal direct zero successor principle onePositive).FunctionExtensionalityFree := by
  unfold directSourceSelectedExists
  apply selectedExists_at_free
  · exact principleFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact ⟨directCountProof_free code rho arguments ordinal direct, oneFree⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact directIndexProof_free code rho arguments ordinal direct

#print axioms compile_subst
#print axioms segmentIndexEvidence
#print axioms directIndexProof_free
#print axioms directSourceSelectedExists_free

end Mettapedia.Logic.HOL.IndexedContainerPositionTerms.Reading
