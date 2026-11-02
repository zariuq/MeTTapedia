import Mettapedia.Logic.HOL.OrderedPositionProofs
import Mettapedia.Logic.HOL.ConstructorIndexSelection

/-!
# Original-field index comparisons for generated position tables

The original segment equations produce the guarded comparison required by
child-witness selection. Field order, repeated segment occurrences and the
fresh index binder are retained. This covers uniformly indexed plans without
assuming arithmetic or semantic truth as a proof certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number)
    (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {assumptions : List (Formula Const Γ)}

def guardedUniformIndexComparison (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (aligned : ∀ position : Fin (plans occurrence).length,
      ProofSyntax Const (applyArguments _ (constructors.allowed occurrence) arguments :: assumptions)
        (.eq (applyFields _ ((plans occurrence).get position).2 arguments) requested)) :
    ProofSyntax Const assumptions
      ((ofSegments constructors zero successor plans).indexComparison occurrence arguments slot requested) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let images : Subst Const Γ (constructors.index :: Γ) := edgeIndexScope (constructors := constructors)
  let data := substituteArguments images _ arguments
  let antecedent := Term.and (applyArguments _ ((constructors.subst images).allowed occurrence) data)
    (applyArguments _ (.app (.app (((ofSegments constructors zero successor plans).subst images).graph occurrence)
      (HOL.subst images slot)) (.var .vz)) data)
  let hypotheses := antecedent :: weakenHyps assumptions
  let currentPlan := substitute images (plans occurrence)
  have relation : ProofSyntax Const hypotheses
      (applyArguments _ (.app (.app (fieldGraph zero successor _ currentPlan)
        (HOL.subst images slot)) (.var .vz)) data) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.andER (ProofSyntax.hyp (Δ := hypotheses) 0))
    simp only [ofSegments, PositionPrograms.subst, fieldGraph_substitute, currentPlan]
    rfl
  have localAllowed : ProofSyntax Const hypotheses
      (HOL.rename Rename.weaken (applyArguments _ (constructors.allowed occurrence) arguments)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.andEL (ProofSyntax.hyp (Δ := hypotheses) 0))
    change applyArguments _ (HOL.subst images (constructors.allowed occurrence)) data = _
    exact (applyArguments_subst images _ (constructors.allowed occurrence) arguments).symm.trans
      (subst_ofRename Rename.weaken _)
  apply fieldGraph_result zero successor _ currentPlan (HOL.subst images slot) (.var .vz) (HOL.subst images requested) data
  · intro position
    let sourcePosition : Fin (plans occurrence).length :=
      ⟨position.val, by simpa only [currentPlan, substitute, List.length_map] using position.isLt⟩
    apply ProofSyntax.castIndices rfl ?_
      (.impE ((ProofSyntax.rename Rename.weaken (ProofSyntax.impI (aligned sourcePosition))).prepend antecedent)
        localAllowed)
    simp only [currentPlan, substitute, List.get_eq_getElem, List.getElem_map, sourcePosition]
    simp only [data]
    apply (subst_ofRename Rename.weaken
      (.eq (applyFields _ ((plans occurrence).get sourcePosition).2 arguments) requested)).symm.trans
    simp only [HOL.subst, applyFields_subst, sourcePosition, List.get_eq_getElem]
    rfl
  · exact relation

theorem guardedUniformIndexComparison_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (aligned : ∀ position : Fin (plans occurrence).length,
      ProofSyntax Const (applyArguments _ (constructors.allowed occurrence) arguments :: assumptions)
        (.eq (applyFields _ ((plans occurrence).get position).2 arguments) requested))
    (alignedFree : ∀ position, (aligned position).FunctionExtensionalityFree) :
    (guardedUniformIndexComparison constructors zero successor plans occurrence arguments slot requested aligned).FunctionExtensionalityFree := by
  unfold guardedUniformIndexComparison
  apply fieldGraph_result_free
  · intro position
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr (alignedFree _)
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

#print axioms guardedUniformIndexComparison_free

def uniformIndexComparison (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (aligned : ∀ position : Fin (plans occurrence).length,
      ProofSyntax Const assumptions (.eq (applyFields _ ((plans occurrence).get position).2 arguments) requested)) :
    ProofSyntax Const assumptions
      ((ofSegments constructors zero successor plans).indexComparison occurrence arguments slot requested) :=
  guardedUniformIndexComparison constructors zero successor plans occurrence arguments slot requested
    (fun position => (aligned position).prepend (applyArguments _ (constructors.allowed occurrence) arguments))

theorem uniformIndexComparison_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (aligned : ∀ position : Fin (plans occurrence).length,
      ProofSyntax Const assumptions (.eq (applyFields _ ((plans occurrence).get position).2 arguments) requested))
    (alignedFree : ∀ position, (aligned position).FunctionExtensionalityFree) :
    (uniformIndexComparison constructors zero successor plans occurrence arguments slot requested aligned).FunctionExtensionalityFree := by
  apply guardedUniformIndexComparison_free
  intro position
  exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (alignedFree position)

#print axioms uniformIndexComparison_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
