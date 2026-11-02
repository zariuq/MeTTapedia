import Mettapedia.Logic.HOL.OrderedPositionProofs
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Retained conversion of ordered position plans

Counts and index labels are compared by supplied HOL equality proofs, rather
than by host syntactic equality. The existing compiler preserves this evidence
through every segment, including the existential scope of later positions.
No normalization algorithm or conversion oracle is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number index : Ty Base}

inductive PlanEquations (assumptions : List (Formula Const Γ)) :
    Plan Const Γ number index → Plan Const Γ number index → Type (max u v) where
  | nil : PlanEquations assumptions [] []
  | cons {left right : Segment Const Γ number index} {leftRest rightRest : Plan Const Γ number index}
      (count : ProofSyntax Const assumptions (.eq left.1 right.1))
      (label : ProofSyntax Const assumptions (.eq left.2 right.2))
      (rest : PlanEquations assumptions leftRest rightRest) :
      PlanEquations assumptions (left :: leftRest) (right :: rightRest)

namespace PlanEquations
variable {Δ : List (Formula Const Γ)} {left right : Plan Const Γ number index}

def Free : {left right : Plan Const Γ number index} → PlanEquations Δ left right → Prop
  | _, _, .nil => True
  | _, _, .cons count label rest => count.FunctionExtensionalityFree ∧ label.FunctionExtensionalityFree ∧ rest.Free

def subst : {left right : Plan Const Γ number index} → (equations : PlanEquations Δ left right) →
    (images : Subst Const Γ Ξ) → PlanEquations (Δ.map (HOL.subst images)) (substitute images left) (substitute images right)
  | _, _, .nil, _ => .nil
  | _, _, .cons count label rest, images => .cons (count.subst images) (label.subst images) (rest.subst images)

theorem subst_free (equations : PlanEquations Δ left right) (images : Subst Const Γ Ξ)
    (free : equations.Free) : (equations.subst images).Free := by
  induction equations with
  | nil => trivial
  | cons count label rest previous =>
      exact ⟨(ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.1,
        (ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.2.1,previous free.2.2⟩

def cast {Δ' : List (Formula Const Γ)} {left' right' : Plan Const Γ number index}
    (hypotheses : Δ = Δ') (source : left = left') (target : right = right')
    (equations : PlanEquations Δ left right) : PlanEquations Δ' left' right' := by
  cases hypotheses; cases source; cases target
  exact equations

theorem cast_free {Δ' : List (Formula Const Γ)} {left' right' : Plan Const Γ number index}
    (hypotheses : Δ = Δ') (source : left = left') (target : right = right')
    (equations : PlanEquations Δ left right) (free : equations.Free) :
    (cast hypotheses source target equations).Free := by
  cases hypotheses; cases source; cases target
  exact free

def prepend : {left right : Plan Const Γ number index} → (equations : PlanEquations Δ left right) →
    (formula : Formula Const Γ) → PlanEquations (formula :: Δ) left right
  | _, _, .nil, _ => .nil
  | _, _, .cons count label rest, formula => .cons (count.prepend formula) (label.prepend formula) (rest.prepend formula)

theorem prepend_free (equations : PlanEquations Δ left right) (formula : Formula Const Γ)
    (free : equations.Free) : (equations.prepend formula).Free := by
  induction equations with
  | nil => trivial
  | cons count label rest previous =>
      refine ⟨?_,?_,previous free.2.2⟩
      · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using free.1
      · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using free.2.1
end PlanEquations

variable (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))
    {Δ : List (Formula Const Γ)}

def compileAt_congr : {left right : Plan Const Γ number index} → (equations : PlanEquations Δ left right) →
    {Ξ : Ctx Base} → (images : Subst Const Γ Ξ) → (slot : Term Const Ξ number) → (target : Term Const Ξ index) →
    ProofSyntax Const (Δ.map (HOL.subst images))
      (.eq (compileAt zero successor left images slot target) (compileAt zero successor right images slot target))
  | [], [], .nil, _, _, _, _ => .eqRefl .bot
  | left :: leftRest, right :: rightRest, .cons count label rest, Ξ, images, slot, target => by
      let firstCount := count.subst images
      let firstLabel := label.subst images
      have here := ProofSyntax.andCongr (.eqAppArg (.app (weakenCtx Ξ (SuccessorOrder.less successor)) slot) firstCount)
        (.eqCongr (.eqRefl target) firstLabel)
      have sumEqual : ProofSyntax Const (weakenHyps (σ := number) (Δ.map (HOL.subst images)))
          (.eq (.app (.app (.app (weakenCtx _ (SuccessorOrder.sum zero successor)) (weaken (HOL.subst images left.1)))
              (.var .vz)) (weaken slot))
            (.app (.app (.app (weakenCtx _ (SuccessorOrder.sum zero successor)) (weaken (HOL.subst images right.1)))
              (.var .vz)) (weaken slot))) :=
        .eqApp (weaken slot) (.eqApp (.var .vz) (.eqAppArg (weakenCtx _ (SuccessorOrder.sum zero successor))
          (firstCount.rename Rename.weaken)))
      have remaining := compileAt_congr rest (fun entry => weaken (images entry)) (.var .vz) (weaken target)
      have underBinder : ProofSyntax Const (weakenHyps (σ := number) (Δ.map (HOL.subst images)))
          (.eq (compileAt zero successor leftRest (fun entry => weaken (images entry)) (.var .vz) (weaken target))
            (compileAt zero successor rightRest (fun entry => weaken (images entry)) (.var .vz) (weaken target))) := by
        apply ProofSyntax.castIndices ?_ rfl remaining
        change Δ.map (HOL.subst (fun entry => weaken (images entry))) = (Δ.map (HOL.subst images)).map weaken
        rw [List.map_map]
        apply List.map_congr_left
        intro formula _
        exact (HOL.rename_subst Rename.weaken images formula).symm
      exact .orCongr here (ContextualTrinity.exCongr (.andCongr sumEqual underBinder))

theorem compileAt_congr_free {left right : Plan Const Γ number index} (equations : PlanEquations Δ left right)
    (free : equations.Free) (images : Subst Const Γ Ξ) (slot : Term Const Ξ number) (target : Term Const Ξ index) :
    (compileAt_congr zero successor equations images slot target).FunctionExtensionalityFree := by
  induction equations generalizing Ξ with
  | nil => trivial
  | cons count label rest previous =>
      unfold compileAt_congr
      apply (ProofSyntax.orCongr_free _ _).mpr
      constructor
      · apply (ProofSyntax.andCongr_free _ _).mpr
        constructor
        · exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.1
        · exact (ProofSyntax.eqCongr_free _ _).mpr ⟨True.intro,(ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.2.1⟩
      · apply (ContextualTrinity.exCongr_free _).mpr
        apply (ProofSyntax.andCongr_free _ _).mpr
        constructor
        · exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr
            ((ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.1)
        · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          exact previous free.2.2 _ _ _

def compileAt_planEquation {left right : Plan Const Γ number index} (equations : PlanEquations Δ left right)
    (slot : Term Const Γ number) (target : Term Const Γ index) :
    ProofSyntax Const Δ (.eq (compileAt zero successor left Subst.id slot target)
      (compileAt zero successor right Subst.id slot target)) :=
  ProofSyntax.castIndices (ProofSyntax.terms_subst_of_identity (fun _ => rfl) Δ) rfl
    (compileAt_congr zero successor equations Subst.id slot target)

theorem compileAt_planEquation_free {left right : Plan Const Γ number index} (equations : PlanEquations Δ left right)
    (slot : Term Const Γ number) (target : Term Const Γ index) (free : equations.Free) :
    (compileAt_planEquation zero successor equations slot target).FunctionExtensionalityFree := by
  unfold compileAt_planEquation
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact compileAt_congr_free zero successor equations free Subst.id slot target

#print axioms compileAt_congr
#print axioms compileAt_congr_free
#print axioms compileAt_planEquation_free
end Mettapedia.Logic.HOL.OrderedPositionPrograms
