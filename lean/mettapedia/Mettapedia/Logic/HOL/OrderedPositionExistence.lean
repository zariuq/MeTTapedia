import Mettapedia.Logic.HOL.OrderedPositionFunctionality
import Mettapedia.Logic.HOL.SuccessorOrderPrefixSums

/-!
# Retained lookup witnesses across dynamic prefixes

A known child in a suffix remains present after any finite prefix. Each
prefix count is handled through the retained sum-existence theorem. Positions
remain existential, including under open substitutions; no chosen addition
operation or semantic inverse is used to build proof syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms

open SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))

def lookupExists (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (target : Term Const Δ index) : Formula Const Δ :=
  .ex (compileAt zero successor plan (fun entry => weaken (images entry)) (.var .vz) (weaken target))

theorem lookupExists_subst (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (later : Subst Const Δ Ξ) (target : Term Const Δ index) :
    HOL.subst later (lookupExists zero successor plan images target) =
      lookupExists zero successor plan (fun entry => HOL.subst later (images entry)) (HOL.subst later target) := by
  simp only [lookupExists, HOL.subst, compileAt_subst, subst_weaken, Subst.lift]

theorem lookupExists_rename (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (later : Rename Base Δ Ξ) (target : Term Const Δ index) :
    HOL.rename later (lookupExists zero successor plan images target) =
      lookupExists zero successor plan (fun entry => HOL.rename later (images entry)) (HOL.rename later target) := by
  simpa only [subst_ofRename] using
    lookupExists_subst zero successor plan images (Subst.ofRename later) target

def lookupExists_intro {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (slot : Term Const Δ number) (target : Term Const Δ index)
    (present : ProofSyntax Const assumptions (compileAt zero successor plan images slot target)) :
    ProofSyntax Const assumptions (lookupExists zero successor plan images target) := by
  apply ProofSyntax.exI slot
  apply ProofSyntax.castIndices rfl ?_ present
  simp only [instantiate, compileAt_subst, HOL.subst, Subst.single,
    PredicateFixedPoint.subst_single_weaken]

theorem lookupExists_intro_free {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (slot : Term Const Δ number) (target : Term Const Δ index)
    (present : ProofSyntax Const assumptions (compileAt zero successor plan images slot target))
    (free : present.FunctionExtensionalityFree) :
    (lookupExists_intro zero successor plan images slot target present).FunctionExtensionalityFree := by
  unfold lookupExists_intro
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def lookupExists_later {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (offset : Term Const Δ number) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (compileAt zero successor rest images offset target)) :
    ProofSyntax Const assumptions (lookupExists zero successor (segment :: rest) images target) := by
  apply ProofSyntax.exE (sumTotal successor zero (HOL.subst images segment.1) offset principle)
  let body := Term.app (.app (.app (weakenCtx _ (sum zero successor))
    (weaken (HOL.subst images segment.1))) (weaken offset)) (.var .vz)
  let hypotheses := body :: weakenHyps assumptions
  let raised : Subst Const Γ (number :: Δ) := fun entry => weaken (images entry)
  have tail : ProofSyntax Const hypotheses
      (compileAt zero successor rest raised (weaken offset) (weaken target)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken remaining).prepend body)
    exact compileAt_rename zero successor rest images Rename.weaken offset target
  have shift : ProofSyntax Const hypotheses
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (HOL.subst raised segment.1))
        (weaken offset)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    change Term.app (.app (.app (weakenCtx _ (sum zero successor))
      (weaken (HOL.subst images segment.1))) (weaken offset)) (.var .vz) = _
    have natural : weaken (HOL.subst images segment.1) = HOL.subst raised segment.1 := by
      unfold weaken raised
      rw [HOL.rename_subst]
      rfl
    rw [natural]
  have result := compileAt_later zero successor segment rest raised (.var .vz)
    (weaken offset) (weaken target) shift tail
  apply ProofSyntax.castIndices rfl ?_
    (lookupExists_intro zero successor (segment :: rest) raised (.var .vz) (weaken target) result)
  exact (lookupExists_rename zero successor (segment :: rest) images Rename.weaken target).symm

theorem lookupExists_later_free {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (offset : Term Const Δ number) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (compileAt zero successor rest images offset target))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (lookupExists_later zero successor segment rest images offset target principle remaining).FunctionExtensionalityFree := by
  unfold lookupExists_later
  refine ⟨sumTotal_free _ _ _ _ _ principleFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply lookupExists_intro_free
  apply compileAt_later_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr remainingFree

def lookupExists_prepend {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (lookupExists zero successor rest images target)) :
    ProofSyntax Const assumptions (lookupExists zero successor (segment :: rest) images target) := by
  apply ProofSyntax.exE remaining
  let body := compileAt zero successor rest (fun entry => weaken (images entry)) (.var .vz) (weaken target)
  let hypotheses := body :: weakenHyps assumptions
  have localPrinciple : ProofSyntax Const hypotheses
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx (number :: Δ) zero) (weakenCtx (number :: Δ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken principle).prepend body)
    simp only [NaturalRecursionProofs.inductionPrinciple, HOL.rename, rename_weakenCtx,
      ExtDerivation.rename_weaken, Rename.lift]
  apply ProofSyntax.castIndices rfl ?_
    (lookupExists_later zero successor segment rest (fun entry => weaken (images entry))
      (.var .vz) (weaken target) localPrinciple (.hyp (Δ := hypotheses) 0))
  exact (lookupExists_rename zero successor (segment :: rest) images Rename.weaken target).symm

theorem lookupExists_prepend_free {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (lookupExists zero successor rest images target))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (lookupExists_prepend zero successor segment rest images target principle remaining).FunctionExtensionalityFree := by
  unfold lookupExists_prepend
  refine ⟨remainingFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply lookupExists_later_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr principleFree
  · trivial

def lookupExists_prefix {assumptions : List (Formula Const Δ)}
    (leading : Plan Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (lookupExists zero successor rest images target)) :
    ProofSyntax Const assumptions (lookupExists zero successor (leading ++ rest) images target) := by
  induction leading with
  | nil => exact remaining
  | cons segment leading previous =>
    exact lookupExists_prepend zero successor segment (leading ++ rest) images target principle previous

theorem lookupExists_prefix_free {assumptions : List (Formula Const Δ)}
    (leading : Plan Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (lookupExists zero successor rest images target))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (lookupExists_prefix zero successor leading rest images target principle remaining).FunctionExtensionalityFree := by
  induction leading with
  | nil => exact remainingFree
  | cons segment leading previous =>
    exact lookupExists_prepend_free zero successor segment (leading ++ rest) images target principle _ principleFree previous

#print axioms lookupExists_prefix
#print axioms lookupExists_prefix_free

end Mettapedia.Logic.HOL.OrderedPositionPrograms
