import Mettapedia.Logic.HOL.OrderedPositionSelection

/-!
# A local position retained through ordered child-segment prefixes

The relation records the same local position while successive segment counts
shift its absolute slot. Counts and child indices may be open. A local bound
and the selected child index turn this relation into the existing selection
predicate; no arithmetic premise is needed for that implication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
open SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))

def selectedOffsetAt (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number)) :
    Nat → Plan Const Γ number index → {targetContext : Ctx Base} → Subst Const Γ targetContext →
    Term Const targetContext number → Term Const targetContext number → Formula Const targetContext
  | _, [], _, _, _, _ => .bot
  | 0, _ :: _, _, _, localPos, slot => .eq slot localPos
  | ordinal + 1, (count, _) :: rest, _, images, localPos, slot =>
      .ex (.and
        (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (subst images count))) (.var .vz)) (weaken slot))
        (selectedOffsetAt zero successor ordinal rest (fun entry => weaken (images entry)) (weaken localPos) (.var .vz)))
termination_by structural _ plan => plan

theorem selectedOffsetAt_subst (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (later : Subst Const Δ Ξ)
    (localPos slot : Term Const Δ number) :
    subst later (selectedOffsetAt zero successor ordinal plan images localPos slot) =
      selectedOffsetAt zero successor ordinal plan (fun entry => subst later (images entry))
        (subst later localPos) (subst later slot) := by
  induction plan generalizing ordinal Δ Ξ with
  | nil => rfl
  | cons segment rest previous =>
      cases ordinal with
      | zero => rfl
      | succ ordinal =>
          simp only [selectedOffsetAt, subst, subst_weakenCtx, subst_comp, previous, subst_weaken, Subst.lift]
          rfl

theorem selectedOffsetAt_rename (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (later : Rename Base Δ Ξ) (localPos slot : Term Const Δ number) :
    rename later (selectedOffsetAt zero successor ordinal plan images localPos slot) =
      selectedOffsetAt zero successor ordinal plan (fun entry => rename later (images entry))
        (rename later localPos) (rename later slot) := by
  simpa only [subst_ofRename] using selectedOffsetAt_subst zero successor ordinal plan images
    (Subst.ofRename later) localPos slot

def selectedOffsetExists (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (localPos : Term Const Δ number) : Formula Const Δ :=
  .ex (selectedOffsetAt zero successor ordinal plan (fun entry => weaken (images entry)) (weaken localPos) (.var .vz))

theorem selectedOffsetExists_rename (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (later : Rename Base Δ Ξ) (localPos : Term Const Δ number) :
    rename later (selectedOffsetExists zero successor ordinal plan images localPos) =
      selectedOffsetExists zero successor ordinal plan (fun entry => rename later (images entry)) (rename later localPos) := by
  simp only [selectedOffsetExists, rename, selectedOffsetAt_rename, Rename.lift, weaken, rename_comp]
  rfl

def selectedOffsetExists_intro {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (localPos slot : Term Const Δ number)
    (present : ProofSyntax Const assumptions (selectedOffsetAt zero successor ordinal plan images localPos slot)) :
    ProofSyntax Const assumptions (selectedOffsetExists zero successor ordinal plan images localPos) := by
  apply ProofSyntax.exI slot
  apply ProofSyntax.castIndices rfl ?_ present
  simp only [instantiate, selectedOffsetAt_subst, subst, Subst.single, PredicateFixedPoint.subst_single_weaken]

def selectedOffsetAt_later {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (localPos slot offset : Term Const Δ number)
    (shift : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Δ (sum zero successor)) (subst images segment.1)) offset) slot))
    (remaining : ProofSyntax Const assumptions (selectedOffsetAt zero successor ordinal rest images localPos offset)) :
    ProofSyntax Const assumptions (selectedOffsetAt zero successor (ordinal + 1) (segment :: rest) images localPos slot) := by
  apply ProofSyntax.exI offset
  apply ProofSyntax.castIndices rfl ?_ (.andI shift remaining)
  simp only [instantiate, subst, Subst.single, subst_weakenCtx, PredicateFixedPoint.subst_single_weaken,
    selectedOffsetAt_subst]

def selectedOffsetAt_selected :
    (plan : Plan Const Γ number index) → (occurrence : Fin plan.length) → {Δ : Ctx Base} →
    {assumptions : List (Formula Const Δ)} → (images : Subst Const Γ Δ) →
    (localPos slot : Term Const Δ number) → (target : Term Const Δ index) →
    ProofSyntax Const assumptions (selectedOffsetAt zero successor occurrence.val plan images localPos slot) →
    ProofSyntax Const assumptions (.app (.app (weakenCtx Δ (less successor)) localPos)
      (subst images (plan.get occurrence).1)) →
    ProofSyntax Const assumptions (.eq target (subst images (plan.get occurrence).2)) →
    ProofSyntax Const assumptions (selectedAt zero successor occurrence.val plan images slot target)
  | [], occurrence, _, _, _, _, _, _, _, _, _ => nomatch occurrence
  | segment :: rest, occurrence, Δ, assumptions, images, localPos, slot, target, present, bounded, targetEq => by
      refine Fin.cases ?_ (fun ordinal => ?_) occurrence present bounded targetEq
      · intro same bound equal
        exact .andI (.impE (.eqPropER (.eqApp (subst images segment.1)
          (.eqAppArg (weakenCtx Δ (less successor)) same))) bound) equal
      · intro selected bound equal
        apply ProofSyntax.exE selected
        let body := Term.and
          (.app (.app (.app (weakenCtx (number :: Δ) (sum zero successor)) (weaken (subst images segment.1)))
            (.var .vz)) (weaken slot))
          (selectedOffsetAt zero successor ordinal.val rest (fun entry => weaken (images entry))
            (weaken localPos) (.var .vz))
        let hypotheses := body :: weakenHyps assumptions
        let raised : Subst Const Γ (number :: Δ) := fun entry => weaken (images entry)
        have localBound : ProofSyntax Const hypotheses
            (.app (.app (weakenCtx (number :: Δ) (less successor)) (weaken localPos))
              (subst raised (rest.get ordinal).1)) := by
          apply ProofSyntax.castIndices rfl ?_ ((PredicateFixedPoint.weakenProof bound).prepend body)
          simp only [weaken, rename, rename_weakenCtx, rename_subst, raised]
          rfl
        have localEqual : ProofSyntax Const hypotheses
            (.eq (weaken target) (subst raised (rest.get ordinal).2)) := by
          apply ProofSyntax.castIndices rfl ?_ ((PredicateFixedPoint.weakenProof equal).prepend body)
          simp only [weaken, rename, rename_subst, raised]
          rfl
        have tail := selectedOffsetAt_selected rest ordinal raised (weaken localPos) (.var .vz) (weaken target)
          (.andER (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩)) localBound localEqual
        have shift : ProofSyntax Const hypotheses
            (.app (.app (.app (weakenCtx (number :: Δ) (sum zero successor)) (subst raised segment.1))
              (.var .vz)) (weaken slot)) := by
          apply ProofSyntax.castIndices rfl ?_ (.andEL (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩))
          simp only [raised, weaken, rename_subst]
        apply ProofSyntax.castIndices rfl ?_
          (selectedAt_later zero successor ordinal.val segment rest raised (weaken slot) (.var .vz)
            (weaken target) shift tail)
        exact (selectedAt_rename zero successor (ordinal.val + 1) (segment :: rest) images
          Rename.weaken slot target).symm
termination_by structural plan => plan

def selectedOffsetExists_later {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (localPos offset : Term Const Δ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedOffsetAt zero successor ordinal rest images localPos offset)) :
    ProofSyntax Const assumptions (selectedOffsetExists zero successor (ordinal + 1) (segment :: rest) images localPos) := by
  apply ProofSyntax.exE (sumTotal successor zero (subst images segment.1) offset principle)
  let body := Term.app (.app (.app (weakenCtx _ (sum zero successor))
    (weaken (subst images segment.1))) (weaken offset)) (.var .vz)
  let hypotheses := body :: weakenHyps assumptions
  let raised : Subst Const Γ (number :: Δ) := fun entry => weaken (images entry)
  have tail : ProofSyntax Const hypotheses
      (selectedOffsetAt zero successor ordinal rest raised (weaken localPos) (weaken offset)) :=
    ProofSyntax.castIndices rfl (selectedOffsetAt_rename zero successor ordinal rest images Rename.weaken localPos offset)
      ((remaining.rename Rename.weaken).prepend body)
  have shift : ProofSyntax Const hypotheses
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (subst raised segment.1)) (weaken offset)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩)
    change Term.app (.app (.app (weakenCtx _ (sum zero successor))
      (weaken (subst images segment.1))) (weaken offset)) (.var .vz) = _
    have natural : weaken (subst images segment.1) = subst raised segment.1 := by
      unfold weaken raised
      rw [rename_subst]
      rfl
    rw [natural]
  have result := selectedOffsetAt_later zero successor ordinal segment rest raised (weaken localPos) (.var .vz)
    (weaken offset) shift tail
  apply ProofSyntax.castIndices rfl ?_
    (selectedOffsetExists_intro zero successor (ordinal + 1) (segment :: rest) raised (weaken localPos) (.var .vz) result)
  exact (selectedOffsetExists_rename zero successor (ordinal + 1) (segment :: rest) images Rename.weaken localPos).symm

def selectedOffsetExists_prepend {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (localPos : Term Const Δ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedOffsetExists zero successor ordinal rest images localPos)) :
    ProofSyntax Const assumptions (selectedOffsetExists zero successor (ordinal + 1) (segment :: rest) images localPos) := by
  apply ProofSyntax.exE remaining
  let body := selectedOffsetAt zero successor ordinal rest (fun entry => weaken (images entry)) (weaken localPos) (.var .vz)
  let hypotheses := body :: weakenHyps assumptions
  have localPrinciple : ProofSyntax Const hypotheses
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx (number :: Δ) zero) (weakenCtx (number :: Δ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((principle.rename Rename.weaken).prepend body)
    simp only [NaturalRecursionProofs.inductionPrinciple, rename, rename_weakenCtx, ExtDerivation.rename_weaken, Rename.lift]
  apply ProofSyntax.castIndices rfl ?_
    (selectedOffsetExists_later zero successor ordinal segment rest (fun entry => weaken (images entry))
      (weaken localPos) (.var .vz) localPrinciple (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩))
  exact (selectedOffsetExists_rename zero successor (ordinal + 1) (segment :: rest) images Rename.weaken localPos).symm

def selectedOffsetExists_proof :
    (plan : Plan Const Γ number index) → (occurrence : Fin plan.length) → {Δ : Ctx Base} →
    {assumptions : List (Formula Const Δ)} → (images : Subst Const Γ Δ) → (localPos : Term Const Δ number) →
    ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)) →
    ProofSyntax Const assumptions (selectedOffsetExists zero successor occurrence.val plan images localPos)
  | [], occurrence, _, _, _, _, _ => nomatch occurrence
  | segment :: rest, occurrence, _, _, images, localPos, principle =>
      Fin.cases
        (selectedOffsetExists_intro zero successor 0 (segment :: rest) images localPos localPos (.eqRefl localPos))
        (fun ordinal => selectedOffsetExists_prepend zero successor ordinal.val segment rest images localPos principle
          (selectedOffsetExists_proof rest ordinal images localPos principle)) occurrence
termination_by structural plan => plan

theorem selectedOffsetExists_intro_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (localPos slot : Term Const Δ number)
    (present : ProofSyntax Const assumptions (selectedOffsetAt zero successor ordinal plan images localPos slot))
    (free : present.FunctionExtensionalityFree) :
    (selectedOffsetExists_intro zero successor ordinal plan images localPos slot present).FunctionExtensionalityFree := by
  unfold selectedOffsetExists_intro
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem selectedOffsetAt_later_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (localPos slot offset : Term Const Δ number)
    (shift : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Δ (sum zero successor)) (subst images segment.1)) offset) slot))
    (remaining : ProofSyntax Const assumptions (selectedOffsetAt zero successor ordinal rest images localPos offset))
    (shiftFree : shift.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (selectedOffsetAt_later zero successor ordinal segment rest images localPos slot offset shift remaining).FunctionExtensionalityFree := by
  unfold selectedOffsetAt_later
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨shiftFree, remainingFree⟩

theorem selectedOffsetExists_later_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (localPos offset : Term Const Δ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedOffsetAt zero successor ordinal rest images localPos offset))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (selectedOffsetExists_later zero successor ordinal segment rest images localPos offset principle remaining).FunctionExtensionalityFree := by
  unfold selectedOffsetExists_later
  constructor
  · exact sumTotal_free successor zero _ _ principle principleFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply selectedOffsetExists_intro_free
    apply selectedOffsetAt_later_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr remainingFree

theorem selectedOffsetExists_prepend_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (localPos : Term Const Δ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedOffsetExists zero successor ordinal rest images localPos))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (selectedOffsetExists_prepend zero successor ordinal segment rest images localPos principle remaining).FunctionExtensionalityFree := by
  unfold selectedOffsetExists_prepend
  constructor
  · exact remainingFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply selectedOffsetExists_later_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr principleFree
    · trivial

theorem selectedOffsetExists_proof_free (plan : Plan Const Γ number index) (occurrence : Fin plan.length)
    {assumptions : List (Formula Const Δ)} (images : Subst Const Γ Δ) (localPos : Term Const Δ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (free : principle.FunctionExtensionalityFree) :
    (selectedOffsetExists_proof zero successor plan occurrence images localPos principle).FunctionExtensionalityFree := by
  induction plan with
  | nil => exact Fin.elim0 occurrence
  | cons segment rest previous =>
      refine Fin.cases ?_ (fun ordinal => ?_) occurrence
      · exact selectedOffsetExists_intro_free zero successor 0 (segment :: rest) images localPos localPos
          (.eqRefl localPos) True.intro
      · exact selectedOffsetExists_prepend_free zero successor ordinal.val segment rest images localPos principle
          (selectedOffsetExists_proof zero successor rest ordinal images localPos principle) free (previous ordinal)

theorem selectedOffsetAt_selected_free (plan : Plan Const Γ number index) (occurrence : Fin plan.length)
    {assumptions : List (Formula Const Δ)} (images : Subst Const Γ Δ)
    (localPos slot : Term Const Δ number) (target : Term Const Δ index)
    (present : ProofSyntax Const assumptions (selectedOffsetAt zero successor occurrence.val plan images localPos slot))
    (bounded : ProofSyntax Const assumptions (.app (.app (weakenCtx Δ (less successor)) localPos)
      (subst images (plan.get occurrence).1)))
    (targetEq : ProofSyntax Const assumptions (.eq target (subst images (plan.get occurrence).2)))
    (presentFree : present.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree)
    (targetFree : targetEq.FunctionExtensionalityFree) :
    (selectedOffsetAt_selected zero successor plan occurrence images localPos slot target present bounded targetEq).FunctionExtensionalityFree := by
  induction plan generalizing Δ with
  | nil => exact Fin.elim0 occurrence
  | cons segment rest previous =>
      refine Fin.cases ?_ (fun ordinal => ?_) occurrence present bounded targetEq presentFree boundedFree targetFree
      · intro same bound equal sameFree boundFree equalFree
        simpa only [selectedOffsetAt_selected, Fin.cases_zero, ProofSyntax.FunctionExtensionalityFree]
          using And.intro (And.intro sameFree boundFree) equalFree
      · intro selected bound equal selectedFree boundFree equalFree
        unfold selectedOffsetAt_selected
        refine ⟨selectedFree, ?_⟩
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply selectedAt_later_free
        · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          trivial
        · apply previous
          · trivial
          · simpa only [ProofSyntax.functionExtensionalityFree_castIndices, PredicateFixedPoint.weakenProof,
              ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
              ProofSyntax.functionExtensionalityFree_rename] using boundFree
          · simpa only [ProofSyntax.functionExtensionalityFree_castIndices, PredicateFixedPoint.weakenProof,
              ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
              ProofSyntax.functionExtensionalityFree_rename] using equalFree

#print axioms selectedOffsetAt_selected
#print axioms selectedOffsetAt_selected_free
#print axioms selectedOffsetExists_proof
#print axioms selectedOffsetExists_proof_free
end Mettapedia.Logic.HOL.OrderedPositionPrograms
