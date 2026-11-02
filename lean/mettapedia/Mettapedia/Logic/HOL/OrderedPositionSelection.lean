import Mettapedia.Logic.HOL.OrderedPositionExistence
import Mettapedia.Logic.HOL.ContextualTrinity

/-!
# Retained selection of one ordered constructor segment

The ordinal identifies a segment occurrence, independently of its child
index. Prefix offsets remain existential sum witnesses. Erasing the selected
branch yields the existing complete lookup relation; it does not identify
different segments that happen to carry the same index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms

open SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))

def selectedAt (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number)) :
    Nat → Plan Const Γ number index → {targetContext : Ctx Base} → Subst Const Γ targetContext →
    Term Const targetContext number → Term Const targetContext index → Formula Const targetContext
  | _, [], _, _, _, _ => .bot
  | 0, (count, childIndex) :: _, _, images, slot, target =>
      .and (.app (.app (weakenCtx _ (less successor)) slot) (subst images count))
        (.eq target (subst images childIndex))
  | ordinal + 1, (count, _) :: rest, _, images, slot, target =>
      .ex (.and
        (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (subst images count))) (.var .vz)) (weaken slot))
        (selectedAt zero successor ordinal rest (fun entry => weaken (images entry)) (.var .vz) (weaken target)))
termination_by structural _ plan => plan

theorem selectedAt_subst (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (later : Subst Const Δ Ξ)
    (slot : Term Const Δ number) (target : Term Const Δ index) :
    subst later (selectedAt zero successor ordinal plan images slot target) =
      selectedAt zero successor ordinal plan (fun entry => subst later (images entry))
        (subst later slot) (subst later target) := by
  induction plan generalizing ordinal Δ Ξ with
  | nil => rfl
  | cons segment rest previous =>
      rcases segment with ⟨count, childIndex⟩
      cases ordinal with
      | zero => simp only [selectedAt, subst, subst_weakenCtx, subst_comp]; rfl
      | succ ordinal =>
          simp only [selectedAt, subst, subst_weakenCtx, subst_comp, previous, subst_weaken, Subst.lift]
          rfl

theorem selectedAt_rename (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (later : Rename Base Δ Ξ)
    (slot : Term Const Δ number) (target : Term Const Δ index) :
    rename later (selectedAt zero successor ordinal plan images slot target) =
      selectedAt zero successor ordinal plan (fun entry => rename later (images entry))
        (rename later slot) (rename later target) := by
  simpa only [subst_ofRename] using
    selectedAt_subst zero successor ordinal plan images (Subst.ofRename later) slot target

def selectedAt_sound :
    (ordinal : Nat) → (plan : Plan Const Γ number index) → {Δ : Ctx Base} →
    {assumptions : List (Formula Const Δ)} → (images : Subst Const Γ Δ) →
    (slot : Term Const Δ number) → (target : Term Const Δ index) →
    ProofSyntax Const assumptions (selectedAt zero successor ordinal plan images slot target) →
    ProofSyntax Const assumptions (compileAt zero successor plan images slot target)
  | _, [], _, _, _, _, _, present => present
  | 0, _ :: _, _, _, _, _, _, present => .orIL present
  | ordinal + 1, segment :: rest, _, _, images, slot, target, present => by
      apply ProofSyntax.orIR
      apply ProofSyntax.impE (ContextualTrinity.exImp ?_) present
      apply ProofSyntax.allI
      apply ProofSyntax.impI
      exact .andI (.andEL (.hyp 0))
        (selectedAt_sound ordinal rest (fun entry => weaken (images entry)) (.var .vz)
          (weaken target) (.andER (.hyp 0)))
termination_by structural _ plan => plan

def selectedExists (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (target : Term Const Δ index) : Formula Const Δ :=
  .ex (selectedAt zero successor ordinal plan (fun entry => weaken (images entry)) (.var .vz) (weaken target))

theorem selectedExists_rename (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (later : Rename Base Δ Ξ) (target : Term Const Δ index) :
    rename later (selectedExists zero successor ordinal plan images target) =
      selectedExists zero successor ordinal plan (fun entry => rename later (images entry)) (rename later target) := by
  simp only [selectedExists, rename, selectedAt_rename, Rename.lift, weaken]
  simp only [rename_comp]
  rfl

def selectedExists_intro {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (slot : Term Const Δ number) (target : Term Const Δ index)
    (present : ProofSyntax Const assumptions (selectedAt zero successor ordinal plan images slot target)) :
    ProofSyntax Const assumptions (selectedExists zero successor ordinal plan images target) := by
  apply ProofSyntax.exI slot
  apply ProofSyntax.castIndices rfl ?_ present
  simp only [instantiate, selectedAt_subst, subst, Subst.single, PredicateFixedPoint.subst_single_weaken]

def selectedAt_later {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (slot offset : Term Const Δ number) (target : Term Const Δ index)
    (shift : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Δ (sum zero successor)) (subst images segment.1)) offset) slot))
    (remaining : ProofSyntax Const assumptions (selectedAt zero successor ordinal rest images offset target)) :
    ProofSyntax Const assumptions (selectedAt zero successor (ordinal + 1) (segment :: rest) images slot target) := by
  apply ProofSyntax.exI offset
  apply ProofSyntax.castIndices rfl ?_ (.andI shift remaining)
  simp only [instantiate, subst, Subst.single, subst_weakenCtx,
    PredicateFixedPoint.subst_single_weaken, selectedAt_subst]

def selectedExists_later {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (offset : Term Const Δ number) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedAt zero successor ordinal rest images offset target)) :
    ProofSyntax Const assumptions (selectedExists zero successor (ordinal + 1) (segment :: rest) images target) := by
  apply ProofSyntax.exE (sumTotal successor zero (subst images segment.1) offset principle)
  let body := Term.app (.app (.app (weakenCtx _ (sum zero successor))
    (weaken (subst images segment.1))) (weaken offset)) (.var .vz)
  let hypotheses := body :: weakenHyps assumptions
  let raised : Subst Const Γ (number :: Δ) := fun entry => weaken (images entry)
  have tail : ProofSyntax Const hypotheses (selectedAt zero successor ordinal rest raised (weaken offset) (weaken target)) :=
    ProofSyntax.castIndices rfl (selectedAt_rename zero successor ordinal rest images Rename.weaken offset target)
      ((remaining.rename Rename.weaken).prepend body)
  have shift : ProofSyntax Const hypotheses
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (subst raised segment.1)) (weaken offset)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    change Term.app (.app (.app (weakenCtx _ (sum zero successor))
      (weaken (subst images segment.1))) (weaken offset)) (.var .vz) = _
    have natural : weaken (subst images segment.1) = subst raised segment.1 := by
      unfold weaken raised
      rw [rename_subst]
      rfl
    rw [natural]
  have result := selectedAt_later zero successor ordinal segment rest raised (.var .vz) (weaken offset) (weaken target) shift tail
  apply ProofSyntax.castIndices rfl ?_
    (selectedExists_intro zero successor (ordinal + 1) (segment :: rest) raised (.var .vz) (weaken target) result)
  exact (selectedExists_rename zero successor (ordinal + 1) (segment :: rest) images Rename.weaken target).symm

def selectedExists_prepend {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedExists zero successor ordinal rest images target)) :
    ProofSyntax Const assumptions (selectedExists zero successor (ordinal + 1) (segment :: rest) images target) := by
  apply ProofSyntax.exE remaining
  let body := selectedAt zero successor ordinal rest (fun entry => weaken (images entry)) (.var .vz) (weaken target)
  let hypotheses := body :: weakenHyps assumptions
  have localPrinciple : ProofSyntax Const hypotheses
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx (number :: Δ) zero) (weakenCtx (number :: Δ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((principle.rename Rename.weaken).prepend body)
    simp only [NaturalRecursionProofs.inductionPrinciple, rename, rename_weakenCtx, ExtDerivation.rename_weaken, Rename.lift]
  apply ProofSyntax.castIndices rfl ?_
    (selectedExists_later zero successor ordinal segment rest (fun entry => weaken (images entry))
      (.var .vz) (weaken target) localPrinciple (.hyp (Δ := hypotheses) 0))
  exact (selectedExists_rename zero successor (ordinal + 1) (segment :: rest) images Rename.weaken target).symm

theorem selectedAt_sound_free (ordinal : Nat) (plan : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (slot : Term Const Δ number) (target : Term Const Δ index)
    {assumptions : List (Formula Const Δ)}
    (present : ProofSyntax Const assumptions (selectedAt zero successor ordinal plan images slot target))
    (free : present.FunctionExtensionalityFree) :
    (selectedAt_sound zero successor ordinal plan images slot target present).FunctionExtensionalityFree := by
  induction plan generalizing ordinal Δ with
  | nil => exact free
  | cons segment rest previous =>
      cases ordinal with
      | zero => exact free
      | succ ordinal =>
          unfold selectedAt_sound
          constructor
          · apply (ContextualTrinity.exImp_free _).mpr
            exact ⟨True.intro, previous ordinal _ _ _ _ True.intro⟩
          · exact free

theorem selectedExists_intro_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (slot : Term Const Δ number) (target : Term Const Δ index)
    (present : ProofSyntax Const assumptions (selectedAt zero successor ordinal plan images slot target))
    (free : present.FunctionExtensionalityFree) :
    (selectedExists_intro zero successor ordinal plan images slot target present).FunctionExtensionalityFree := by
  unfold selectedExists_intro
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem selectedAt_later_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (slot offset : Term Const Δ number) (target : Term Const Δ index)
    (shift : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Δ (sum zero successor)) (subst images segment.1)) offset) slot))
    (remaining : ProofSyntax Const assumptions (selectedAt zero successor ordinal rest images offset target))
    (shiftFree : shift.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (selectedAt_later zero successor ordinal segment rest images slot offset target shift remaining).FunctionExtensionalityFree := by
  unfold selectedAt_later
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨shiftFree, remainingFree⟩

theorem selectedExists_later_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (offset : Term Const Δ number) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedAt zero successor ordinal rest images offset target))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (selectedExists_later zero successor ordinal segment rest images offset target principle remaining).FunctionExtensionalityFree := by
  unfold selectedExists_later
  constructor
  · exact sumTotal_free successor zero _ _ principle principleFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply selectedExists_intro_free
    apply selectedAt_later_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr remainingFree

theorem selectedExists_prepend_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedExists zero successor ordinal rest images target))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (selectedExists_prepend zero successor ordinal segment rest images target principle remaining).FunctionExtensionalityFree := by
  unfold selectedExists_prepend
  constructor
  · exact remainingFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply selectedExists_later_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr principleFree
    · trivial

def selectedExists_prefix {assumptions : List (Formula Const Δ)} :
    (leading rest : Plan Const Γ number index) → (ordinal : Nat) → (images : Subst Const Γ Δ) → (target : Term Const Δ index) →
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor))) →
    (remaining : ProofSyntax Const assumptions (selectedExists zero successor ordinal rest images target)) →
    ProofSyntax Const assumptions (selectedExists zero successor (leading.length + ordinal) (leading ++ rest) images target)
  | [], rest, ordinal, images, target, _, remaining =>
      ProofSyntax.castIndices rfl (congrArg (fun selected => selectedExists zero successor selected rest images target)
        (Nat.zero_add ordinal).symm) remaining
  | segment :: leading, rest, ordinal, images, target, principle, remaining =>
      let previous := selectedExists_prefix leading rest ordinal images target principle remaining
      let result := selectedExists_prepend zero successor (leading.length + ordinal) segment (leading ++ rest) images target principle previous
      ProofSyntax.castIndices rfl (congrArg (fun selected => selectedExists zero successor selected
        ((segment :: leading) ++ rest) images target) (by simp only [List.length_cons]; omega)) result

def selectedExists_here {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (target : Term Const Δ index)
    (positive : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Δ (less successor)) (weakenCtx Δ zero)) (subst images segment.1)))
    (indexProof : ProofSyntax Const assumptions (.eq target (subst images segment.2))) :
    ProofSyntax Const assumptions (selectedExists zero successor 0 (segment :: rest) images target) :=
  selectedExists_intro zero successor 0 (segment :: rest) images (weakenCtx Δ zero) target (.andI positive indexProof)

theorem selectedExists_here_free {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (target : Term Const Δ index)
    (positive : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Δ (less successor)) (weakenCtx Δ zero)) (subst images segment.1)))
    (indexProof : ProofSyntax Const assumptions (.eq target (subst images segment.2)))
    (positiveFree : positive.FunctionExtensionalityFree) (indexFree : indexProof.FunctionExtensionalityFree) :
    (selectedExists_here zero successor segment rest images target positive indexProof).FunctionExtensionalityFree :=
  selectedExists_intro_free zero successor 0 (segment :: rest) images (weakenCtx Δ zero) target _ ⟨positiveFree, indexFree⟩

theorem selectedExists_prefix_free {assumptions : List (Formula Const Δ)}
    (leading rest : Plan Const Γ number index) (ordinal : Nat) (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (remaining : ProofSyntax Const assumptions (selectedExists zero successor ordinal rest images target))
    (principleFree : principle.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (selectedExists_prefix zero successor leading rest ordinal images target principle remaining).FunctionExtensionalityFree := by
  induction leading with
  | nil => exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr remainingFree
  | cons segment leading previous =>
      simp only [selectedExists_prefix]
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact selectedExists_prepend_free zero successor _ _ _ _ _ principle _ principleFree previous

def selectedExists_sound {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (plan : Plan Const Γ number index) (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (present : ProofSyntax Const assumptions (selectedExists zero successor ordinal plan images target)) :
    ProofSyntax Const assumptions (lookupExists zero successor plan images target) := by
  apply ProofSyntax.impE (ContextualTrinity.exImp ?_) present
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  exact selectedAt_sound zero successor ordinal plan (fun entry => weaken (images entry)) (.var .vz)
    (weaken target) (.hyp 0)

def selectedExists_at {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (ordinal : Nat) (segment : Segment Const Γ number index)
    (found : plan[ordinal]? = some segment) (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (positive : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Δ (less successor)) (weakenCtx Δ zero)) (subst images segment.1)))
    (indexProof : ProofSyntax Const assumptions (.eq target (subst images segment.2))) :
    ProofSyntax Const assumptions (selectedExists zero successor ordinal plan images target) := by
  have inside : ordinal < plan.length := (List.getElem?_eq_some_iff.mp found).1
  have chosen : plan[ordinal] = segment := (List.getElem?_eq_some_iff.mp found).2
  have assembled : plan.take ordinal ++ segment :: plan.drop (ordinal + 1) = plan := by
    simpa only [List.drop_eq_getElem_cons inside, chosen] using List.take_append_drop ordinal plan
  let result := selectedExists_prefix zero successor (plan.take ordinal) (segment :: plan.drop (ordinal + 1)) 0 images target
    principle (selectedExists_here zero successor segment _ images target positive indexProof)
  exact ProofSyntax.castIndices rfl (by
    rw [List.length_take, Nat.min_eq_left (by omega), Nat.add_zero, assembled]) result

theorem selectedExists_at_free {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (ordinal : Nat) (segment : Segment Const Γ number index)
    (found : plan[ordinal]? = some segment) (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Δ zero) (weakenCtx Δ successor)))
    (positive : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Δ (less successor)) (weakenCtx Δ zero)) (subst images segment.1)))
    (indexProof : ProofSyntax Const assumptions (.eq target (subst images segment.2)))
    (principleFree : principle.FunctionExtensionalityFree) (positiveFree : positive.FunctionExtensionalityFree)
    (indexFree : indexProof.FunctionExtensionalityFree) :
    (selectedExists_at zero successor plan ordinal segment found images target principle positive indexProof).FunctionExtensionalityFree := by
  unfold selectedExists_at
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact selectedExists_prefix_free zero successor _ _ _ _ _ principle _ principleFree
    (selectedExists_here_free zero successor _ _ _ _ positive indexProof positiveFree indexFree)

theorem selectedExists_sound_free {assumptions : List (Formula Const Δ)}
    (ordinal : Nat) (plan : Plan Const Γ number index) (images : Subst Const Γ Δ) (target : Term Const Δ index)
    (present : ProofSyntax Const assumptions (selectedExists zero successor ordinal plan images target))
    (free : present.FunctionExtensionalityFree) :
    (selectedExists_sound zero successor ordinal plan images target present).FunctionExtensionalityFree := by
  unfold selectedExists_sound
  constructor
  · apply (ContextualTrinity.exImp_free _).mpr
    exact selectedAt_sound_free zero successor ordinal plan _ _ _ _ True.intro
  · exact free

#print axioms selectedAt_sound_free
#print axioms selectedExists_prepend_free

#print axioms selectedAt_sound
#print axioms selectedExists_prepend

end Mettapedia.Logic.HOL.OrderedPositionPrograms
