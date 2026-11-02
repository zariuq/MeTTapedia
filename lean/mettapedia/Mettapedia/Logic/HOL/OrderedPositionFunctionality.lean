import Mettapedia.Logic.HOL.OrderedPositionProofs
import Mettapedia.Logic.HOL.SuccessorOrderArithmetic
import Mettapedia.Logic.HOL.ConstructorIndexSelection

/-!
# Functional child indices for heterogeneous ordered segments

Lookup branches are separated using retained Peano arithmetic. Two residual
branches have equal offsets; ordinary equality congruence then places both
queries at the same slot before structural recursion on the original plan.
Empty segments and duplicate occurrences remain part of that plan.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms

open SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))

theorem compileAt_rename (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (mapping : Rename Base Δ Ξ) (slot : Term Const Δ number) (target : Term Const Δ index) :
    HOL.rename mapping (compileAt zero successor plan images slot target) =
      compileAt zero successor plan (fun entry => HOL.rename mapping (images entry))
        (HOL.rename mapping slot) (HOL.rename mapping target) := by
  simpa only [subst_ofRename] using
    (compileAt_subst zero successor plan images (Subst.ofRename mapping) slot target)

/-- Introduce a source position in the first segment, retaining its exact index. -/
def compileAt_here {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (slot : Term Const Δ number) (target : Term Const Δ index)
    (before : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Δ (less successor)) slot) (HOL.subst images segment.1)))
    (selected : ProofSyntax Const assumptions (.eq target (HOL.subst images segment.2))) :
    ProofSyntax Const assumptions (compileAt zero successor (segment :: rest) images slot target) :=
  .orIL (.andI before selected)

theorem compileAt_here_free {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (slot : Term Const Δ number) (target : Term Const Δ index)
    (before : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Δ (less successor)) slot) (HOL.subst images segment.1)))
    (selected : ProofSyntax Const assumptions (.eq target (HOL.subst images segment.2)))
    (beforeFree : before.FunctionExtensionalityFree) (selectedFree : selected.FunctionExtensionalityFree) :
    (compileAt_here zero successor segment rest images slot target before selected).FunctionExtensionalityFree :=
  ⟨beforeFree, selectedFree⟩

/-- Introduce a later source position using its retained prefix-sum witness. -/
def compileAt_later {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (slot offset : Term Const Δ number) (target : Term Const Δ index)
    (shift : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Δ (sum zero successor)) (HOL.subst images segment.1)) offset) slot))
    (remaining : ProofSyntax Const assumptions (compileAt zero successor rest images offset target)) :
    ProofSyntax Const assumptions (compileAt zero successor (segment :: rest) images slot target) := by
  apply ProofSyntax.orIR
  apply ProofSyntax.exI offset
  apply ProofSyntax.castIndices rfl ?_ (.andI shift remaining)
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx,
    PredicateFixedPoint.subst_single_weaken, compileAt_subst]

theorem compileAt_later_free {assumptions : List (Formula Const Δ)}
    (segment : Segment Const Γ number index) (rest : Plan Const Γ number index)
    (images : Subst Const Γ Δ) (slot offset : Term Const Δ number) (target : Term Const Δ index)
    (shift : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Δ (sum zero successor)) (HOL.subst images segment.1)) offset) slot))
    (remaining : ProofSyntax Const assumptions (compileAt zero successor rest images offset target))
    (shiftFree : shift.FunctionExtensionalityFree) (remainingFree : remaining.FunctionExtensionalityFree) :
    (compileAt_later zero successor segment rest images slot offset target shift remaining).FunctionExtensionalityFree := by
  unfold compileAt_later
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨shiftFree, remainingFree⟩

def queryAt (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (target : Term Const Δ index) : Term Const Δ (number ⇒ .prop) :=
  .lam (compileAt zero successor plan (fun entry => weaken (images entry)) (.var .vz) (weaken target))

def queryAt_beta {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (slot : Term Const Δ number) (target : Term Const Δ index) :
    ProofSyntax Const assumptions (.eq (.app (queryAt zero successor plan images target) slot)
      (compileAt zero successor plan images slot target)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta slot
    (compileAt zero successor plan (fun entry => weaken (images entry)) (.var .vz) (weaken target)))
  apply congrArg₂ Term.eq
  · rfl
  · simp only [instantiate, compileAt_subst, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]

theorem queryAt_beta_free {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (slot : Term Const Δ number) (target : Term Const Δ index) :
    (queryAt_beta zero successor (assumptions := assumptions) plan images slot target).FunctionExtensionalityFree := by
  unfold queryAt_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def compileAt_slotEquality {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (left right : Term Const Δ number) (target : Term Const Δ index)
    (equal : ProofSyntax Const assumptions (.eq left right)) :
    ProofSyntax Const assumptions (.eq (compileAt zero successor plan images left target)
      (compileAt zero successor plan images right target)) :=
  .eqTrans (.eqSymm (queryAt_beta zero successor plan images left target))
    (.eqTrans (.eqAppArg (queryAt zero successor plan images target) equal)
      (queryAt_beta zero successor plan images right target))

theorem compileAt_slotEquality_free {assumptions : List (Formula Const Δ)}
    (plan : Plan Const Γ number index) (images : Subst Const Γ Δ)
    (left right : Term Const Δ number) (target : Term Const Δ index)
    (equal : ProofSyntax Const assumptions (.eq left right)) (free : equal.FunctionExtensionalityFree) :
    (compileAt_slotEquality zero successor plan images left right target equal).FunctionExtensionalityFree := by
  exact ⟨queryAt_beta_free _ _ _ _ _ _, free, queryAt_beta_free _ _ _ _ _ _⟩

def shiftedBranchRefute {assumptions : List (Formula Const Δ)}
    (arithmetic : PeanoEvidence successor zero assumptions)
    (count slot : Term Const Δ number) (tail : Formula Const (number :: Δ))
    (before : ProofSyntax Const assumptions (.app (.app (weakenCtx Δ (less successor)) slot) count))
    (later : ProofSyntax Const assumptions (.ex (.and
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken count)) (.var .vz)) (weaken slot)) tail))) :
    ProofSyntax Const assumptions .bot := by
  apply ProofSyntax.exE later
  let body := Term.and (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken count)) (.var .vz))
    (weaken slot)) tail
  let hypotheses := body :: weakenHyps assumptions
  let localArithmetic := (arithmetic.rename Rename.weaken).prepend body
  have given : ProofSyntax Const hypotheses body := .hyp 0
  have before' : ProofSyntax Const hypotheses
      (.app (.app (weakenCtx _ (less successor)) (weaken slot)) (weaken count)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken before).prepend body)
    simp only [HOL.rename, weaken, rename_weakenCtx]
  exact .notE (sumExcludesLeft successor zero (weaken count) (.var .vz) (weaken slot)
    localArithmetic.separation localArithmetic.injectivity localArithmetic.induction (.andEL given)) before'

theorem shiftedBranchRefute_free {assumptions : List (Formula Const Δ)}
    (arithmetic : PeanoEvidence successor zero assumptions)
    (count slot : Term Const Δ number) (tail : Formula Const (number :: Δ))
    (before : ProofSyntax Const assumptions (.app (.app (weakenCtx Δ (less successor)) slot) count))
    (later : ProofSyntax Const assumptions (.ex (.and
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken count)) (.var .vz)) (weaken slot)) tail)))
    (arithmeticFree : arithmetic.Free) (beforeFree : before.FunctionExtensionalityFree)
    (laterFree : later.FunctionExtensionalityFree) :
    (shiftedBranchRefute zero successor arithmetic count slot tail before later).FunctionExtensionalityFree := by
  unfold shiftedBranchRefute
  refine ⟨laterFree, ?_, ?_⟩
  · apply sumExcludesLeft_free
    · exact (PeanoEvidence.prepend_free _ _ (arithmetic.rename_free Rename.weaken arithmeticFree)).1
    · exact (PeanoEvidence.prepend_free _ _ (arithmetic.rename_free Rename.weaken arithmeticFree)).2.1
    · exact (PeanoEvidence.prepend_free _ _ (arithmetic.rename_free Rename.weaken arithmeticFree)).2.2
    · trivial
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr beforeFree

#print axioms compileAt_slotEquality_free
#print axioms shiftedBranchRefute_free

def compileAt_functional (plan : Plan Const Γ number index) :
    {Δ : Ctx Base} → (images : Subst Const Γ Δ) →
    (slot : Term Const Δ number) → (leftTarget rightTarget : Term Const Δ index) →
    {assumptions : List (Formula Const Δ)} →
    PeanoEvidence successor zero assumptions →
    ProofSyntax Const assumptions (compileAt zero successor plan images slot leftTarget) →
    ProofSyntax Const assumptions (compileAt zero successor plan images slot rightTarget) →
    ProofSyntax Const assumptions (.eq leftTarget rightTarget) := by
  induction plan with
  | nil =>
      intro Δ images slot leftTarget rightTarget assumptions arithmetic left _
      exact .botE left
  | cons segment rest previous =>
      intro Δ images slot leftTarget rightTarget assumptions arithmetic left right
      let firstLeft := Term.and
        (.app (.app (weakenCtx Δ (less successor)) slot) (HOL.subst images segment.1))
        (.eq leftTarget (HOL.subst images segment.2))
      let firstRight := Term.and
        (.app (.app (weakenCtx Δ (less successor)) slot) (HOL.subst images segment.1))
        (.eq rightTarget (HOL.subst images segment.2))
      let raised : Subst Const Γ (number :: Δ) := fun entry => weaken (images entry)
      let leftTail := compileAt zero successor rest raised (.var .vz) (weaken leftTarget)
      let rightTail := compileAt zero successor rest raised (.var .vz) (weaken rightTarget)
      let leftBody := Term.and
        (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (HOL.subst images segment.1)))
          (.var .vz)) (weaken slot)) leftTail
      let rightBody := Term.and
        (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (HOL.subst images segment.1)))
          (.var .vz)) (weaken slot)) rightTail
      let laterLeft := Term.ex leftBody
      let laterRight := Term.ex rightBody
      apply ProofSyntax.orE left
      · apply ProofSyntax.orE (right.prepend firstLeft)
        · exact .eqTrans (.andER (.hyp 1)) (.eqSymm (.andER (.hyp 0)))
        · exact .botE (shiftedBranchRefute zero successor
            ((arithmetic.prepend firstLeft).prepend laterRight)
            (HOL.subst images segment.1) slot rightTail (.andEL (.hyp 1)) (.hyp 0))
      · apply ProofSyntax.orE (right.prepend laterLeft)
        · exact .botE (shiftedBranchRefute zero successor
            ((arithmetic.prepend laterLeft).prepend firstRight)
            (HOL.subst images segment.1) slot leftTail (.andEL (.hyp 0)) (.hyp 1))
        · let branchHypotheses := laterRight :: laterLeft :: assumptions
          have leftPresent : ProofSyntax Const branchHypotheses laterLeft := .hyp 1
          apply ProofSyntax.exE leftPresent
          let leftHypotheses := leftBody :: weakenHyps branchHypotheses
          let raisedAgain : Subst Const Γ (number :: number :: Δ) := fun entry => weaken (raised entry)
          let rightBody' : Formula Const (number :: number :: Δ) := Term.and
            (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (weaken (HOL.subst images segment.1))))
              (.var .vz)) (weaken (weaken slot)))
            (compileAt zero successor rest raisedAgain (.var .vz) (weaken (weaken rightTarget)))
          have rightPresent : ProofSyntax Const leftHypotheses (.ex rightBody') := by
            apply ProofSyntax.castIndices rfl ?_
              ((ProofSyntax.rename Rename.weaken (ProofSyntax.hyp (Δ := branchHypotheses) 0)).prepend leftBody)
            change HOL.rename Rename.weaken laterRight = _
            simp only [laterRight, rightBody, rightTail, HOL.rename, rename_weakenCtx,
              ExtDerivation.rename_weaken, Rename.lift, compileAt_rename, raised, raisedAgain, rightBody']
            rfl
          apply ProofSyntax.exE rightPresent
          let hypotheses := rightBody' :: weakenHyps leftHypotheses
          have rightGiven : ProofSyntax Const hypotheses rightBody' := .hyp 0
          have leftGiven : ProofSyntax Const hypotheses
              (.and (.app (.app (.app (weakenCtx _ (sum zero successor))
                (weaken (weaken (HOL.subst images segment.1)))) (.var (.vs .vz))) (weaken (weaken slot)))
                (compileAt zero successor rest raisedAgain (.var (.vs .vz)) (weaken (weaken leftTarget)))) := by
            apply ProofSyntax.castIndices rfl ?_
              ((ProofSyntax.rename Rename.weaken (ProofSyntax.hyp (Δ := leftHypotheses) 0)).prepend rightBody')
            change HOL.rename Rename.weaken leftBody = _
            simp only [leftBody, leftTail, HOL.rename, rename_weakenCtx,
              compileAt_rename, Rename.weaken]
            rfl
          let localArithmetic :=
            (((((arithmetic.prepend laterLeft).prepend laterRight).rename Rename.weaken).prepend leftBody).rename
              Rename.weaken).prepend rightBody'
          have sameOffset := sumOffsetUnique successor zero (weaken (weaken (HOL.subst images segment.1)))
            (.var (.vs .vz)) (.var .vz) (weaken (weaken slot))
            localArithmetic.injectivity localArithmetic.induction (.andEL leftGiven) (.andEL rightGiven)
          have rightAtLeft := ProofSyntax.impE (.eqPropER
            (compileAt_slotEquality zero successor rest raisedAgain (.var (.vs .vz)) (.var .vz)
              (weaken (weaken rightTarget)) sameOffset)) (.andER rightGiven)
          exact previous raisedAgain (.var (.vs .vz)) (weaken (weaken leftTarget)) (weaken (weaken rightTarget))
            localArithmetic (.andER leftGiven) rightAtLeft

#print axioms compileAt_functional

theorem compileAt_functional_free (plan : Plan Const Γ number index) :
    {Δ : Ctx Base} → (images : Subst Const Γ Δ) →
    (slot : Term Const Δ number) → (leftTarget rightTarget : Term Const Δ index) →
    {assumptions : List (Formula Const Δ)} →
    (arithmetic : PeanoEvidence successor zero assumptions) →
    (left : ProofSyntax Const assumptions (compileAt zero successor plan images slot leftTarget)) →
    (right : ProofSyntax Const assumptions (compileAt zero successor plan images slot rightTarget)) →
    arithmetic.Free → left.FunctionExtensionalityFree → right.FunctionExtensionalityFree →
    (compileAt_functional zero successor plan images slot leftTarget rightTarget arithmetic left right).FunctionExtensionalityFree := by
  induction plan with
  | nil =>
      intro Δ images slot leftTarget rightTarget assumptions arithmetic left right arithmeticFree leftFree _
      exact leftFree
  | cons segment rest previous =>
      intro Δ images slot leftTarget rightTarget assumptions arithmetic left right arithmeticFree leftFree rightFree
      unfold compileAt_functional
      refine ⟨leftFree, ?_, ?_⟩
      · refine ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr rightFree, by trivial, ?_⟩
        apply shiftedBranchRefute_free
        · apply PeanoEvidence.prepend_free
          exact PeanoEvidence.prepend_free _ _ arithmeticFree
        · trivial
        · trivial
      · refine ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr rightFree, ?_, ?_⟩
        · apply shiftedBranchRefute_free
          · apply PeanoEvidence.prepend_free
            exact PeanoEvidence.prepend_free _ _ arithmeticFree
          · trivial
          · trivial
        · refine ⟨trivial, ?_, ?_⟩
          · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
            apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
            exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr True.intro
          · apply previous
            · apply PeanoEvidence.prepend_free
              apply PeanoEvidence.rename_free
              apply PeanoEvidence.prepend_free
              apply PeanoEvidence.rename_free
              apply PeanoEvidence.prepend_free
              exact PeanoEvidence.prepend_free _ _ arithmeticFree
            · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
              apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
              exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr True.intro
            · constructor
              · apply compileAt_slotEquality_free
                apply sumOffsetUnique_free
                · exact (PeanoEvidence.prepend_free _ _
                    (PeanoEvidence.rename_free _ _ (PeanoEvidence.prepend_free _ _
                      (PeanoEvidence.rename_free _ _ (PeanoEvidence.prepend_free _ _
                        (PeanoEvidence.prepend_free _ _ arithmeticFree)))))).2.1
                · exact (PeanoEvidence.prepend_free _ _
                    (PeanoEvidence.rename_free _ _ (PeanoEvidence.prepend_free _ _
                      (PeanoEvidence.rename_free _ _ (PeanoEvidence.prepend_free _ _
                        (PeanoEvidence.prepend_free _ _ arithmeticFree)))))).2.2
                · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
                  apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
                  exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr True.intro
                · trivial
              · trivial

#print axioms compileAt_functional_free

def graphFunctionality {assumptions : List (Formula Const Γ)}
    (plan : Plan Const Γ number index) (slot : Term Const Γ number)
    (leftTarget rightTarget : Term Const Γ index) (arithmetic : PeanoEvidence successor zero assumptions)
    (left : ProofSyntax Const assumptions (.app (.app (graph zero successor plan) slot) leftTarget))
    (right : ProofSyntax Const assumptions (.app (.app (graph zero successor plan) slot) rightTarget)) :
    ProofSyntax Const assumptions (.eq leftTarget rightTarget) :=
  compileAt_functional zero successor plan Subst.id slot leftTarget rightTarget arithmetic
    (.impE (.eqPropEL (graph_beta zero successor plan slot leftTarget)) left)
    (.impE (.eqPropEL (graph_beta zero successor plan slot rightTarget)) right)

theorem graphFunctionality_free {assumptions : List (Formula Const Γ)}
    (plan : Plan Const Γ number index) (slot : Term Const Γ number)
    (leftTarget rightTarget : Term Const Γ index) (arithmetic : PeanoEvidence successor zero assumptions)
    (left : ProofSyntax Const assumptions (.app (.app (graph zero successor plan) slot) leftTarget))
    (right : ProofSyntax Const assumptions (.app (.app (graph zero successor plan) slot) rightTarget))
    (arithmeticFree : arithmetic.Free) (leftFree : left.FunctionExtensionalityFree)
    (rightFree : right.FunctionExtensionalityFree) :
    (graphFunctionality zero successor plan slot leftTarget rightTarget arithmetic left right).FunctionExtensionalityFree := by
  apply compileAt_functional_free
  · exact arithmeticFree
  · exact ⟨graph_beta_free _ _ _ _ _, leftFree⟩
  · exact ⟨graph_beta_free _ _ _ _ _, rightFree⟩

open FiniteConstructorEncoding CurriedPredicates

def fieldGraph_functional {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (arguments : Arguments Const Γ fields)
    (slot : Term Const Γ number) (leftTarget rightTarget : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (left : ProofSyntax Const assumptions
      (applyArguments fields (.app (.app (fieldGraph zero successor fields plan) slot) leftTarget) arguments))
    (right : ProofSyntax Const assumptions
      (applyArguments fields (.app (.app (fieldGraph zero successor fields plan) slot) rightTarget) arguments)) :
    ProofSyntax Const assumptions (.eq leftTarget rightTarget) :=
  compileAt_functional zero successor (fieldTerms fields plan Subst.id arguments) Subst.id slot leftTarget rightTarget arithmetic
    (.impE (.eqPropEL (fieldGraph_beta zero successor fields plan slot leftTarget arguments)) left)
    (.impE (.eqPropEL (fieldGraph_beta zero successor fields plan slot rightTarget arguments)) right)

theorem fieldGraph_functional_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (arguments : Arguments Const Γ fields)
    (slot : Term Const Γ number) (leftTarget rightTarget : Term Const Γ index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (left : ProofSyntax Const assumptions
      (applyArguments fields (.app (.app (fieldGraph zero successor fields plan) slot) leftTarget) arguments))
    (right : ProofSyntax Const assumptions
      (applyArguments fields (.app (.app (fieldGraph zero successor fields plan) slot) rightTarget) arguments))
    (arithmeticFree : arithmetic.Free) (leftFree : left.FunctionExtensionalityFree)
    (rightFree : right.FunctionExtensionalityFree) :
    (fieldGraph_functional zero successor fields plan arguments slot leftTarget rightTarget arithmetic left right).FunctionExtensionalityFree := by
  apply compileAt_functional_free
  · exact arithmeticFree
  · exact ⟨fieldGraph_beta_free _ _ _ _ _ _ _, leftFree⟩
  · exact ⟨fieldGraph_beta_free _ _ _ _ _ _ _, rightFree⟩

#print axioms graphFunctionality_free
#print axioms fieldGraph_functional_free

end Mettapedia.Logic.HOL.OrderedPositionPrograms

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms

open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number)
    (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {assumptions : List (Formula Const Γ)}

/-- A guarded source witness fixes the index for every answer at this slot. -/
def guardedIndexComparisonFromWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (witness : ProofSyntax Const (applyArguments _ (constructors.allowed occurrence) arguments :: assumptions)
      (applyArguments _ (.app (.app (fieldGraph zero successor _ (plans occurrence)) slot) requested) arguments)) :
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
  have wanted : ProofSyntax Const hypotheses
      (applyArguments _ (.app (.app (fieldGraph zero successor _ currentPlan)
        (HOL.subst images slot)) (HOL.subst images requested)) data) := by
    have shifted := ProofSyntax.impE
      ((ProofSyntax.rename Rename.weaken (ProofSyntax.impI witness)).prepend antecedent) localAllowed
    apply ProofSyntax.castIndices rfl ?_ shifted
    rw [← subst_ofRename Rename.weaken]
    simp only [HOL.subst, applyArguments_subst, fieldGraph_substitute]
    rfl
  exact fieldGraph_functional zero successor _ currentPlan data (HOL.subst images slot) (.var .vz)
    (HOL.subst images requested) ((arithmetic.rename Rename.weaken).prepend antecedent) relation wanted

theorem guardedIndexComparisonFromWitness_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) (requested : Term Const Γ constructors.index)
    (arithmetic : PeanoEvidence successor zero assumptions)
    (witness : ProofSyntax Const (applyArguments _ (constructors.allowed occurrence) arguments :: assumptions)
      (applyArguments _ (.app (.app (fieldGraph zero successor _ (plans occurrence)) slot) requested) arguments))
    (arithmeticFree : arithmetic.Free) (witnessFree : witness.FunctionExtensionalityFree) :
    (guardedIndexComparisonFromWitness constructors zero successor plans occurrence arguments slot requested arithmetic witness).FunctionExtensionalityFree := by
  unfold guardedIndexComparisonFromWitness
  apply fieldGraph_functional_free
  · exact PeanoEvidence.prepend_free _ _ (arithmetic.rename_free Rename.weaken arithmeticFree)
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr witnessFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial

#print axioms guardedIndexComparisonFromWitness
#print axioms guardedIndexComparisonFromWitness_free

end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
