import Mettapedia.GSLT.ProofPlans.Transforms

/-!
# Least general generalization of two plans

`antiUnify` is linear: a disagreement between two plans for one goal opens a
fresh obligation at every position, even when the same pair of sub-plans
disagrees again.  Least general generalization shares one obligation across
repeated identical disagreement pairs.  Two sub-plans form one pair when their
wire erasures are equal.  Where the root rules agree, both algorithms keep
that rule.

The linear generalization instantiates to the least general one by sending
each of its obligations to the shared obligation of the same erasure pair.
Two substitutions recover the original plans.

A second generalization of a pair whose slots are already allocated opens no
further slot, and a citation weakens to the citation of the same numeral.
The minimality substitution is not proved.  It would send each obligation of a
plan that uses every obligation to the least general sub-plan of that
obligation's two instances, computed in the slot context already allocated and
then weakened to the final slot context.  The missing step is that
local-to-global transport of a replayed plan.  An obligation the plan never
cites has no such sub-plan, because it then has no derivation from the shared
context.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine

variable {definition : ValidatedCalculusLanguageDef}

/-! ## Equality of erased open proofs -/

instance : DecidableEq RuleInstance := fun first second =>
  match decEq first.ruleId second.ruleId, decEq first.arguments second.arguments with
  | isTrue sameId, isTrue sameArguments =>
      isTrue (by
        cases first
        cases second
        simp only at sameId sameArguments
        subst sameId sameArguments
        rfl)
  | isFalse differentId, _ =>
      isFalse (by
        intro same
        cases first
        cases second
        cases same
        exact differentId rfl)
  | _, isFalse differentArguments =>
      isFalse (by
        intro same
        cases first
        cases second
        cases same
        exact differentArguments rfl)

mutual

private def decEqRawOpenProof : DecidableEq RawOpenProof
  | .premise index, .premise index' =>
      if same : index = index' then isTrue (by subst same; rfl)
      else isFalse (by
        intro equal
        cases equal
        exact same rfl)
  | .premise _, .node _ _ => isFalse (by intro equal; cases equal)
  | .node _ _, .premise _ => isFalse (by intro equal; cases equal)
  | .node ruleInstance children, .node ruleInstance' children' =>
      match decEq ruleInstance ruleInstance' with
      | isFalse different => isFalse (fun equal => different (by cases equal; rfl))
      | isTrue sameInstance =>
          match decEqRawOpenProofList children children' with
          | isFalse different => isFalse (fun equal => different (by cases equal; rfl))
          | isTrue sameChildren => isTrue (by subst sameInstance; subst sameChildren; rfl)

private def decEqRawOpenProofList : DecidableEq (List RawOpenProof)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro equal; cases equal)
  | _ :: _, [] => isFalse (by intro equal; cases equal)
  | head :: tail, head' :: tail' =>
      match decEqRawOpenProof head head' with
      | isFalse different => isFalse (fun equal => different (List.cons.inj equal).1)
      | isTrue sameHead =>
          match decEqRawOpenProofList tail tail' with
          | isFalse different => isFalse (fun equal => different (List.cons.inj equal).2)
          | isTrue sameTail => isTrue (by subst sameHead; subst sameTail; rfl)

end

instance : DecidableEq RawOpenProof := decEqRawOpenProof

/-! ## Obligation contexts -/

/-- Move a derivation along a goal equality.  When the two goals are already
the same term, the comparison proof is reflexivity and the derivation is
unchanged. -/
def transportGoal {context : List Pattern} {source target : Pattern}
    (backup : source = target) (derivation : OpenDerivation definition context source) :
    OpenDerivation definition context target :=
  if equal : source = target then
    equal ▸ derivation
  else
    backup ▸ derivation

/-- Move a derivation along a context equality, in the same way. -/
def transportContext {context context' : List Pattern} {goal : Pattern}
    (backup : context = context') (derivation : OpenDerivation definition context goal) :
    OpenDerivation definition context' goal :=
  if equal : context = context' then
    equal ▸ derivation
  else
    backup ▸ derivation

/-- Move an ordered vector along a context equality. -/
def transportContextList {context context' goals : List Pattern}
    (backup : context = context')
    (derivations : OpenDerivationList definition context goals) :
    OpenDerivationList definition context' goals :=
  if equal : context = context' then
    equal ▸ derivations
  else
    backup ▸ derivations

/-- Cite an obligation whose judgment is the goal. -/
def cite {context : List Pattern} {goal : Pattern} (index : Fin context.length)
    (backup : context.get index = goal) : OpenDerivation definition context goal :=
  transportGoal backup (.assumption index)

mutual

/-- Extend the obligation context on the right.  Assumption indices still cite
the original prefix. -/
def weakenAppend {context extra : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal) :
    OpenDerivation definition (context ++ extra) goal :=
  match derivation with
  | .assumption index =>
      cite ⟨index.1, OpenDerivationList.length_left (secondGoals := extra) index⟩
        (OpenDerivationList.get_left (secondGoals := extra) index)
  | .byRule ruleInstance application children =>
      .byRule ruleInstance application (weakenAppendList (extra := extra) children)

def weakenAppendList {context extra goals : List Pattern}
    (derivations : OpenDerivationList definition context goals) :
    OpenDerivationList definition (context ++ extra) goals :=
  match derivations with
  | .nil => .nil
  | .cons head tail =>
      .cons (weakenAppend (extra := extra) head) (weakenAppendList (extra := extra) tail)

end

/-- One shared disagreement: the judgment, and the two sub-plans that disagree. -/
structure Slot (definition : ValidatedCalculusLanguageDef)
    (leftContext rightContext : List Pattern) where
  goal : Pattern
  left : OpenDerivation definition leftContext goal
  right : OpenDerivation definition rightContext goal

/-- The two sub-plans are the same disagreement when their erasures agree. -/
def Slot.matches {leftContext rightContext : List Pattern} {goal : Pattern}
    (slot : Slot definition leftContext rightContext)
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) : Bool :=
  decide (slot.left.eraseOpen = left.eraseOpen ∧ slot.right.eraseOpen = right.eraseOpen)

abbrev obligationsOf {leftContext rightContext : List Pattern}
    (slots : List (Slot definition leftContext rightContext)) : List Pattern :=
  slots.map Slot.goal

def slotLefts {leftContext rightContext : List Pattern} :
    (slots : List (Slot definition leftContext rightContext)) →
      OpenDerivationList definition leftContext (obligationsOf slots)
  | [] => .nil
  | slot :: slots => .cons slot.left (slotLefts slots)

def slotRights {leftContext rightContext : List Pattern} :
    (slots : List (Slot definition leftContext rightContext)) →
      OpenDerivationList definition rightContext (obligationsOf slots)
  | [] => .nil
  | slot :: slots => .cons slot.right (slotRights slots)

theorem obligations_append_nil {leftContext rightContext : List Pattern}
    (seen : List (Slot definition leftContext rightContext)) :
    obligationsOf seen = obligationsOf (seen ++ []) := by
  unfold obligationsOf
  simp only [List.append_nil]

theorem obligations_append {leftContext rightContext : List Pattern}
    (base extra : List (Slot definition leftContext rightContext)) :
    obligationsOf base ++ obligationsOf extra = obligationsOf (base ++ extra) := by
  unfold obligationsOf
  simp only [List.map_append]

theorem obligations_assoc {leftContext rightContext : List Pattern}
    (first second third : List (Slot definition leftContext rightContext)) :
    obligationsOf ((first ++ second) ++ third) =
      obligationsOf (first ++ (second ++ third)) := by
  unfold obligationsOf
  simp only [List.append_assoc]

def weakenSlots {leftContext rightContext : List Pattern}
    {base extra : List (Slot definition leftContext rightContext)} {goal : Pattern}
    (derivation : OpenDerivation definition (obligationsOf base) goal) :
    OpenDerivation definition (obligationsOf (base ++ extra)) goal :=
  transportContext (obligations_append base extra)
    (weakenAppend (extra := obligationsOf extra) derivation)

def weakenSlotsList {leftContext rightContext : List Pattern}
    {base extra : List (Slot definition leftContext rightContext)} {goals : List Pattern}
    (derivations : OpenDerivationList definition (obligationsOf base) goals) :
    OpenDerivationList definition (obligationsOf (base ++ extra)) goals :=
  transportContextList (obligations_append base extra)
    (weakenAppendList (extra := obligationsOf extra) derivations)

/-- A least-general step relative to slots already allocated. -/
structure LeastStep {leftContext rightContext : List Pattern}
    (seen : List (Slot definition leftContext rightContext)) (goal : Pattern) where
  added : List (Slot definition leftContext rightContext)
  plan : OpenDerivation definition (obligationsOf (seen ++ added)) goal

/-- A least-general step for an ordered vector of sub-plans. -/
structure LeastStepList {leftContext rightContext : List Pattern}
    (seen : List (Slot definition leftContext rightContext)) (goals : List Pattern) where
  added : List (Slot definition leftContext rightContext)
  plans : OpenDerivationList definition (obligationsOf (seen ++ added)) goals

variable {leftContext rightContext : List Pattern}

/-- The obligation-list position of a slot already stored at `index`. -/
def obligationIndex (seen : List (Slot definition leftContext rightContext))
    (index : Fin seen.length) : Fin (obligationsOf seen).length :=
  ⟨index.val, by
    unfold obligationsOf
    rw [List.length_map]
    exact index.isLt⟩

/-- The judgment at that position is the stored slot's judgment. -/
theorem slotGoal_get (seen : List (Slot definition leftContext rightContext))
    (index : Fin seen.length) :
    (obligationsOf seen).get (obligationIndex seen index) = (seen.get index).goal := by
  unfold obligationsOf obligationIndex
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]

/-- Position of a slot appended after `seen`. -/
def appendedIndex (seen : List (Slot definition leftContext rightContext))
    (slot : Slot definition leftContext rightContext) :
    Fin (obligationsOf (seen ++ [slot])).length :=
  ⟨seen.length, by
    unfold obligationsOf
    rw [List.length_map, List.length_append, List.length_singleton]
    omega⟩

/-- The appended slot's judgment sits at that position. -/
theorem appendedGoal (seen : List (Slot definition leftContext rightContext))
    (slot : Slot definition leftContext rightContext) :
    (obligationsOf (seen ++ [slot])).get (appendedIndex seen slot) = slot.goal := by
  unfold obligationsOf appendedIndex
  rw [List.get_eq_getElem, List.getElem_map,
    List.getElem_append_right (h₁ := Nat.le_refl seen.length)]
  simp only [Nat.sub_self]
  rfl

/-- Cite the stored slot of an identical erasure pair. -/
def reusePlan {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal)
    (found : seen.findIdx (fun slot => slot.matches left right) < seen.length) :
    OpenDerivation definition (obligationsOf (seen ++ [])) goal :=
  let index : Fin seen.length :=
    ⟨seen.findIdx (fun slot => slot.matches left right), found⟩
  let slot := seen.get index
  have matched : slot.matches left right = true :=
    List.findIdx_getElem (xs := seen)
      (p := fun slot => slot.matches left right) (w := found)
  have erased :
      slot.left.eraseOpen = left.eraseOpen ∧ slot.right.eraseOpen = right.eraseOpen :=
    of_decide_eq_true matched
  have sameGoal : slot.goal = goal :=
    (eraseOpen_determines slot.left left erased.1).1
  transportContext (obligations_append_nil seen)
    (cite (obligationIndex seen index) ((slotGoal_get seen index).trans sameGoal))

/-- Open one obligation, or reuse the obligation of an identical erasure pair. -/
def share {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) : LeastStep seen goal :=
  if found : seen.findIdx (fun slot => slot.matches left right) < seen.length then
    { added := [], plan := reusePlan seen left right found }
  else
    let slot : Slot definition leftContext rightContext := ⟨goal, left, right⟩
    { added := [slot]
      plan := cite (appendedIndex seen slot) (appendedGoal seen slot) }

mutual

/-- **Least general generalization** of two plans for one goal, given the
disagreement pairs already allocated. -/
def leastStep {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) → LeastStep seen goal
  | seen, left@(.assumption _), right => share seen left right
  | seen, left@(.byRule _ _ _), right@(.assumption _) =>
      share seen left right
  | seen, left@(.byRule (premises := premises) ruleInstance application children),
      right@(.byRule (premises := premises') _ruleInstance' _application' children') =>
      if same : ruleInstance.ruleId = _ruleInstance'.ruleId ∧
          ruleInstance.arguments = _ruleInstance'.arguments ∧ premises = premises' then
        let descended := leastStepList seen children (same.2.2 ▸ children')
        { added := descended.added
          plan := .byRule ruleInstance application descended.plans }
      else
        share seen left right

/-- Least general generalization of two ordered vectors. -/
def leastStepList {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) → LeastStepList seen goals
  | _, .nil, _ => { added := [], plans := .nil }
  | seen, .cons head tail, .cons head' tail' =>
      let first := leastStep seen head head'
      let rest := leastStepList (seen ++ first.added) tail tail'
      { added := first.added ++ rest.added
        plans := .cons
          (transportContext (obligations_assoc seen first.added rest.added)
            (weakenSlots (base := seen ++ first.added) (extra := rest.added) first.plan))
          (transportContextList (obligations_assoc seen first.added rest.added) rest.plans) }

end

/-- **Least general generalization** of two plans for one goal. -/
def leastGeneral {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    Generalization definition leftContext rightContext goal :=
  let generalized := leastStep [] left right
  { obligations := obligationsOf generalized.added
    plan := generalized.plan
    left := slotLefts generalized.added
    right := slotRights generalized.added }

/-- Every obligation of `plan` occurs at least once. -/
def UsesAll {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation definition context goal) : Prop :=
  ∀ index : Fin context.length, index ∈ holeOccurrences plan

theorem transportGoal_id {context : List Pattern} {goal : Pattern}
    (backup : goal = goal) (derivation : OpenDerivation definition context goal) :
    transportGoal backup derivation = derivation := by
  unfold transportGoal
  rw [dif_pos backup]

theorem transportGoal_bind {context target : List Pattern} {source goal : Pattern}
    (backup : source = goal) (derivation : OpenDerivation definition context source)
    (environment : OpenDerivationList definition target context) :
    (transportGoal backup derivation).bind environment =
      transportGoal backup (derivation.bind environment) := by
  unfold transportGoal
  cases decEq source goal with
  | isTrue equal =>
      simp only [dif_pos equal, OpenDerivationList.cast_bind]
  | isFalse different =>
      exact absurd backup different

theorem cite_bind {context target : List Pattern} {goal : Pattern}
    (index : Fin context.length) (backup : context.get index = goal)
    (environment : OpenDerivationList definition target context) :
    (cite index backup).bind environment =
      transportGoal backup (environment.get index) := by
  simp only [cite, transportGoal_bind, OpenDerivation.assumption_bind]

theorem transportGoal_cast_symm {context : List Pattern} {source goal : Pattern}
    (backup : source = goal) (derivation : OpenDerivation definition context goal) :
    transportGoal backup (backup.symm ▸ derivation) = derivation := by
  cases backup
  exact transportGoal_id rfl derivation

theorem transportGoal_proof_irrel {context : List Pattern} {source goal : Pattern}
    (first second : source = goal) (derivation : OpenDerivation definition context source) :
    transportGoal first derivation = transportGoal second derivation := by
  cases first
  cases second
  unfold transportGoal
  rfl

/-- The derivation stored for an appended slot is that slot's left sub-plan. -/
theorem slotLefts_appended (seen : List (Slot definition leftContext rightContext))
    (slot : Slot definition leftContext rightContext) :
    transportGoal (appendedGoal seen slot)
        ((slotLefts (seen ++ [slot])).get (appendedIndex seen slot)) =
      slot.left := by
  induction seen with
  | nil =>
      simp only [List.nil_append, slotLefts, appendedIndex, OpenDerivationList.get]
      exact transportGoal_id (appendedGoal [] slot) slot.left
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, slotLefts, OpenDerivationList.get]
      rw [transportGoal_proof_irrel
        (appendedGoal (head :: tail) slot) (appendedGoal tail slot)]
      exact inductionHypothesis

/-- The derivation stored for an appended slot is that slot's right sub-plan. -/
theorem slotRights_appended (seen : List (Slot definition leftContext rightContext))
    (slot : Slot definition leftContext rightContext) :
    transportGoal (appendedGoal seen slot)
        ((slotRights (seen ++ [slot])).get (appendedIndex seen slot)) =
      slot.right := by
  induction seen with
  | nil =>
      simp only [List.nil_append, slotRights, appendedIndex, OpenDerivationList.get]
      exact transportGoal_id (appendedGoal [] slot) slot.right
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, slotRights, OpenDerivationList.get]
      rw [transportGoal_proof_irrel
        (appendedGoal (head :: tail) slot) (appendedGoal tail slot)]
      exact inductionHypothesis

/-! ## Casts along obligation equalities -/

theorem transportGoal_trans {context : List Pattern} {first second third : Pattern}
    (toSecond : first = second) (toThird : second = third)
    (derivation : OpenDerivation definition context first) :
    transportGoal (toSecond.trans toThird) derivation =
      transportGoal toThird (transportGoal toSecond derivation) := by
  cases toSecond
  cases toThird
  rw [transportGoal_id rfl, transportGoal_id rfl]

theorem transportGoal_of_erasure {context : List Pattern} {storedGoal goal : Pattern}
    (stored : OpenDerivation definition context storedGoal)
    (original : OpenDerivation definition context goal)
    (erased : stored.eraseOpen = original.eraseOpen) :
    transportGoal (eraseOpen_determines stored original erased).1 stored = original := by
  obtain ⟨sameGoal, sameDerivation⟩ := eraseOpen_determines stored original erased
  cases sameGoal
  rw [transportGoal_id]
  exact eq_of_heq sameDerivation

theorem transportContext_cast {source target : List Pattern} {goal : Pattern}
    (backup : source = target) (derivation : OpenDerivation definition source goal) :
    transportContext backup derivation = backup ▸ derivation := by
  unfold transportContext
  cases decEq source target with
  | isTrue equal =>
      simp only [dif_pos equal]
  | isFalse different =>
      exact absurd backup different

theorem transportContextList_cast {source target goals : List Pattern}
    (backup : source = target)
    (derivations : OpenDerivationList definition source goals) :
    transportContextList backup derivations = backup ▸ derivations := by
  unfold transportContextList
  cases decEq source target with
  | isTrue equal =>
      simp only [dif_pos equal]
  | isFalse different =>
      exact absurd backup different

theorem cast_context_bind {source target outer : List Pattern} {goal : Pattern}
    (equal : source = target) (derivation : OpenDerivation definition source goal)
    (environment : OpenDerivationList definition outer source) :
    (equal ▸ derivation).bind (equal ▸ environment) = derivation.bind environment := by
  cases equal
  rfl

theorem cast_contextList_bind {source target outer goals : List Pattern}
    (equal : source = target) (plans : OpenDerivationList definition source goals)
    (environment : OpenDerivationList definition outer source) :
    (equal ▸ plans).bind (equal ▸ environment) = plans.bind environment := by
  cases equal
  rfl

theorem slotLefts_heq {xs ys : List (Slot definition leftContext rightContext)}
    (equal : xs = ys) :
    slotLefts xs = (congrArg obligationsOf equal).symm ▸ slotLefts ys := by
  cases equal
  rfl

theorem slotRights_heq {xs ys : List (Slot definition leftContext rightContext)}
    (equal : xs = ys) :
    slotRights xs = (congrArg obligationsOf equal).symm ▸ slotRights ys := by
  cases equal
  rfl

theorem slotLefts_append_nil (seen : List (Slot definition leftContext rightContext)) :
    slotLefts (seen ++ []) = (obligations_append_nil seen) ▸ slotLefts seen :=
  slotLefts_heq (List.append_nil seen)

theorem slotRights_append_nil (seen : List (Slot definition leftContext rightContext)) :
    slotRights (seen ++ []) = (obligations_append_nil seen) ▸ slotRights seen :=
  slotRights_heq (List.append_nil seen)

theorem derivationList_cons_cast {context : List Pattern} {goal : Pattern}
    {goals goals' : List Pattern} (equal : goals = goals')
    (head : OpenDerivation definition context goal)
    (tail : OpenDerivationList definition context goals) :
    OpenDerivationList.cons head (equal ▸ tail) =
      congrArg (List.cons goal) equal ▸ OpenDerivationList.cons head tail := by
  cases equal
  rfl

theorem slotLefts_append (base extra : List (Slot definition leftContext rightContext)) :
    slotLefts (base ++ extra) =
      (obligations_append base extra) ▸ ((slotLefts base).append (slotLefts extra)) := by
  induction base with
  | nil =>
      simp only [List.nil_append, slotLefts, OpenDerivationList.nil_append]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, slotLefts, OpenDerivationList.cons_append]
      rw [inductionHypothesis, derivationList_cons_cast]

theorem slotRights_append (base extra : List (Slot definition leftContext rightContext)) :
    slotRights (base ++ extra) =
      (obligations_append base extra) ▸ ((slotRights base).append (slotRights extra)) := by
  induction base with
  | nil =>
      simp only [List.nil_append, slotRights, OpenDerivationList.nil_append]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, slotRights, OpenDerivationList.cons_append]
      rw [inductionHypothesis, derivationList_cons_cast]

theorem slotLefts_assoc (first second third : List (Slot definition leftContext rightContext)) :
    slotLefts (first ++ (second ++ third)) =
      (obligations_assoc first second third) ▸ slotLefts ((first ++ second) ++ third) := by
  induction first with
  | nil =>
      simp only [List.nil_append]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, slotLefts]
      rw [inductionHypothesis, derivationList_cons_cast]

theorem slotRights_assoc (first second third : List (Slot definition leftContext rightContext)) :
    slotRights (first ++ (second ++ third)) =
      (obligations_assoc first second third) ▸ slotRights ((first ++ second) ++ third) := by
  induction first with
  | nil =>
      simp only [List.nil_append]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, slotRights]
      rw [inductionHypothesis, derivationList_cons_cast]

theorem slotLefts_at (seen : List (Slot definition leftContext rightContext))
    (index : Fin seen.length) :
    transportGoal (slotGoal_get seen index)
        ((slotLefts seen).get (obligationIndex seen index)) =
      (seen.get index).left := by
  induction seen with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · simp only [slotLefts, OpenDerivationList.get]
        exact transportGoal_id (slotGoal_get (head :: tail) 0) head.left
      · intro tailIndex
        simp only [slotLefts, OpenDerivationList.get]
        rw [transportGoal_proof_irrel
          (slotGoal_get (head :: tail) tailIndex.succ) (slotGoal_get tail tailIndex)]
        exact inductionHypothesis tailIndex

theorem slotRights_at (seen : List (Slot definition leftContext rightContext))
    (index : Fin seen.length) :
    transportGoal (slotGoal_get seen index)
        ((slotRights seen).get (obligationIndex seen index)) =
      (seen.get index).right := by
  induction seen with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · simp only [slotRights, OpenDerivationList.get]
        exact transportGoal_id (slotGoal_get (head :: tail) 0) head.right
      · intro tailIndex
        simp only [slotRights, OpenDerivationList.get]
        rw [transportGoal_proof_irrel
          (slotGoal_get (head :: tail) tailIndex.succ) (slotGoal_get tail tailIndex)]
        exact inductionHypothesis tailIndex

theorem weakenAssumption_bind {context extra outer : List Pattern}
    (index : Fin context.length)
    (environment : OpenDerivationList definition outer context)
    (extraEnvironment : OpenDerivationList definition outer extra) :
    (weakenAppend (extra := extra) (.assumption index)).bind
        (environment.append extraEnvironment) =
      environment.get index := by
  unfold weakenAppend
  rw [cite_bind, OpenDerivationList.append_get_left]
  exact transportGoal_cast_symm
    (OpenDerivationList.get_left (secondGoals := extra) index) (environment.get index)

mutual

theorem weakenAppend_bind {context extra outer : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal)
    (environment : OpenDerivationList definition outer context)
    (extraEnvironment : OpenDerivationList definition outer extra) :
    (weakenAppend (extra := extra) derivation).bind
        (environment.append extraEnvironment) =
      derivation.bind environment := by
  match derivation with
  | .assumption index =>
      rw [OpenDerivation.assumption_bind]
      exact weakenAssumption_bind index environment extraEnvironment
  | .byRule ruleInstance application children =>
      simp only [weakenAppend, OpenDerivation.bind]
      exact congrArg (OpenDerivation.byRule ruleInstance application)
        (weakenAppendList_bind children environment extraEnvironment)

theorem weakenAppendList_bind {context extra outer goals : List Pattern}
    (derivations : OpenDerivationList definition context goals)
    (environment : OpenDerivationList definition outer context)
    (extraEnvironment : OpenDerivationList definition outer extra) :
    (weakenAppendList (extra := extra) derivations).bind
        (environment.append extraEnvironment) =
      derivations.bind environment := by
  match derivations with
  | .nil => rfl
  | .cons head tail =>
      simp only [weakenAppendList, OpenDerivationList.bind]
      congr 1
      · exact weakenAppend_bind head environment extraEnvironment
      · exact weakenAppendList_bind tail environment extraEnvironment

end

theorem weakenSlots_left {base extra : List (Slot definition leftContext rightContext)}
    {goal : Pattern}
    (plan : OpenDerivation definition (obligationsOf base) goal) :
    (weakenSlots (base := base) (extra := extra) plan).bind (slotLefts (base ++ extra)) =
      plan.bind (slotLefts base) := by
  unfold weakenSlots
  rw [transportContext_cast, slotLefts_append, cast_context_bind, weakenAppend_bind]

theorem weakenSlots_right {base extra : List (Slot definition leftContext rightContext)}
    {goal : Pattern}
    (plan : OpenDerivation definition (obligationsOf base) goal) :
    (weakenSlots (base := base) (extra := extra) plan).bind (slotRights (base ++ extra)) =
      plan.bind (slotRights base) := by
  unfold weakenSlots
  rw [transportContext_cast, slotRights_append, cast_context_bind, weakenAppend_bind]

/-! ## The two substitutions recover the original plans -/

theorem reuse_left {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal)
    (found : seen.findIdx (fun slot => slot.matches left right) < seen.length) :
    (reusePlan seen left right found).bind (slotLefts (seen ++ [])) = left := by
  let index : Fin seen.length :=
    ⟨seen.findIdx (fun slot => slot.matches left right), found⟩
  have matched : (seen.get index).matches left right = true :=
    List.findIdx_getElem (xs := seen)
      (p := fun slot => slot.matches left right) (w := found)
  have erased :
      (seen.get index).left.eraseOpen = left.eraseOpen ∧
        (seen.get index).right.eraseOpen = right.eraseOpen :=
    of_decide_eq_true matched
  unfold reusePlan
  dsimp only
  rw [transportContext_cast, slotLefts_append_nil, cast_context_bind, cite_bind,
    transportGoal_trans (toSecond := slotGoal_get seen index), slotLefts_at]
  exact transportGoal_of_erasure (seen.get index).left left erased.1

theorem reuse_right {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal)
    (found : seen.findIdx (fun slot => slot.matches left right) < seen.length) :
    (reusePlan seen left right found).bind (slotRights (seen ++ [])) = right := by
  let index : Fin seen.length :=
    ⟨seen.findIdx (fun slot => slot.matches left right), found⟩
  have matched : (seen.get index).matches left right = true :=
    List.findIdx_getElem (xs := seen)
      (p := fun slot => slot.matches left right) (w := found)
  have erased :
      (seen.get index).left.eraseOpen = left.eraseOpen ∧
        (seen.get index).right.eraseOpen = right.eraseOpen :=
    of_decide_eq_true matched
  unfold reusePlan
  dsimp only
  rw [transportContext_cast, slotRights_append_nil, cast_context_bind, cite_bind,
    transportGoal_trans (toSecond := slotGoal_get seen index), slotRights_at]
  exact transportGoal_of_erasure (seen.get index).right right erased.2

theorem share_left {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (share seen left right).plan.bind
        (slotLefts (seen ++ (share seen left right).added)) = left := by
  unfold share
  by_cases found : seen.findIdx (fun slot => slot.matches left right) < seen.length
  · rw [dif_pos found]
    exact reuse_left seen left right found
  · rw [dif_neg found, cite_bind, slotLefts_appended]

theorem share_right {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (share seen left right).plan.bind
        (slotRights (seen ++ (share seen left right).added)) = right := by
  unfold share
  by_cases found : seen.findIdx (fun slot => slot.matches left right) < seen.length
  · rw [dif_pos found]
    exact reuse_right seen left right found
  · rw [dif_neg found, cite_bind, slotRights_appended]

theorem leastStepList_cons {goal : Pattern} {tailGoals : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    leastStepList seen (.cons head tail) (.cons head' tail') =
      let first := leastStep seen head head'
      let rest := leastStepList (seen ++ first.added) tail tail'
      { added := first.added ++ rest.added
        plans := OpenDerivationList.cons
          (transportContext (obligations_assoc seen first.added rest.added)
            (weakenSlots (base := seen ++ first.added) (extra := rest.added) first.plan))
          (transportContextList (obligations_assoc seen first.added rest.added) rest.plans) } :=
  rfl

mutual

theorem leastStep_left {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) →
    (leastStep seen left right).plan.bind
        (slotLefts (seen ++ (leastStep seen left right).added)) = left
  | seen, .assumption index, right => by
      simp only [leastStep]
      exact share_left seen (.assumption index) right
  | seen, .byRule (premises := premises) ruleInstance application children, right => by
      cases right
      case assumption index =>
        simp only [leastStep]
        exact share_left seen
          (.byRule (premises := premises) ruleInstance application children)
          (.assumption index)
      case byRule ruleInstance' premises' children' application' =>
        simp only [leastStep]
        by_cases same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
            ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises'
        · rw [dif_pos same]
          simp only [OpenDerivation.bind]
          rw [leastStepList_left seen children (same.2.2 ▸ children')]
        · rw [dif_neg same]
          exact share_left seen
            (.byRule (premises := premises) ruleInstance application children)
            (.byRule (premises := premises') ruleInstance' application' children')

theorem leastStepList_left {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) →
    (leastStepList seen left right).plans.bind
        (slotLefts (seen ++ (leastStepList seen left right).added)) = left
  | _, .nil, .nil => rfl
  | seen, .cons head tail, .cons head' tail' => by
      rw [leastStepList_cons]
      simp only [OpenDerivationList.bind]
      congr 1
      · rw [transportContext_cast, slotLefts_assoc, cast_context_bind, weakenSlots_left,
          leastStep_left]
      · rw [transportContextList_cast, slotLefts_assoc, cast_contextList_bind,
          leastStepList_left]

theorem leastStep_right {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) →
    (leastStep seen left right).plan.bind
        (slotRights (seen ++ (leastStep seen left right).added)) = right
  | seen, .assumption index, right => by
      simp only [leastStep]
      exact share_right seen (.assumption index) right
  | seen, .byRule (premises := premises) ruleInstance application children, right => by
      cases right
      case assumption index =>
        simp only [leastStep]
        exact share_right seen
          (.byRule (premises := premises) ruleInstance application children)
          (.assumption index)
      case byRule ruleInstance' premises' children' application' =>
        simp only [leastStep]
        by_cases same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
            ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises'
        · rw [dif_pos same]
          simp only [OpenDerivation.bind]
          obtain ⟨sameId, sameArguments, samePremises⟩ := same
          have sameInstance := ruleInstance_ext sameId sameArguments
          subst sameInstance
          subst samePremises
          rw [leastStepList_right seen children children']
        · rw [dif_neg same]
          exact share_right seen
            (.byRule (premises := premises) ruleInstance application children)
            (.byRule (premises := premises') ruleInstance' application' children')

theorem leastStepList_right {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) →
    (leastStepList seen left right).plans.bind
        (slotRights (seen ++ (leastStepList seen left right).added)) = right
  | _, .nil, .nil => rfl
  | seen, .cons head tail, .cons head' tail' => by
      rw [leastStepList_cons]
      simp only [OpenDerivationList.bind]
      congr 1
      · rw [transportContext_cast, slotRights_assoc, cast_context_bind, weakenSlots_right,
          leastStep_right]
      · rw [transportContextList_cast, slotRights_assoc, cast_contextList_bind,
          leastStepList_right]

end

/-- **The left substitution recovers the left plan.** -/
theorem leastGeneral_left {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (leastGeneral left right).plan.bind (leastGeneral left right).left = left :=
  leastStep_left [] left right

/-- **The right substitution recovers the right plan.** -/
theorem leastGeneral_right {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (leastGeneral left right).plan.bind (leastGeneral left right).right = right :=
  leastStep_right [] left right

/-! ## Identifying the linear slots -/

theorem bind_singleton {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation definition context goal) :
    (OpenDerivation.assumption (⟨0, Nat.zero_lt_succ 0⟩ : Fin [goal].length)).bind
        (OpenDerivationList.cons plan .nil) = plan :=
  rfl

theorem bind_cast_environment {source target goals : List Pattern} {goal : Pattern}
    (equal : source = target) (plan : OpenDerivation definition goals goal)
    (environment : OpenDerivationList definition source goals) :
    plan.bind (equal ▸ environment) = equal ▸ (plan.bind environment) := by
  cases equal
  rfl

theorem bindList_cast_environment {source target goals outer : List Pattern}
    (equal : source = target) (plans : OpenDerivationList definition goals outer)
    (environment : OpenDerivationList definition source goals) :
    plans.bind (equal ▸ environment) = equal ▸ (plans.bind environment) := by
  cases equal
  rfl

theorem weakenAppendList_get {context extra : List Pattern} :
    {goals : List Pattern} → (derivations : OpenDerivationList definition context goals) →
      (index : Fin goals.length) →
        (weakenAppendList (extra := extra) derivations).get index =
          weakenAppend (extra := extra) (derivations.get index)
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons _ tail, index => by
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro tailIndex
        simp only [weakenAppendList, OpenDerivationList.get]
        exact weakenAppendList_get tail tailIndex

mutual

theorem bind_weakenEnvironment {context extra goals : List Pattern} {goal : Pattern}
    (plan : OpenDerivation definition goals goal)
    (environment : OpenDerivationList definition context goals) :
    plan.bind (weakenAppendList (extra := extra) environment) =
      weakenAppend (extra := extra) (plan.bind environment) := by
  match plan with
  | .assumption index =>
      rw [OpenDerivation.assumption_bind, OpenDerivation.assumption_bind, weakenAppendList_get]
  | .byRule ruleInstance application children =>
      simp only [OpenDerivation.bind, weakenAppend]
      exact congrArg (OpenDerivation.byRule ruleInstance application)
        (bindList_weakenEnvironment children environment)

theorem bindList_weakenEnvironment {context extra goals outer : List Pattern}
    (plans : OpenDerivationList definition goals outer)
    (environment : OpenDerivationList definition context goals) :
    plans.bind (weakenAppendList (extra := extra) environment) =
      weakenAppendList (extra := extra) (plans.bind environment) := by
  match plans with
  | .nil => rfl
  | .cons head tail =>
      simp only [OpenDerivationList.bind, weakenAppendList]
      congr 1
      · exact bind_weakenEnvironment head environment
      · exact bindList_weakenEnvironment tail environment

end

theorem bind_transportContext {source target goals : List Pattern} {goal : Pattern}
    (equal : source = target) (plan : OpenDerivation definition goals goal)
    (environment : OpenDerivationList definition source goals) :
    plan.bind (transportContextList equal environment) =
      transportContext equal (plan.bind environment) := by
  rw [transportContextList_cast, bind_cast_environment, transportContext_cast]

theorem bindList_transportContext {source target goals outer : List Pattern}
    (equal : source = target) (plans : OpenDerivationList definition goals outer)
    (environment : OpenDerivationList definition source goals) :
    plans.bind (transportContextList equal environment) =
      transportContextList equal (plans.bind environment) := by
  rw [transportContextList_cast, bindList_cast_environment, transportContextList_cast]

theorem bind_weakenSlotsList
    {base extra : List (Slot definition leftContext rightContext)}
    {goals : List Pattern} {goal : Pattern}
    (plan : OpenDerivation definition goals goal)
    (environment : OpenDerivationList definition (obligationsOf base) goals) :
    plan.bind (weakenSlotsList (base := base) (extra := extra) environment) =
      weakenSlots (base := base) (extra := extra) (plan.bind environment) := by
  unfold weakenSlotsList weakenSlots
  rw [transportContextList_cast, bind_cast_environment, bind_weakenEnvironment,
    transportContext_cast]

/-- Where the linear obligations of one subtree land in the shared context. -/
structure Found (seen : List (Slot definition leftContext rightContext)) where
  added : List (Slot definition leftContext rightContext)
  obligations : List Pattern
  identified : OpenDerivationList definition (obligationsOf (seen ++ added)) obligations

/-- The same, for an ordered vector of sub-plans. -/
structure FoundList (seen : List (Slot definition leftContext rightContext)) where
  added : List (Slot definition leftContext rightContext)
  obligations : List Pattern
  identified : OpenDerivationList definition (obligationsOf (seen ++ added)) obligations

/-- A disagreement that does not share a root rule is one linear obligation,
sent to the least general sub-plan of that disagreement. -/
def foundFromShare {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) : Found seen :=
  let shared : LeastStep seen goal := share seen left right
  { added := shared.added
    obligations := [goal]
    identified := .cons shared.plan .nil }

mutual

/-- Send each linear obligation to the shared sub-plan of the same erasure pair. -/
def identifyStep {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) → Found seen
  | seen, left@(.assumption _), right => foundFromShare seen left right
  | seen, left@(.byRule _ _ _), right@(.assumption _) => foundFromShare seen left right
  | seen, left@(.byRule (premises := premises) ruleInstance _application children),
      right@(.byRule (premises := premises') ruleInstance' _application' children') =>
      if same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
          ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises' then
        let descended := identifyList seen children (same.2.2 ▸ children')
        { added := descended.added
          obligations := descended.obligations
          identified := descended.identified }
      else
        foundFromShare seen left right

/-- Pointwise form. The head identification is weakened by slots the tail adds,
over one shared context, and the two vectors are appended. -/
def identifyList {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) → FoundList seen
  | _, .nil, _ => { added := [], obligations := [], identified := .nil }
  | seen, .cons head tail, .cons head' tail' =>
      let first := identifyStep seen head head'
      let rest := identifyList (seen ++ first.added) tail tail'
      let headThere := transportContextList (obligations_assoc seen first.added rest.added)
        (weakenSlotsList (base := seen ++ first.added) (extra := rest.added) first.identified)
      let tailThere := transportContextList (obligations_assoc seen first.added rest.added)
        rest.identified
      { added := first.added ++ rest.added
        obligations := first.obligations ++ rest.obligations
        identified := headThere.append tailThere }

end

theorem identifyList_cons {goal : Pattern} {tailGoals : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    identifyList seen (.cons head tail) (.cons head' tail') =
      let first := identifyStep seen head head'
      let rest := identifyList (seen ++ first.added) tail tail'
      let headThere := transportContextList (obligations_assoc seen first.added rest.added)
        (weakenSlotsList (base := seen ++ first.added) (extra := rest.added) first.identified)
      let tailThere := transportContextList (obligations_assoc seen first.added rest.added)
        rest.identified
      { added := first.added ++ rest.added
        obligations := first.obligations ++ rest.obligations
        identified := headThere.append tailThere } :=
  rfl

/-- The identified vector, transported onto the least-general context and the
linear obligations. -/
def castIdentified {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal)
    (addedEq : (identifyStep seen left right).added = (leastStep seen left right).added)
    (obligationsEq :
      (identifyStep seen left right).obligations = (antiUnify left right).obligations) :
    OpenDerivationList definition
      (obligationsOf (seen ++ (leastStep seen left right).added))
      (antiUnify left right).obligations :=
  obligationsEq ▸
    congrArg (fun added => obligationsOf (seen ++ added)) addedEq ▸
      (identifyStep seen left right).identified

def castIdentifiedList {goals : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivationList definition leftContext goals)
    (right : OpenDerivationList definition rightContext goals)
    (addedEq : (identifyList seen left right).added = (leastStepList seen left right).added)
    (obligationsEq :
      (identifyList seen left right).obligations = (antiUnifyList left right).obligations) :
    OpenDerivationList definition
      (obligationsOf (seen ++ (leastStepList seen left right).added))
      (antiUnifyList left right).obligations :=
  obligationsEq ▸
    congrArg (fun added => obligationsOf (seen ++ added)) addedEq ▸
      (identifyList seen left right).identified

mutual

theorem identifyStep_added {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) →
    (identifyStep seen left right).added = (leastStep seen left right).added
  | seen, .assumption _, right => by
      simp only [identifyStep, leastStep, foundFromShare]
  | seen, .byRule _ _ _, .assumption _ => by
      simp only [identifyStep, leastStep, foundFromShare]
  | seen, .byRule (premises := premises) ruleInstance _application children,
      .byRule (premises := premises') ruleInstance' _application' children' => by
      simp only [identifyStep, leastStep]
      by_cases same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
          ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises'
      · rw [dif_pos same, dif_pos same]
        exact identifyList_added seen children (same.2.2 ▸ children')
      · rw [dif_neg same, dif_neg same]
        simp only [foundFromShare]

theorem identifyList_added {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) →
    (identifyList seen left right).added = (leastStepList seen left right).added
  | _, .nil, .nil => rfl
  | seen, .cons head tail, .cons head' tail' => by
      change (identifyStep seen head head').added ++
          (identifyList (seen ++ (identifyStep seen head head').added) tail tail').added =
        (leastStep seen head head').added ++
          (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added
      congr 1
      · exact identifyStep_added seen head head'
      · rw [identifyStep_added seen head head']
        exact identifyList_added (seen ++ (leastStep seen head head').added) tail tail'

theorem identifyStep_obligations {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) →
    (identifyStep seen left right).obligations = (antiUnify left right).obligations
  | _, .assumption _, _ => by
      simp only [identifyStep, foundFromShare, antiUnify, slot]
  | _, .byRule _ _ _, .assumption _ => by
      simp only [identifyStep, foundFromShare, antiUnify, rootRule?, slot]
  | seen, .byRule (premises := premises) ruleInstance _application children,
      .byRule (premises := premises') ruleInstance' _application' children' => by
      simp only [identifyStep, antiUnify, rootRule?]
      by_cases same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
          ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises'
      · rw [dif_pos same, dif_pos same]
        exact identifyList_obligations seen children (same.2.2 ▸ children')
      · rw [dif_neg same, dif_neg same]
        simp only [foundFromShare, slot]

theorem identifyList_obligations {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) →
    (identifyList seen left right).obligations = (antiUnifyList left right).obligations
  | _, .nil, .nil => rfl
  | seen, .cons head tail, .cons head' tail' => by
      change (identifyStep seen head head').obligations ++
          (identifyList (seen ++ (identifyStep seen head head').added) tail tail').obligations =
        (antiUnify head head').obligations ++ (antiUnifyList tail tail').obligations
      congr 1
      · exact identifyStep_obligations seen head head'
      · exact identifyList_obligations (seen ++ (identifyStep seen head head').added) tail tail'

end

/-- The obligation list of a decidable branch, on the chosen side. -/
theorem generalization_obligations_pos {goal : Pattern} {c : Prop} [d : Decidable c]
    (h : c) (t : c → Generalization definition leftContext rightContext goal)
    (e : ¬ c → Generalization definition leftContext rightContext goal) :
    (dite c t e).obligations = (t h).obligations := by
  match d with
  | isTrue _ => rfl
  | isFalse hc => exact absurd h hc

theorem generalization_obligations_neg {goal : Pattern} {c : Prop} [d : Decidable c]
    (h : ¬ c) (t : c → Generalization definition leftContext rightContext goal)
    (e : ¬ c → Generalization definition leftContext rightContext goal) :
    (dite c t e).obligations = (e h).obligations := by
  match d with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

/-- The plan of a decidable branch, transported back onto the branched context. -/
theorem generalization_plan_pos {goal : Pattern} {c : Prop} [d : Decidable c]
    (h : c) (t : c → Generalization definition leftContext rightContext goal)
    (e : ¬ c → Generalization definition leftContext rightContext goal) :
    (dite c t e).plan =
      (generalization_obligations_pos h t e).symm ▸ ((t h).plan) := by
  match d with
  | isTrue _ => rfl
  | isFalse hc => exact absurd h hc

theorem generalization_plan_neg {goal : Pattern} {c : Prop} [d : Decidable c]
    (h : ¬ c) (t : c → Generalization definition leftContext rightContext goal)
    (e : ¬ c → Generalization definition leftContext rightContext goal) :
    (dite c t e).plan =
      (generalization_obligations_neg h t e).symm ▸ ((e h).plan) := by
  match d with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

theorem least_added_pos {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : c) (t : c → LeastStep seen goal) (e : ¬ c → LeastStep seen goal) :
    (dite c t e).added = (t h).added := by
  match d with
  | isTrue _ => rfl
  | isFalse hc => exact absurd h hc

theorem least_added_neg {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : ¬ c) (t : c → LeastStep seen goal) (e : ¬ c → LeastStep seen goal) :
    (dite c t e).added = (e h).added := by
  match d with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

theorem least_plan_pos {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : c) (t : c → LeastStep seen goal) (e : ¬ c → LeastStep seen goal) :
    (dite c t e).plan =
      (congrArg (fun added => obligationsOf (seen ++ added)) (least_added_pos seen h t e)).symm ▸
        ((t h).plan) := by
  match d with
  | isTrue _ => rfl
  | isFalse hc => exact absurd h hc

theorem least_plan_neg {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : ¬ c) (t : c → LeastStep seen goal) (e : ¬ c → LeastStep seen goal) :
    (dite c t e).plan =
      (congrArg (fun added => obligationsOf (seen ++ added)) (least_added_neg seen h t e)).symm ▸
        ((e h).plan) := by
  match d with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

theorem antiUnifyList_plans_cons {goal : Pattern} {tailGoals : List Pattern}
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    (antiUnifyList (.cons head tail) (.cons head' tail')).plans =
      .cons
        ((antiUnify head head').plan.bind
          (OpenDerivationList.leftProjection (antiUnify head head').obligations
            (antiUnifyList tail tail').obligations))
        ((antiUnifyList tail tail').plans.bind
          (OpenDerivationList.rightProjection (antiUnify head head').obligations
            (antiUnifyList tail tail').obligations)) :=
  rfl

theorem bind_symm_cast {source target result : List Pattern} {goal : Pattern}
    (equal : source = target) (plan : OpenDerivation definition target goal)
    (environment : OpenDerivationList definition result source) :
    (equal.symm ▸ plan).bind environment = plan.bind (equal ▸ environment) := by
  cases equal
  rfl

theorem goals_cast_cancel {source target result : List Pattern}
    (equal : source = target)
    (environment : OpenDerivationList definition result target) :
    equal ▸ (equal.symm ▸ environment) = environment := by
  cases equal
  rfl

theorem byRule_transport {source target premises : List Pattern} {conclusion : Pattern}
    (equal : source = target) (ruleInstance : RuleInstance)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (children : OpenDerivationList definition source premises) :
    (equal ▸ (.byRule ruleInstance application children :
        OpenDerivation definition source conclusion)) =
      .byRule ruleInstance application (equal ▸ children) := by
  cases equal
  rfl

theorem bind_singleton_context {context context' : List Pattern} {goal : Pattern}
    (equal : context = context') (plan : OpenDerivation definition context goal) :
    (OpenDerivation.assumption (⟨0, Nat.zero_lt_succ 0⟩ : Fin [goal].length)).bind
        (equal ▸ OpenDerivationList.cons plan .nil) =
      equal ▸ plan := by
  cases equal
  exact bind_singleton plan

theorem bindList_context_cast {source target goals result : List Pattern}
    (equal : source = target)
    (plans : OpenDerivationList definition source goals)
    (environment : OpenDerivationList definition result target) :
    (equal ▸ plans).bind environment =
      plans.bind (equal.symm ▸ environment) := by
  cases equal
  rfl

theorem cons_context_cast {source target : List Pattern} {premise : Pattern}
    {premises : List Pattern} (equal : source = target)
    (head : OpenDerivation definition source premise)
    (tail : OpenDerivationList definition source premises) :
    (equal ▸ (OpenDerivationList.cons head tail :
        OpenDerivationList definition source (premise :: premises))) =
      .cons (equal ▸ head) (equal ▸ tail) := by
  cases equal
  rfl

/-- The two cast orders on a context and a goal vector agree. -/
theorem identified_cast_square {cL cS cM cR gL gS gA gR : List Pattern}
    (idAddedSymm : cL = cS) (idOblSymm : gL = gS)
    (stepAdded : cS = cM) (stepObl : gS = gA)
    (listAdded : cL = cR) (listObl : gL = gR)
    (leastAddedSymm : cR = cM) (antiOblSymm : gR = gA)
    (listId : OpenDerivationList definition cL gL) :
    stepObl ▸ (stepAdded ▸ (idAddedSymm ▸ (idOblSymm ▸ listId))) =
      antiOblSymm ▸ (leastAddedSymm ▸ (listObl ▸ (listAdded ▸ listId))) := by
  cases idAddedSymm
  cases idOblSymm
  cases stepAdded
  cases stepObl
  cases listAdded
  cases listObl
  cases leastAddedSymm
  cases antiOblSymm
  rfl

theorem found_added_pos
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : c) (t : c → Found seen) (e : ¬ c → Found seen) :
    (dite c t e).added = (t h).added := by
  match d with
  | isTrue _ => rfl
  | isFalse hc => exact absurd h hc

theorem found_added_neg
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : ¬ c) (t : c → Found seen) (e : ¬ c → Found seen) :
    (dite c t e).added = (e h).added := by
  match d with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

theorem found_obligations_pos {c : Prop} [d : Decidable c]
    (seen : List (Slot definition leftContext rightContext))
    (h : c) (t : c → Found seen) (e : ¬ c → Found seen) :
    (dite c t e).obligations = (t h).obligations := by
  match d with
  | isTrue _ => rfl
  | isFalse hc => exact absurd h hc

theorem found_obligations_neg {c : Prop} [d : Decidable c]
    (seen : List (Slot definition leftContext rightContext))
    (h : ¬ c) (t : c → Found seen) (e : ¬ c → Found seen) :
    (dite c t e).obligations = (e h).obligations := by
  match d with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

theorem found_identified_pos
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : c) (t : c → Found seen) (e : ¬ c → Found seen) :
    (dite c t e).identified =
      (congrArg (fun added => obligationsOf (seen ++ added)) (found_added_pos seen h t e)).symm ▸
        ((found_obligations_pos seen h t e).symm ▸ ((t h).identified)) := by
  match d with
  | isTrue _ => rfl
  | isFalse hc => exact absurd h hc

theorem found_identified_neg
    (seen : List (Slot definition leftContext rightContext)) {c : Prop} [d : Decidable c]
    (h : ¬ c) (t : c → Found seen) (e : ¬ c → Found seen) :
    (dite c t e).identified =
      (congrArg (fun added => obligationsOf (seen ++ added)) (found_added_neg seen h t e)).symm ▸
        ((found_obligations_neg seen h t e).symm ▸ ((e h).identified)) := by
  match d with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

theorem antiUnify_obligations_match {goal : Pattern} {premises premises' : List Pattern}
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    (antiUnify (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).obligations =
      (antiUnifyList children (same.2.2 ▸ children')).obligations := by
  simp only [antiUnify, rootRule?]
  exact generalization_obligations_pos same
    (fun h =>
      { obligations := (antiUnifyList children (h.2.2 ▸ children')).obligations
        plan := .byRule ruleInstance application
          (antiUnifyList children (h.2.2 ▸ children')).plans
        left := (antiUnifyList children (h.2.2 ▸ children')).left
        right := (antiUnifyList children (h.2.2 ▸ children')).right })
    (fun _ => slot (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem antiUnify_plan_match {goal : Pattern} {premises premises' : List Pattern}
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    (antiUnify (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).plan =
      (antiUnify_obligations_match application application' children children' same).symm ▸
        (.byRule ruleInstance application
          (antiUnifyList children (same.2.2 ▸ children')).plans) := by
  simp only [antiUnify, rootRule?]
  exact generalization_plan_pos same
    (fun h =>
      { obligations := (antiUnifyList children (h.2.2 ▸ children')).obligations
        plan := .byRule ruleInstance application
          (antiUnifyList children (h.2.2 ▸ children')).plans
        left := (antiUnifyList children (h.2.2 ▸ children')).left
        right := (antiUnifyList children (h.2.2 ▸ children')).right })
    (fun _ => slot (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem antiUnify_obligations_mismatch {goal : Pattern} {premises premises' : List Pattern}
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    (antiUnify (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).obligations =
      [goal] := by
  simp only [antiUnify, rootRule?, slot]
  exact generalization_obligations_neg diff
    (fun h =>
      { obligations := (antiUnifyList children (h.2.2 ▸ children')).obligations
        plan := .byRule ruleInstance application
          (antiUnifyList children (h.2.2 ▸ children')).plans
        left := (antiUnifyList children (h.2.2 ▸ children')).left
        right := (antiUnifyList children (h.2.2 ▸ children')).right })
    (fun _ => slot (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem antiUnify_plan_mismatch {goal : Pattern} {premises premises' : List Pattern}
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    (antiUnify (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).plan =
      (antiUnify_obligations_mismatch application application' children children' diff).symm ▸
        (.assumption (⟨0, Nat.zero_lt_succ 0⟩ : Fin [goal].length)) := by
  simp only [antiUnify, rootRule?, slot]
  exact generalization_plan_neg diff
    (fun h =>
      { obligations := (antiUnifyList children (h.2.2 ▸ children')).obligations
        plan := .byRule ruleInstance application
          (antiUnifyList children (h.2.2 ▸ children')).plans
        left := (antiUnifyList children (h.2.2 ▸ children')).left
        right := (antiUnifyList children (h.2.2 ▸ children')).right })
    (fun _ => slot (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem least_added_match {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    (leastStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).added =
      (leastStepList seen children (same.2.2 ▸ children')).added := by
  simp only [leastStep]
  exact least_added_pos seen same
    (fun h =>
      { added := (leastStepList seen children (h.2.2 ▸ children')).added
        plan := .byRule ruleInstance application
          (leastStepList seen children (h.2.2 ▸ children')).plans })
    (fun _ => share seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem least_plan_match {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    (leastStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).plan =
      (congrArg (fun added => obligationsOf (seen ++ added))
          (least_added_match seen application application' children children' same)).symm ▸
        (.byRule ruleInstance application
          (leastStepList seen children (same.2.2 ▸ children')).plans) := by
  simp only [leastStep]
  exact least_plan_pos seen same
    (fun h =>
      { added := (leastStepList seen children (h.2.2 ▸ children')).added
        plan := .byRule ruleInstance application
          (leastStepList seen children (h.2.2 ▸ children')).plans })
    (fun _ => share seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem least_added_mismatch {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    (leastStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).added =
      (share seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).added := by
  simp only [leastStep]
  exact least_added_neg seen diff
    (fun h =>
      { added := (leastStepList seen children (h.2.2 ▸ children')).added
        plan := .byRule ruleInstance application
          (leastStepList seen children (h.2.2 ▸ children')).plans })
    (fun _ => share seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem least_plan_mismatch {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    (leastStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).plan =
      (congrArg (fun added => obligationsOf (seen ++ added))
          (least_added_mismatch seen application application' children children' diff)).symm ▸
        (share seen (.byRule (premises := premises) ruleInstance application children)
          (.byRule (premises := premises') ruleInstance' application' children')).plan := by
  simp only [leastStep]
  exact least_plan_neg seen diff
    (fun h =>
      { added := (leastStepList seen children (h.2.2 ▸ children')).added
        plan := .byRule ruleInstance application
          (leastStepList seen children (h.2.2 ▸ children')).plans })
    (fun _ => share seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem identify_added_match {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    (identifyStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).added =
      (identifyList seen children (same.2.2 ▸ children')).added := by
  simp only [identifyStep]
  exact found_added_pos seen same
    (fun h =>
      let descended := identifyList seen children (h.2.2 ▸ children')
      { added := descended.added
        obligations := descended.obligations
        identified := descended.identified })
    (fun _ => foundFromShare seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem identify_obligations_match {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    (identifyStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).obligations =
      (identifyList seen children (same.2.2 ▸ children')).obligations := by
  simp only [identifyStep]
  exact found_obligations_pos seen same
    (fun h =>
      let descended := identifyList seen children (h.2.2 ▸ children')
      { added := descended.added
        obligations := descended.obligations
        identified := descended.identified })
    (fun _ => foundFromShare seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem identifyStep_identified_match {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    (identifyStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).identified =
      (congrArg (fun added => obligationsOf (seen ++ added))
          (identify_added_match seen application application' children children' same)).symm ▸
        ((identify_obligations_match seen application application' children children' same).symm ▸
          (identifyList seen children (same.2.2 ▸ children')).identified) := by
  simp only [identifyStep]
  exact found_identified_pos seen same
    (fun h =>
      let descended := identifyList seen children (h.2.2 ▸ children')
      { added := descended.added
        obligations := descended.obligations
        identified := descended.identified })
    (fun _ => foundFromShare seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem identify_added_mismatch {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    (identifyStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).added =
      (foundFromShare seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).added := by
  simp only [identifyStep]
  exact found_added_neg seen diff
    (fun h =>
      let descended := identifyList seen children (h.2.2 ▸ children')
      { added := descended.added
        obligations := descended.obligations
        identified := descended.identified })
    (fun _ => foundFromShare seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem identify_obligations_mismatch {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    (identifyStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).obligations =
      (foundFromShare seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).obligations := by
  simp only [identifyStep]
  exact found_obligations_neg seen diff
    (fun h =>
      let descended := identifyList seen children (h.2.2 ▸ children')
      { added := descended.added
        obligations := descended.obligations
        identified := descended.identified })
    (fun _ => foundFromShare seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem identifyStep_identified_mismatch {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    (identifyStep seen (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).identified =
      (congrArg (fun added => obligationsOf (seen ++ added))
          (identify_added_mismatch seen application application' children children' diff)).symm ▸
        ((identify_obligations_mismatch seen application application' children children' diff).symm ▸
          (foundFromShare seen
            (.byRule (premises := premises) ruleInstance application children)
            (.byRule (premises := premises') ruleInstance' application' children')).identified) := by
  simp only [identifyStep]
  exact found_identified_neg seen diff
    (fun h =>
      let descended := identifyList seen children (h.2.2 ▸ children')
      { added := descended.added
        obligations := descended.obligations
        identified := descended.identified })
    (fun _ => foundFromShare seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))

theorem castIdentified_match {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') :
    castIdentified seen
        (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')
        (identifyStep_added seen
          (.byRule (premises := premises) ruleInstance application children)
          (.byRule (premises := premises') ruleInstance' application' children'))
        (identifyStep_obligations seen
          (.byRule (premises := premises) ruleInstance application children)
          (.byRule (premises := premises') ruleInstance' application' children')) =
      (antiUnify_obligations_match application application' children children' same).symm ▸
        ((congrArg (fun added => obligationsOf (seen ++ added))
            (least_added_match seen application application' children children' same)).symm ▸
          castIdentifiedList seen children (same.2.2 ▸ children')
            (identifyList_added seen children (same.2.2 ▸ children'))
            (identifyList_obligations seen children (same.2.2 ▸ children'))) := by
  simp only [castIdentified, castIdentifiedList]
  rw [identifyStep_identified_match seen application application' children children' same]
  exact identified_cast_square
    ((congrArg (fun added => obligationsOf (seen ++ added))
        (identify_added_match seen application application' children children' same)).symm)
    ((identify_obligations_match seen application application' children children' same).symm)
    (congrArg (fun added => obligationsOf (seen ++ added))
      (identifyStep_added seen
        (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')))
    (identifyStep_obligations seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))
    (congrArg (fun added => obligationsOf (seen ++ added))
      (identifyList_added seen children (same.2.2 ▸ children')))
    (identifyList_obligations seen children (same.2.2 ▸ children'))
    ((congrArg (fun added => obligationsOf (seen ++ added))
        (least_added_match seen application application' children children' same)).symm)
    ((antiUnify_obligations_match application application' children children' same).symm)
    (identifyList seen children (same.2.2 ▸ children')).identified

theorem castIdentified_mismatch {goal : Pattern} {premises premises' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    {ruleInstance ruleInstance' : RuleInstance}
    (application : RuleApplication definition ruleInstance premises goal)
    (application' : RuleApplication definition ruleInstance' premises' goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises')
    (diff : ¬ (ruleInstance.ruleId = ruleInstance'.ruleId ∧
      ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises')) :
    castIdentified seen
        (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')
        (identifyStep_added seen
          (.byRule (premises := premises) ruleInstance application children)
          (.byRule (premises := premises') ruleInstance' application' children'))
        (identifyStep_obligations seen
          (.byRule (premises := premises) ruleInstance application children)
          (.byRule (premises := premises') ruleInstance' application' children')) =
      (antiUnify_obligations_mismatch application application' children children' diff).symm ▸
        ((congrArg (fun added => obligationsOf (seen ++ added))
            (least_added_mismatch seen application application' children children' diff)).symm ▸
          .cons (share seen
              (.byRule (premises := premises) ruleInstance application children)
              (.byRule (premises := premises') ruleInstance' application' children')).plan
            .nil) := by
  simp only [castIdentified]
  rw [identifyStep_identified_mismatch seen application application' children children' diff]
  simp only [foundFromShare]
  exact identified_cast_square
    ((congrArg (fun added => obligationsOf (seen ++ added))
        (identify_added_mismatch seen application application' children children' diff)).symm)
    ((identify_obligations_mismatch seen application application' children children' diff).symm)
    (congrArg (fun added => obligationsOf (seen ++ added))
      (identifyStep_added seen
        (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')))
    (identifyStep_obligations seen
      (.byRule (premises := premises) ruleInstance application children)
      (.byRule (premises := premises') ruleInstance' application' children'))
    rfl
    rfl
    ((congrArg (fun added => obligationsOf (seen ++ added))
        (least_added_mismatch seen application application' children children' diff)).symm)
    ((antiUnify_obligations_mismatch application application' children children' diff).symm)
    (.cons (share seen
        (.byRule (premises := premises) ruleInstance application children)
        (.byRule (premises := premises') ruleInstance' application' children')).plan
      .nil)

theorem obligations_cons_append {goal : Pattern} {tailGoals : List Pattern}
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    (antiUnify head head').obligations ++ (antiUnifyList tail tail').obligations =
      (antiUnifyList (.cons head tail) (.cons head' tail')).obligations :=
  rfl

theorem antiUnifyList_plans_at_folded {goal : Pattern} {tailGoals : List Pattern}
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    (antiUnifyList (.cons head tail) (.cons head' tail')).plans =
      .cons
        ((antiUnify head head').plan.bind
          (obligations_cons_append head tail head' tail' ▸
            OpenDerivationList.leftProjection (antiUnify head head').obligations
              (antiUnifyList tail tail').obligations))
        ((antiUnifyList tail tail').plans.bind
          (obligations_cons_append head tail head' tail' ▸
            OpenDerivationList.rightProjection (antiUnify head head').obligations
              (antiUnifyList tail tail').obligations)) := by
  have eq := obligations_cons_append head tail head' tail'
  cases eq
  exact antiUnifyList_plans_cons head tail head' tail'

theorem leastStepList_added_cons {goal : Pattern} {tailGoals : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    (leastStepList seen (.cons head tail) (.cons head' tail')).added =
      (leastStep seen head head').added ++
        (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added := by
  rw [leastStepList_cons]

theorem leastStepList_plans_at_folded {goal : Pattern} {tailGoals : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    (leastStepList seen (.cons head tail) (.cons head' tail')).plans =
      (congrArg (fun added => obligationsOf (seen ++ added))
          (leastStepList_added_cons seen head tail head' tail')).symm ▸
        .cons
          (transportContext
              (obligations_assoc seen (leastStep seen head head').added
                (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
            (weakenSlots (base := seen ++ (leastStep seen head head').added)
              (extra :=
                (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
              (leastStep seen head head').plan))
          (transportContextList
              (obligations_assoc seen (leastStep seen head head').added
                (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
            (leastStepList (seen ++ (leastStep seen head head').added) tail tail').plans) :=
  rfl

/-- The identified vector of a cons is the weakened head appended to the tail,
transported onto one shared slot context. The equalities are parameters so each
side is a variable, which is what makes the transport compute. -/
theorem splitIdentified
    {p p' e' : List (Slot definition leftContext rightContext)}
    {g g' k' : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (eAt : List (Slot definition leftContext rightContext) →
      List (Slot definition leftContext rightContext))
    (kAt : List (Slot definition leftContext rightContext) → List Pattern)
    (hp : p = p') (he : eAt p' = e') (hg : g = g') (hk : kAt p' = k')
    (hAdd : p ++ eAt p = p' ++ e')
    (hObl : g ++ kAt p = g' ++ k')
    (headId : OpenDerivationList definition (obligationsOf (seen ++ p)) g)
    (idAt : (s : List (Slot definition leftContext rightContext)) →
      OpenDerivationList definition (obligationsOf ((seen ++ s) ++ eAt s)) (kAt s)) :
    hObl ▸
      (congrArg (fun added => obligationsOf (seen ++ added)) hAdd ▸
        ((transportContextList (obligations_assoc seen p (eAt p))
            (weakenSlotsList (base := seen ++ p) (extra := eAt p) headId)).append
          (transportContextList (obligations_assoc seen p (eAt p)) (idAt p)))) =
      (transportContextList (obligations_assoc seen p' e')
          (weakenSlotsList (base := seen ++ p') (extra := e')
            (hg ▸
              (congrArg (fun added => obligationsOf (seen ++ added)) hp ▸ headId)))).append
        (transportContextList (obligations_assoc seen p' e')
          (hk ▸
            (congrArg (fun added => obligationsOf ((seen ++ p') ++ added)) he ▸
              (idAt p')))) := by
  cases hp
  cases he
  cases hk
  cases hg
  cases hAdd
  cases hObl
  rfl

theorem castIdentifiedList_cons {goal : Pattern} {tailGoals : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (head : OpenDerivation definition leftContext goal)
    (tail : OpenDerivationList definition leftContext tailGoals)
    (head' : OpenDerivation definition rightContext goal)
    (tail' : OpenDerivationList definition rightContext tailGoals) :
    castIdentifiedList seen (.cons head tail) (.cons head' tail')
        (identifyList_added seen (.cons head tail) (.cons head' tail'))
        (identifyList_obligations seen (.cons head tail) (.cons head' tail')) =
      (transportContextList
          (obligations_assoc seen (leastStep seen head head').added
            (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
        (weakenSlotsList
          (base := seen ++ (leastStep seen head head').added)
          (extra :=
            (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
          (castIdentified seen head head'
            (identifyStep_added seen head head')
            (identifyStep_obligations seen head head')))).append
        (transportContextList
          (obligations_assoc seen (leastStep seen head head').added
            (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
          (castIdentifiedList (seen ++ (leastStep seen head head').added) tail tail'
            (identifyList_added (seen ++ (leastStep seen head head').added) tail tail')
            (identifyList_obligations
              (seen ++ (leastStep seen head head').added) tail tail'))) := by
  unfold castIdentifiedList castIdentified
  exact splitIdentified (seen := seen)
    (eAt := fun s => (identifyList (seen ++ s) tail tail').added)
    (kAt := fun s => (identifyList (seen ++ s) tail tail').obligations)
    (hp := identifyStep_added seen head head')
    (he := identifyList_added (seen ++ (leastStep seen head head').added) tail tail')
    (hg := identifyStep_obligations seen head head')
    (hk := identifyList_obligations (seen ++ (leastStep seen head head').added) tail tail')
    (hAdd := identifyList_added seen (.cons head tail) (.cons head' tail'))
    (hObl := identifyList_obligations seen (.cons head tail) (.cons head' tail'))
    (headId := (identifyStep seen head head').identified)
    (idAt := fun s => (identifyList (seen ++ s) tail tail').identified)

mutual

/-- **Binding the identified vector recovers the least general plan.** -/
theorem identifyStep_spec {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) →
    (antiUnify left right).plan.bind
        (castIdentified seen left right (identifyStep_added seen left right)
          (identifyStep_obligations seen left right)) =
      (leastStep seen left right).plan
  | seen, .assumption _, right => by
      simp only [castIdentified, identifyStep, foundFromShare, leastStep, antiUnify, slot]
      exact bind_singleton _
  | seen, .byRule (premises := premises) ruleInstance application children, right => by
      cases right
      case assumption _ =>
        simp only [castIdentified, identifyStep, foundFromShare, leastStep, antiUnify,
          rootRule?, slot]
        exact bind_singleton _
      case byRule ruleInstance' premises' children' application' =>
        by_cases same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
            ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises'
        · rw [antiUnify_plan_match application application' children children' same,
            least_plan_match seen application application' children children' same]
          rw [bind_symm_cast]
          rw [byRule_transport
              ((congrArg (fun added => obligationsOf (seen ++ added))
                  (least_added_match seen application application' children children' same)).symm)]
          simp only [OpenDerivation.bind]
          apply congrArg (OpenDerivation.byRule ruleInstance application)
          rw [castIdentified_match seen application application' children children' same]
          rw [goals_cast_cancel
              (antiUnify_obligations_match application application' children children' same)]
          rw [bindList_cast_environment
              ((congrArg (fun added => obligationsOf (seen ++ added))
                  (least_added_match seen application application' children children' same)).symm)]
          exact congrArg
            (fun (plans : OpenDerivationList definition
                (obligationsOf (seen ++
                  (leastStepList seen children (same.2.2 ▸ children')).added))
                premises) =>
              (congrArg (fun added => obligationsOf (seen ++ added))
                  (least_added_match seen application application' children children' same)).symm ▸
                plans)
            (identifyList_spec seen children (same.2.2 ▸ children'))
          exact antiUnify_obligations_match application application' children children' same
        · rw [antiUnify_plan_mismatch application application' children children' same,
            least_plan_mismatch seen application application' children children' same]
          rw [bind_symm_cast]
          rw [castIdentified_mismatch seen application application' children children' same]
          rw [goals_cast_cancel
              (antiUnify_obligations_mismatch application application' children children' same)]
          exact bind_singleton_context
            ((congrArg (fun added => obligationsOf (seen ++ added))
                (least_added_mismatch seen application application' children children' same)).symm)
            (share seen
              (.byRule (premises := premises) ruleInstance application children)
              (.byRule (premises := premises') ruleInstance' application' children')).plan
          exact antiUnify_obligations_mismatch application application' children children' same

/-- Pointwise form. -/
theorem identifyList_spec {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) →
    (antiUnifyList left right).plans.bind
        (castIdentifiedList seen left right (identifyList_added seen left right)
          (identifyList_obligations seen left right)) =
      (leastStepList seen left right).plans
  | _, .nil, .nil => rfl
  | seen, .cons head tail, .cons head' tail' => by
      rw [castIdentifiedList_cons]
      show
          OpenDerivationList.cons
            (((antiUnify head head').plan.bind
                (OpenDerivationList.leftProjection (antiUnify head head').obligations
                  (antiUnifyList tail tail').obligations)).bind
              ((transportContextList
                    (obligations_assoc seen (leastStep seen head head').added
                      (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
                  (weakenSlotsList (base := seen ++ (leastStep seen head head').added)
                    (extra :=
                      (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
                    (castIdentified seen head head'
                      (identifyStep_added seen head head')
                      (identifyStep_obligations seen head head')))).append
                (transportContextList
                    (obligations_assoc seen (leastStep seen head head').added
                      (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
                  (castIdentifiedList (seen ++ (leastStep seen head head').added) tail tail'
                    (identifyList_added (seen ++ (leastStep seen head head').added) tail tail')
                    (identifyList_obligations
                      (seen ++ (leastStep seen head head').added) tail tail')))))
            (((antiUnifyList tail tail').plans.bind
                (OpenDerivationList.rightProjection (antiUnify head head').obligations
                  (antiUnifyList tail tail').obligations)).bind
              ((transportContextList
                    (obligations_assoc seen (leastStep seen head head').added
                      (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
                  (weakenSlotsList (base := seen ++ (leastStep seen head head').added)
                    (extra :=
                      (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
                    (castIdentified seen head head'
                      (identifyStep_added seen head head')
                      (identifyStep_obligations seen head head')))).append
                (transportContextList
                    (obligations_assoc seen (leastStep seen head head').added
                      (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
                  (castIdentifiedList (seen ++ (leastStep seen head head').added) tail tail'
                    (identifyList_added (seen ++ (leastStep seen head head').added) tail tail')
                    (identifyList_obligations
                      (seen ++ (leastStep seen head head').added) tail tail'))))) =
          OpenDerivationList.cons
            (transportContext
                (obligations_assoc seen (leastStep seen head head').added
                  (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
              (weakenSlots (base := seen ++ (leastStep seen head head').added)
                (extra :=
                  (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
                (leastStep seen head head').plan))
            (transportContextList
                (obligations_assoc seen (leastStep seen head head').added
                  (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added)
              (leastStepList (seen ++ (leastStep seen head head').added) tail tail').plans)
      congr 1
      · rw [OpenDerivation.bind_assoc, OpenDerivationList.leftProjection_bind_append,
          bind_transportContext, bind_weakenSlotsList, identifyStep_spec]
      · rw [OpenDerivationList.bind_assoc, OpenDerivationList.rightProjection_bind_append,
          bindList_transportContext, identifyList_spec]

end

/-- **The linear anti-unification instantiates to the least general plan** by
sending each linear obligation to the shared sub-plan of the same erasure pair. -/
theorem antiUnify_instantiates {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (antiUnify left right).plan.bind
        (castIdentified [] left right (identifyStep_added [] left right)
          (identifyStep_obligations [] left right)) =
      (leastGeneral left right).plan :=
  identifyStep_spec [] left right

/-! ## The skeleton of a generalizing plan

Instantiating a plan and then taking the least general generalization keeps
that plan's rules.  At an obligation, the step is the least general
generalization of the two derivations substituted for it.  Repeated
obligations are not identified here: each occurrence generalizes its own pair
against the slots already allocated.  Every obligation being used is not
required for this agreement.
-/

/-- When both plans carry the same rule, least general generalization descends
under that rule. -/
theorem leastStep_byRule_same {goal : Pattern} {premises : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (ruleInstance : RuleInstance)
    (application : RuleApplication definition ruleInstance premises goal)
    (children : OpenDerivationList definition leftContext premises)
    (children' : OpenDerivationList definition rightContext premises) :
    leastStep seen
        (.byRule ruleInstance application children)
        (.byRule ruleInstance application children') =
      let descended := leastStepList seen children children'
      { added := descended.added
        plan := OpenDerivation.byRule ruleInstance application descended.plans } := by
  simp only [leastStep]
  rw [dif_pos ⟨trivial, trivial, trivial⟩]

mutual

/-- Least general generalization driven by one plan's constructors. -/
def skeletonStep {context : List Pattern} {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (plan : OpenDerivation definition context goal) →
    (leftSub : OpenDerivationList definition leftContext context) →
    (rightSub : OpenDerivationList definition rightContext context) →
      LeastStep seen goal
  | seen, .assumption index, leftSub, rightSub =>
      leastStep seen (leftSub.get index) (rightSub.get index)
  | seen, .byRule ruleInstance application children, leftSub, rightSub =>
      let descended := skeletonStepList seen children leftSub rightSub
      { added := descended.added
        plan := .byRule ruleInstance application descended.plans }

/-- The same walk, premise by premise. -/
def skeletonStepList {context : List Pattern} {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (plans : OpenDerivationList definition context goals) →
    (leftSub : OpenDerivationList definition leftContext context) →
    (rightSub : OpenDerivationList definition rightContext context) →
      LeastStepList seen goals
  | _, .nil, _, _ => { added := [], plans := .nil }
  | seen, .cons head tail, leftSub, rightSub =>
      let first := skeletonStep seen head leftSub rightSub
      let rest := skeletonStepList (seen ++ first.added) tail leftSub rightSub
      { added := first.added ++ rest.added
        plans := .cons
          (transportContext (obligations_assoc seen first.added rest.added)
            (weakenSlots (base := seen ++ first.added) (extra := rest.added) first.plan))
          (transportContextList (obligations_assoc seen first.added rest.added) rest.plans) }

end

theorem skeletonStepList_cons {context : List Pattern} {goal : Pattern}
    {tailGoals : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (head : OpenDerivation definition context goal)
    (tail : OpenDerivationList definition context tailGoals)
    (leftSub : OpenDerivationList definition leftContext context)
    (rightSub : OpenDerivationList definition rightContext context) :
    skeletonStepList seen (.cons head tail) leftSub rightSub =
      let first := skeletonStep seen head leftSub rightSub
      let rest := skeletonStepList (seen ++ first.added) tail leftSub rightSub
      { added := first.added ++ rest.added
        plans := OpenDerivationList.cons
          (transportContext (obligations_assoc seen first.added rest.added)
            (weakenSlots (base := seen ++ first.added) (extra := rest.added) first.plan))
          (transportContextList (obligations_assoc seen first.added rest.added)
            rest.plans) } :=
  rfl

mutual

/-- Walking the plan agrees with least general generalization of its two
instantiations. -/
theorem skeletonStep_spec {context : List Pattern} {goal : Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (plan : OpenDerivation definition context goal) →
    (leftSub : OpenDerivationList definition leftContext context) →
    (rightSub : OpenDerivationList definition rightContext context) →
      skeletonStep seen plan leftSub rightSub =
        leastStep seen (plan.bind leftSub) (plan.bind rightSub)
  | seen, .assumption index, leftSub, rightSub => by
      simp only [skeletonStep, OpenDerivation.bind]
  | seen, .byRule ruleInstance application children, leftSub, rightSub => by
      simp only [skeletonStep, OpenDerivation.bind]
      rw [leastStep_byRule_same]
      rw [skeletonStepList_spec seen children leftSub rightSub]

/-- The premise walk agrees as well. -/
theorem skeletonStepList_spec {context : List Pattern} {goals : List Pattern} :
    (seen : List (Slot definition leftContext rightContext)) →
    (plans : OpenDerivationList definition context goals) →
    (leftSub : OpenDerivationList definition leftContext context) →
    (rightSub : OpenDerivationList definition rightContext context) →
      skeletonStepList seen plans leftSub rightSub =
        leastStepList seen (plans.bind leftSub) (plans.bind rightSub)
  | _, .nil, _, _ => by
      simp only [skeletonStepList, OpenDerivationList.bind, leastStepList]
  | seen, .cons head tail, leftSub, rightSub => by
      rw [skeletonStepList_cons]
      simp only [OpenDerivationList.bind]
      rw [leastStepList_cons]
      rw [skeletonStep_spec seen head leftSub rightSub]
      rw [skeletonStepList_spec
        (seen ++ (leastStep seen (head.bind leftSub) (head.bind rightSub)).added)
        tail leftSub rightSub]

end

/-! ## Replaying a generalization

Once the slots of a pair have been allocated, generalizing that same pair
again allocates nothing.  A citation in the original context weakens to the
citation of the same numeral.  Identifying the replayed plan with that
weakened plan, and packaging one entry per obligation, is not proved here.
-/

theorem leastStep_cast {goal : Pattern}
    {seen seen' : List (Slot definition leftContext rightContext)}
    (equal : seen = seen')
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    equal ▸ leastStep seen left right = leastStep seen' left right := by
  cases equal
  rfl

theorem leastStepList_cast {goals : List Pattern}
    {seen seen' : List (Slot definition leftContext rightContext)}
    (equal : seen = seen')
    (left : OpenDerivationList definition leftContext goals)
    (right : OpenDerivationList definition rightContext goals) :
    equal ▸ leastStepList seen left right = leastStepList seen' left right := by
  cases equal
  rfl

theorem leastAdded_cast {goal : Pattern}
    {seen seen' : List (Slot definition leftContext rightContext)}
    (equal : seen = seen') (step : LeastStep seen goal) :
    (equal ▸ step).added = step.added := by
  cases equal
  rfl

theorem leastListAdded_cast {goals : List Pattern}
    {seen seen' : List (Slot definition leftContext rightContext)}
    (equal : seen = seen') (step : LeastStepList seen goals) :
    (equal ▸ step).added = step.added := by
  cases equal
  rfl

theorem slot_matches_self {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (⟨goal, left, right⟩ : Slot definition leftContext rightContext).matches left right = true := by
  unfold Slot.matches
  exact decide_eq_true ⟨rfl, rfl⟩

/-- A second share of the same pair allocates no slot, whether the first share
reused one or opened one. -/
theorem share_replay_added {goal : Pattern}
    (seen later : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (share ((seen ++ (share seen left right).added) ++ later) left right).added = [] := by
  unfold share
  let pred := fun slot : Slot definition leftContext rightContext => slot.matches left right
  cases decision : decide (seen.findIdx pred < seen.length) with
  | true =>
      have found := of_decide_eq_true decision
      rw [dif_pos found]
      have idx :
          ((seen ++ []) ++ later).findIdx pred = seen.findIdx pred := by
        rw [List.append_nil, List.findIdx_append, if_pos found]
      have lt :
          ((seen ++ []) ++ later).findIdx pred < ((seen ++ []) ++ later).length := by
        rw [idx]
        refine Nat.lt_of_lt_of_le found ?_
        rw [List.append_nil, List.length_append]
        omega
      rw [dif_pos lt]
  | false =>
      have miss := of_decide_eq_false decision
      rw [dif_neg miss]
      let slot : Slot definition leftContext rightContext := ⟨goal, left, right⟩
      have atSlot : (seen ++ [slot]).findIdx pred = seen.length := by
        rw [List.findIdx_append, if_neg miss]
        have matched : pred slot = true := by
          dsimp only [pred, slot]
          exact slot_matches_self left right
        rw [List.findIdx_singleton, matched, if_pos rfl, Nat.zero_add]
      have ltSlot :
          (seen ++ [slot]).findIdx pred < (seen ++ [slot]).length := by
        rw [atSlot, List.length_append, List.length_singleton]
        omega
      have idx : ((seen ++ [slot]) ++ later).findIdx pred = seen.length := by
        rw [List.findIdx_append, if_pos ltSlot, atSlot]
      have lt :
          ((seen ++ [slot]) ++ later).findIdx pred <
            ((seen ++ [slot]) ++ later).length := by
        rw [idx, List.length_append]
        omega
      rw [dif_pos lt]

mutual

/-- Generalizing a pair whose own slots are already present allocates nothing. -/
theorem replay_added {goal : Pattern} :
    (seen later : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) →
      (leastStep ((seen ++ (leastStep seen left right).added) ++ later) left right).added = []
  | seen, later, .assumption index, right => by
      simp only [leastStep]
      exact share_replay_added seen later (.assumption index) right
  | seen, later, .byRule _ _ _, .assumption _ => by
      simp only [leastStep]
      exact share_replay_added seen later _ _
  | seen, later,
      .byRule (premises := premises) ruleInstance application children,
      .byRule (premises := premises') ruleInstance' application' children' => by
      cases decision : decide
          (ruleInstance.ruleId = ruleInstance'.ruleId ∧
            ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises') with
      | false =>
          simp only [leastStep]
          rw [dif_neg (of_decide_eq_false decision), dif_neg (of_decide_eq_false decision)]
          exact share_replay_added seen later
            (.byRule (premises := premises) ruleInstance application children)
            (.byRule (premises := premises') ruleInstance' application' children')
      | true =>
          have same := of_decide_eq_true decision
          have innerAdded :
              (leastStep seen
                  (.byRule (premises := premises) ruleInstance application children)
                  (.byRule (premises := premises') ruleInstance' application'
                    children')).added =
                (leastStepList seen children (same.2.2 ▸ children')).added := by
            simp only [leastStep]
            rw [dif_pos same]
          rw [innerAdded]
          have outerAdded :
              (leastStep
                  ((seen ++ (leastStepList seen children (same.2.2 ▸ children')).added) ++
                    later)
                  (.byRule (premises := premises) ruleInstance application children)
                  (.byRule (premises := premises') ruleInstance' application'
                    children')).added =
                (leastStepList
                    ((seen ++ (leastStepList seen children (same.2.2 ▸ children')).added) ++
                      later)
                    children (same.2.2 ▸ children')).added := by
            simp only [leastStep]
            rw [dif_pos same]
          exact outerAdded.trans
            (replayList_added seen later children (same.2.2 ▸ children'))

/-- The same replay for an ordered vector of premises. -/
theorem replayList_added {goals : List Pattern} :
    (seen later : List (Slot definition leftContext rightContext)) →
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) →
      (leastStepList
          ((seen ++ (leastStepList seen left right).added) ++ later) left right).added = []
  | _, _, .nil, .nil => by
      simp only [leastStepList]
  | seen, later, .cons head tail, .cons head' tail' => by
      have innerAdded :
          (leastStepList seen (.cons head tail) (.cons head' tail')).added =
            (leastStep seen head head').added ++
              (leastStepList (seen ++ (leastStep seen head head').added) tail tail').added := by
        rw [leastStepList_cons]
      rw [innerAdded]
      let headStep := leastStep seen head head'
      let tailStep := leastStepList (seen ++ headStep.added) tail tail'
      let big := (seen ++ (headStep.added ++ tailStep.added)) ++ later
      have headNil : (leastStep big head head').added = [] := by
        have assoc :
            (seen ++ headStep.added) ++ (tailStep.added ++ later) = big := by
          dsimp only [big]
          simp only [List.append_assoc]
        have ih := replay_added seen (tailStep.added ++ later) head head'
        have castEq := leastStep_cast assoc head head'
        rw [← castEq, leastAdded_cast assoc
          (leastStep ((seen ++ headStep.added) ++ (tailStep.added ++ later)) head head')]
        exact ih
      have tailNil :
          (leastStepList (big ++ (leastStep big head head').added) tail tail').added = [] := by
        rw [headNil]
        have seenEq :
            ((seen ++ headStep.added) ++ tailStep.added) ++ later = big ++ [] := by
          dsimp only [big]
          simp only [List.append_assoc, List.append_nil]
        have ih := replayList_added (seen ++ headStep.added) later tail tail'
        have castEq := leastStepList_cast seenEq tail tail'
        rw [← castEq, leastListAdded_cast seenEq
          (leastStepList (((seen ++ headStep.added) ++ tailStep.added) ++ later) tail tail')]
        exact ih
      have outerAdded :
          (leastStepList big (.cons head tail) (.cons head' tail')).added =
            (leastStep big head head').added ++
              (leastStepList (big ++ (leastStep big head head').added) tail tail').added := by
        rw [leastStepList_cons]
      rw [outerAdded, tailNil, headNil]
      rfl

end

theorem weakenAppend_transportGoal {context extra : List Pattern} {source goal : Pattern}
    (backup : source = goal) (derivation : OpenDerivation definition context source) :
    weakenAppend (extra := extra) (transportGoal backup derivation) =
      transportGoal backup (weakenAppend (extra := extra) derivation) := by
  cases backup
  rw [transportGoal_id rfl, transportGoal_id rfl]

theorem weakenAppend_cite {context extra : List Pattern} {goal : Pattern}
    (index : Fin context.length) (backup : context.get index = goal) :
    (weakenAppend (extra := extra) (cite index backup) :
        OpenDerivation definition (context ++ extra) goal) =
      transportGoal
        ((OpenDerivationList.get_left (secondGoals := extra) index).trans backup)
        (OpenDerivation.assumption
          ⟨index.1, OpenDerivationList.length_left (secondGoals := extra) index⟩) := by
  unfold cite
  rw [weakenAppend_transportGoal backup (.assumption index)]
  unfold weakenAppend cite
  rw [← transportGoal_trans
    (OpenDerivationList.get_left (secondGoals := extra) index) backup]

/-! ## Controls -/

namespace LeastGeneral

open Fixture

/-- `pair(axA₁, axA₁)`. -/
def pairSameLeft : OpenDerivation kernelDefinition [] D :=
  .byRule _ (kernelApp (rule := rulePair) (by simp [kernelRules]))
    (.cons (OpenDerivation.ofClosed dA₁) (.cons (OpenDerivation.ofClosed dA₁) .nil))

/-- `pair(axA₂, axA₂)`. -/
def pairSameRight : OpenDerivation kernelDefinition [] D :=
  .byRule _ (kernelApp (rule := rulePair) (by simp [kernelRules]))
    (.cons (OpenDerivation.ofClosed dA₂) (.cons (OpenDerivation.ofClosed dA₂) .nil))

/-- **Positive.**  `pair(a,a)` and `pair(b,b)` share one slot. -/
theorem shared_slot :
    (leastGeneral pairSameLeft pairSameRight).obligations = [A] ∧
      (leastGeneral pairSameLeft pairSameRight).plan.ruleCount = 1 ∧
      (holeOccurrences (leastGeneral pairSameLeft pairSameRight).plan).map Fin.val = [0, 0] := by
  decide

/-- **Negative.**  `pair(a,b)` and `pair(b,a)` are two distinct erasure pairs,
so least general generalization still opens two slots. -/
theorem distinct_slots :
    (leastGeneral AntiUnification.pairOneTwo AntiUnification.pairTwoOne).obligations = [A, A] ∧
      (holeOccurrences
        (leastGeneral AntiUnification.pairOneTwo AntiUnification.pairTwoOne).plan).map Fin.val =
        [0, 1] := by
  decide

/-- The two axioms for `A`, read in a context that also assumes `CastCG`. -/
def axiomLeft : OpenDerivation kernelDefinition [CastCG] A :=
  OpenDerivation.ofClosed dA₁

def axiomRight : OpenDerivation kernelDefinition [CastCG] A :=
  OpenDerivation.ofClosed dA₂

/-- A generalization that cites only `A` and never the extra obligation `CastCG`. -/
def spuriousPlan : OpenDerivation kernelDefinition [A, CastCG] A :=
  .assumption ⟨0, by decide⟩

def spuriousLeft : OpenDerivationList kernelDefinition [CastCG] [A, CastCG] :=
  .cons (OpenDerivation.ofClosed dA₁) (.cons (.assumption ⟨0, by decide⟩) .nil)

def spuriousRight : OpenDerivationList kernelDefinition [CastCG] [A, CastCG] :=
  .cons (OpenDerivation.ofClosed dA₂) (.cons (.assumption ⟨0, by decide⟩) .nil)

theorem spurious_recovers_left : spuriousPlan.bind spuriousLeft = axiomLeft := rfl

theorem spurious_recovers_right : spuriousPlan.bind spuriousRight = axiomRight := rfl

/-- `CastCG` does not follow from `A`. -/
theorem no_castCG_from_A (derivation : OpenDerivation kernelDefinition [A] CastCG) : False :=
  (OpenDerivation.sound_of_ruleApplications kernelTruth kernelRules_preserve_truth
    (fun premise member => by
      simp only [List.mem_singleton] at member
      subst member
      decide) derivation).2.1 rfl

theorem spurious_misses_cast (uses : UsesAll spuriousPlan) : False := by
  have member := uses ⟨1, by decide⟩
  have holes : holeOccurrences spuriousPlan = [⟨0, by decide⟩] := rfl
  rw [holes] at member
  have values : (1 : Nat) = 0 := congrArg Fin.val (List.mem_singleton.mp member)
  cases values

/-- **Why minimality needs every obligation to be used.**  The unused `CastCG`
is derivable from both original contexts and from neither shared obligation of
the least general plan, so no substitution lands on that plan. -/
theorem unused_obligation_blocks_minimality :
    spuriousPlan.bind spuriousLeft = axiomLeft ∧
      spuriousPlan.bind spuriousRight = axiomRight ∧
      ¬ UsesAll spuriousPlan ∧
      ¬ ∃ environment : OpenDerivationList kernelDefinition
          (leastGeneral axiomLeft axiomRight).obligations [A, CastCG],
        spuriousPlan.bind environment = (leastGeneral axiomLeft axiomRight).plan := by
  refine ⟨rfl, rfl, spurious_misses_cast, ?_⟩
  intro ⟨environment, _⟩
  have obligations : (leastGeneral axiomLeft axiomRight).obligations = [A] := by
    decide
  have typed : OpenDerivationList kernelDefinition [A] [A, CastCG] :=
    obligations ▸ environment
  cases typed with
  | cons _ rest =>
      cases rest with
      | cons bad _ => exact no_castCG_from_A bad

end LeastGeneral

end Mettapedia.GSLT.ProofPlans
