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

A second generalization in the allocated table recalls the same rule instances
and slot indices. Every plan that generalizes the two inputs and cites all its
obligations has a unique specialization to the least general plan. Its
substitution restricts along each input environment to that original
environment, preserving its ordered premises.
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

private def Slot.matchesErasure {leftContext rightContext : List Pattern}
    (slot : Slot definition leftContext rightContext) (left right : RawOpenProof) : Bool :=
  decide (slot.left.eraseOpen = left ∧ slot.right.eraseOpen = right)

/-- The two sub-plans are the same disagreement when their erasures agree. -/
def Slot.matches {leftContext rightContext : List Pattern} {goal : Pattern}
    (slot : Slot definition leftContext rightContext)
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) : Bool :=
  slot.matchesErasure left.eraseOpen right.eraseOpen

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

private def citeMatchingSlot {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal)
    (index : Fin seen.length) (matched : (seen.get index).matches left right = true) :
    OpenDerivation definition (obligationsOf (seen ++ [])) goal :=
  let slot := seen.get index
  have erased : slot.left.eraseOpen = left.eraseOpen ∧ slot.right.eraseOpen = right.eraseOpen :=
    of_decide_eq_true matched
  have sameGoal : slot.goal = goal := (eraseOpen_determines slot.left left erased.1).1
  transportContext (obligations_append_nil seen)
    (cite (obligationIndex seen index) ((slotGoal_get seen index).trans sameGoal))

/-- Cite the stored slot of an identical erasure pair. -/
def reusePlan {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal)
    (found : seen.findIdx (fun slot => slot.matches left right) < seen.length) :
    OpenDerivation definition (obligationsOf (seen ++ [])) goal :=
  citeMatchingSlot seen left right
    ⟨seen.findIdx (fun slot => slot.matches left right), found⟩
    (List.findIdx_getElem (xs := seen) (p := fun slot => slot.matches left right) (w := found))

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

/-- Share the erased candidate pair and the position of its first matching slot. -/
private def shareWithErasure {goal : Pattern} (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) : LeastStep seen goal :=
  let leftErasure := left.eraseOpen
  let rightErasure := right.eraseOpen
  let isCandidate := fun slot : Slot definition leftContext rightContext =>
    slot.matchesErasure leftErasure rightErasure
  let position := seen.findIdx isCandidate
  if found : position < seen.length then
    { added := [], plan := citeMatchingSlot seen left right ⟨position, found⟩
        (List.findIdx_getElem (xs := seen) (p := isCandidate) (w := found)) }
  else
    let slot : Slot definition leftContext rightContext := ⟨goal, left, right⟩
    { added := [slot], plan := cite (appendedIndex seen slot) (appendedGoal seen slot) }

@[csimp] theorem share_eq_shareWithErasure : @share = @shareWithErasure := rfl

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

section SubstitutionSupport

variable {context target : List Pattern}

mutual

/-- An instantiated derivation determines exactly the values substituted at its cited slots. -/
theorem bind_eq_iff_citations {goal : Pattern}
    (plan : OpenDerivation definition context goal)
    (left right : OpenDerivationList definition target context) :
    plan.bind left = plan.bind right ↔
      ∀ index ∈ holeOccurrences plan, left.get index = right.get index := by
  cases plan with
  | assumption index =>
      simp [OpenDerivation.bind, holeOccurrences]
  | byRule _ _ premises =>
      simp only [OpenDerivation.bind, holeOccurrences, OpenDerivation.byRule.injEq,
        heq_eq_eq, true_and]
      exact bindList_eq_iff_citations premises left right

theorem bindList_eq_iff_citations {goals : List Pattern}
    (plans : OpenDerivationList definition context goals)
    (left right : OpenDerivationList definition target context) :
    plans.bind left = plans.bind right ↔
      ∀ index ∈ holeOccurrencesList plans, left.get index = right.get index := by
  cases plans with
  | nil => simp [OpenDerivationList.bind, holeOccurrencesList]
  | cons first rest =>
      rw [OpenDerivationList.bind, OpenDerivationList.bind, OpenDerivationList.cons.injEq]
      rw [bind_eq_iff_citations first left right, bindList_eq_iff_citations rest left right]
      simp only [holeOccurrencesList, List.mem_append]
      exact ⟨fun ⟨a, b⟩ i h => h.elim (a i) (b i),
        fun h => ⟨fun i hi => h i (.inl hi), fun i hi => h i (.inr hi)⟩⟩

end

/-- When a plan cites every slot, its instantiated proof determines the whole environment. -/
theorem UsesAll.bind_injective {goal : Pattern} {plan : OpenDerivation definition context goal}
    (used : UsesAll plan) :
    Function.Injective (fun environment : OpenDerivationList definition target context =>
      plan.bind environment) := by
  intro left right same
  have entries : (fun index => left.get index) = fun index => right.get index :=
    funext fun index => (bind_eq_iff_citations plan left right).mp same index (used index)
  simpa only [OpenDerivationList.ofFn_get] using
    congrArg (OpenDerivationList.ofFn context) entries

end SubstitutionSupport

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
  unfold reusePlan citeMatchingSlot
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
  unfold reusePlan citeMatchingSlot
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

private theorem erase_contextCast {first second : List Pattern} {goal : Pattern}
    (same : first = second) (proof : OpenDerivation definition first goal) :
    (same ▸ proof : OpenDerivation definition second goal).eraseOpen = proof.eraseOpen := by
  cases same
  rfl

private theorem erase_contextListCast {first second goals : List Pattern}
    (same : first = second) (proofs : OpenDerivationList definition first goals) :
    (same ▸ proofs : OpenDerivationList definition second goals).eraseOpen = proofs.eraseOpen := by
  cases same
  rfl

private theorem erase_goalsListCast {context first second : List Pattern}
    (same : first = second) (proofs : OpenDerivationList definition context first) :
    (same ▸ proofs : OpenDerivationList definition context second).eraseOpen = proofs.eraseOpen := by
  cases same
  rfl

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
  rw [dif_pos same]

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
  apply eraseOpen_injective
  rw [erase_contextCast]
  simp only [antiUnify, rootRule?]
  rw [dif_pos same]

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
  simp only [antiUnify, rootRule?]
  rw [dif_neg diff]
  rfl

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
  apply eraseOpen_injective
  rw [erase_contextCast]
  simp only [antiUnify, rootRule?]
  rw [dif_neg diff]
  rfl

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
  rw [dif_pos same]

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
  apply eraseOpen_injective
  rw [erase_contextCast]
  simp only [leastStep]
  rw [dif_pos same]

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
  rw [dif_neg diff]

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
  apply eraseOpen_injective
  rw [erase_contextCast]
  simp only [leastStep]
  rw [dif_neg diff]

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
  rw [dif_pos same]

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
  rw [dif_pos same]

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
  apply eraseOpenList_injective
  rw [erase_contextListCast, erase_goalsListCast]
  simp only [identifyStep]
  rw [dif_pos same]

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
  rw [dif_neg diff]

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
  rw [dif_neg diff]

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
  apply eraseOpenList_injective
  rw [erase_contextListCast, erase_goalsListCast]
  simp only [identifyStep]
  rw [dif_neg diff]

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

Once all slots of a pair have been allocated, generalizing the pair again
recalls every original citation and rule instance. The readout commutes with
each prefix-preserving extension of the allocated table.
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
  unfold Slot.matches Slot.matchesErasure
  exact decide_eq_true ⟨rfl, rfl⟩

@[simp] private theorem erase_transportGoal {context : List Pattern}
    {source goal : Pattern} (same : source = goal)
    (proof : OpenDerivation definition context source) :
    (transportGoal same proof).eraseOpen = proof.eraseOpen := by
  cases same
  rw [transportGoal_id]

@[simp] private theorem erase_transportContext {source target : List Pattern}
    {goal : Pattern} (same : source = target)
    (proof : OpenDerivation definition source goal) :
    (transportContext same proof).eraseOpen = proof.eraseOpen := by
  rw [transportContext_cast]
  cases same
  rfl

@[simp] private theorem erase_transportContextList {source target goals : List Pattern}
    (same : source = target) (proofs : OpenDerivationList definition source goals) :
    (transportContextList same proofs).eraseOpen = proofs.eraseOpen := by
  rw [transportContextList_cast]
  cases same
  rfl

@[simp] private theorem erase_cite {context : List Pattern} {goal : Pattern}
    (index : Fin context.length) (same : context.get index = goal) :
    (cite (definition := definition) index same).eraseOpen = .premise index.val := by
  simp only [cite, erase_transportGoal, OpenDerivation.eraseOpen]

mutual

@[simp] private theorem erase_weakenAppend {context extra : List Pattern} {goal : Pattern}
    (proof : OpenDerivation definition context goal) :
    (weakenAppend (extra := extra) proof).eraseOpen = proof.eraseOpen := by
  cases proof with
  | assumption index => simp only [weakenAppend, erase_cite, OpenDerivation.eraseOpen]
  | byRule rule application children =>
      simp only [weakenAppend, OpenDerivation.eraseOpen, erase_weakenAppendList children]

@[simp] private theorem erase_weakenAppendList {context extra goals : List Pattern}
    (proofs : OpenDerivationList definition context goals) :
    (weakenAppendList (extra := extra) proofs).eraseOpen = proofs.eraseOpen := by
  cases proofs with
  | nil => rfl
  | cons head tail =>
      simp only [weakenAppendList, OpenDerivationList.eraseOpen, erase_weakenAppend,
        erase_weakenAppendList tail]

end

/-- A step recalls the same result once its recorded slots are present.
Later slots may extend the table while leaving the earlier indices valid. -/
private def AppendStable {α β : Type*} (step : List α → List α × β) : Prop :=
  ∀ seen later, step ((seen ++ (step seen).1) ++ later) = ([], (step seen).2)

private theorem AppendStable.map {α β γ : Type*} {step : List α → List α × β}
    (stable : AppendStable step) (transform : β → γ) :
    AppendStable (fun seen => ((step seen).1, transform (step seen).2)) := by
  intro seen later
  dsimp only
  rw [stable seen later]

private theorem AppendStable.combine {α β γ δ : Type*}
    {head : List α → List α × β} {tail : List α → List α × γ}
    (headStable : AppendStable head) (tailStable : AppendStable tail) (combine : β → γ → δ) :
    AppendStable (fun seen =>
      let first := head seen
      let rest := tail (seen ++ first.1)
      (first.1 ++ rest.1, combine first.2 rest.2)) := by
  intro seen later
  dsimp only
  let first := head seen
  let rest := tail (seen ++ first.1)
  let extended := (seen ++ (first.1 ++ rest.1)) ++ later
  have headReplay : head extended = ([], first.2) := by
    simpa only [extended, first, List.append_assoc] using headStable seen (rest.1 ++ later)
  have tailReplay : tail extended = ([], rest.2) := by
    simpa only [extended, rest, List.append_assoc] using tailStable (seen ++ first.1) later
  change ((head extended).1 ++ (tail (extended ++ (head extended).1)).1,
    combine (head extended).2 (tail (extended ++ (head extended).1)).2) =
      ([], combine first.2 rest.2)
  simp only [headReplay, List.append_nil, tailReplay]

private theorem share_readout {goal : Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    let index := seen.findIdx (fun slot => slot.matches left right)
    ((share seen left right).added, (share seen left right).plan.eraseOpen) =
      (if index < seen.length then [] else [⟨goal, left, right⟩], .premise index) := by
  dsimp only
  unfold share
  by_cases found : seen.findIdx (fun slot => slot.matches left right) < seen.length
  · rw [dif_pos found, if_pos found]
    simp only [reusePlan, citeMatchingSlot, erase_transportContext, erase_cite, obligationIndex]
  · rw [dif_neg found, if_neg found]
    have atEnd : seen.findIdx (fun slot => slot.matches left right) = seen.length :=
      Nat.le_antisymm List.findIdx_le_length (Nat.le_of_not_lt found)
    simp only [erase_cite, appendedIndex, atEnd]

private theorem shareIndex_stable {α : Type*} (slot : α) (test : α → Bool)
    (self : test slot = true) :
    AppendStable (fun seen =>
      let index := seen.findIdx test
      (if index < seen.length then [] else [slot], RawOpenProof.premise index)) := by
  intro seen later
  dsimp only
  by_cases found : seen.findIdx test < seen.length
  · have index : (seen ++ later).findIdx test = seen.findIdx test := by
      rw [List.findIdx_append, if_pos found]
    have hit : (seen ++ later).findIdx test < (seen ++ later).length := by
      rw [index, List.length_append]
      omega
    rw [index] at hit
    simp only [if_pos found, List.append_nil, index, if_pos hit]
  · have atEnd : seen.findIdx test = seen.length :=
      Nat.le_antisymm List.findIdx_le_length (Nat.le_of_not_lt found)
    have atSlot : (seen ++ [slot]).findIdx test = seen.length := by
      rw [List.findIdx_append, if_neg found, List.findIdx_singleton, self,
        if_pos rfl, Nat.zero_add]
    have inside : (seen ++ [slot]).findIdx test < (seen ++ [slot]).length := by
      simp only [atSlot, List.length_append, List.length_singleton, Nat.lt_succ_self]
    have index : ((seen ++ [slot]) ++ later).findIdx test = seen.findIdx test := by
      rw [List.findIdx_append, if_pos inside, atSlot, atEnd]
    have hit : ((seen ++ [slot]) ++ later).findIdx test < ((seen ++ [slot]) ++ later).length := by
      rw [index, atEnd, List.length_append, List.length_append, List.length_singleton]
      omega
    rw [index] at hit
    simp only [if_neg found, index, if_pos hit]

private theorem share_stable {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    AppendStable (fun seen => ((share seen left right).added, (share seen left right).plan.eraseOpen)) := by
  have readout :
      (fun seen => ((share seen left right).added, (share seen left right).plan.eraseOpen)) =
        fun seen =>
          let index := seen.findIdx (fun slot => slot.matches left right)
          (if index < seen.length then [] else [⟨goal, left, right⟩], RawOpenProof.premise index) :=
    funext fun seen => share_readout seen left right
  rw [readout]
  exact shareIndex_stable (⟨goal, left, right⟩ : Slot definition leftContext rightContext)
    (fun slot => slot.matches left right) (slot_matches_self left right)

/-- Sharing the same pair twice allocates no extra slot. -/
theorem share_replay_added {goal : Pattern}
    (seen later : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (share ((seen ++ (share seen left right).added) ++ later) left right).added = [] :=
  congrArg Prod.fst (share_stable left right seen later)

private def stepReadout {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal)
    (seen : List (Slot definition leftContext rightContext)) :
    List (Slot definition leftContext rightContext) × RawOpenProof :=
  let step := leastStep seen left right
  (step.added, step.plan.eraseOpen)

private def listReadout {goals : List Pattern}
    (left : OpenDerivationList definition leftContext goals)
    (right : OpenDerivationList definition rightContext goals)
    (seen : List (Slot definition leftContext rightContext)) :
    List (Slot definition leftContext rightContext) × List RawOpenProof :=
  let step := leastStepList seen left right
  (step.added, step.plans.eraseOpen)

mutual

private theorem stepReadout_stable {goal : Pattern} :
    (left : OpenDerivation definition leftContext goal) →
    (right : OpenDerivation definition rightContext goal) →
      AppendStable (stepReadout left right)
  | .assumption index, right => share_stable (.assumption index) right
  | .byRule _ _ _, .assumption _ => by
      intro seen later
      simp only [stepReadout, leastStep]
      exact share_stable _ _ seen later
  | .byRule (premises := premises) rule app children,
      .byRule (premises := premises') rule' app' children' => by
      by_cases same : rule.ruleId = rule'.ruleId ∧ rule.arguments = rule'.arguments ∧
          premises = premises'
      · have descends :
            stepReadout (.byRule rule app children) (.byRule rule' app' children') =
              fun seen =>
                let step := listReadout children (same.2.2 ▸ children') seen
                (step.1, .node rule step.2) := by
          funext seen
          simp only [stepReadout, listReadout, leastStep]
          rw [dif_pos same]
          rfl
        rw [descends]
        exact (listReadout_stable children (same.2.2 ▸ children')).map (RawOpenProof.node rule)
      · have shares :
            stepReadout (.byRule rule app children) (.byRule rule' app' children') =
              fun seen =>
                let step := share seen (.byRule rule app children) (.byRule rule' app' children')
                (step.added, step.plan.eraseOpen) := by
          funext seen
          simp only [stepReadout, leastStep]
          rw [dif_neg same]
        rw [shares]
        exact share_stable (.byRule rule app children) (.byRule rule' app' children')

private theorem listReadout_stable {goals : List Pattern} :
    (left : OpenDerivationList definition leftContext goals) →
    (right : OpenDerivationList definition rightContext goals) →
      AppendStable (listReadout left right)
  | .nil, .nil => fun _ _ => rfl
  | .cons head tail, .cons head' tail' => by
      have combines : listReadout (.cons head tail) (.cons head' tail') =
          fun seen =>
            let first := stepReadout head head' seen
            let rest := listReadout tail tail' (seen ++ first.1)
            (first.1 ++ rest.1, first.2 :: rest.2) := by
        funext seen
        simp only [listReadout, stepReadout]
        rw [leastStepList_cons]
        simp only [OpenDerivationList.eraseOpen, erase_transportContext,
          erase_transportContextList, weakenSlots, erase_weakenAppend]
      rw [combines]
      exact AppendStable.combine (stepReadout_stable head head')
        (listReadout_stable tail tail') List.cons

end

/-- Generalizing a pair whose own slots are already present allocates nothing. -/
theorem replay_added {goal : Pattern}
    (seen later : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (leastStep ((seen ++ (leastStep seen left right).added) ++ later) left right).added = [] :=
  congrArg Prod.fst (stepReadout_stable left right seen later)

/-- The same replay for an ordered vector of premises. -/
theorem replayList_added {goals : List Pattern}
    (seen later : List (Slot definition leftContext rightContext))
    (left : OpenDerivationList definition leftContext goals)
    (right : OpenDerivationList definition rightContext goals) :
    (leastStepList ((seen ++ (leastStepList seen left right).added) ++ later) left right).added = [] :=
  congrArg Prod.fst (listReadout_stable left right seen later)

/-- Replay preserves rule instances, child order and the exact numeral of every cited slot. -/
theorem replay_eraseOpen {goal : Pattern}
    (seen later : List (Slot definition leftContext rightContext))
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    (leastStep ((seen ++ (leastStep seen left right).added) ++ later) left right).plan.eraseOpen =
      (leastStep seen left right).plan.eraseOpen :=
  congrArg Prod.snd (stepReadout_stable left right seen later)

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

/-! ## Specializing every used obligation -/

private def obligationStep {context : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivationList definition leftContext context)
    (right : OpenDerivationList definition rightContext context) (index : Fin context.length) :
    LeastStep seen (context.get index) :=
  leastStep seen (left.get index) (right.get index)

private def obligationReadouts {context : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivationList definition leftContext context)
    (right : OpenDerivationList definition rightContext context) : List RawOpenProof :=
  List.ofFn fun index => (obligationStep seen left right index).plan.eraseOpen

private theorem obligationReadouts_getD {context : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivationList definition leftContext context)
    (right : OpenDerivationList definition rightContext context)
    (index : Fin context.length) (fallback : RawOpenProof) :
    (obligationReadouts seen left right).getD index.val fallback =
      (obligationStep seen left right index).plan.eraseOpen := by
  have inside : index.val < (obligationReadouts seen left right).length := by
    simpa only [obligationReadouts, List.length_ofFn] using index.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
  simp only [obligationReadouts, List.getElem_ofFn, Option.getD_some]

mutual

private theorem skeletonFixed {context : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivationList definition leftContext context)
    (right : OpenDerivationList definition rightContext context) :
    ∀ {goal : Pattern} (plan : OpenDerivation definition context goal),
      (skeletonStep seen plan left right).added = [] →
      (∀ index ∈ holeOccurrences plan, (obligationStep seen left right index).added = []) ∧
      (skeletonStep seen plan left right).plan.eraseOpen =
        RawOpenProof.substitute (obligationReadouts seen left right) plan.eraseOpen
  | _, .assumption index, done => by
      refine ⟨?_, ?_⟩
      · intro i occurs
        simp only [holeOccurrences, List.mem_singleton] at occurs
        subst i
        exact done
      · simp only [skeletonStep, OpenDerivation.eraseOpen, RawOpenProof.substitute_premise,
          obligationReadouts_getD, obligationStep]
  | _, .byRule rule application children, done => by
      obtain ⟨ready, erased⟩ := skeletonListFixed seen left right children done
      refine ⟨ready, ?_⟩
      simp only [skeletonStep, OpenDerivation.eraseOpen, RawOpenProof.substitute_node, erased]

private theorem skeletonListFixed {context : List Pattern}
    (seen : List (Slot definition leftContext rightContext))
    (left : OpenDerivationList definition leftContext context)
    (right : OpenDerivationList definition rightContext context) :
    ∀ {goals : List Pattern} (plans : OpenDerivationList definition context goals),
      (skeletonStepList seen plans left right).added = [] →
      (∀ index ∈ holeOccurrencesList plans, (obligationStep seen left right index).added = []) ∧
      (skeletonStepList seen plans left right).plans.eraseOpen =
        RawOpenProof.substituteList (obligationReadouts seen left right) plans.eraseOpen
  | _, .nil, _ => by
      simp only [holeOccurrencesList, List.not_mem_nil, false_implies, implies_true, true_and]
      rfl
  | _, .cons head tail, done => by
      rw [skeletonStepList_cons] at done
      obtain ⟨headDone, tailDone⟩ := List.append_eq_nil_iff.mp done
      have tailSeen : seen ++ (skeletonStep seen head left right).added = seen := by
        rw [headDone, List.append_nil]
      rw [tailSeen] at tailDone
      obtain ⟨headReady, headErased⟩ := skeletonFixed seen left right head headDone
      obtain ⟨tailReady, tailErased⟩ := skeletonListFixed seen left right tail tailDone
      refine ⟨?_, ?_⟩
      · intro i occurs
        simp only [holeOccurrencesList, List.mem_append] at occurs
        exact occurs.elim (headReady i) (tailReady i)
      · rw [skeletonStepList_cons]
        simp only [OpenDerivationList.eraseOpen, erase_transportContext,
          erase_transportContextList, weakenSlots, erase_weakenAppend, RawOpenProof.substituteList_cons]
        exact congrArg₂ List.cons headErased
          ((congrArg (fun table =>
            (skeletonStepList table tail left right).plans.eraseOpen) tailSeen).trans tailErased)

end

private theorem eraseOpen_ofFn {context : List Pattern} :
    (goals : List Pattern) →
    (entries : (index : Fin goals.length) →
      OpenDerivation definition context (goals.get index)) →
    (OpenDerivationList.ofFn goals entries).eraseOpen =
      List.ofFn (fun index => (entries index).eraseOpen)
  | [], _ => rfl
  | premise :: premises, entries => by
      rw [List.ofFn_succ]
      have tailErased := eraseOpen_ofFn premises (fun index => entries index.succ)
      exact congrArg (List.cons (entries 0).eraseOpen) tailErased

/-- The least general plan is a unique specialization of every plan that
uses all of its obligations and yields the two input proofs. The substitution
keeps the input plan's binding context and the exact order of its obligations. -/
theorem leastGeneral_specializes_used {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation definition context goal) (used : UsesAll plan)
    (left : OpenDerivationList definition leftContext context)
    (right : OpenDerivationList definition rightContext context) :
    let generalized := leastGeneral (plan.bind left) (plan.bind right)
    ∃! environment : OpenDerivationList definition generalized.obligations context,
      plan.bind environment = generalized.plan ∧
        environment.bind generalized.left = left ∧ environment.bind generalized.right = right := by
  let leftProof := plan.bind left
  let rightProof := plan.bind right
  let slots := (leastStep [] leftProof rightProof).added
  have replay : stepReadout leftProof rightProof slots =
      ([], (leastGeneral leftProof rightProof).plan.eraseOpen) := by
    have law := stepReadout_stable leftProof rightProof [] []
    change stepReadout leftProof rightProof (([] ++ slots) ++ []) =
      ([], (leastGeneral leftProof rightProof).plan.eraseOpen) at law
    simpa only [List.nil_append, List.append_nil] using law
  have ready : (leastStep slots leftProof rightProof).added = [] :=
    congrArg Prod.fst replay
  have recalled : (leastStep slots leftProof rightProof).plan.eraseOpen =
      (leastGeneral leftProof rightProof).plan.eraseOpen :=
    congrArg Prod.snd replay
  have fixed : (skeletonStep slots plan left right).added = [] := by
    rw [skeletonStep_spec]
    exact ready
  obtain ⟨available, erased⟩ := skeletonFixed slots left right plan fixed
  let entry (index : Fin context.length) :
      OpenDerivation definition (obligationsOf slots) (context.get index) :=
    transportContext (by rw [available index (used index), List.append_nil])
      (obligationStep slots left right index).plan
  let environment : OpenDerivationList definition
      (leastGeneral leftProof rightProof).obligations context :=
    OpenDerivationList.ofFn context entry
  have observed : environment.eraseOpen = obligationReadouts slots left right := by
    change (OpenDerivationList.ofFn context entry).eraseOpen = obligationReadouts slots left right
    rw [eraseOpen_ofFn]
    simp only [entry, obligationReadouts, erase_transportContext]
  have specialization :
      plan.bind environment = (leastGeneral leftProof rightProof).plan := by
    apply eraseOpen_injective
    rw [OpenDerivation.eraseOpen_bind, observed, ← erased, skeletonStep_spec]
    exact recalled
  refine ⟨environment, ⟨specialization, ?_, ?_⟩, ?_⟩
  · apply used.bind_injective
    change plan.bind (environment.bind (leastGeneral leftProof rightProof).left) = leftProof
    rw [← OpenDerivation.bind_assoc, specialization, leastGeneral_left]
  · apply used.bind_injective
    change plan.bind (environment.bind (leastGeneral leftProof rightProof).right) = rightProof
    rw [← OpenDerivation.bind_assoc, specialization, leastGeneral_right]
  · intro other same
    exact used.bind_injective (same.1.trans specialization.symm)

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

private def splitPair : OpenDerivation kernelDefinition [A, A] D :=
  .byRule _ (kernelApp (rule := rulePair) (by simp [kernelRules]))
    (.cons (.assumption ⟨0, by decide⟩) (.cons (.assumption ⟨1, by decide⟩) .nil))

private def both (proof : Derivation kernelDefinition A) :
    OpenDerivationList kernelDefinition [] [A, A] :=
  .cons (.ofClosed proof) (.cons (.ofClosed proof) .nil)

example :
    let generalized := leastGeneral (splitPair.bind (both dA₁)) (splitPair.bind (both dA₂))
    ∃ environment : OpenDerivationList kernelDefinition generalized.obligations [A, A],
      environment.eraseOpen = [.premise 0, .premise 0] ∧
        environment.bind generalized.left = both dA₁ ∧
        environment.bind generalized.right = both dA₂ := by
  let generalized := leastGeneral (splitPair.bind (both dA₁)) (splitPair.bind (both dA₂))
  have used : UsesAll splitPair := by
    intro i
    fin_cases i <;> decide
  obtain ⟨environment, agreement, _⟩ :=
    leastGeneral_specializes_used splitPair used (both dA₁) (both dA₂)
  let children : RawOpenProof → List RawOpenProof
    | .premise _ => []
    | .node _ premises => premises
  have expected : children generalized.plan.eraseOpen = [.premise 0, .premise 0] := by
    decide +kernel
  have observed := congrArg (fun plan => children plan.eraseOpen) agreement.1
  change children (splitPair.bind environment).eraseOpen = children generalized.plan.eraseOpen at observed
  rw [expected] at observed
  refine ⟨environment, ?_, agreement.2.1, agreement.2.2⟩
  cases environment with
  | cons first rest =>
      cases rest with
      | cons second rest => cases rest; exact observed

example :
    let first : Slot kernelDefinition [] [] := ⟨A, .ofClosed dA₁, .ofClosed dA₂⟩
    let second : Slot kernelDefinition [] [] := ⟨A, .ofClosed dA₂, .ofClosed dA₁⟩
    (share [first, second] first.left first.right).plan.eraseOpen = .premise 0 ∧
      (share [second, first] first.left first.right).plan.eraseOpen = .premise 1 := by
  decide +kernel

/-- **Negative.**  `pair(a,b)` and `pair(b,a)` are two distinct erasure pairs,
so least general generalization still opens two slots. -/
theorem distinct_slots :
    (leastGeneral AntiUnification.pairOneTwo AntiUnification.pairTwoOne).obligations = [A, A] ∧
      (holeOccurrences
        (leastGeneral AntiUnification.pairOneTwo AntiUnification.pairTwoOne).plan).map Fin.val =
        [0, 1] := by
  decide

/-- The first-slot plan observes changes to that proof and ignores the other slot. -/
example :
    let plan : OpenDerivation kernelDefinition [A, A] A := .assumption ⟨0, by decide⟩
    let one : OpenDerivation kernelDefinition [] A := .ofClosed dA₁
    let two : OpenDerivation kernelDefinition [] A := .ofClosed dA₂
    let given : OpenDerivationList kernelDefinition [] [A, A] := .cons one (.cons one .nil)
    plan.bind given = plan.bind (.cons one (.cons two .nil)) ∧
      plan.bind given ≠ plan.bind (.cons two (.cons one .nil)) := by
  dsimp only
  constructor
  · apply (bind_eq_iff_citations _ _ _).mpr
    intro index cited
    simp only [holeOccurrences, List.mem_singleton] at cited
    subst cited
    rfl
  · intro same
    have sameWire := congrArg OpenDerivation.eraseOpen same
    exact (by decide : (OpenDerivation.ofClosed (context := []) dA₁).eraseOpen ≠
      (OpenDerivation.ofClosed (context := []) dA₂).eraseOpen) sameWire

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
