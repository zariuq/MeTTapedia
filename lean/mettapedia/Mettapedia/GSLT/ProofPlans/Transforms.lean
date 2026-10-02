import Mettapedia.GSLT.ProofPlans.Derivations
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchMachine

/-!
# Plan transforms and what they preserve

A plan transform changes a plan and owes obligations instead of claiming to
preserve truth.  Each transform below is stated with what it preserves and
with a naive variant that loses it.

**Generalization (anti-unification).**  `antiUnify` generalizes two plans for
one goal: where they apply the same rule it keeps the rule, and where they
differ it leaves a *method slot*, a new obligation for the judgment at that
position.  It returns the generalization and the two substitutions that
recover the originals (`antiUnify_left`, `antiUnify_right`).  Hence each
original is an instance of the generalization and its completion space is
contained in the generalization's (`antiUnify_refines_left`,
`antiUnify_refines_right`); a plan anti-unified with itself gets one slot
per obligation occurrence and no other (`antiUnify_self_obligations`).
*Naive control*: identifying two method slots of the same judgment loses an
original: `pair(axA₁, axA₂)` is a completion of the correct generalization
`pair(?A₀, ?A₁)` and not of the merged `pair(?A, ?A)`
(`AntiUnification.merged_slots_lose_original`).

**Abduction (backward chaining).**  `abduce` replaces the first obligation by a
rule concluding it; the rule's premises become the new obligations.  Abduction
refines (`abduce_refines`), and its new obligations are exactly the missing
premises: the completions of the abduced plan are the completions of the
original whose first obligation is discharged through that rule
(`abduce_discharge`), and from the assumed goal they are exactly the
derivations ending with that rule (`abduce_assume_exact`).
*Naive control*: dropping the residual obligation is unsound.  Backward
chaining from `C` through `xc : X ⊢ C` leaves the residual `X`, which the
countermodel refutes; no derivation of `C` ends with `xc`
(`Abduction.no_derivation_through_xc`), and the raw node `xc` without its
premise is rejected by the checker (`Abduction.naive_abduction_rejected`).

**Blending (amalgamation along shared obligations).**  `blend` joins two plans
over a shared obligation context `K`, keeping their private obligations
apart.  Discharging the blend discharges both plans with the same evidence for
`K` (`blend_bind`), and the joint completions of the blend are exactly the
pairs of completions that agree on `K` (`blend_completion_iff`): the pushout
of plans along `K` has the fibred product of completion spaces.
*Controls*: the blend is strictly finer than the product
(`Blending.mixed_pair_not_blended`), and identifying obligations of different
judgments without a coercion is unsound: `CastAB` and `C` are derivable and
`G` is not, so no coercion from `CastAB` to `CastCG` exists
(`Blending.no_silent_identification`).

**Bypass (explicit cast).**  A bypass from an established `φ` to a target `ψ`
is a plan through a cast rule `Cast(φ, ψ), φ ⊢ ψ` whose obligation is the cast.
The target is closed exactly when the cast obligation is
(`Bypass.bypass_closed_iff`): no cast is discharged silently.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.OSLF.Programs

variable {definition : ValidatedCalculusLanguageDef}

/-! ## Generalization -/

/-- A generalization of two open derivations of one goal: a plan over new
obligations and the two substitutions recovering the originals. -/
structure Generalization (definition : ValidatedCalculusLanguageDef)
    (leftContext rightContext : List Pattern) (goal : Pattern) where
  obligations : List Pattern
  plan : OpenDerivation definition obligations goal
  left : OpenDerivationList definition leftContext obligations
  right : OpenDerivationList definition rightContext obligations

/-- A generalization of two ordered vectors of open derivations. -/
structure GeneralizationList (definition : ValidatedCalculusLanguageDef)
    (leftContext rightContext : List Pattern) (goals : List Pattern) where
  obligations : List Pattern
  plans : OpenDerivationList definition obligations goals
  left : OpenDerivationList definition leftContext obligations
  right : OpenDerivationList definition rightContext obligations

/-- The root rule of an open derivation, with its children. -/
def rootRule? {context : List Pattern} {goal : Pattern} :
    OpenDerivation definition context goal →
      Option (Σ (ruleInstance : RuleInstance) (premises : List Pattern),
        PLift (RuleApplication definition ruleInstance premises goal) ×
          OpenDerivationList definition context premises)
  | .assumption _ => none
  | .byRule ruleInstance application children =>
      some ⟨ruleInstance, _, ⟨application⟩, children⟩

theorem eq_of_rootRule? {context : List Pattern} {goal : Pattern}
    {derivation : OpenDerivation definition context goal} {ruleInstance : RuleInstance}
    {premises : List Pattern}
    {application : PLift (RuleApplication definition ruleInstance premises goal)}
    {children : OpenDerivationList definition context premises}
    (found : rootRule? derivation = some ⟨ruleInstance, premises, application, children⟩) :
    derivation = .byRule ruleInstance application.down children := by
  cases derivation with
  | assumption _ => simp [rootRule?] at found
  | byRule ruleInstance' application' children' =>
      simp only [rootRule?, Option.some.injEq, Sigma.mk.injEq] at found
      obtain ⟨rfl, found⟩ := found
      simp only [heq_eq_eq, Sigma.mk.injEq] at found
      obtain ⟨rfl, found⟩ := found
      simp only [heq_eq_eq, Prod.mk.injEq] at found
      obtain ⟨-, rfl⟩ := found
      rfl

/-- The generalization that leaves the whole derivation as one method slot. -/
def slot {leftContext rightContext : List Pattern} {goal : Pattern}
    (left : OpenDerivation definition leftContext goal)
    (right : OpenDerivation definition rightContext goal) :
    Generalization definition leftContext rightContext goal :=
  ⟨[goal], .assumption ⟨0, by simp⟩, .cons left .nil, .cons right .nil⟩

mutual

/-- **Anti-unification of two plans for one goal.**  Equal root rules are
kept; different ones become a method slot. -/
def antiUnify {leftContext rightContext : List Pattern} :
    {goal : Pattern} → OpenDerivation definition leftContext goal →
      OpenDerivation definition rightContext goal →
        Generalization definition leftContext rightContext goal
  | _, .assumption index, right => slot (.assumption index) right
  | _, .byRule (premises := premises) ruleInstance application children, right =>
      match rootRule? right with
      | some ⟨ruleInstance', premises', _, children'⟩ =>
          if same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
              ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises' then
            { obligations := (antiUnifyList children (same.2.2 ▸ children')).obligations
              plan := .byRule ruleInstance application
                (antiUnifyList children (same.2.2 ▸ children')).plans
              left := (antiUnifyList children (same.2.2 ▸ children')).left
              right := (antiUnifyList children (same.2.2 ▸ children')).right }
          else
            slot (.byRule ruleInstance application children) right
      | none => slot (.byRule ruleInstance application children) right

/-- Anti-unification of two ordered vectors. -/
def antiUnifyList {leftContext rightContext : List Pattern} :
    {goals : List Pattern} → OpenDerivationList definition leftContext goals →
      OpenDerivationList definition rightContext goals →
        GeneralizationList definition leftContext rightContext goals
  | _, .nil, _ => ⟨[], .nil, .nil, .nil⟩
  | _, .cons head tail, .cons head' tail' =>
      { obligations := (antiUnify head head').obligations ++ (antiUnifyList tail tail').obligations
        plans := .cons ((antiUnify head head').plan.bind (OpenDerivationList.leftProjection _ _))
          ((antiUnifyList tail tail').plans.bind (OpenDerivationList.rightProjection _ _))
        left := (antiUnify head head').left.append (antiUnifyList tail tail').left
        right := (antiUnify head head').right.append (antiUnifyList tail tail').right }

end

/-- Rule instances with equal identifiers and arguments are equal. -/
theorem ruleInstance_ext {first second : RuleInstance} (sameId : first.ruleId = second.ruleId)
    (sameArguments : first.arguments = second.arguments) : first = second := by
  cases first
  cases second
  simp_all

mutual

/-- **The left substitution recovers the left plan.** -/
theorem antiUnify_left {leftContext rightContext : List Pattern} :
    {goal : Pattern} → (left : OpenDerivation definition leftContext goal) →
      (right : OpenDerivation definition rightContext goal) →
      (antiUnify left right).plan.bind (antiUnify left right).left = left
  | _, .assumption _, _ => rfl
  | _, .byRule _ _ _, .assumption _ => rfl
  | _, .byRule (premises := premises) ruleInstance application children,
      .byRule (premises := premises') ruleInstance' application' children' => by
      simp only [antiUnify, rootRule?]
      by_cases same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
          ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises'
      · rw [dif_pos same]
        simp only [OpenDerivation.bind]
        rw [antiUnifyList_left children]
      · rw [dif_neg same]
        rfl

/-- Pointwise form. -/
theorem antiUnifyList_left {leftContext rightContext : List Pattern} :
    {goals : List Pattern} → (left : OpenDerivationList definition leftContext goals) →
      (right : OpenDerivationList definition rightContext goals) →
      (antiUnifyList left right).plans.bind (antiUnifyList left right).left = left
  | _, .nil, .nil => rfl
  | _, .cons head tail, .cons head' tail' => by
      show OpenDerivationList.cons
          (((antiUnify head head').plan.bind (OpenDerivationList.leftProjection _ _)).bind
            ((antiUnify head head').left.append (antiUnifyList tail tail').left))
          (((antiUnifyList tail tail').plans.bind (OpenDerivationList.rightProjection _ _)).bind
            ((antiUnify head head').left.append (antiUnifyList tail tail').left)) = _
      rw [OpenDerivation.bind_assoc, OpenDerivationList.leftProjection_bind_append,
        antiUnify_left head head', OpenDerivationList.bind_assoc,
        OpenDerivationList.rightProjection_bind_append, antiUnifyList_left tail tail']

end

mutual

/-- **The right substitution recovers the right plan.** -/
theorem antiUnify_right {leftContext rightContext : List Pattern} :
    {goal : Pattern} → (left : OpenDerivation definition leftContext goal) →
      (right : OpenDerivation definition rightContext goal) →
      (antiUnify left right).plan.bind (antiUnify left right).right = right
  | _, .assumption _, _ => rfl
  | _, .byRule _ _ _, .assumption _ => rfl
  | _, .byRule (premises := premises) ruleInstance application children,
      .byRule (premises := premises') ruleInstance' application' children' => by
      simp only [antiUnify, rootRule?]
      by_cases same : ruleInstance.ruleId = ruleInstance'.ruleId ∧
          ruleInstance.arguments = ruleInstance'.arguments ∧ premises = premises'
      · rw [dif_pos same]
        obtain ⟨sameId, sameArguments, samePremises⟩ := same
        have sameInstance := ruleInstance_ext sameId sameArguments
        subst sameInstance
        subst samePremises
        simp only [OpenDerivation.bind]
        rw [antiUnifyList_right children children']
      · rw [dif_neg same]
        rfl

/-- Pointwise form. -/
theorem antiUnifyList_right {leftContext rightContext : List Pattern} :
    {goals : List Pattern} → (left : OpenDerivationList definition leftContext goals) →
      (right : OpenDerivationList definition rightContext goals) →
      (antiUnifyList left right).plans.bind (antiUnifyList left right).right = right
  | _, .nil, .nil => rfl
  | _, .cons head tail, .cons head' tail' => by
      show OpenDerivationList.cons
          (((antiUnify head head').plan.bind (OpenDerivationList.leftProjection _ _)).bind
            ((antiUnify head head').right.append (antiUnifyList tail tail').right))
          (((antiUnifyList tail tail').plans.bind (OpenDerivationList.rightProjection _ _)).bind
            ((antiUnify head head').right.append (antiUnifyList tail tail').right)) = _
      rw [OpenDerivation.bind_assoc, OpenDerivationList.leftProjection_bind_append,
        antiUnify_right head head', OpenDerivationList.bind_assoc,
        OpenDerivationList.rightProjection_bind_append, antiUnifyList_right tail tail']

end

open OpenSearchMachine in
mutual

/-- **Identical plans are generalized without spurious slots**: each
obligation occurrence becomes one slot, and nothing else does. -/
theorem antiUnify_self_obligations {context : List Pattern} :
    {goal : Pattern} → (plan : OpenDerivation definition context goal) →
      (antiUnify plan plan).obligations.length = (holeOccurrences plan).length
  | _, .assumption _ => rfl
  | _, .byRule (premises := premises) ruleInstance application children => by
      simp only [antiUnify, rootRule?, and_self, dite_true]
      exact antiUnifyList_self_obligations children

/-- Pointwise form. -/
theorem antiUnifyList_self_obligations {context : List Pattern} :
    {goals : List Pattern} → (plans : OpenDerivationList definition context goals) →
      (antiUnifyList plans plans).obligations.length = (holeOccurrencesList plans).length
  | _, .nil => rfl
  | _, .cons head tail => by
      show ((antiUnify head head).obligations ++ (antiUnifyList tail tail).obligations).length =
        (holeOccurrences head ++ holeOccurrencesList tail).length
      rw [List.length_append, List.length_append, antiUnify_self_obligations head,
        antiUnifyList_self_obligations tail]

end

variable {object : Object}

/-- The generalization as a proof plan. -/
def Generalization.toPlan {leftContext rightContext : List Pattern} {goal : Pattern}
    (generalization : Generalization object.definition leftContext rightContext goal) :
    DerivationPlan object goal :=
  ofOpen generalization.plan

/-- **The left plan is an instance of the generalization.** -/
theorem antiUnify_instance_left {leftContext rightContext : List Pattern} {goal : Pattern}
    (left : OpenDerivation object.definition leftContext goal)
    (right : OpenDerivation object.definition rightContext goal) :
    InstanceOf (ofOpen left) (antiUnify left right).toPlan :=
  ⟨fun index => (antiUnify left right).left.get index,
    ((substitute_eq_bind _ _).trans (antiUnify_left left right)).symm⟩

/-- **The right plan is an instance of the generalization.** -/
theorem antiUnify_instance_right {leftContext rightContext : List Pattern} {goal : Pattern}
    (left : OpenDerivation object.definition leftContext goal)
    (right : OpenDerivation object.definition rightContext goal) :
    InstanceOf (ofOpen right) (antiUnify left right).toPlan :=
  ⟨fun index => (antiUnify left right).right.get index,
    ((substitute_eq_bind _ _).trans (antiUnify_right left right)).symm⟩

/-- **The completion space of the generalization contains the left plan's.** -/
theorem antiUnify_refines_left {leftContext rightContext : List Pattern} {goal : Pattern}
    (left : OpenDerivation object.definition leftContext goal)
    (right : OpenDerivation object.definition rightContext goal) :
    Completion.Refines (Completes (derivationClone object)) (ofOpen left)
      (antiUnify left right).toPlan :=
  (antiUnify_instance_left left right).refines

/-- **The completion space of the generalization contains the right plan's.** -/
theorem antiUnify_refines_right {leftContext rightContext : List Pattern} {goal : Pattern}
    (left : OpenDerivation object.definition leftContext goal)
    (right : OpenDerivation object.definition rightContext goal) :
    Completion.Refines (Completes (derivationClone object)) (ofOpen right)
      (antiUnify left right).toPlan :=
  (antiUnify_instance_right left right).refines

/-! ## Abduction -/

/-- **Abduction**: backward chaining from the first obligation through a rule;
the rule's premises become the new first obligations. -/
def abduce {head goal : Pattern} {context premises : List Pattern}
    (plan : OpenDerivation definition (head :: context) goal) (ruleInstance : RuleInstance)
    (application : RuleApplication definition ruleInstance premises head) :
    OpenDerivation definition (premises ++ context) goal :=
  plan.bind (.cons (.byRule ruleInstance application
      (OpenDerivationList.leftProjection premises context))
    (OpenDerivationList.rightProjection premises context))

/-- **Discharging the abduced plan discharges the original through the
rule.** -/
theorem abduce_bind {head goal : Pattern} {context premises target : List Pattern}
    (plan : OpenDerivation definition (head :: context) goal) (ruleInstance : RuleInstance)
    (application : RuleApplication definition ruleInstance premises head)
    (premiseEvidence : OpenDerivationList definition target premises)
    (contextEvidence : OpenDerivationList definition target context) :
    (abduce plan ruleInstance application).bind (premiseEvidence.append contextEvidence) =
      plan.bind (.cons (.byRule ruleInstance application premiseEvidence) contextEvidence) := by
  unfold abduce
  rw [OpenDerivation.bind_assoc]
  simp only [OpenDerivationList.bind, OpenDerivation.bind,
    OpenDerivationList.leftProjection_bind_append,
    OpenDerivationList.rightProjection_bind_append]

/-- **Abduction refines the completion space.** -/
theorem abduce_refines {head goal : Pattern} {context premises : List Pattern}
    (plan : OpenDerivation object.definition (head :: context) goal)
    (ruleInstance : RuleInstance)
    (application : RuleApplication object.definition ruleInstance premises head) :
    Completion.Refines (Completes (derivationClone object))
      (ofOpen (abduce plan ruleInstance application)) (ofOpen plan) :=
  refines_bind (ofOpen plan) _

/-- **The residual obligations of abduction are exactly the missing premises**:
discharging them, with evidence for the remaining obligations, is discharging
the original plan through the rule. -/
theorem abduce_discharge {head goal : Pattern} {context premises : List Pattern}
    (plan : OpenDerivation object.definition (head :: context) goal)
    (ruleInstance : RuleInstance)
    (application : RuleApplication object.definition ruleInstance premises head)
    (premiseEvidence : OpenDerivationList object.definition [] premises)
    (contextEvidence : OpenDerivationList object.definition [] context) :
    ((abduce plan ruleInstance application).bind
        (premiseEvidence.append contextEvidence)).close =
      (plan.bind (.cons (.byRule ruleInstance application premiseEvidence)
        contextEvidence)).close := by
  rw [abduce_bind]

/-- **From the assumed goal, abduction is exact**: the completions of the
abduced plan are exactly the derivations of the goal whose last step is the
rule. -/
theorem abduce_assume_exact {goal : Pattern} {premises : List Pattern}
    (ruleInstance : RuleInstance)
    (application : RuleApplication object.definition ruleInstance premises goal)
    (completion : OpenDerivation object.definition [] goal) :
    completion ∈ completions (derivationClone object)
        (ofOpen (abduce (.assumption ⟨0, by simp⟩ : OpenDerivation object.definition [goal]
          goal) ruleInstance application)) ↔
      ∃ children : OpenDerivationList object.definition [] premises,
        completion = .byRule ruleInstance application children := by
  rw [mem_completions_iff_bind]
  constructor
  · rintro ⟨evidence, rfl⟩
    have split := OpenDerivationList.append_take (firstGoals := premises) (secondGoals := [])
      evidence
    have rightNil : OpenDerivationList.takeRight premises [] evidence = .nil :=
      ClassifyingContext.OpenDerivationList.eq_nil _
    refine ⟨OpenDerivationList.takeLeft premises [] evidence, ?_⟩
    change OpenDerivation.bind (abduce _ ruleInstance application) evidence = _
    conv_lhs => rw [← split]
    rw [abduce_bind, rightNil]
    rfl
  · rintro ⟨children, rfl⟩
    refine ⟨children.append .nil, ?_⟩
    change OpenDerivation.bind (abduce _ ruleInstance application) (children.append .nil) = _
    rw [abduce_bind]
    rfl

/-! ## Blending -/

/-- The obligations of the left plan inside the blended context. -/
def blendLeftEnv (shared first second : List Pattern) :
    OpenDerivationList definition (shared ++ (first ++ second)) (shared ++ first) :=
  (OpenDerivationList.leftProjection shared (first ++ second)).append
    ((OpenDerivationList.leftProjection first second).bind
      (OpenDerivationList.rightProjection shared (first ++ second)))

/-- The obligations of the right plan inside the blended context. -/
def blendRightEnv (shared first second : List Pattern) :
    OpenDerivationList definition (shared ++ (first ++ second)) (shared ++ second) :=
  (OpenDerivationList.leftProjection shared (first ++ second)).append
    ((OpenDerivationList.rightProjection first second).bind
      (OpenDerivationList.rightProjection shared (first ++ second)))

/-- **Blend two plans along their shared obligations** `shared`; private
obligations stay apart. -/
def blend {shared first second : List Pattern} {leftGoal rightGoal : Pattern}
    (left : OpenDerivation definition (shared ++ first) leftGoal)
    (right : OpenDerivation definition (shared ++ second) rightGoal) :
    OpenDerivationList definition (shared ++ (first ++ second)) [leftGoal, rightGoal] :=
  .cons (left.bind (blendLeftEnv shared first second))
    (.cons (right.bind (blendRightEnv shared first second)) .nil)

/-- **Discharging the blend discharges both plans with the same shared
evidence.** -/
theorem blend_bind {shared first second target : List Pattern} {leftGoal rightGoal : Pattern}
    (left : OpenDerivation definition (shared ++ first) leftGoal)
    (right : OpenDerivation definition (shared ++ second) rightGoal)
    (sharedEvidence : OpenDerivationList definition target shared)
    (firstEvidence : OpenDerivationList definition target first)
    (secondEvidence : OpenDerivationList definition target second) :
    (blend left right).bind (sharedEvidence.append (firstEvidence.append secondEvidence)) =
      .cons (left.bind (sharedEvidence.append firstEvidence))
        (.cons (right.bind (sharedEvidence.append secondEvidence)) .nil) := by
  simp only [blend, OpenDerivationList.bind, OpenDerivation.bind_assoc, blendLeftEnv,
    blendRightEnv, OpenDerivationList.append_bind, OpenDerivationList.bind_assoc,
    OpenDerivationList.leftProjection_bind_append, OpenDerivationList.rightProjection_bind_append]

/-- **The completions of the blend are the pairs of completions that agree on
the shared obligations**: the fibred product of the completion spaces. -/
theorem blend_completion_iff {shared first second : List Pattern} {leftGoal rightGoal : Pattern}
    (left : OpenDerivation definition (shared ++ first) leftGoal)
    (right : OpenDerivation definition (shared ++ second) rightGoal)
    (leftCompletion : OpenDerivation definition [] leftGoal)
    (rightCompletion : OpenDerivation definition [] rightGoal) :
    (∃ evidence : OpenDerivationList definition [] (shared ++ (first ++ second)),
        (blend left right).bind evidence = .cons leftCompletion (.cons rightCompletion .nil)) ↔
      ∃ (sharedEvidence : OpenDerivationList definition [] shared)
        (firstEvidence : OpenDerivationList definition [] first)
        (secondEvidence : OpenDerivationList definition [] second),
        left.bind (sharedEvidence.append firstEvidence) = leftCompletion ∧
          right.bind (sharedEvidence.append secondEvidence) = rightCompletion := by
  constructor
  · rintro ⟨evidence, equation⟩
    have outer := OpenDerivationList.append_take (firstGoals := shared)
      (secondGoals := first ++ second) evidence
    have inner := OpenDerivationList.append_take (firstGoals := first) (secondGoals := second)
      (OpenDerivationList.takeRight shared (first ++ second) evidence)
    refine ⟨OpenDerivationList.takeLeft shared (first ++ second) evidence,
      OpenDerivationList.takeLeft first second
        (OpenDerivationList.takeRight shared (first ++ second) evidence),
      OpenDerivationList.takeRight first second
        (OpenDerivationList.takeRight shared (first ++ second) evidence), ?_⟩
    rw [← outer, ← inner, blend_bind] at equation
    injection equation with _ _ leftEq rest
    injection rest with _ _ rightEq _
    exact ⟨leftEq, rightEq⟩
  · rintro ⟨sharedEvidence, firstEvidence, secondEvidence, leftEq, rightEq⟩
    refine ⟨sharedEvidence.append (firstEvidence.append secondEvidence), ?_⟩
    rw [blend_bind, leftEq, rightEq]

/-! ## Controls -/

namespace AntiUnification

open Fixture

/-- `pair(axA₁, axA₂)`. -/
def pairOneTwo : OpenDerivation kernelDefinition [] D :=
  .byRule _ (kernelApp (rule := rulePair) (by simp [kernelRules]))
    (.cons (OpenDerivation.ofClosed dA₁) (.cons (OpenDerivation.ofClosed dA₂) .nil))

/-- `pair(axA₂, axA₁)`. -/
def pairTwoOne : OpenDerivation kernelDefinition [] D :=
  .byRule _ (kernelApp (rule := rulePair) (by simp [kernelRules]))
    (.cons (OpenDerivation.ofClosed dA₂) (.cons (OpenDerivation.ofClosed dA₁) .nil))

/-- **Positive.**  Anti-unifying `pair(axA₁, axA₂)` and `pair(axA₂, axA₁)` keeps
the rule `pair` (one rule node) and leaves two distinct method slots. -/
theorem generalization_is_pair :
    (antiUnify pairOneTwo pairTwoOne).obligations = [A, A] ∧
      (antiUnify pairOneTwo pairTwoOne).plan.ruleCount = 1 ∧
      (OpenSearchMachine.holeOccurrences (antiUnify pairOneTwo pairTwoOne).plan).map Fin.val =
        [0, 1] := by
  decide

/-- **Positive: the method slot of two plans for `C`.**  `bc(ab(axA₁))` and
`bc(axB)` generalize to `bc(?B)`: the step producing `B` becomes a slot. -/
theorem methodSlot :
    (antiUnify (OpenDerivation.ofClosed (context := []) dC)
        (OpenDerivation.ofClosed (context := []) (.byRule _
          (kernelApp (rule := ruleBC) (by simp [kernelRules])) (.cons dB .nil)))).obligations =
      [B] ∧
    (antiUnify (OpenDerivation.ofClosed (context := []) dC)
        (OpenDerivation.ofClosed (context := []) (.byRule _
          (kernelApp (rule := ruleBC) (by simp [kernelRules])) (.cons dB .nil)))).plan.ruleCount =
      1 := by
  decide

/-- **Naive control.**  Merging the two method slots of the same judgment into
one obligation loses an original: `pair(axA₁, axA₂)` is a completion of the
correct generalization `pair(?A₀, ?A₁)` and not of `pair(?A, ?A)`. -/
theorem merged_slots_lose_original :
    pairOneTwo ∈ completions (derivationClone kernel) (ofOpen planPair) ∧
      pairOneTwo ∉ completions (derivationClone kernel) (ofOpen planPairShared) := by
  constructor
  · exact (mem_completions_iff_bind _ _).mpr
      ⟨.cons (OpenDerivation.ofClosed dA₁) (.cons (OpenDerivation.ofClosed dA₂) .nil), rfl⟩
  · intro member
    obtain ⟨evidence, equation⟩ := mem_completions_iff.mp member
    have bound : OpenDerivation.bind planPairShared
        (OpenDerivationList.ofFn [A] evidence) = pairOneTwo := equation
    injection bound with _ _ _ children
    injection children with _ _ first rest
    injection rest with _ _ second _
    have same : OpenDerivation.ofClosed (context := []) dA₁ = OpenDerivation.ofClosed dA₂ :=
      first.symm.trans second
    exact PlanControls.dA₁_ne_dA₂ (ofClosed_injective same)

end AntiUnification

namespace Abduction

open Fixture

/-- **Positive.**  Abducing `ab : A ⊢ B` from the assumed `B` gives the plan
`ab(?A)`. -/
theorem abduce_ab :
    abduce (.assumption ⟨0, by simp⟩ : OpenDerivation kernelDefinition [B] B)
      (ruleInstance ruleAB) (kernelApp (rule := ruleAB) (by simp [kernelRules])) = planAB := rfl

/-- **Negative control.**  No derivation of `C` ends with `xc`: its premise
`X` is refuted by the countermodel.  Backward chaining through `xc` must keep
the residual obligation `X`; dropping it would claim a derivation that does not
exist. -/
theorem no_derivation_through_xc :
    ∀ derivation : Derivation kernelDefinition C,
      ¬ ∃ children : DerivationList kernelDefinition [X],
        derivation = .byRule (ruleInstance ruleXC)
          (kernelApp (rule := ruleXC) (by simp [kernelRules])) children := by
  rintro derivation ⟨children, -⟩
  cases children with
  | cons premise _ => exact no_derivation_X premise

/-- **The naive transform is rejected by the checker.**  Dropping the residual
of `xc` leaves the raw node `xc` without its premise, which the checker rejects
for `C`. -/
theorem naive_abduction_rejected :
    checkOpenRaw kernelDefinition [] C (.node (ruleInstance ruleXC) []) = false := by
  rw [checkOpenRaw, instantiate_kernel (rule := ruleXC) (by simp [kernelRules])]
  simp [checkOpenRawChildren, ruleXC, groundRule]

/-- The abduced plan `xc(?X)` has no completion. -/
theorem abduced_xc_dead :
    ∀ completion, completion ∉ completions (derivationClone kernel) (ofOpen planXC) :=
  PlanControls.planXC_no_completion

end Abduction

namespace Blending

open Fixture

/-- `ab(?A)` with shared obligation `A`. -/
def leftShared : OpenDerivation kernelDefinition ([A] ++ []) B := planAB

/-- `bc(ab(?A))` with shared obligation `A`. -/
def rightShared : OpenDerivation kernelDefinition ([A] ++ []) C := planC

/-- **Positive.**  Blending along `A` discharges both plans with one
derivation of `A`. -/
theorem blended_pair :
    (blend leftShared rightShared).bind
        ((OpenDerivationList.cons (OpenDerivation.ofClosed dA₁) .nil).append
          ((OpenDerivationList.nil).append .nil)) =
      .cons (OpenDerivation.ofClosed (context := []) dBA₁)
        (.cons (OpenDerivation.ofClosed (context := []) dC) .nil) := by
  rw [blend_bind]
  rfl

/-- **The blend is finer than the product.**  `ab(axA₁)` and `bc(ab(axA₂))`
complete the two plans separately, but disagree on the shared `A`. -/
theorem mixed_pair_not_blended :
    ¬ ∃ evidence : OpenDerivationList kernelDefinition [] ([A] ++ ([] ++ [])),
      (blend leftShared rightShared).bind evidence =
        .cons (OpenDerivation.ofClosed (context := []) dBA₁)
          (.cons (OpenDerivation.ofClosed (context := []) (.byRule _ (kernelApp (rule := ruleBC)
            (by simp [kernelRules])) (.cons dBA₂ .nil))) .nil) := by
  rw [blend_completion_iff]
  rintro ⟨sharedEvidence, firstEvidence, secondEvidence, leftEq, rightEq⟩
  cases sharedEvidence with
  | cons sharedA rest =>
      cases rest
      cases firstEvidence
      cases secondEvidence
      have leftA : sharedA = OpenDerivation.ofClosed dA₁ := by
        injection leftEq with _ _ _ children
        injection children
      have rightA : sharedA = OpenDerivation.ofClosed dA₂ := by
        injection rightEq with _ _ _ children
        injection children with _ _ abChild _
        injection abChild with _ _ _ grandchildren
        injection grandchildren
      exact PlanControls.dA₁_ne_dA₂ (ofClosed_injective (leftA.symm.trans rightA))

/-- **Negative control: no silent identification.**  `CastAB` and `C` are
derivable and `G` is not; so no coercion turns evidence for `CastAB` into
evidence for `CastCG`, and a blend that identified the two obligations would
derive `G`. -/
theorem no_silent_identification :
    Nonempty (Derivation kernelDefinition CastAB) ∧ Nonempty (Derivation kernelDefinition C) ∧
      ¬ Nonempty (Derivation kernelDefinition CastAB → Derivation kernelDefinition CastCG) :=
  ⟨⟨dCastAB⟩, ⟨dC⟩, fun ⟨coerce⟩ => no_derivation_castCG (coerce dCastAB)⟩

end Blending

namespace Bypass

open Fixture

/-- **A bypass is closed exactly when its cast obligation is.** -/
theorem bypass_closed_iff :
    (completions (derivationClone kernel) (ofOpen planBypass)).Nonempty ↔
      Nonempty (Derivation kernelDefinition CastCG) := by
  rw [completions_nonempty_iff]
  constructor
  · rintro ⟨evidence⟩
    exact ⟨(evidence ⟨0, Nat.one_pos⟩).close⟩
  · rintro ⟨derivation⟩
    exact ⟨fun index => Fin.cases (motive := fun index =>
      (derivationClone kernel).Hom [] ((ofOpen planBypass).obligations.get index))
      (OpenDerivation.ofClosed derivation) (fun impossible => Fin.elim0 impossible) index⟩

/-- **Negative.**  The bypass from `C` to `G` never closes: its cast
obligation is refuted, and the refutation names the cast (position `0`). -/
theorem bypass_blamed :
    ∀ completion, completion ∉ completions (derivationClone kernel) (ofOpen planBypass) :=
  PlanControls.kernelPlanTruth.completions_empty (ofOpen planBypass) ⟨0, Nat.one_pos⟩
    fun holds => holds.2.1 rfl

/-- **Positive.**  The cast from `A` to `B` closes with its obligation. -/
theorem castAB_closes :
    OpenDerivation.ofClosed (planCastAB.discharge (.cons dCastAB .nil)) ∈
      completions (derivationClone kernel) (ofOpen planCastAB) :=
  discharge_mem_completions (ofOpen planCastAB) _

end Bypass

end Mettapedia.GSLT.ProofPlans
