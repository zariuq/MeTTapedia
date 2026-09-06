import Mettapedia.Languages.SUMO.Native.Checker
import Mettapedia.GSLT.Core.GSLT

/-!
# Native SUMO proof search as a GSLT

The native calculus induces a backward proof-search GSLT directly over scoped
SUMO sequents.  One rewrite replaces the first outstanding sequent by the
premises of one native logical rule.  No target logic, generic rule identifier,
or imported theorem participates in this relation.

Because sequents package their ordinary-variable and exact-row scopes, one
proof-search state may contain obligations at different binder depths.  This
is required by the native quantifier rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.ProofSearch

open Mettapedia.GSLT
open Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral

/-- A native SUMO sequent packages its two scopes, assumptions, and goal. -/
structure Sequent (Symbol : Type uSymbol) (Literal : Type uLiteral) where
  ordinary : Nat
  rows : Nat
  assumptions : List (Formula Symbol Literal ordinary rows)
  conclusion : Formula Symbol Literal ordinary rows

namespace Sequent

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}

/-- Construct a sequent while inferring both intrinsic scope sizes. -/
def of {ordinary rows : Nat}
    (assumptions : List (Formula Symbol Literal ordinary rows))
    (conclusion : Formula Symbol Literal ordinary rows) :
    Sequent Symbol Literal :=
  ⟨ordinary, rows, assumptions, conclusion⟩

/-- Native derivability of a packaged sequent. -/
abbrev Derivable (sequent : Sequent Symbol Literal) : Prop :=
  Derivation Symbol Literal sequent.assumptions sequent.conclusion

end Sequent

set_option autoImplicit true in
/-- One native rule application, indexed by its conclusion and exact ordered
premise list. -/
inductive RuleApplication (Symbol : Type uSymbol) (Literal : Type uLiteral) :
    Sequent Symbol Literal -> List (Sequent Symbol Literal) -> Prop where
  | hypothesis (member : body ∈ assumptions) :
      RuleApplication Symbol Literal (Sequent.of assumptions body) []
  | topIntroduction :
      RuleApplication Symbol Literal (Sequent.of assumptions .top) []
  | bottomElimination :
      RuleApplication Symbol Literal (Sequent.of assumptions body)
        [Sequent.of assumptions .bottom]
  | andIntroduction :
      RuleApplication Symbol Literal (Sequent.of assumptions (.and left right))
        [Sequent.of assumptions left, Sequent.of assumptions right]
  | andEliminationLeft :
      RuleApplication Symbol Literal (Sequent.of assumptions left)
        [Sequent.of assumptions (.and left right)]
  | andEliminationRight :
      RuleApplication Symbol Literal (Sequent.of assumptions right)
        [Sequent.of assumptions (.and left right)]
  | orIntroductionLeft :
      RuleApplication Symbol Literal (Sequent.of assumptions (.or left right))
        [Sequent.of assumptions left]
  | orIntroductionRight :
      RuleApplication Symbol Literal (Sequent.of assumptions (.or left right))
        [Sequent.of assumptions right]
  | orElimination :
      RuleApplication Symbol Literal (Sequent.of assumptions result)
        [Sequent.of assumptions (.or left right),
          Sequent.of (left :: assumptions) result,
          Sequent.of (right :: assumptions) result]
  | implicationIntroduction :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.implies antecedent consequent))
        [Sequent.of (antecedent :: assumptions) consequent]
  | implicationElimination :
      RuleApplication Symbol Literal (Sequent.of assumptions consequent)
        [Sequent.of assumptions (.implies antecedent consequent),
          Sequent.of assumptions antecedent]
  | negationIntroduction :
      RuleApplication Symbol Literal (Sequent.of assumptions (.not body))
        [Sequent.of (body :: assumptions) .bottom]
  | negationElimination :
      RuleApplication Symbol Literal (Sequent.of assumptions .bottom)
        [Sequent.of assumptions (.not body), Sequent.of assumptions body]
  | iffIntroduction :
      RuleApplication Symbol Literal (Sequent.of assumptions (.iff left right))
        [Sequent.of assumptions (.implies left right),
          Sequent.of assumptions (.implies right left)]
  | iffEliminationLeft :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.implies left right))
        [Sequent.of assumptions (.iff left right)]
  | iffEliminationRight :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.implies right left))
        [Sequent.of assumptions (.iff left right)]
  | allInSpineFromAllObject
      (arguments : Spine Symbol Literal ordinary rows) :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.allInSpine arguments body))
        [Sequent.of assumptions (.allObject body)]
  | allInSpineNilIntroduction :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.allInSpine .nil body)) []
  | allInSpineTermIntroduction
      (value : Term Symbol Literal ordinary rows)
      (rest : Spine Symbol Literal ordinary rows) :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.allInSpine (.term value rest) body))
        [Sequent.of assumptions
          (Substitution.instantiateObjectFormula value body),
         Sequent.of assumptions (.allInSpine rest body)]
  | allInSpineHeadElimination :
      RuleApplication Symbol Literal
        (Sequent.of assumptions
          (Substitution.instantiateObjectFormula value body))
        [Sequent.of assumptions (.allInSpine (.term value rest) body)]
  | allInSpineTermTailElimination :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.allInSpine rest body))
        [Sequent.of assumptions (.allInSpine (.term value rest) body)]
  | allInSpineRowTailElimination :
      RuleApplication Symbol Literal
        (Sequent.of assumptions (.allInSpine rest body))
        [Sequent.of assumptions (.allInSpine (.row rowIndex rest) body)]
  | allObjectIntroduction :
      RuleApplication Symbol Literal (Sequent.of assumptions (.allObject body))
        [Sequent.of (weakenObjectHypotheses assumptions) body]
  | allObjectElimination (value : Term Symbol Literal ordinary rows) :
      RuleApplication Symbol Literal
        (Sequent.of assumptions
          (Substitution.instantiateObjectFormula value body))
        [Sequent.of assumptions (.allObject body)]
  | someObjectIntroduction (value : Term Symbol Literal ordinary rows) :
      RuleApplication Symbol Literal (Sequent.of assumptions (.someObject body))
        [Sequent.of assumptions
          (Substitution.instantiateObjectFormula value body)]
  | someObjectElimination :
      RuleApplication Symbol Literal (Sequent.of assumptions result)
        [Sequent.of assumptions (.someObject body),
          Sequent.of (body :: weakenObjectHypotheses assumptions)
            (Renaming.weakenObjectFormula result)]
  | allRowIntroduction :
      RuleApplication Symbol Literal (Sequent.of assumptions (.allRow body))
        [Sequent.of (weakenRowHypotheses assumptions) body]
  | allRowElimination (arguments : Spine Symbol Literal ordinary rows) :
      RuleApplication Symbol Literal
        (Sequent.of assumptions
          (Substitution.instantiateRowFormula arguments body))
        [Sequent.of assumptions (.allRow body)]
  | someRowIntroduction (arguments : Spine Symbol Literal ordinary rows) :
      RuleApplication Symbol Literal (Sequent.of assumptions (.someRow body))
        [Sequent.of assumptions
          (Substitution.instantiateRowFormula arguments body)]
  | someRowElimination :
      RuleApplication Symbol Literal (Sequent.of assumptions result)
        [Sequent.of assumptions (.someRow body),
          Sequent.of (body :: weakenRowHypotheses assumptions)
            (Renaming.weakenRowFormula result)]
  | equalityReflexivity (value : Term Symbol Literal ordinary rows) :
      RuleApplication Symbol Literal (Sequent.of assumptions (.equal value value)) []
  | equalitySubstitution
      (context : Formula Symbol Literal (ordinary + 1) rows) :
      RuleApplication Symbol Literal
        (Sequent.of assumptions
          (Substitution.instantiateObjectFormula right context))
        [Sequent.of assumptions (.equal left right),
          Sequent.of assumptions
            (Substitution.instantiateObjectFormula left context)]
  | classicalContradiction :
      RuleApplication Symbol Literal (Sequent.of assumptions body)
        [Sequent.of ((.not body) :: assumptions) .bottom]

/-- Every outstanding sequent has a native derivation. -/
def AllDerivable {Symbol : Type uSymbol} {Literal : Type uLiteral}
    (goals : List (Sequent Symbol Literal)) : Prop :=
  forall goal, goal ∈ goals -> goal.Derivable

namespace AllDerivable

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {goal : Sequent Symbol Literal} {goals : List (Sequent Symbol Literal)}

theorem head (derivable : AllDerivable (goal :: goals)) : goal.Derivable :=
  derivable goal (by simp)

theorem tail (derivable : AllDerivable (goal :: goals)) : AllDerivable goals := by
  intro candidate membership
  exact derivable candidate (List.mem_cons_of_mem goal membership)

end AllDerivable

namespace RuleApplication

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}

/-- A native rule reconstructs its conclusion from derivations of its exact
ordered premises. -/
theorem sound
    {goal : Sequent Symbol Literal} {premises : List (Sequent Symbol Literal)}
    (rule : RuleApplication Symbol Literal goal premises)
    (premisesDerivable : AllDerivable premises) :
    goal.Derivable := by
  cases rule with
  | hypothesis member => exact .hypothesis member
  | topIntroduction => exact .topIntroduction
  | bottomElimination =>
      exact .bottomElimination (AllDerivable.head premisesDerivable)
  | andIntroduction =>
      exact .andIntroduction
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | andEliminationLeft =>
      exact .andEliminationLeft (AllDerivable.head premisesDerivable)
  | andEliminationRight =>
      exact .andEliminationRight (AllDerivable.head premisesDerivable)
  | orIntroductionLeft =>
      exact .orIntroductionLeft (AllDerivable.head premisesDerivable)
  | orIntroductionRight =>
      exact .orIntroductionRight (AllDerivable.head premisesDerivable)
  | orElimination =>
      exact .orElimination
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
        (AllDerivable.head
          (AllDerivable.tail (AllDerivable.tail premisesDerivable)))
  | implicationIntroduction =>
      exact .implicationIntroduction (AllDerivable.head premisesDerivable)
  | implicationElimination =>
      exact .implicationElimination
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | negationIntroduction =>
      exact .negationIntroduction (AllDerivable.head premisesDerivable)
  | negationElimination =>
      exact .negationElimination
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | iffIntroduction =>
      exact .iffIntroduction
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | iffEliminationLeft =>
      exact .iffEliminationLeft (AllDerivable.head premisesDerivable)
  | iffEliminationRight =>
      exact .iffEliminationRight (AllDerivable.head premisesDerivable)
  | allInSpineFromAllObject arguments =>
      exact .allInSpineFromAllObject arguments
        (AllDerivable.head premisesDerivable)
  | allInSpineNilIntroduction => exact .allInSpineNilIntroduction _
  | allInSpineTermIntroduction value rest =>
      exact .allInSpineTermIntroduction value rest
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | allInSpineHeadElimination =>
      exact .allInSpineHeadElimination (AllDerivable.head premisesDerivable)
  | allInSpineTermTailElimination =>
      exact .allInSpineTermTailElimination (AllDerivable.head premisesDerivable)
  | allInSpineRowTailElimination =>
      exact .allInSpineRowTailElimination (AllDerivable.head premisesDerivable)
  | allObjectIntroduction =>
      exact .allObjectIntroduction (AllDerivable.head premisesDerivable)
  | allObjectElimination value =>
      exact .allObjectElimination value (AllDerivable.head premisesDerivable)
  | someObjectIntroduction value =>
      exact .someObjectIntroduction value (AllDerivable.head premisesDerivable)
  | someObjectElimination =>
      exact .someObjectElimination
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | allRowIntroduction =>
      exact .allRowIntroduction (AllDerivable.head premisesDerivable)
  | allRowElimination arguments =>
      exact .allRowElimination arguments (AllDerivable.head premisesDerivable)
  | someRowIntroduction arguments =>
      exact .someRowIntroduction arguments (AllDerivable.head premisesDerivable)
  | someRowElimination =>
      exact .someRowElimination
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | equalityReflexivity value => exact .equalityReflexivity value
  | equalitySubstitution context =>
      exact .equalitySubstitution context
        (AllDerivable.head premisesDerivable)
        (AllDerivable.head (AllDerivable.tail premisesDerivable))
  | classicalContradiction =>
      exact .classicalContradiction (AllDerivable.head premisesDerivable)

end RuleApplication

/-- A proof-search state is an ordered list of native sequents. -/
abbrev GoalState (Symbol : Type uSymbol) (Literal : Type uLiteral) :=
  List (Sequent Symbol Literal)

/-- One backward native proof-search step replaces the first goal by the
premises of one native rule. -/
def Resolves {Symbol : Type uSymbol} {Literal : Type uLiteral} :
    GoalState Symbol Literal -> GoalState Symbol Literal -> Prop :=
  fun source target =>
    exists goal premises rest,
      RuleApplication Symbol Literal goal premises /\
      source = goal :: rest /\ target = premises ++ rest

/-- The GSLT induced directly by the native SUMO rule calculus. -/
def nativeProofSearchGSLT
    (Symbol : Type uSymbol) (Literal : Type uLiteral) : GSLT where
  Term := GoalState Symbol Literal
  equations :=
    { r := Eq
      iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := Resolves
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The abstract GSLT step is exactly one native rule expansion. -/
theorem step_iff_rule
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    (source target : GoalState Symbol Literal) :
    (nativeProofSearchGSLT Symbol Literal).Step source target <->
      exists goal premises rest,
        RuleApplication Symbol Literal goal premises /\
        source = goal :: rest /\ target = premises ++ rest :=
  Iff.rfl

/-- Resolving the first obligations is stable under an untouched suffix. -/
theorem Resolves.append_right
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {source target : GoalState Symbol Literal}
    (step : Resolves source target) (suffix : GoalState Symbol Literal) :
    Resolves (source ++ suffix) (target ++ suffix) := by
  obtain ⟨goal, premises, rest, rule, rfl, rfl⟩ := step
  refine ⟨goal, premises, rest ++ suffix, rule, ?_, ?_⟩
  · rfl
  · simp [List.append_assoc]

/-- Multi-step native proof search is stable under an untouched suffix. -/
def multiStep_append_right
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {source target : GoalState Symbol Literal}
    (steps : (nativeProofSearchGSLT Symbol Literal).MultiStep source target)
    (suffix : GoalState Symbol Literal) :
    (nativeProofSearchGSLT Symbol Literal).MultiStep
      (source ++ suffix) (target ++ suffix) :=
  match steps with
  | .refl state => by
      change GoalState Symbol Literal at state
      exact @GSLT.MultiStep.refl (nativeProofSearchGSLT Symbol Literal)
        (state ++ suffix)
  | .step first rest =>
      .step (Resolves.append_right first suffix)
        (multiStep_append_right rest suffix)

/-- Transitivity of native proof-search reachability. -/
def multiStep_trans
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {first second third : GoalState Symbol Literal}
    (firstSecond :
      (nativeProofSearchGSLT Symbol Literal).MultiStep first second)
    (secondThird :
      (nativeProofSearchGSLT Symbol Literal).MultiStep second third) :
    (nativeProofSearchGSLT Symbol Literal).MultiStep first third :=
  match firstSecond with
  | .refl _ => secondThird
  | .step first rest => .step first (multiStep_trans rest secondThird)

/-- A native rule is one GSLT step from its singleton conclusion to its exact
premise list. -/
theorem singleton_step
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {goal : Sequent Symbol Literal} {premises : List (Sequent Symbol Literal)}
    (rule : RuleApplication Symbol Literal goal premises) :
    (nativeProofSearchGSLT Symbol Literal).Step [goal] premises := by
  exact ⟨goal, premises, [], rule, rfl, by simp⟩

/-- Sequentially discharge two native obligations. -/
def solve_two
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {first second : Sequent Symbol Literal}
    (firstSteps :
      (nativeProofSearchGSLT Symbol Literal).MultiStep [first] [])
    (secondSteps :
      (nativeProofSearchGSLT Symbol Literal).MultiStep [second] []) :
    (nativeProofSearchGSLT Symbol Literal).MultiStep [first, second] [] := by
  have firstWithSuffix := multiStep_append_right firstSteps [second]
  exact multiStep_trans firstWithSuffix secondSteps

/-- Sequentially discharge three native obligations. -/
def solve_three
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {first second third : Sequent Symbol Literal}
    (firstSteps :
      (nativeProofSearchGSLT Symbol Literal).MultiStep [first] [])
    (secondSteps :
      (nativeProofSearchGSLT Symbol Literal).MultiStep [second] [])
    (thirdSteps :
      (nativeProofSearchGSLT Symbol Literal).MultiStep [third] []) :
    (nativeProofSearchGSLT Symbol Literal).MultiStep [first, second, third] [] := by
  have firstWithSuffix := multiStep_append_right firstSteps [second, third]
  exact multiStep_trans firstWithSuffix (solve_two secondSteps thirdSteps)

/-- One proof-search step transports native derivability backwards. -/
theorem allDerivable_of_step
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {source target : GoalState Symbol Literal}
    (step : (nativeProofSearchGSLT Symbol Literal).Step source target)
    (targetDerivable : AllDerivable target) :
    AllDerivable source := by
  obtain ⟨goal, premises, rest, rule, rfl, rfl⟩ := step
  have premisesDerivable : AllDerivable premises := by
    intro premise member
    exact targetDerivable premise (List.mem_append_left rest member)
  have restDerivable : AllDerivable rest := by
    intro remainder member
    exact targetDerivable remainder (List.mem_append_right premises member)
  intro candidate membership
  simp only [List.mem_cons] at membership
  rcases membership with equality | membership
  · subst candidate
    exact rule.sound premisesDerivable
  · exact restDerivable candidate membership

/-- Multi-step native proof search transports derivability backwards. -/
theorem allDerivable_of_multiStep
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {source target : GoalState Symbol Literal}
    (steps : (nativeProofSearchGSLT Symbol Literal).MultiStep source target) :
    AllDerivable target -> AllDerivable source := by
  let motive : forall (first last : GoalState Symbol Literal),
      (nativeProofSearchGSLT Symbol Literal).MultiStep first last -> Prop :=
    fun first last _ => AllDerivable last -> AllDerivable first
  exact GSLT.MultiStep.rec (motive := motive)
    (fun _ derivable => derivable)
    (fun first _ inductionHypothesis targetDerivable =>
      allDerivable_of_step first (inductionHypothesis targetDerivable))
    steps

/-- Reaching the empty state yields native derivations of every initial goal. -/
theorem derivable_of_reaches_empty
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {goals : GoalState Symbol Literal}
    (steps : (nativeProofSearchGSLT Symbol Literal).MultiStep goals []) :
    AllDerivable goals :=
  allDerivable_of_multiStep steps (by intro goal membership; simp at membership)

/-- Every native derivation executes as backward proof search to the empty
obligation state. -/
theorem derivation_to_multiStep
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {ordinary rows : Nat}
    {assumptions : List (Formula Symbol Literal ordinary rows)}
    {body : Formula Symbol Literal ordinary rows}
    (derivation : Derivation Symbol Literal assumptions body) :
    (nativeProofSearchGSLT Symbol Literal).MultiStep
      [Sequent.of assumptions body] [] := by
  induction derivation with
  | hypothesis member =>
      exact .step (singleton_step (RuleApplication.hypothesis member))
        (@GSLT.MultiStep.refl (nativeProofSearchGSLT Symbol Literal) [])
  | topIntroduction =>
      exact .step (singleton_step RuleApplication.topIntroduction)
        (@GSLT.MultiStep.refl (nativeProofSearchGSLT Symbol Literal) [])
  | bottomElimination premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.bottomElimination)
        inductionHypothesis
  | andIntroduction leftProof rightProof leftIH rightIH =>
      exact .step (singleton_step RuleApplication.andIntroduction)
        (solve_two leftIH rightIH)
  | andEliminationLeft premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.andEliminationLeft)
        inductionHypothesis
  | andEliminationRight premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.andEliminationRight)
        inductionHypothesis
  | orIntroductionLeft premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.orIntroductionLeft)
        inductionHypothesis
  | orIntroductionRight premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.orIntroductionRight)
        inductionHypothesis
  | orElimination disjunction leftBranch rightBranch disjunctionIH leftIH rightIH =>
      exact .step (singleton_step RuleApplication.orElimination)
        (solve_three disjunctionIH leftIH rightIH)
  | implicationIntroduction premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.implicationIntroduction)
        inductionHypothesis
  | implicationElimination functionProof argumentProof functionIH argumentIH =>
      exact .step (singleton_step RuleApplication.implicationElimination)
        (solve_two functionIH argumentIH)
  | negationIntroduction premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.negationIntroduction)
        inductionHypothesis
  | negationElimination negativeProof positiveProof negativeIH positiveIH =>
      exact .step (singleton_step RuleApplication.negationElimination)
        (solve_two negativeIH positiveIH)
  | iffIntroduction forwardProof reverseProof forwardIH reverseIH =>
      exact .step (singleton_step RuleApplication.iffIntroduction)
        (solve_two forwardIH reverseIH)
  | iffEliminationLeft premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.iffEliminationLeft)
        inductionHypothesis
  | iffEliminationRight premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.iffEliminationRight)
        inductionHypothesis
  | allInSpineFromAllObject arguments premise inductionHypothesis =>
      exact .step
        (singleton_step (RuleApplication.allInSpineFromAllObject arguments))
        inductionHypothesis
  | allInSpineNilIntroduction body =>
      exact .step (singleton_step RuleApplication.allInSpineNilIntroduction)
        (@GSLT.MultiStep.refl (nativeProofSearchGSLT Symbol Literal) [])
  | allInSpineTermIntroduction value rest valueProof restProof valueIH restIH =>
      exact .step
        (singleton_step
          (RuleApplication.allInSpineTermIntroduction value rest))
        (solve_two valueIH restIH)
  | allInSpineHeadElimination premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.allInSpineHeadElimination)
        inductionHypothesis
  | allInSpineTermTailElimination premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.allInSpineTermTailElimination)
        inductionHypothesis
  | allInSpineRowTailElimination premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.allInSpineRowTailElimination)
        inductionHypothesis
  | allObjectIntroduction premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.allObjectIntroduction)
        inductionHypothesis
  | allObjectElimination value premise inductionHypothesis =>
      exact .step (singleton_step (RuleApplication.allObjectElimination value))
        inductionHypothesis
  | someObjectIntroduction value premise inductionHypothesis =>
      exact .step (singleton_step (RuleApplication.someObjectIntroduction value))
        inductionHypothesis
  | someObjectElimination existentialProof branchProof existentialIH branchIH =>
      exact .step (singleton_step RuleApplication.someObjectElimination)
        (solve_two existentialIH branchIH)
  | allRowIntroduction premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.allRowIntroduction)
        inductionHypothesis
  | allRowElimination arguments premise inductionHypothesis =>
      exact .step (singleton_step (RuleApplication.allRowElimination arguments))
        inductionHypothesis
  | someRowIntroduction arguments premise inductionHypothesis =>
      exact .step (singleton_step (RuleApplication.someRowIntroduction arguments))
        inductionHypothesis
  | someRowElimination existentialProof branchProof existentialIH branchIH =>
      exact .step (singleton_step RuleApplication.someRowElimination)
        (solve_two existentialIH branchIH)
  | equalityReflexivity value =>
      exact .step
        (singleton_step (RuleApplication.equalityReflexivity value))
        (@GSLT.MultiStep.refl (nativeProofSearchGSLT Symbol Literal) [])
  | equalitySubstitution context equalityProof contextProof equalityIH contextIH =>
      exact .step
        (singleton_step (RuleApplication.equalitySubstitution context))
        (solve_two equalityIH contextIH)
  | classicalContradiction premise inductionHypothesis =>
      exact .step (singleton_step RuleApplication.classicalContradiction)
        inductionHypothesis

/-- **Native adequacy.** A scoped SUMO sequent is derivable exactly when its
native proof-search GSLT reaches the empty obligation state. -/
theorem derivable_iff_reaches_empty
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    (goal : Sequent Symbol Literal) :
    goal.Derivable <->
      (nativeProofSearchGSLT Symbol Literal).MultiStep [goal] [] := by
  cases goal with
  | mk ordinary rows assumptions body =>
      constructor
      · exact derivation_to_multiStep
      · intro steps
        exact derivable_of_reaches_empty steps _ (by simp)

/-- Checker acceptance enters the native proof-search GSLT through the
derivation reconstructed by the proof-producing kernel. -/
theorem accepted_certificate_reaches_empty
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    [DecidableEq Symbol] [DecidableEq Literal]
    {ordinary rows : Nat}
    {assumptions : List (Formula Symbol Literal ordinary rows)}
    {body : Formula Symbol Literal ordinary rows}
    {certificate : Certificate Symbol Literal ordinary rows}
    (accepted : Certificate.infer assumptions certificate = some body) :
    (nativeProofSearchGSLT Symbol Literal).MultiStep
      [Sequent.of assumptions body] [] :=
  derivation_to_multiStep (Certificate.infer_sound accepted)

/-! ## Positive and negative controls -/

theorem implication_identity_reaches_empty :
    (nativeProofSearchGSLT String Unit).MultiStep
      [Sequent.of []
        (.implies SyntaxCanary.selfApplication SyntaxCanary.selfApplication)] [] :=
  accepted_certificate_reaches_empty
    (show Certificate.infer [] Certificate.implicationIdentity =
      some (.implies SyntaxCanary.selfApplication SyntaxCanary.selfApplication) by
      rfl)

theorem empty_state_has_no_step
    (target : GoalState String Unit) :
    ¬ (nativeProofSearchGSLT String Unit).Step [] target := by
  rintro ⟨goal, premises, rest, rule, impossible, targetShape⟩
  cases impossible

end Mettapedia.Languages.SUMO.Native.ProofSearch
