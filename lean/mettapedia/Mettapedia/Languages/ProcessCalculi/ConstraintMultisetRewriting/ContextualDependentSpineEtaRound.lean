import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEtaUnder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSolveRound

/-!
# The flexible-base round

The pieces of two elimination spines of one local at a base shape become store equations once their annotations are
formed at the budget (R97's `formPieces`). The decomposition has exactly the equation's solutions at every solution
(`elimAnyUnder_exact_subst`), whatever the solution makes of the base type, and it weighs at least two less
(`elimAnyUnder_weight`), so it is a committed step of the weight rank (`finishFlex`).

The **flexible-base round** is the prune-and-solve round, and when that round is stuck, one committed decomposition of
elimination spines at a base shape on the prepared store with homogeneous twins (`flexRound`). It is conservative over
the prune-and-solve round (`flexRound_eq_of_pruneSolve`, `flex_decided_of_pruneSolve`), eventually constant
(`flexRound_const`), and settles where it is not stuck (`flexSettledOfConst`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpineEta

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentDecisiveFragment
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentRank
open ContextualDependentSpinesMany ContextualDependentConversionBudget ContextualDependentFragmentDecisive
open ContextualDependentOccursFull ContextualDependentTwinsUnder ContextualDependentConstantHeads
open ContextualDependentCensusPairEta ContextualDependentIdEndpoints ContextualDependentRigidDecomposition
open ContextualDependentConstantHeadsProjections ContextualDependentPatternFiring ContextualDependentEliminations
open ContextualDependentPruneSolve

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **Finish the decomposition of one equation between elimination spines at a base shape**: exact at every solution,
and lighter. -/
def finishFlex {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (found : elimAnyUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (store : PieceStore facts roots heads algebra rigid complete pieces) :
    WeighedParts facts roots heads algebra rigid complete equation :=
  ⟨⟨store.val, fun {Δ} σ => by
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have exact := elimAnyUnder_exact_subst facts roots heads algebra rigid complete [] _ _ _ found σ.substitution
        (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _) Δ.formed
        (by rw [List.map_nil]; exact LocalTypes.nil _) tl tr
      rw [solves_raw, same, store.property.1 σ]
      constructor
      · rintro ⟨_, held⟩ piece member
        exact exact.mp held piece member
      · intro held
        exact ⟨(Typed.isType tl Δ.formed).refl, exact.mpr held⟩⟩, by
    have tr := equation.2.2.typed
    rw [same] at tr
    obtain ⟨w, wl, wr, weighs, ⟨v, nv, wv⟩, ⟨v', nv', wv'⟩, total⟩ :=
      elimAnyUnder_weight facts roots heads algebra rigid complete [] _ _ _ Θ.formed (LocalTypes.nil _) found
        equation.1.2.typed tr
    have left := sideWeight_eq facts roots heads algebra rigid complete equation.1 nv
    have right := sideWeight_eq facts roots heads algebra rigid complete equation.2 (by rw [same]; exact nv')
    change storeWeight facts roots heads algebra rigid complete store.val <
      sideWeight facts roots heads algebra rigid complete equation.1 +
        sideWeight facts roots heads algebra rigid complete equation.2
    rw [store.property.2 w weighs, left, right]
    omega⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)

/-- **The decomposition of one store equation between elimination spines at a base shape**, with its weight. -/
def flexWeighed (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match found : elimAnyUnder [] equation.1.1.code equation.1.2.code equation.2.2.code with
    | some pieces =>
        (formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces
          (elimAnyUnder_typed facts [] _ _ _ Θ.formed (LocalTypes.nil _) found equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishFlex facts roots heads algebra rigid complete equation same found)
    | none => none
  else none

/-- **Decompose the first equation between elimination spines at a base shape.** -/
def decomposeFlex (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (flexWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation,
        decomposeFlex fuel rest)

variable (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The decomposition at a base shape on the prepared store with homogeneous twins. -/
def flexRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining with
  | some found => .progress ((preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).then
        ((Update.pending S.levels found.val).rephrase found.property.1))
      (below_of_preparedTwins facts roots heads algebra rigid complete reducer root rootComplete fuel found.property.2)
  | none => .stuck

/-- **One flexible-base round**: the prune-and-solve round; when it is stuck, one committed decomposition of elimination
spines at a base shape. -/
def flexRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck => flexRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem
  | other => other

/-- **The flexible-base family**, at the weight rank. -/
noncomputable def flexFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Conservativity over the prune-and-solve family -/

/-- **The flexible-base round makes the move of the prune-and-solve round wherever that round moves.** -/
theorem flexRound_eq_of_pruneSolve (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold flexRound
  cases computed : pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the prune-and-solve family decides, the flexible-base family decides with the same outcome.** -/
theorem flex_run_of_pruneSolve (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => flexRound_eq_of_pruneSolve facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the prune-and-solve family decides at a joint budget, the flexible-base family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem flex_decided_of_pruneSolve {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((pruneSolveFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => flex_run_of_pruneSolve facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-- **The flexible-base round is not stuck where the decomposition fires.** -/
theorem flexRound_not_stuck_of_rest (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : flexRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel
      problem ≠ .stuck) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold flexRound
  cases pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem flexWeighed_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      flexWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation := by
  unfold flexWeighed
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    split
    · rename_i pieces found
      exact EventuallyConst.comp _ (formPieces_const facts roots heads algebra rigid complete declared choices reducer
        stable pieces _)
    · exact EventuallyConst.const _
  · simp only [same, dite_false]
    exact EventuallyConst.const _

include stable in
theorem decomposeFlex_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      EventuallyConst fun fuel =>
        decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (flexWeighed_const facts roots heads algebra rigid complete declared choices reducer stable equation)
          (decomposeFlex_const rest))

theorem flexRest_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (flexRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel
      problem) =
      projectionsViewOf facts roots heads algebra rigid complete
        (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem)
        (decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel
          (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining) := by
  unfold flexRest projectionsViewOf
  cases decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel
    (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining <;> rfl

include stable in
theorem flexRest_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => flexRest facts roots heads algebra rigid complete declared choices reducer root
      rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => flexRest_view facts roots heads algebra rigid complete declared
    choices reducer root rootComplete fuel problem) ?_
  refine EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => projectionsViewOf facts roots heads algebra rigid complete
      (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining)))
      (decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel
        (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining))).remaining))
    (prepare_const root rootComplete facts roots heads problem) (fun prepared => ?_)
  exact EventuallyConst.dep (h := fun fuel => collapsed facts roots heads algebra reducer fuel prepared.remaining)
    (k := fun fuel store => projectionsViewOf facts roots heads algebra rigid complete (prepared.then (collapseOf store))
      (decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel
        (prepared.then (collapseOf store)).remaining))
    (collapsed_const facts roots heads algebra reducer stable prepared.remaining)
    (fun store => EventuallyConst.comp (projectionsViewOf facts roots heads algebra rigid complete
        (prepared.then (collapseOf store)))
      (decomposeFlex_const facts roots heads algebra rigid complete declared choices reducer stable
        (prepared.then (collapseOf store)).remaining))

theorem flexRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (roundView (flexRest facts roots heads algebra rigid complete declared choices reducer root rootComplete
          fuel problem)) := by
  unfold flexRound
  cases pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem <;> rfl

include stable in
/-- **The flexible-base round is eventually constant on every store.** -/
theorem flexRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => flexRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => flexRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (pruneSolveRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp roundView (flexRest_const facts roots heads algebra rigid complete declared choices
        reducer root rootComplete stable problem)))

include stable in
/-- **The flexible-base family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def flexSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (flexFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => flexRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentSpineEta
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
