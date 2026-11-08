import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEliminationsUnder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInPlace

/-!
# The eliminations round

The pieces of two elimination spines of one local become store equations once their annotations are formed at the
budget (R97's `formPieces`). The decomposition has exactly the equation's solutions at every solution, since the
reading is kept by substitutions that fix the locals (`elimUnder_subst`, `elimUnder_exact`), and it weighs at least
two less (`elimUnder_weight`), so it is a committed step of the weight rank (`finishElims`).

The **eliminations round** is the placed round, and when that round is stuck, one committed decomposition of an
elimination spine on the prepared store with homogeneous twins (R99's `preparedTwins`). It is conservative over the
placed round (`elimsRound_eq_of_placed`, `elims_decided_of_placed`) and eventually constant (`elimsRound_const`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEliminations

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
open ContextualDependentConstantHeadsProjections ContextualDependentPatternFiring

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **Finish the decomposition of one equation between elimination spines of one local**: exact at every solution,
and lighter. -/
def finishElims {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (found : elimUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (store : PieceStore facts roots heads algebra rigid complete pieces) :
    WeighedParts facts roots heads algebra rigid complete equation :=
  ⟨⟨store.val, fun {Δ} σ => by
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have read := elimUnder_subst [] _ _ _ found σ.substitution
        (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
      rw [List.map_nil] at read
      have exact := elimUnder_exact facts roots heads algebra complete [] _ _ _ Δ.formed (LocalTypes.nil _) read
        tl tr
      rw [solves_raw, same, store.property.1 σ]
      constructor
      · rintro ⟨_, held⟩ piece member
        exact exact.mp held _ (List.mem_map.mpr ⟨piece, member, rfl⟩)
      · intro held
        refine ⟨(Typed.isType tl Δ.formed).refl, exact.mpr fun piece member => ?_⟩
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact held original inside⟩, by
    have tr := equation.2.2.typed
    rw [same] at tr
    obtain ⟨w, wl, wr, weighs, ⟨v, nv, wv⟩, ⟨v', nv', wv'⟩, total⟩ :=
      elimUnder_weight facts roots heads algebra rigid complete [] _ _ _ Θ.formed (LocalTypes.nil _) found
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

/-- **The decomposition of one store equation between elimination spines**, with its weight. -/
def elimsWeighed (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match found : elimUnder [] equation.1.1.code equation.1.2.code equation.2.2.code with
    | some pieces =>
        (formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces
          (elimUnder_typed facts [] _ _ _ Θ.formed (LocalTypes.nil _) found equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishElims facts roots heads algebra rigid complete equation same found)
    | none => none
  else none

/-- **Decompose the first equation between elimination spines.** -/
def decomposeElims (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (elimsWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation,
        decomposeElims fuel rest)

/-! ## The round -/

variable (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The decomposition of elimination spines on the prepared store with homogeneous twins. -/
def elimsRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining with
  | some found => .progress ((preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).then
        ((Update.pending S.levels found.val).rephrase found.property.1))
      (below_of_preparedTwins facts roots heads algebra rigid complete reducer root rootComplete fuel found.property.2)
  | none => .stuck

/-- **One eliminations round**: the placed round; when it is stuck, one committed decomposition of an elimination
spine on the prepared store with homogeneous twins. -/
def elimsRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck => elimsRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem
  | other => other

/-- **The eliminations family**, at the weight rank. -/
noncomputable def elimsFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Conservativity over the placed family -/

/-- **The eliminations round makes the move of the placed round wherever that round moves.** -/
theorem elimsRound_eq_of_placed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold elimsRound
  cases computed : placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the placed family decides, the eliminations family decides with the same outcome.** -/
theorem elims_run_of_placed (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => elimsRound_eq_of_placed facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the placed family decides at a joint budget, the eliminations family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem elims_decided_of_placed {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => elims_run_of_placed facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-- The eliminations round is not stuck where the placed round is not. -/
theorem elimsRound_not_stuck_of_placed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  rw [elimsRound_eq_of_placed facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel moving]
  exact moving

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem elimsWeighed_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      elimsWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation := by
  unfold elimsWeighed
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
theorem decomposeElims_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      EventuallyConst fun fuel =>
        decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (elimsWeighed_const facts roots heads algebra rigid complete declared choices reducer stable equation)
          (decomposeElims_const rest))

theorem elimsRest_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (elimsRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel
      problem) =
      projectionsViewOf facts roots heads algebra rigid complete
        (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem)
        (decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel
          (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining) := by
  unfold elimsRest projectionsViewOf
  cases decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel
    (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining <;> rfl

include stable in
theorem elimsRest_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => elimsRest facts roots heads algebra rigid complete declared choices reducer root
      rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => elimsRest_view facts roots heads algebra rigid complete declared
    choices reducer root rootComplete fuel problem) ?_
  refine EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => projectionsViewOf facts roots heads algebra rigid complete
      (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining)))
      (decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel
        (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining))).remaining))
    (prepare_const root rootComplete facts roots heads problem) (fun prepared => ?_)
  exact EventuallyConst.dep (h := fun fuel => collapsed facts roots heads algebra reducer fuel prepared.remaining)
    (k := fun fuel store => projectionsViewOf facts roots heads algebra rigid complete (prepared.then (collapseOf store))
      (decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel
        (prepared.then (collapseOf store)).remaining))
    (collapsed_const facts roots heads algebra reducer stable prepared.remaining)
    (fun store => EventuallyConst.comp (projectionsViewOf facts roots heads algebra rigid complete
        (prepared.then (collapseOf store)))
      (decomposeElims_const facts roots heads algebra rigid complete declared choices reducer stable
        (prepared.then (collapseOf store)).remaining))

theorem elimsRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (roundView (elimsRest facts roots heads algebra rigid complete declared choices reducer root rootComplete
          fuel problem)) := by
  unfold elimsRound
  cases placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem <;> rfl

include stable in
/-- **The eliminations round is eventually constant on every store.** -/
theorem elimsRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => elimsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => elimsRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (placedRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp roundView (elimsRest_const facts roots heads algebra rigid complete declared choices
        reducer root rootComplete stable problem)))

include stable in
/-- **The eliminations family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def elimsSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => elimsRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentEliminations
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
