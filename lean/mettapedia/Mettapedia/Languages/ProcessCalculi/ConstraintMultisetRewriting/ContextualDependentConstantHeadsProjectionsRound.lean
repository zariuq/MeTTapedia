import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeadsProjections

/-!
# The projections round

The pieces of two projections of spines become store equations once their annotations are formed at the
budget (R97's `formPieces`); the decomposition has exactly the equation's solutions and weighs at least two
less (`projUnder_exact`, `projUnder_weight`), so it is a committed step of the weight rank.

The **projections round** is the endpoints round, and when that round is stuck, one committed
decomposition of a projection spine on the prepared store with homogeneous twins. Preparing the store and
making its twins homogeneous keep the weight rank (`preparedTwins_rank`), so the committed step lowers the
rank of the original store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantHeadsProjections

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

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- Finish the decomposition of one equation between projections of spines of one local. -/
def finishProj {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (found : projUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (store : PieceStore facts roots heads algebra rigid complete pieces) :
    WeighedParts facts roots heads algebra rigid complete equation :=
  ⟨⟨store.val, fun {Δ} σ => by
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have read := projUnder_subst [] _ _ _ found σ.substitution
        (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
      rw [List.map_nil] at read
      have exact := projUnder_exact facts roots heads algebra complete [] _ _ _ Δ.formed (LocalTypes.nil _) read
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
      projUnder_weight facts roots heads algebra rigid complete [] _ _ _ Θ.formed (LocalTypes.nil _) found
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

/-- **The decomposition of one store equation between projections of spines**, with its weight. -/
def projWeighed (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match found : projUnder [] equation.1.1.code equation.1.2.code equation.2.2.code with
    | some pieces =>
        (formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces
          (projUnder_typed facts [] _ _ _ Θ.formed (LocalTypes.nil _) found equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishProj facts roots heads algebra rigid complete equation same found)
    | none => none
  else none

/-- **Decompose the first equation between projections of spines.** -/
def decomposeProjections (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (projWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation,
        decomposeProjections fuel rest)

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

omit [DecidableRel S.R.cumulative] in
include rigid complete in
/-- **Preparing the store and making its twins homogeneous keep the weight rank.** -/
theorem preparedTwins_rank (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete
        (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).target.arity,
      storeWeight facts roots heads algebra rigid complete
        ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining.map
          (collapseOne facts roots heads algebra reducer fuel))) =
    (Θ.arity, storeWeight facts roots heads algebra rigid complete problem)
  rw [collapse_weight facts roots heads algebra rigid complete reducer fuel,
    prepare_weight facts roots heads algebra rigid complete root rootComplete fuel problem,
    prepare_arity facts roots heads root rootComplete fuel problem]

omit [DecidableRel S.R.cumulative] in
include rigid complete in
/-- **A lighter store after preparation with homogeneous twins lowers the weight rank of the original store.** -/
theorem below_of_preparedTwins (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {store : EquationStore
      (TotalTerm (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).target)}
    (lower : storeWeight facts roots heads algebra rigid complete store <
      storeWeight facts roots heads algebra rigid complete
        (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining) :
    ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete store)
      (weightRank facts roots heads algebra rigid complete problem) := by
  have rank := preparedTwins_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem
  simp only [weightRank, Prod.mk.injEq] at rank
  unfold weightRank ContextualDependentWorklist.Below
  rw [rank.1]
  exact Prod.Lex.right _ (rank.2 ▸ lower)

/-- The decomposition of projection spines on the prepared store with homogeneous twins. -/
def projectionsRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining with
  | some found => .progress ((preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).then
        ((Update.pending S.levels found.val).rephrase found.property.1))
      (below_of_preparedTwins facts roots heads algebra rigid complete reducer root rootComplete fuel found.property.2)
  | none => .stuck

/-- **One projections round**: the endpoints round; when it is stuck, one committed decomposition of a
projection spine on the prepared store with homogeneous twins. -/
def projectionsRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | .stuck => projectionsRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel
      problem
  | other => other

/-- **The projections family**, at the weight rank. -/
noncomputable def projectionsFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem projWeighed_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      projWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation := by
  unfold projWeighed
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
theorem decomposeProjections_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      EventuallyConst fun fuel =>
        decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (projWeighed_const facts roots heads algebra rigid complete declared choices reducer stable equation)
          (decomposeProjections_const rest))

/-- The view of the decomposition, from an update of the store. -/
def projectionsViewOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem)
    (found : Option (Decomposed facts roots heads algebra rigid complete prepared.remaining)) :
    Option (Option (Update S.levels problem)) :=
  found.map fun found => some (prepared.then ((Update.pending S.levels found.val).rephrase found.property.1))

theorem projectionsRest_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (projectionsRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel
      problem) =
      projectionsViewOf facts roots heads algebra rigid complete
        (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem)
        (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
          (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining) := by
  unfold projectionsRest projectionsViewOf
  cases decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
    (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining <;> rfl

include stable in
theorem projectionsRest_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => projectionsRest facts roots heads algebra rigid complete declared choices reducer root
      rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => projectionsRest_view facts roots heads algebra rigid complete declared
    choices reducer root rootComplete fuel problem) ?_
  refine EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => projectionsViewOf facts roots heads algebra rigid complete
      (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining)))
      (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
        (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining))).remaining))
    (prepare_const root rootComplete facts roots heads problem) (fun prepared => ?_)
  exact EventuallyConst.dep (h := fun fuel => collapsed facts roots heads algebra reducer fuel prepared.remaining)
    (k := fun fuel store => projectionsViewOf facts roots heads algebra rigid complete (prepared.then (collapseOf store))
      (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
        (prepared.then (collapseOf store)).remaining))
    (collapsed_const facts roots heads algebra reducer stable prepared.remaining)
    (fun store => EventuallyConst.comp (projectionsViewOf facts roots heads algebra rigid complete
        (prepared.then (collapseOf store)))
      (decomposeProjections_const facts roots heads algebra rigid complete declared choices reducer stable
        (prepared.then (collapseOf store)).remaining))

theorem projectionsRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (roundView (projectionsRest facts roots heads algebra rigid complete declared choices reducer root rootComplete
          fuel problem)) := by
  unfold projectionsRound
  cases endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem <;> rfl

include stable in
/-- **The projections round is eventually constant on every store.** -/
theorem projectionsRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => projectionsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => projectionsRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (endpointsRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp roundView (projectionsRest_const facts roots heads algebra rigid complete declared choices
        reducer root rootComplete stable problem)))

include stable in
/-- **The projections family settles** on every class of stores on which, at each nonempty store and from
some budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def projectionsSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (projectionsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => projectionsRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentConstantHeadsProjections
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
