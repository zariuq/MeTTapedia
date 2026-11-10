import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthFamily

/-!
# The η-long prepared family

`ContextualDependentEtaDepthFamily` expands the store as it is given. Its annotations need not be normal, so its Π
counts can fall short of the annotations' normal forms, and its twins need not be homogeneous. **The η-long prepared
store** (`longUpdate`) expands after preparation and twin collapse: every annotation is then normal from some budget
on, every collapsed twin has its left annotation, and both sides of every homogeneous equation are expanded to the
same depth, the normal annotation's Π count. It has the store's solutions and rank (`longUpdate_rank`, from
`preparedTwins_rank` and `storeWeight_expand`) and stays in the permuted Miller class (`longUpdate_keeps`).

**The η-long prepared round** (`etaRound`) is the under-binder round; when that is stuck, the under-binder round on the
η-long prepared store, read back through the update (`liftCollapsed`). The family is conservative over the
under-binder family (`eta_run_of_under`), eventually constant (`etaRound_const`, from the eventual constancy of
preparation and twin collapse), closed in the permuted Miller class (`etaRound_closure`), and so decides every store of
the dynamic pattern fragment as soon as its round is eventually not stuck on nonempty stores of the class
(`eta_decided_of_firing`, `tower_eta_decided_of_firing`), in particular as soon as an under-binder reader reads the store
or its η-long prepared store (`EtaReads`, `tower_eta_decided_of_etaReads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentIntersectionGeneral ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentCoverageReadersHalf ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem roundView_orElse {rank : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (first second : Round S.levels rank problem) :
    roundView (orElse first second) = (roundView first).or (roundView second) := by
  cases first <;> rfl

section Rule

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (strengthening : EqualStrengthening S.R)

/-- **The η-long prepared store**: preparation, twin collapse, then η-expansion of every side to its annotation's
Π count, as an update of the store. -/
noncomputable def longUpdate (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Update S.levels problem :=
  (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).then
    ((Update.pending S.levels (expandStore facts
        (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining)).rephrase
      (expand_equivalent facts _))

omit [DecidableRel S.R.cumulative] in
theorem longUpdate_remaining (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining =
      expandStore facts (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining :=
  rfl

omit [DecidableRel S.R.cumulative] in
theorem longUpdate_rank (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  have twins := ContextualDependentConstantHeadsProjections.preparedTwins_rank facts roots heads algebra rigid complete
    reducer root rootComplete fuel problem
  change ((preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).target.arity,
    storeWeight facts roots heads algebra rigid complete (expandStore facts
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining)) = _
  rw [storeWeight_expand]
  exact twins

/-- **The η-long prepared round**: the under-binder round; when it is stuck, the under-binder round on the η-long
prepared store, read as a round of the store. -/
noncomputable def etaRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))

/-- **The η-long prepared family**, at the weight rank. -/
noncomputable def etaFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ## Conservativity and readers -/

theorem etaRound_eq_of_under (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold etaRound
  cases computed : underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the under-binder family decides, the η-long prepared family decides with the same outcome.** -/
theorem eta_run_of_under (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((underFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((underFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => etaRound_eq_of_under facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem liftCollapsed_not_stuck {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (collapsedUpdate : Update S.levels problem)
    (keeps : weightRank facts roots heads algebra rigid complete collapsedUpdate.remaining =
      weightRank facts roots heads algebra rigid complete problem)
    {round : Round S.levels (weightRank facts roots heads algebra rigid complete) collapsedUpdate.remaining}
    (moving : round ≠ .stuck) :
    liftCollapsed facts roots heads algebra rigid complete collapsedUpdate keeps round ≠ .stuck := by
  cases round with
  | stuck => exact absurd rfl moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem liftCollapsed_keeps (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (collapsedUpdate : Update S.levels problem)
    (keeps : weightRank facts roots heads algebra rigid complete collapsedUpdate.remaining =
      weightRank facts roots heads algebra rigid complete problem)
    {round : Round S.levels (weightRank facts roots heads algebra rigid complete) collapsedUpdate.remaining}
    (inner : ∀ (update : Update S.levels collapsedUpdate.remaining)
      (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
        (weightRank facts roots heads algebra rigid complete collapsedUpdate.remaining)),
      round = .progress update smaller → holds update.remaining)
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem)}
    (fired : liftCollapsed facts roots heads algebra rigid complete collapsedUpdate keeps round =
      .progress update smaller) :
    holds update.remaining := by
  cases round with
  | progress first firstSmaller =>
      cases fired
      exact inner first firstSmaller rfl
  | refuted absent => cases fired
  | stuck => cases fired

/-- **The η-long prepared reader**: the round moves wherever the under-binder round moves on the η-long prepared
store. -/
theorem etaRound_not_stuck_of_long (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining ≠ .stuck) :
    etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold etaRound
  cases underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      exact liftCollapsed_not_stuck facts roots heads algebra rigid complete _
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem) moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The η-long prepared family's readers**: an under-binder reader on the store or on its η-long prepared store. -/
def EtaReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  UnderReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    UnderReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining

theorem etaRound_not_stuck_of_etaReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : EtaReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem) :
    etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with direct | expanded
  · rw [etaRound_eq_of_under facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel
      (underRound_not_stuck_of_underReads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel direct)]
    exact underRound_not_stuck_of_underReads facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel direct
  · exact etaRound_not_stuck_of_long facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel
      (underRound_not_stuck_of_underReads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel expanded)

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem collapse_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => collapse facts roots heads algebra reducer fuel problem :=
  EventuallyConst.of_eq (fun _ => rfl)
    (EventuallyConst.comp collapseOf (collapsed_const facts roots heads algebra reducer stable problem))

omit [DecidableRel S.R.cumulative] in
include stable in
/-- **The prepared store with homogeneous twins is eventually constant.** -/
theorem preparedTwins_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => preparedTwins facts roots heads algebra reducer root rootComplete fuel problem :=
  EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel
      problem)
    (k := fun fuel prepared => prepared.then (collapse facts roots heads algebra reducer fuel prepared.remaining))
    (prepare_const root rootComplete facts roots heads problem)
    (fun prepared => EventuallyConst.comp (fun collapsedUpdate => prepared.then collapsedUpdate)
      (collapse_const facts roots heads algebra reducer stable prepared.remaining))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem longUpdate_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => longUpdate facts roots heads algebra reducer root rootComplete fuel problem :=
  EventuallyConst.comp (fun twins : Update S.levels problem => twins.then
      ((Update.pending S.levels (expandStore facts twins.remaining)).rephrase (expand_equivalent facts _)))
    (preparedTwins_const facts roots heads algebra reducer root rootComplete stable problem)

theorem etaRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) =
      (roundView (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (liftView (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
          (roundView (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel
            (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))) := by
  unfold etaRound
  rw [roundView_orElse, liftCollapsed_view]

include stable in
/-- **The η-long prepared round is eventually constant on every store.** -/
theorem etaRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => etaRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => etaRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (underRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
      (EventuallyConst.dep (h := fun fuel => longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (k := fun fuel prepared => liftView prepared
          (roundView (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel prepared.remaining)))
        (longUpdate_const facts roots heads algebra reducer root rootComplete stable problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (underRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening stable prepared.remaining))))

include stable in
/-- **The η-long prepared family settles** on every class on which, from some budget on, its round is not stuck and
keeps the class. -/
noncomputable def etaSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (etaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => etaRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

/-! ## Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

omit [DecidableRel S.R.cumulative] in
include rigid sn in
/-- **The η-long prepared store stays in the permuted Miller class.** -/
theorem longUpdate_keeps (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining :=
  PermutedMiller.expand facts rigid sn
    (collapse_keeps facts roots heads algebra reducer fuel _
      (prepare_keeps root rootComplete facts roots heads rigid sn fuel problem permuted))

include sn directed in
/-- **Closure of the η-long prepared round** at every budget. -/
theorem etaRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) =
      .progress update smaller at fired
  cases computed : underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
        (fun first firstSmaller inner => underRound_closure facts roots heads algebra rigid complete declared
          choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _
          first firstSmaller
          (longUpdate_keeps facts roots heads algebra rigid reducer root rootComplete sn fuel permuted) inner) fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact underRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Acceptance for the η-long prepared family from firing**: on a strongly normalizing package without root
computation whose reducer returns reducts and is monotone in its budget, and where typed equality strengthens past an
unused variable, the family decides every store of the dynamic pattern fragment, with a principal answer or a
certified refutation, constant at every larger budget, as soon as its round is eventually not stuck on nonempty stores
of the permuted class. -/
theorem eta_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (etaSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        etaRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

include sn directed stable in
/-- **Acceptance for the η-long prepared family from eventual reading.** -/
theorem eta_decided_of_etaReads
    (reads : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        EtaReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique rootComplete strengthening larger problem)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  eta_decided_of_firing facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable sn directed
    (fun permuted nonempty => by
      obtain ⟨bound, eventually⟩ := reads permuted nonempty
      exact ⟨bound, fun larger enough => etaRound_not_stuck_of_etaReads facts roots heads algebra rigid complete
        declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening larger
        (eventually larger enough)⟩)
    inside

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The η-long prepared family of the tower controls. -/
noncomputable def etaTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  etaFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- The tower's η-long prepared store at one budget. -/
noncomputable abbrev towerLong (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Update setting.levels problem :=
  longUpdate (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel problem

/-- Readers of the tower's η-long prepared family at one budget. -/
abbrev TowerEtaReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  EtaReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Acceptance for the tower's η-long prepared family from firing**, on every store of the dynamic pattern
fragment. -/
theorem tower_eta_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → etaTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (etaTower.solver larger) problem larger = run (etaTower.solver budget) problem budget ∧
      ((∃ state finished, run (etaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (etaTower.solver larger) problem larger = .refuted absent)) :=
  eta_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

/-- **Acceptance for the tower's η-long prepared family from eventual reading**, on every store of the dynamic
pattern fragment. -/
theorem tower_eta_decided_of_etaReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerEtaReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (etaTower.solver larger) problem larger = run (etaTower.solver budget) problem budget ∧
      ((∃ state finished, run (etaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (etaTower.solver larger) problem larger = .refuted absent)) :=
  eta_decided_of_etaReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed reads inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
