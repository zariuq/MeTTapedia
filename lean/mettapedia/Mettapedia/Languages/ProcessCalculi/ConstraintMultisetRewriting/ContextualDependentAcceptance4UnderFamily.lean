import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4UnderReading

/-!
# Dead binders under live binders, in front of every rule

**The under-binder family** is the every-rule family with R119's dead binder in front replaced by a dead binder under at
most as many live binders as the left side has abstractions (`readDead`): it runs the dead-binder round; when that is
stuck, it reads each rotation of the store without the dead binder of its first equation and runs the same round there,
one level down (`underRoundAt`). A round of the store so read is a round of the store (`dropRound`).

The family is conservative over the dead-binder family (`under_run_of_dead`) and eventually constant at every depth
(`underRoundAt_const`); it keeps the permuted Miller class at every budget on a strongly normalizing package without
root computation whose reducer returns reducts (`underRound_closure`); so **it decides every store of the dynamic
pattern fragment if its round is eventually not stuck on nonempty stores of the permuted class**
(`under_decided_of_firing`, `tower_under_decided_of_firing`). These are conditional decisions; at the tower firing
fails, since the conclusion would decide `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentEtaLong
open ContextualDependentIntersection ContextualDependentDynamicFragment ContextualDependentInPlace
open ContextualDependentIntersectionGeneral ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance3

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Rounds behind a dropped binder -/

section Transfer

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (strengthening : EqualStrengthening S.R)

include facts roots strengthening in
/-- **Dropping a dead binder under live binders keeps the solutions of the store.** -/
theorem equivalent_dropsDead {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (drops : DropsDead equation reduced) :
    (frames S.levels).Equivalent (equation :: rest) (reduced :: rest) := by
  intro Δ σ
  rw [models_cons, models_cons]
  exact and_congr (drops.solves facts roots strengthening σ) Iff.rfl

/-- **Dropping a dead binder under live binders keeps the weight of the store.** -/
theorem storeWeight_dropsDead {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)}
    (rest : EquationStore (TotalTerm Θ)) (drops : DropsDead equation reduced) :
    storeWeight facts roots heads algebra rigid complete (reduced :: rest) =
      storeWeight facts roots heads algebra rigid complete (equation :: rest) := by
  simp only [storeWeight, drops.weight facts roots heads algebra rigid complete]

/-- **A round of the store with a dead binder dropped from its first equation is a round of the store.** -/
def dropRound {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (drops : DropsDead equation reduced) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) (reduced :: rest) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) (equation :: rest) :=
  transferRound facts roots heads algebra rigid complete (equivalent_dropsDead facts roots strengthening drops)
    (storeWeight_dropsDead facts roots heads algebra rigid complete rest drops)

end Transfer

/-! ## The round, the family -/

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

/-- An inner round on the first equation of a store, read without a dead binder under its live binders. -/
def underAt (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored) :
    (stored : EquationStore (TotalTerm Θ)) → Round S.levels (weightRank facts roots heads algebra rigid complete) stored
  | [] => .stuck
  | equation :: rest =>
      match readDead facts roots heads algebra declared choices reducer fuel (lamDepth equation.1.2.code) equation with
      | none => .stuck
      | some found => dropRound facts roots heads algebra rigid complete strengthening found.property
          (inner (found.val :: rest))

/-- An inner round on the rotations of the store in turn, each read without a dead binder of its first equation. -/
def underSearch (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (problem : EquationStore (TotalTerm Θ)) :
    List Nat → Round S.levels (weightRank facts roots heads algebra rigid complete) problem
  | [] => .stuck
  | k :: ks =>
      match underAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner
          (problem.rotate k) with
      | .stuck => underSearch fuel inner problem ks
      | found => unrotateRound facts roots heads algebra rigid complete k found

/-- One level of the under-binder round over a lower level. -/
def underStep (fuel : Nat) {Θ : Context S.R}
    (lower : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | .stuck => underSearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel lower
      problem (List.range problem.length)
  | other => other

/-- **The under-binder round at a recursion depth.** -/
def underRoundAt (fuel : Nat) : Nat → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem
  | 0, _, problem => deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem
  | depth + 1, _, problem => underStep facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (fun stored => underRoundAt fuel depth stored)
      problem

/-- **The under-binder round**, at the store's depth. -/
def underRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  underRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique rootComplete strengthening fuel (deadDepth problem) problem

/-- **The under-binder family**, at the weight rank. -/
noncomputable def underFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ## Conservativity -/

theorem underRoundAt_eq_of_dead (fuel : Nat) : ∀ (depth : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)}, deadRound facts roots heads algebra rigid complete declared choices reducer
      root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck →
    underRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel depth problem =
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem
  | 0, _, _, _ => rfl
  | depth + 1, _, problem, moving => by
      change underStep facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel _ problem = _
      unfold underStep
      cases computed : deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem with
      | stuck => exact absurd computed moving
      | progress update smaller => rfl
      | refuted absent => rfl

/-- **Every run that the dead-binder family decides, the under-binder family decides with the same outcome.** -/
theorem under_run_of_dead (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((underFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => underRoundAt_eq_of_dead facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel _ moving)
    rounds _ decided

/-- **The under-binder round fires wherever the dead-binder round does.** -/
theorem underRound_not_stuck_of_dead (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold underRound
  rw [underRoundAt_eq_of_dead facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel _ moving]
  exact moving

/-! ## Eventual constancy -/

theorem underRoundAt_view (fuel depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (underRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (depth + 1) problem) =
      (roundView (deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (roundView (underSearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel
          (fun stored => underRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel depth stored)
          problem (List.range problem.length))) := by
  change roundView (underStep facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel _ problem) = _
  unfold underStep
  cases deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem underAt_const {Θ : Context S.R}
    (inner : Nat → (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (constant : ∀ stored, EventuallyConst fun fuel => inner fuel stored) :
    ∀ stored : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      underAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel (inner fuel) stored
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.dep (h := fun fuel => readDead facts roots heads algebra declared choices reducer fuel
          (lamDepth equation.1.2.code) equation)
        (k := fun fuel (found : Option {reduced : Equation (TotalTerm Θ) // DropsDead equation reduced}) =>
          (match found with
            | none => .stuck
            | some found => dropRound facts roots heads algebra rigid complete strengthening found.property
                (inner fuel (found.val :: rest)) :
            Round S.levels (weightRank facts roots heads algebra rigid complete) (equation :: rest)))
        (readDead_const facts roots heads algebra declared choices reducer stable _ equation)
        (fun found => by
          cases found with
          | none => exact EventuallyConst.const _
          | some found =>
              exact EventuallyConst.comp (dropRound facts roots heads algebra rigid complete strengthening
                found.property) (constant _))

include stable in
theorem underSearch_const {Θ : Context S.R}
    (inner : Nat → (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (constant : ∀ stored, EventuallyConst fun fuel => inner fuel stored) (problem : EquationStore (TotalTerm Θ)) :
    ∀ rotations : List Nat, EventuallyConst fun fuel =>
      underSearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel (inner fuel)
        problem rotations
  | [] => EventuallyConst.const _
  | k :: ks => by
      obtain ⟨t₁, first⟩ := (underAt_const facts roots heads algebra rigid complete declared choices reducer
        strengthening stable inner constant (problem.rotate k)).spec
      obtain ⟨t₂, later⟩ := (underSearch_const inner constant problem ks).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [underSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

include stable in
/-- **The under-binder round is eventually constant on every store, at every depth.** -/
theorem underRoundAt_const : ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel => underRoundAt facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel depth problem
  | 0, _, problem => EventuallyConst.of_eq (fun _ => rfl) (deadRound_const facts roots heads algebra rigid complete
      declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem)
  | depth + 1, _, problem => by
      refine round_const_of_view ?_
      refine EventuallyConst.of_eq (fun fuel => underRoundAt_view facts roots heads algebra rigid complete declared
        choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel depth problem) ?_
      exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
          Option (Option (Update S.levels problem)) => pair.1.or pair.2)
        (EventuallyConst.pair
          (EventuallyConst.comp roundView (deadRound_const facts roots heads algebra rigid complete declared choices
            reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
          (EventuallyConst.comp roundView (underSearch_const facts roots heads algebra rigid complete declared choices
            reducer strengthening stable
            (fun fuel stored => underRoundAt facts roots heads algebra rigid complete declared choices reducer root
              normalizes certifyNormal headTypingUnique rootComplete strengthening fuel depth stored)
            (fun stored => underRoundAt_const depth stored) problem _)))

include stable in
/-- **The under-binder family settles** on every class on which, from some budget on, its round is not stuck and
keeps the class. -/
noncomputable def underSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (underFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => underRoundAt_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable (deadDepth problem)
    problem) holds eventual

/-! ## Closure -/

variable (sn : StronglyNormalizing S.R)

include sn in
theorem underAt_keeps (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (keeps : KeepsAt facts roots heads algebra rigid complete inner) :
    KeepsAt facts roots heads algebra rigid complete
      (underAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner) := by
  intro stored update smaller permuted fired
  cases stored with
  | nil => cases fired
  | cons equation rest =>
      simp only [underAt] at fired
      split at fired
      · cases fired
      · rename_i found _
        exact transferRound_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
          (fun first firstSmaller computed => keeps _ first firstSmaller
            (PermutedMiller.dropsDead facts roots rigid sn strengthening found.property permuted) computed) fired

include sn in
theorem underSearch_keeps (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (keeps : KeepsAt facts roots heads algebra rigid complete inner) (problem : EquationStore (TotalTerm Θ)) :
    ∀ (rotations : List Nat) (update : Update S.levels problem)
      (smaller : ContextualDependentWorklist.Below
        (weightRank facts roots heads algebra rigid complete update.remaining)
        (weightRank facts roots heads algebra rigid complete problem)),
      PermutedMiller S.levels problem →
      underSearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner problem
        rotations = .progress update smaller → PermutedMiller S.levels update.remaining
  | [], _, _, _, fired => by cases fired
  | k :: ks, update, smaller, permuted, fired => by
      simp only [underSearch] at fired
      cases computed : underAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel
          inner (problem.rotate k) with
      | stuck =>
          rw [computed] at fired
          exact underSearch_keeps fuel inner keeps problem ks update smaller permuted fired
      | progress first firstSmaller =>
          rw [computed] at fired
          exact transferRound_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
            (fun first' firstSmaller' same => by
              cases same
              exact underAt_keeps facts roots heads algebra rigid complete declared choices reducer strengthening sn
                fuel inner keeps _ first firstSmaller (permuted.perm (List.rotate_perm problem k).symm) computed)
            fired
      | refuted absent =>
          rw [computed] at fired
          cases fired

include sn in
theorem underStep_keeps (fuel : Nat) {Θ : Context S.R}
    (lower : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (keepsLower : KeepsAt facts roots heads algebra rigid complete lower)
    (keepsDead : KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel stored) :
    KeepsAt facts roots heads algebra rigid complete
      (underStep facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel lower) := by
  intro problem update smaller permuted fired
  unfold underStep at fired
  cases computed : deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact underSearch_keeps facts roots heads algebra rigid complete declared choices reducer strengthening sn fuel
        lower keepsLower problem _ update smaller permuted fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact keepsDead problem _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn in
theorem underRoundAt_keeps (fuel : Nat)
    (keepsDead : ∀ {Θ : Context S.R}, KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel stored) :
    ∀ (depth : Nat) {Θ : Context S.R}, KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      underRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel depth stored
  | 0, _ => keepsDead
  | depth + 1, _ => fun problem update smaller permuted fired =>
      underStep_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening sn fuel _ (underRoundAt_keeps fuel keepsDead depth) keepsDead
        problem update smaller permuted fired

variable (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
  reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

include sn directed in
/-- **Closure of the under-binder round** at every budget. -/
theorem underRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  have keepsDead : ∀ {Θ : Context S.R}, KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel stored := fun {_} =>
    (keepsPermutedNormal_iff facts roots heads algebra rigid complete sn _).mp
      (deadRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening fuel
        (cumulativeRound_keepsPermutedNormal facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal headTypingUnique rootComplete sn directed fuel))
  intro Θ problem update smaller permuted fired
  exact underRoundAt_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening sn fuel keepsDead (deadDepth problem) problem update
    smaller permuted fired

include sn directed stable in
/-- **Conditional decision for the under-binder family, from firing**: on a strongly normalizing package without root
computation whose reducer returns reducts and is monotone in its budget, and where typed equality strengthens past an
unused variable, if the family's round is eventually not stuck on nonempty stores of the permuted class, the family
decides every store of the dynamic pattern fragment, with a principal answer or a certified refutation, constant at
every larger budget. At the tower's setting the conclusion fails on `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails. For every store, runs
are exact; on `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem under_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((underFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((underFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((underFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((underFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (underSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        underRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The under-binder family of the tower controls. -/
noncomputable def underTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  underFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- **Conditional decision for the tower's under-binder family, from firing**, on every store of the dynamic pattern
fragment; no rule obligation remains. At the tower firing fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_under_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → underTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (underTower.solver larger) problem larger = run (underTower.solver budget) problem budget ∧
      ((∃ state finished, run (underTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (underTower.solver larger) problem larger = .refuted absent)) :=
  under_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
