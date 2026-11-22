import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceRounds

/-!
# Firing in place: the inversion row for an older metavariable

R97's in-place rule solves a pattern for an older metavariable `F` of `Γ, F, D₁, …, D_d` by separating the store
at each later declaration: the equations that do not mention `D_d` are read over the shorter context, solved there,
and the answer is carried back past `D_d` (`ContextualDependentInPlace.carry`). At depth `0` it runs the syntactic
pattern rule.

The **placed rule** is the same search with the conversion pattern rule at depth `0` (`placedAt`), and the **placed
round** runs it on the store as it is when the firing round is stuck (`placedRound`). A carried answer removes `F`,
so it lowers the weight rank by its first component. The placed round is conservative over the firing round
(`placedRound_eq_of_firing`, `placed_decided_of_firing`) and eventually constant (`placedRound_const`).

**The placed row** (`PlacedRow`) at depth `d`: through every view of the `d` later declarations, the equation is
read without them (`Weakens`), with normal codes, and every such reading is the inversion row one level down; at depth
`0` it is the inversion row with the hypotheses of `patternRuleConv_fires`. Strengthening a typed side with normal
codes succeeds from some budget on (`strengthen_eventually`), the separated store keeps it (`separate_mem`), so the
placed rule fires on the row (`placedAt_fires`), and the placed round is not stuck there (`placedRound_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentInPlace

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **`strong` is `equation` read without the newest declaration**: each code of `equation` is the weakening of the
corresponding code of `strong`. -/
def Weakens {Γ : Context S.R} {type : TypeOver Γ} (strong : Equation (TotalTerm Γ))
    (equation : Equation (TotalTerm (extend Γ type))) : Prop :=
  rename wk strong.1.1.code = equation.1.1.code ∧ rename wk strong.1.2.code = equation.1.2.code ∧
    rename wk strong.2.1.code = equation.2.1.code ∧ rename wk strong.2.2.code = equation.2.2.code

theorem throughNewest_extend {Γ : Context S.R} {type : TypeOver Γ}
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (solve : (stored : EquationStore (TotalTerm (extend Γ type))) → Option (Found stored)) :
    ContextualDependentPatternSolver.throughNewest ⟨Γ, type, rfl⟩ problem solve = solve problem := rfl

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

/-! ## The placed rule and round -/

/-- **Solving at one depth below the newest declaration**, with the conversion pattern rule at depth `0`. -/
def placedAt (fuel : Nat) : (depth : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (Found problem)
  | 0, _, problem => ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared
      choices reducer rigid complete root normalizes certifyNormal fuel problem
  | depth + 1, Θ, problem =>
      match newestOf facts roots heads algebra declared choices reducer fuel Θ with
      | none => none
      | some view => ContextualDependentPatternSolver.throughNewest view problem fun stored =>
          (placedAt fuel depth (separation facts roots heads algebra declared choices reducer fuel view.type
              stored).val.1).map
            (carry view.type (separation facts roots heads algebra declared choices reducer fuel view.type
              stored).property)

/-- Try the depths in turn. -/
def placedSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : List Nat →
    Option (Found problem)
  | [] => none
  | depth :: rest =>
      match placedAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          fuel depth problem with
      | some found => some found
      | none => placedSearch fuel problem rest

/-- **The placed rule**: every depth below the newest declaration. -/
def placedRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  placedSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal fuel
    problem (List.range' 1 (Θ.arity - 1))

/-- **One placed round**: the firing round; when it is stuck, the placed rule on the store as it is. -/
def placedRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match placedRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          fuel problem with
      | some (.solved update smaller) => .progress update (below_of_arity facts roots heads algebra rigid complete smaller)
      | some (.refuted absent) => .refuted absent
      | none => .stuck
  | other => other

/-- **The placed family**, at the weight rank. -/
noncomputable def placedFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Conservativity over the firing family -/

/-- **The placed round makes the move of the firing round wherever that round moves.** -/
theorem placedRound_eq_of_firing (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold placedRound
  cases computed : firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the firing family decides, the placed family decides with the same outcome.** -/
theorem placed_run_of_firing (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((firingFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((firingFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => placedRound_eq_of_firing facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the firing family decides at a joint budget, the placed family decides at that budget**, with
the same outcome at every larger joint budget. -/
theorem placed_decided_of_firing {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((firingFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((firingFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => placed_run_of_firing facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-- **Every store that R99's arguments family decides at a joint budget, the placed family decides at that budget**,
with the same outcome at every larger joint budget. -/
theorem placed_decided_of_arguments {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((ContextualDependentIdEndpointsArguments.argumentsFamily facts roots heads algebra rigid complete declared
        choices reducer root normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem
          larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((ContextualDependentIdEndpointsArguments.argumentsFamily facts roots heads algebra rigid complete declared
          choices reducer root normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger := by
  intro larger enough
  have same := firing_decided_of_arguments facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete decided larger enough
  have firingDecided : (run ((firingFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided := by
    rw [same]
    exact decided larger enough
  rw [placed_run_of_firing facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete larger larger problem firingDecided, same]

/-- The placed round is not stuck where the firing round is not. -/
theorem placedRound_not_stuck_of_firing (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  rw [placedRound_eq_of_firing facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel moving]
  exact moving

/-- **The placed rows.** When the placed rule decides, the placed round is not stuck. -/
theorem placedRound_not_stuck_of_placed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (placedRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      fuel problem).isSome) :
    placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold placedRound
  cases firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      cases found with
      | solved update smaller => exact fun impossible => by cases impossible
      | refuted absent => exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- The search decides when one of its depths does. -/
theorem placedSearch_isSome_of_mem (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {depth : Nat} (fires : (placedAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal fuel depth problem).isSome) :
    ∀ depths : List Nat, depth ∈ depths →
      (placedSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel problem depths).isSome
  | [], member => absurd member List.not_mem_nil
  | first :: rest, member => by
      simp only [placedSearch]
      cases computed : placedAt facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal fuel first problem with
      | some found => rfl
      | none =>
          rcases List.mem_cons.mp member with same | later
          · subst same
            rw [computed] at fires
            cases fires
          · exact placedSearch_isSome_of_mem fuel problem fires rest later

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The placed rule at every depth is eventually constant on every store.** -/
theorem placedAt_const : ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel =>
      placedAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal fuel
        depth problem
  | 0, _, problem => ContextualDependentRecognitionConversion.patternRuleConv_const facts roots heads algebra declared
      choices reducer rigid complete root normalizes certifyNormal stable problem
  | depth + 1, Θ, problem => by
      obtain ⟨t₁, viewed⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
      cases viewRun : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          simp only [placedAt]
          erw [viewed fuel enough, viewRun]
      | some view =>
          obtain ⟨t₂, solved⟩ := (ContextualDependentDecisiveFragment.throughNewest_const view problem
            (fun fuel stored =>
              (placedAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
                fuel depth (separation facts roots heads algebra declared choices reducer fuel view.type stored).val.1).map
                (carry view.type (separation facts roots heads algebra declared choices reducer fuel view.type
                  stored).property))
            (fun stored => EventuallyConst.dep
              (h := fun fuel => separation facts roots heads algebra declared choices reducer fuel view.type stored)
              (k := fun fuel separated =>
                (placedAt facts roots heads algebra rigid complete declared choices reducer root normalizes
                  certifyNormal fuel depth separated.val.1).map (carry view.type separated.property))
              (separation_const facts roots heads algebra declared choices reducer stable view.type stored)
              (fun separated => EventuallyConst.comp (Option.map (carry view.type separated.property))
                (placedAt_const depth separated.val.1)))).spec
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          simp only [placedAt]
          erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
          exact (solved fuel (le_of_max_le_right enough)).trans (solved _ (le_max_right _ _)).symm

include stable in
/-- The search through the depths is eventually constant. -/
theorem placedSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, EventuallyConst fun fuel =>
      placedSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel problem depths
  | [] => EventuallyConst.const _
  | depth :: rest => by
      obtain ⟨t₁, first⟩ := (placedAt_const facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal stable depth problem).spec
      obtain ⟨t₂, later⟩ := (placedSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [placedSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

include stable in
/-- **The placed rule is eventually constant on every store.** -/
theorem placedRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      placedRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal fuel
        problem :=
  placedSearch_const facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    stable problem _

theorem placedRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (foundView (placedRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal fuel problem)) := by
  unfold placedRound
  cases firingRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases placedRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          fuel problem with
      | some found =>
          cases found with
          | solved update smaller => rfl
          | refuted absent => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The placed round is eventually constant on every store.** -/
theorem placedRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => placedRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => placedRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) × Option (Found problem) =>
      pair.1.or (foundView pair.2))
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (firingRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (placedRule_const facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        stable problem))

include stable in
/-- **The placed family settles** on every class of stores on which, at each nonempty store and from some budget on,
its round is not stuck and keeps every residual store in the class. -/
noncomputable def placedSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          placedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (placedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => placedRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end General

/-! ## Firing on the placed row, in the tower -/

section Tower

open ExecutableReduction ExecutableChecking ContextualDependentExecutableJoin ContextualDependentExecutableConversion
open ContextualDependentExecutableChecking ContextualDependentExecutableDiscovery ContextualDependentDynamicFragment

variable {L : Type} [UniverseLevel.LevelOrder L]
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

local instance settingHeadEqPlaced (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniversePlaced (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulativePlaced (valuation : Nat → L) :
    DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

variable (valuation : Nat → L)

/-- **Strengthening a side read without the newest declaration succeeds** from some budget on, when its codes are
normal: the inverted type code is formed, and the inverted term is recovered at it. -/
theorem strengthen_eventually {Γ : Context (TowerModel.setting valuation).R} (type : TypeOver Γ)
    (side : TotalTerm (extend Γ type)) (strong : TotalTerm Γ)
    (typeCode : rename wk strong.1.code = side.1.code) (termCode : rename wk strong.2.code = side.2.code)
    (typeNormal : Normal (LevelTower.rules L) side.1.code) (termNormal : Normal (LevelTower.rules L) side.2.code) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (strengthen (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra declared tc red larger type side).isSome := by
  have strongNormal : Normal (LevelTower.rules L) strong.1.code := by
    rw [← typeCode] at typeNormal
    exact normal_of_rename wk typeNormal
  obtain ⟨f₁, formed, forms⟩ := formType_stable valuation (Γ := Γ) strongNormal strong.1.isType
  let recovered : ContextualDependentTypedInversion.Recovery (ContextualDependentFlex.withoutNewest Γ type) formed.val
      side.2.code :=
    ⟨⟨strong.2.code, by rw [formed.property]; exact strong.2.typed⟩, termCode⟩
  obtain ⟨f₂, recovers⟩ := recover_eventually valuation (ContextualDependentFlex.withoutNewest Γ type) formed.val
    recovered termNormal
  have inverted : ContextualDependentInversion.invert
      (ContextualDependentInversion.lookup (wk : Ren Γ.arity (Γ.arity + 1))) side.1.code = some strong.1.code := by
    rw [← typeCode]
    exact ContextualDependentInversion.invert_rename strong.1.code wk _
      (ContextualDependentInversion.lookup_exact wk (Fin.succ_injective _))
  have coded : strengthenCode (n := Γ.arity) side.1.code = some ⟨strong.1.code, typeCode⟩ := by
    unfold strengthenCode
    split
    · rename_i missing
      rw [inverted] at missing
      cases missing
    · rename_i found computed
      rw [inverted] at computed
      cases computed
      rfl
  refine ⟨max f₁ f₂, fun larger enough => ?_⟩
  unfold strengthen
  rw [coded, Option.bind_some]
  dsimp only
  erw [forms larger (by omega)]
  rw [Option.bind_some]
  erw [recovers larger (by omega)]
  rfl

/-- **Separation keeps an equation whose sides strengthen**: its strengthening is among the separated equations. -/
theorem separate_mem (fuel : Nat) {Γ : Context (TowerModel.setting valuation).R} (type : TypeOver Γ)
    {equation : Equation (TotalTerm (extend Γ type))}
    (leftSome : (strengthen (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra declared tc red fuel type equation.1).isSome)
    (rightSome : (strengthen (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra declared tc red fuel type equation.2).isSome) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), equation ∈ problem →
      ∃ strong ∈ (separate (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra declared tc red fuel type problem).1, Weakens strong equation
  | [], member => absurd member List.not_mem_nil
  | first :: rest, member => by
      rcases List.mem_cons.mp member with same | later
      · subst same
        obtain ⟨left, leftRun⟩ := Option.isSome_iff_exists.mp leftSome
        obtain ⟨right, rightRun⟩ := Option.isSome_iff_exists.mp rightSome
        simp only [separate, leftRun, rightRun]
        exact ⟨(left.val, right.val), List.mem_cons_self, left.property.1, left.property.2, right.property.1,
          right.property.2⟩
      · obtain ⟨strong, inside, weakens⟩ := separate_mem fuel type leftSome rightSome rest later
        refine ⟨strong, ?_, weakens⟩
        simp only [separate]
        split
        · exact List.mem_cons_of_mem _ inside
        · exact inside

/-- **The placed row at a depth.** At depth `0`: the dynamic pattern fragment, a normal newest declaration, and the
inversion row through every view of it. At depth `d + 1`: a normal newest declaration `D`, normal codes, and through
every view of `D` the equation is read without `D`, and every such reading is in the placed row at depth `d`. -/
def PlacedRow : (depth : Nat) → {Θ : Context (TowerModel.setting valuation).R} → Equation (TotalTerm Θ) → Prop
  | 0, Θ, equation => InFragment equation ∧ ∃ nonempty : 0 < Θ.arity,
      Normal (LevelTower.rules L) (Ctx.lookup Θ.raw ⟨0, nonempty⟩) ∧
      ∀ view : Newest Θ, InversionRow (view.same ▸ equation)
  | depth + 1, Θ, equation =>
      (∃ nonempty : 0 < Θ.arity, Normal (LevelTower.rules L) (Ctx.lookup Θ.raw ⟨0, nonempty⟩)) ∧
      Normal (LevelTower.rules L) equation.1.1.code ∧ Normal (LevelTower.rules L) equation.1.2.code ∧
      Normal (LevelTower.rules L) equation.2.1.code ∧ Normal (LevelTower.rules L) equation.2.2.code ∧
      ∀ view : Newest Θ, (∃ strong : Equation (TotalTerm view.base), Weakens strong (view.same ▸ equation)) ∧
        ∀ strong : Equation (TotalTerm view.base), Weakens strong (view.same ▸ equation) → PlacedRow depth strong

/-- A placed row at depth `d` lives below at least `d + 1` declarations. -/
theorem PlacedRow.depth_lt : ∀ (depth : Nat) {Θ : Context (TowerModel.setting valuation).R}
    {equation : Equation (TotalTerm Θ)}, PlacedRow valuation depth equation → depth < Θ.arity
  | 0, _, _, row => by
      unfold PlacedRow at row
      obtain ⟨_, nonempty, _⟩ := row
      exact nonempty
  | depth + 1, Θ, equation, row => by
      unfold PlacedRow at row
      obtain ⟨⟨nonempty, newestNormal⟩, _, _, _, _, rows⟩ := row
      obtain ⟨_, view, _⟩ := newestOf_stable valuation nonempty newestNormal
      obtain ⟨⟨strong, weakens⟩, all⟩ := rows view
      have below := PlacedRow.depth_lt depth (all strong weakens)
      have arity : Θ.arity = view.base.arity + 1 := congrArg Context.arity view.same
      omega

variable (rigid : ∀ name, (TowerModel.setting valuation).roles name = .rigid)
  (complete : AlgorithmicComplete (TowerModel.setting valuation).R (TowerModel.setting valuation).roles)
  (normalizes : ∀ {Θ : Context (TowerModel.setting valuation).R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm (LevelTower.Head L) Θ.arity, ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation)
      code ∧ Equal (TowerModel.setting valuation).R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm (LevelTower.Head L) n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := TowerModel.setting valuation) term)))

/-- **The placed rule fires on the placed row at its depth**, from some budget on. -/
theorem placedAt_fires : ∀ (depth : Nat) {Θ : Context (TowerModel.setting valuation).R}
    (problem : EquationStore (TotalTerm Θ)) {equation : Equation (TotalTerm Θ)}, equation ∈ problem →
    PlacedRow valuation depth equation →
    ∃ bound, ∀ larger, bound ≤ larger →
      (placedAt TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal larger depth problem).isSome
  | 0, _, problem, _, member, row => by
      unfold PlacedRow at row
      obtain ⟨inside, nonempty, newestNormal, rows⟩ := row
      exact patternRuleConv_fires valuation rigid complete normalizes certifyNormal problem member inside nonempty
        newestNormal rows
  | depth + 1, Θ, problem, equation, member, row => by
      unfold PlacedRow at row
      obtain ⟨⟨nonempty, newestNormal⟩, n₁, n₂, n₃, n₄, rows⟩ := row
      obtain ⟨f₀, view, viewStable⟩ := newestOf_stable valuation nonempty newestNormal
      have rowsView := rows view
      rcases view with ⟨base, type, same⟩
      subst same
      obtain ⟨⟨strong, weakens⟩, all⟩ := rowsView
      obtain ⟨f₁, leftRuns⟩ := strengthen_eventually valuation type equation.1 strong.1 weakens.1 weakens.2.1 n₁ n₂
      obtain ⟨f₂, rightRuns⟩ :=
        strengthen_eventually valuation type equation.2 strong.2 weakens.2.2.1 weakens.2.2.2 n₃ n₄
      obtain ⟨f₃, separated⟩ := (separation_const (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red (red_stable (L := L)) type problem).spec
      have stableSeparation : ∀ fuel, f₃ ≤ fuel →
          separation (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
            TowerModel.algebra declared tc red fuel type problem =
          separation (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
            TowerModel.algebra declared tc red f₃ type problem :=
        fun fuel enough => separated fuel enough
      obtain ⟨found, foundMember, foundWeakens⟩ := separate_mem valuation (max f₁ (max f₂ f₃)) type
        (leftRuns _ (by omega)) (rightRuns _ (by omega)) problem member
      have atFixed : separate (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
            TowerModel.algebra declared tc red (max f₁ (max f₂ f₃)) type problem =
          (separation (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots TowerModel.heads
            TowerModel.algebra declared tc red f₃ type problem).val :=
        congrArg Subtype.val (stableSeparation _ (by omega))
      rw [atFixed] at foundMember
      obtain ⟨f₄, fires⟩ := placedAt_fires depth _ foundMember (all found foundWeakens)
      refine ⟨max f₀ (max f₃ f₄), fun larger enough => ?_⟩
      simp only [placedAt]
      erw [viewStable larger (by omega)]
      dsimp only
      rw [throughNewest_extend]
      erw [Option.isSome_map]
      have firesHere := fires larger (by omega)
      rw [← stableSeparation larger (by omega)] at firesHere
      exact firesHere

/-- **The placed rule fires on the placed row** at a positive depth, from some budget on. -/
theorem placedRule_fires {Θ : Context (TowerModel.setting valuation).R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) {depth : Nat} (positive : 0 < depth)
    (row : PlacedRow valuation depth equation) :
    ∃ bound, ∀ larger, bound ≤ larger →
      (placedRule TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal larger problem).isSome := by
  obtain ⟨bound, fires⟩ := placedAt_fires valuation rigid complete normalizes certifyNormal depth problem member row
  have below := PlacedRow.depth_lt valuation depth row
  refine ⟨bound, fun larger enough => placedSearch_isSome_of_mem TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra rigid complete declared tc red (fun _ => none) normalizes certifyNormal larger problem
    (fires larger enough) _ ?_⟩
  rw [List.mem_range'_1]
  omega

variable (headTypingUnique : ∀ {head first second : LevelTower.Head L},
  (TowerModel.setting valuation).R.headTyping head first → (TowerModel.setting valuation).R.headTyping head second →
    first = second)

/-- **The placed round fires on the placed row** at every depth: from some budget on it is not stuck on a store with
an equation of that row. At depth `0` this is the firing round on the inversion row. -/
theorem placedRound_fires {Θ : Context (TowerModel.setting valuation).R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) {depth : Nat}
    (row : PlacedRow valuation depth equation) :
    ∃ bound, ∀ larger, bound ≤ larger →
      placedRound TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra rigid complete declared tc red
        (fun _ => none) normalizes certifyNormal headTypingUnique
        (ContextualDependentNormalizing.tower_rootComplete valuation) larger problem ≠ .stuck := by
  cases depth with
  | zero =>
      unfold PlacedRow at row
      obtain ⟨inside, nonempty, newestNormal, rows⟩ := row
      obtain ⟨bound, fires⟩ := firingRound_fires_inversion valuation rigid complete normalizes certifyNormal
        headTypingUnique problem member inside nonempty newestNormal rows
      exact ⟨bound, fun larger enough => placedRound_not_stuck_of_firing TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra rigid complete declared tc red (fun _ => none) normalizes certifyNormal
        headTypingUnique (ContextualDependentNormalizing.tower_rootComplete valuation) larger (fires larger enough)⟩
  | succ depth =>
      obtain ⟨bound, fires⟩ := placedRule_fires valuation rigid complete normalizes certifyNormal problem member
        (Nat.succ_pos depth) row
      exact ⟨bound, fun larger enough => placedRound_not_stuck_of_placed TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra rigid complete declared tc red (fun _ => none) normalizes certifyNormal
        headTypingUnique (ContextualDependentNormalizing.tower_rootComplete valuation) larger (fires larger enough)⟩

end Tower

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
