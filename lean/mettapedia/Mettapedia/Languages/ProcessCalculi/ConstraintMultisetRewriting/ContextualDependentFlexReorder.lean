import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEliminationsRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMetaArityRank

/-!
# Flex–flex across a declaration: reorder, then solve in place

R76's prune rule reads `G ȳ ≐ F x̄` for the newest metavariable `G` and the **next older** `F`: it prunes `G` to the
intersection with `F`'s arguments, exchanges `F` and the pruned metavariable, and solves `F`. With a declaration `D`
between them (`…, F, D, G`) the rule does not apply, and R97's in-place search does not either, since the equation
mentions the newest declaration `G`.

The **reorder rule** moves `G` down. When `G`'s type does not mention `D` (it strengthens past `D` and is formed again
by the type former), the two are exchanged, an isomorphism of contexts (`ContextualDependentPrune.exchange`). Now `D`
is the newest declaration; the store is separated past it (R97's `separation`), the rule one depth lower runs on the
equations that do not mention `D`, and its outcome is carried back past `D` (`carry`). At depth `0` the rule is R97's
first rule: the pattern rule, the adjacent prune rule and the adjacent exchange rule (`reorderAt`).

Every part is an update of the store it reads, so a solved outcome keeps exactly the solutions, and a refutation of a
part refutes the store. A solved outcome removes a declaration (the depth-`0` rule does), so the progress carries the
decrease of the **first component** of R97's `weightRank` in its type (`below_of_arity`); no statement about the weight
is needed.

The **reorder round** is R107's eliminations round, and when that round is stuck, the reorder rule at every depth on
the store as it is (`reorderRound`). It is conservative over the eliminations round (`reorderRound_eq_of_elims`,
`reorder_decided_of_elims`), eventually constant (`reorderRound_const`), and settles where it is not stuck
(`reorderSettledOfConst`). It fires wherever the reorder rule fires (`reorderRound_not_stuck_of_reorder`), and the rule
at depth `d + 1` fires when the newest declaration is independent of the one below it and the rule at depth `d` fires
on the separated store (`reorderAt_isSome`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFlexReorder

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentInPlace ContextualDependentEliminations
open ContextualDependentConversionBudget
open ContextualDependentParameterExchange (second)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
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

/-! ## Exchanging, then solving below the moved declaration -/

/-- **Finish after an exchange**: an outcome on the exchanged store is an outcome on the store. -/
def afterExchange {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (exchanged : Update S.levels problem)
    (same : exchanged.target.arity = Γ.arity) : Option (Found exchanged.remaining) → Option (Found problem)
  | none => none
  | some (.solved solved smaller) => some (.solved (exchanged.then solved) (by
      change solved.target.arity < Γ.arity
      omega))
  | some (.refuted absent) => some (.refuted fun solvable => absent (exchanged.solvable_iff.mp solvable))

/-- **Exchange the two newest declarations, then solve below the moved one.** When the newest declaration does not
depend on the one below it, the two are exchanged; the store is separated past the moved declaration, now the newest;
`solve` runs on the separated store, and its outcome is carried back and composed with the exchange. -/
def exchangeThen (fuel : Nat)
    (solve : {Γ : Context S.R} → (stored : EquationStore (TotalTerm Γ)) → Option (Found stored))
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) : Option (Found problem) := by
  exact
  match ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
  | none => none
  | some code =>
      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀ code with
      | none => none
      | some next =>
          if same : newer.code = (second older next.val).code ∧ newer.level = (second older next.val).level then by
            have independent : newer = second older next.val := TypeOver.ext same.1 same.2
            subst independent
            exact afterExchange (ContextualDependentPrune.exchange S.levels older next.val problem) rfl
              ((solve (separation facts roots heads algebra declared choices reducer fuel (second next.val older)
                  (ContextualDependentPrune.exchange S.levels older next.val problem).remaining).val.1).map
                (carry (second next.val older) (separation facts roots heads algebra declared choices reducer fuel
                  (second next.val older) (ContextualDependentPrune.exchange S.levels older next.val problem).remaining).property))
          else none

/-! ## The reorder rule -/

/-- **Reorder and solve at one depth.** At depth `0`, R97's first rule; at depth `d + 1`, exchange the two newest
declarations and run depth `d` below the moved one. -/
def reorderAt (fuel : Nat) : (depth : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (Found problem)
  | 0, _, problem => firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem
  | depth + 1, Θ, problem =>
      match newestOf facts roots heads algebra declared choices reducer fuel Θ with
      | none => none
      | some outer =>
          match newestOf facts roots heads algebra declared choices reducer fuel outer.base with
          | none => none
          | some inner => throughTwo outer inner problem fun older newer stored =>
              exchangeThen facts roots heads algebra declared choices reducer fuel
                (fun separated => reorderAt fuel depth separated) older newer stored

/-- Try the depths in turn. -/
def reorderSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : List Nat →
    Option (Found problem)
  | [] => none
  | depth :: rest =>
      match reorderAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel depth problem with
      | some found => some found
      | none => reorderSearch fuel problem rest

/-- **The reorder rule**: every depth from `1` below the number of declarations. -/
def reorderRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  reorderSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique fuel problem (List.range' 1 (Θ.arity - 1))

/-! ## The round -/

/-- **One reorder round**: the eliminations round; when it is stuck, the reorder rule on the store as it is. -/
def reorderRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match reorderRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel problem with
      | some (.solved update smaller) => .progress update (below_of_arity facts roots heads algebra rigid complete smaller)
      | some (.refuted absent) => .refuted absent
      | none => .stuck
  | other => other

/-- **The reorder family**, at the weight rank. -/
noncomputable def reorderFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Conservativity over the eliminations family -/

/-- **The reorder round makes the move of the eliminations round wherever that round moves.** -/
theorem reorderRound_eq_of_elims (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold reorderRound
  cases computed : elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the eliminations family decides, the reorder family decides with the same outcome.** -/
theorem reorder_run_of_elims (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => reorderRound_eq_of_elims facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that the eliminations family decides at a joint budget, the reorder family decides at that
budget**, with the same outcome at every larger joint budget. -/
theorem reorder_decided_of_elims {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((elimsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => reorder_run_of_elims facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-! ## Firing -/

/-- **The reorder round is not stuck where the reorder rule decides.** -/
theorem reorderRound_not_stuck_of_reorder (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (reorderRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel problem).isSome) :
    reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold reorderRound
  cases elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      cases found with
      | solved update smaller => exact fun impossible => by cases impossible
      | refuted absent => exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- The search decides when one of its depths does. -/
theorem reorderSearch_isSome_of_mem (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {depth : Nat} (fires : (reorderAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel depth problem).isSome) :
    ∀ depths : List Nat, depth ∈ depths →
      (reorderSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem depths).isSome
  | [], member => absurd member List.not_mem_nil
  | first :: rest, member => by
      simp only [reorderSearch]
      cases computed : reorderAt facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel first problem with
      | some found => rfl
      | none =>
          rcases List.mem_cons.mp member with same | later
          · subst same
            rw [computed] at fires
            cases fires
          · exact reorderSearch_isSome_of_mem fuel problem fires rest later

/-- **The reorder rule decides when one depth between `1` and the number of declarations does.** -/
theorem reorderRule_isSome_of_depth (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {depth : Nat} (positive : 1 ≤ depth) (inside : depth < Θ.arity)
    (fires : (reorderAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel depth problem).isSome) :
    (reorderRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel problem).isSome :=
  reorderSearch_isSome_of_mem facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique fuel problem fires _ (List.mem_range'_1.mpr ⟨positive, by omega⟩)

/-- **The exchange step decides when the solver below decides**: if the newest declaration strengthens past the one
below it, its strengthened type is formed at the budget and agrees with it, and `solve` decides on the separated
exchanged store, then the exchange step decides. -/
theorem exchangeThen_isSome (fuel : Nat)
    (solve : {Γ : Context S.R} → (stored : EquationStore (TotalTerm Γ)) → Option (Found stored))
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) {code : Tm Head Γ₀.arity} (next : {type : TypeOver Γ₀ // type.code = code})
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) (second older next.val))))
    (inverted : ContextualDependentInversion.invert (withoutNewest Γ₀.arity) (second older next.val).code = some code)
    (formed : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀ code =
      some next)
    (fires : (solve (separation facts roots heads algebra declared choices reducer fuel (second next.val older)
      (ContextualDependentPrune.exchange S.levels older next.val problem).remaining).val.1).isSome) :
    (exchangeThen facts roots heads algebra declared choices reducer fuel solve older (second older next.val)
      problem).isSome := by
  unfold exchangeThen
  simp only [inverted, formed, and_self, dite_true]
  obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp fires
  rw [computed]
  cases found with
  | solved update smaller => rfl
  | refuted absent => rfl

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The exchange step is eventually constant** when the solver below it is, on every store. -/
theorem exchangeThen_const
    (solve : Nat → {Γ : Context S.R} → (stored : EquationStore (TotalTerm Γ)) → Option (Found stored))
    (constant : ∀ {Γ : Context S.R} (stored : EquationStore (TotalTerm Γ)), EventuallyConst fun fuel => solve fuel stored)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    EventuallyConst fun fuel =>
      exchangeThen facts roots heads algebra declared choices reducer fuel (solve fuel) older newer problem := by
  cases inverted : ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      dsimp only
      unfold exchangeThen
      simp only [inverted]
  | some code =>
      obtain ⟨t₁, formed⟩ := (formType_const facts roots heads algebra declared choices reducer stable
        (Γ := Γ₀) code).spec
      cases next : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer t₁ Γ₀ code with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          unfold exchangeThen
          simp only [inverted]
          erw [formed fuel enough, next]
      | some formedType =>
          by_cases same : newer.code = (second older formedType.val).code ∧
              newer.level = (second older formedType.val).level
          · have independent : newer = second older formedType.val := TypeOver.ext same.1 same.2
            subst independent
            obtain ⟨t₂, solved⟩ := (EventuallyConst.dep
              (h := fun fuel => separation facts roots heads algebra declared choices reducer fuel
                (second formedType.val older)
                (ContextualDependentPrune.exchange S.levels older formedType.val problem).remaining)
              (k := fun fuel separated => afterExchange (ContextualDependentPrune.exchange S.levels older formedType.val
                  problem) rfl ((solve fuel separated.val.1).map (carry (second formedType.val older) separated.property)))
              (separation_const facts roots heads algebra declared choices reducer stable (second formedType.val older)
                (ContextualDependentPrune.exchange S.levels older formedType.val problem).remaining)
              (fun separated => EventuallyConst.comp (fun found => afterExchange
                  (ContextualDependentPrune.exchange S.levels older formedType.val problem) rfl
                  (found.map (carry (second formedType.val older) separated.property)))
                (constant separated.val.1))).spec
            refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
            dsimp only
            unfold exchangeThen
            simp only [inverted]
            erw [formed fuel (le_of_max_le_left enough), next, formed _ (le_max_left _ _), next]
            dsimp only
            rw [dif_pos same, dif_pos same]
            exact (solved fuel (le_of_max_le_right enough)).trans (solved _ (le_max_right _ _)).symm
          · refine ⟨t₁, fun fuel enough => ?_⟩
            dsimp only
            unfold exchangeThen
            simp only [inverted]
            erw [formed fuel enough, next]
            dsimp only
            rw [dif_neg same, dif_neg same]

include stable in
/-- **The reorder rule at every depth is eventually constant on every store.** -/
theorem reorderAt_const : ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel =>
      reorderAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel depth problem
  | 0, _, problem => firstRule_const rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique stable problem
  | depth + 1, Θ, problem => by
      obtain ⟨t₁, outerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
      cases outer : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          simp only [reorderAt]
          erw [outerSame fuel enough, outer]
      | some outerView =>
          obtain ⟨t₂, innerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable
            outerView.base).spec
          cases inner : newestOf facts roots heads algebra declared choices reducer t₂ outerView.base with
          | none =>
              refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
              dsimp only
              simp only [reorderAt]
              erw [outerSame fuel (le_of_max_le_left enough), outer, outerSame _ (le_max_left _ _), outer]
              dsimp only
              erw [innerSame fuel (le_of_max_le_right enough), inner, innerSame _ (le_max_right _ _), inner]
          | some innerView =>
              obtain ⟨t₃, through⟩ := (throughTwo_const outerView innerView problem
                (fun fuel {_} older newer stored => exchangeThen facts roots heads algebra declared choices reducer
                  fuel (fun stored => reorderAt facts roots heads algebra rigid complete declared choices reducer root
                    normalizes certifyNormal headTypingUnique fuel depth stored) older newer stored)
                (fun older newer stored => exchangeThen_const facts roots heads algebra declared choices reducer stable
                  (fun fuel {_} stored => reorderAt facts roots heads algebra rigid complete declared choices reducer
                    root normalizes certifyNormal headTypingUnique fuel depth stored)
                  (fun stored => reorderAt_const depth stored) older newer stored)).spec
              refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
              have e₁ : t₁ ≤ fuel := by omega
              have e₂ : t₂ ≤ fuel := by omega
              have e₃ : t₃ ≤ fuel := by omega
              dsimp only
              simp only [reorderAt]
              erw [outerSame fuel e₁, outer, outerSame _ (by omega), outer]
              dsimp only
              erw [innerSame fuel e₂, inner, innerSame _ (by omega), inner]
              dsimp only
              exact (through fuel e₃).trans (through _ (by omega)).symm

include stable in
/-- The search through the depths is eventually constant. -/
theorem reorderSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, EventuallyConst fun fuel =>
      reorderSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem depths
  | [] => EventuallyConst.const _
  | depth :: rest => by
      obtain ⟨t₁, first⟩ := (reorderAt_const facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique stable depth problem).spec
      obtain ⟨t₂, later⟩ := (reorderSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [reorderSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

include stable in
/-- **The reorder rule is eventually constant on every store.** -/
theorem reorderRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      reorderRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem :=
  reorderSearch_const facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique stable problem _

theorem reorderRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (ContextualDependentPatternFiring.foundView (reorderRule facts roots heads algebra rigid complete declared
          choices reducer root normalizes certifyNormal headTypingUnique fuel problem)) := by
  unfold reorderRound
  cases elimsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases reorderRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel problem with
      | some found =>
          cases found with
          | solved update smaller => rfl
          | refuted absent => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The reorder round is eventually constant on every store.** -/
theorem reorderRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => reorderRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => reorderRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (elimsRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp ContextualDependentPatternFiring.foundView (reorderRule_const facts roots heads algebra
        rigid complete declared choices reducer root normalizes certifyNormal headTypingUnique stable problem)))

include stable in
/-- **The reorder family settles** on every class of stores on which, at each nonempty store and from some budget
on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def reorderSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          reorderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (reorderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => reorderRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentFlexReorder
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
