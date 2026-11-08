import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpoints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensus

/-!
# The census, read by the rules

The rows of the census whose two opened sides are rigid are read by rules that inspect codes only,
under the common abstractions of the equation. For each such row this module proves that the reading
is complete for the shape, and that the endpoints round is then not stuck:

* **rigid clashes** (`HeadClash`): two neutral terms of different skeletons at a rigid base type, two
  type forms of different kinds at a universe, reflexivity against a neutral term at an identity type,
  under any number of abstractions. The decision reads every such equation (`headClashAt_complete`), and
  a prepared store with homogeneous twins that contains one makes the endpoints round refute
  (`endpointsRound_not_stuck_of_clash`);
* **occurrences** along type-former positions and identity endpoints at a universe (`Inside`): read by
  `occursInside` (`occursInside_complete`), with the same conclusion
  (`endpointsRound_not_stuck_of_inside`);
* **decompositions**: whenever the decomposition finds an equation of the prepared store, the ranked
  abstraction round, and every round built on it, is not stuck (`endpointsRound_not_stuck_of_decomposed`).

Every round of the chain inherits the progress of the round below it: twin, heads, pairs and endpoints
rounds are not stuck when the ranked abstraction round is not (`endpointsRound_not_stuck_of_any`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCensusReadings

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRigidFormers ContextualDependentRank ContextualDependentSpinesMany
open ContextualDependentTwinsUnder ContextualDependentConstantHeads ContextualDependentCensusPairEta
open ContextualDependentIdEndpoints ContextualDependentFragmentDecisive ContextualDependentEtaExpansion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The decisions read every equation of their shapes -/

section Decisions

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- **The head clash decision reads every head clash.** -/
theorem headClashAt_complete {depth n : Nat} {annotation left right : Tm Head n}
    (clash : HeadClash S.R depth annotation left right) : headClashAt (S := S) depth annotation left right = true := by
  induction clash with
  | @base depth n C l r s s' base kl kr differ =>
      have notPi : ∀ D T, C ≠ .pi D T := rigidBase_not_pi base
      have reduces : headClashAt (S := S) depth C l r = headClashBase (S := S) depth C l r := by
        cases C with
        | pi D T => exact absurd rfl (notPi D T)
        | _ => rfl
      rw [reduces]
      unfold headClashBase skeletonsDiffer
      simp [base, kl, kr, differ]
  | @universal depth n u l r k k' hu kl kr differ =>
      change headClashBase (S := S) depth (.head u) l r = true
      unfold headClashBase ContextualDependentConstantHeads.kindsDiffer
      simp [universeCode, hu, kl, kr, differ]
  | @reflNeutral depth n C x y z r s kr =>
      change headClashBase (S := S) depth (.id C x y) (.refl z) r = true
      unfold headClashBase ContextualDependentConstantHeads.reflAgainst
      simp [identityCode, kr]
  | @neutralRefl depth n C x y z l s kl =>
      have reduces : headClashAt (S := S) depth (.id C x y) l (.refl z) =
          headClashBase (S := S) depth (.id C x y) l (.refl z) := rfl
      rw [reduces]
      have against : ContextualDependentConstantHeads.reflAgainst depth (.refl z) l = true := by
        simp only [ContextualDependentConstantHeads.reflAgainst, kl]
      unfold headClashBase
      simp [identityCode, against]
  | bind _ ih => exact ih

/-- **The occurrence decision reads every proper occurrence.** -/
theorem occursInside_complete [DecidableEq Head] {proper : Bool} {n : Nat} {value T : Tm Head n}
    (inside : Inside S.R proper value T) :
    (proper = true → occursInside (S := S) value T = true) ∧ (proper = false → T = value) := by
  induction inside with
  | here value => exact ⟨fun impossible => absurd impossible (by decide), fun _ => rfl⟩
  | @domain isPi proper' n value A B _ ih =>
      refine ⟨fun _ => ?_, fun impossible => absurd impossible (by decide)⟩
      cases proper' with
      | true => cases isPi <;> simp [binder, occursInside, ih.1 rfl]
      | false => cases isPi <;> simp [binder, occursInside, ih.2 rfl]
  | @codomain isPi proper' n value A B _ ih =>
      refine ⟨fun _ => ?_, fun impossible => absurd impossible (by decide)⟩
      cases proper' with
      | true => cases isPi <;> simp [binder, occursInside, ih.1 rfl]
      | false => cases isPi <;> simp [binder, occursInside, ih.2 rfl]
  | @carrier proper' n value A x y _ ih =>
      refine ⟨fun _ => ?_, fun impossible => absurd impossible (by decide)⟩
      cases proper' with
      | true => simp [occursInside, ih.1 rfl]
      | false => simp [occursInside, ih.2 rfl]
  | @left proper' n value x y u hu _ ih =>
      refine ⟨fun _ => ?_, fun impossible => absurd impossible (by decide)⟩
      cases proper' with
      | true => simp [occursInside, universeCode, hu, ih.1 rfl]
      | false => simp [occursInside, universeCode, hu, ih.2 rfl]
  | @right proper' n value x y u hu _ ih =>
      refine ⟨fun _ => ?_, fun impossible => absurd impossible (by decide)⟩
      cases proper' with
      | true => simp [occursInside, universeCode, hu, ih.1 rfl]
      | false => simp [occursInside, universeCode, hu, ih.2 rfl]

end Decisions

/-! ## Store searches find every readable equation -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **A head clash at one annotation code is read.** -/
theorem headClashShape_some {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (same : equation.2.1.code = equation.1.1.code)
    (clash : HeadClash S.R 0 equation.1.1.code equation.1.2.code equation.2.2.code) :
    (headClashShape equation).isSome := by
  unfold headClashShape
  rw [dif_pos same, dif_pos (headClashAt_complete clash)]
  rfl

/-- **The head clash search refutes every store with a readable equation.** -/
theorem headClashSearch_refutes {Θ : Context S.R} :
    ∀ {problem : EquationStore (TotalTerm Θ)}, (∃ equation ∈ problem, (headClashShape equation).isSome) →
      ∃ absent, headClashSearch facts rigid complete problem = some (.refuted absent)
  | [], ⟨_, member, _⟩ => absurd member List.not_mem_nil
  | equation :: rest, ⟨other, member, read⟩ => by
      cases shape : headClashShape equation with
      | some found =>
          refine ⟨fun ⟨_, σ, solved⟩ => found.refutes facts rigid complete σ (solved equation List.mem_cons_self), ?_⟩
          simp only [headClashSearch, shape]
      | none =>
          rcases List.mem_cons.mp member with rfl | inside
          · rw [shape] at read
            cases read
          · obtain ⟨absent, later⟩ := headClashSearch_refutes ⟨other, inside, read⟩
            refine ⟨fun ⟨Δ, σ, modeled⟩ => absent ⟨Δ, σ, fun e m => modeled e (List.mem_cons_of_mem _ m)⟩, ?_⟩
            simp only [headClashSearch, shape, later, Option.map_some]
            rfl

theorem headClashOf_some {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (update : Update S.levels problem)
    (readable : ∃ equation ∈ update.remaining, (headClashShape equation).isSome) :
    (headClashOf facts rigid complete update).isSome := by
  unfold headClashOf
  obtain ⟨absent, found⟩ := headClashSearch_refutes facts rigid complete readable
  rw [found]
  rfl

/-- **The occurrence decision under abstractions reads every such occurrence.** -/
theorem underInsideOccurs_complete {n : Nat} {annotation left right : Tm Head n}
    (under : UnderInside S.R annotation left right) : underInsideOccurs (S := S) annotation left right = true := by
  induction under with
  | @base n u V T hu inside =>
      simp only [underInsideOccurs, hu, decide_true, Bool.true_and]
      exact (occursInside_complete inside).1 rfl
  | bind _ ih => exact ih

/-- **An occurrence under abstractions, at one annotation code, is read.** -/
theorem insideShape_some {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (same : equation.2.1.code = equation.1.1.code)
    (under : UnderInside S.R equation.1.1.code equation.1.2.code equation.2.2.code) :
    (insideShape equation).isSome := by
  unfold insideShape
  rw [dif_pos same, dif_pos (underInsideOccurs_complete under)]
  rfl

/-- **The endpoint occurs search refutes every store with an equation read in the first orientation.** -/
theorem insideSearch_refutes {Θ : Context S.R} :
    ∀ {problem : EquationStore (TotalTerm Θ)}, (∃ equation ∈ problem, (insideShape equation).isSome) →
      ∃ absent, insideSearch facts roots heads algebra rigid complete problem = some (.refuted absent)
  | [], ⟨_, member, _⟩ => absurd member List.not_mem_nil
  | equation :: rest, ⟨other, member, read⟩ => by
      cases shape : insideShape equation with
      | some found =>
          refine ⟨fun ⟨_, σ, solved⟩ => found.refutes facts roots heads algebra rigid complete σ
            (solved equation List.mem_cons_self), ?_⟩
          simp only [insideSearch, shape]
      | none =>
          cases swapped : insideShape (swap equation) with
          | some found =>
              refine ⟨fun ⟨_, σ, solved⟩ => found.refutes facts roots heads algebra rigid complete σ
                ((solves_swap σ equation).mpr (solved equation List.mem_cons_self)), ?_⟩
              simp only [insideSearch, shape, swapped]
          | none =>
              rcases List.mem_cons.mp member with rfl | inside
              · rw [shape] at read
                cases read
              · obtain ⟨absent, later⟩ := insideSearch_refutes ⟨other, inside, read⟩
                refine ⟨fun ⟨Δ, σ, modeled⟩ => absent ⟨Δ, σ, fun e m => modeled e (List.mem_cons_of_mem _ m)⟩, ?_⟩
                simp only [insideSearch, shape, swapped, later, Option.map_some]
                rfl

theorem insideOf_some {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (update : Update S.levels problem)
    (readable : ∃ equation ∈ update.remaining, (insideShape equation).isSome) :
    (insideOf facts roots heads algebra rigid complete update).isSome := by
  unfold insideOf
  obtain ⟨absent, found⟩ := insideSearch_refutes facts roots heads algebra rigid complete readable
  rw [found]
  rfl

/-! ## The chain of rounds -/

variable [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R) (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **The ranked abstraction round is not stuck when its decomposition finds an equation.** -/
theorem anyRound_not_stuck_of_decomposed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining).isSome) :
    anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have rest : anyRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem ≠
      .stuck := by
    unfold anyRest
    split
    · exact fun impossible => by cases impossible
    · obtain ⟨decomposed, computed⟩ := Option.isSome_iff_exists.mp found
      rw [computed]
      exact fun impossible => by cases impossible
  unfold anyRound
  split
  · exact fun impossible => by cases impossible
  · split
    · exact fun impossible => by cases impossible
    · split
      · exact fun impossible => by cases impossible
      · exact rest
    · exact rest

theorem twinRound_not_stuck_of_any (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold twinRound
  cases computed : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

theorem headsRound_not_stuck_of_twin (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold headsRound
  cases computed : twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The heads round refutes when the head clash is read.** -/
theorem headsRound_not_stuck_of_clash (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (headsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome) :
    headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold headsRound
  cases twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp read
      simp only [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

theorem pairsRound_not_stuck_of_heads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold pairsRound
  cases computed : headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

theorem endpointsRound_not_stuck_of_pairs (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold endpointsRound
  cases computed : pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The endpoints round refutes when the endpoint occurs check is read.** -/
theorem endpointsRound_not_stuck_of_endpoints (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (endpointsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome) :
    endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold endpointsRound
  cases pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp read
      simp only [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The endpoints round inherits the progress of the ranked abstraction round.** -/
theorem endpointsRound_not_stuck_of_any (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  endpointsRound_not_stuck_of_pairs facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (pairsRound_not_stuck_of_heads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel
      (headsRound_not_stuck_of_twin facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel
        (twinRound_not_stuck_of_any facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel moving)))

/-! ## The census rows that the rules read -/

/-- **Decomposition row.** When the decomposition finds an equation of the prepared store, the endpoints
round is not stuck. -/
theorem endpointsRound_not_stuck_of_decomposed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining).isSome) :
    endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck :=
  endpointsRound_not_stuck_of_any facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel
    (anyRound_not_stuck_of_decomposed facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel found)

/-- **Clash row.** A prepared store with homogeneous twins that contains a head clash at one annotation code,
under any number of abstractions, makes the endpoints round not stuck. -/
theorem endpointsRound_not_stuck_of_clash (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (clash : ∃ equation ∈ (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining,
      equation.2.1.code = equation.1.1.code ∧
        HeadClash S.R 0 equation.1.1.code equation.1.2.code equation.2.2.code) :
    endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  obtain ⟨equation, member, same, found⟩ := clash
  exact endpointsRound_not_stuck_of_pairs facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel
    (pairsRound_not_stuck_of_heads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel
      (headsRound_not_stuck_of_clash facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel
        (headClashOf_some facts rigid complete _ ⟨equation, member, headClashShape_some same found⟩)))

/-- **Occurrence row.** A prepared store with homogeneous twins that contains an equation
`λ x̄. V ≐ λ x̄. T` at `Π x̄. U`, at one annotation code, with `U` a universe and `V` occurring properly in
`T` along positions and identity endpoints, makes the endpoints round not stuck. -/
theorem endpointsRound_not_stuck_of_inside (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (occurrence : ∃ equation ∈ (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining,
      equation.2.1.code = equation.1.1.code ∧
        UnderInside S.R equation.1.1.code equation.1.2.code equation.2.2.code) :
    endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  obtain ⟨equation, member, same, under⟩ := occurrence
  exact endpointsRound_not_stuck_of_endpoints facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete fuel
    (insideOf_some facts roots heads algebra rigid complete _ ⟨equation, member, insideShape_some same under⟩)

end ContextualDependentCensusReadings
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
