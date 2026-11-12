import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSigma
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthAnyBase

/-!
# The base family: spines of one local decomposed at every base type

**The decomposition** (`baseNormal`). An equation of the η-long prepared store whose sides are spines of one bound
local, at an annotation that is a base type as it stands (a universe, an identity type, or a neutral type: a variable
or an application or projection of one), is replaced by its argument pieces, read along the reducer's reducts of the
instantiated types (`readSpines`), with the piece annotations at the reducer's reducts. The step

* has exactly the equation's solutions at every solution, whatever the solution makes of the base type
  (`SpineRel.subst`, `SpineRel.exact`);
* weighs at least two less (`SpineRel.weight`), so it is a committed step of the weight rank;
* keeps the permuted Miller class (`baseNormal_keeps`), through the generic splice of related pieces;
* is eventually constant in the budget (`baseNormal_const`).

**The base family** (`baseFamily`) runs the Σ round and, when that round is stuck, one such decomposition on the
η-long prepared store. It is conservative over the Σ family (`base_run_of_sigma`), eventually constant
(`baseRound_const`), and closed in the permuted Miller class (`baseRound_closure`). It decides every store of the
fragment if it fires (`base_decided_of_firing`, `tower_base_decided_of_firing`, `tower_base_decided_of_baseReads`).
These are conditional decisions; at the tower the hypothesis fails, since the conclusion would decide `crossStore`,
solvable and without principal answer (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For
every store, runs are exact; on `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
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
open ContextualDependentSpinesMany ContextualDependentShortClosure ContextualDependentClosure ContextualDependentEtaLong
open ContextualDependentRigidFormers

/-! ## The decomposition -/

section Normal

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
variable (reducer : ExecutableReduction.Reducer S.R)

/-- Finish the decomposition between spines of one local at a base type as it stands. -/
def finishBase {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (read : SpineRel S.R true [] equation.1.1.code equation.1.2.code equation.2.2.code pieces)
    (store : PieceStore facts roots heads algebra rigid complete pieces) :
    WeighedParts facts roots heads algebra rigid complete equation :=
  ⟨⟨store.val, fun {Δ} σ => by
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have moved := read.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _))
        (Nat.zero_le _)
      rw [List.map_nil] at moved
      have exactly := moved.exact facts roots heads algebra rigid complete Δ.formed (LocalTypes.nil _) tl tr
      rw [solves_raw, same, store.property.1 σ]
      constructor
      · rintro ⟨_, held⟩ piece member
        exact exactly.mp held _ (List.mem_map.mpr ⟨piece, member, rfl⟩)
      · intro held
        refine ⟨(Typed.isType tl Δ.formed).refl, exactly.mpr fun piece member => ?_⟩
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact held original inside⟩, by
    have tr := equation.2.2.typed
    rw [same] at tr
    obtain ⟨w, wl, wr, weighs, ⟨v, nv, wv⟩, ⟨v', nv', wv'⟩, total⟩ :=
      read.weight facts roots heads algebra rigid complete Θ.formed (LocalTypes.nil _) equation.1.2.typed tr
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

/-- **The decomposition between spines of one local at a base type as it stands**, along the reducts of the
instantiated types, at normal annotations. -/
def baseNormal (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    (readSpines reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code).bind fun read =>
      (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
        (read.property.typed facts roots heads Θ.formed (LocalTypes.nil _) equation.1.2.typed
          (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
        (finishBase facts roots heads algebra rigid complete equation same read.property)
  else none

/-- **Decompose the first equation between spines of one local at a base type.** -/
def decomposeBase (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (baseNormal facts roots heads algebra rigid complete reducer declared choices fuel equation,
        decomposeBase fuel rest)

/-- **The decomposition round at every base type.** -/
def baseNormalRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  decomposedRound facts roots heads algebra rigid complete
    (decomposeBase facts roots heads algebra rigid complete reducer declared choices fuel problem)

/-! ### The codes of the decomposition -/

theorem baseNormal_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : baseNormal facts roots heads algebra rigid complete reducer declared choices fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      ∃ pieces, SpineRel S.R true [] equation.1.1.code equation.1.2.code equation.2.2.code pieces ∧
        List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) weighed.val.val pieces := by
  unfold baseNormal at found
  split at found
  · rename_i same
    obtain ⟨read, _, formedSome⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp formedSome
    exact ⟨same, read.val, read.property, formRelated_codes facts roots heads algebra rigid complete reducer
      declared choices fuel _ formed⟩
  · cases found

/-- **The decomposition reads an equation** whose sides are read and whose pieces are formed. -/
theorem baseNormal_isSome (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (same : equation.2.1.code = equation.1.1.code)
    {read : {pieces : List (Piece Head Θ.arity) //
      SpineRel S.R true [] equation.1.1.code equation.1.2.code equation.2.2.code pieces}}
    (found : readSpines reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code = some read)
    (formed : ∀ typed, (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
      typed).isSome) :
    (baseNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome := by
  unfold baseNormal
  rw [dif_pos same, found]
  simp only [Option.bind_some]
  rw [Option.isSome_map]
  exact formed _

/-- **The search reads a store with an equation that decomposes.** -/
theorem decomposeBase_isSome (fuel : Nat) {Θ : Context S.R} :
    ∀ {problem : EquationStore (TotalTerm Θ)} {equation : Equation (TotalTerm Θ)}, equation ∈ problem →
      (baseNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome →
      (decomposeBase facts roots heads algebra rigid complete reducer declared choices fuel problem).isSome
  | [], _, member, _ => absurd member List.not_mem_nil
  | first :: rest, equation, member, read => by
      simp only [decomposeBase]
      unfold decomposeStep
      cases computed : baseNormal facts roots heads algebra rigid complete reducer declared choices fuel first with
      | some weighed => rfl
      | none =>
          rcases List.mem_cons.mp member with rfl | later
          · rw [computed] at read
            cases read
          · dsimp only
            rw [Option.isSome_map]
            exact decomposeBase_isSome fuel later read

/-! ### Closure -/

/-- **The decomposition keeps the class.** -/
theorem baseNormal_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (baseNormal facts roots heads algebra rigid complete reducer declared choices fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, pieces, read, related⟩ := baseNormal_codes facts roots heads algebra rigid complete reducer
    declared choices fuel found
  have empty := computation_empty rigid
  refine PermutedMiller.splice_related rigid sn permuted
    (fun leftReduct rightReduct => read.reducts empty (fun _ => true)
      (fun _ small => absurd small (Nat.not_lt_zero _)) leftReduct rightReduct)
    (fun {Δ} σ first last piece split held => ?_) weighed.val.val related fun σ => (weighed.val.property σ).symm
  have tl := equation.1.2.typed.substitute σ.typed
  have tr := equation.2.2.typed.substitute σ.typed
  rw [same] at tr
  have moved := read.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
  rw [List.map_nil] at moved
  exact moved.internal facts roots heads Δ.formed (LocalTypes.nil _) tl tr
    (first.map (Piece.subst σ.substitution)) (last.map (Piece.subst σ.substitution)) (piece.subst σ.substitution)
    (by rw [split]; simp)
    (fun q member => by
      obtain ⟨q', inFirst, rfl⟩ := List.mem_map.mp member
      exact held q' inFirst)

theorem decomposeBase_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), PositionKeeps facts roots heads algebra rigid complete
      (decomposeBase facts roots heads algebra rigid complete reducer declared choices fuel problem)
  | [] => fun _ found => by cases found
  | equation :: rest => decomposeStep_keeps facts roots heads algebra rigid complete equation rest
      (baseNormal_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel equation)
      (decomposeBase_keeps sn fuel rest)

/-- **The decomposition round keeps the class.** -/
theorem baseNormalRound_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem)
    (update : Update S.levels problem)
    (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem))
    (fired : baseNormalRound facts roots heads algebra rigid complete reducer declared choices fuel problem =
      .progress update smaller) :
    PermutedMiller S.levels update.remaining := by
  unfold baseNormalRound at fired
  cases computed : decomposeBase facts roots heads algebra rigid complete reducer declared choices fuel problem with
  | none =>
      rw [computed] at fired
      cases fired
  | some found =>
      rw [computed] at fired
      cases fired
      exact decomposeBase_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel problem
        found computed [] permuted

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem baseNormal_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      baseNormal facts roots heads algebra rigid complete reducer declared choices fuel equation := by
  unfold baseNormal
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    exact EventuallyConst.dep
      (h := fun fuel => readSpines reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code)
      (k := fun fuel found => found.bind fun read =>
        (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
          (read.property.typed facts roots heads Θ.formed (LocalTypes.nil _) equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishBase facts roots heads algebra rigid complete equation same read.property))
      (readSpines_const reducer stable _ _ _)
      (fun found => by
        cases found with
        | none => exact EventuallyConst.const _
        | some read =>
            simp only [Option.bind_some]
            exact EventuallyConst.comp _ (formNormal_const facts roots heads algebra rigid complete reducer declared
              choices stable read.val _))
  · simp only [same, dite_false]
    exact EventuallyConst.const _

include stable in
theorem decomposeBase_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      decomposeBase facts roots heads algebra rigid complete reducer declared choices fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (baseNormal_const facts roots heads algebra rigid complete reducer declared choices stable equation)
          (decomposeBase_const rest))

include stable in
theorem baseNormalRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      baseNormalRound facts roots heads algebra rigid complete reducer declared choices fuel problem :=
  EventuallyConst.comp (decomposedRound facts roots heads algebra rigid complete)
    (decomposeBase_const facts roots heads algebra rigid complete reducer declared choices stable problem)

end Normal

/-! ## The base family -/

section Rule

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
  (strengthening : EqualStrengthening S.R)

/-- **The base round**: the Σ round; when it is stuck, the decomposition between spines of one local at every base
type, on the η-long prepared store. -/
noncomputable def baseRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (baseNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))

/-- **The base family**, at the weight rank. -/
noncomputable def baseFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ### Conservativity and readers -/

theorem baseRound_eq_of_sigma (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold baseRound
  cases computed : sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the Σ family decides, the base family decides with the same outcome.** -/
theorem base_run_of_sigma (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((sigmaFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((baseFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((sigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => baseRound_eq_of_sigma facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

/-- **The base reader**: the round moves wherever the decomposition at every base type reads the η-long prepared
store. -/
theorem baseRound_not_stuck_of_normal (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (decomposeBase facts roots heads algebra rigid complete reducer declared choices fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome) :
    baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold baseRound
  obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
  cases sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      refine liftCollapsed_not_stuck facts roots heads algebra rigid complete _
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem) ?_
      unfold baseNormalRound
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The base family's readers**: a reader of the Σ family, or the decomposition at every base type of the η-long
prepared store. -/
def BaseReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  SigmaReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    (decomposeBase facts roots heads algebra rigid complete reducer declared choices fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome

theorem baseRound_not_stuck_of_baseReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : BaseReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with sigma | normal
  · have moving := sigmaRound_not_stuck_of_sigmaReads facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel sigma
    rw [baseRound_eq_of_sigma facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel moving]
    exact moving
  · exact baseRound_not_stuck_of_normal facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel normal

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

theorem baseRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) =
      (roundView (sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (liftView (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
          (roundView (baseNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
            (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))) := by
  unfold baseRound
  rw [roundView_orElse, liftCollapsed_view]

include stable in
/-- **The base round is eventually constant on every store.** -/
theorem baseRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => baseRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => baseRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (sigmaRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
      (EventuallyConst.dep (h := fun fuel => longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (k := fun fuel prepared => liftView prepared
          (roundView (baseNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
            prepared.remaining)))
        (longUpdate_const facts roots heads algebra reducer root rootComplete stable problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (baseNormalRound_const facts roots heads algebra rigid complete reducer declared choices stable
            prepared.remaining))))

include stable in
/-- **The base family settles** on every class on which, from some budget on, its round is not stuck and keeps the
class. -/
noncomputable def baseSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (baseFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => baseRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

/-! ### Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

include sn directed in
/-- **Closure of the base round** at every budget. -/
theorem baseRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (baseNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) =
      .progress update smaller at fired
  cases computed : sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
        (fun first firstSmaller inner => baseNormalRound_keeps facts roots heads algebra rigid complete reducer
          declared choices sn fuel
          (longUpdate_keeps facts roots heads algebra rigid reducer root rootComplete sn fuel permuted)
          first firstSmaller inner) fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact sigmaRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Conditional decision for the base family, from firing**: on a strongly normalizing package without root
computation whose reducer returns reducts and is monotone in its budget, and where typed equality strengthens past an
unused variable, if the family's round is eventually not stuck on nonempty stores of the permuted class, the family
decides every store of the dynamic pattern fragment, with a principal answer or a certified refutation, constant at
every larger budget. At the tower's setting the conclusion fails on `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails. For every store, runs
are exact; on `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem base_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((baseFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((baseFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((baseFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((baseFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (baseSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        baseRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The base family of the tower controls. -/
noncomputable def baseTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  baseFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- Readers of the tower's base family at one budget. -/
abbrev TowerBaseReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  BaseReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Conditional decision for the tower's base family, from firing**, on every store of the dynamic pattern
fragment. At the tower firing fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_base_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → baseTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (baseTower.solver larger) problem larger = run (baseTower.solver budget) problem budget ∧
      ((∃ state finished, run (baseTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (baseTower.solver larger) problem larger = .refuted absent)) :=
  base_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

/-- **Conditional decision for the tower's base family, from eventual reading**, on every store of the dynamic
pattern fragment. At the tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_base_decided_of_baseReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerBaseReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (baseTower.solver larger) problem larger = run (baseTower.solver budget) problem budget ∧
      ((∃ state finished, run (baseTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (baseTower.solver larger) problem larger = .refuted absent)) :=
  tower_base_decided_of_firing (fun permuted nonempty => by
      obtain ⟨bound, eventually⟩ := reads permuted nonempty
      exact ⟨bound, fun larger enough => baseRound_not_stuck_of_baseReads (S := setting) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid
        TowerModel.complete ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
        ContextualDependentInversion.Controls.reducer (fun _ => none)
        ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
        ContextualDependentGeneralPattern.DispatchControls.certifyNormal
        ContextualDependentNormalCheckingTower.head_typing_unique
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening larger
        (eventually larger enough)⟩)
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
