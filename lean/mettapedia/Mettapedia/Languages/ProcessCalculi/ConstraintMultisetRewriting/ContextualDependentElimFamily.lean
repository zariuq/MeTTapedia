import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimRelUnder

/-!
# The mixed family: elimination spines of one local decomposed at every base type

**The decomposition** (`mixedNormal`). An equation of the η-long prepared store whose sides are elimination spines of
one bound local, applications and projections in any order, at an annotation that is a base type as it stands, is
replaced by its argument pieces, read along the reducer's reducts of the types read (`readElims`), with the piece
annotations at the reducer's reducts. The step

* has exactly the equation's solutions at every solution, whatever the solution makes of the base type
  (`ElimSpines.subst`, `ElimSpines.exact`);
* weighs at least two less (`ElimSpines.weight`), so it is a committed step of the weight rank;
* keeps the permuted Miller class (`mixedNormal_keeps`), through the generic splice of related pieces;
* is eventually constant in the budget (`mixedNormal_const`).

**The mixed family** (`mixedFamily`) runs the base round and, when that round is stuck, one such decomposition on
the η-long prepared store. It is conservative over the base family (`mixed_run_of_base`), eventually constant
(`mixedRound_const`), and closed in the permuted Miller class (`mixedRound_closure`). It decides every store of the
fragment if it fires (`mixed_decided_of_firing`, `tower_mixed_decided_of_firing`, `tower_mixed_decided_of_mixedReads`).
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

/-- Finish the decomposition between elimination spines of one local at a base type as it stands. -/
def finishMixed {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (read : ElimSpines S.R true [] equation.1.1.code equation.1.2.code equation.2.2.code pieces)
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

/-- **The decomposition between elimination spines of one local at a base type as it stands**, along the reducts of
the types read, at normal annotations. -/
def mixedNormal (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    (readElims reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code).bind fun read =>
      (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
        (read.property.typed facts roots heads Θ.formed (LocalTypes.nil _) equation.1.2.typed
          (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
        (finishMixed facts roots heads algebra rigid complete equation same read.property)
  else none

/-- **Decompose the first equation between elimination spines of one local at a base type.** -/
def decomposeMixed (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (mixedNormal facts roots heads algebra rigid complete reducer declared choices fuel equation,
        decomposeMixed fuel rest)

/-- **The decomposition round of elimination spines at every base type.** -/
def mixedNormalRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  decomposedRound facts roots heads algebra rigid complete
    (decomposeMixed facts roots heads algebra rigid complete reducer declared choices fuel problem)

/-! ### The codes of the decomposition -/

theorem mixedNormal_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : mixedNormal facts roots heads algebra rigid complete reducer declared choices fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      ∃ pieces, ElimSpines S.R true [] equation.1.1.code equation.1.2.code equation.2.2.code pieces ∧
        List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) weighed.val.val pieces := by
  unfold mixedNormal at found
  split at found
  · rename_i same
    obtain ⟨read, _, formedSome⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp formedSome
    exact ⟨same, read.val, read.property, formRelated_codes facts roots heads algebra rigid complete reducer
      declared choices fuel _ formed⟩
  · cases found

/-- **The decomposition reads an equation** whose sides are read and whose pieces are formed. -/
theorem mixedNormal_isSome (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (same : equation.2.1.code = equation.1.1.code)
    {read : {pieces : List (Piece Head Θ.arity) //
      ElimSpines S.R true [] equation.1.1.code equation.1.2.code equation.2.2.code pieces}}
    (found : readElims reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code = some read)
    (formed : ∀ typed, (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
      typed).isSome) :
    (mixedNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome := by
  unfold mixedNormal
  rw [dif_pos same, found]
  simp only [Option.bind_some]
  rw [Option.isSome_map]
  exact formed _

/-- **The search reads a store with an equation that decomposes.** -/
theorem decomposeMixed_isSome (fuel : Nat) {Θ : Context S.R} :
    ∀ {problem : EquationStore (TotalTerm Θ)} {equation : Equation (TotalTerm Θ)}, equation ∈ problem →
      (mixedNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).isSome →
      (decomposeMixed facts roots heads algebra rigid complete reducer declared choices fuel problem).isSome
  | [], _, member, _ => absurd member List.not_mem_nil
  | first :: rest, equation, member, read => by
      simp only [decomposeMixed]
      unfold decomposeStep
      cases computed : mixedNormal facts roots heads algebra rigid complete reducer declared choices fuel first with
      | some weighed => rfl
      | none =>
          rcases List.mem_cons.mp member with rfl | later
          · rw [computed] at read
            cases read
          · dsimp only
            rw [Option.isSome_map]
            exact decomposeMixed_isSome fuel later read

/-! ### Closure -/

/-- **The decomposition keeps the class.** -/
theorem mixedNormal_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (mixedNormal facts roots heads algebra rigid complete reducer declared choices fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, pieces, read, related⟩ := mixedNormal_codes facts roots heads algebra rigid complete reducer
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

theorem decomposeMixed_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), PositionKeeps facts roots heads algebra rigid complete
      (decomposeMixed facts roots heads algebra rigid complete reducer declared choices fuel problem)
  | [] => fun _ found => by cases found
  | equation :: rest => decomposeStep_keeps facts roots heads algebra rigid complete equation rest
      (mixedNormal_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel equation)
      (decomposeMixed_keeps sn fuel rest)

/-- **The decomposition round keeps the class.** -/
theorem mixedNormalRound_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem)
    (update : Update S.levels problem)
    (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem))
    (fired : mixedNormalRound facts roots heads algebra rigid complete reducer declared choices fuel problem =
      .progress update smaller) :
    PermutedMiller S.levels update.remaining := by
  unfold mixedNormalRound at fired
  cases computed : decomposeMixed facts roots heads algebra rigid complete reducer declared choices fuel problem with
  | none =>
      rw [computed] at fired
      cases fired
  | some found =>
      rw [computed] at fired
      cases fired
      exact decomposeMixed_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel problem
        found computed [] permuted

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem mixedNormal_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      mixedNormal facts roots heads algebra rigid complete reducer declared choices fuel equation := by
  unfold mixedNormal
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    exact EventuallyConst.dep
      (h := fun fuel => readElims reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code)
      (k := fun fuel found => found.bind fun read =>
        (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
          (read.property.typed facts roots heads Θ.formed (LocalTypes.nil _) equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishMixed facts roots heads algebra rigid complete equation same read.property))
      (readElims_const reducer stable _ _ _)
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
theorem decomposeMixed_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      decomposeMixed facts roots heads algebra rigid complete reducer declared choices fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (mixedNormal_const facts roots heads algebra rigid complete reducer declared choices stable equation)
          (decomposeMixed_const rest))

include stable in
theorem mixedNormalRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      mixedNormalRound facts roots heads algebra rigid complete reducer declared choices fuel problem :=
  EventuallyConst.comp (decomposedRound facts roots heads algebra rigid complete)
    (decomposeMixed_const facts roots heads algebra rigid complete reducer declared choices stable problem)

end Normal

/-! ## The mixed family -/

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

/-- **The mixed round**: the base round; when it is stuck, the decomposition between elimination spines of one local
at every base type, on the η-long prepared store. -/
noncomputable def mixedRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (mixedNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))

/-- **The mixed family**, at the weight rank. -/
noncomputable def mixedFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ### Conservativity and readers -/

theorem mixedRound_eq_of_base (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold mixedRound
  cases computed : baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the base family decides, the mixed family decides with the same outcome.** -/
theorem mixed_run_of_base (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((baseFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((mixedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((baseFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => mixedRound_eq_of_base facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

/-- **The mixed reader**: the round moves wherever the decomposition between elimination spines reads the η-long
prepared store. -/
theorem mixedRound_not_stuck_of_normal (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (decomposeMixed facts roots heads algebra rigid complete reducer declared choices fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome) :
    mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold mixedRound
  obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
  cases baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      refine liftCollapsed_not_stuck facts roots heads algebra rigid complete _
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem) ?_
      unfold mixedNormalRound
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The mixed family's readers**: a reader of the base family, or the decomposition between elimination spines of
the η-long prepared store. -/
def MixedReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  BaseReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    (decomposeMixed facts roots heads algebra rigid complete reducer declared choices fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome

theorem mixedRound_not_stuck_of_mixedReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : MixedReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with base | normal
  · have moving := baseRound_not_stuck_of_baseReads facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel base
    rw [mixedRound_eq_of_base facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel moving]
    exact moving
  · exact mixedRound_not_stuck_of_normal facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel normal

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

theorem mixedRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) =
      (roundView (baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (liftView (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
          (roundView (mixedNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
            (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))) := by
  unfold mixedRound
  rw [roundView_orElse, liftCollapsed_view]

include stable in
/-- **The mixed round is eventually constant on every store.** -/
theorem mixedRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => mixedRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => mixedRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (baseRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
      (EventuallyConst.dep (h := fun fuel => longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (k := fun fuel prepared => liftView prepared
          (roundView (mixedNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
            prepared.remaining)))
        (longUpdate_const facts roots heads algebra reducer root rootComplete stable problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (mixedNormalRound_const facts roots heads algebra rigid complete reducer declared choices stable
            prepared.remaining))))

include stable in
/-- **The mixed family settles** on every class on which, from some budget on, its round is not stuck and keeps the
class. -/
noncomputable def mixedSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (mixedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => mixedRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

/-! ### Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

include sn directed in
/-- **Closure of the mixed round** at every budget. -/
theorem mixedRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (mixedNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) =
      .progress update smaller at fired
  cases computed : baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
        (fun first firstSmaller inner => mixedNormalRound_keeps facts roots heads algebra rigid complete reducer
          declared choices sn fuel
          (longUpdate_keeps facts roots heads algebra rigid reducer root rootComplete sn fuel permuted)
          first firstSmaller inner) fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact baseRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Conditional decision for the mixed family, from firing**: on a strongly normalizing package without root
computation whose reducer returns reducts and is monotone in its budget, and where typed equality strengthens past an
unused variable, if the family's round is eventually not stuck on nonempty stores of the permuted class, the family
decides every store of the dynamic pattern fragment, with a principal answer or a certified refutation, constant at
every larger budget. At the tower's setting the conclusion fails on `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails. For every store, runs
are exact; on `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem mixed_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((mixedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((mixedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((mixedFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((mixedFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (mixedSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        mixedRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The mixed family of the tower controls. -/
noncomputable def mixedTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  mixedFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- Readers of the tower's mixed family at one budget. -/
abbrev TowerMixedReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  MixedReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Every run that the tower's base family decides, its mixed family decides with the same outcome.** -/
theorem tower_mixed_run_of_base (fuel rounds : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run (baseTower.solver fuel) problem rounds).Decided) :
    run (mixedTower.solver fuel) problem rounds = run (baseTower.solver fuel) problem rounds :=
  mixed_run_of_base (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel rounds problem
    decided

/-- **Conditional decision for the tower's mixed family, from firing**, on every store of the dynamic pattern
fragment. At the tower firing fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_mixed_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → mixedTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (mixedTower.solver larger) problem larger = run (mixedTower.solver budget) problem budget ∧
      ((∃ state finished, run (mixedTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (mixedTower.solver larger) problem larger = .refuted absent)) :=
  mixed_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

/-- **Conditional decision for the tower's mixed family, from eventual reading**, on every store of the dynamic
pattern fragment. At the tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_mixed_decided_of_mixedReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerMixedReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (mixedTower.solver larger) problem larger = run (mixedTower.solver budget) problem budget ∧
      ((∃ state finished, run (mixedTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (mixedTower.solver larger) problem larger = .refuted absent)) :=
  tower_mixed_decided_of_firing (fun permuted nonempty => by
      obtain ⟨bound, eventually⟩ := reads permuted nonempty
      exact ⟨bound, fun larger enough => mixedRound_not_stuck_of_mixedReads (S := setting) TowerModel.facts
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
