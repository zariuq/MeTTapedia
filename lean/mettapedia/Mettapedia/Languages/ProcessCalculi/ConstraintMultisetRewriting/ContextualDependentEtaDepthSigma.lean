import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthPieces

/-!
# The Σ family: η-expansion at a Σ base

The η-depth families η-expand each side to its annotation's Π count, and the decompositions between spines of one
local read spines only at a rigid base: a universe, an identity type, or a local. At a Σ base two spines of one local,
`h y ≐ h (F y)` at `Σ (x : U0). U0`, are read by nothing (`SigmaControls.sigmaStore`).

**η-expansion at a Σ base** (`sigmaTo`) replaces, under the annotation's Π binders, a spine of a bound local at a Σ
type by the pair of its projections, `t ↦ (fst t, snd t)` (`pair_eta_equal`, `sigmaTo_equal`). The pair has the
solutions of the side, so the expanded store has the store's solutions (`sigma_equivalent`) and weight
(`storeWeight_sigma`), and since the spine's head is a rigid local its projections keep Miller normal reducts
(`MarkedReduct.sigmaTo`), so the expanded store stays in the permuted Miller class (`PermutedMiller.sigma`). The pair is
then decomposed into its projections by the decomposition under abstractions, and the projections of spines of one
local by R99's projection rule; the rounds repeat both expansions on the pieces, so the η-long form at Π and Σ types is
reached step by step.

**The Σ round** (`sigmaRound`) is the piece round; when that is stuck, the piece round on the η-long prepared store
η-expanded at Σ bases. The family is conservative over the piece family (`sigma_run_of_piece`), eventually constant
(`sigmaRound_const`), and closed in the permuted Miller class (`sigmaRound_closure`). So it decides every store of the
dynamic pattern fragment if its round is eventually not stuck on nonempty stores of the class
(`sigma_decided_of_firing`, `tower_sigma_decided_of_firing`), in particular if one of its readers reads (`SigmaReads`,
`tower_sigma_decided_of_sigmaReads`). These are conditional decisions; at the tower the hypothesis fails, since the
conclusion would decide `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
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
open ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure ContextualDependentShortClosure
open ContextualDependentIntersectionGeneral ContextualDependentCoverageReadersHalf

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## η-expansion at a Σ base -/

/-- Whether a term is a spine of a local bound by the `depth` abstractions read so far. -/
def boundSpine {n : Nat} (depth : Nat) (t : Tm Head n) : Bool :=
  match spineHead t with
  | .var j => decide (j.val < depth)
  | _ => false

/-- **η-expansion at a Σ base**, under the annotation's Π binders, of a spine of a bound local. -/
def sigmaTo : {n : Nat} → Nat → Tm Head n → Tm Head n → Tm Head n
  | _, depth, .pi _ T, .lam body => .lam (sigmaTo (depth + 1) T body)
  | _, depth, .sigma _ _, t => if boundSpine depth t then .pair (.fst t) (.snd t) else t
  | _, _, _, t => t

theorem sigmaTo_sigma {n : Nat} (depth : Nat) (A : Tm Head n) (B : Tm Head (n + 1)) (t : Tm Head n) :
    sigmaTo depth (.sigma A B) t = if boundSpine depth t then .pair (.fst t) (.snd t) else t := rfl

theorem sigmaTo_base {n : Nat} {depth : Nat} {T t : Tm Head n}
    (notUnder : ¬ ∃ A B body, T = .pi A B ∧ t = .lam body) (notSigma : ¬ ∃ A B, T = .sigma A B) :
    sigmaTo depth T t = t := by
  cases T with
  | pi A B =>
      cases t with
      | lam body => exact absurd ⟨A, B, body, rfl, rfl⟩ notUnder
      | _ => rfl
  | sigma A B => exact absurd ⟨A, B, rfl⟩ notSigma
  | _ => rfl

theorem boundSpine_spec {n : Nat} {depth : Nat} {t : Tm Head n} (bound : boundSpine depth t = true) :
    ∃ j : Fin n, spineHead t = .var j ∧ j.val < depth := by
  unfold boundSpine at bound
  split at bound
  · rename_i j head
    exact ⟨j, head, of_decide_eq_true bound⟩
  · cases bound

/-- **The Σ η law**: a term of a Σ type is its pair of projections. -/
theorem pair_eta_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t A : Tm Head n}
    {B : Tm Head (n + 1)} (typed : TypedEquality.Typed S.R Γ t (.sigma A B)) :
    Equal S.R Γ t (.pair (.fst t) (.snd t)) (.sigma A B) := by
  obtain ⟨u, hu, sigmaTyped⟩ := Typed.isType typed formed
  have tFst : TypedEquality.Typed S.R Γ (.fst t) A := .fstElim typed
  have tSnd : TypedEquality.Typed S.R Γ (.snd t) (inst0 (.fst t) B) := .sndElim typed
  have tPair : TypedEquality.Typed S.R Γ (.pair (.fst t) (.snd t)) (.sigma A B) := .pairIntro sigmaTyped hu tFst tSnd
  exact .etaSigma typed tPair (.symm (.betaFst sigmaTyped hu tFst tSnd)) (.symm (.betaSnd sigmaTyped hu tFst tSnd))

variable (facts : FormFacts S.R S.roles)

include facts in
/-- **η-expansion at a Σ base is typed equality.** -/
theorem sigmaTo_equal {n : Nat} (depth : Nat) {Γ : Ctx Head n} (T t : Tm Head n) (formed : CtxFormed S.R Γ)
    (typed : TypedEquality.Typed S.R Γ t T) : Equal S.R Γ t (sigmaTo depth T t) T := by
  by_cases under : ∃ A B body, T = .pi A B ∧ t = .lam body
  · obtain ⟨A, B, body, rfl, rfl⟩ := under
    obtain ⟨u, hu, piTyped⟩ := Typed.isType typed formed
    have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed (IsType.pi_parts ⟨u, hu, piTyped⟩).1
    exact .lamCong piTyped hu (sigmaTo_equal (depth + 1) B body formedA (Typed.lam_inv facts typed formed))
  · by_cases sig : ∃ A B, T = .sigma A B
    · obtain ⟨A, B, rfl⟩ := sig
      rw [sigmaTo_sigma]
      split
      · exact pair_eta_equal formed typed
      · exact .refl typed
    · rw [sigmaTo_base under sig]
      exact .refl typed
termination_by sizeOf T

/-! ## Miller reducts -/

section Reducts

variable {R : Rules Head} (empty : R.computation = RootComputation.empty)

omit [UniverseLevel.LevelOrder L] in
theorem isPair_of_spineHead {n : Nat} {X : Tm Head n} {j : Fin n} (head : spineHead X = .var j) :
    isPair X = false := by
  cases X <;> simp_all [spineHead, isPair]

include empty in
/-- **η-expansion at a Σ base keeps Miller normal reducts**, the bound locals rigid. -/
theorem MarkedReduct.sigmaTo {n : Nat} (depth : Nat) (mark : Fin n → Bool) (T t : Tm Head n)
    (bound : ∀ j : Fin n, j.val < depth → mark j = false) (reduct : MarkedReduct R mark t) :
    MarkedReduct R mark (ContextualDependentEtaDepth.sigmaTo depth T t) := by
  by_cases under : ∃ A B body, T = .pi A B ∧ t = .lam body
  · obtain ⟨A, B, body, rfl, rfl⟩ := under
    have lifted : ∀ j : Fin (n + 1), j.val < depth + 1 →
        ContextualDependentGeneralPattern.liftFlexible mark j = false := by
      intro j
      refine Fin.cases (motive := fun j : Fin (n + 1) =>
        j.val < depth + 1 → ContextualDependentGeneralPattern.liftFlexible mark j = false) ?_ (fun j small => ?_) j
      · intro _
        rfl
      · change mark j = false
        simp only [Fin.val_succ] at small
        exact bound j (by omega)
    exact MarkedReduct.lam empty (MarkedReduct.sigmaTo (depth + 1) _ B body lifted
      (MarkedReduct.of_lam empty reduct))
  · by_cases sig : ∃ A B, T = .sigma A B
    · obtain ⟨A, B, rfl⟩ := sig
      rw [sigmaTo_sigma]
      split
      · rename_i spine
        obtain ⟨j, head, small⟩ := boundSpine_spec spine
        obtain ⟨X, toX, normalX, millerX⟩ := reduct
        have headX : spineHead X = .var j := spineHead_star empty head toX
        have notPair := isPair_of_spineHead headX
        have rigidX : flexHead mark (spineHead X) = false := by
          rw [headX]
          exact bound j small
        refine ⟨.pair (.fst X) (.snd X), ?_, ?_, ?_⟩
        · have first := ContextualDependentExecutableJoin.star_fst (R := R) toX
          have second := ContextualDependentExecutableJoin.star_snd (R := R) toX
          exact (ContextualDependentExecutableJoin.star_map (fun x => Tm.pair x (.snd t))
              (fun step => .congPairFst step) first).trans
            (ContextualDependentExecutableJoin.star_map (fun y => Tm.pair (.fst X) y)
              (fun step => .congPairSnd step) second)
        · exact (normal_pair_iff empty).mpr ⟨(normal_fst_iff empty).mpr ⟨notPair, normalX⟩,
            (normal_snd_iff empty).mpr ⟨notPair, normalX⟩⟩
        · simp only [miller, rigidX, millerX, Bool.not_false, Bool.and_self]
      · exact reduct
    · rw [sigmaTo_base under sig]
      exact reduct
termination_by sizeOf T

end Reducts

/-! ## The store η-expanded at Σ bases -/

section Store

/-- A side η-expanded at a Σ base. -/
def sigmaSide {Θ : Context S.R} (term : TotalTerm Θ) : TotalTerm Θ :=
  ⟨term.1, ⟨sigmaTo 0 term.1.code term.2.code,
    (Equal.typed (sigmaTo_equal facts 0 _ _ Θ.formed term.2.typed) Θ.formed).2⟩⟩

theorem sigmaSide_equivalent {Θ : Context S.R} (term : TotalTerm Θ) :
    (frames S.levels).E term (sigmaSide facts term) :=
  ⟨IsType.refl term.1.isType, sigmaTo_equal facts 0 _ _ Θ.formed term.2.typed⟩

/-- **The store η-expanded at Σ bases.** -/
def sigmaExpandStore {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : EquationStore (TotalTerm Θ) :=
  problem.map fun equation => (sigmaSide facts equation.1, sigmaSide facts equation.2)

theorem sigma_solves {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ (sigmaSide facts equation.1, sigmaSide facts equation.2) ↔
      (frames S.levels).Solves σ equation := by
  have first := (frames S.levels).preserves σ (sigmaSide_equivalent facts equation.1)
  have second := (frames S.levels).preserves σ (sigmaSide_equivalent facts equation.2)
  have eqv := (frames S.levels).equivalence Δ
  exact ⟨fun solved => eqv.trans first (eqv.trans solved (eqv.symm second)),
    fun solved => eqv.trans (eqv.symm first) (eqv.trans solved second)⟩

/-- **The store η-expanded at Σ bases has exactly the solutions of the store.** -/
theorem sigma_equivalent {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent problem (sigmaExpandStore facts problem) := fun _ σ => by
  simp only [sigmaExpandStore, Frames.Models, List.forall_mem_map]
  exact forall₂_congr fun equation _ => (sigma_solves facts σ equation).symm

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

/-- **The store η-expanded at Σ bases has the weight of the store.** -/
theorem storeWeight_sigma {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete (sigmaExpandStore facts problem) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      have tail := storeWeight_sigma rest
      simp only [sigmaExpandStore, List.map_cons, storeWeight, equationWeight] at tail ⊢
      rw [tail, ← sideWeight_of_equivalent facts roots heads algebra rigid complete
        (sigmaSide_equivalent facts equation.1), ← sideWeight_of_equivalent facts roots heads algebra rigid complete
        (sigmaSide_equivalent facts equation.2)]

include rigid in
/-- **The store η-expanded at Σ bases stays in the permuted Miller class.** -/
theorem PermutedMiller.sigma (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (sigmaExpandStore facts problem) :=
  PermutedMiller.map_equivalent permuted (sigmaSide facts) (sigmaSide_equivalent facts)
    (fun _ _ sides => by
      obtain ⟨left, right⟩ := side_reduct rigid sn sides
      exact sides_of_reducts (computation_empty rigid)
        (MarkedReduct.sigmaTo (computation_empty rigid) 0 _ _ _ (fun _ small => absurd small (Nat.not_lt_zero _))
          left)
        (MarkedReduct.sigmaTo (computation_empty rigid) 0 _ _ _ (fun _ small => absurd small (Nat.not_lt_zero _))
          right))

end Store

/-! ## The Σ family -/

section Rule

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
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

/-- **The η-long prepared store, η-expanded at Σ bases**, as an update of the store. -/
noncomputable def sigmaUpdate (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Update S.levels problem :=
  (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).then
    ((Update.pending S.levels (sigmaExpandStore facts
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)).rephrase
      (sigma_equivalent facts _))

omit [DecidableRel S.R.cumulative] in
theorem sigmaUpdate_rank (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete
        (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  have long := longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem
  change ((longUpdate facts roots heads algebra reducer root rootComplete fuel problem).target.arity,
    storeWeight facts roots heads algebra rigid complete (sigmaExpandStore facts
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) = _
  rw [storeWeight_sigma]
  exact long

/-- **The Σ round**: the piece round; when it is stuck, the piece round on the η-long prepared store η-expanded at
Σ bases. -/
noncomputable def sigmaRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (sigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))

/-- **The Σ family**, at the weight rank. -/
noncomputable def sigmaFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ### Conservativity and readers -/

theorem sigmaRound_eq_of_piece (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold sigmaRound
  cases computed : pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the piece family decides, the Σ family decides with the same outcome.** -/
theorem sigma_run_of_piece (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((pieceFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((sigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((pieceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => sigmaRound_eq_of_piece facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

/-- **The Σ reader**: the round moves wherever the piece round moves on the η-long prepared store η-expanded at Σ
bases. -/
theorem sigmaRound_not_stuck_of_expanded (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel
      (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining ≠ .stuck) :
    sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold sigmaRound
  cases pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      exact liftCollapsed_not_stuck facts roots heads algebra rigid complete _
        (sigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem) moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The Σ family's readers**: a reader of the piece family, on the store or on its η-long prepared store
η-expanded at Σ bases. -/
def SigmaReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  PieceReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    PieceReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel
      (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining

theorem sigmaRound_not_stuck_of_sigmaReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : SigmaReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with piece | expanded
  · have moving := pieceRound_not_stuck_of_pieceReads facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel piece
    rw [sigmaRound_eq_of_piece facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel moving]
    exact moving
  · exact sigmaRound_not_stuck_of_expanded facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel
      (pieceRound_not_stuck_of_pieceReads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel expanded)

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem sigmaUpdate_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem :=
  EventuallyConst.comp (fun long : Update S.levels problem => long.then
      ((Update.pending S.levels (sigmaExpandStore facts long.remaining)).rephrase (sigma_equivalent facts _)))
    (longUpdate_const facts roots heads algebra reducer root rootComplete stable problem)

theorem sigmaRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) =
      (roundView (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (liftView (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
          (roundView (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel
            (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))) := by
  unfold sigmaRound
  rw [roundView_orElse, liftCollapsed_view]

include stable in
/-- **The Σ round is eventually constant on every store.** -/
theorem sigmaRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => sigmaRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => sigmaRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (pieceRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
      (EventuallyConst.dep (h := fun fuel => sigmaUpdate facts roots heads algebra reducer root rootComplete fuel
          problem)
        (k := fun fuel prepared => liftView prepared
          (roundView (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel prepared.remaining)))
        (sigmaUpdate_const facts roots heads algebra reducer root rootComplete stable problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (pieceRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening stable prepared.remaining))))

include stable in
/-- **The Σ family settles** on every class on which, from some budget on, its round is not stuck and keeps the
class. -/
noncomputable def sigmaSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (sigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => sigmaRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

/-! ### Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

omit [DecidableRel S.R.cumulative] in
include rigid sn in
/-- **The η-long prepared store η-expanded at Σ bases stays in the permuted Miller class.** -/
theorem sigmaUpdate_keeps (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining :=
  PermutedMiller.sigma facts rigid sn (longUpdate_keeps facts roots heads algebra rigid reducer root rootComplete sn
    fuel permuted)

include sn directed in
/-- **Closure of the Σ round** at every budget. -/
theorem sigmaRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (sigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) =
      .progress update smaller at fired
  cases computed : pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
        (sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (sigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
        (fun first firstSmaller inner => pieceRound_closure facts roots heads algebra rigid complete declared choices
          reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ first
          firstSmaller (sigmaUpdate_keeps facts roots heads algebra rigid reducer root rootComplete sn fuel permuted)
          inner) fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact pieceRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Conditional decision for the Σ family, from firing**, on every store of the dynamic pattern fragment, with a
principal answer or a certified refutation, constant at every larger budget. At the tower's setting the conclusion
fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails.
For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem sigma_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((sigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((sigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((sigmaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((sigmaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (sigmaSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        sigmaRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The Σ family of the tower controls. -/
noncomputable def sigmaTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  sigmaFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- Readers of the tower's Σ family at one budget. -/
abbrev TowerSigmaReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  SigmaReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Conditional decision for the tower's Σ family, from firing**, on every store of the dynamic pattern fragment.
At the tower firing fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_sigma_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → sigmaTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (sigmaTower.solver larger) problem larger = run (sigmaTower.solver budget) problem budget ∧
      ((∃ state finished, run (sigmaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (sigmaTower.solver larger) problem larger = .refuted absent)) :=
  sigma_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

/-- **Conditional decision for the tower's Σ family, from eventual reading**, on every store of the dynamic pattern
fragment. At the tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_sigma_decided_of_sigmaReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerSigmaReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (sigmaTower.solver larger) problem larger = run (sigmaTower.solver budget) problem budget ∧
      ((∃ state finished, run (sigmaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (sigmaTower.solver larger) problem larger = .refuted absent)) :=
  tower_sigma_decided_of_firing (fun permuted nonempty => by
      obtain ⟨bound, eventually⟩ := reads permuted nonempty
      exact ⟨bound, fun larger enough => sigmaRound_not_stuck_of_sigmaReads (S := setting) TowerModel.facts
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
