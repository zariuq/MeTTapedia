import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimFamily

/-!
# η-expansion at a Σ base for every elimination spine, and the family above the mixed family

R121's η-expansion at a Σ base (`sigmaTo`) expands a side only when it is an **application** spine of a bound local
(`boundSpine`). An elimination spine with a projection, `fst (g X)` at a Σ type, is refused by that test and the
mixed family is stuck on it, although the η law holds for every term of a Σ type.

**The step** (`elimSigmaTo`) replaces, under the annotation's Π binders, every elimination spine of a bound local at a
Σ type by the pair of its projections (`boundElim`: applications and projections in any order). It agrees with R121's
step wherever that step expands (`boundElim_of_boundSpine`). It is typed equality (`elimSigmaTo_equal`), keeps Miller
normal reducts because the head is a rigid local (`MarkedReduct.elimSigmaTo`), and so the expanded store has the
store's solutions, weight and class (`elimSigma_equivalent`, `storeWeight_elimSigma`, `PermutedMiller.elimSigma`).

**The family** (`elimSigmaFamily`) runs the mixed round and, when that round is stuck, the mixed round on the η-long
prepared store η-expanded at Σ bases. It is conservative over the mixed family (`elimSigma_run_of_mixed`), eventually
constant (`elimSigmaRound_const`), and closed in the permuted Miller class (`elimSigmaRound_closure`). It decides
every store of the fragment if it fires (`elimSigma_decided_of_firing`, `tower_elimSigma_decided_of_firing`). These
are conditional decisions; at the tower the hypothesis fails, since the conclusion would decide `crossStore`, solvable
and without principal answer (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every
store, runs are exact; on `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
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
open ContextualDependentExecutableJoin (Elim)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## η-expansion at a Σ base -/

/-- Whether a term is an elimination spine of a local bound by the `depth` abstractions read so far. -/
def boundElim (depth : Nat) : {n : Nat} → Tm Head n → Bool
  | _, .var j => decide (j.val < depth)
  | _, .app function _ => boundElim depth function
  | _, .fst inner => boundElim depth inner
  | _, .snd inner => boundElim depth inner
  | _, .const _ | _, .head _ | _, .pi _ _ | _, .sigma _ _ | _, .id _ _ _ | _, .lam _ | _, .pair _ _
  | _, .refl _ => false

omit [UniverseLevel.LevelOrder L] in
/-- An elimination spine of a bound local is an elimination spine with a rigid head. -/
theorem boundElim_spec {n depth : Nat} {mark : Fin n → Bool} (bound : ∀ j : Fin n, j.val < depth → mark j = false) :
    ∀ {t : Tm Head n}, boundElim depth t = true → Elim t ∧ flexHead mark (spineHead t) = false
  | .var j, found => ⟨.var j, bound j (of_decide_eq_true found)⟩
  | .app function _, found => ⟨.app (boundElim_spec bound (t := function) found).1,
      (boundElim_spec bound (t := function) found).2⟩
  | .fst inner, found => ⟨.fst (boundElim_spec bound (t := inner) found).1, rfl⟩
  | .snd inner, found => ⟨.snd (boundElim_spec bound (t := inner) found).1, rfl⟩
  | .const _, found | .head _, found | .pi _ _, found | .sigma _ _, found | .id _ _ _, found | .lam _, found
  | .pair _ _, found | .refl _, found => by cases found

omit [UniverseLevel.LevelOrder L] in
/-- **An application spine of a bound local is an elimination spine of one.** -/
theorem boundElim_of_boundSpine {depth : Nat} : ∀ {n : Nat} {t : Tm Head n}, boundSpine depth t = true →
    boundElim depth t = true
  | _, .var j, found => by
      obtain ⟨k, head, small⟩ := boundSpine_spec found
      cases head
      exact decide_eq_true small
  | _, .app function _, found => boundElim_of_boundSpine (t := function) found
  | _, .const _, found | _, .head _, found | _, .pi _ _, found | _, .sigma _ _, found | _, .id _ _ _, found
  | _, .lam _, found | _, .pair _ _, found | _, .fst _, found | _, .snd _, found | _, .refl _, found => by
      obtain ⟨k, head, _⟩ := boundSpine_spec found
      cases head

/-- **η-expansion at a Σ base**, under the annotation's Π binders, of an elimination spine of a bound local. -/
def elimSigmaTo : {n : Nat} → Nat → Tm Head n → Tm Head n → Tm Head n
  | _, depth, .pi _ T, .lam body => .lam (elimSigmaTo (depth + 1) T body)
  | _, depth, .sigma _ _, t => if boundElim depth t then .pair (.fst t) (.snd t) else t
  | _, _, _, t => t

theorem elimSigmaTo_sigma {n : Nat} (depth : Nat) (A : Tm Head n) (B : Tm Head (n + 1)) (t : Tm Head n) :
    elimSigmaTo depth (.sigma A B) t = if boundElim depth t then .pair (.fst t) (.snd t) else t := rfl

theorem elimSigmaTo_base {n : Nat} {depth : Nat} {T t : Tm Head n}
    (notUnder : ¬ ∃ A B body, T = .pi A B ∧ t = .lam body) (notSigma : ¬ ∃ A B, T = .sigma A B) :
    elimSigmaTo depth T t = t := by
  cases T with
  | pi A B =>
      cases t with
      | lam body => exact absurd ⟨A, B, body, rfl, rfl⟩ notUnder
      | _ => rfl
  | sigma A B => exact absurd ⟨A, B, rfl⟩ notSigma
  | _ => rfl

variable (facts : FormFacts S.R S.roles)

include facts in
/-- **η-expansion at a Σ base is typed equality.** -/
theorem elimSigmaTo_equal {n : Nat} (depth : Nat) {Γ : Ctx Head n} (T t : Tm Head n) (formed : CtxFormed S.R Γ)
    (typed : TypedEquality.Typed S.R Γ t T) : Equal S.R Γ t (elimSigmaTo depth T t) T := by
  by_cases under : ∃ A B body, T = .pi A B ∧ t = .lam body
  · obtain ⟨A, B, body, rfl, rfl⟩ := under
    obtain ⟨u, hu, piTyped⟩ := Typed.isType typed formed
    have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed (IsType.pi_parts ⟨u, hu, piTyped⟩).1
    exact .lamCong piTyped hu (elimSigmaTo_equal (depth + 1) B body formedA (Typed.lam_inv facts typed formed))
  · by_cases sig : ∃ A B, T = .sigma A B
    · obtain ⟨A, B, rfl⟩ := sig
      rw [elimSigmaTo_sigma]
      split
      · exact pair_eta_equal formed typed
      · exact .refl typed
    · rw [elimSigmaTo_base under sig]
      exact .refl typed
termination_by sizeOf T

/-! ## Miller reducts -/

section Reducts

variable {R : Rules Head} (empty : R.computation = RootComputation.empty)

include empty in
/-- **η-expansion at a Σ base keeps Miller normal reducts**, the bound locals rigid. -/
theorem MarkedReduct.elimSigmaTo {n : Nat} (depth : Nat) (mark : Fin n → Bool) (T t : Tm Head n)
    (bound : ∀ j : Fin n, j.val < depth → mark j = false) (reduct : MarkedReduct R mark t) :
    MarkedReduct R mark (ContextualDependentEtaDepth.elimSigmaTo depth T t) := by
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
    exact MarkedReduct.lam empty (MarkedReduct.elimSigmaTo (depth + 1) _ B body lifted
      (MarkedReduct.of_lam empty reduct))
  · by_cases sig : ∃ A B, T = .sigma A B
    · obtain ⟨A, B, rfl⟩ := sig
      rw [elimSigmaTo_sigma]
      split
      · rename_i spine
        obtain ⟨elim, head⟩ := boundElim_spec (mark := mark) bound spine
        obtain ⟨X, toX, normalX, millerX⟩ := reduct
        have elimX : Elim X := elim.star empty toX
        have notPair : isPair X = false := by
          cases X <;> first | rfl | exact (Elim.not_pair elimX).elim
        have rigidX : flexHead mark (spineHead X) = false := flexHead_star empty elim head toX
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
    · rw [elimSigmaTo_base under sig]
      exact reduct
termination_by sizeOf T

end Reducts

/-! ## The store η-expanded at Σ bases -/

section Store

/-- A side η-expanded at a Σ base. -/
def elimSigmaSide {Θ : Context S.R} (term : TotalTerm Θ) : TotalTerm Θ :=
  ⟨term.1, ⟨elimSigmaTo 0 term.1.code term.2.code,
    (Equal.typed (elimSigmaTo_equal facts 0 _ _ Θ.formed term.2.typed) Θ.formed).2⟩⟩

theorem elimSigmaSide_equivalent {Θ : Context S.R} (term : TotalTerm Θ) :
    (frames S.levels).E term (elimSigmaSide facts term) :=
  ⟨IsType.refl term.1.isType, elimSigmaTo_equal facts 0 _ _ Θ.formed term.2.typed⟩

/-- **The store η-expanded at Σ bases**, every elimination spine of a bound local. -/
def elimSigmaStore {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : EquationStore (TotalTerm Θ) :=
  problem.map fun equation => (elimSigmaSide facts equation.1, elimSigmaSide facts equation.2)

theorem elimSigma_solves {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ (elimSigmaSide facts equation.1, elimSigmaSide facts equation.2) ↔
      (frames S.levels).Solves σ equation := by
  have first := (frames S.levels).preserves σ (elimSigmaSide_equivalent facts equation.1)
  have second := (frames S.levels).preserves σ (elimSigmaSide_equivalent facts equation.2)
  have eqv := (frames S.levels).equivalence Δ
  exact ⟨fun solved => eqv.trans first (eqv.trans solved (eqv.symm second)),
    fun solved => eqv.trans (eqv.symm first) (eqv.trans solved second)⟩

/-- **The store η-expanded at Σ bases has exactly the solutions of the store.** -/
theorem elimSigma_equivalent {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent problem (elimSigmaStore facts problem) := fun _ σ => by
  simp only [elimSigmaStore, Frames.Models, List.forall_mem_map]
  exact forall₂_congr fun equation _ => (elimSigma_solves facts σ equation).symm

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

/-- **The store η-expanded at Σ bases has the weight of the store.** -/
theorem storeWeight_elimSigma {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete (elimSigmaStore facts problem) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      have tail := storeWeight_elimSigma rest
      simp only [elimSigmaStore, List.map_cons, storeWeight, equationWeight] at tail ⊢
      rw [tail, ← sideWeight_of_equivalent facts roots heads algebra rigid complete
        (elimSigmaSide_equivalent facts equation.1), ← sideWeight_of_equivalent facts roots heads algebra rigid complete
        (elimSigmaSide_equivalent facts equation.2)]

include rigid in
/-- **The store η-expanded at Σ bases stays in the permuted Miller class.** -/
theorem PermutedMiller.elimSigma (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (elimSigmaStore facts problem) :=
  PermutedMiller.map_equivalent permuted (elimSigmaSide facts) (elimSigmaSide_equivalent facts)
    (fun _ _ sides => by
      obtain ⟨left, right⟩ := side_reduct rigid sn sides
      exact sides_of_reducts (computation_empty rigid)
        (MarkedReduct.elimSigmaTo (computation_empty rigid) 0 _ _ _
          (fun _ small => absurd small (Nat.not_lt_zero _)) left)
        (MarkedReduct.elimSigmaTo (computation_empty rigid) 0 _ _ _
          (fun _ small => absurd small (Nat.not_lt_zero _)) right))

end Store

/-! ## The family -/

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

/-- **The η-long prepared store, η-expanded at Σ bases at every elimination spine**, as an update of the store. -/
noncomputable def elimSigmaUpdate (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Update S.levels problem :=
  (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).then
    ((Update.pending S.levels (elimSigmaStore facts
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)).rephrase
      (elimSigma_equivalent facts _))

omit [DecidableRel S.R.cumulative] in
theorem elimSigmaUpdate_rank (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    weightRank facts roots heads algebra rigid complete
        (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  have long := longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem
  change ((longUpdate facts roots heads algebra reducer root rootComplete fuel problem).target.arity,
    storeWeight facts roots heads algebra rigid complete (elimSigmaStore facts
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) = _
  rw [storeWeight_elimSigma]
  exact long

/-- **The round**: the mixed round; when it is stuck, the mixed round on the η-long prepared store η-expanded at Σ
bases at every elimination spine. -/
noncomputable def elimSigmaRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (elimSigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))

/-- **The family**, at the weight rank. -/
noncomputable def elimSigmaFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ### Conservativity and readers -/

theorem elimSigmaRound_eq_of_mixed (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold elimSigmaRound
  cases computed : mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the mixed family decides, this family decides with the same outcome.** -/
theorem elimSigma_run_of_mixed (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((mixedFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((elimSigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((mixedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => elimSigmaRound_eq_of_mixed facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

/-- **The reader**: the round moves wherever the mixed round moves on the η-long prepared store η-expanded at Σ
bases. -/
theorem elimSigmaRound_not_stuck_of_expanded (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel
      (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining ≠ .stuck) :
    elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold elimSigmaRound
  cases mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      exact liftCollapsed_not_stuck facts roots heads algebra rigid complete _
        (elimSigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem) moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The family's readers**: a reader of the mixed family, on the store or on its η-long prepared store η-expanded
at Σ bases. -/
def ElimSigmaReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  MixedReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    MixedReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel
      (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining

theorem elimSigmaRound_not_stuck_of_reads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : ElimSigmaReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with mixed | expanded
  · have moving := mixedRound_not_stuck_of_mixedReads facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel mixed
    rw [elimSigmaRound_eq_of_mixed facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel moving]
    exact moving
  · exact elimSigmaRound_not_stuck_of_expanded facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel
      (mixedRound_not_stuck_of_mixedReads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel expanded)

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem elimSigmaUpdate_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem :=
  EventuallyConst.comp (fun long : Update S.levels problem => long.then
      ((Update.pending S.levels (elimSigmaStore facts long.remaining)).rephrase (elimSigma_equivalent facts _)))
    (longUpdate_const facts roots heads algebra reducer root rootComplete stable problem)

theorem elimSigmaRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) =
      (roundView (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (liftView (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
          (roundView (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel
            (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))) := by
  unfold elimSigmaRound
  rw [roundView_orElse, liftCollapsed_view]

include stable in
/-- **The round is eventually constant on every store.** -/
theorem elimSigmaRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => elimSigmaRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (mixedRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
      (EventuallyConst.dep (h := fun fuel => elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel
          problem)
        (k := fun fuel prepared => liftView prepared
          (roundView (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel prepared.remaining)))
        (elimSigmaUpdate_const facts roots heads algebra reducer root rootComplete stable problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (mixedRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening stable prepared.remaining))))

include stable in
/-- **The family settles** on every class on which, from some budget on, its round is not stuck and keeps the
class. -/
noncomputable def elimSigmaSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (elimSigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => elimSigmaRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

/-! ### Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

omit [DecidableRel S.R.cumulative] in
include rigid sn in
/-- **The η-long prepared store η-expanded at Σ bases stays in the permuted Miller class.** -/
theorem elimSigmaUpdate_keeps (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels
      (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining :=
  PermutedMiller.elimSigma facts rigid sn (longUpdate_keeps facts roots heads algebra rigid reducer root rootComplete
    sn fuel permuted)

include sn directed in
/-- **Closure of the round** at every budget. -/
theorem elimSigmaRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (elimSigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) =
      .progress update smaller at fired
  cases computed : mixedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
        (elimSigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (elimSigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
        (fun first firstSmaller inner => mixedRound_closure facts roots heads algebra rigid complete declared choices
          reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ first
          firstSmaller (elimSigmaUpdate_keeps facts roots heads algebra rigid reducer root rootComplete sn fuel
            permuted) inner) fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact mixedRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Conditional decision for the family, from firing**, on every store of the dynamic pattern fragment, with a
principal answer or a certified refutation, constant at every larger budget. At the tower's setting the conclusion
fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails.
For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem elimSigma_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        elimSigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((elimSigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((elimSigmaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((elimSigmaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((elimSigmaFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (elimSigmaSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        elimSigmaRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The family of the tower controls. -/
noncomputable def elimSigmaTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  elimSigmaFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- **Every run that the tower's mixed family decides, this family decides with the same outcome.** -/
theorem tower_elimSigma_run_of_mixed (fuel rounds : Nat) {Θ : Context setting.R}
    (problem : EquationStore (TotalTerm Θ)) (decided : (run (mixedTower.solver fuel) problem rounds).Decided) :
    run (elimSigmaTower.solver fuel) problem rounds = run (mixedTower.solver fuel) problem rounds :=
  elimSigma_run_of_mixed (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel rounds problem
    decided

/-- **Conditional decision for the tower's family, from firing**, on every store of the dynamic pattern fragment. At
the tower firing fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_elimSigma_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → elimSigmaTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (elimSigmaTower.solver larger) problem larger = run (elimSigmaTower.solver budget) problem budget ∧
      ((∃ state finished, run (elimSigmaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (elimSigmaTower.solver larger) problem larger = .refuted absent)) :=
  elimSigma_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
