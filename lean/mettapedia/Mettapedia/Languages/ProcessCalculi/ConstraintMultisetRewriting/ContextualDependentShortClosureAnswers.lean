import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentHereditary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStratifiedClosureAnswers

/-!
# The stratified Miller class under an answer for the newest metavariable

A pattern answer for the newest metavariable `F` of `Γ, F` instantiates the rest of the store along `F := v` and drops
the solved equation. When `v` is normal with Miller occurrences, the instantiated store is again in the stratified
Miller class (`stratifiedMiller_instantiate_newest`):

* **Miller sides**: each opened side, instantiated and normalized, keeps Miller occurrences, by hereditary
  substitution (`ContextualDependentHereditary.stableMiller`). No arity is read, so neither the number of
  abstractions of `v` nor the number of arguments of `F`'s occurrences matters.
* **Opening depth**: instantiating a bare `F` on a left side by an abstraction opens that equation deeper. The
  instantiated side is still Miller at every larger depth: each further local is one more distinct rigid argument
  (`miller_deeper`), and substitution never removes a leading abstraction (`lamDepth_le_subst`). So no condition on
  depths is needed, unlike R107's exact-arity version (`ContextualDependentStratifiedClosure.stratified_instantiate_newest`).
* **Stratified annotations**: as in R107, a solution of the instantiated equations before an equation is, composed
  with the answer, a solution of the original equations before it, the solved one included.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentShortClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure ContextualDependentHereditary
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Answers for the newest metavariable, under binders -/

section Raw

variable {Head : Type} {R : Rules Head}

/-- A pattern answer lifted under `count` binders. -/
def liftAnswer {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m} :
    (count : Nat) → PatternAnswer R flexible flexible' σ →
      PatternAnswer R (liftFlexibleK count flexible) (liftFlexibleK count flexible') (liftSubK count σ)
  | 0, answer => answer
  | count + 1, answer => (liftAnswer count answer).lift

/-- **The newest metavariable, answered by a normal Miller term**, as a pattern answer of the closed context: every
variable is flexible. -/
def newestAnswer {Γ : Context R} {type : TypeOver Γ} (value : Term Γ type) (normal : Normal R value.code)
    (millerValue : miller (fun _ => true) value.code = true) :
    PatternAnswer R (bodyFlexible (o := Γ.arity + 1) 0) (bodyFlexible (o := Γ.arity) 0)
      (ContextualDependentEta.Elimination.instantiate Γ value).substitution where
  target := 0
  flexibleTarget := rfl
  rename i hi := i.pred hi
  injective := fun _ _ _ _ same => Fin.pred_inj.mp same
  respects := fun _ _ => rfl
  others := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨prior, rfl⟩
    · exact absurd rfl hi
    · rw [Fin.pred_succ]
      rfl
  outerArity := Γ.arity
  outer := idRen
  outerInjective := fun _ _ same => same
  outerFlexible := fun _ => rfl
  value := value.code
  solution := by
    change (consSub (value.cast type.reindex_id.symm).code ids) 0 = _
    simp only [consSub, Fin.cases_zero, Term.cast_code]
    exact (rename_id value.code).symm
  valueMiller := millerValue
  valueNormal := normal

/-- Substitution never removes a leading abstraction. -/
theorem lamDepth_le_subst : ∀ {n m : Nat} (σ : Sub Head n m) (t : Tm Head n),
    ContextualDependentPatternSolver.lamDepth t ≤ ContextualDependentPatternSolver.lamDepth (subst σ t)
  | _, _, σ, .lam body => by
      simp only [ContextualDependentPatternSolver.lamDepth, subst]
      exact Nat.succ_le_succ (lamDepth_le_subst (liftSub σ) body)
  | _, _, _, .var _ | _, _, _, .const _ | _, _, _, .head _ | _, _, _, .pi _ _ | _, _, _, .sigma _ _
  | _, _, _, .id _ _ _ | _, _, _, .app _ _ | _, _, _, .pair _ _ | _, _, _, .fst _ | _, _, _, .snd _
  | _, _, _, .refl _ => Nat.zero_le _

variable (empty : R.computation = RootComputation.empty)
include empty

/-- Every normal form has Miller occurrences when one does. -/
theorem all_miller_of_one {n : Nat} {flexible : Fin n → Bool} {x : Tm Head n}
    (found : ∃ N, Star (R := R) x N ∧ Normal R N ∧ miller flexible N = true) :
    ∀ code, Star (R := R) x code → Normal R code → miller flexible code = true := by
  obtain ⟨N, toN, normalN, millerN⟩ := found
  intro code toCode normalCode
  rw [normal_reduct_unique empty toN normalN toCode normalCode]
  exact millerN

/-- **An opened side with Miller occurrences keeps them under a pattern answer between closed contexts** (every
variable a metavariable), after normalization. -/
theorem answer_side_miller {n m : Nat} {σ : Sub Head n m}
    (answer : PatternAnswer R (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) σ) (count : Nat)
    {side : Tm Head (n + count)} (millerSide : miller (openedFlexible count) side = true) (normalSide : Normal R side) :
    ∃ side', Star (R := R) (subst (liftSubK count σ) side) side' ∧ Normal R side' ∧
      miller (openedFlexible count) side' = true := by
  have markSource : liftFlexibleK count (bodyFlexible (o := n) 0) = openedFlexible count :=
    funext fun index => (liftFlexibleK_body count index).trans (bodyFlexible_eq count index)
  have markTarget : liftFlexibleK count (bodyFlexible (o := m) 0) = openedFlexible count :=
    funext fun index => (liftFlexibleK_body count index).trans (bodyFlexible_eq count index)
  obtain ⟨side', steps, normal', miller', -⟩ := stableMiller empty side (liftAnswer count answer)
    (by rw [markSource]; exact millerSide) normalSide
  exact ⟨side', steps, normal', by rw [← markTarget]; exact miller'⟩

/-- **An answered equation side, opened, has a Miller normal form** when the original opened side has a normal form
and all its normal forms are Miller. -/
theorem answered_side_miller {n m : Nat} {σ : Sub Head n m}
    (answer : PatternAnswer R (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) σ) (count : Nat)
    {code : Tm Head n}
    (inside : ∀ opened, Star (R := R) (openCode count code) opened → Normal R opened →
      miller (openedFlexible count) opened = true)
    (normalizes : ∃ opened, Star (R := R) (openCode count code) opened ∧ Normal R opened) :
    ∃ opened, Star (R := R) (openCode count (subst σ code)) opened ∧ Normal R opened ∧
      miller (openedFlexible count) opened = true := by
  obtain ⟨N, toN, normalN⟩ := normalizes
  obtain ⟨N', toN', normalN', millerN'⟩ := answer_side_miller empty answer count (inside N toN normalN) normalN
  refine ⟨N', ?_, normalN', millerN'⟩
  rw [openCode_subst]
  exact (star_subst _ toN).trans toN'

/-- **An opened side with Miller occurrences keeps them** when the newest metavariable is answered and the result
normalized. -/
theorem instantiate_side_miller {Γ : Context R} {type : TypeOver Γ} (value : Term Γ type) (normal : Normal R value.code)
    (millerValue : miller (fun _ => true) value.code = true) (count : Nat) {side : Tm Head (Γ.arity + 1 + count)}
    (millerSide : miller (openedFlexible count) side = true) (normalSide : Normal R side) :
    ∃ side', Star (R := R)
        (subst (liftSubK count (ContextualDependentEta.Elimination.instantiate Γ value).substitution) side) side' ∧
      Normal R side' ∧ miller (openedFlexible count) side' = true := by
  have markSource : liftFlexibleK count (bodyFlexible (o := Γ.arity + 1) 0) = openedFlexible count :=
    funext fun index => (liftFlexibleK_body count index).trans (bodyFlexible_eq count index)
  have markTarget : liftFlexibleK count (bodyFlexible (o := Γ.arity) 0) = openedFlexible count :=
    funext fun index => (liftFlexibleK_body count index).trans (bodyFlexible_eq count index)
  obtain ⟨side', steps, normal', miller', -⟩ := stableMiller empty side
    (liftAnswer count (newestAnswer value normal millerValue)) (by rw [markSource]; exact millerSide) normalSide
  exact ⟨side', steps, normal', by rw [← markTarget]; exact miller'⟩

/-- **An instantiated equation side, opened, has a Miller normal form** when the original opened side has a normal
form and all its normal forms are Miller. -/
theorem instantiated_side_miller {Γ : Context R} {type : TypeOver Γ} (value : Term Γ type)
    (normal : Normal R value.code) (millerValue : miller (fun _ => true) value.code = true) (count : Nat)
    {code : Tm Head (Γ.arity + 1)}
    (inside : ∀ opened, Star (R := R) (openCode count code) opened → Normal R opened →
      miller (openedFlexible count) opened = true)
    (normalizes : ∃ opened, Star (R := R) (openCode count code) opened ∧ Normal R opened) :
    ∃ opened, Star (R := R)
        (openCode count (subst (ContextualDependentEta.Elimination.instantiate Γ value).substitution code)) opened ∧
      Normal R opened ∧ miller (openedFlexible count) opened = true := by
  obtain ⟨N, toN, normalN⟩ := normalizes
  obtain ⟨N', toN', normalN', millerN'⟩ :=
    instantiate_side_miller empty value normal millerValue count (inside N toN normalN) normalN
  refine ⟨N', ?_, normalN', millerN'⟩
  rw [openCode_subst]
  exact (star_subst _ toN).trans toN'

/-- **Opening deeper keeps Miller normal forms**: each further local is one more distinct rigid argument. -/
theorem miller_deeper {n : Nat} {code : Tm Head n} :
    ∀ (k : Nat) {d : Nat},
      (∃ opened, Star (R := R) (openCode d code) opened ∧ Normal R opened ∧ miller (openedFlexible d) opened = true) →
      ∃ opened, Star (R := R) (openCode (d + k) code) opened ∧ Normal R opened ∧
        miller (openedFlexible (d + k)) opened = true
  | 0, _, found => found
  | k + 1, d, found => by
      obtain ⟨N, toN, normalN, millerN⟩ := miller_deeper k found
      have respects : ∀ i : Fin (n + (d + k)),
          openedFlexible (d + k + 1) ((wk : Ren (n + (d + k)) (n + (d + k) + 1)) i) = openedFlexible (d + k) i := by
        intro i
        simp only [openedFlexible, wk, Fin.val_succ, Nat.add_le_add_iff_right]
      obtain ⟨t', steps, normal', miller'⟩ := collapse_miller empty [0] N (openedFlexible (d + k)) wk normalN millerN
        (Fin.succ_injective _) respects
        (fun y member => by
          rw [List.mem_singleton.mp member]
          simp [openedFlexible])
        (List.nodup_singleton _)
        (fun y member i same => by
          rw [List.mem_singleton.mp member] at same
          exact Fin.succ_ne_zero _ same)
      refine ⟨t', ?_, normal', miller'⟩
      change Star (R := R) (.app (Presentation.rename wk (openCode (d + k) code)) (.var 0)) t'
      exact (star_app (star_rename wk toN) .refl).trans steps

end Raw

/-! ## The store under the answer -/

section Store

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- Every equation of a store in the Miller class has Miller sides. -/
theorem StratifiedMiller.sides_of_mem {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (stratified : StratifiedMiller levels problem) {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) :
    FragmentSidesMiller equation := by
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  exact (stratified before after equation split).1

/-- **The stratified Miller class is closed under an answer for the newest metavariable**, removing the solved
equation, when the answer is a normal term with Miller occurrences and every opened side has a normal form. No
condition on arities or on opening depths is needed. -/
theorem stratifiedMiller_instantiate_newest (empty : rules.computation = RootComputation.empty) {Γ : Context rules}
    {type : TypeOver Γ} (value : Term Γ type) (normal : Normal rules value.code)
    (millerValue : miller (fun _ => true) value.code = true)
    {before after : EquationStore (TotalTerm (extend Γ type))} {solved : Equation (TotalTerm (extend Γ type))}
    (stratified : StratifiedMiller levels (before ++ solved :: after))
    (solves : ∀ {Δ : Context rules} (τ : Δ ⟶ Γ),
      (frames levels).Solves (τ ≫ Elimination.instantiate Γ value) solved)
    (normalizes : ∀ equation ∈ before ++ after,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened)) :
    StratifiedMiller levels ((frames levels).applyStore (Elimination.instantiate Γ value) (before ++ after)) := by
  intro before' after' later split
  change (before ++ after).map (fun equation => (equation.1.reindex (Elimination.instantiate Γ value),
    equation.2.reindex (Elimination.instantiate Γ value))) = before' ++ later :: after' at split
  obtain ⟨prefix', rest, hsplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
  obtain ⟨equation, suffix, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
  have member : equation ∈ before ++ after := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have inOriginal : equation ∈ before ++ solved :: after := by
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact List.mem_append_left _ inBefore
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
  have sides := StratifiedMiller.sides_of_mem stratified inOriginal
  refine ⟨?_, ?_⟩
  · -- Miller sides of the instantiated equation, at its own opening depth
    unfold FragmentSidesMiller
    change (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code))
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code)) code → Normal rules code →
        miller (openedFlexible (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code))) code = true) ∧
      (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code))
          (subst (Elimination.instantiate Γ value).substitution equation.2.2.code)) code → Normal rules code →
        miller (openedFlexible (ContextualDependentPatternSolver.lamDepth
          (subst (Elimination.instantiate Γ value).substitution equation.1.2.code))) code = true)
    obtain ⟨k, deeper⟩ := Nat.exists_eq_add_of_le
      (lamDepth_le_subst (Elimination.instantiate Γ value).substitution equation.1.2.code)
    rw [deeper]
    exact ⟨all_miller_of_one empty (miller_deeper empty k
        (instantiated_side_miller empty value normal millerValue _ sides.1 (normalizes equation member).1)),
      all_miller_of_one empty (miller_deeper empty k
        (instantiated_side_miller empty value normal millerValue _ sides.2 (normalizes equation member).2))⟩
  · -- stratified annotations
    intro Δ τ solvedPrefix
    have pulled : (frames levels).Models (τ ≫ Elimination.instantiate Γ value) prefix' :=
      (Frames.models_applyStore (X := frames levels) (Elimination.instantiate Γ value) τ prefix').mp solvedPrefix
    have annotations : TypeEq rules Δ.raw
        (subst (τ ≫ Elimination.instantiate Γ value).substitution equation.1.1.code)
        (subst (τ ≫ Elimination.instantiate Γ value).substitution equation.2.1.code) := by
      rcases List.append_eq_append_iff.mp hsplit with ⟨middle, prefixEq, afterEq⟩ | ⟨middle, beforeEq, restEq⟩
      · -- the equation was after the solved one
        have atOriginal : StratifiedAt levels (before ++ solved :: middle) equation :=
          (stratified (before ++ solved :: middle) suffix equation (by
          rw [afterEq]; simp)).2
        refine atOriginal _ ?_
        rw [prefixEq, ContextualDependentClosure.models_append_iff] at pulled
        rw [ContextualDependentClosure.models_append_iff]
        refine ⟨pulled.1, ?_⟩
        intro other inOther
        rcases List.mem_cons.mp inOther with same | inMiddle
        · rw [same]
          exact solves τ
        · exact pulled.2 other inMiddle
      · rcases middle with _ | ⟨first, middle⟩
        · -- the equation is the first one of `after`
          rw [List.nil_append] at restEq
          rw [List.append_nil] at beforeEq
          have atOriginal : StratifiedAt levels (prefix' ++ [solved]) equation :=
            (stratified (prefix' ++ [solved]) suffix equation (by
            rw [beforeEq, ← restEq]; simp)).2
          refine atOriginal _ ?_
          rw [ContextualDependentClosure.models_append_iff]
          refine ⟨pulled, ?_⟩
          intro other inOther
          rw [List.mem_singleton.mp inOther]
          exact solves τ
        · -- the equation was before the solved one
          rw [List.cons_append, List.cons.injEq] at restEq
          obtain ⟨headEq, _⟩ := restEq
          have atOriginal : StratifiedAt levels prefix' equation :=
            (stratified prefix' (middle ++ solved :: after) equation (by
            rw [beforeEq, headEq]; simp)).2
          exact atOriginal _ pulled
    have leftSame : subst τ.substitution (equation.1.reindex (Elimination.instantiate Γ value)).1.code =
        subst (τ ≫ Elimination.instantiate Γ value).substitution equation.1.1.code :=
      (congrArg TypeOver.code (TypeOver.reindex_comp equation.1.1 τ (Elimination.instantiate Γ value))).symm
    have rightSame : subst τ.substitution (equation.2.reindex (Elimination.instantiate Γ value)).1.code =
        subst (τ ≫ Elimination.instantiate Γ value).substitution equation.2.1.code :=
      (congrArg TypeOver.code (TypeOver.reindex_comp equation.2.1 τ (Elimination.instantiate Γ value))).symm
    change TypeEq rules Δ.raw (subst τ.substitution (equation.1.reindex (Elimination.instantiate Γ value)).1.code)
      (subst τ.substitution (equation.2.reindex (Elimination.instantiate Γ value)).1.code)
    rw [leftSame, rightSame]
    exact annotations

/-- **The stratified Miller class is closed under every pattern answer between contexts**: a context morphism whose
substitution solves one metavariable by a normal Miller term over the target's metavariables and renames the others
injectively. This covers the pruning answer `G := λ z̄. H (z̄ restricted)` of intersection and pruning, and the
in-place instantiations. Every equation is kept, instantiated; no condition on arities or depths. -/
theorem stratifiedMiller_applyStore (empty : rules.computation = RootComputation.empty) {Θ Δ : Context rules}
    (σ : Δ ⟶ Θ) (answer : PatternAnswer rules (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := Δ.arity) 0)
      σ.substitution)
    {problem : EquationStore (TotalTerm Θ)} (stratified : StratifiedMiller levels problem)
    (normalizes : ∀ equation ∈ problem,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened)) :
    StratifiedMiller levels ((frames levels).applyStore σ problem) := by
  intro before' after' later split
  change problem.map (fun equation => (equation.1.reindex σ, equation.2.reindex σ)) =
    before' ++ later :: after' at split
  obtain ⟨prefix', rest, hsplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
  obtain ⟨equation, suffix, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
  have member : equation ∈ problem := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have sides := StratifiedMiller.sides_of_mem stratified member
  refine ⟨?_, ?_⟩
  · unfold FragmentSidesMiller
    change (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth
          (subst σ.substitution equation.1.2.code)) (subst σ.substitution equation.1.2.code)) code →
        Normal rules code → miller (openedFlexible (ContextualDependentPatternSolver.lamDepth
          (subst σ.substitution equation.1.2.code))) code = true) ∧
      (∀ code, Star (R := rules) (openCode (ContextualDependentPatternSolver.lamDepth
          (subst σ.substitution equation.1.2.code)) (subst σ.substitution equation.2.2.code)) code →
        Normal rules code → miller (openedFlexible (ContextualDependentPatternSolver.lamDepth
          (subst σ.substitution equation.1.2.code))) code = true)
    obtain ⟨k, deeper⟩ := Nat.exists_eq_add_of_le (lamDepth_le_subst σ.substitution equation.1.2.code)
    rw [deeper]
    exact ⟨all_miller_of_one empty (miller_deeper empty k
        (answered_side_miller empty answer _ sides.1 (normalizes equation member).1)),
      all_miller_of_one empty (miller_deeper empty k
        (answered_side_miller empty answer _ sides.2 (normalizes equation member).2))⟩
  · intro Δ' τ solvedPrefix
    have pulled : (frames levels).Models (τ ≫ σ) prefix' :=
      (Frames.models_applyStore (X := frames levels) σ τ prefix').mp solvedPrefix
    have annotations := (stratified prefix' suffix equation hsplit).2 _ pulled
    have leftSame : subst τ.substitution (equation.1.reindex σ).1.code =
        subst (τ ≫ σ).substitution equation.1.1.code :=
      (congrArg TypeOver.code (TypeOver.reindex_comp equation.1.1 τ σ)).symm
    have rightSame : subst τ.substitution (equation.2.reindex σ).1.code =
        subst (τ ≫ σ).substitution equation.2.1.code :=
      (congrArg TypeOver.code (TypeOver.reindex_comp equation.2.1 τ σ)).symm
    change TypeEq rules Δ'.raw (subst τ.substitution (equation.1.reindex σ).1.code)
      (subst τ.substitution (equation.2.reindex σ).1.code)
    rw [leftSame, rightSame]
    exact annotations

/-- **Dropping an equation that every substitution solves keeps the stratified Miller class.** -/
theorem stratifiedMiller_drop {Θ : Context rules} {before after : EquationStore (TotalTerm Θ)}
    {dropped : Equation (TotalTerm Θ)} (stratified : StratifiedMiller levels (before ++ dropped :: after))
    (valid : ∀ {Δ : Context rules} (τ : Δ ⟶ Θ), (frames levels).Solves τ dropped) :
    StratifiedMiller levels (before ++ after) := by
  intro before' after' equation split
  have member : equation ∈ before ++ dropped :: after := by
    have inShort : equation ∈ before ++ after := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    rcases List.mem_append.mp inShort with inBefore | inAfter
    · exact List.mem_append_left _ inBefore
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
  refine ⟨StratifiedMiller.sides_of_mem stratified member, ?_⟩
  rcases List.append_eq_append_iff.mp split with ⟨middle, prefixEq, afterEq⟩ | ⟨middle, beforeEq, restEq⟩
  · -- the equation is after the dropped one
    have atOriginal : StratifiedAt levels (before ++ dropped :: middle) equation :=
      (stratified (before ++ dropped :: middle) after' equation (by rw [afterEq]; simp)).2
    intro Δ τ solvedPrefix
    refine atOriginal _ ?_
    rw [prefixEq, ContextualDependentClosure.models_append_iff] at solvedPrefix
    rw [ContextualDependentClosure.models_append_iff]
    refine ⟨solvedPrefix.1, ?_⟩
    intro other inOther
    rcases List.mem_cons.mp inOther with same | inMiddle
    · rw [same]
      exact valid τ
    · exact solvedPrefix.2 other inMiddle
  · rcases middle with _ | ⟨first, middle⟩
    · -- the equation is the first one after the dropped one
      rw [List.nil_append] at restEq
      rw [List.append_nil] at beforeEq
      have atOriginal : StratifiedAt levels (before' ++ [dropped]) equation :=
        (stratified (before' ++ [dropped]) after' equation (by rw [beforeEq, ← restEq]; simp)).2
      intro Δ τ solvedPrefix
      refine atOriginal _ ?_
      rw [ContextualDependentClosure.models_append_iff]
      refine ⟨solvedPrefix, ?_⟩
      intro other inOther
      rw [List.mem_singleton.mp inOther]
      exact valid τ
    · -- the equation is before the dropped one
      rw [List.cons_append, List.cons.injEq] at restEq
      obtain ⟨headEq, _⟩ := restEq
      exact (stratified before' (middle ++ dropped :: after) equation (by rw [beforeEq, headEq]; simp)).2

/-- **Answer, then drop the instantiated first equation**: the shape of the intersection progress. If the store is
in the Miller class and the answer makes its first equation valid, the instantiated rest is in the Miller class. -/
theorem stratifiedMiller_answer_drop (empty : rules.computation = RootComputation.empty) {Θ Δ : Context rules}
    (σ : Δ ⟶ Θ) (answer : PatternAnswer rules (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := Δ.arity) 0)
      σ.substitution)
    {first : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (stratified : StratifiedMiller levels (first :: rest))
    (normalizes : ∀ equation ∈ first :: rest,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened))
    (valid : ∀ {Δ' : Context rules} (τ : Δ' ⟶ Δ), (frames levels).Solves τ (first.1.reindex σ, first.2.reindex σ)) :
    StratifiedMiller levels ((frames levels).applyStore σ rest) :=
  stratifiedMiller_drop (before := []) (stratifiedMiller_applyStore empty σ answer stratified normalizes) valid

/-- **R110's certified drop keeps the Miller class** (`ContextualDependentIntersection.dropValid`, whose residual store
is `rest`): the dropped equation holds at the identity, hence at every substitution. -/
theorem stratifiedMiller_dropValid {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (stratified : StratifiedMiller levels (equation :: rest))
    (valid : (frames levels).E equation.1 equation.2) : StratifiedMiller levels rest :=
  stratifiedMiller_drop (before := []) stratified fun τ => (frames levels).preserves τ valid

end Store

/-! ## Renamings and the exchange of independent metavariables -/

section Renaming

variable {Head : Type} {R : Rules Head}

/-- **A renaming of metavariables is a pattern answer** (for any of its variables, answered by its image). -/
def PatternAnswer.ofRenaming (empty : R.computation = RootComputation.empty) {n m : Nat} {σ : Sub Head n m}
    (ρ : Ren n m) (injective : Function.Injective ρ) (renames : ∀ i, σ i = .var (ρ i)) (target : Fin n) :
    PatternAnswer R (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) σ where
  target := target
  flexibleTarget := rfl
  rename i _ := ρ i
  injective := fun _ _ _ _ same => injective same
  respects := fun _ _ => rfl
  others := fun i _ => renames i
  outerArity := 1
  outer := fun _ => ρ target
  outerInjective := fun first second _ => Subsingleton.elim first second
  outerFlexible := fun _ => rfl
  value := .var 0
  solution := renames target
  valueMiller := rfl
  valueNormal := normal_var empty 0

/-- The transposition of the two newest variables. -/
def swapRen {n : Nat} : Ren (n + 1 + 1) (n + 1 + 1) :=
  Fin.cases (0 : Fin (n + 1)).succ (Fin.cases 0 fun j => j.succ.succ)

theorem swapRen_involutive {n : Nat} : Function.Involutive (swapRen (n := n)) := by
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> rfl

theorem swapRen_injective {n : Nat} : Function.Injective (swapRen (n := n)) :=
  swapRen_involutive.injective

end Renaming

section Exchange

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **The exchange of two independent metavariables keeps the Miller class** (R110's reorder step): its answer is
the transposition of the two newest variables. -/
theorem stratifiedMiller_exchange (empty : rules.computation = RootComputation.empty) {Γ : Context rules}
    (first next : TypeOver Γ)
    {problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))}
    (stratified : StratifiedMiller levels problem)
    (normalizes : ∀ equation ∈ problem,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened)) :
    StratifiedMiller levels (ContextualDependentPrune.exchange levels first next problem).remaining := by
  have renames : ∀ i, (ContextualDependentParameterExchange.swap next first).substitution i = .var (swapRen i) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact ContextualDependentParameterExchange.swap_zero next first
    · exact ContextualDependentParameterExchange.swap_one next first
    · exact ContextualDependentParameterExchange.swap_older next first i
  exact stratifiedMiller_applyStore empty (ContextualDependentParameterExchange.swap next first)
    (PatternAnswer.ofRenaming empty swapRen swapRen_injective renames 0) stratified normalizes

end Exchange

end ContextualDependentShortClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
