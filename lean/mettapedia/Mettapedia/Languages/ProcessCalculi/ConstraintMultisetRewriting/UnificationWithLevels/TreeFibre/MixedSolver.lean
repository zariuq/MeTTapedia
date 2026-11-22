import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedStores

/-!
# One solver of the tree's driver, with one rank, for stores mixing Miller patterns and arrow codes

**The solver** (`mixedSolver`). Its rank is the common rank (`commonRank`: the weight of the occurring unknowns, then
the size). Its round at a store:
* when every equation lies in the fragment of arrow codes (`inArrowsCodB`), the round of the solver of arrow codes;
* otherwise, the Miller equations first (`millerFirst`, a permutation: an equivalent store with the same rank,
  `transport`), and the Miller round there.

Both rounds lower the common rank (`millerGlbRound_commonRank`, `arrowCodRound_commonRank`), so the piece is read
again at every round and no rank indexed by the piece is needed.

**The fragment** (`InMixed`): the fragment of arrow codes, or a mixed store (a telescope of universe families, every
equation a Miller equation or an equation between arrow codes). It contains the Miller fragment, the fragment of
arrow codes with codomains and the flex–rigid fragment with codomains. The rounds keep it (`mixedRound_stable`: the
arrow round keeps its fragment; a Miller round keeps a mixed store mixed); on it a nonempty store is never stuck
(`mixedRound_ne_stuck`: a store outside the fragment of arrow codes has a Miller equation, which comes first).
**Decided** (`mixed_decided`): from some budget on, a principal answer or a certified refutation.

**Why the Miller equations first.** The Miller rounds keep equations between arrow codes (an unknown at a universe is
answered by an unknown at a universe). The arrow rounds do not keep Miller equations: solving `X := t` with `t` rigid
turns a Miller side `λ ȳ. X` into `λ ȳ. t`, in no piece. So the arrow round runs only on stores with no Miller
equation left.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section Solver

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Miller.Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The Miller equations first**: the equations the Miller reading accepts, then the others, each in its order. -/
def millerFirst {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : EquationStore (TotalTerm Θ) :=
  problem.filter (fun e => (Miller.readEq (S := S) e).isSome) ++
    problem.filter (fun e => !(Miller.readEq (S := S) e).isSome)

omit [DecidableRel S.R.headEq] in
theorem millerFirst_perm {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (millerFirst problem).Perm problem :=
  List.filter_append_perm _ _

/-- **The round of the mixed solver.** -/
def mixedRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Round S.levels commonRank problem :=
  if hA : inArrowsCodB choices problem = true then
    retarget (arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
        strengthening problem)
      (fun _ _ progressed => arrowCodRound_commonRank choices glb spec facts roots heads algebra rigid complete
        headTypingUnique declared strengthening (inArrowsCod_of_B choices hA) progressed)
  else
    transport (equivalent_perm (millerFirst_perm problem).symm) (commonRank_perm (millerFirst_perm problem))
      (retarget (Miller.millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
          (millerFirst problem))
        (fun _ _ progressed => Miller.millerGlbRound_commonRank facts roots heads algebra rigid complete normalizes inh
          headTypingUnique glb spec progressed))

/-- **The mixed solver of the tree's driver**: one rank, the piece read at every round. -/
def mixedSolver : ContextualDependentWorklist.Solver S.levels where
  rank := commonRank
  round := mixedRound choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
    strengthening glb spec

/-- **The fragment of the mixed solver**: the fragment of arrow codes, or a mixed store. -/
def InMixed {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  InArrowsCod choices problem ∨ Miller.MixedStore choices problem

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
/-- The Miller fragment lies inside. -/
theorem inMixed_of_miller {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : Miller.InMillerGlb (S := S) problem) : InMixed choices problem :=
  .inr (Miller.MixedStore.of_miller inside)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
/-- The fragment of arrow codes with codomains lies inside. -/
theorem inMixed_of_arrows {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod choices problem) : InMixed choices problem :=
  .inl inside

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
/-- The flex–rigid fragment with codomains lies inside. -/
theorem inMixed_of_flexCod {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFlexCod choices problem) : InMixed choices problem :=
  .inl (inArrowsCod_of_flexCod inside)

/-- **Membership in the fragment of the mixed solver, decided.** -/
def inMixedB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  inArrowsCodB choices problem ||
    (decide (Miller.Families Θ) &&
      problem.all fun e => (Miller.readEq (S := S) e).isSome || inArrowsCodB choices [e])

omit [DecidableRel S.R.headEq] in
theorem inMixed_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inMixedB choices problem = true) : InMixed choices problem := by
  simp only [inMixedB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rcases h with arrows | ⟨families, each⟩
  · exact .inl (inArrowsCod_of_B choices arrows)
  · refine .inr ⟨families, fun e member => ?_⟩
    rcases each e member with read | arrow
    · obtain ⟨v, _⟩ := Option.isSome_iff_exists.mp read
      exact .inl ⟨v⟩
    · exact .inr (inArrowsCod_of_B choices arrow)

omit [DecidableRel S.R.cumulative] [DecidableRel S.R.headEq] in
/-- Outside the fragment of arrow codes, a mixed store is a mixed store. -/
theorem mixed_of_not_arrows {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InMixed choices problem) (notArrows : ¬ inArrowsCodB choices problem = true) :
    Miller.MixedStore choices problem := by
  rcases inside with arrows | mixed
  · exact absurd (Miller.inArrowsCodB_of choices arrows) notArrows
  · exact mixed

/-- **The rounds keep the fragment.** -/
theorem mixedRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (commonRank update.remaining) (commonRank problem)}
    (inside : InMixed choices problem)
    (progressed : mixedRound choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening glb spec problem = .progress update smaller) :
    InMixed choices update.remaining := by
  unfold mixedRound at progressed
  split at progressed
  · rename_i hA
    obtain ⟨_, inner⟩ := retarget_progress progressed
    exact .inl (arrowCodRound_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique
      declared strengthening (inArrowsCod_of_B choices hA) inner)
  · rename_i hA
    obtain ⟨inner, _, isInner, rfl⟩ := transport_progress progressed
    obtain ⟨_, isMiller⟩ := retarget_progress isInner
    have mixed := (mixed_of_not_arrows choices inside hA).perm (millerFirst_perm problem).symm
    have kept := Miller.millerGlbRound_mixed choices facts roots heads algebra rigid complete normalizes inh
      headTypingUnique glb spec (problem := millerFirst problem) (update := inner) mixed isMiller
    exact .inr kept

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include total in
/-- **Progress on the fragment**: a nonempty store is never stuck. -/
theorem mixedRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InMixed choices problem) (nonempty : problem ≠ []) :
    mixedRound choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening glb spec problem ≠ .stuck := by
  unfold mixedRound
  split
  · rename_i hA
    exact retarget_ne_stuck (arrowCodRound_ne_stuck choices glb spec facts roots heads algebra rigid complete
      headTypingUnique declared strengthening total (inArrowsCod_of_B choices hA) nonempty)
  · rename_i hA
    apply transport_ne_stuck
    apply retarget_ne_stuck
    have mixed := mixed_of_not_arrows choices inside hA
    obtain ⟨e₀, m₀, notArrow⟩ : ∃ e ∈ problem, ¬ InArrowsCod choices [e] := by
      by_contra none
      apply hA
      apply Miller.inArrowsCodB_of choices
      apply Miller.inArrowsCod_iff.mpr
      intro e m
      by_contra h
      exact none ⟨e, m, h⟩
    have view₀ : Nonempty (Miller.EqView (S := S) e₀) := (mixed.each e₀ m₀).resolve_right notArrow
    obtain ⟨w₀⟩ := view₀
    have inFilter : e₀ ∈ problem.filter (fun e => (Miller.readEq (S := S) e).isSome) :=
      List.mem_filter.mpr ⟨m₀, Miller.readEq_isSome_of_view w₀⟩
    unfold millerFirst
    cases hf : problem.filter (fun e => (Miller.readEq (S := S) e).isSome) with
    | nil =>
        rw [hf] at inFilter
        cases inFilter
    | cons e₁ rest₁ =>
        have read₁ : (Miller.readEq (S := S) e₁).isSome = true := by
          have m₁ : e₁ ∈ problem.filter (fun e => (Miller.readEq (S := S) e).isSome) := by
            rw [hf]
            exact List.mem_cons_self
          exact (List.mem_filter.mp m₁).2
        obtain ⟨v₁, _⟩ := Option.isSome_iff_exists.mp read₁
        exact Miller.millerGlbRound_ne_stuck_head facts roots heads algebra rigid complete normalizes inh
          headTypingUnique glb spec total mixed.families ⟨v₁⟩

include total in
/-- **The fragment of the mixed solver.** -/
def mixedFragment :
    ContextualDependentWorklist.Fragment
      (mixedSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
        strengthening glb spec) where
  holds := InMixed choices
  stable := fun inside progressed =>
    mixedRound_stable choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening glb spec inside progressed
  decisive := fun inside nonempty =>
    mixedRound_ne_stuck choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening glb spec total inside nonempty

include total in
/-- **Stores mixing Miller patterns and arrow codes are decided by one solver with one rank**: on the fragment, the
tree's driver reaches, at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem mixed_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMixed choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (mixedSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
          strengthening glb spec) original larger =
        run (mixedSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
          strengthening glb spec) original fuel ∧
        ((∃ state finished,
              run (mixedSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique
                  declared strengthening glb spec) original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (mixedSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique
              declared strengthening glb spec) original larger = .refuted absent)) :=
  (mixedFragment choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
    strengthening glb spec total).decided inside

include facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening spec total in
/-- **Every mixed store has a principal answer or no solution.** -/
theorem mixed_principal_or_unsolvable {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMixed choices original) :
    (∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer) ∨
      ¬ (frames S.levels).Solvable original := by
  obtain ⟨fuel, decided⟩ := mixed_decided choices facts roots heads algebra rigid complete normalizes inh
    headTypingUnique declared strengthening glb spec total inside
  rcases (decided fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, _⟩
  · exact .inl ⟨_, _, principal⟩
  · exact .inr absent

end Solver

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
