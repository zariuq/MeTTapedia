import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRankGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedJoin

/-!
# One solver of the tree's driver, with one rank, for every decided piece

**The solver** (`oneSolver`). Its rank is the common rank (`commonRank`). Its round reads the piece at every store:
* the fragment of arrow codes: the arrow round;
* otherwise the glb-join fragment: the glb-join round;
* otherwise the fragment of glb groups: the round of glb groups;
* otherwise the Miller equations first and the Miller round (a mixed store).

Every one of these rounds lowers the common rank (`arrowCodRound_commonRank`, `glbJoinRoundK_commonRank`,
`glbGroupRound_commonRank`, `millerGlbRound_commonRank`), so a store may move between pieces from round to round.

**The fragment** (`InOne`): the fragment of arrow codes, the glb-join fragment, the fragment of glb groups, or a mixed
store. It contains every piece of the earlier union (`inOne_of_piece`): Miller patterns, arrow codes with codomains,
flex–rigid equations with codomains, the glb join and the glb groups. Kept by the rounds, never stuck, **decided**
(`one_decided`).

The rank obstruction recorded with the earlier union does not hold: the ranks of the pieces were pairs that did not
dominate each other, but one occurrence count, lexicographic with the size, is lowered by every rule.
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

section One

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
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The fragment of the one solver**: arrow codes, the glb join, glb groups, a store mixing Miller patterns with
arrow codes, or a store mixing glb-join families with arrow codes. -/
def InOne {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  InArrowsCod choices problem ∨ InGlbJoinFragmentK problem ∨ InGlbFragment problem ∨
    Miller.MixedStore choices problem ∨ MixedJoinStore choices problem

/-- The glb-join round on the store with its families with parameters first, carried back. -/
def joinFirstRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Round S.levels commonRank problem :=
  transport (equivalent_perm (joinFirst_perm problem).symm) (commonRank_perm (joinFirst_perm problem))
    (retarget (glbJoinRoundK facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec
        (joinFirst problem))
      (fun _ _ progressed => glbJoinRoundK_commonRank facts roots heads algebra rigid complete headTypingUnique join
        joinSound glb spec progressed))

/-- The Miller round on the store with its Miller equations first, carried back. -/
def millerFirstRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Round S.levels commonRank problem :=
  transport (equivalent_perm (millerFirst_perm problem).symm) (commonRank_perm (millerFirst_perm problem))
    (retarget (Miller.millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
        (millerFirst problem))
      (fun _ _ progressed => Miller.millerGlbRound_commonRank facts roots heads algebra rigid complete normalizes inh
        headTypingUnique glb spec progressed))

/-- **The round of the one solver**: the piece read at every store. -/
noncomputable def oneRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    Round S.levels commonRank problem := by
  classical
  exact if hA : InArrowsCod choices problem then
      retarget (arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          strengthening problem)
        (fun _ _ progressed => arrowCodRound_commonRank choices glb spec facts roots heads algebra rigid complete
          headTypingUnique declared strengthening hA progressed)
    else if InGlbJoinFragmentK problem then
      retarget (glbJoinRoundK facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec problem)
        (fun _ _ progressed => glbJoinRoundK_commonRank facts roots heads algebra rigid complete headTypingUnique join
          joinSound glb spec progressed)
    else if InGlbFragment problem then
      retarget (glbGroupRound facts roots heads algebra rigid complete headTypingUnique glb spec problem)
        (fun _ _ progressed => glbGroupRound_commonRank facts roots heads algebra rigid complete headTypingUnique glb
          spec progressed)
    else if Miller.MixedStore choices problem then
      millerFirstRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec problem
    else joinFirstRound facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec problem

/-- **One solver of the tree's driver**, one rank, every piece. -/
noncomputable def oneSolver : ContextualDependentWorklist.Solver S.levels where
  rank := commonRank
  round := oneRound choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
    strengthening join joinSound glb spec

omit [DecidableRel S.R.headEq] in
/-- **The Miller round on a mixed store keeps it mixed.** -/
theorem millerFirstRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (commonRank update.remaining) (commonRank problem)}
    (mixed : Miller.MixedStore choices problem)
    (progressed : millerFirstRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
      problem = .progress update smaller) :
    Miller.MixedStore choices update.remaining := by
  unfold millerFirstRound at progressed
  obtain ⟨inner, _, isInner, rfl⟩ := transport_progress progressed
  obtain ⟨_, isMiller⟩ := retarget_progress isInner
  exact Miller.millerGlbRound_mixed choices facts roots heads algebra rigid complete normalizes inh headTypingUnique
    glb spec (problem := millerFirst problem) (update := inner) (mixed.perm (millerFirst_perm problem).symm) isMiller

variable (glbTotal : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

omit [DecidableRel S.R.headEq] in
include glbTotal in
/-- **On a mixed store outside the fragment of arrow codes, the Miller round is not stuck**: some equation is not
between arrow codes, so it is a Miller equation, and it comes first. -/
theorem millerFirstRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (mixed : Miller.MixedStore choices problem) (notArrows : ¬ InArrowsCod choices problem) :
    millerFirstRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec problem ≠
      .stuck := by
  unfold millerFirstRound
  apply transport_ne_stuck
  apply retarget_ne_stuck
  obtain ⟨e₀, m₀, notArrow⟩ : ∃ e ∈ problem, ¬ InArrowsCod choices [e] := by
    by_contra none
    apply notArrows
    apply Miller.inArrowsCod_iff.mpr
    intro e m
    by_contra h
    exact none ⟨e, m, h⟩
  obtain ⟨w₀⟩ := (mixed.each e₀ m₀).resolve_right notArrow
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
        headTypingUnique glb spec glbTotal mixed.families ⟨v₁⟩

omit glbTotal [DecidableRel S.R.headEq] in
/-- **The glb-join round on a mixed join store keeps it mixed.** -/
theorem joinFirstRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (commonRank update.remaining) (commonRank problem)}
    (mixed : MixedJoinStore choices problem) (notArrows : ¬ InArrowsCod choices problem)
    (progressed : joinFirstRound facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec
      problem = .progress update smaller) :
    MixedJoinStore choices update.remaining := by
  unfold joinFirstRound at progressed
  obtain ⟨inner, _, isInner, rfl⟩ := transport_progress progressed
  obtain ⟨_, isJoin⟩ := retarget_progress isInner
  obtain ⟨inF, inA⟩ := joinFirst_parts choices mixed
  obtain ⟨e, F, hf⟩ := joinFirst_cons choices mixed notArrows
  rw [hf] at inF
  have hQ : joinFirst problem = (e :: F) ++ problem.filter (fun e => !isFamEq e) := by
    unfold joinFirst
    rw [hf]
  exact glbJoinRoundK_mixed choices facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec
    hQ inF inA isJoin

omit glbTotal in
/-- **The rounds keep the fragment.** -/
theorem oneRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (commonRank update.remaining) (commonRank problem)}
    (inside : InOne choices problem)
    (progressed : oneRound choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening join joinSound glb spec problem = .progress update smaller) :
    InOne choices update.remaining := by
  unfold oneRound at progressed
  split_ifs at progressed with hA hJ hG hM
  · obtain ⟨_, inner⟩ := retarget_progress progressed
    exact .inl (arrowCodRound_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening hA inner)
  · obtain ⟨_, inner⟩ := retarget_progress progressed
    exact .inr (.inl (glbJoinRoundK_stable facts roots heads algebra rigid complete headTypingUnique join joinSound glb
      spec hJ inner))
  · obtain ⟨_, inner⟩ := retarget_progress progressed
    exact .inr (.inr (.inl (glbGroupRound_stable facts roots heads algebra rigid complete headTypingUnique glb spec hG
      inner)))
  · exact .inr (.inr (.inr (.inl (millerFirstRound_stable choices facts roots heads algebra rigid complete normalizes
      inh headTypingUnique glb spec hM progressed))))
  · have mixed : MixedJoinStore choices problem := by
      rcases inside with arrows | joined | grouped | mixedM | mixedJ
      · exact absurd arrows hA
      · exact absurd joined hJ
      · exact absurd grouped hG
      · exact absurd mixedM hM
      · exact mixedJ
    exact .inr (.inr (.inr (.inr (joinFirstRound_stable choices facts roots heads algebra rigid complete
      headTypingUnique join joinSound glb spec mixed hA progressed))))

variable (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)

omit [DecidableRel S.R.headEq] in
include glbTotal joinTotal in
/-- **The glb-join round on a mixed join store outside the fragment of arrow codes is not stuck.** -/
theorem joinFirstRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (mixed : MixedJoinStore choices problem) (notArrows : ¬ InArrowsCod choices problem) :
    joinFirstRound facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec problem ≠
      .stuck := by
  unfold joinFirstRound
  apply transport_ne_stuck
  apply retarget_ne_stuck
  obtain ⟨inF, _⟩ := joinFirst_parts choices mixed
  obtain ⟨e, F, hf⟩ := joinFirst_cons choices mixed notArrows
  rw [hf] at inF
  have hQ : joinFirst problem = (e :: F) ++ problem.filter (fun e => !isFamEq e) := by
    unfold joinFirst
    rw [hf]
  exact glbJoinRoundK_ne_stuck_head facts roots heads algebra rigid complete headTypingUnique join joinSound glb spec
    joinTotal glbTotal hQ inF

include glbTotal joinTotal in
/-- **Progress on the fragment**: a nonempty store is never stuck. -/
theorem oneRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InOne choices problem) (nonempty : problem ≠ []) :
    oneRound choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening
      join joinSound glb spec problem ≠ .stuck := by
  unfold oneRound
  split_ifs with hA hJ hG hM
  · exact retarget_ne_stuck (arrowCodRound_ne_stuck choices glb spec facts roots heads algebra rigid complete
      headTypingUnique declared strengthening glbTotal hA nonempty)
  · exact retarget_ne_stuck (glbJoinRoundK_ne_stuck facts roots heads algebra rigid complete headTypingUnique join
      joinSound glb spec joinTotal glbTotal hJ nonempty)
  · exact retarget_ne_stuck (glbGroupRound_ne_stuck facts roots heads algebra rigid complete headTypingUnique glb spec
      glbTotal hG nonempty)
  · exact millerFirstRound_ne_stuck choices facts roots heads algebra rigid complete normalizes inh headTypingUnique
      glb spec glbTotal hM hA
  · have mixed : MixedJoinStore choices problem := by
      rcases inside with arrows | joined | grouped | mixedM | mixedJ
      · exact absurd arrows hA
      · exact absurd joined hJ
      · exact absurd grouped hG
      · exact absurd mixedM hM
      · exact mixedJ
    exact joinFirstRound_ne_stuck choices facts roots heads algebra rigid complete headTypingUnique join joinSound glb
      spec glbTotal joinTotal mixed hA

include glbTotal joinTotal in
/-- **The fragment of the one solver.** -/
noncomputable def oneFragment :
    ContextualDependentWorklist.Fragment
      (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening
        join joinSound glb spec) where
  holds := InOne choices
  stable := fun inside progressed =>
    oneRound_stable choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening join joinSound glb spec inside progressed
  decisive := fun inside nonempty =>
    oneRound_ne_stuck choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
      strengthening join joinSound glb spec glbTotal joinTotal inside nonempty

include glbTotal joinTotal in
/-- **One solver with one rank decides every piece and every mixed store**: on the fragment, the tree's driver reaches,
at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem one_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} (inside : InOne choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
          strengthening join joinSound glb spec) original larger =
        run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
          strengthening join joinSound glb spec) original fuel ∧
        ((∃ state finished,
              run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
                  strengthening join joinSound glb spec) original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
              strengthening join joinSound glb spec) original larger = .refuted absent)) :=
  (oneFragment choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening
    join joinSound glb spec glbTotal joinTotal).decided inside

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
/-- **Every piece of the earlier union lies inside.** -/
theorem inOne_of_piece {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (k : Piece)
    (inside : InPiece choices k problem) : InOne choices problem := by
  cases k with
  | miller => exact .inr (.inr (.inr (.inl (Miller.MixedStore.of_miller inside))))
  | arrows => exact .inl inside
  | flexRigid => exact .inl (inArrowsCod_of_flexCod inside)
  | glbJoin => exact .inr (.inl inside)
  | glbGroups => exact .inr (.inr (.inl inside))

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
/-- **Every store mixing Miller patterns and arrow codes lies inside.** -/
theorem inOne_of_mixed {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InMixed choices problem) : InOne choices problem := by
  rcases inside with arrows | mixed
  · exact .inl arrows
  · exact .inr (.inr (.inr (.inl mixed)))

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
/-- **Every store mixing glb-join families and arrow codes lies inside.** -/
theorem inOne_of_mixedJoin {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InMixedJoin choices problem) : InOne choices problem := by
  rcases inside with arrows | mixed
  · exact .inl arrows
  · exact .inr (.inr (.inr (.inr mixed)))

include facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening joinSound spec
  glbTotal joinTotal in
/-- **The union of the earlier pieces is decided by one solver with one rank.** -/
theorem one_decided_of_piece {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} (k : Piece)
    (inside : InPiece choices k original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
          strengthening join joinSound glb spec) original larger =
        run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
          strengthening join joinSound glb spec) original fuel ∧
        ((∃ state finished,
              run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
                  strengthening join joinSound glb spec) original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (oneSolver choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared
              strengthening join joinSound glb spec) original larger = .refuted absent)) :=
  one_decided choices facts roots heads algebra rigid complete normalizes inh headTypingUnique declared strengthening
    join joinSound glb spec glbTotal joinTotal (inOne_of_piece choices k inside)

end One

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
