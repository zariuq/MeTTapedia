import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowSolver

/-!
# Equations between arrow codes: progress by shape and decision

* `readArrowEq`: an equation between two arrow codes at a universe, read off its codes.
* **Progress by shape** (`arrowRound_ne_stuck`): on a nonempty store of `InArrows`, the round is not stuck. An unknown
  side meets a declaration at a universe comparable with every other (the chain), so narrowing applies; two rigid
  sides are heads or Π types with head codomains, and every pair of them is decided.
* **The rules keep the fragment** (`arrowRound_stable`).
* **Decided** (`arrows_decided`): on `InArrows`, the tree's driver reaches, at some budget and every larger one, a
  principal answer or a certified refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Reading -/

section Reading

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

/-- **Read an equation between two arrow codes at a universe** off its codes. -/
def readArrowEq {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option Head :=
  (headOf e.1.1.code).bind fun v =>
    if e.2.1.code = .head v ∧ S.R.isUniverse v ∧ isArrow e.1.2.code = true ∧ isArrow e.2.2.code = true then some v
    else none

theorem readArrowEq_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {v : Head} (h : readArrowEq e = some v) :
    e.1.1.code = .head v ∧ e.2.1.code = .head v ∧ S.R.isUniverse v ∧ Arrow e.1.2.code ∧ Arrow e.2.2.code := by
  unfold readArrowEq at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨v', hv, h⟩ := h
  split_ifs at h with hc
  cases h
  exact ⟨headOf_sound hv, hc.1, hc.2.1, arrow_of_isArrow hc.2.2.1, arrow_of_isArrow hc.2.2.2⟩

/-- The view of a successful reading. -/
def viewOfArrowEq {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {v : Head} (h : readArrowEq e = some v) :
    ArrowEq e :=
  ⟨v, (readArrowEq_sound h).1, (readArrowEq_sound h).2.1, (readArrowEq_sound h).2.2.1,
    (readArrowEq_sound h).2.2.2.1, (readArrowEq_sound h).2.2.2.2⟩

theorem readArrowEq_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) :
    readArrowEq e = some w.v := by
  unfold readArrowEq
  rw [w.annotation_left]
  simp [headOf, w.annotation_right, w.universe_v, isArrow_of_arrow w.arrow_left, isArrow_of_arrow w.arrow_right]

end Reading

/-! ## Stability of the rigid rules -/

section Decompose

variable (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)

/-- **Decomposition keeps the fragment.** -/
theorem inArrows_decompose {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrows choices (e :: rest))
    (w : ArrowEq e) {A A' : Tm Head Θ.arity} {h h' : Head} (left : e.1.2.code = .pi A (.head h))
    (right : e.2.2.code = .pi A' (.head h')) :
    InArrows choices (domainEquation facts algebra w left right :: rest) := by
  refine ⟨inside.universes, inside.chain, fun e' member => ?_, fun e' member => ?_⟩
  · rcases List.mem_cons.mp member with rfl | member
    · have arrowL : Arrow (Tm.pi A (.head h)) := left ▸ w.arrow_left
      have arrowR : Arrow (Tm.pi A' (.head h')) := right ▸ w.arrow_right
      exact ⟨⟨w.v, w.annotation_left, w.annotation_left, w.universe_v, arrow_domain arrowL, arrow_domain arrowR⟩⟩
    · exact inside.shapes e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨headsL, headsR⟩ := inside.typedHeads e List.mem_cons_self
      rw [left] at headsL
      rw [right] at headsR
      exact ⟨fun h₀ m => headsL h₀ (List.mem_cons_of_mem _ m), fun h₀ m => headsR h₀ (List.mem_cons_of_mem _ m)⟩
    · exact inside.typedHeads e' (List.mem_cons_of_mem _ member)

end Decompose

/-! ## The solver -/

section Solver

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **The round of the solver**: read the first equation, then step. -/
def arrowRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels arrowRank problem
  | _, [] => .stuck
  | _, e :: rest =>
      match hd : readArrowEq e with
      | some _ => stepArrow choices facts roots heads algebra rigid complete headTypingUnique (viewOfArrowEq hd) rest
      | none => .stuck

/-- **The tree's driver on equations between arrow codes.** -/
def arrowSolver : ContextualDependentWorklist.Solver S.levels where
  rank := arrowRank
  round := arrowRound choices facts roots heads algebra rigid complete headTypingUnique

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
theorem declared_universe {Θ : Context S.R} (universes : AllUniverseDecls Θ) {X : Fin Θ.arity} {u : Head}
    (hu : declaredUniverse Θ.raw X = some u) : S.R.isUniverse u := by
  obtain ⟨w, hw, uw⟩ := universes X
  unfold declaredUniverse at hu
  rw [hw] at hu
  cases hu
  exact uw

omit [DecidableEq Head] [DecidableRel S.R.headEq] in
/-- **In the fragment, the conditions of narrow-and-solve hold** once neither refutation applies. -/
theorem solvable_in_fragment {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InArrows choices (e :: rest)) (v : FlexArrow e)
    (none : (arrowHeads e.2.2.code).find? (misfitPred choices v.u) = none) :
    solvableB choices v = true := by
  simp only [solvableB, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, allUniverseDeclsB_of inside.universes⟩
  · apply List.all_eq_true.mpr
    intro h member
    have typed := (inside.typedHeads e List.mem_cons_self).2 h member
    have notMisfit := List.find?_eq_none.mp none h member
    unfold fitPred
    unfold misfitPred at notMisfit
    cases hk : choices.typing h with
    | none => rw [hk] at typed; cases typed
    | some k =>
        rw [hk] at notMisfit
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_not] at notMisfit
        exact decide_eq_true notMisfit
  · apply List.all_eq_true.mpr
    intro Y _
    obtain ⟨w, hw, _⟩ := inside.universes Y
    unfold comparablePred declaredUniverse
    rw [hw]
    simp only [headOf, Bool.or_eq_true, decide_eq_true_eq]
    exact inside.chain Y v.X w v.u hw v.declared

omit [DecidableEq Head] [DecidableRel S.R.headEq] in
theorem flexStep_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : FlexArrow e) (ne : e.2.2.code ≠ .var v.X) (inside : InArrows choices (e :: rest)) :
    flexStep choices facts roots heads algebra rigid complete headTypingUnique v ne rest ≠ .stuck := by
  unfold flexStep
  by_cases hocc : v.X ∈ domainVars e.2.2.code
  · rw [dif_pos hocc]
    intro h; cases h
  · rw [dif_neg hocc]
    split
    · intro h; cases h
    · rename_i hmis
      have ok : solvableB choices v = true ∧ allArrowsB rest = true :=
        ⟨solvable_in_fragment choices inside v hmis, allArrowsB_of (inArrows_drop inside).arrows⟩
      rw [dif_pos ok]
      intro h; cases h

omit [DecidableEq Head] [DecidableRel S.R.headEq] in
theorem flexStep_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : FlexArrow e) (ne : e.2.2.code ≠ .var v.X) {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (arrowRank update.remaining) (arrowRank (e :: rest))}
    (inside : InArrows choices (e :: rest))
    (progressed : flexStep choices facts roots heads algebra rigid complete headTypingUnique v ne rest =
      .progress update smaller) : InArrows choices update.remaining := by
  unfold flexStep at progressed
  by_cases hocc : v.X ∈ domainVars e.2.2.code
  · rw [dif_pos hocc] at progressed
    cases progressed
  · rw [dif_neg hocc] at progressed
    split at progressed
    · cases progressed
    · by_cases hok : solvableB choices v = true ∧ allArrowsB rest = true
      · rw [dif_pos hok] at progressed
        cases progressed
        exact inArrows_solved algebra inside v _
      · rw [dif_neg hok] at progressed
        cases progressed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
theorem swapRound_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {round : Round S.levels arrowRank (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest)} (moving : round ≠ .stuck) :
    swapRound round ≠ .stuck := by
  cases round with
  | progress _ _ => intro h; cases h
  | refuted _ => intro h; cases h
  | stuck => exact absurd rfl moving

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
theorem swapRound_progress {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {round : Round S.levels arrowRank (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest)}
    {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (arrowRank update.remaining) (arrowRank (e :: rest))}
    (progressed : swapRound round = .progress update smaller) :
    ∃ inner innerSmaller, round = .progress inner innerSmaller ∧ update = inner.rephrase (swap_equivalent e rest) := by
  cases round with
  | progress inner innerSmaller =>
      cases progressed
      exact ⟨inner, innerSmaller, rfl, rfl⟩
  | refuted _ => cases progressed
  | stuck => cases progressed

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem rigidStep_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e)
    (rest : EquationStore (TotalTerm Θ)) (notLeft : varOf e.1.2.code = none) (notRight : varOf e.2.2.code = none) :
    rigidStep facts roots heads algebra rigid complete w rest ≠ .stuck := by
  have sl := rigidOf_arrow w.arrow_left notLeft
  have sr := rigidOf_arrow w.arrow_right notRight
  unfold rigidStep
  split
  · split_ifs <;> intro h <;> cases h
  · intro h; cases h
  · intro h; cases h
  · split_ifs <;> intro h <;> cases h
  · exfalso
    simp_all
  · exfalso
    simp_all

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem rigidStep_stable {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (w : ArrowEq e)
    {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (arrowRank update.remaining) (arrowRank (e :: rest))}
    (inside : InArrows choices (e :: rest))
    (progressed : rigidStep facts roots heads algebra rigid complete w rest = .progress update smaller) :
    InArrows choices update.remaining := by
  unfold rigidStep at progressed
  split at progressed
  · split_ifs at progressed
    · cases progressed
      exact inArrows_drop inside
    · cases progressed
      exact inArrows_drop inside
  · cases progressed
  · cases progressed
  · split_ifs at progressed
    cases progressed
    exact inArrows_decompose facts algebra inside w _ _
  · cases progressed
  · cases progressed

theorem stepArrow_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (w : ArrowEq e) (inside : InArrows choices (e :: rest)) :
    stepArrow choices facts roots heads algebra rigid complete headTypingUnique w rest ≠ .stuck := by
  unfold stepArrow
  by_cases hsame : e.1.2.code = e.2.2.code
  · rw [dif_pos hsame]
    intro h; cases h
  · rw [dif_neg hsame]
    split
    · split
      · rename_i u hu
        rw [dif_pos (declared_universe inside.universes hu)]
        exact flexStep_ne_stuck choices facts roots heads algebra rigid complete headTypingUnique _ _ inside
      · rename_i X _ hu
        exfalso
        obtain ⟨w', hw', _⟩ := inside.universes X
        unfold declaredUniverse at hu
        rw [hw'] at hu
        cases hu
    · split
      · split
        · rename_i u hu
          rw [dif_pos (declared_universe inside.universes hu)]
          exact swapRound_ne_stuck (flexStep_ne_stuck choices facts roots heads algebra rigid complete
            headTypingUnique _ _ (inArrows_swap inside))
        · rename_i Y _ hu
          exfalso
          obtain ⟨w', hw', _⟩ := inside.universes Y
          unfold declaredUniverse at hu
          rw [hw'] at hu
          cases hu
      · rename_i hX hY
        exact rigidStep_ne_stuck facts roots heads algebra rigid complete w rest hX hY

theorem stepArrow_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (w : ArrowEq e) {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (arrowRank update.remaining) (arrowRank (e :: rest))}
    (inside : InArrows choices (e :: rest))
    (progressed : stepArrow choices facts roots heads algebra rigid complete headTypingUnique w rest =
      .progress update smaller) : InArrows choices update.remaining := by
  unfold stepArrow at progressed
  by_cases hsame : e.1.2.code = e.2.2.code
  · rw [dif_pos hsame] at progressed
    cases progressed
    exact inArrows_drop inside
  · rw [dif_neg hsame] at progressed
    split at progressed
    · split at progressed
      · split_ifs at progressed
        exact flexStep_stable choices facts roots heads algebra rigid complete headTypingUnique _ _ inside progressed
      · cases progressed
    · split at progressed
      · split at progressed
        · split_ifs at progressed
          obtain ⟨inner, _, isInner, same⟩ := swapRound_progress progressed
          subst same
          show InArrows choices inner.remaining
          exact flexStep_stable choices facts roots heads algebra rigid complete headTypingUnique _ _
            (inArrows_swap inside) isInner
        · cases progressed
      · exact rigidStep_stable facts roots heads algebra rigid complete w inside progressed

/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem arrowRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InArrows choices problem) (nonempty : problem ≠ []) :
    arrowRound choices facts roots heads algebra rigid complete headTypingUnique problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨w⟩ := inside.shapes e List.mem_cons_self
      have hd := readArrowEq_complete w
      simp only [arrowRound]
      split
      · exact stepArrow_ne_stuck choices facts roots heads algebra rigid complete headTypingUnique _ inside
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem arrowRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (arrowRank update.remaining) (arrowRank problem)}
    (inside : InArrows choices problem)
    (progressed : arrowRound choices facts roots heads algebra rigid complete headTypingUnique problem =
      .progress update smaller) :
    InArrows choices update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [arrowRound] at progressed
      split at progressed
      · exact stepArrow_stable choices facts roots heads algebra rigid complete headTypingUnique _ inside progressed
      · cases progressed

/-- **The fragment of the solver.** -/
def arrowFragment :
    ContextualDependentWorklist.Fragment
      (arrowSolver choices facts roots heads algebra rigid complete headTypingUnique) where
  holds := InArrows choices
  stable := fun inside progressed =>
    arrowRound_stable choices facts roots heads algebra rigid complete headTypingUnique inside progressed
  decisive := fun inside nonempty =>
    arrowRound_ne_stuck choices facts roots heads algebra rigid complete headTypingUnique inside nonempty

include facts roots heads algebra rigid complete headTypingUnique in
/-- **Decided by shape**: on the fragment of equations between arrow codes, the tree's driver with narrowing,
solving, decomposition and the refutations reaches, at some budget and at every larger one, a principal answer or a
certified refutation. -/
theorem arrows_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} (inside : InArrows choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (arrowSolver choices facts roots heads algebra rigid complete headTypingUnique) original larger =
          run (arrowSolver choices facts roots heads algebra rigid complete headTypingUnique) original fuel ∧
        ((∃ state finished,
              run (arrowSolver choices facts roots heads algebra rigid complete headTypingUnique) original larger =
                .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (arrowSolver choices facts roots heads algebra rigid complete headTypingUnique) original larger =
              .refuted absent)) :=
  (arrowFragment choices facts roots heads algebra rigid complete headTypingUnique).decided inside

end Solver

/-! ## Membership, decided -/

section Membership

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)

/-- **Membership in the fragment of equations between arrow codes, decided.** -/
def inArrowsB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allUniverseDeclsB Θ && chainB Θ && problem.all (fun e => (readArrowEq e).isSome) &&
    problem.all (fun e => (arrowHeads e.1.2.code).all (fun h => (choices.typing h).isSome) &&
      (arrowHeads e.2.2.code).all (fun h => (choices.typing h).isSome))

theorem inArrows_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inArrowsB choices problem = true) : InArrows choices problem := by
  simp only [inArrowsB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hAll, hChain⟩, hShapes⟩, hHeads⟩ := h
  refine ⟨allUniverseDecls_of_B hAll, chain_of_B hChain, fun e member => ?_, fun e member => ?_⟩
  · have he := List.all_eq_true.mp hShapes e member
    cases hd : readArrowEq e with
    | none => rw [hd] at he; cases he
    | some v => exact ⟨viewOfArrowEq hd⟩
  · have he := List.all_eq_true.mp hHeads e member
    simp only [Bool.and_eq_true] at he
    exact ⟨fun h hh => List.all_eq_true.mp he.1 h hh, fun h hh => List.all_eq_true.mp he.2 h hh⟩

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
