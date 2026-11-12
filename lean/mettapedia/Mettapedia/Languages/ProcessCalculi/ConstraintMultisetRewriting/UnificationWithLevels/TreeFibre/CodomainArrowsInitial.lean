import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrows

/-!
# Initial solutions of answers between arrow codes with codomains

The run invariant `CodInv` is kept by every rule of the solver of arrow codes with codomains:

* deletion, equal heads and decomposition have the identity as answer, and the unknowns of the parts of a
  decomposition are those of the whole (`CodInv.decompose`);
* narrowing and solving keeps it for any remaining store of arrow codes (`CodInv.narrowSolveCodes`), in either
  orientation (`CodInv.swap`).

**Every solved run, over a telescope of universe families, trimmed, is the initial solution**
(`arrowsCod_solved_initial`), and every solvable store of the fragment over such a telescope has one
(`arrowsCod_initial`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## The invariant under the rules of arrow codes -/

section Invariant

variable {S : Setting Head L}

/-- **Swapping the sides keeps the invariant.** -/
theorem CodInv.swap {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inv : CodInv σ (e :: rest)) :
    CodInv σ (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) := by
  refine ⟨inv.covered, fun e' member Y hY => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact inv.occurs e List.mem_cons_self Y hY.symm
  · exact inv.occurs e' (List.mem_cons_of_mem _ member) Y hY

/-- **Decomposition keeps the invariant**: the answer is the identity, and the unknowns of the parts are those of the
whole. -/
theorem CodInv.decompose {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e d c : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} {A A' B B' : Tm Head Θ.arity}
    (left : e.1.2.code = .pi A (Presentation.rename wk B)) (right : e.2.2.code = .pi A' (Presentation.rename wk B'))
    (dl : d.1.2.code = A) (dr : d.2.2.code = A') (cl : c.1.2.code = B) (cr : c.2.2.code = B')
    (inv : CodInv σ (e :: rest)) : CodInv (𝟙 Θ ≫ σ) (d :: c :: rest) := by
  rw [Category.id_comp]
  have whole : ∀ Y, (Y ∈ A.support ∨ Y ∈ B.support) ∨ (Y ∈ A'.support ∨ Y ∈ B'.support) → WideCovered σ Y := by
    intro Y h
    apply inv.occurs e List.mem_cons_self Y
    rw [left, right, mem_support_pi_wk, mem_support_pi_wk]
    exact h
  refine ⟨inv.covered, fun e' member Y hY => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · rw [dl, dr] at hY
    rcases hY with h | h
    · exact whole Y (.inl (.inl h))
    · exact whole Y (.inr (.inl h))
  rcases List.mem_cons.mp member with rfl | member
  · rw [cl, cr] at hY
    rcases hY with h | h
    · exact whole Y (.inl (.inr h))
    · exact whole Y (.inr (.inr h))
  · exact inv.occurs e' (List.mem_cons_of_mem _ member) Y hY

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b) (algebra : CumulativeAlgebra S.R)

/-- **Narrowing and solving keeps the invariant**, for any remaining store of arrow codes with codomains. -/
theorem CodInv.narrowSolveCodes {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (families : Miller.Families Θ) (codes : AllArrowCod rest)
    (inv : CodInv σ (e :: rest)) (v : FlexCod e) (ok : CodSolvable glb v) :
    CodInv (codNarrowSolve glb spec algebra v ok ≫ σ)
      ((frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest) := by
  have keep : ∀ k, k ≠ v.X → WideCovered σ k → WideCovered (codNarrowSolve glb spec algebra v ok ≫ σ) k := by
    intro k ne cov
    exact WideCovered.transport algebra.trans (codNarrowSolve glb spec algebra v ok) cov (solveSub_ne _ ne)
      (codNarrowed_decl glb spec v families k)
  have fromT : ∀ Y, Y ∈ e.2.2.code.support → WideCovered (codNarrowSolve glb spec algebra v ok ≫ σ) Y :=
    fun Y h => keep Y (fun same => ok.absent (same ▸ h)) (inv.occurs e List.mem_cons_self Y (.inr h))
  constructor
  · rintro j ⟨i, hj⟩
    change j ∈ (Presentation.subst (solveSub v.X e.2.2.code) (σ.substitution i)).support at hj
    obtain ⟨k, hk, hjk⟩ := Miller.support_subst_sub _ (solveSub v.X e.2.2.code) hj
    by_cases hkX : k = v.X
    · rw [hkX, solveSub_self] at hjk
      exact fromT j hjk
    · rw [solveSub_ne _ hkX] at hjk
      have jk : j = k := Finset.mem_singleton.mp hjk
      rw [jk]
      exact keep k hkX (inv.covered k ⟨i, hk⟩)
  · intro e'' member Y hY
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨codeL, codeR⟩ := codes e' inRest
    have side : ∀ s, ArrowCod s → (∀ Z ∈ s.support, WideCovered σ Z) →
        Y ∈ (Presentation.subst (solveSub v.X e.2.2.code) s).support →
          WideCovered (codNarrowSolve glb spec algebra v ok ≫ σ) Y := by
      intro s code covS inside
      rcases support_subst_solve code Y inside with ⟨h, ne⟩ | h
      · exact keep Y ne (covS Y h)
      · exact fromT Y h
    rcases hY with hL | hR
    · exact side _ codeL (fun Z hZ => inv.occurs e' (List.mem_cons_of_mem _ inRest) Z (.inl hZ)) hL
    · exact side _ codeR (fun Z hZ => inv.occurs e' (List.mem_cons_of_mem _ inRest) Z (.inr hZ)) hR

end Invariant

/-! ## The solver of arrow codes with codomains: solved runs are initial -/

section Rounds

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)

omit [DecidableEq Head] [DecidableRel S.R.headEq] in
theorem flexStepCod_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (v : FlexCod e) (ne : e.2.2.code ≠ .var v.X)
    {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))}
    (families : Miller.Families Θ) (codes : AllArrowCod rest) (inv : CodInv σ (e :: rest))
    (progressed : flexStepCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared v ne
      rest = .progress update smaller) :
    CodInv (update.answer ≫ σ) update.remaining ∧ Miller.Families update.target := by
  unfold flexStepCod at progressed
  by_cases hocc : v.X ∈ e.2.2.code.support
  · rw [dif_pos hocc] at progressed
    cases progressed
  · rw [dif_neg hocc] at progressed
    split at progressed
    · cases progressed
    · by_cases hok : codSolvableB choices glb v = true ∧ allArrowCodB rest = true
      · rw [dif_pos hok] at progressed
        cases progressed
        exact ⟨CodInv.narrowSolveCodes glb spec algebra families codes inv v _,
          families_codNarrowed glb spec v families⟩
      · rw [dif_neg hok] at progressed
        cases progressed

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem rigidStepCod_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (w : ArrowCodEq e) {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))}
    (families : Miller.Families Θ) (inv : CodInv σ (e :: rest))
    (progressed : rigidStepCod facts roots heads algebra rigid complete headTypingUnique declared strengthening w
      rest = .progress update smaller) :
    CodInv (update.answer ≫ σ) update.remaining ∧ Miller.Families update.target := by
  unfold rigidStepCod at progressed
  split at progressed
  · split_ifs at progressed
    · cases progressed
      exact ⟨inv.delete, families⟩
    · cases progressed
      exact ⟨inv.delete, families⟩
  · cases progressed
  · cases progressed
  · rename_i A B A' B' hl hr
    cases progressed
    exact ⟨CodInv.decompose (rigidCodOf_pi hl) (rigidCodOf_pi hr) rfl rfl rfl rfl inv, families⟩
  · cases progressed
  · cases progressed

theorem stepArrowCod_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (w : ArrowCodEq e) {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))}
    (inside : InArrowsCod choices (e :: rest)) (families : Miller.Families Θ) (inv : CodInv σ (e :: rest))
    (progressed : stepArrowCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening w rest = .progress update smaller) :
    CodInv (update.answer ≫ σ) update.remaining ∧ Miller.Families update.target := by
  unfold stepArrowCod at progressed
  by_cases hsame : e.1.2.code = e.2.2.code
  · rw [dif_pos hsame] at progressed
    cases progressed
    exact ⟨inv.delete, families⟩
  · rw [dif_neg hsame] at progressed
    split at progressed
    · split at progressed
      · split_ifs at progressed
        exact flexStepCod_inv choices glb spec facts roots heads algebra rigid complete headTypingUnique declared _ _
          families (inArrowsCod_drop inside).codes inv progressed
      · cases progressed
    · split at progressed
      · split at progressed
        · split_ifs at progressed
          obtain ⟨inner, _, isInner, same⟩ := swapRoundCod_progress progressed
          subst same
          show CodInv (inner.answer ≫ σ) inner.remaining ∧ Miller.Families inner.target
          exact flexStepCod_inv choices glb spec facts roots heads algebra rigid complete headTypingUnique declared _ _
            families (inArrowsCod_drop inside).codes inv.swap isInner
        · cases progressed
      · exact rigidStepCod_inv facts roots heads algebra rigid complete headTypingUnique declared strengthening w
          families inv progressed

/-- **Every round keeps the invariant and the telescope of universe families.** -/
theorem arrowCodRound_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank problem)}
    (inside : InArrowsCod choices problem) (families : Miller.Families Θ) (inv : CodInv σ problem)
    (progressed : arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening problem = .progress update smaller) :
    CodInv (update.answer ≫ σ) update.remaining ∧ Miller.Families update.target := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [arrowCodRound] at progressed
      split at progressed
      · exact stepArrowCod_inv choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          strengthening _ inside families inv progressed
      · cases progressed

/-- **The driver keeps the invariant, the fragment and the telescope of universe families.** -/
theorem drive_codInvA {Γ : Context S.R} {original : EquationStore (TotalTerm Γ)} (fuel : Nat) :
    ∀ (state : Update S.levels original), CodInv state.answer state.remaining →
      InArrowsCod choices state.remaining → Miller.Families state.target →
        ∀ (final : Update S.levels original) (finished : final.remaining = []),
          drive (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
              strengthening) fuel state = .solved final finished →
            CodInv final.answer final.remaining ∧ Miller.Families final.target := by
  induction fuel with
  | zero =>
      intro state _ _ _ final finished h
      cases h
  | succ fuel ih =>
      intro state inv inside families final finished h
      rw [drive] at h
      cases ha : advance (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique
        declared strengthening) state with
      | done outcome =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
            cases h
            exact ⟨inv, families⟩
          · split at ha
            · cases ha
            · cases ha
              cases h
            · cases ha
              cases h
      | next next =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
          · split at ha
            · rename_i update smaller hround
              cases ha
              obtain ⟨inv', families'⟩ := arrowCodRound_inv choices glb spec facts roots heads algebra rigid complete
                headTypingUnique declared strengthening inside families inv hround
              have inside' := arrowCodRound_stable choices glb spec facts roots heads algebra rigid complete
                headTypingUnique declared strengthening inside hround
              exact ih (state.then update) inv' inside' families' final finished h
            · cases ha
            · cases ha

variable (inh : Miller.Inhabitants S.R)

include facts roots heads algebra rigid complete inh in
/-- **Every solved run of the solver of arrow codes with codomains, over a telescope of universe families, ends with an
answer whose trimming is the initial solution.** -/
theorem arrowsCod_solved_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod choices original) (families : Miller.Families Θ) {fuel : Nat}
    {state : Update S.levels original} {finished : state.remaining = []}
    (solved : run (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening) original fuel = .solved state finished) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨inv, familiesFinal⟩ := drive_codInvA choices glb spec facts roots heads algebra rigid complete
    headTypingUnique declared strengthening fuel (Update.pending S.levels original)
    (CodInv.pending families original) inside families state finished solved
  choose ps c hd hu huc using familiesFinal
  exact ⟨_, _, initial_of_wideTrimmed facts roots heads algebra rigid complete inh (state.completed finished)
    (fun j => (ps j, c j)) hd (fun j => ⟨hu j, huc j⟩) inv.covered⟩

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include spec facts roots heads algebra rigid complete headTypingUnique declared strengthening inh total in
/-- **Every solvable store of the fragment of arrow codes with codomains, over a telescope of universe families, has an
initial solution.** -/
theorem arrowsCod_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod choices original) (families : Miller.Families Θ)
    (solvable : (frames S.levels).Solvable original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨fuel, decided⟩ := arrowsCod_decided choices glb spec facts roots heads algebra rigid complete
    headTypingUnique declared strengthening total inside
  rcases (decided fuel le_rfl).2 with ⟨state, finished, solved, _⟩ | ⟨absent, _⟩
  · exact arrowsCod_solved_initial choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening inh inside families solved
  · exact absurd solvable absent

end Rounds

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
