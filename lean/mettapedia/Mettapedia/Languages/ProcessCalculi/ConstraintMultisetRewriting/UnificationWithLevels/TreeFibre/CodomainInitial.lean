import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinInitial

/-!
# Initial solutions of answers with codomains

The rule with codomains keeps the solved unknown `X` declared and sends it to the code `t`; the other unknowns are kept,
the misfit ones declared again at greatest lower bounds. So the answer is not an epimorphism as it stands: `X` is a free
choice of every factor. Deleting the unknowns the answer does not mention, `X` among them, makes a principal answer the
initial solution, through the widening covering of `GlbJoinInitial` at arity zero.

* **The run invariant** (`CodInv`): every unknown the answer mentions, and every unknown of a remaining equation, is
  widening-covered. Narrowing and solving keeps it (`CodInv.narrowSolve`): a kept unknown is transported, its
  declaration the same family or its universe lowered (`codNarrowed_decl`); the unknowns of `t` were covered as
  unknowns of the solved equation.
* **Every solved run of the flex–rigid solver with codomains, trimmed, is the initial solution**
  (`flexCod_solved_initial`), over a telescope of universe families; and every solvable store of its fragment over
  such a telescope has an initial solution (`flexCod_initial`).
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

/-! ## The run invariant -/

section Invariant

variable {S : Setting Head L}

/-- **The run invariant**: every unknown the answer mentions, and every unknown of a remaining equation, is
widening-covered by the answer. -/
structure CodInv {Γ Θ : Context S.R} (σ : Θ ⟶ Γ) (remaining : EquationStore (TotalTerm Θ)) : Prop where
  covered : ∀ j, (∃ i, j ∈ (σ.substitution i).support) → WideCovered σ j
  occurs : ∀ e ∈ remaining, ∀ Y, (Y ∈ e.1.2.code.support ∨ Y ∈ e.2.2.code.support) → WideCovered σ Y

/-- **At the start**, the identity covers every unknown of a telescope of universe families. -/
theorem CodInv.pending {Γ : Context S.R} (families : Miller.Families Γ) (problem : EquationStore (TotalTerm Γ)) :
    CodInv (𝟙 Γ) problem := by
  have all : ∀ j, WideCovered (𝟙 Γ) j := fun j => by
    obtain ⟨ps, c, dj, ups, uc⟩ := families j
    exact fixed_wideCovered (𝟙 Γ) rfl dj dj ups uc uc (S.levels.cumulative_refl uc)
  exact ⟨fun j _ => all j, fun _ _ Y _ => all Y⟩

/-- **Deleting the first equation keeps the invariant.** -/
theorem CodInv.delete {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inv : CodInv σ (e :: rest)) : CodInv (𝟙 Θ ≫ σ) rest := by
  rw [Category.id_comp]
  exact ⟨inv.covered, fun e' member => inv.occurs e' (List.mem_cons_of_mem _ member)⟩

/-- Declarations at universes are universe families. -/
theorem families_of_universes {Θ : Context S.R} (universes : AllUniverseDecls Θ) : Miller.Families Θ := by
  intro i
  obtain ⟨w, hw, uw⟩ := universes i
  exact ⟨[], w, hw, (fun _ h => by cases h), uw⟩

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b) (algebra : CumulativeAlgebra S.R)

include spec in
/-- **The declaration of an unknown after narrowing**: the same family, or its universe lowered. -/
theorem codNarrowed_decl {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e)
    (families : Miller.Families Θ) (k : Fin Θ.arity) (ps : List Head) (c : Head)
    (dk : Ctx.lookup Θ.raw k = famCode ps c) :
    ∃ ps₀ c₀, Ctx.lookup (codNarrowed glb spec v).raw k = famCode ps₀ c₀ ∧ AllUniverses S.R ps₀ ∧
      S.R.isUniverse c₀ ∧ List.Forall₂ S.R.cumulative ps ps₀ ∧ S.R.cumulative c₀ c := by
  obtain ⟨ups, uc⟩ := Miller.famFacts families dk
  cases found : codTarget (S := S) glb Θ.raw v.u e.2.2.code k with
  | some g =>
      obtain ⟨w, hw, low⟩ := codTarget_lowerable glb spec k g found
      have same : (famCode ps c : Tm Head Θ.arity) = famCode [] w := dk.symm.trans hw
      obtain ⟨rfl, rfl⟩ := famCode_inj same
      exact ⟨[], g, lookup_lowerTo_some Θ.raw _ k found, (fun _ h => by cases h),
        codTarget_universe glb spec k g found, .nil, low⟩
  | none =>
      exact ⟨ps, c, (lookup_lowerTo_none Θ.raw _ k found).trans dk, ups, uc,
        List.forall₂_same.mpr (fun x hx => S.levels.cumulative_refl (ups x hx)), S.levels.cumulative_refl uc⟩

include spec in
/-- **Narrowing keeps a telescope of universe families.** -/
theorem families_codNarrowed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e)
    (families : Miller.Families Θ) : Miller.Families (codNarrowed glb spec v) := by
  intro k
  obtain ⟨ps, c, dk, _, _⟩ := families k
  obtain ⟨ps₀, c₀, dk', ups₀, uc₀, _, _⟩ := codNarrowed_decl glb spec v families k ps c dk
  exact ⟨ps₀, c₀, dk', ups₀, uc₀⟩

/-- **Narrowing and solving keeps the invariant**: a kept unknown is transported; the unknowns of `t` were covered as
unknowns of the solved equation. -/
theorem CodInv.narrowSolve {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (families : Miller.Families Θ)
    (shapes : ∀ e' ∈ rest, Nonempty (FlexCod e')) (inv : CodInv σ (e :: rest)) (v : FlexCod e)
    (ok : CodSolvable glb v) :
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
    obtain ⟨w⟩ := shapes e' inRest
    have codeL : ArrowCod e'.1.2.code := by rw [w.side_left]; exact .var w.X
    have side : ∀ s, ArrowCod s → (∀ Z ∈ s.support, WideCovered σ Z) →
        Y ∈ (Presentation.subst (solveSub v.X e.2.2.code) s).support →
          WideCovered (codNarrowSolve glb spec algebra v ok ≫ σ) Y := by
      intro s code covS inside
      rcases support_subst_solve code Y inside with ⟨h, ne⟩ | h
      · exact keep Y ne (covS Y h)
      · exact fromT Y h
    rcases hY with hL | hR
    · exact side _ codeL (fun Z hZ => inv.occurs e' (List.mem_cons_of_mem _ inRest) Z (.inl hZ)) hL
    · exact side _ w.code (fun Z hZ => inv.occurs e' (List.mem_cons_of_mem _ inRest) Z (.inr hZ)) hR

end Invariant

/-! ## The flex–rigid solver with codomains: solved runs are initial -/

section Rounds

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

/-- **Every round keeps the invariant and the telescope of universe families.** -/
theorem flexCodRound_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InFlexCod choices problem) (families : Miller.Families Θ) (inv : CodInv σ problem)
    (progressed : flexCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      problem = .progress update smaller) :
    CodInv (update.answer ≫ σ) update.remaining ∧ Miller.Families update.target := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [flexCodRound] at progressed
      split at progressed
      · rename_i d hd
        unfold stepFlexCod at progressed
        by_cases hdel : e.2.2.code = .var (viewOfCod hd).X
        · rw [dif_pos hdel] at progressed
          cases progressed
          exact ⟨inv.delete, families⟩
        · rw [dif_neg hdel] at progressed
          by_cases hocc : (viewOfCod hd).X ∈ e.2.2.code.support
          · rw [dif_pos hocc] at progressed
            cases progressed
          · rw [dif_neg hocc] at progressed
            split at progressed
            · cases progressed
            · by_cases hok : codSolvableB choices glb (viewOfCod hd) = true
              · rw [dif_pos hok] at progressed
                cases progressed
                exact ⟨CodInv.narrowSolve glb spec algebra families
                    (fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member)) inv (viewOfCod hd) _,
                  families_codNarrowed glb spec (viewOfCod hd) families⟩
              · rw [dif_neg hok] at progressed
                cases progressed
      · cases progressed

/-- **The driver keeps the invariant, the fragment and the telescope of universe families.** -/
theorem drive_codInv {Γ : Context S.R} {original : EquationStore (TotalTerm Γ)} (fuel : Nat) :
    ∀ (state : Update S.levels original), CodInv state.answer state.remaining →
      InFlexCod choices state.remaining → Miller.Families state.target →
        ∀ (final : Update S.levels original) (finished : final.remaining = []),
          drive (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared)
              fuel state = .solved final finished →
            CodInv final.answer final.remaining ∧ Miller.Families final.target := by
  induction fuel with
  | zero =>
      intro state _ _ _ final finished h
      cases h
  | succ fuel ih =>
      intro state inv inside families final finished h
      rw [drive] at h
      cases ha : advance (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique
        declared) state with
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
              obtain ⟨inv', families'⟩ := flexCodRound_inv choices glb spec facts roots heads algebra rigid complete
                headTypingUnique declared inside families inv hround
              have inside' := flexCodRound_stable choices glb spec facts roots heads algebra rigid complete
                headTypingUnique declared inside hround
              exact ih (state.then update) inv' inside' families' final finished h
            · cases ha
            · cases ha

variable (inh : Miller.Inhabitants S.R)

include facts roots heads algebra rigid complete inh in
/-- **Every solved run of the flex–rigid solver with codomains, over a telescope of universe families, ends with an
answer whose trimming is the initial solution.** -/
theorem flexCod_solved_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexCod choices original) (families : Miller.Families Θ) {fuel : Nat}
    {state : Update S.levels original} {finished : state.remaining = []}
    (solved : run (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared)
      original fuel = .solved state finished) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨inv, familiesFinal⟩ := drive_codInv choices glb spec facts roots heads algebra rigid complete
    headTypingUnique declared fuel (Update.pending S.levels original) (CodInv.pending families original) inside
    families state finished solved
  choose ps c hd hu huc using familiesFinal
  exact ⟨_, _, initial_of_wideTrimmed facts roots heads algebra rigid complete inh (state.completed finished)
    (fun j => (ps j, c j)) hd (fun j => ⟨hu j, huc j⟩) inv.covered⟩

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include spec facts roots heads algebra rigid complete headTypingUnique declared inh total in
/-- **Every solvable store of the fragment, over a telescope of universe families, has an initial solution.** -/
theorem flexCod_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexCod choices original) (families : Miller.Families Θ)
    (solvable : (frames S.levels).Solvable original) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨fuel, decided⟩ := flexCod_decided choices glb spec facts roots heads algebra rigid complete
    headTypingUnique declared total inside
  rcases (decided fuel le_rfl).2 with ⟨state, finished, solved, _⟩ | ⟨absent, _⟩
  · exact flexCod_solved_initial choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      inh inside families solved
  · exact absurd solvable absent

end Rounds

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
