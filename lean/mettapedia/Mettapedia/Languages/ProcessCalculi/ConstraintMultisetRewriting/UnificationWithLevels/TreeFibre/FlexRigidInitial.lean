import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupsInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlb

/-!
# Initial solutions for flex-rigid equations without the chain

Every solved run of the flex-rigid solver narrowing to greatest lower bounds ends with an answer the trimming
theorem applies to (`flexRigidGlb_solved_initial`), as for glb groups (`glbGroup_solved_initial`).

* **The unknowns of an arrow code are its domain unknowns** (`arrow_support`).
* **In place, for flex-rigid stores** (`InPlaceFR`): as `InPlaceData`, with the remaining equations' left unknowns
  and right-side unknowns fixed.
* **One step** (`InPlaceFR.step`): the identity on the unknowns but possibly one `G`, sent to a term whose unknowns
  are fixed and other than `G`.
* **Narrowing to greatest lower bounds and solving is such a step** (`flexRigidGlbRound_inPlace`); the driver keeps
  the shape (`driveFR_inPlace`).
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

theorem arrow_support {n : Nat} {t : Tm Head n} (arrow : Arrow t) {x : Fin n} (member : x ∈ t.support) :
    x ∈ domainVars t := by
  induction arrow with
  | var Y =>
      simp only [Tm.support, Finset.mem_singleton] at member
      subst member
      exact List.mem_singleton_self _
  | head h => simp only [Tm.support, Finset.notMem_empty] at member
  | pi h _ ih =>
      simp only [Tm.support, Finset.mem_union, mem_outerSupport, Finset.notMem_empty, or_false] at member
      exact ih member

section Shape

variable {S : Setting Head L}

/-- **In place, for flex-rigid stores.** -/
structure InPlaceFR {Γ Θ : Context S.R} (σ : Θ ⟶ Γ) (remaining : EquationStore (TotalTerm Θ)) : Prop where
  same : Θ.arity = Γ.arity
  families : ∀ j : Fin Θ.arity, ∃ (ps : List Head) (c : Head),
    Ctx.lookup Θ.raw j = famCode ps c ∧ AllUniverses S.R ps ∧ S.R.isUniverse c
  fixedSupport : ∀ (i : Fin Γ.arity) (j : Fin Θ.arity), j ∈ (σ.substitution i).support →
    σ.substitution (Fin.cast same j) = .var j
  lowered : ∀ j : Fin Θ.arity, σ.substitution (Fin.cast same j) = .var j →
    ∃ (ps : List Head) (c c' : Head), Ctx.lookup Θ.raw j = famCode ps c ∧
      Ctx.lookup Γ.raw (Fin.cast same j) = famCode ps c' ∧ S.R.isUniverse c' ∧ S.R.cumulative c c'
  remaining : ∀ e ∈ remaining, ∀ v : FlexArrow e,
    σ.substitution (Fin.cast same v.X) = .var v.X ∧
      ∀ Y ∈ domainVars e.2.2.code, σ.substitution (Fin.cast same Y) = .var Y

/-- **The start of a run is in place.** -/
theorem InPlaceFR.pending {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ))
    (families : ∀ j : Fin Γ.arity, ∃ (ps : List Head) (c : Head),
      Ctx.lookup Γ.raw j = famCode ps c ∧ AllUniverses S.R ps ∧ S.R.isUniverse c) :
    InPlaceFR (𝟙 Γ) problem where
  same := rfl
  families := families
  fixedSupport := by
    intro i j member
    change j ∈ (Tm.var i : Tm Head Γ.arity).support at member
    simp only [Tm.support, Finset.mem_singleton] at member
    subst member
    rfl
  lowered := by
    intro j _
    obtain ⟨ps, c, d, _, uc⟩ := families j
    exact ⟨ps, c, c, d, d, uc, S.levels.cumulative_refl uc⟩
  remaining := fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩

/-- **One in-place step**: the identity on the unknowns but possibly one `G`, sent to a term whose unknowns are fixed
and other than `G`; the step's telescope lowers codomains only; its remaining equations avoid `G` and mention only
fixed unknowns. -/
theorem InPlaceFR.step {Γ Θ Θ' : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)}
    (inv : InPlaceFR σ R) (trans : ∀ {u v w : Head}, S.R.cumulative u v → S.R.cumulative v w → S.R.cumulative u w)
    (τ : Θ' ⟶ Θ) (sameU : Θ'.arity = Θ.arity) (R' : EquationStore (TotalTerm Θ')) (G : Option (Fin Θ.arity))
    (sub : ∀ k : Fin Θ.arity,
      (G = some k ∧ ∀ x ∈ (τ.substitution k).support, G ≠ some (Fin.cast sameU x) ∧
        σ.substitution (Fin.cast inv.same (Fin.cast sameU x)) = .var (Fin.cast sameU x)) ∨
      (G ≠ some k ∧ τ.substitution k = .var (Fin.cast sameU.symm k)))
    (decl : ∀ k : Fin Θ'.arity, ∃ (ps : List Head) (c c₀ : Head), Ctx.lookup Θ'.raw k = famCode ps c ∧
      Ctx.lookup Θ.raw (Fin.cast sameU k) = famCode ps c₀ ∧ AllUniverses S.R ps ∧ S.R.isUniverse c ∧
      S.R.cumulative c c₀)
    (rem : ∀ e ∈ R', ∀ v : FlexArrow e,
      (G ≠ some (Fin.cast sameU v.X) ∧
        σ.substitution (Fin.cast inv.same (Fin.cast sameU v.X)) = .var (Fin.cast sameU v.X)) ∧
      ∀ Y ∈ domainVars e.2.2.code, G ≠ some (Fin.cast sameU Y) ∧
        σ.substitution (Fin.cast inv.same (Fin.cast sameU Y)) = .var (Fin.cast sameU Y)) :
    InPlaceFR (τ ≫ σ) R' := by
  -- the image of a variable that the step fixes and the answer fixes
  have keep : ∀ x : Fin Θ'.arity, G ≠ some (Fin.cast sameU x) →
      σ.substitution (Fin.cast inv.same (Fin.cast sameU x)) = .var (Fin.cast sameU x) →
      Presentation.subst τ.substitution (σ.substitution (Fin.cast (sameU.trans inv.same) x)) = .var x := by
    intro x hG fixed
    have castEq : Fin.cast (sameU.trans inv.same) x = Fin.cast inv.same (Fin.cast sameU x) := Fin.ext rfl
    rw [castEq, fixed]
    change τ.substitution (Fin.cast sameU x) = .var x
    rcases sub (Fin.cast sameU x) with ⟨hG', _⟩ | ⟨_, hτ⟩
    · exact absurd hG' hG
    · rw [hτ]
      exact congrArg Tm.var (Fin.ext rfl)
  refine ⟨sameU.trans inv.same, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨ps, c, _, dk, _, ups, uc, _⟩ := decl k
    exact ⟨ps, c, dk, ups, uc⟩
  · intro i j member
    change j ∈ (Presentation.subst τ.substitution (σ.substitution i)).support at member
    obtain ⟨k, hk, hj⟩ := Miller.support_subst_sub _ τ.substitution member
    have fixedK := inv.fixedSupport i k hk
    rcases sub k with ⟨_, hsupp⟩ | ⟨_, hτ⟩
    · obtain ⟨hG, fixed⟩ := hsupp j hj
      exact keep j hG fixed
    · rw [hτ] at hj
      have jk : j = Fin.cast sameU.symm k := by
        simpa only [Tm.support, Finset.mem_singleton] using hj
      change Presentation.subst τ.substitution (σ.substitution (Fin.cast (sameU.trans inv.same) j)) = .var j
      have castEq : Fin.cast (sameU.trans inv.same) j = Fin.cast inv.same k := by
        rw [jk]
        exact Fin.ext rfl
      rw [castEq, fixedK]
      change τ.substitution k = .var j
      rw [hτ, jk]
  · intro j fixed
    change Presentation.subst τ.substitution (σ.substitution (Fin.cast (sameU.trans inv.same) j)) = .var j at fixed
    obtain ⟨k', hk', hτk'⟩ := subst_eq_var fixed
    have k'eq : k' = Fin.cast sameU j := by
      rcases sub k' with ⟨hG, hsupp⟩ | ⟨_, hτ⟩
      · -- `k'` is the solved unknown: its image is a variable `j`, fixed and not `k'`
        have member : j ∈ (τ.substitution k').support := by
          rw [hτk']
          simp only [Tm.support, Finset.mem_singleton]
        obtain ⟨hGj, fixedj⟩ := hsupp j member
        have castEq : Fin.cast (sameU.trans inv.same) j = Fin.cast inv.same (Fin.cast sameU j) := Fin.ext rfl
        rw [castEq, fixedj] at hk'
        exact absurd (hG.trans (congrArg some (Tm.var.inj hk').symm)) hGj
      · rw [hτ] at hτk'
        have jk : Fin.cast sameU.symm k' = j := Tm.var.inj hτk'
        rw [← jk]
        exact Fin.ext rfl
    have castEq : Fin.cast (sameU.trans inv.same) j = Fin.cast inv.same k' := by
      rw [k'eq]
      exact Fin.ext rfl
    rw [castEq] at hk'
    obtain ⟨ps, c, c', dΘ, dΓ, uc', le⟩ := inv.lowered k' hk'
    obtain ⟨ps₂, c₂, c₀, d₂, d₀, _, _, le₂⟩ := decl j
    rw [← k'eq] at d₀
    obtain ⟨hps, hc⟩ := famCode_inj (d₀.symm.trans dΘ)
    rw [hc] at le₂
    refine ⟨ps₂, c₂, c', d₂, ?_, uc', trans le₂ le⟩
    rw [castEq, hps]
    exact dΓ
  · intro e member v
    obtain ⟨⟨hGX, fixedX⟩, hY⟩ := rem e member v
    refine ⟨keep v.X hGX fixedX, fun Y memberY => ?_⟩
    obtain ⟨hGY, fixedY⟩ := hY Y memberY
    exact keep Y hGY fixedY

end Shape

/-! ## The round and the driver keep the shape -/

section Round

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **Every progress of the round is an in-place step.** -/
theorem flexRigidGlbRound_inPlace {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inv : InPlaceFR σ problem) (inside : InFlexRigidGlb choices problem)
    (progressed : flexRigidGlbRound choices glb spec facts roots heads algebra rigid complete headTypingUnique
      problem = .progress update smaller) :
    InPlaceFR (update.answer ≫ σ) update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      have restFixed : ∀ e' ∈ rest, ∀ w : FlexArrow e',
          σ.substitution (Fin.cast inv.same w.X) = .var w.X ∧
            ∀ Y ∈ domainVars e'.2.2.code, σ.substitution (Fin.cast inv.same Y) = .var Y :=
        fun e' member w => inv.remaining e' (List.mem_cons_of_mem _ member) w
      simp only [flexRigidGlbRound] at progressed
      split at progressed
      · rename_i d hd
        have here := inv.remaining e List.mem_cons_self (viewOfArrow hd)
        unfold stepFlexRigidGlb at progressed
        by_cases hdel : e.2.2.code = .var (viewOfArrow hd).X
        · rw [dif_pos hdel] at progressed
          cases progressed
          refine inv.step algebra.trans _ ?_ _ none ?_ ?_ ?_
          · rfl
          · intro k
            exact Or.inr ⟨fun h => (nomatch h), rfl⟩
          · intro k
            obtain ⟨ps, c, dk, ups, uc⟩ := inv.families k
            exact ⟨ps, c, c, dk, dk, ups, uc, S.levels.cumulative_refl uc⟩
          · intro e' member w
            obtain ⟨fx, fy⟩ := restFixed e' member w
            exact ⟨⟨fun h => (nomatch h), fx⟩, fun Y memberY => ⟨fun h => (nomatch h), fy Y memberY⟩⟩
        · rw [dif_neg hdel] at progressed
          by_cases hocc : (viewOfArrow hd).X ∈ domainVars e.2.2.code
          · rw [dif_pos hocc] at progressed
            cases progressed
          · rw [dif_neg hocc] at progressed
            split at progressed
            · cases progressed
            · by_cases hok : glbSolvableB choices glb (viewOfArrow hd) = true
              · rw [dif_pos hok] at progressed
                cases progressed
                refine inv.step algebra.trans _ ?_ _ (some (viewOfArrow hd).X) ?_ ?_ ?_
                · rfl
                · intro k
                  by_cases hk : k = (viewOfArrow hd).X
                  · subst hk
                    refine Or.inl ⟨rfl, fun x member => ?_⟩
                    change x ∈ (solveSub (viewOfArrow hd).X e.2.2.code (viewOfArrow hd).X).support at member
                    rw [solveSub_self] at member
                    have inT := arrow_support (viewOfArrow hd).arrow member
                    refine ⟨fun same => hocc ?_, here.2 x inT⟩
                    have xX : x = (viewOfArrow hd).X := (Option.some.inj same).symm
                    rw [← xX]
                    exact inT
                  · exact Or.inr ⟨fun same => hk (Option.some.inj same).symm, solveSub_ne _ hk⟩
                · intro k
                  obtain ⟨w, hw, uw⟩ := (glbSolvable_of_B choices glb (viewOfArrow hd) hok hocc).universes k
                  cases found : glbTarget (S := S) glb Θ.raw (viewOfArrow hd).u e.2.2.code k with
                  | none =>
                      exact ⟨[], w, w, (lookup_lowerTo_none Θ.raw _ k found).trans hw, hw,
                        (fun _ member => nomatch member), uw, S.levels.cumulative_refl uw⟩
                  | some g =>
                      obtain ⟨w', hw', below⟩ := glbTarget_lowerable glb spec k g found
                      have ww : w' = w := Tm.head.inj (hw'.symm.trans hw)
                      rw [ww] at below
                      exact ⟨[], g, w, lookup_lowerTo_some Θ.raw _ k found, hw, (fun _ member => nomatch member),
                        glbTarget_universe glb spec k g found, below⟩
                · intro e' member w
                  obtain ⟨e₁, inRest, rfl⟩ := List.mem_map.mp member
                  obtain ⟨w₁⟩ := inside.shapes e₁ (List.mem_cons_of_mem _ inRest)
                  have distinct := (List.pairwise_cons.mp inside.distinct).1 e₁ inRest (viewOfArrow hd) w₁
                  obtain ⟨t, tX⟩ := glbNarrowSolve_view glb spec algebra (viewOfArrow hd)
                    (glbSolvable_of_B choices glb (viewOfArrow hd) hok hocc) w₁ (fun same => distinct same.symm)
                  have wX : w.X = w₁.X := (FlexArrow.unique w t).trans tX
                  obtain ⟨fx, fy⟩ := restFixed e₁ inRest w₁
                  refine ⟨⟨fun same => distinct ((Option.some.inj same).trans wX), ?_⟩, fun Y memberY => ?_⟩
                  · change σ.substitution (Fin.cast inv.same w.X) = .var w.X
                    rw [wX]
                    exact fx
                  · rcases domainVars_subst_solve (X := (viewOfArrow hd).X) (t := e.2.2.code) w₁.arrow Y memberY with
                      ⟨inE, ne⟩ | inT
                    · exact ⟨fun same => ne (Option.some.inj same).symm, fy Y inE⟩
                    · refine ⟨fun same => hocc ?_, here.2 Y inT⟩
                      have YX : Y = (viewOfArrow hd).X := (Option.some.inj same).symm
                      rw [← YX]
                      exact inT
              · rw [dif_neg hok] at progressed
                cases progressed
      · cases progressed

/-- **The driver keeps the shape** on the fragment without the chain. -/
theorem driveFR_inPlace {Γ : Context S.R} {original : EquationStore (TotalTerm Γ)} (fuel : Nat) :
    ∀ (state : Update S.levels original), InPlaceFR state.answer state.remaining →
      InFlexRigidGlb choices state.remaining → ∀ (final : Update S.levels original) (finished : final.remaining = []),
        drive (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique) fuel
          state = .solved final finished → InPlaceFR final.answer final.remaining := by
  induction fuel with
  | zero =>
      intro state _ _ final finished h
      cases h
  | succ fuel ih =>
      intro state inv inside final finished h
      rw [drive] at h
      cases ha : advance (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete
          headTypingUnique) state with
      | done outcome =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
            cases h
            exact inv
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
              have inv' := flexRigidGlbRound_inPlace choices glb spec facts roots heads algebra rigid complete
                headTypingUnique inv inside hround
              have inside' := flexRigidGlbRound_stable choices glb spec facts roots heads algebra rigid complete
                headTypingUnique inside hround
              exact ih (state.then update) inv' inside' final finished h
            · cases ha
            · cases ha

include facts roots heads algebra rigid complete headTypingUnique spec in
/-- **Every solved run of the flex-rigid solver without the chain, trimmed, is the initial solution.** -/
theorem flexRigidGlb_solved_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexRigidGlb choices original) (inh : Miller.Inhabitants S.R)
    (families : ∀ j : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw j = famCode ps c ∧
      AllUniverses S.R ps ∧ S.R.isUniverse c)
    {fuel : Nat} {state : Update S.levels original} {finished : state.remaining = []}
    (solved : run (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique)
      original fuel = .solved state finished) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  have shape := driveFR_inPlace choices glb spec facts roots heads algebra rigid complete headTypingUnique fuel
    (Update.pending S.levels original) (InPlaceFR.pending original families) inside state finished solved
  choose ps c hd hu huc using shape.families
  refine ⟨_, _, initial_of_trimmed facts roots heads algebra rigid complete inh (state.completed finished) shape.same
    (fun j => (ps j, c j)) hd (fun j => ⟨hu j, huc j⟩) shape.fixedSupport ?_⟩
  intro j fixed
  obtain ⟨ps', c₁, c', d₁, dΓ, uc', le⟩ := shape.lowered j fixed
  obtain ⟨hps, hc⟩ := famCode_inj ((hd j).symm.trans d₁)
  refine ⟨c', ?_, uc', ?_⟩
  · rw [dΓ, ← hps]
  · rw [hc]
    exact le

include facts roots heads algebra rigid complete headTypingUnique spec in
/-- **Flex-rigid stores without the chain: an initial solution, or none at all.** -/
theorem flexRigidGlb_initial_or_refuted {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexRigidGlb choices original) (inh : Miller.Inhabitants S.R)
    (families : ∀ j : Fin Θ.arity, ∃ (ps : List Head) (c : Head), Ctx.lookup Θ.raw j = famCode ps c ∧
      AllUniverses S.R ps ∧ S.R.isUniverse c)
    (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g) :
    (∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer) ∨
      ¬ (frames S.levels).Solvable original := by
  obtain ⟨fuel, ends⟩ := flexRigidGlb_decided choices glb spec facts roots heads algebra rigid complete
    headTypingUnique total inside
  rcases (ends fuel le_rfl).2 with ⟨state, finished, solved, _⟩ | ⟨absent, _⟩
  · exact Or.inl (flexRigidGlb_solved_initial choices glb spec facts roots heads algebra rigid complete
      headTypingUnique inside inh families solved)
  · exact Or.inr absent

end Round

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
