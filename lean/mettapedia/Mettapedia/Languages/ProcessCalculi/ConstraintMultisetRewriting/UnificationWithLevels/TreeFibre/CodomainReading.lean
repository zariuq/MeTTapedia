import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyNeutral

/-!
# Arrow codes with codomains: reading them, refuting them, instantiating them

* **Reading** (`arrowCodB`, `arrowCod_of_B`, `arrowCodB_of_arrowCod`): a code is read as an arrow code with codomains
  by strengthening each codomain past its binder (`strengthenCode`); the reading is sound and complete.
  `readFlexCod` reads a flex–rigid equation of such a code (`readFlexCod_complete`).
* **The occurs check** (`within_of_support`, `cod_occurs_refutes`): an unknown of its own code, other than the code
  itself, occurs along domains and codomains (`Within`), and the tree's full occurs check refutes the equation.
* **A misfit head refutes** (`arrowCod_misfit`, `cod_misfitHead_refutes`): a head typed by no universe below `u`, at a
  domain or at a codomain, leaves no type of `U_u` equal to an instance of the code. Under a codomain the instance is
  read over the domain with the substitution weakened; no strengthening is needed.
* **Instantiation** (`arrowCod_subst_solve`, `codHeads_subst_solve`): `X := t` keeps arrow codes with codomains, and
  brings only the heads of `t`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentUniverseInjective
open ContextualDependentOccursFull

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Reading -/

section Reading

/-- **Whether a code is an arrow code with codomains**: every codomain is strengthened past its binder. -/
def arrowCodB : {n : Nat} → Tm Head n → Bool
  | _, .var _ => true
  | _, .head _ => true
  | _, .pi A B =>
      arrowCodB A &&
        match ContextualDependentInPlace.strengthenCode B with
        | some B₀ => arrowCodB B₀.1
        | none => false
  | _, .const _ => false
  | _, .sigma _ _ => false
  | _, .id _ _ _ => false
  | _, .lam _ => false
  | _, .app _ _ => false
  | _, .pair _ _ => false
  | _, .fst _ => false
  | _, .snd _ => false
  | _, .refl _ => false
termination_by _ t => ContextualDependentOccursCheck.nodes t
decreasing_by
  · simp only [ContextualDependentOccursCheck.nodes]
    omega
  · have same := congrArg ContextualDependentOccursCheck.nodes B₀.2
    rw [nodes_rename] at same
    simp only [ContextualDependentOccursCheck.nodes]
    omega

/-- **The reading is sound.** -/
theorem arrowCod_of_B : ∀ (k : Nat) {n : Nat} (t : Tm Head n), ContextualDependentOccursCheck.nodes t ≤ k →
    arrowCodB t = true → ArrowCod t := by
  intro k
  induction k with
  | zero =>
      intro n t size _
      cases t <;> simp [ContextualDependentOccursCheck.nodes] at size
  | succ k ih =>
      intro n t size found
      cases t with
      | var Y => exact .var Y
      | head h => exact .head h
      | pi A B =>
          rw [arrowCodB] at found
          simp only [Bool.and_eq_true] at found
          obtain ⟨foundA, foundB⟩ := found
          simp only [ContextualDependentOccursCheck.nodes] at size
          have codeA := ih A (by omega) foundA
          split at foundB
          · rename_i B₀ _
            have same := congrArg ContextualDependentOccursCheck.nodes B₀.2
            rw [nodes_rename] at same
            have codeB := ih B₀.1 (by omega) foundB
            have code := ArrowCod.pi codeA codeB
            rw [B₀.2] at code
            exact code
          · cases foundB
      | const _ => simp [arrowCodB] at found
      | sigma _ _ => simp [arrowCodB] at found
      | id _ _ _ => simp [arrowCodB] at found
      | lam _ => simp [arrowCodB] at found
      | app _ _ => simp [arrowCodB] at found
      | pair _ _ => simp [arrowCodB] at found
      | fst _ => simp [arrowCodB] at found
      | snd _ => simp [arrowCodB] at found
      | refl _ => simp [arrowCodB] at found

/-- **The reading is complete.** -/
theorem arrowCodB_of_arrowCod {n : Nat} {t : Tm Head n} (code : ArrowCod t) : arrowCodB t = true := by
  induction code with
  | var Y => rw [arrowCodB]
  | head h => rw [arrowCodB]
  | @pi A B _ _ ihA ihB =>
      rw [arrowCodB]
      simp only [Bool.and_eq_true]
      refine ⟨ihA, ?_⟩
      have strong := ContextualDependentSpinesMany.strengthenCode_rename B
      split
      · rename_i B₀ found
        rw [found] at strong
        simp only [Option.map_some, Option.some.injEq] at strong
        rw [strong]
        exact ihB
      · rename_i found
        rw [found] at strong
        cases strong

variable {S : Setting Head L} [DecidableEq Head]

/-- **Read a flex–rigid equation of a universe unknown and an arrow code with codomains.** -/
def readFlexCod {Θ : Context S.R} [∀ head, Decidable (S.R.isUniverse head)] (e : Equation (TotalTerm Θ)) :
    Option (FlexArrowData Head Θ.arity) :=
  (headOf e.1.1.code).bind fun v =>
  (varOf e.1.2.code).bind fun X =>
  (declaredUniverse Θ.raw X).bind fun u =>
  if e.2.1.code = .head v ∧ S.R.isUniverse u ∧ S.R.isUniverse v ∧ arrowCodB e.2.2.code = true then some ⟨v, X, u⟩
  else none

variable [∀ head, Decidable (S.R.isUniverse head)]

theorem readFlexCod_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexArrowData Head Θ.arity}
    (h : readFlexCod e = some d) :
    e.1.1.code = .head d.v ∧ e.1.2.code = .var d.X ∧ Ctx.lookup Θ.raw d.X = .head d.u ∧ e.2.1.code = .head d.v ∧
      S.R.isUniverse d.u ∧ S.R.isUniverse d.v ∧ ArrowCod e.2.2.code := by
  unfold readFlexCod at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, X, hX, u, hu, h⟩ := h
  split_ifs at h with hc
  cases h
  exact ⟨headOf_sound hv, varOf_sound hX, headOf_sound hu, hc.1, hc.2.1, hc.2.2.1,
    arrowCod_of_B _ _ le_rfl hc.2.2.2⟩

/-- The view of a successful reading. -/
def viewOfCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexArrowData Head Θ.arity}
    (h : readFlexCod e = some d) : FlexCod e where
  v := d.v
  X := d.X
  u := d.u
  annotation_left := (readFlexCod_sound h).1
  annotation_right := (readFlexCod_sound h).2.2.2.1
  side_left := (readFlexCod_sound h).2.1
  declared := (readFlexCod_sound h).2.2.1
  universe_u := (readFlexCod_sound h).2.2.2.2.1
  universe_v := (readFlexCod_sound h).2.2.2.2.2.1
  code := (readFlexCod_sound h).2.2.2.2.2.2

/-- **The reader reads every flex–rigid equation with codomains.** -/
theorem readFlexCod_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) :
    readFlexCod e = some ⟨v.v, v.X, v.u⟩ := by
  unfold readFlexCod
  rw [v.annotation_left, v.side_left]
  simp [headOf, varOf, declaredUniverse, v.declared, v.annotation_right, v.universe_u, v.universe_v,
    arrowCodB_of_arrowCod v.code]

end Reading

/-- **The reading of an equation is unique.** -/
theorem FlexCod.unique {S : Setting Head L} {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v w : FlexCod e) :
    v.X = w.X :=
  Tm.var.inj (v.side_left.symm.trans w.side_left)

/-! ## Instantiation -/

section Instantiation

/-- `X := t` keeps arrow codes with codomains. -/
theorem arrowCod_subst_solve {n : Nat} {X : Fin n} {t : Tm Head n} (codeT : ArrowCod t) :
    ∀ {s : Tm Head n}, ArrowCod s → ArrowCod (Presentation.subst (solveSub X t) s) := by
  intro s code
  induction code with
  | var Y =>
      change ArrowCod (solveSub X t Y)
      by_cases h : Y = X
      · rw [h, solveSub_self]
        exact codeT
      · rw [solveSub_ne t h]
        exact .var Y
  | head h => exact .head h
  | @pi A B _ _ ihA ihB =>
      change ArrowCod (.pi (Presentation.subst (solveSub X t) A)
        (Presentation.subst (liftSub (solveSub X t)) (Presentation.rename wk B)))
      rw [subst_liftSub_wk]
      exact .pi ihA ihB

/-- The heads of an instance are heads of the code or of `t`. -/
theorem codHeads_subst_solve {n : Nat} {X : Fin n} {t : Tm Head n} :
    ∀ {s : Tm Head n}, ArrowCod s → ∀ h ∈ codHeads (Presentation.subst (solveSub X t) s),
      h ∈ codHeads s ∨ h ∈ codHeads t := by
  intro s code
  induction code with
  | var Y =>
      intro h member
      change h ∈ codHeads (solveSub X t Y) at member
      by_cases same : Y = X
      · rw [same, solveSub_self] at member
        exact .inr member
      · rw [solveSub_ne t same] at member
        cases member
  | head h => intro h' member; exact .inl member
  | @pi A B _ _ ihA ihB =>
      intro h member
      change h ∈ codHeads (.pi (Presentation.subst (solveSub X t) A)
        (Presentation.subst (liftSub (solveSub X t)) (Presentation.rename wk B))) at member
      rw [subst_liftSub_wk] at member
      simp only [codHeads, codHeads_rename, List.mem_append] at member
      simp only [codHeads, codHeads_rename, List.mem_append]
      rcases member with inA | inB
      · rcases ihA h inA with left | right
        · exact .inl (.inl left)
        · exact .inr right
      · rcases ihB h inB with left | right
        · exact .inl (.inr left)
        · exact .inr right

end Instantiation

/-! ## Refutations -/

section Refutations

/-- **An unknown of its own code occurs in it along domains and codomains**, unless it is the code. -/
theorem within_of_support {n : Nat} {X : Fin n} {t : Tm Head n} (code : ArrowCod t) (member : X ∈ t.support) :
    t = .var X ∨ Within true (.var X) t := by
  induction code with
  | var Y =>
      have same : X = Y := by simpa [Tm.support] using member
      exact .inl (by rw [same])
  | head h => simp [Tm.support] at member
  | @pi A B _ _ ihA ihB =>
      right
      simp only [Tm.support, Finset.mem_union, mem_outerSupport] at member
      rcases member with inA | inB
      · rcases ihA inA with same | within
        · rw [same]
          exact .domain true (.here _)
        · exact .domain true within
      · rw [ContextualDependentSupport.support_rename, Finset.mem_image] at inB
        obtain ⟨a, ha, same⟩ := inB
        have aX : a = X := Fin.succ_injective _ same
        rw [aX] at ha
        rcases ihB ha with sameB | within
        · rw [sameB]
          exact .codomain true (.here _)
        · have moved := within.subst (renSub wk)
          rw [subst_renSub, subst_renSub] at moved
          exact .codomain true moved

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The occurs check, codomains included**: `X ≐ t` with `X` in `t`, `t` not `X`, has no solution. -/
theorem cod_occurs_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e)
    (member : v.X ∈ e.2.2.code.support) (ne : e.2.2.code ≠ .var v.X) (rest : EquationStore (TotalTerm Θ)) :
    ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  rcases within_of_support v.code member with same | within
  · exact ne same
  · rw [← v.side_left] at within
    exact OccursFullShape.refutes facts roots heads algebra rigid complete
      ⟨v.v, v.universe_v, v.annotation_left, v.annotation_right, within⟩ σ (models e List.mem_cons_self)

include facts roots heads algebra rigid complete in
/-- **A misfit head refutes**, at a domain or at a codomain. -/
theorem arrowCod_misfit {u h₀ : Head} (hu : S.R.isUniverse u)
    (apart : ∀ k, S.R.headTyping h₀ k → ¬ S.R.cumulative k u) :
    ∀ {n : Nat} {t : Tm Head n}, ArrowCod t → h₀ ∈ codHeads t → ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ →
      ∀ (σ : Sub Head n m) {s : Tm Head m}, Typed S.R Δ s (.head u) → ¬ TypeEq S.R Δ s (Presentation.subst σ t) := by
  intro n t code
  induction code with
  | var Y => intro member; cases member
  | head h =>
      intro member m Δ formed σ s ts
      have same : h₀ = h := List.mem_singleton.mp member
      subst same
      exact sort_not_small facts roots heads algebra rigid complete formed hu apart ts
  | @pi A B _ _ ihA ihB =>
      intro member m Δ formed σ s ts equal
      change TypeEq S.R Δ s (.pi (Presentation.subst σ A)
        (Presentation.subst (liftSub σ) (Presentation.rename wk B))) at equal
      rw [subst_liftSub_wk] at equal
      obtain ⟨A', B', tA', eA', tB', eB'⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      simp only [codHeads, codHeads_rename, List.mem_append] at member
      rcases member with inA | inB
      · exact ihA inA formed σ tA' eA'
      · have formedA' : CtxFormed S.R (.snoc Δ A') := formed.snoc ⟨u, hu, tA'⟩
        have moved : Presentation.rename wk (Presentation.subst σ B) =
            Presentation.subst (fun i => Presentation.rename wk (σ i)) B := by
          rw [← subst_renSub, subst_comp]
          congr 1
          funext i
          exact subst_renSub wk (σ i)
        rw [moved] at eB'
        exact ihB inB formedA' _ tB' eB'

include facts roots heads algebra rigid complete in
/-- **A misfit head refutes** `X ≐ t`. -/
theorem cod_misfitHead_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) {h₀ : Head}
    (member : h₀ ∈ codHeads e.2.2.code) (apart : ∀ k, S.R.headTyping h₀ k → ¬ S.R.cumulative k v.u)
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := ((equivalent_iff S.levels _ _).mp (models e List.mem_cons_self)).2
  change Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code)
    (Presentation.subst σ.substitution e.2.2.code) (Presentation.subst σ.substitution e.1.1.code) at equal
  rw [v.side_left, v.annotation_left] at equal
  have tX : Typed S.R Δ.raw (σ.substitution v.X) (.head v.u) := by
    have typed := σ.typed v.X
    rw [v.declared] at typed
    exact typed
  exact arrowCod_misfit facts roots heads algebra rigid complete v.universe_u apart v.code member Δ.formed
    σ.substitution tX ⟨v.v, v.universe_v, equal⟩

end Refutations

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
