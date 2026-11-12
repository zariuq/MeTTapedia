import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainForcing

/-!
# Flex–rigid equations with unknowns at codomain positions: narrowing to greatest lower bounds and solving, exact

**Arrow codes with codomains** (`ArrowCod`): an unknown, a head, or `Π (_ : A). B` with `A` and `B` again such codes and
`B` not using the argument. The first-order arrow codes of `FlexRigid` are the case where every codomain is a head
(`arrowCod_of_arrow`).

* **Every unknown of such a code sits at a type position** (`holdsAt_of_support`), domains and codomains alike.
* **Such codes are normal** (`PiCode.normal`): built from variables, heads and Π types, they have no step.
* **Typing** (`arrowCod_typed`): a type of `U_u` when its unknowns are declared at universes below `u` and its heads
  are typed by universes below `u`.
* **What the equation forces** (`cod_misfit_forced`): every solution of `X ≐ t` sends every unknown of `t` declared
  above `X`'s universe to a type equal to one of the greatest lower bound; the codomain positions through
  `HoldsAt.small`.
* **The rule** (`codNarrowSolveUpdate`, `codNarrowSolve_exact`): the misfit unknowns declared again at their greatest
  lower bounds with `U_u`, and `X := t`; exact.
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
open ContextualDependentNormalChecking

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Codes -/

section Codes

/-- **An arrow code with codomains**: an unknown, a head, or `Π (_ : A). B` with `B` not using the argument. -/
inductive ArrowCod {n : Nat} : Tm Head n → Prop
  | var (Y : Fin n) : ArrowCod (.var Y)
  | head (h : Head) : ArrowCod (.head h)
  | pi {A B : Tm Head n} : ArrowCod A → ArrowCod B → ArrowCod (.pi A (Presentation.rename wk B))

/-- The first-order arrow codes are arrow codes with codomains. -/
theorem arrowCod_of_arrow {n : Nat} {t : Tm Head n} (arrow : Arrow t) : ArrowCod t := by
  induction arrow with
  | var Y => exact .var Y
  | head h => exact .head h
  | @pi A h _ ih => exact ArrowCod.pi (B := .head h) ih (.head h)

/-- **Built from variables, heads and Π types.** -/
inductive PiCode : {n : Nat} → Tm Head n → Prop
  | var {n : Nat} (Y : Fin n) : PiCode (.var Y)
  | head {n : Nat} (h : Head) : PiCode (n := n) (.head h)
  | pi {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} : PiCode A → PiCode B → PiCode (.pi A B)

theorem PiCode.rename {n : Nat} {t : Tm Head n} (code : PiCode t) :
    ∀ {m : Nat} (ρ : Ren n m), PiCode (Presentation.rename ρ t) := by
  induction code with
  | var Y => intro m ρ; exact .var (ρ Y)
  | head h => intro m ρ; exact .head h
  | pi _ _ ihA ihB => intro m ρ; exact .pi (ihA ρ) (ihB (liftRen ρ))

theorem piCode_of_arrowCod {n : Nat} {t : Tm Head n} (code : ArrowCod t) : PiCode t := by
  induction code with
  | var Y => exact .var Y
  | head h => exact .head h
  | pi _ _ ihA ihB => exact .pi ihA (ihB.rename wk)

/-- The heads of an arrow code with codomains. -/
def codHeads : {n : Nat} → Tm Head n → List Head
  | _, .head h => [h]
  | _, .pi A B => codHeads A ++ codHeads B
  | _, _ => []

theorem codHeads_rename {n : Nat} (t : Tm Head n) :
    ∀ {m : Nat} (ρ : Ren n m), codHeads (Presentation.rename ρ t) = codHeads t := by
  induction t with
  | var _ => intro m ρ; rfl
  | const _ => intro m ρ; rfl
  | head _ => intro m ρ; rfl
  | pi A B ihA ihB => intro m ρ; simp only [Presentation.rename, codHeads, ihA, ihB]
  | sigma _ _ _ _ => intro m ρ; rfl
  | id _ _ _ _ _ _ => intro m ρ; rfl
  | lam _ _ => intro m ρ; rfl
  | app _ _ _ _ => intro m ρ; rfl
  | pair _ _ _ _ => intro m ρ; rfl
  | fst _ _ => intro m ρ; rfl
  | snd _ _ => intro m ρ; rfl
  | refl _ _ => intro m ρ; rfl

/-- **Every unknown of an arrow code with codomains sits at a type position.** -/
theorem holdsAt_of_support {n : Nat} {t : Tm Head n} (code : ArrowCod t) :
    ∀ {Y : Fin n}, Y ∈ t.support → HoldsAt Y t := by
  induction code with
  | var Y =>
      intro Y' member
      have same : Y' = Y := by simpa [Tm.support] using member
      rw [same]
      exact .here
  | head h =>
      intro Y member
      simp [Tm.support] at member
  | @pi A B _ _ ihA ihB =>
      intro Y member
      simp only [Tm.support, Finset.mem_union, mem_outerSupport] at member
      rcases member with inA | inB
      · exact .piDomain (ihA inA)
      · rw [ContextualDependentSupport.support_rename, Finset.mem_image] at inB
        obtain ⟨a, ha, same⟩ := inB
        have aY : a = Y := Fin.succ_injective _ same
        rw [← aY]
        exact .piCodomain (ihB ha)

/-- `X := t` leaves a code without `X` as it is. -/
theorem subst_solveSub_absent {n : Nat} {X : Fin n} (t : Tm Head n) :
    ∀ {s : Tm Head n}, ArrowCod s → X ∉ s.support → Presentation.subst (solveSub X t) s = s := by
  intro s code
  induction code with
  | var Y =>
      intro absent
      have ne : Y ≠ X := fun same => absent (by rw [same]; simp [Tm.support])
      change solveSub X t Y = .var Y
      exact solveSub_ne t ne
  | head h => intro _; rfl
  | @pi A B _ _ ihA ihB =>
      intro absent
      simp only [Tm.support, Finset.mem_union, mem_outerSupport, not_or] at absent
      have absentB : X ∉ B.support := by
        intro inB
        apply absent.2
        rw [ContextualDependentSupport.support_rename, Finset.mem_image]
        exact ⟨X, inB, rfl⟩
      change Tm.pi (Presentation.subst (solveSub X t) A)
        (Presentation.subst (liftSub (solveSub X t)) (Presentation.rename wk B)) = _
      rw [subst_liftSub_wk, ihA absent.1, ihB absentB]

/-- Substitutions agreeing on the unknowns under a binder agree after lifting. -/
theorem liftSub_agree {n m : Nat} {σ σ' : Sub Head n m} {B : Tm Head (n + 1)}
    (agree : ∀ i, i.succ ∈ B.support → σ i = σ' i) : ∀ j ∈ B.support, liftSub σ j = liftSub σ' j := by
  intro j member
  cases j using Fin.cases with
  | zero => rfl
  | succ k =>
      show Presentation.rename wk (σ k) = Presentation.rename wk (σ' k)
      rw [agree k member]

/-- **Substitutions agreeing on the unknowns of a term give the same instance.** -/
theorem subst_congr_support {n : Nat} (t : Tm Head n) :
    ∀ {m : Nat} {σ σ' : Sub Head n m}, (∀ i ∈ t.support, σ i = σ' i) →
      Presentation.subst σ t = Presentation.subst σ' t := by
  induction t with
  | var i => intro m σ σ' agree; exact agree i (Finset.mem_singleton_self i)
  | const _ => intro _ _ _ _; rfl
  | head _ => intro _ _ _ _; rfl
  | pi A B ihA ihB =>
      intro m σ σ' agree
      show Tm.pi _ _ = Tm.pi _ _
      rw [ihA fun i hi => agree i (Finset.mem_union_left _ hi),
        ihB (liftSub_agree fun i hi => agree i (Finset.mem_union_right _ (mem_outerSupport.mpr hi)))]
  | sigma A B ihA ihB =>
      intro m σ σ' agree
      show Tm.sigma _ _ = Tm.sigma _ _
      rw [ihA fun i hi => agree i (Finset.mem_union_left _ hi),
        ihB (liftSub_agree fun i hi => agree i (Finset.mem_union_right _ (mem_outerSupport.mpr hi)))]
  | id C a b ihC iha ihb =>
      intro m σ σ' agree
      show Tm.id _ _ _ = Tm.id _ _ _
      rw [ihC fun i hi => agree i (Finset.mem_union_left _ (Finset.mem_union_left _ hi)),
        iha fun i hi => agree i (Finset.mem_union_left _ (Finset.mem_union_right _ hi)),
        ihb fun i hi => agree i (Finset.mem_union_right _ hi)]
  | lam body ih =>
      intro m σ σ' agree
      show Tm.lam _ = Tm.lam _
      rw [ih (liftSub_agree fun i hi => agree i (mem_outerSupport.mpr hi))]
  | app f a ihf iha =>
      intro m σ σ' agree
      show Tm.app _ _ = Tm.app _ _
      rw [ihf fun i hi => agree i (Finset.mem_union_left _ hi), iha fun i hi => agree i (Finset.mem_union_right _ hi)]
  | pair f a ihf iha =>
      intro m σ σ' agree
      show Tm.pair _ _ = Tm.pair _ _
      rw [ihf fun i hi => agree i (Finset.mem_union_left _ hi), iha fun i hi => agree i (Finset.mem_union_right _ hi)]
  | fst p ih => intro m σ σ' agree; show Tm.fst _ = Tm.fst _; rw [ih agree]
  | snd p ih => intro m σ σ' agree; show Tm.snd _ = Tm.snd _; rw [ih agree]
  | refl p ih => intro m σ σ' agree; show Tm.refl _ = Tm.refl _; rw [ih agree]

/-- **`X := t` leaves every term without `X` as it is**, whatever its shape. -/
theorem subst_solveSub_fresh {n : Nat} {X : Fin n} (t : Tm Head n) {D : Tm Head n} (absent : X ∉ D.support) :
    Presentation.subst (solveSub X t) D = D := by
  have agree : ∀ i ∈ D.support, solveSub X t i = ids i := by
    intro i member
    have ne : i ≠ X := by
      rintro rfl
      exact absent member
    exact solveSub_ne t ne
  rw [subst_congr_support D agree, subst_ids]

end Codes

/-! ## Normal codes -/

section Normal

variable {S : Setting Head L} (rigid : ∀ name, S.roles name = .rigid)

include rigid in
/-- **Codes built from variables, heads and Π types are normal.** -/
theorem PiCode.normal {n : Nat} {t : Tm Head n} (code : PiCode t) : Normal (S := S) t := by
  induction code with
  | var Y =>
      intro target step
      cases step with
      | root r => exact no_root_step rigid r
  | head h =>
      intro target step
      cases step with
      | root r => exact no_root_step rigid r
      | head h => exact h
  | pi _ _ ihA ihB =>
      intro target step
      cases step with
      | root r => exact no_root_step rigid r
      | congPiDom s => exact ihA _ s
      | congPiCod s => exact ihB _ s

end Normal

/-! ## Typing -/

section Typing

variable {S : Setting Head L}

/-- **An arrow code with codomains is a type of `U_u`** when its unknowns are declared at universes below `u` and its
heads are typed by universes below `u`. -/
theorem arrowCod_typed (algebra : CumulativeAlgebra S.R) {u : Head} (hu : S.R.isUniverse u) :
    ∀ {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}, ArrowCod t → CtxFormed S.R Γ →
      (∀ Y ∈ t.support, ∃ w, Ctx.lookup Γ Y = .head w ∧ S.R.cumulative w u) →
      (∀ h ∈ codHeads t, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k u) →
      Typed S.R Γ t (.head u) := by
  intro n Γ t code
  induction code with
  | var Y =>
      intro _ vars _
      obtain ⟨w, hw, c⟩ := vars Y (by simp [Tm.support])
      have typed := Derivable.var (R := S.R) (Γ := Γ) Y
      rw [hw] at typed
      exact Derivable.cumul typed c
  | head h =>
      intro _ _ heads
      obtain ⟨k, typing, c⟩ := heads h (List.mem_singleton_self h)
      exact Derivable.cumul (Derivable.headType typing) c
  | @pi A B _ _ ihA ihB =>
      intro formed vars heads
      have tA : Typed S.R Γ A (.head u) :=
        ihA formed (fun Y member => vars Y (by simp only [Tm.support, Finset.mem_union]; exact .inl member))
          (fun h member => heads h (by simp only [codHeads]; exact List.mem_append_left _ member))
      have tB : Typed S.R Γ B (.head u) :=
        ihB formed (fun Y member => vars Y (by
            simp only [Tm.support, Finset.mem_union, mem_outerSupport]
            refine .inr ?_
            rw [ContextualDependentSupport.support_rename, Finset.mem_image]
            exact ⟨Y, member, rfl⟩))
          (fun h member => heads h (by
            simp only [codHeads, codHeads_rename]
            exact List.mem_append_right _ member))
      have isA : IsType S.R Γ A := ⟨u, hu, tA⟩
      have tB' : Typed S.R (.snoc Γ A) (Presentation.rename wk B) (.head u) := tB.rename (CtxRen.wk Γ A)
      obtain ⟨w', join'⟩ := S.levels.join_exists hu hu
      have _ := isA
      exact Derivable.cumul (Derivable.piForm tA hu tB' hu join')
        (algebra.join_least join' (S.levels.cumulative_refl hu) (S.levels.cumulative_refl hu))

end Typing

/-! ## The rule -/

section Rule

variable {S : Setting Head L}

/-- **A flex–rigid equation with codomains**: `X ≐ t` at `U_v`, `X : U_u`, `t` an arrow code with codomains. -/
structure FlexCod {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  v : Head
  X : Fin Θ.arity
  u : Head
  annotation_left : e.1.1.code = .head v
  annotation_right : e.2.1.code = .head v
  side_left : e.1.2.code = .var X
  declared : Ctx.lookup Θ.raw X = .head u
  universe_u : S.R.isUniverse u
  universe_v : S.R.isUniverse v
  code : ArrowCod e.2.2.code

variable [DecidableRel S.R.cumulative]

/-- The unknowns of `t` declared at universes not below `u`. -/
def codMisfit {n : Nat} (Γ : Ctx Head n) (u : Head) (t : Tm Head n) : Fin n → Bool :=
  fun i => decide (i ∈ t.support) &&
    match declaredUniverse Γ i with
    | some w => !decide (S.R.cumulative w u)
    | none => false

theorem codMisfit_mem {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n}
    (h : codMisfit (S := S) Γ u t i = true) : i ∈ t.support := by
  unfold codMisfit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem codMisfit_out {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n} {w : Head}
    (declared : Ctx.lookup Γ i = .head w) (h : codMisfit (S := S) Γ u t i = false) (member : i ∈ t.support) :
    S.R.cumulative w u := by
  unfold codMisfit declaredUniverse at h
  rw [declared] at h
  simp only [headOf, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_false,
    decide_eq_true_eq] at h
  rcases h with absent | below
  · exact absurd member absent
  · exact below

variable (glb : Head → Head → Option Head)

/-- **The target of each unknown**: a misfit unknown, declared at `U_w`, goes to `glb u w`. -/
def codTarget {n : Nat} (Γ : Ctx Head n) (u : Head) (t : Tm Head n) (i : Fin n) : Option Head :=
  if codMisfit (S := S) Γ u t i = true then (declaredUniverse Γ i).bind (glb u) else none

theorem codTarget_some {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n} {g : Head}
    (found : codTarget (S := S) glb Γ u t i = some g) :
    codMisfit (S := S) Γ u t i = true ∧ ∃ w, Ctx.lookup Γ i = .head w ∧ glb u w = some g := by
  unfold codTarget at found
  by_cases misfit : codMisfit (S := S) Γ u t i = true
  · rw [if_pos misfit] at found
    refine ⟨misfit, ?_⟩
    cases hd : declaredUniverse Γ i with
    | none => rw [hd] at found; cases found
    | some w =>
        rw [hd] at found
        exact ⟨w, headOf_sound hd, found⟩
  · rw [if_neg misfit] at found
    cases found

theorem codTarget_none_of_fit {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n}
    (fit : codMisfit (S := S) Γ u t i = false) : codTarget (S := S) glb Γ u t i = none := by
  unfold codTarget
  rw [if_neg (by rw [fit]; decide)]

theorem codTarget_of_misfit {n : Nat} {Γ : Ctx Head n} {u w g : Head} {t : Tm Head n} {i : Fin n}
    (misfit : codMisfit (S := S) Γ u t i = true) (declared : Ctx.lookup Γ i = .head w) (found : glb u w = some g) :
    codTarget (S := S) glb Γ u t i = some g := by
  unfold codTarget declaredUniverse
  rw [if_pos misfit, declared]
  exact found

/-- **The conditions of the rule**: no occurrence of `X`, heads typed below `u`, the unknowns of `t` declared at
universes, no declaration mentioning `X` or an unknown of `t`, and a greatest lower bound with `u` for every misfit
unknown. -/
structure CodSolvable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) : Prop where
  absent : v.X ∉ e.2.2.code.support
  heads : ∀ h ∈ codHeads e.2.2.code, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k v.u
  occurring : ∀ Y ∈ e.2.2.code.support, ∃ w, Ctx.lookup Θ.raw Y = .head w ∧ S.R.isUniverse w
  apart : ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, j ≠ v.X ∧ j ∉ e.2.2.code.support
  meets : ∀ i, codMisfit (S := S) Θ.raw v.u e.2.2.code i = true → ∀ w, Ctx.lookup Θ.raw i = .head w →
    ∃ g, glb v.u w = some g

omit [DecidableRel S.R.cumulative] in
/-- Declarations at universes mention no unknown. -/
theorem apart_of_universes {Θ : Context S.R} (universes : AllUniverseDecls Θ) {P : Fin Θ.arity → Prop} :
    ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, P j := by
  intro i j member
  obtain ⟨w, hw, _⟩ := universes i
  rw [hw] at member
  simp [Tm.support] at member

variable (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

include spec in
theorem codTarget_universe {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} :
    ∀ i g, codTarget (S := S) glb Γ u t i = some g → S.R.isUniverse g := by
  intro i g found
  obtain ⟨_, _, _, hg⟩ := codTarget_some glb found
  exact (spec hg).1

include spec in
theorem codTarget_lowerable {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} :
    ∀ i g, codTarget (S := S) glb Γ u t i = some g → ∃ w, Ctx.lookup Γ i = .head w ∧ S.R.cumulative g w := by
  intro i g found
  obtain ⟨_, w, hw, hg⟩ := codTarget_some glb found
  exact ⟨w, hw, (spec hg).2.2.1⟩

/-- **The telescope with the misfit unknowns lowered to their greatest lower bounds with `u`.** -/
abbrev codNarrowed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) : Context S.R where
  arity := Θ.arity
  raw := lowerTo Θ.raw (codTarget (S := S) glb Θ.raw v.u e.2.2.code)
  formed := lowerTo_formed Θ.raw _ (codTarget_universe glb spec) Θ.formed (codTarget_lowerable glb spec)

theorem codNarrowed_narrows {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) :
    CtxNarrows S.R Θ.raw (codNarrowed glb spec v).raw :=
  lowerTo_narrows Θ.raw _ (codTarget_lowerable glb spec)

/-- **The right side is a type of `U_u` over the narrowed telescope.** -/
theorem codNarrowed_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexCod e) (ok : CodSolvable glb v) :
    Typed S.R (codNarrowed glb spec v).raw e.2.2.code (.head v.u) := by
  refine arrowCod_typed algebra v.universe_u v.code (codNarrowed glb spec v).formed ?_ ok.heads
  intro Y member
  cases misfit : codMisfit (S := S) Θ.raw v.u e.2.2.code Y with
  | true =>
      obtain ⟨w, hw, _⟩ := ok.occurring Y member
      obtain ⟨g, hg⟩ := ok.meets Y misfit w hw
      exact ⟨g, lookup_lowerTo_some Θ.raw _ Y (codTarget_of_misfit glb misfit hw hg), (spec hg).2.1⟩
  | false =>
      obtain ⟨w, hw, _⟩ := ok.occurring Y member
      exact ⟨w, (lookup_lowerTo_none Θ.raw _ Y (codTarget_none_of_fit glb misfit)).trans hw,
        codMisfit_out hw misfit member⟩

/-- **`X := t` is a typed substitution from the narrowed telescope.** -/
theorem codNarrowSolve_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexCod e) (ok : CodSolvable glb v) :
    SubstMor S.R Θ.raw (codNarrowed glb spec v).raw (solveSub v.X e.2.2.code) := by
  intro i
  by_cases h : i = v.X
  · rw [h, v.declared]
    change Typed S.R _ (solveSub v.X e.2.2.code v.X) (.head v.u)
    rw [solveSub_self]
    exact codNarrowed_typed glb spec algebra v ok
  · change Typed S.R _ (solveSub v.X e.2.2.code i) (Presentation.subst (solveSub v.X e.2.2.code) (Ctx.lookup Θ.raw i))
    rw [solveSub_ne _ h, subst_solveSub_fresh _ fun inside => (ok.apart i v.X inside).1 rfl]
    have moved := (codNarrowed_narrows glb spec v).substMor i
    rw [subst_ids] at moved
    exact moved

/-- **The answer `X := t`**, from the narrowed telescope. -/
def codNarrowSolve (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexCod e) (ok : CodSolvable glb v) : codNarrowed glb spec v ⟶ Θ where
  substitution := solveSub v.X e.2.2.code
  typed := codNarrowSolve_typed glb spec algebra v ok

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **What the equation forces of every unknown of the code**, codomains included: a type equal to one of `U_u`. -/
theorem cod_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) {Y : Fin Θ.arity} (member : Y ∈ e.2.2.code.support) :
    ∃ small, Typed S.R Δ.raw small (.head v.u) ∧ TypeEq S.R Δ.raw small (σ.substitution Y) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code)
    (Presentation.subst σ.substitution e.2.2.code) (Presentation.subst σ.substitution e.1.1.code) at equal
  rw [v.side_left, v.annotation_left] at equal
  have tX : Typed S.R Δ.raw (σ.substitution v.X) (.head v.u) := by
    have typed := σ.typed v.X
    rw [v.declared] at typed
    exact typed
  have tT : Typed S.R Θ.raw e.2.2.code (.head v.v) := by
    have typed := e.2.2.typed
    rw [v.annotation_right] at typed
    exact typed
  exact HoldsAt.small facts roots heads algebra rigid complete headTypingUnique declared
    (holdsAt_of_support v.code member) Θ.formed v.universe_v tT (PiCode.normal rigid (piCode_of_arrowCod v.code))
    Δ.formed v.universe_u σ.substitution σ.typed tX ⟨v.v, v.universe_v, equal⟩

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **At a greatest lower bound**: every solution sends a misfit unknown to a type equal, at its own universe, to a type
of `U_g`. -/
theorem cod_misfit_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) {Y : Fin Θ.arity} (member : Y ∈ e.2.2.code.support) {w g : Head}
    (declaredY : Ctx.lookup Θ.raw Y = .head w) (universe_w : S.R.isUniverse w) (glbYes : IsGlb S.R g v.u w) :
    ∃ N, Typed S.R Δ.raw N (.head g) ∧ Equal S.R Δ.raw (σ.substitution Y) N (.head w) := by
  obtain ⟨small, tSmall, eSmall⟩ := cod_forced facts roots heads algebra rigid complete headTypingUnique declared v σ
    solved member
  have tY : Typed S.R Δ.raw (σ.substitution Y) (.head w) := by
    have typed := σ.typed Y
    rw [declaredY] at typed
    exact typed
  exact small_of_glb facts roots heads algebra rigid complete headTypingUnique v.universe_u universe_w universe_w
    glbYes (NarrowsBelow.refl g Δ.raw) Δ.formed Δ.formed tY tSmall tY eSmall ⟨w, universe_w, .refl tY⟩

/-- **Narrow to greatest lower bounds and solve, codomains included**: the misfit unknowns declared again at their
greatest lower bounds with `U_u`, and `X := t`; the solved equation is removed and the rest is instantiated. -/
def codNarrowSolveUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) (ok : CodSolvable glb v)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := codNarrowed glb spec v
  answer := codNarrowSolve glb spec algebra v ok
  remaining := (frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · apply e_of_codes
      · change Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.1.1.code =
          Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.1.code
        rw [v.annotation_left, v.annotation_right]
      · change Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.1.2.code =
          Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.2.code
        have fixed : Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.2.code =
            Presentation.subst g.substitution e'.2.2.code := by
          change Presentation.subst (fun i => Presentation.subst g.substitution (solveSub v.X e'.2.2.code i))
            e'.2.2.code = _
          rw [← subst_comp, subst_solveSub_absent _ v.code ok.absent]
        rw [fixed, v.side_left]
        change Presentation.subst g.substitution (solveSub v.X e'.2.2.code v.X) = _
        rw [solveSub_self]
    · exact (Frames.models_applyStore (X := frames S.levels) _ g rest).mp solved e' member
  complete := by
    intro Δ f solved
    have equation := solved e List.mem_cons_self
    let chosen := codMisfit (S := S) Θ.raw v.u e.2.2.code
    have smallOf : ∀ i, chosen i = true → ∃ N,
        (∀ g, codTarget (S := S) glb Θ.raw v.u e.2.2.code i = some g → Typed S.R Δ.raw N (.head g)) ∧
          Equal S.R Δ.raw (f.substitution i) N (Presentation.subst f.substitution (Ctx.lookup Θ.raw i)) := by
      intro i inside
      obtain ⟨w, hw, uw⟩ := ok.occurring i (codMisfit_mem inside)
      obtain ⟨g, hg⟩ := ok.meets i inside w hw
      obtain ⟨N, tN, eN⟩ := cod_misfit_forced facts roots heads algebra rigid complete headTypingUnique declared v f
        equation (codMisfit_mem inside) hw uw (spec hg)
      refine ⟨N, fun g' found => ?_, ?_⟩
      · rw [codTarget_of_misfit glb inside hw hg] at found
        rw [← Option.some.inj found]
        exact tN
      · rw [hw]
        exact eN
    let value : Sub Head Θ.arity Δ.arity := fun i =>
      if inside : chosen i = true then Classical.choose (smallOf i inside) else f.substitution i
    have valueIn : ∀ i (inside : chosen i = true), value i = Classical.choose (smallOf i inside) :=
      fun i inside => dif_pos inside
    have valueOut : ∀ i, chosen i = false → value i = f.substitution i := by
      intro i outside
      have notIn : ¬ chosen i = true := by rw [outside]; decide
      exact dif_neg notIn
    have same : SubstEq S.R Θ.raw Δ.raw f.substitution value := by
      refine ⟨f.typed, fun i => ?_⟩
      cases inside : chosen i with
      | true =>
          rw [valueIn i inside]
          exact (Classical.choose_spec (smallOf i inside)).2
      | false =>
          rw [valueOut i inside]
          exact .refl (f.typed i)
    have typed : SubstMor S.R (lowerTo Θ.raw (codTarget (S := S) glb Θ.raw v.u e.2.2.code)) Δ.raw value := by
      intro i
      cases inside : chosen i with
      | true =>
          obtain ⟨w, hw, _⟩ := ok.occurring i (codMisfit_mem inside)
          obtain ⟨g, hg⟩ := ok.meets i inside w hw
          have found := codTarget_of_misfit glb inside hw hg
          rw [lookup_lowerTo_some Θ.raw _ i found, valueIn i inside]
          exact (Classical.choose_spec (smallOf i inside)).1 g found
      | false =>
          rw [lookup_lowerTo_none Θ.raw _ i (codTarget_none_of_fit glb inside), valueOut i inside]
          have agree : ∀ j ∈ (Ctx.lookup Θ.raw i).support, value j = f.substitution j := by
            intro j member
            apply valueOut j
            cases hj : chosen j with
            | false => rfl
            | true => exact absurd (codMisfit_mem hj) (ok.apart i j member).2
          rw [subst_congr_support _ agree]
          exact f.typed i
    let g : Δ ⟶ codNarrowed glb spec v := ⟨value, typed⟩
    have factored : homTypedEquality S.R f (g ≫ codNarrowSolve glb spec algebra v ok) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i) (Presentation.subst value (solveSub v.X e.2.2.code i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = v.X
      · rw [h, solveSub_self, v.declared]
        have eq := ((equivalent_iff S.levels _ _).mp equation).2
        change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
          (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at eq
        rw [v.side_left, v.annotation_left] at eq
        have tRight : Typed S.R Θ.raw e.2.2.code (.head v.v) := by
          have typed := e.2.2.typed
          rw [v.annotation_right] at typed
          exact typed
        have functional := Typed.functional tRight same
        have atV : Equal S.R Δ.raw (f.substitution v.X) (Presentation.subst value e.2.2.code) (.head v.v) :=
          eq.trans functional
        have tX : Typed S.R Δ.raw (f.substitution v.X) (.head v.u) := by
          have t := f.typed v.X
          rw [v.declared] at t
          exact t
        have tValue : Typed S.R Δ.raw (Presentation.subst value e.2.2.code) (.head v.u) :=
          (codNarrowed_typed glb spec algebra v ok).substitute typed
        exact universe_injective facts roots heads algebra rigid complete Δ.formed v.universe_u v.universe_v
          tX tValue atV
      · rw [solveSub_ne _ h]
        exact same.2 i
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **Narrowing to greatest lower bounds and solving is exact, unknowns at codomains included.** -/
theorem codNarrowSolve_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e)
    (ok : CodSolvable glb v) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (codNarrowSolve glb spec algebra v ok)
      ((frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨codNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique declared v ok rest, rfl,
      rfl, rfl⟩

end Rule

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
