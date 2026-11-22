import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainReading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughLater

/-!
# Codomains that use their argument: narrowing through the binder, exact

`X ≐ t` with `t` built from unknowns, heads and Π types whose codomain may use its argument.

* **Type positions read through every binder** (`HoldsAtD`): the code, a domain, and a codomain, which may use its
  argument; every unknown of a Π-code sits at one (`holdsAtD_of_support`).
* **What a type of a universe forces through a binder** (`HoldsAtD.small`): for a normal type `t` and a typed
  substitution `σ`, a type of `U_u` equal to `σ t` makes `σ y` equal to a type of `U_u` for every unknown `y` declared at
  a universe and read at a type position of `t`. Under a codomain that uses its argument, the small Π type's codomain is
  moved to the instantiated domain (context conversion), the forcing recurses with the lifted substitution, and the
  normal form of `σ y` comes back through the weakening (`small_under`).
* **Dependent codes** (`DepCode`): a Π-code in which every bound variable that is used is bound by a universe below
  `U_u`. Such a code is a type of `U_u` when its unknowns are declared at universes below `u` and its heads are typed by
  universes below `u` (`depCode_typed`).
* **The rule** (`depNarrowSolveUpdate`, `depNarrowSolve_exact`): the misfit unknowns declared again at their greatest
  lower bounds with `U_u`, and `X := t`; exact. The arrow codes with codomains are the dependent codes that use no bound
  variable (`depCode_of_arrowCod`).
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
open ContextualDependentNormalChecking ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Type positions through every binder -/

/-- **`y` at a type position of `t`, through every binder**: the code itself, along a domain, or along a codomain
that may use its argument. -/
inductive HoldsAtD : {n : Nat} → Fin n → Tm Head n → Prop where
  | here {n : Nat} {y : Fin n} : HoldsAtD y (.var y)
  | piDomain {n : Nat} {y : Fin n} {A : Tm Head n} {B : Tm Head (n + 1)} : HoldsAtD y A → HoldsAtD y (.pi A B)
  | piCodomain {n : Nat} {y : Fin n} {A : Tm Head n} {B : Tm Head (n + 1)} :
      HoldsAtD y.succ B → HoldsAtD y (.pi A B)

/-- **Every unknown of a Π-code sits at a type position.** -/
theorem holdsAtD_of_support {n : Nat} {t : Tm Head n} (code : PiCode t) :
    ∀ {y : Fin n}, y ∈ t.support → HoldsAtD y t := by
  induction code with
  | var Y =>
      intro y member
      have same : y = Y := Finset.mem_singleton.mp member
      subst same
      exact .here
  | head h => intro y member; simp only [Tm.support, Finset.notMem_empty] at member
  | pi _ _ ihA ihB =>
      intro y member
      simp only [Tm.support, Finset.mem_union, mem_outerSupport] at member
      rcases member with inA | inB
      · exact .piDomain (ihA inA)
      · exact .piCodomain (ihB inB)

section Forcing

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **Back through a binder**: a type of `U_u` under one more declaration, equal to the weakening of a type `C` of the
outer telescope, makes `C` equal to a type of `U_u` there. -/
theorem small_under {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed S.R Δ) {A : Tm Head m}
    (formedA : CtxFormed S.R (.snoc Δ A)) {u v : Head} (hu : S.R.isUniverse u) (hv : S.R.isUniverse v)
    {C : Tm Head m} (tC : Typed S.R Δ C (.head v)) {s : Tm Head (m + 1)} (ts : Typed S.R (.snoc Δ A) s (.head u))
    (equal : TypeEq S.R (.snoc Δ A) s (Presentation.rename wk C)) :
    ∃ small, Typed S.R Δ small (.head u) ∧ TypeEq S.R Δ small C := by
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨v, hv, tC⟩
  obtain ⟨_, eN⟩ := atN hv tC
  have lN' : Long S.R S.roles (.type (.snoc Δ A) (Presentation.rename wk N)) :=
    Long.rename facts lN (CtxRen.wk Δ A) formed formedA
  have eN' : Equal S.R (.snoc Δ A) (Presentation.rename wk C) (Presentation.rename wk N) (.head v) :=
    eN.rename (CtxRen.wk Δ A)
  have tN' : Typed S.R (.snoc Δ A) (Presentation.rename wk N) (.head u) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedA hu ts
      (TypeEq.trans S.levels equal ⟨v, hv, eN'⟩) lN'
  have tN : Typed S.R Δ N (.head u) :=
    strengthen_normal facts roots heads algebra rigid complete headTypingUnique declared formed formedA hu
      (long_type_normal rigid lN') tN'
  exact ⟨N, tN, ⟨v, hv, eN.symm⟩⟩

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **What a type of a universe forces through every binder**: a type of `U_u` equal to `σ t` makes `σ y` equal to a
type of `U_u`, for every unknown `y` declared at a universe and read at a type position of the normal type `t`. -/
theorem HoldsAtD.small {n : Nat} {y : Fin n} {t : Tm Head n} (holds : HoldsAtD (Head := Head) y t) :
    ∀ {Θ : Ctx Head n}, CtxFormed S.R Θ → (∃ w, Ctx.lookup Θ y = .head w ∧ S.R.isUniverse w) →
      ∀ {w : Head}, S.R.isUniverse w → Typed S.R Θ t (.head w) → Normal (S := S) t →
      ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ → ∀ {u : Head}, S.R.isUniverse u → ∀ (σ : Sub Head n m),
        SubstMor S.R Θ Δ σ → ∀ {s : Tm Head m}, Typed S.R Δ s (.head u) → TypeEq S.R Δ s (Presentation.subst σ t) →
          ∃ small, Typed S.R Δ small (.head u) ∧ TypeEq S.R Δ small (σ y) := by
  induction holds with
  | here =>
      intro Θ _ _ _ _ _ _ m Δ _ u _ σ _ s ts equal
      exact ⟨s, ts, equal⟩
  | @piDomain n y A B _ ih =>
      intro Θ formedΘ declY w hw tt normal m Δ formed u hu σ typedσ s ts equal
      have generation : GenerationAt S.R Θ (.pi A B) (.head w) := Typed.generation tt
      obtain ⟨u₁, _, _, tA, hu₁, _, _, _, _⟩ := generation
      obtain ⟨_, _, tA', eA', _, _⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      exact ih formedΘ declY hu₁ tA (normal_pi_domain normal) formed hu σ typedσ tA' eA'
  | @piCodomain n y A B _ ih =>
      intro Θ formedΘ declY w hw tt normal m Δ formed u hu σ typedσ s ts equal
      have generation : GenerationAt S.R Θ (.pi A B) (.head w) := Typed.generation tt
      obtain ⟨u₁, u₂, _, tA, hu₁, tB, hu₂, _, _⟩ := generation
      have equal' : TypeEq S.R Δ s (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) := equal
      obtain ⟨A', B', _, eA', tB', eB'⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal'
      have formedΘA : CtxFormed S.R (.snoc Θ A) := formedΘ.snoc ⟨u₁, hu₁, tA⟩
      have formedσA : CtxFormed S.R (.snoc Δ (Presentation.subst σ A)) :=
        formed.snoc ⟨u₁, hu₁, tA.substitute typedσ⟩
      have conv : CtxEq S.R (.snoc Δ A') (.snoc Δ (Presentation.subst σ A)) :=
        .snoc (CtxEq.refl Δ formed) eA'.symm
      have tB'' : Typed S.R (.snoc Δ (Presentation.subst σ A)) B' (.head u) := Typed.stable tB' conv
      have eB'' : TypeEq S.R (.snoc Δ (Presentation.subst σ A)) B' (Presentation.subst (liftSub σ) B) :=
        TypeEq.stable eB' conv
      obtain ⟨w', hw', uw'⟩ := declY
      have declY' : ∃ w, Ctx.lookup (.snoc Θ A) y.succ = .head w ∧ S.R.isUniverse w :=
        ⟨w', by rw [Ctx.lookup_snoc_succ, hw']; rfl, uw'⟩
      obtain ⟨small', tSmall', eSmall'⟩ := ih formedΘA declY' hu₂ tB (normal_pi_codomain normal) formedσA hu
        (liftSub σ) (typedσ.lift A) tB'' eB''
      have tY : Typed S.R Δ (σ y) (.head w') := by
        have t := typedσ y
        rw [hw'] at t
        exact t
      exact small_under facts roots heads algebra rigid complete headTypingUnique declared formed formedσA hu uw' tY
        tSmall' eSmall'

end Forcing

/-! ## Dependent codes -/

section Codes

/-- **A Π-code whose used bound variables are bound by universes below `u`.** -/
inductive DepCode (R : Rules Head) (u : Head) : {n : Nat} → Tm Head n → Prop where
  | var {n : Nat} (Y : Fin n) : DepCode R u (.var Y)
  | head {n : Nat} (h : Head) : DepCode R u (n := n) (.head h)
  | pi {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} : DepCode R u A → DepCode R u B →
      (0 ∈ B.support → ∃ w, A = .head w ∧ R.cumulative w u) → DepCode R u (.pi A B)

theorem DepCode.piCode {R : Rules Head} {u : Head} {n : Nat} {t : Tm Head n} (code : DepCode R u t) : PiCode t := by
  induction code with
  | var Y => exact .var Y
  | head h => exact .head h
  | pi _ _ _ ihA ihB => exact .pi ihA ihB

/-- Renaming keeps a dependent code. -/
theorem DepCode.rename {R : Rules Head} {u : Head} {n : Nat} {t : Tm Head n} (code : DepCode R u t) :
    ∀ {m : Nat} (ρ : Ren n m), DepCode R u (Presentation.rename ρ t) := by
  induction code with
  | var Y => intro m ρ; exact .var (ρ Y)
  | head h => intro m ρ; exact .head h
  | @pi n A B _ _ bound ihA ihB =>
      intro m ρ
      refine .pi (ihA ρ) (ihB (liftRen ρ)) fun inside => ?_
      rw [ContextualDependentSupport.support_rename, Finset.mem_image] at inside
      obtain ⟨a, member, same⟩ := inside
      have zero : a = 0 := by
        refine Fin.cases (motive := fun a => liftRen ρ a = 0 → a = 0) (fun _ => rfl) (fun a' h => ?_) a same
        exact absurd h (Fin.succ_ne_zero _)
      subst zero
      obtain ⟨w, hA, c⟩ := bound member
      exact ⟨w, by rw [hA]; rfl, c⟩

/-- **The arrow codes with codomains are the dependent codes that use no bound variable.** -/
theorem depCode_of_arrowCod {R : Rules Head} {u : Head} {n : Nat} {t : Tm Head n} (code : ArrowCod t) :
    DepCode R u t := by
  induction code with
  | var Y => exact .var Y
  | head h => exact .head h
  | @pi A B _ _ ihA ihB =>
      refine .pi ihA (ihB.rename wk) fun inside => ?_
      rw [ContextualDependentSupport.support_rename, Finset.mem_image] at inside
      obtain ⟨a, _, same⟩ := inside
      exact absurd same (Fin.succ_ne_zero a)

variable {S : Setting Head L}

/-- **A dependent code is a type of `U_u`** when its unknowns are declared at universes below `u` and its heads are
typed by universes below `u`. -/
theorem depCode_typed (algebra : CumulativeAlgebra S.R) {u : Head} (hu : S.R.isUniverse u) :
    ∀ {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}, DepCode S.R u t → CtxFormed S.R Γ →
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
  | @pi n A B _ _ bound ihA ihB =>
      intro formed vars heads
      have tA : Typed S.R Γ A (.head u) :=
        ihA formed (fun Y member => vars Y (by simp only [Tm.support, Finset.mem_union]; exact .inl member))
          (fun h member => heads h (by simp only [codHeads]; exact List.mem_append_left _ member))
      have formedA : CtxFormed S.R (.snoc Γ A) := formed.snoc ⟨u, hu, tA⟩
      have tB : Typed S.R (.snoc Γ A) B (.head u) := by
        refine ihB formedA (fun Y member => ?_)
          (fun h member => heads h (by simp only [codHeads]; exact List.mem_append_right _ member))
        refine Fin.cases (motive := fun Y => Y ∈ B.support → ∃ w, Ctx.lookup (.snoc Γ A) Y = .head w ∧
          S.R.cumulative w u) ?_ (fun Y' member' => ?_) Y member
        · intro zero
          obtain ⟨w, hA, c⟩ := bound zero
          refine ⟨w, ?_, c⟩
          rw [hA]
          rfl
        · obtain ⟨w, hw, c⟩ := vars Y' (by
            simp only [Tm.support, Finset.mem_union, mem_outerSupport]
            exact .inr member')
          refine ⟨w, ?_, c⟩
          rw [Ctx.lookup_snoc_succ, hw]
          rfl
      obtain ⟨w', join'⟩ := S.levels.join_exists hu hu
      exact Derivable.cumul (Derivable.piForm tA hu tB hu join')
        (algebra.join_least join' (S.levels.cumulative_refl hu) (S.levels.cumulative_refl hu))

end Codes

/-! ## The rule -/

section Rule

variable {S : Setting Head L}

/-- **A flex–rigid equation with a dependent code**: `X ≐ t` at `U_v`, `X : U_u`, `t` a dependent code below `u`. -/
structure FlexDep {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  v : Head
  X : Fin Θ.arity
  u : Head
  annotation_left : e.1.1.code = .head v
  annotation_right : e.2.1.code = .head v
  side_left : e.1.2.code = .var X
  declared : Ctx.lookup Θ.raw X = .head u
  universe_u : S.R.isUniverse u
  universe_v : S.R.isUniverse v
  code : DepCode S.R u e.2.2.code

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)

/-- **The conditions of the rule**: no occurrence of `X`, heads typed below `u`, the unknowns of `t` declared at
universes, no declaration mentioning `X` or an unknown of `t`, and a greatest lower bound with `u` for every misfit
unknown. -/
structure DepSolvable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e) : Prop where
  absent : v.X ∉ e.2.2.code.support
  heads : ∀ h ∈ codHeads e.2.2.code, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k v.u
  occurring : ∀ Y ∈ e.2.2.code.support, ∃ w, Ctx.lookup Θ.raw Y = .head w ∧ S.R.isUniverse w
  apart : ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, j ≠ v.X ∧ j ∉ e.2.2.code.support
  meets : ∀ i, codMisfit (S := S) Θ.raw v.u e.2.2.code i = true → ∀ w, Ctx.lookup Θ.raw i = .head w →
    ∃ g, glb v.u w = some g

variable (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The telescope with the misfit unknowns lowered to their greatest lower bounds with `u`.** -/
abbrev depNarrowed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e) : Context S.R where
  arity := Θ.arity
  raw := lowerTo Θ.raw (codTarget (S := S) glb Θ.raw v.u e.2.2.code)
  formed := lowerTo_formed Θ.raw _ (codTarget_universe glb spec) Θ.formed (codTarget_lowerable glb spec)

theorem depNarrowed_narrows {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e) :
    CtxNarrows S.R Θ.raw (depNarrowed glb spec v).raw :=
  lowerTo_narrows Θ.raw _ (codTarget_lowerable glb spec)

/-- **The right side is a type of `U_u` over the narrowed telescope.** -/
theorem depNarrowed_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexDep e) (ok : DepSolvable glb v) :
    Typed S.R (depNarrowed glb spec v).raw e.2.2.code (.head v.u) := by
  refine depCode_typed algebra v.universe_u v.code (depNarrowed glb spec v).formed ?_ ok.heads
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
theorem depNarrowSolve_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexDep e) (ok : DepSolvable glb v) :
    SubstMor S.R Θ.raw (depNarrowed glb spec v).raw (solveSub v.X e.2.2.code) := by
  intro i
  by_cases h : i = v.X
  · rw [h, v.declared]
    change Typed S.R _ (solveSub v.X e.2.2.code v.X) (.head v.u)
    rw [solveSub_self]
    exact depNarrowed_typed glb spec algebra v ok
  · rw [solveSub_ne _ h, subst_solveSub_fresh _ fun inside => (ok.apart i v.X inside).1 rfl]
    have moved := (depNarrowed_narrows glb spec v).substMor i
    rw [subst_ids] at moved
    exact moved

/-- **The answer `X := t`**, from the narrowed telescope. -/
def depNarrowSolve (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexDep e) (ok : DepSolvable glb v) : depNarrowed glb spec v ⟶ Θ where
  substitution := solveSub v.X e.2.2.code
  typed := depNarrowSolve_typed glb spec algebra v ok

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **What the equation forces of every unknown of the code, through every binder**: a type equal to one of `U_u`. -/
theorem dep_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) {Y : Fin Θ.arity} (member : Y ∈ e.2.2.code.support)
    (declaredY : ∃ w, Ctx.lookup Θ.raw Y = .head w ∧ S.R.isUniverse w) :
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
  exact HoldsAtD.small facts roots heads algebra rigid complete headTypingUnique declared
    (holdsAtD_of_support v.code.piCode member) Θ.formed declaredY v.universe_v tT
    (PiCode.normal rigid v.code.piCode) Δ.formed v.universe_u σ.substitution σ.typed tX ⟨v.v, v.universe_v, equal⟩

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **At a greatest lower bound**: every solution sends a misfit unknown to a type equal, at its own universe, to a type
of `U_g`. -/
theorem dep_misfit_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) {Y : Fin Θ.arity} (member : Y ∈ e.2.2.code.support) {w g : Head}
    (declaredY : Ctx.lookup Θ.raw Y = .head w) (universe_w : S.R.isUniverse w) (glbYes : IsGlb S.R g v.u w) :
    ∃ N, Typed S.R Δ.raw N (.head g) ∧ Equal S.R Δ.raw (σ.substitution Y) N (.head w) := by
  obtain ⟨small, tSmall, eSmall⟩ := dep_forced facts roots heads algebra rigid complete headTypingUnique declared v σ
    solved member ⟨w, declaredY, universe_w⟩
  have tY : Typed S.R Δ.raw (σ.substitution Y) (.head w) := by
    have typed := σ.typed Y
    rw [declaredY] at typed
    exact typed
  exact small_of_glb facts roots heads algebra rigid complete headTypingUnique v.universe_u universe_w universe_w
    glbYes (NarrowsBelow.refl g Δ.raw) Δ.formed Δ.formed tY tSmall tY eSmall ⟨w, universe_w, .refl tY⟩

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **Narrow to greatest lower bounds and solve, codomains that use their argument included**: the misfit unknowns
declared again at their greatest lower bounds with `U_u`, and `X := t`; the solved equation is removed and the rest is
instantiated. -/
def depNarrowSolveUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e) (ok : DepSolvable glb v)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := depNarrowed glb spec v
  answer := depNarrowSolve glb spec algebra v ok
  remaining := (frames S.levels).applyStore (depNarrowSolve glb spec algebra v ok) rest
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
          rw [← subst_comp, subst_solveSub_fresh _ ok.absent]
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
      obtain ⟨N, tN, eN⟩ := dep_misfit_forced facts roots heads algebra rigid complete headTypingUnique declared v f
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
    let g : Δ ⟶ depNarrowed glb spec v := ⟨value, typed⟩
    have factored : homTypedEquality S.R f (g ≫ depNarrowSolve glb spec algebra v ok) := by
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
          (depNarrowed_typed glb spec algebra v ok).substitute typed
        exact universe_injective facts roots heads algebra rigid complete Δ.formed v.universe_u v.universe_v
          tX tValue atV
      · rw [solveSub_ne _ h]
        exact same.2 i
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **Narrowing to greatest lower bounds and solving is exact, codomains that use their argument included.** -/
theorem depNarrowSolve_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e)
    (ok : DepSolvable glb v) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (depNarrowSolve glb spec algebra v ok)
      ((frames S.levels).applyStore (depNarrowSolve glb spec algebra v ok) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨depNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique declared v ok rest, rfl,
      rfl, rfl⟩

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **One such equation has a principal answer**: the narrowed telescope and `X := t`. -/
theorem depNarrowSolve_principal {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e)
    (ok : DepSolvable glb v) :
    (frames S.levels).Principal [e] (depNarrowSolve glb spec algebra v ok) :=
  (depNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique declared v ok []).completed rfl

end Rule

/-! ## The refutations, and one equation decided -/

section Decide

open ContextualDependentOccursFull

/-- **An unknown of a Π-code is the code, or occurs properly in it**, through every binder. -/
theorem within_of_support_pi {n : Nat} {X : Fin n} {t : Tm Head n} (code : PiCode t) (member : X ∈ t.support) :
    t = .var X ∨ Within true (.var X) t := by
  induction code with
  | var Y =>
      have same : X = Y := by simpa [Tm.support] using member
      exact .inl (by rw [same])
  | head h => simp [Tm.support] at member
  | @pi n A B _ _ ihA ihB =>
      right
      simp only [Tm.support, Finset.mem_union, mem_outerSupport] at member
      rcases member with inA | inB
      · rcases ihA inA with same | within
        · rw [same]
          exact .domain true (.here _)
        · exact .domain true within
      · rcases ihB inB with same | within
        · rw [same]
          exact .codomain true (.here _)
        · exact .codomain true within

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The occurs check through every binder**: `X ≐ t` with `X` in `t`, `t` not `X`, has no solution. -/
theorem dep_occurs_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e)
    (member : v.X ∈ e.2.2.code.support) (ne : e.2.2.code ≠ .var v.X) (rest : EquationStore (TotalTerm Θ)) :
    ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  rcases within_of_support_pi v.code.piCode member with same | within
  · exact ne same
  · rw [← v.side_left] at within
    exact OccursFullShape.refutes facts roots heads algebra rigid complete
      ⟨v.v, v.universe_v, v.annotation_left, v.annotation_right, within⟩ σ (models e List.mem_cons_self)

include facts roots heads algebra rigid complete in
/-- **A misfit head refutes, through every binder.** -/
theorem piCode_misfit {u h₀ : Head} (hu : S.R.isUniverse u) (apart : ∀ k, S.R.headTyping h₀ k → ¬ S.R.cumulative k u) :
    ∀ {n : Nat} {t : Tm Head n}, PiCode t → h₀ ∈ codHeads t → ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ →
      ∀ (σ : Sub Head n m) {s : Tm Head m}, Typed S.R Δ s (.head u) → ¬ TypeEq S.R Δ s (Presentation.subst σ t) := by
  intro n t code
  induction code with
  | var Y => intro member; cases member
  | head h =>
      intro member m Δ formed σ s ts
      have same : h₀ = h := List.mem_singleton.mp member
      subst same
      exact sort_not_small facts roots heads algebra rigid complete formed hu apart ts
  | @pi n A B _ _ ihA ihB =>
      intro member m Δ formed σ s ts equal
      change TypeEq S.R Δ s (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) at equal
      obtain ⟨A', B', tA', eA', tB', eB'⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      simp only [codHeads, List.mem_append] at member
      rcases member with inA | inB
      · exact ihA inA formed σ tA' eA'
      · have formedA' : CtxFormed S.R (.snoc Δ A') := formed.snoc ⟨u, hu, tA'⟩
        exact ihB inB formedA' (liftSub σ) tB' eB'

include facts roots heads algebra rigid complete in
/-- **A misfit head refutes** `X ≐ t`. -/
theorem dep_misfitHead_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e) {h₀ : Head}
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
  exact piCode_misfit facts roots heads algebra rigid complete v.universe_u apart v.code.piCode member Δ.formed
    σ.substitution tX ⟨v.v, v.universe_v, equal⟩

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include facts roots heads algebra rigid complete spec headTypingUnique declared total in
/-- **One equation with a dependent code is decided**: when the unknowns of `t` are declared at universes and no
declaration mentions `X` or an unknown of `t`, the store `[X ≐ t]` has a finished update (a principal answer) or no
solution: `t` is `X`; or `X` occurs in `t` (no solution); or a head of `t` is typed by no universe below `u` (no
solution); or the misfit unknowns are narrowed and `X := t`. -/
theorem dep_settles {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexDep e)
    (occurring : ∀ Y ∈ e.2.2.code.support, ∃ w, Ctx.lookup Θ.raw Y = .head w ∧ S.R.isUniverse w)
    (apart : ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, j ≠ v.X ∧ j ∉ e.2.2.code.support) :
    Settles [e] := by
  by_cases same : e.2.2.code = .var v.X
  · refine .inl ⟨deleteCodes e (v.annotation_left.trans v.annotation_right.symm) (v.side_left.trans same.symm) [], rfl⟩
  by_cases occurs : v.X ∈ e.2.2.code.support
  · exact .inr (dep_occurs_refutes facts roots heads algebra rigid complete v occurs same [])
  by_cases misfit : ∃ h ∈ codHeads e.2.2.code, ∀ k, S.R.headTyping h k → ¬ S.R.cumulative k v.u
  · obtain ⟨h, member, apartH⟩ := misfit
    exact .inr (dep_misfitHead_refutes facts roots heads algebra rigid complete v member apartH [])
  · have headsOk : ∀ h ∈ codHeads e.2.2.code, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k v.u := by
      intro h member
      by_contra none
      apply misfit
      refine ⟨h, member, fun k typing below => none ⟨k, typing, below⟩⟩
    have ok : DepSolvable glb v :=
      { absent := occurs
        heads := headsOk
        occurring := occurring
        apart := apart
        meets := fun i _ w hw => by
          obtain ⟨w', hw', uw'⟩ := occurring i (codMisfit_mem ‹_›)
          rw [hw] at hw'
          cases hw'
          exact total v.universe_u uw' }
    exact .inl ⟨depNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique declared v ok [],
      rfl⟩

end Decide

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
