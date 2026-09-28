import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Lift

/-!
# The algorithmic equality as a generic equality

Two types, terms or spines are related when they are equal in the typed
equality and, after every renaming into a formed context, algorithmically
equal there (spines at a type below the renamed type). Closing under formed
renamings makes weakening immediate; the typed equality supplies soundness.
Every law of the generic equality holds, given the facts about the weak-head
forms of types, the package's preservation of typing by its root and head steps,
its cumulativity order, and the lifting of spine comparisons (`SpineLift`); so
a model can be built over it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Renaming helpers -/

theorem TypeLe.rename {R : Rules Head} {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} {A B : Tm Head n} (le : TypeLe R Γ A B) (compatible : CtxRen Γ Δ ρ) :
    TypeLe R Δ (Presentation.rename ρ A) (Presentation.rename ρ B) := by
  induction le with
  | refl => exact .refl _
  | conv e hu _ ih => exact .conv (e.rename compatible) hu ih
  | cumul c _ ih => exact .cumul c ih
  | sub le _ ih => exact .sub (Derivable.renames le compatible) ih

theorem Liftable.rename {roles : Roles Head} {n m : Nat} {t : Tm Head n}
    (lifted : Liftable roles t) (ρ : Ren n m) : Liftable roles (Presentation.rename ρ t) := by
  rcases lifted with neutral | ⟨k, arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
  · exact .inl (neutral.rename ρ)
  · refine .inr (.inl ⟨k, arity, args.map (Presentation.rename ρ), role, ?_⟩)
    rw [rename_appSpine]
    rfl
  · exact .inr (.inr ⟨T, ctors, role, rfl⟩)

theorem rename_liftRen_rename_wk {n m : Nat} (ρ : Ren n m) (t : Tm Head n) :
    Presentation.rename (liftRen ρ) (Presentation.rename wk t) =
      Presentation.rename wk (Presentation.rename ρ t) := by
  rw [rename_rename, rename_rename]
  rfl

theorem rename_liftRen_appFresh {n m : Nat} (ρ : Ren n m) (f : Tm Head n) :
    Presentation.rename (liftRen ρ) (.app (Presentation.rename wk f) (.var 0)) =
      .app (Presentation.rename wk (Presentation.rename ρ f)) (.var 0) := by
  show Tm.app (Presentation.rename (liftRen ρ) (Presentation.rename wk f)) (.var (liftRen ρ 0)) = _
  rw [rename_liftRen_rename_wk]
  rfl

/-! ## The instance -/

/-- The algorithmic equality, closed under renamings into formed contexts, and
paired with the typed equality. -/
def algorithmic (R : Rules Head) (roles : Roles Head) : GenericEquality Head where
  convTy := fun {n} Γ A B => TypeEq R Γ A B ∧
    ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren n m⦄, CtxRen Γ Δ ρ → CtxFormed R Δ →
      Algorithmic R roles (.types Δ (Presentation.rename ρ A) (Presentation.rename ρ B))
  convTm := fun {n} Γ t u A => Equal R Γ t u A ∧
    ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren n m⦄, CtxRen Γ Δ ρ → CtxFormed R Δ →
      Algorithmic R roles (.terms Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
        (Presentation.rename ρ A))
  convNe := fun {n} Γ t u A => Equal R Γ t u A ∧
    ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren n m⦄, CtxRen Γ Δ ρ → CtxFormed R Δ →
      ∃ U, Algorithmic R roles (.spines Δ (Presentation.rename ρ t) (Presentation.rename ρ u) U) ∧
        TypeLe R Δ U (Presentation.rename ρ A)

variable {S : Setting Head L}

/-! ## Algorithmic facts used by the laws -/

section Facts

variable {n : Nat} {Δ : Ctx Head n}

theorem Algorithmic.types_of_universe {t u : Tm Head n} {h : Head} (hu : S.R.isUniverse h)
    (derivation : Algorithmic S.R S.roles (.terms Δ t u (.head h))) :
    Algorithmic S.R S.roles (.types Δ t u) := by
  cases derivation with
  | terms rA fA rt ru d =>
      obtain rfl := (WhRed.eq_of_whnf (head_whnf S.shape h) rA.red)
      cases d with
      | univ _ _ _ dW =>
          exact .types (rt.toRedTy hu) (ru.toRedTy hu) dW.typesW_form.1 dW.typesW_form.2 dW
      | spine sA _ _ _ _ _ => exact absurd hu sA.not_universe

theorem Algorithmic.terms_cumul {t u : Tm Head n} {v w : Head}
    (derivation : Algorithmic S.R S.roles (.terms Δ t u (.head v))) (c : S.R.cumulative v w) :
    Algorithmic S.R S.roles (.terms Δ t u (.head w)) := by
  have hw := (S.levels.cumulative_universe c).2.1
  obtain ⟨w', _, typing, _⟩ := S.levels.successor hw
  have isW : IsType S.R Δ (.head w) :=
    ⟨w', (S.levels.universe_typing hw typing).1, .headType typing⟩
  cases derivation with
  | terms rA fA rt ru d =>
      obtain rfl := (WhRed.eq_of_whnf (head_whnf S.shape v) rA.red)
      cases d with
      | univ hv tt tu dW =>
          exact .terms (RedTy.refl isW) (.inl ⟨w, rfl⟩) (RedTm.cumul rt c) (RedTm.cumul ru c)
            (.univ hw (.cumul tt c) (.cumul tu c) dW)
      | spine sA _ _ _ _ _ => exact absurd (S.levels.cumulative_universe c).1 sA.not_universe

theorem universe_isType {h : Head} (hu : S.R.isUniverse h) : IsType S.R Δ (.head h) := by
  obtain ⟨v, _, typing, _⟩ := S.levels.successor hu
  exact ⟨v, (S.levels.universe_typing hu typing).1, .headType typing⟩

theorem algorithmic_convTy_of_convTm {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (h : (algorithmic S.R S.roles).convTm Γ A B (.head u)) (hu : S.R.isUniverse u) :
    (algorithmic S.R S.roles).convTy Γ A B :=
  ⟨⟨u, hu, h.1⟩, fun _ _ _ cr formed => Algorithmic.types_of_universe hu (h.2 cr formed)⟩

/-- Liftable terms compared as spines in every formed world are compared at the
type in every formed world, when spine comparisons lift. -/
theorem algorithmic_convTm_of_convNe (lift : SpineLift S) {n : Nat} {Γ : Ctx Head n}
    {t u A : Tm Head n} (lt : Liftable S.roles t) (lu : Liftable S.roles u)
    (h : (algorithmic S.R S.roles).convNe Γ t u A) :
    (algorithmic S.R S.roles).convTm Γ t u A := by
  refine ⟨h.1, fun m Δ ρ cr formed => ?_⟩
  have spines : SpinesEverywhere S Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
      (Presentation.rename ρ A) := by
    intro k Θ ρ' w'
    obtain ⟨U, d, le⟩ := h.2 (CtxRen.comp cr w'.1) w'.2
    rw [rename_rename, rename_rename, rename_rename]
    exact ⟨U, d, le⟩
  exact lift formed (lt.rename ρ) (lu.rename ρ) (h.1.rename cr) spines

end Facts

section Laws

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts roots heads algebra

/-- A comparison of terms at a type is a comparison at every type it is usable
at, under every typed substitution. At a dependent function type the
applications to a fresh variable are compared at the larger codomain, over
the domain changed to its equal; at a dependent pair type the first
projections are compared at the larger domain and the second ones at the
larger codomain instantiated at the same first projection. -/
theorem Algorithmic.terms_below {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (le : Below S.R Γ A B) :
    ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, SubstMor S.R Γ Δ σ → CtxFormed S.R Δ →
      ∀ {t u : Tm Head m}, Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ A)) →
        Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ B)) := by
  refine Below.induction (motive := fun n Γ A B =>
      ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, SubstMor S.R Γ Δ σ → CtxFormed S.R Δ →
        ∀ {t u : Tm Head m}, Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ A)) →
          Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ B)))
    ?equal ?univ ?pi ?sigma ?trans le
  case equal =>
    intro n Γ A B u e hu m Δ σ typed formed t s d
    exact Algorithmic.converts facts roots heads algebra d (CtxEq.refl Δ formed) formed
      ⟨u, hu, e.substitute typed⟩
  case univ =>
    intro n Γ u v c m Δ σ typed formed t s d
    exact Algorithmic.terms_cumul d c
  case pi =>
    intro n Γ A A' B B' u u' w tPi hu tPi' hu' eA hw leB ihB m Δ σ typed formed t s d
    have belowσ : Below S.R Δ (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (.pi (Presentation.subst σ A') (Presentation.subst (liftSub σ) B')) :=
      Derivable.substitutes (Derivable.subPi tPi hu tPi' hu' eA hw leB) typed
    have tPiσ' : Typed S.R Δ (.pi (Presentation.subst σ A') (Presentation.subst (liftSub σ) B'))
        (.head u') := tPi'.substitute typed
    obtain ⟨⟨_, hA', tA'⟩, ⟨_, hB', tB'⟩⟩ := IsType.pi_parts ⟨u', hu', tPiσ'⟩
    have eAσ : TypeEq S.R Δ (Presentation.subst σ A) (Presentation.subst σ A') :=
      ⟨w, hw, eA.substitute typed⟩
    have d' : Algorithmic S.R S.roles
        (.terms Δ t s (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))) := d
    cases d' with
    | terms rA fA rt rs dW =>
        obtain rfl := WhRed.eq_of_whnf (pi_whnf S.shape _ _) rA.red
        cases dW with
        | eta isA tf funF tg funG d₁ =>
            have d₂ := ihB (typed.lift A) (.snoc formed isA) d₁
            have formedA' : CtxFormed S.R (.snoc Δ (Presentation.subst σ A')) :=
              .snoc formed ⟨_, hA', tA'⟩
            have d₃ := Algorithmic.converts facts roots heads algebra d₂
              (.snoc (CtxEq.refl Δ formed) eAσ.symm) formedA' (IsType.refl ⟨_, hB', tB'⟩)
            exact .terms (RedTy.refl ⟨u', hu', tPiσ'⟩) (.inr (.inl ⟨_, _, rfl⟩)) (rt.below belowσ)
              (rs.below belowσ)
              (.eta ⟨_, hA', tA'⟩ (.sub tf belowσ) funF (.sub tg belowσ) funG d₃)
        | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_pi
  case sigma =>
    intro n Γ A A' B B' u u' tS hu tS' hu' leA leB ihA ihB m Δ σ typed formed t s d
    have belowσ : Below S.R Δ (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (.sigma (Presentation.subst σ A') (Presentation.subst (liftSub σ) B')) :=
      Derivable.substitutes (Derivable.subSigma tS hu tS' hu' leA leB) typed
    have tSσ' : Typed S.R Δ (.sigma (Presentation.subst σ A') (Presentation.subst (liftSub σ) B'))
        (.head u') := tS'.substitute typed
    have d' : Algorithmic S.R S.roles
        (.terms Δ t s (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))) := d
    cases d' with
    | @terms _ _ _ p _ q _ _ rA fA rt rs dW =>
        obtain rfl := WhRed.eq_of_whnf (sigma_whnf S.shape _ _) rA.red
        cases dW with
        | sigmaEta tp pairP tq pairQ dFst dSnd =>
            have dFst' := ihA typed formed dFst
            have typedCons : SubstMor S.R (.snoc Γ A) Δ (consSub (.fst p) σ) := by
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · show Typed S.R Δ (.fst p) (Presentation.subst (consSub (.fst p) σ) (Presentation.rename wk A))
                rw [subst_rename_wk]
                exact .fstElim tp
              · show Typed S.R Δ (σ j)
                  (Presentation.subst (consSub (.fst p) σ) (Presentation.rename wk (Ctx.lookup Γ j)))
                rw [subst_rename_wk]
                exact typed j
            rw [inst0_subst_liftSub] at dSnd
            have dSnd' := ihB typedCons formed dSnd
            rw [← inst0_subst_liftSub] at dSnd'
            exact .terms (RedTy.refl ⟨u', hu', tSσ'⟩) (.inr (.inr (.inl ⟨_, _, rfl⟩)))
              (rt.below belowσ) (rs.below belowσ)
              (.sigmaEta (.sub tp belowσ) pairP (.sub tq belowσ) pairQ dFst' dSnd')
        | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_sigma
  case trans =>
    intro n Γ A B C _ _ ih₁ ih₂ m Δ σ typed formed t s d
    exact ih₂ typed formed (ih₁ typed formed d)

/-- A comparison of terms at a type is one at every type it is usable at. -/
theorem Algorithmic.terms_below_here {n : Nat} {Δ : Ctx Head n} {A B t u : Tm Head n}
    (le : Below S.R Δ A B) (formed : CtxFormed S.R Δ)
    (derivation : Algorithmic S.R S.roles (.terms Δ t u A)) :
    Algorithmic S.R S.roles (.terms Δ t u B) := by
  have d := Algorithmic.terms_below facts roots heads algebra le
    (CtxEq.substMor (CtxEq.refl Δ formed)) formed (t := t) (u := u) (by rwa [subst_ids])
  rwa [subst_ids] at d

/-- A comparison at a type, of terms of a type below it, is a comparison at the
smaller type, under every typed substitution. At a universe both compare the
terms as types. At a dependent function type the applications to a fresh
variable are compared at the smaller codomain, over the domain changed to its
equal. At a dependent pair type the first projections are compared at the
smaller domain, and the second ones at the smaller codomain instantiated at the
first projection of the left pair, to which the right one's is equal. -/
theorem Algorithmic.terms_down {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (le : Below S.R Γ A B) :
    ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, SubstMor S.R Γ Δ σ → CtxFormed S.R Δ →
      ∀ {t u : Tm Head m}, Typed S.R Δ t (Presentation.subst σ A) →
        Typed S.R Δ u (Presentation.subst σ A) →
        Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ B)) →
        Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ A)) := by
  refine Below.induction (motive := fun n Γ A B =>
      ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m}, SubstMor S.R Γ Δ σ → CtxFormed S.R Δ →
        ∀ {t u : Tm Head m}, Typed S.R Δ t (Presentation.subst σ A) →
          Typed S.R Δ u (Presentation.subst σ A) →
          Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ B)) →
          Algorithmic S.R S.roles (.terms Δ t u (Presentation.subst σ A)))
    ?equal ?univ ?pi ?sigma ?trans le
  case equal =>
    intro n Γ A B u e hu m Δ σ typed formed t s _ _ d
    exact Algorithmic.converts facts roots heads algebra d (CtxEq.refl Δ formed) formed
      (TypeEq.symm ⟨u, hu, e.substitute typed⟩)
  case univ =>
    intro n Γ u v c m Δ σ typed formed t s tt ts d
    have hu := (S.levels.cumulative_universe c).1
    have tt' : Typed S.R Δ t (.head u) := tt
    have ts' : Typed S.R Δ s (.head u) := ts
    have d' : Algorithmic S.R S.roles (.terms Δ t s (.head v)) := d
    cases d' with
    | terms rA fA rt rs dW =>
        obtain rfl := WhRed.eq_of_whnf (head_whnf S.shape v) rA.red
        cases dW with
        | univ _ _ _ dT =>
            obtain ⟨tt₀, et⟩ := WhRed.preserve facts roots formed rt.red tt'
            obtain ⟨ts₀, es⟩ := WhRed.preserve facts roots formed rs.red ts'
            exact .terms (RedTy.refl (universe_isType hu)) (.inl ⟨u, rfl⟩) ⟨rt.red, tt', tt₀, et⟩
              ⟨rs.red, ts', ts₀, es⟩ (.univ hu tt₀ ts₀ dT)
        | spine sA _ _ _ _ _ => exact absurd (S.levels.cumulative_universe c).2.1 sA.not_universe
  case pi =>
    intro n Γ A A' B B' u u' w tPi hu tPi' hu' eA hw _ ihB m Δ σ typed formed t s tt ts d
    have tPiσ : Typed S.R Δ (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (.head u) := tPi.substitute typed
    have tPiσ' : Typed S.R Δ (.pi (Presentation.subst σ A') (Presentation.subst (liftSub σ) B'))
        (.head u') := tPi'.substitute typed
    obtain ⟨⟨_, hA, tA⟩, _⟩ := IsType.pi_parts ⟨u, hu, tPiσ⟩
    obtain ⟨_, ⟨_, hB', tB'⟩⟩ := IsType.pi_parts ⟨u', hu', tPiσ'⟩
    have eAσ : TypeEq S.R Δ (Presentation.subst σ A) (Presentation.subst σ A') :=
      ⟨w, hw, eA.substitute typed⟩
    have formedA : CtxFormed S.R (.snoc Δ (Presentation.subst σ A)) := .snoc formed ⟨_, hA, tA⟩
    have tt' : Typed S.R Δ t
        (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) := tt
    have ts' : Typed S.R Δ s
        (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) := ts
    have d' : Algorithmic S.R S.roles
        (.terms Δ t s (.pi (Presentation.subst σ A') (Presentation.subst (liftSub σ) B'))) := d
    have apply : ∀ {f : Tm Head m},
        Typed S.R Δ f (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) →
        Typed S.R (.snoc Δ (Presentation.subst σ A)) (.app (Presentation.rename wk f) (.var 0))
          (Presentation.subst (liftSub σ) B) := by
      intro f tf
      have tw : Typed S.R (.snoc Δ (Presentation.subst σ A)) (Presentation.rename wk f)
          (.pi (Presentation.rename wk (Presentation.subst σ A))
            (Presentation.rename (liftRen wk) (Presentation.subst (liftSub σ) B))) :=
        Typed.weaken tf
      have tapp := Derivable.appElim tw
        (.var 0 : Typed S.R (.snoc Δ (Presentation.subst σ A)) (.var 0) _)
      rwa [inst0_var_rename_liftRen_wk] at tapp
    cases d' with
    | terms rA fA rt rs dW =>
        obtain rfl := WhRed.eq_of_whnf (pi_whnf S.shape _ _) rA.red
        cases dW with
        | eta _ _ funF _ funG d₁ =>
            obtain ⟨tf, ef⟩ := WhRed.preserve facts roots formed rt.red tt'
            obtain ⟨tg, eg⟩ := WhRed.preserve facts roots formed rs.red ts'
            have d₂ := Algorithmic.converts facts roots heads algebra d₁
              (.snoc (CtxEq.refl Δ formed) eAσ) formedA
              (IsType.refl ⟨_, hB', Typed.ctxBelow tB' (TypeEq.below eAσ)⟩)
            have d₃ := ihB (typed.lift A) formedA (apply tf) (apply tg) d₂
            exact .terms (RedTy.refl ⟨u, hu, tPiσ⟩) (.inr (.inl ⟨_, _, rfl⟩))
              ⟨rt.red, tt', tf, ef⟩ ⟨rs.red, ts', tg, eg⟩ (.eta ⟨_, hA, tA⟩ tf funF tg funG d₃)
        | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_pi
  case sigma =>
    intro n Γ A A' B B' u u' tS hu tS' hu' _ _ ihA ihB m Δ σ typed formed t s tt ts d
    have tSσ : Typed S.R Δ (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B))
        (.head u) := tS.substitute typed
    obtain ⟨_, ⟨_, hB, tB⟩⟩ := IsType.sigma_parts ⟨u, hu, tSσ⟩
    have tt' : Typed S.R Δ t
        (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) := tt
    have ts' : Typed S.R Δ s
        (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) := ts
    have d' : Algorithmic S.R S.roles
        (.terms Δ t s (.sigma (Presentation.subst σ A') (Presentation.subst (liftSub σ) B'))) := d
    cases d' with
    | @terms _ _ _ p _ q _ _ rA fA rt rs dW =>
        obtain rfl := WhRed.eq_of_whnf (sigma_whnf S.shape _ _) rA.red
        cases dW with
        | sigmaEta _ pairP _ pairQ dFst dSnd =>
            obtain ⟨tp, ep⟩ := WhRed.preserve facts roots formed rt.red tt'
            obtain ⟨tq, eq⟩ := WhRed.preserve facts roots formed rs.red ts'
            have dFst' := ihA typed formed (.fstElim tp) (.fstElim tq) dFst
            have typedCons : SubstMor S.R (.snoc Γ A) Δ (consSub (.fst p) σ) := by
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · show Typed S.R Δ (.fst p)
                  (Presentation.subst (consSub (.fst p) σ) (Presentation.rename wk A))
                rw [subst_rename_wk]
                exact .fstElim tp
              · show Typed S.R Δ (σ j)
                  (Presentation.subst (consSub (.fst p) σ) (Presentation.rename wk (Ctx.lookup Γ j)))
                rw [subst_rename_wk]
                exact typed j
            -- The right pair's second projection, at the left pair's first projection.
            have eFst : Equal S.R Δ (.fst p) (.fst q) (Presentation.subst σ A) :=
              Algorithmic.sound_terms facts roots heads algebra formed dFst'
            have eB : TypeEq S.R Δ (inst0 (.fst q) (Presentation.subst (liftSub σ) B))
                (inst0 (.fst p) (Presentation.subst (liftSub σ) B)) :=
              (TypeEq.of_instantiateEq tB hB (.fstElim tp) eFst).symm
            have tSndP : Typed S.R Δ (.snd p)
                (inst0 (.fst p) (Presentation.subst (liftSub σ) B)) := .sndElim tp
            have tSndQ : Typed S.R Δ (.snd q)
                (inst0 (.fst p) (Presentation.subst (liftSub σ) B)) :=
              Typed.convType (.sndElim tq) eB
            rw [inst0_subst_liftSub] at dSnd tSndP tSndQ
            have dSnd' := ihB typedCons formed tSndP tSndQ dSnd
            rw [← inst0_subst_liftSub] at dSnd'
            exact .terms (RedTy.refl ⟨u, hu, tSσ⟩) (.inr (.inr (.inl ⟨_, _, rfl⟩)))
              ⟨rt.red, tt', tp, ep⟩ ⟨rs.red, ts', tq, eq⟩
              (.sigmaEta tp pairP tq pairQ dFst' dSnd')
        | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_sigma
  case trans =>
    intro n Γ A B C le₁ _ ih₁ ih₂ m Δ σ typed formed t s tt ts d
    have below₁ : Below S.R Δ (Presentation.subst σ A) (Presentation.subst σ B) :=
      Derivable.substitutes le₁ typed
    exact ih₁ typed formed tt ts (ih₂ typed formed (.sub tt below₁) (.sub ts below₁) d)

/-- A comparison at a type, of terms of a type below it, is one at the smaller
type. -/
theorem Algorithmic.terms_down_here {n : Nat} {Δ : Ctx Head n} {A B t u : Tm Head n}
    (le : Below S.R Δ A B) (formed : CtxFormed S.R Δ) (tt : Typed S.R Δ t A)
    (tu : Typed S.R Δ u A) (derivation : Algorithmic S.R S.roles (.terms Δ t u B)) :
    Algorithmic S.R S.roles (.terms Δ t u A) := by
  have d := Algorithmic.terms_down facts roots heads algebra le
    (CtxEq.substMor (CtxEq.refl Δ formed)) formed (t := t) (u := u) (by rwa [subst_ids])
    (by rwa [subst_ids]) (by rwa [subst_ids])
  rwa [subst_ids] at d

/-- **The laws of the generic equality hold for the algorithmic equality**, given
the facts about weak-head forms of types, the package's preservation of typing
by root and head steps, its cumulativity order, and the lifting of spine
comparisons. -/
theorem algorithmic_laws (lift : SpineLift S) : (algorithmic S.R S.roles).Laws S.R S.roles where
  convTy_sound := fun h => h.1
  convTm_sound := fun h => h.1
  convNe_sound := fun h => h.1
  convTy_of_convTm := fun h hu =>
    algorithmic_convTy_of_convTm h hu
  convTm_of_convNe := fun lt lu h =>
    algorithmic_convTm_of_convNe lift lt lu h
  convTy_symm := fun h => ⟨h.1.symm, fun _ _ _ cr formed =>
    Algorithmic.symmetric facts roots heads algebra (h.2 cr formed)
      (CtxEq.refl _ formed) formed⟩
  convTy_trans := fun h₁ h₂ => ⟨TypeEq.trans S.levels h₁.1 h₂.1, fun _ _ _ cr formed =>
    Algorithmic.transitive facts roots heads algebra (h₁.2 cr formed) formed
      (h₂.2 cr formed)⟩
  convTm_symm := fun h => ⟨.symm h.1, fun _ _ _ cr formed => by
    have d := h.2 cr formed
    have isA := Typed.isType d.terms_typed.1 formed
    exact Algorithmic.symmetric facts roots heads algebra d (CtxEq.refl _ formed) formed
      isA.refl⟩
  convTm_trans := fun h₁ h₂ => ⟨.trans h₁.1 h₂.1, fun _ _ _ cr formed =>
    Algorithmic.transitive facts roots heads algebra (h₁.2 cr formed) formed
      (h₂.2 cr formed)⟩
  convNe_symm := fun h => ⟨.symm h.1, fun _ _ _ cr formed => by
    obtain ⟨U, d, le⟩ := h.2 cr formed
    obtain ⟨U', d', e⟩ := Algorithmic.symmetric facts roots heads algebra d
      (CtxEq.refl _ formed) formed
    exact ⟨U', d', (TypeEq.toLe e.symm).trans le⟩⟩
  convNe_trans := fun h₁ h₂ => ⟨.trans h₁.1 h₂.1, fun _ _ _ cr formed => by
    obtain ⟨U, d₁, le⟩ := h₁.2 cr formed
    obtain ⟨_, d₂, _⟩ := h₂.2 cr formed
    exact ⟨U, Algorithmic.transitive facts roots heads algebra d₁ formed d₂, le⟩⟩
  convTm_cumul := fun h c => ⟨.cumulEq h.1 c, fun _ _ _ cr formed =>
    Algorithmic.terms_cumul (h.2 cr formed) c⟩
  convTm_below := fun h le => ⟨.subEq h.1 le, fun _ _ _ cr formed =>
    Algorithmic.terms_below_here facts roots heads algebra (Derivable.renames le cr) formed
      (h.2 cr formed)⟩
  convNe_cumul := fun h c => ⟨.cumulEq h.1 c, fun _ _ _ cr formed => by
    obtain ⟨U, d, le⟩ := h.2 cr formed
    exact ⟨U, d, le.trans (TypeLe.of_cumulative c)⟩⟩
  convNe_below := fun h below => ⟨.subEq h.1 below, fun _ _ _ cr formed => by
    obtain ⟨U, d, le⟩ := h.2 cr formed
    exact ⟨U, d, le.trans (.sub (Derivable.renames below cr) (.refl _))⟩⟩
  convTm_conv := fun h e => ⟨Equal.convType h.1 e, fun _ _ _ cr formed =>
    Algorithmic.converts facts roots heads algebra (h.2 cr formed) (CtxEq.refl _ formed)
      formed (e.rename cr)⟩
  convNe_conv := fun h e => ⟨Equal.convType h.1 e, fun _ _ _ cr formed => by
    obtain ⟨U, d, le⟩ := h.2 cr formed
    exact ⟨U, d, le.trans (e.rename cr).toLe⟩⟩
  convTy_rename := fun cr _ h => ⟨h.1.rename cr, fun _ _ _ cr' formed' => by
    have d := h.2 (CtxRen.comp cr cr') formed'
    rw [rename_rename, rename_rename]
    exact d⟩
  convTm_rename := fun cr _ h => ⟨h.1.rename cr, fun _ _ _ cr' formed' => by
    have d := h.2 (CtxRen.comp cr cr') formed'
    rw [rename_rename, rename_rename, rename_rename]
    exact d⟩
  convNe_rename := fun cr _ h => ⟨h.1.rename cr, fun _ _ _ cr' formed' => by
    obtain ⟨U, d, le⟩ := h.2 (CtxRen.comp cr cr') formed'
    rw [rename_rename, rename_rename, rename_rename]
    exact ⟨U, d, le⟩⟩
  convTy_expand := fun rA rB h => ⟨TypeEq.trans S.levels rA.typeEq
      (TypeEq.trans S.levels h.1 rB.typeEq.symm), fun _ _ _ cr formed => by
    cases h.2 cr formed with
    | types rA' rB' fA fB d =>
        exact .types (RedTy.trans S.levels (rA.rename cr) rA') (RedTy.trans S.levels (rB.rename cr) rB')
          fA fB d⟩
  convTm_expand := fun rt ru h => ⟨.trans rt.equal (.trans h.1 (.symm ru.equal)),
    fun _ _ _ cr formed => by
      cases h.2 cr formed with
      | terms rA fA rt' ru' d =>
          exact .terms rA fA (RedTm.trans ((rt.rename cr).conv rA.typeEq) rt')
            (RedTm.trans ((ru.rename cr).conv rA.typeEq) ru') d⟩
  convTy_head := fun same tA tB hu => ⟨⟨_, hu, headEquality same tA tB⟩, fun _ _ _ cr _ =>
    .types (RedTy.refl ⟨_, hu, tA.rename cr⟩) (RedTy.refl ⟨_, hu, tB.rename cr⟩) (.inl ⟨_, rfl⟩)
      (.inl ⟨_, rfl⟩) (.heads same (tA.rename cr) (tB.rename cr) hu)⟩
  convTm_head := fun same tA tB hu => ⟨headEquality same tA tB, fun _ _ _ cr _ =>
    .terms (RedTy.refl (universe_isType hu)) (.inl ⟨_, rfl⟩) (RedTm.refl (tA.rename cr))
      (RedTm.refl (tB.rename cr))
      (.univ hu (tA.rename cr) (tB.rename cr) (.heads same (tA.rename cr) (tB.rename cr) hu))⟩
  convTy_pi := fun isA h₁ h₂ => by
    have decl := (declarative_laws S.roles S.levels).convTy_pi isA h₁.1 h₂.1
    refine ⟨decl, fun _ Δ ρ cr formed => ?_⟩
    have isA' := isA.rename cr
    obtain ⟨u, hu, e⟩ := decl.rename cr
    obtain ⟨tPi, tPi'⟩ := Equal.typed e formed
    exact .types (RedTy.refl ⟨u, hu, tPi⟩) (RedTy.refl ⟨u, hu, tPi'⟩) (.inr (.inl ⟨_, _, rfl⟩))
      (.inr (.inl ⟨_, _, rfl⟩))
      (.pi isA' (h₁.2 cr formed) (h₂.2 (CtxRen.snoc cr _) (.snoc formed isA')))
  convTy_sigma := fun isA h₁ h₂ => by
    have decl := (declarative_laws S.roles S.levels).convTy_sigma isA h₁.1 h₂.1
    refine ⟨decl, fun _ Δ ρ cr formed => ?_⟩
    have isA' := isA.rename cr
    obtain ⟨u, hu, e⟩ := decl.rename cr
    obtain ⟨tS, tS'⟩ := Equal.typed e formed
    exact .types (RedTy.refl ⟨u, hu, tS⟩) (RedTy.refl ⟨u, hu, tS'⟩) (.inr (.inr (.inl ⟨_, _, rfl⟩)))
      (.inr (.inr (.inl ⟨_, _, rfl⟩)))
      (.sigma isA' (h₁.2 cr formed) (h₂.2 (CtxRen.snoc cr _) (.snoc formed isA')))
  convTy_id := fun h₁ hx hy => by
    have decl := (declarative_laws S.roles S.levels).convTy_id h₁.1 hx.1 hy.1
    refine ⟨decl, fun _ Δ ρ cr formed => ?_⟩
    obtain ⟨u, hu, e⟩ := decl.rename cr
    obtain ⟨tI, tI'⟩ := Equal.typed e formed
    exact .types (RedTy.refl ⟨u, hu, tI⟩) (RedTy.refl ⟨u, hu, tI'⟩)
      (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))
      (.id (h₁.2 cr formed) (hx.2 cr formed) (hy.2 cr formed))
  convTm_pi := fun tA hu h₁ h₂ hv join => by
    have decl := (declarative_laws S.roles S.levels).convTm_pi tA hu h₁.1 h₂.1 hv join
    refine ⟨decl, fun _ Δ ρ cr formed => ?_⟩
    have hw := (S.levels.join_level join).1
    have isA' : IsType S.R Δ _ := ⟨_, hu, tA.rename cr⟩
    obtain ⟨tPi, tPi'⟩ := Equal.typed (decl.rename cr) formed
    exact .terms (RedTy.refl (universe_isType hw)) (.inl ⟨_, rfl⟩) (RedTm.refl tPi)
      (RedTm.refl tPi') (.univ hw tPi tPi' (.pi isA' (Algorithmic.types_of_universe hu
        (h₁.2 cr formed)) (Algorithmic.types_of_universe hv
          (h₂.2 (CtxRen.snoc cr _) (.snoc formed isA')))))
  convTm_sigma := fun tA hu h₁ h₂ hv join => by
    have decl := (declarative_laws S.roles S.levels).convTm_sigma tA hu h₁.1 h₂.1 hv join
    refine ⟨decl, fun _ Δ ρ cr formed => ?_⟩
    have hw := (S.levels.join_level join).1
    have isA' : IsType S.R Δ _ := ⟨_, hu, tA.rename cr⟩
    obtain ⟨tS, tS'⟩ := Equal.typed (decl.rename cr) formed
    exact .terms (RedTy.refl (universe_isType hw)) (.inl ⟨_, rfl⟩) (RedTm.refl tS)
      (RedTm.refl tS') (.univ hw tS tS' (.sigma isA' (Algorithmic.types_of_universe hu
        (h₁.2 cr formed)) (Algorithmic.types_of_universe hv
          (h₂.2 (CtxRen.snoc cr _) (.snoc formed isA')))))
  convTm_id := fun h₁ hu hx hy => by
    have decl := (declarative_laws S.roles S.levels).convTm_id h₁.1 hu hx.1 hy.1
    refine ⟨decl, fun _ Δ ρ cr formed => ?_⟩
    obtain ⟨tI, tI'⟩ := Equal.typed (decl.rename cr) formed
    exact .terms (RedTy.refl (universe_isType hu)) (.inl ⟨_, rfl⟩) (RedTm.refl tI)
      (RedTm.refl tI') (.univ hu tI tI' (.id (Algorithmic.types_of_universe hu (h₁.2 cr formed))
        (hx.2 cr formed) (hy.2 cr formed)))
  convTm_etaPi := fun isA _ tf funF tg funG h => by
    refine ⟨.etaPi tf tg h.1, fun _ Δ ρ cr formed => ?_⟩
    have isA' := isA.rename cr
    have d := h.2 (CtxRen.snoc cr _) (.snoc formed isA')
    rw [rename_liftRen_appFresh, rename_liftRen_appFresh] at d
    have tf' := tf.rename cr
    have tg' := tg.rename cr
    exact .terms (RedTy.refl (Typed.isType tf' formed)) (.inr (.inl ⟨_, _, rfl⟩))
      (RedTm.refl tf') (RedTm.refl tg') (.eta isA' tf' (funF.rename ρ) tg' (funG.rename ρ) d)
  convTm_etaSigma := fun _ _ tp pairP tq pairQ h₁ h₂ => by
    refine ⟨.etaSigma tp tq h₁.1 h₂.1, fun _ Δ ρ cr formed => ?_⟩
    have d₂ := h₂.2 cr formed
    rw [rename_inst0] at d₂
    have tp' := tp.rename cr
    have tq' := tq.rename cr
    exact .terms (RedTy.refl (Typed.isType tp' formed))
      (.inr (.inr (.inl ⟨_, _, rfl⟩))) (RedTm.refl tp') (RedTm.refl tq')
      (.sigmaEta tp' (pairP.rename ρ) tq' (pairQ.rename ρ) (h₁.2 cr formed) d₂)
  convTm_refl := fun h => by
    refine ⟨.reflCong h.1, fun _ Δ ρ cr formed => ?_⟩
    obtain ⟨t₁, t₂⟩ := Equal.typed (Equal.rename (Derivable.reflCong h.1) cr) formed
    exact .terms (RedTy.refl (Typed.isType t₁ formed))
      (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (RedTm.refl t₁) (RedTm.refl t₂)
      (.refl t₁ t₂ (h.2 cr formed))
  convNe_var := fun i typing => by
    refine ⟨.refl typing, fun _ Δ ρ cr _ => ?_⟩
    have le : TypeLe S.R _ (Ctx.lookup _ i) _ := Typed.generation typing
    refine ⟨_, .var (ρ i), ?_⟩
    rw [cr i]
    exact TypeLe.rename le cr
  convNe_const := fun c typing => by
    refine ⟨.refl typing, fun _ Δ ρ cr _ => ?_⟩
    obtain ⟨type, u, declared, typedType, hu, le⟩ := Typed.generation typing
    refine ⟨_, .const declared (.const declared typedType hu), ?_⟩
    have le' := TypeLe.rename le cr
    rwa [rename_liftClosed] at le'
  convNe_app := fun hf ha => by
    refine ⟨.appCong hf.1 ha.1, fun _ Δ ρ cr formed => ?_⟩
    obtain ⟨U, dU, le⟩ := hf.2 cr formed
    obtain ⟨tf, _⟩ := Equal.typed (hf.1.rename cr) formed
    obtain ⟨A₂, B₂, dW, eA, leB⟩ := Algorithmic.spinesW_pi facts roots heads algebra formed
      dU le (Typed.isType tf formed)
    have da := Algorithmic.converts facts roots heads algebra (ha.2 cr formed)
      (CtxEq.refl _ formed) formed eA
    obtain ⟨ta, _⟩ := Equal.typed (ha.1.rename cr) formed
    refine ⟨_, .app dW da, ?_⟩
    rw [rename_inst0]
    exact .sub (Derivable.substitutes leB (SubstMor.single ta)) (.refl _)
  convNe_fst := fun h => by
    refine ⟨.fstCong h.1, fun _ Δ ρ cr formed => ?_⟩
    obtain ⟨U, dU, le⟩ := h.2 cr formed
    obtain ⟨tp, _⟩ := Equal.typed (h.1.rename cr) formed
    obtain ⟨A₂, B₂, dW, leA, _⟩ := Algorithmic.spinesW_sigma facts roots heads algebra
      formed dU le (Typed.isType tp formed)
    exact ⟨_, .fst dW, .sub leA (.refl _)⟩
  convNe_snd := fun h => by
    refine ⟨.sndCong h.1, fun _ Δ ρ cr formed => ?_⟩
    obtain ⟨U, dU, le⟩ := h.2 cr formed
    obtain ⟨tp, _⟩ := Equal.typed (h.1.rename cr) formed
    obtain ⟨A₂, B₂, dW, _, leB⟩ := Algorithmic.spinesW_sigma facts roots heads algebra
      formed dU le (Typed.isType tp formed)
    obtain ⟨tW, _⟩ := Algorithmic.sound facts roots heads algebra dW formed
    refine ⟨_, .snd dW, ?_⟩
    rw [rename_inst0]
    exact .sub (Derivable.substitutes leB (SubstMor.single (.fstElim tW))) (.refl _)

end Laws

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
