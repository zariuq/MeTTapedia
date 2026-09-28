import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Transitivity

/-!
# Lifting spine comparisons to comparisons at a type

A neutral term, a constructor spine or the type constant of an inductive type,
compared as a spine in every formed world, is compared at its type: at a
dependent function type through its applications to a fresh variable, at a
dependent pair type through its projections, at a universe as a type, and
elsewhere as a spine (`SpineLift`). The laws of the algorithmic equality take
this property as an input. For a setting whose declared constants are semantic
it holds (`SpineLift.ofSemantic`), by induction on the reducibility of the type,
which supplies the codomain at the fresh variable.

The reductions of a spine comparison to the weak-head form of its type use only
the facts about weak-head forms of types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Renamings and worlds -/

theorem inst0_var_rename_liftRen_comp {n m : Nat} (ρ : Ren (n + 1) m) (B : Tm Head (n + 1)) :
    inst0 (.var (ρ 0)) (Presentation.rename (liftRen (fun i => ρ (wk i))) B) =
      Presentation.rename ρ B := by
  unfold inst0
  rw [subst_rename, ← subst_renSub]
  apply subst_ext
  intro i
  refine Fin.cases rfl (fun j => rfl) i

theorem World.self {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    World S Γ Γ idRen :=
  ⟨CtxRen.id Γ, formed⟩

theorem World.fresh {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (formed : CtxFormed S.R Γ)
    (isA : IsType S.R Γ A) : World S Γ (.snoc Γ A) wk :=
  ⟨CtxRen.wk Γ A, .snoc formed isA⟩

/-! ## Spines in every world -/

/-- Terms whose renamings into every formed world are compared as spines, at a
type below the renamed type. -/
def SpinesEverywhere (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (t u A : Tm Head n) : Prop :=
  ∀ ⦃m : Nat⦄ ⦃Δ : Ctx Head m⦄ ⦃ρ : Ren n m⦄, World S Γ Δ ρ →
    ∃ U, Algorithmic S.R S.roles
        (.spines Δ (Presentation.rename ρ t) (Presentation.rename ρ u) U) ∧
      TypeLe S.R Δ U (Presentation.rename ρ A)

theorem SpinesEverywhere.here {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (spines : SpinesEverywhere S Γ t u A) (formed : CtxFormed S.R Γ) :
    ∃ U, Algorithmic S.R S.roles (.spines Γ t u U) ∧ TypeLe S.R Γ U A := by
  obtain ⟨U, d, le⟩ := spines (World.self formed)
  simp only [rename_id] at d le
  exact ⟨U, d, le⟩

theorem SpinesEverywhere.rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {t u A : Tm Head n} (spines : SpinesEverywhere S Γ t u A) (w : World S Γ Δ ρ) :
    SpinesEverywhere S Δ (Presentation.rename ρ t) (Presentation.rename ρ u)
      (Presentation.rename ρ A) := by
  intro k Θ ρ' w'
  obtain ⟨U, d, le⟩ := spines (w.comp w')
  rw [rename_rename, rename_rename, rename_rename]
  exact ⟨U, d, le⟩

theorem SpinesEverywhere.var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
    SpinesEverywhere S Γ (.var i) (.var i) (Ctx.lookup Γ i) := by
  intro m Δ ρ w
  refine ⟨_, .var (ρ i), ?_⟩
  rw [w.1 i]
  exact .refl _

/-! ## Shapes of liftable terms -/

theorem constSpine_cases {n : Nat} (c : DeclName) :
    ∀ (args : List (Tm Head n)), appSpine (.const c) args = .const c ∨
      ∃ f a, appSpine (.const c) args = .app f a := by
  have general : ∀ (args : List (Tm Head n)) {f : Tm Head n},
      (f = .const c ∨ ∃ g a, f = .app g a) →
        (appSpine f args = .const c ∨ ∃ g a, appSpine f args = .app g a) := by
    intro args
    induction args with
    | nil => intro f shape; exact shape
    | cons a args ih => intro f _; exact ih (.inr ⟨f, a, rfl⟩)
  intro args
  exact general args (.inl rfl)

theorem Liftable.whnf {n : Nat} {t : Tm Head n} (lifted : Liftable S.roles t) :
    Whnf S.R S.roles t := by
  rcases lifted with neutral | ⟨k, arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
  · exact neutral.whnf S.shape
  · exact canonical_whnf S.shape (.inr ⟨k, arity, args, role, rfl⟩)
  · exact inductive_whnf S.shape role

theorem Liftable.not_refl {roles : Roles Head} {n : Nat} {x : Tm Head n} :
    ¬ Liftable roles (.refl x) := by
  rintro (neutral | ⟨k, _, args, _, e⟩ | ⟨_, _, _, e⟩)
  · exact neutral.ne_refl rfl
  · rcases constSpine_cases k args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
  · cases e

theorem ctorSpine_not_typeForm {roles : Roles Head} {n : Nat} {k : DeclName} {arity : Nat}
    {args : List (Tm Head n)} (role : roles k = .constructor arity) :
    ¬ IsTypeForm roles (appSpine (.const k) args) := by
  rintro (⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | neutral | ⟨T, _, role', e⟩)
  · rcases constSpine_cases k args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
  · rcases constSpine_cases k args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
  · rcases constSpine_cases k args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
  · rcases constSpine_cases k args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
  · exact neutral.not_canonical (.inr ⟨k, arity, args, role, rfl⟩)
  · rcases constSpine_cases k args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e
    · cases e
      rw [role] at role'
      cases role'
    · cases e

theorem Liftable.not_pair {roles : Roles Head} {n : Nat} {a b : Tm Head n} :
    ¬ Liftable roles (.pair a b) := by
  rintro (neutral | ⟨k, _, args, _, e⟩ | ⟨_, _, _, e⟩)
  · exact neutral.ne_pair rfl
  · rcases constSpine_cases k args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
  · cases e

theorem rename_liftRen_idRen {n : Nat} (B : Tm Head (n + 1)) :
    Presentation.rename (liftRen idRen) B = B := by
  have same : (liftRen idRen : Ren (n + 1) (n + 1)) = idRen := by
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  rw [same, rename_id]

theorem TypeEq.toLe {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (equal : TypeEq R Γ A B) : TypeLe R Γ A B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .conv e hu (.refl _)

/-- A liftable function applied to a fresh variable is liftable. -/
theorem Liftable.appFresh {n : Nat} {t : Tm Head n} (lifted : Liftable S.roles t)
    (function : IsFun S.roles t) :
    Liftable S.roles (.app (Presentation.rename wk t) (.var 0)) := by
  rcases lifted with neutral | ⟨k, arity, args, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
  · exact .inl (.app (neutral.rename wk))
  · refine .inr (.inl ⟨k, arity, args.map (Presentation.rename wk) ++ [.var 0], role, ?_⟩)
    rw [appSpine_concat, rename_appSpine]
    rfl
  · exfalso
    rcases function with ⟨_, e⟩ | neutral | ⟨c, args, arity, role', _, e⟩
    · cases e
    · exact neutral.ne_inductive role rfl
    · rcases constSpine_cases c args with e' | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
      rcases role' with r | ⟨_, r⟩ <;> rw [r] at role <;> cases role

section Lift

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include facts roots heads algebra

omit roots heads algebra in
/-- A type below a universe that is equal to a head: the head is a universe. -/
theorem TypeLe.head_universe {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {X Y : Tm Head n} (le : TypeLe S.R Γ X Y) :
    ∀ {v u : Head}, TypeEq S.R Γ X (.head v) → Y = .head u → S.R.isUniverse u →
      S.R.isUniverse v := by
  intro v u equal eY hu
  subst eY
  have typeU := IsType.head_of_universe (Γ := Γ) hu
  obtain ⟨w, hw, eX, _⟩ := Below.universe_target facts (TypeLe.toBelow le typeU) formed hu
    (IsType.refl typeU)
  exact (HeadSame.level S.levels (TypeEq.head_injective facts
    (TypeEq.trans S.levels equal.symm eX) formed)).1.mpr hw

omit roots heads algebra in
/-- A type form below a universe is a universe. -/
theorem TypeLe.universe_form {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {X : Tm Head n} {u : Head} (le : TypeLe S.R Γ X (.head u)) (hu : S.R.isUniverse u)
    (isX : IsType S.R Γ X) (form : IsTypeForm S.roles X) :
    ∃ v, X = .head v ∧ S.R.isUniverse v := by
  have typeU := IsType.head_of_universe (Γ := Γ) hu
  obtain ⟨w, hw, eX, _⟩ := Below.universe_target facts (TypeLe.toBelow le typeU) formed hu
    (IsType.refl typeU)
  rcases form with ⟨v, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | ⟨C, a, b, rfl⟩ | neutral |
    ⟨T, ctors, role, rfl⟩
  · exact ⟨v, rfl, (HeadSame.level S.levels (TypeEq.head_injective facts eX formed)).1.mpr
      hw⟩
  · exact absurd eX (TypeEq.pi_ne_head facts formed)
  · exact absurd eX (TypeEq.sigma_ne_head facts formed)
  · exact absurd eX (TypeEq.id_ne_head facts formed)
  · exact ((TypeEq.neutral_form facts eX formed neutral (.inl ⟨w, rfl⟩)).not_former.1 w
      rfl).elim
  · exact absurd eX (TypeEq.inductive_ne_head facts role formed)

/-- A spine comparison, reduced to the weak-head form of its type. -/
theorem Algorithmic.spinesW_of_spines {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {t u U : Tm Head n} (derivation : Algorithmic S.R S.roles (.spines Γ t u U)) :
    ∃ U', Algorithmic S.R S.roles (.spinesW Γ t u U') ∧ TypeEq S.R Γ U U' ∧
      IsTypeForm S.roles U' := by
  obtain ⟨tt, _, _⟩ := Algorithmic.sound facts roots heads algebra derivation formed
  obtain ⟨U', rU, fU⟩ :=
    facts.typeForm (Typed.isType tt formed) formed
  exact ⟨U', .spinesW derivation rU fU, rU.typeEq, fU⟩

/-- A spine comparison at a type below a dependent function type, reduced to a
dependent function type with an equal domain and a codomain usable at the
other's. -/
theorem Algorithmic.spinesW_pi {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {t u U A : Tm Head n} {B : Tm Head (n + 1)}
    (derivation : Algorithmic S.R S.roles (.spines Γ t u U)) (le : TypeLe S.R Γ U (.pi A B))
    (isPi : IsType S.R Γ (.pi A B)) :
    ∃ A₂ B₂, Algorithmic S.R S.roles (.spinesW Γ t u (.pi A₂ B₂)) ∧ TypeEq S.R Γ A A₂ ∧
      Below S.R (.snoc Γ A) B₂ B := by
  obtain ⟨U', d, eU, fU⟩ :=
    Algorithmic.spinesW_of_spines facts roots heads algebra formed derivation
  obtain ⟨A₀, B₀, e₀, eA₀, leB₀⟩ := Below.pi_inv facts
    (TypeLe.toBelow ((eU.symm).toLe.trans le) isPi) formed (IsType.refl isPi)
  obtain ⟨A₂, B₂, rfl, eA₂, eB₂⟩ :=
    (facts.forms e₀.symm formed (.inr (.inl ⟨_, _, rfl⟩)) fU).pi_left
  have codomain : Below S.R (.snoc Γ A₀) B₂ B := .subTrans eB₂.symm.below leB₀
  exact ⟨A₂, B₂, d, TypeEq.trans S.levels eA₀.symm eA₂, Below.ctxConv codomain eA₀⟩

/-- A spine comparison at a type below a dependent pair type, reduced to a
dependent pair type whose domain and codomain are usable at the other's. -/
theorem Algorithmic.spinesW_sigma {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {t u U A : Tm Head n} {B : Tm Head (n + 1)}
    (derivation : Algorithmic S.R S.roles (.spines Γ t u U)) (le : TypeLe S.R Γ U (.sigma A B))
    (isSigma : IsType S.R Γ (.sigma A B)) :
    ∃ A₂ B₂, Algorithmic S.R S.roles (.spinesW Γ t u (.sigma A₂ B₂)) ∧ Below S.R Γ A₂ A ∧
      Below S.R (.snoc Γ A₂) B₂ B := by
  obtain ⟨U', d, eU, fU⟩ :=
    Algorithmic.spinesW_of_spines facts roots heads algebra formed derivation
  obtain ⟨A₀, B₀, e₀, leA₀, leB₀⟩ := Below.sigma_inv facts
    (TypeLe.toBelow ((eU.symm).toLe.trans le) isSigma) formed (IsType.refl isSigma)
  obtain ⟨A₂, B₂, rfl, eA₂, eB₂⟩ :=
    (facts.forms e₀.symm formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) fU).sigma_left
  have codomain : Below S.R (.snoc Γ A₀) B₂ B := .subTrans eB₂.symm.below leB₀
  exact ⟨A₂, B₂, d, .subTrans eA₂.symm.below leA₀, Below.ctxConv codomain eA₂⟩

end Lift

/-! ## Lifting spine comparisons -/

/-- **Spine comparisons lift to comparisons at the type**: two liftable terms,
equal at a type of a formed context and compared as spines in every formed
world, are compared at that type. -/
def SpineLift (S : Setting Head L) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}, CtxFormed S.R Γ →
    Liftable S.roles t → Liftable S.roles u → Equal S.R Γ t u A →
    SpinesEverywhere S Γ t u A → Algorithmic S.R S.roles (.terms Γ t u A)

section LiftModel

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include laws constants roots heads algebra

/-- Spine comparisons in every world of liftable, reducibly equal terms of a
reducible type lift to comparisons at the type. -/
theorem LR.liftSpines {l : L} {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : LR S l (levelsBelow S l) Γ A P) :
    CtxFormed S.R Γ → ∀ {t u : Tm Head n}, Liftable S.roles t → Liftable S.roles u →
      P.eqTm t u → Typed S.R Γ t A → Typed S.R Γ u A →
      SpinesEverywhere S Γ t u A → Algorithmic S.R S.roles (.terms Γ t u A) := by
  have facts : FormFacts S.R S.roles := .ofSemantic laws constants
  have sound := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.sound facts roots heads algebra d
  have conv := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.converts facts roots heads algebra d
  induction reducible with
  | @sort n Γ A u isUniverse _ _ red =>
      intro formed t s lt ls equal tt ts spines
      obtain ⟨nf, nf', rt, rs, ft, fs, _⟩ := equal
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt.red).symm
      obtain rfl := (WhRed.eq_of_whnf ls.whnf rs.red).symm
      have tt' := Typed.convType tt red.typeEq
      have ts' := Typed.convType ts red.typeEq
      obtain ⟨U, dU, leU⟩ := spines.here formed
      obtain ⟨U', dW, eU, fU⟩ :=
        Algorithmic.spinesW_of_spines facts roots heads algebra formed dU
      have le' := (eU.symm).toLe.trans (leU.trans red.typeEq.toLe)
      obtain ⟨v, rfl, hv⟩ := TypeLe.universe_form facts formed le'
        isUniverse ((TypeEq.isType eU formed).2) fU
      rcases lt with nt | ⟨k, _, _, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
      · have ns : Neutral S.roles s := by
          rcases ls with ns | ⟨k, _, _, role, rfl⟩ | ⟨T, ctors, role, rfl⟩
          · exact ns
          · exact absurd fs (ctorSpine_not_typeForm role)
          · cases dU with
            | const => exact absurd rfl (nt.ne_inductive role)
        exact .terms red (.inl ⟨u, rfl⟩) (RedTm.refl tt') (RedTm.refl ts')
          (.univ isUniverse tt' ts' (.neutralTypes nt ns hv dW))
      · exact absurd ft (ctorSpine_not_typeForm role)
      · cases dU with
        | const =>
            exact .terms red (.inl ⟨u, rfl⟩) (RedTm.refl tt') (RedTm.refl ts')
              (.univ isUniverse tt' ts' (.inductiveType role ⟨u, isUniverse, tt'⟩))
  | @neutral n Γ A ty v red neutral _ _ _ =>
      intro formed t s lt ls equal tt ts spines
      obtain ⟨nf, nf', rt, rs, nt, ns, _⟩ := equal
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt.red).symm
      obtain rfl := (WhRed.eq_of_whnf ls.whnf rs.red).symm
      have tt' := Typed.convType tt red.typeEq
      have ts' := Typed.convType ts red.typeEq
      obtain ⟨U, dU, _⟩ := spines.here formed
      obtain ⟨_, dW, _, _⟩ :=
        Algorithmic.spinesW_of_spines facts roots heads algebra formed dU
      exact .terms red (.inr (.inr (.inr (.inr (.inl neutral))))) (RedTm.refl tt') (RedTm.refl ts')
        (.spine (.inr (.inl neutral)) (.inl nt) (.inl ns) tt' ts' dW)
  | @ground n Γ A h v notUniverse red _ _ =>
      intro formed t s lt ls equal tt ts spines
      obtain ⟨nf, nf', rt, rs, nt, ns, _⟩ := equal
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt.red).symm
      obtain rfl := (WhRed.eq_of_whnf ls.whnf rs.red).symm
      have tt' := Typed.convType tt red.typeEq
      have ts' := Typed.convType ts red.typeEq
      obtain ⟨U, dU, _⟩ := spines.here formed
      obtain ⟨_, dW, _, _⟩ :=
        Algorithmic.spinesW_of_spines facts roots heads algebra formed dU
      exact .terms red (.inl ⟨h, rfl⟩) (RedTm.refl tt') (RedTm.refl ts')
        (.spine (.inr (.inr (.inr ⟨h, rfl, notUniverse⟩))) (.inl nt) (.inl ns) tt' ts' dW)
  | @ident n Γ A ty lhs rhs red _ _ _ _ _ _ _ _ _ _ =>
      intro formed t s lt ls equal tt ts spines
      obtain ⟨nf, nf', rt, rs, _, props⟩ := equal
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt.red).symm
      obtain rfl := (WhRed.eq_of_whnf ls.whnf rs.red).symm
      obtain ⟨nt, ns⟩ : Neutral S.roles t ∧ Neutral S.roles s := by
        rcases props with ⟨x, x', rfl, _⟩ | ⟨nt, ns, _⟩
        · exact absurd lt Liftable.not_refl
        · exact ⟨nt, ns⟩
      have tt' := Typed.convType tt red.typeEq
      have ts' := Typed.convType ts red.typeEq
      obtain ⟨U, dU, _⟩ := spines.here formed
      obtain ⟨_, dW, _, _⟩ :=
        Algorithmic.spinesW_of_spines facts roots heads algebra formed dU
      exact .terms red (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (RedTm.refl tt') (RedTm.refl ts')
        (.spine (.inl ⟨_, _, _, rfl⟩) (.inl nt) (.inl ns) tt' ts' dW)
  | @inductiveType n Γ A T ctors u red role _ _ _ _ _ =>
      intro formed t s lt ls equal tt ts spines
      obtain ⟨rt, rs, _, normal⟩ := equal
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt.red).symm
      obtain rfl := (WhRed.eq_of_whnf ls.whnf rs.red).symm
      obtain ⟨ft, fs⟩ : SpineForm S.roles t ∧ SpineForm S.roles s := by
        cases normal with
        | ctor mem _ =>
            exact ⟨.inr ⟨_, _, _, S.constructors.arity role mem, rfl⟩,
              .inr ⟨_, _, _, S.constructors.arity role mem, rfl⟩⟩
        | neutral nt ns _ => exact ⟨.inl nt, .inl ns⟩
      have tt' := Typed.convType tt red.typeEq
      have ts' := Typed.convType ts red.typeEq
      obtain ⟨U, dU, _⟩ := spines.here formed
      obtain ⟨_, dW, _, _⟩ :=
        Algorithmic.spinesW_of_spines facts roots heads algebra formed dU
      exact .terms red (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩))))) (RedTm.refl tt')
        (RedTm.refl ts') (.spine (.inr (.inr (.inl ⟨T, ctors, role, rfl⟩))) ft fs tt' ts' dW)
  | @pi n Γ A dom cod red domType _ _ P domAdequate codAdequate domIH codIH =>
      intro formed t s lt ls equal tt ts spines
      obtain ⟨_, _, nf, nf', rt, rs, funT, funS, _, apps⟩ := equal
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt.red).symm
      obtain rfl := (WhRed.eq_of_whnf ls.whnf rs.red).symm
      have tt' := Typed.convType tt red.typeEq
      have ts' := Typed.convType ts red.typeEq
      have w₀ : World S Γ (.snoc Γ dom) wk := World.fresh formed domType
      have tvar : Typed S.R (.snoc Γ dom) (.var 0) (Presentation.rename wk dom) := .var 0
      have h0 : (P.domPack w₀).redTm (.var 0) :=
        (LR.reflects laws (domAdequate w₀)).redTm (.var 0) tvar (laws.convNe_var 0 tvar)
      have tt₁ : Typed S.R (.snoc Γ dom) (.app (Presentation.rename wk t) (.var 0))
          (inst0 (.var 0) (Presentation.rename (liftRen wk) cod)) :=
        .appElim (tt'.rename (CtxRen.wk Γ dom)) tvar
      have ts₁ : Typed S.R (.snoc Γ dom) (.app (Presentation.rename wk s) (.var 0))
          (inst0 (.var 0) (Presentation.rename (liftRen wk) cod)) :=
        .appElim (ts'.rename (CtxRen.wk Γ dom)) tvar
      have spines₁ : SpinesEverywhere S (.snoc Γ dom) (.app (Presentation.rename wk t) (.var 0))
          (.app (Presentation.rename wk s) (.var 0))
          (inst0 (.var 0) (Presentation.rename (liftRen wk) cod)) := by
        intro m Θ ρ' w'
        have w'' : World S Γ Θ (fun i => ρ' (wk i)) := w₀.comp w'
        have formedΘ := w'.2
        obtain ⟨U, dU, leU⟩ := spines w''
        have eA := red.typeEq.rename w''.1
        obtain ⟨A₂, B₂, dW, eDom, leCod⟩ := Algorithmic.spinesW_pi facts roots heads
          algebra formedΘ dU (leU.trans eA.toLe) ((TypeEq.isType eA formedΘ).2)
        have lookupVar : Ctx.lookup Θ (ρ' 0) = Presentation.rename (fun i => ρ' (wk i)) dom := by
          rw [w'.1 0]
          exact rename_rename wk ρ' dom
        have tv : Typed S.R Θ (.var (ρ' 0)) (Presentation.rename (fun i => ρ' (wk i)) dom) := by
          rw [← lookupVar]
          exact .var _
        have ev := (LR.reflects laws (domAdequate w'')).eqTm (.var _) (.var _) tv tv
          (laws.convNe_var _ tv)
        have spinesVar : SpinesEverywhere S Θ (.var (ρ' 0)) (.var (ρ' 0))
            (Presentation.rename (fun i => ρ' (wk i)) dom) := by
          have base := SpinesEverywhere.var (S := S) (Γ := Θ) (ρ' 0)
          rw [lookupVar] at base
          exact base
        have dVar := domIH w'' formedΘ (.inl (.var _)) (.inl (.var _)) ev tv tv spinesVar
        have dVar' := conv dVar (CtxEq.refl Θ formedΘ) formedΘ eDom
        show ∃ U, Algorithmic S.R S.roles
            (.spines Θ (.app (Presentation.rename ρ' (Presentation.rename wk t)) (.var (ρ' 0)))
              (.app (Presentation.rename ρ' (Presentation.rename wk s)) (.var (ρ' 0))) U) ∧
          TypeLe S.R Θ U
            (Presentation.rename ρ' (inst0 (.var 0) (Presentation.rename (liftRen wk) cod)))
        rw [rename_rename, rename_rename, inst0_var_rename_liftRen_wk]
        refine ⟨_, .app dW dVar', ?_⟩
        have e := Derivable.substitutes leCod (SubstMor.single tv)
        change Below S.R Θ (inst0 (.var (ρ' 0)) B₂)
          (inst0 (.var (ρ' 0)) (Presentation.rename (liftRen (fun i => ρ' (wk i))) cod)) at e
        rw [inst0_var_rename_liftRen_comp] at e
        exact .sub e (.refl _)
      have d₁ := codIH w₀ h0 w₀.2 (lt.appFresh funT) (ls.appFresh funS) (apps w₀ h0) tt₁ ts₁
        spines₁
      rw [inst0_var_rename_liftRen_wk] at d₁
      exact .terms red (.inr (.inl ⟨_, _, rfl⟩)) (RedTm.refl tt') (RedTm.refl ts')
        (.eta domType tt' funT ts' funS d₁)
  | @sigma n Γ A dom cod red domType codType _ P domAdequate codAdequate domIH codIH =>
      intro formed t s lt ls equal tt ts spines
      obtain ⟨⟨nf₀, rt₀, _, _, first, _⟩, _, nf, nf', rt, rs, pairT, pairS, _, fsts, snds⟩ := equal
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt.red).symm
      obtain rfl := (WhRed.eq_of_whnf ls.whnf rs.red).symm
      obtain rfl := (WhRed.eq_of_whnf lt.whnf rt₀.red).symm
      obtain ⟨nt, ns⟩ : Neutral S.roles t ∧ Neutral S.roles s := by
        refine ⟨?_, ?_⟩
        · rcases pairT with ⟨a, b, rfl⟩ | nt
          · exact absurd lt Liftable.not_pair
          · exact nt
        · rcases pairS with ⟨a, b, rfl⟩ | ns
          · exact absurd ls Liftable.not_pair
          · exact ns
      have tt' := Typed.convType tt red.typeEq
      have ts' := Typed.convType ts red.typeEq
      have w₁ := World.self formed
      -- the first projections
      have spinesFst : SpinesEverywhere S Γ (.fst t) (.fst s) dom := by
        intro m Θ ρ w
        obtain ⟨U, dU, leU⟩ := spines w
        have eA := red.typeEq.rename w.1
        obtain ⟨A₂, B₂, dW, leDom, _⟩ := Algorithmic.spinesW_sigma facts roots heads
          algebra w.2 dU (leU.trans eA.toLe) ((TypeEq.isType eA w.2).2)
        exact ⟨_, .fst dW, .sub leDom (.refl _)⟩
      have dFst₀ := domIH w₁ formed (.inl (.fst (nt.rename idRen))) (.inl (.fst (ns.rename idRen)))
        (fsts w₁) (by simpa only [rename_id] using Derivable.fstElim tt')
        (by simpa only [rename_id] using Derivable.fstElim ts')
        (by simpa only [rename_id] using spinesFst)
      have dFst : Algorithmic S.R S.roles (.terms Γ (.fst t) (.fst s) dom) := by
        simpa only [rename_id] using dFst₀
      -- the second projections
      obtain ⟨v, hv, tCod⟩ := codType
      have eFst : Equal S.R Γ (.fst s) (.fst t) dom := .symm (sound dFst formed)
      have codEq : TypeEq S.R Γ (inst0 (.fst s) cod) (inst0 (.fst t) cod) :=
        TypeEq.of_instantiateEq tCod hv (.fstElim ts') eFst
      have spinesSnd : SpinesEverywhere S Γ (.snd t) (.snd s) (inst0 (.fst t) cod) := by
        intro m Θ ρ w
        obtain ⟨U, dU, leU⟩ := spines w
        have eA := red.typeEq.rename w.1
        obtain ⟨A₂, B₂, dW, _, leCod⟩ := Algorithmic.spinesW_sigma facts roots heads
          algebra w.2 dU (leU.trans eA.toLe) ((TypeEq.isType eA w.2).2)
        obtain ⟨tW, _⟩ := sound dW w.2
        refine ⟨_, .snd dW, ?_⟩
        rw [rename_inst0]
        exact .sub (Derivable.substitutes leCod (SubstMor.single (.fstElim tW))) (.refl _)
      have dSnd₀ := codIH w₁ (first w₁) formed (.inl (.snd (nt.rename idRen)))
        (.inl (.snd (ns.rename idRen))) (snds w₁ (first w₁))
        (by simpa only [rename_id, rename_liftRen_idRen] using Derivable.sndElim tt')
        (by simpa only [rename_id, rename_liftRen_idRen] using
          Typed.convType (Derivable.sndElim ts') codEq)
        (by simpa only [rename_id, rename_liftRen_idRen] using spinesSnd)
      have dSnd : Algorithmic S.R S.roles (.terms Γ (.snd t) (.snd s) (inst0 (.fst t) cod)) := by
        simpa only [rename_id, rename_liftRen_idRen] using dSnd₀
      exact .terms red (.inr (.inr (.inl ⟨_, _, rfl⟩))) (RedTm.refl tt') (RedTm.refl ts')
        (.sigmaEta tt' pairT ts' pairS dFst dSnd)

/-- **For a setting whose declared constants are semantic, spine comparisons
lift**, by induction on the reducibility of the type. -/
theorem SpineLift.ofSemantic : SpineLift S := by
  intro n Γ t u A formed lt lu equal spines
  obtain ⟨⟨_, r⟩, eqTm⟩ := Equal.reducible laws constants equal formed
  obtain ⟨tt, tu⟩ := Equal.typed equal formed
  exact LR.liftSpines laws constants roots heads algebra r formed lt lu eqTm tt tu spines

end LiftModel

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
