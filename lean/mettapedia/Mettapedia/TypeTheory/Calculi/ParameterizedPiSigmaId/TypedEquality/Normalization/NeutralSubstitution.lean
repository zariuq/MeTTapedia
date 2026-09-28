import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Renaming

/-!
# Substituting neutral terms creates no weak-head redex

A substitution of neutral terms (`NeutralSub`) puts, in place of a variable, a
term that is never an abstraction, a pair, reflexivity or a constructor form,
and that takes no weak-head step. So it creates no β-redex, no projection of a
pair, and no inspected constructor form, and a variable it replaces is never
the place of a step.

Two properties of the rule package make this exact:

* every computing constant inspects only constructor forms. A head-form
  inspection is not covered: a variable is no head form, but a rigid spine
  substituted for it is one, so the substitution creates a redex;
* its root computation reflects substitutions of neutral terms
  (`RootReflectsNeutral`): a root step from the instance of a spine of a
  constant comes from a root step of the spine. The computations of declared
  constants have this property, since their left-hand sides are headed by a
  constant and the arguments they inspect are constructor forms or
  reflexivity: the equation of a definition, the computation rules of a
  recursor and of a definition by structural recursion, the identity
  eliminator at reflexivity, and the decoding of codes.

Then every weak-head step of an instance comes from a weak-head step of the
term (`NeutralReflecting.of_constructors`), and a weak-head reduction of an
instance is the instance of a weak-head reduction of the term
(`WhRed.of_neutralSub`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (applyClosed)
open StrongNormalization (not_spine_of)

variable {Head : Type}

/-! ## Substitutions of neutral terms -/

/-- A substitution of neutral terms. -/
def NeutralSub (roles : Roles Head) {n m : Nat} (σ : Sub Head n m) : Prop :=
  ∀ i, Neutral roles (σ i)

namespace NeutralSub

variable {roles : Roles Head}

/-- The variables are neutral. -/
theorem ids {n : Nat} : NeutralSub roles (ids : Sub Head n n) :=
  fun i => .var i

/-- A renaming of neutral terms is neutral. -/
theorem rename {n m k : Nat} {σ : Sub Head n m} (neutral : NeutralSub roles σ) (ρ : Ren m k) :
    NeutralSub roles (fun i => Presentation.rename ρ (σ i)) :=
  fun i => (neutral i).rename ρ

/-- Lifting a substitution of neutral terms under a binder. -/
theorem lift {n m : Nat} {σ : Sub Head n m} (neutral : NeutralSub roles σ) :
    NeutralSub roles (liftSub σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .var 0
  · exact (neutral j).rename wk

/-- Extending a substitution of neutral terms by a neutral term. -/
theorem cons {n m : Nat} {σ : Sub Head n m} (neutral : NeutralSub roles σ) {a : Tm Head m}
    (neutralA : Neutral roles a) : NeutralSub roles (consSub a σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact neutralA
  · exact neutral j

end NeutralSub

/-- A neutral term applied to arguments is neutral. -/
theorem Neutral.appSpine {roles : Roles Head} {n : Nat} {f : Tm Head n}
    (neutral : Neutral roles f) : ∀ args : List (Tm Head n), Neutral roles (appSpine f args)
  | [] => neutral
  | _ :: args => Neutral.appSpine (.app neutral) args

/-! ## Terms whose instance has a given shape -/

section Inversion

variable {n m : Nat} {σ : Sub Head n m} {t : Tm Head n}

theorem subst_eq_app_or_var {f a : Tm Head m} (h : Presentation.subst σ t = .app f a) :
    (∃ i, t = .var i) ∨ ∃ f' a', t = .app f' a' ∧ Presentation.subst σ f' = f ∧
      Presentation.subst σ a' = a := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.app.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case app f' a' => exact .inr ⟨_, _, rfl, h.1, h.2⟩

theorem subst_eq_lam_or_var {b : Tm Head (m + 1)} (h : Presentation.subst σ t = .lam b) :
    (∃ i, t = .var i) ∨ ∃ b', t = .lam b' ∧ Presentation.subst (liftSub σ) b' = b := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.lam.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case lam b' => exact .inr ⟨_, rfl, h⟩

theorem subst_eq_pair_or_var {a b : Tm Head m} (h : Presentation.subst σ t = .pair a b) :
    (∃ i, t = .var i) ∨ ∃ a' b', t = .pair a' b' ∧ Presentation.subst σ a' = a ∧
      Presentation.subst σ b' = b := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.pair.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case pair a' b' => exact .inr ⟨_, _, rfl, h.1, h.2⟩

theorem subst_eq_fst_or_var {p : Tm Head m} (h : Presentation.subst σ t = .fst p) :
    (∃ i, t = .var i) ∨ ∃ p', t = .fst p' ∧ Presentation.subst σ p' = p := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.fst.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case fst p' => exact .inr ⟨_, rfl, h⟩

theorem subst_eq_snd_or_var {p : Tm Head m} (h : Presentation.subst σ t = .snd p) :
    (∃ i, t = .var i) ∨ ∃ p', t = .snd p' ∧ Presentation.subst σ p' = p := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.snd.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case snd p' => exact .inr ⟨_, rfl, h⟩

theorem subst_eq_refl_or_var {a : Tm Head m} (h : Presentation.subst σ t = .refl a) :
    (∃ i, t = .var i) ∨ ∃ a', t = .refl a' ∧ Presentation.subst σ a' = a := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.refl.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case refl a' => exact .inr ⟨_, rfl, h⟩

theorem subst_eq_pi_or_var {A : Tm Head m} {B : Tm Head (m + 1)}
    (h : Presentation.subst σ t = .pi A B) :
    (∃ i, t = .var i) ∨ ∃ A' B', t = .pi A' B' ∧ Presentation.subst σ A' = A ∧
      Presentation.subst (liftSub σ) B' = B := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.pi.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case pi A' B' => exact .inr ⟨_, _, rfl, h.1, h.2⟩

theorem subst_eq_sigma_or_var {A : Tm Head m} {B : Tm Head (m + 1)}
    (h : Presentation.subst σ t = .sigma A B) :
    (∃ i, t = .var i) ∨ ∃ A' B', t = .sigma A' B' ∧ Presentation.subst σ A' = A ∧
      Presentation.subst (liftSub σ) B' = B := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.sigma.injEq] at h
  case var i => exact .inl ⟨i, rfl⟩
  case sigma A' B' => exact .inr ⟨_, _, rfl, h.1, h.2⟩

end Inversion

/-- A term whose instance is a spine of a constant is a spine of that constant,
with the arguments substituted, or a spine of a variable. -/
theorem subst_eq_constSpine_or_varSpine {c : DeclName} :
    ∀ {n m : Nat} {σ : Sub Head n m} {t : Tm Head n} {as : List (Tm Head m)},
      Presentation.subst σ t = appSpine (.const c) as →
        (∃ as', t = appSpine (.const c) as' ∧ as'.map (Presentation.subst σ) = as) ∨
          ∃ i bs, t = appSpine (.var i) bs
  | _, _, _, .var i, _, _ => .inr ⟨i, [], rfl⟩
  | _, _, _, .const c', as, h => by
      simp only [Presentation.subst] at h
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective (show appSpine (.const c') [] = _ from h)
      exact .inl ⟨[], rfl, rfl⟩
  | _, _, σ, .app g a, as, h => by
      simp only [Presentation.subst] at h
      obtain ⟨init, rfl, hg⟩ := appSpine_const_eq_app h.symm
      rcases subst_eq_constSpine_or_varSpine hg with ⟨init', rfl, hmap⟩ | ⟨i, bs, rfl⟩
      · exact .inl ⟨init' ++ [a], (appSpine_concat _ _ _).symm, by
          rw [List.map_append, hmap]
          rfl⟩
      · exact .inr ⟨i, bs ++ [a], (appSpine_concat _ _ _).symm⟩
  | _, _, _, .head _, as, h | _, _, _, .pi _ _, as, h | _, _, _, .sigma _ _, as, h
  | _, _, _, .id _ _ _, as, h | _, _, _, .lam _, as, h | _, _, _, .pair _ _, as, h
  | _, _, _, .fst _, as, h | _, _, _, .snd _, as, h | _, _, _, .refl _, as, h => by
      simp only [Presentation.subst] at h
      exact absurd h (not_spine_of (by simp) (by simp) c as)

section Neutral

variable {roles : Roles Head} {n m : Nat} {σ : Sub Head n m}

/-- The instance of a spine of a variable by neutral terms is neutral. -/
theorem NeutralSub.varSpine (neutral : NeutralSub roles σ) (i : Fin n) (bs : List (Tm Head n)) :
    Neutral roles (Presentation.subst σ (appSpine (.var i) bs)) := by
  rw [subst_appSpine]
  exact (neutral i).appSpine _

/-- A term whose instance by neutral terms is a spine of a constructor is a
spine of that constructor. -/
theorem NeutralSub.constructorSpine (neutral : NeutralSub roles σ) {t : Tm Head n} {k : DeclName}
    {arity : Nat} (role : roles k = .constructor arity) {as : List (Tm Head m)}
    (h : Presentation.subst σ t = appSpine (.const k) as) :
    ∃ as', t = appSpine (.const k) as' ∧ as'.map (Presentation.subst σ) = as := by
  rcases subst_eq_constSpine_or_varSpine h with found | ⟨i, bs, rfl⟩
  · exact found
  · have stuck := neutral.varSpine i bs
    rw [h] at stuck
    exact absurd (.inr ⟨k, arity, as, role, rfl⟩) stuck.not_canonical

/-- **A constructor form of an instance by neutral terms is the instance of a
constructor form**, with the same key. -/
theorem ConstructorView.of_neutralSub (neutral : NeutralSub roles σ) {t : Tm Head n}
    {key : InspectKey} {fields : List (Tm Head m)}
    (view : ConstructorView roles (Presentation.subst σ t) key fields) :
    ∃ fields', ConstructorView roles t key fields' ∧
      fields'.map (Presentation.subst σ) = fields := by
  generalize e : Presentation.subst σ t = s at view
  cases view with
  | spine args role =>
      obtain ⟨as', rfl, rfl⟩ := neutral.constructorSpine role e
      exact ⟨as', .spine as' role, rfl⟩
  | refl a =>
      rcases subst_eq_refl_or_var e with ⟨i, rfl⟩ | ⟨a', rfl, rfl⟩
      · exact absurd e (neutral i).ne_refl
      · exact ⟨[a'], .refl a', rfl⟩

end Neutral

/-! ## Inspecting the arguments of an instance -/

section Focus

variable {roles : Roles Head}

/-- A constructor form with the fields replaced by as many others. -/
theorem ConstructorView.rebuild {n : Nat} {t : Tm Head n} {key : InspectKey}
    {fields : List (Tm Head n)} (view : ConstructorView roles t key fields)
    {fields' : List (Tm Head n)} (length : fields'.length = fields.length) :
    ∃ t', ConstructorView roles t' key fields' := by
  cases view with
  | spine args role => exact ⟨_, .spine fields' role⟩
  | refl a =>
      match fields', length with
      | [a'], _ => exact ⟨_, .refl a'⟩

/-- A focus keeps the number of values. -/
theorem InspectTree.Focus.length_eq {n : Nat} {tree : InspectTree}
    {values values' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n}
    (focus : tree.Focus roles values values' kind a a') : values'.length = values.length := by
  induction focus with
  | here _ => simp only [List.length_append, List.length_cons]
  | constructor lengthBefore lengthBefore' lengthFields _ _ _ ih =>
      simp only [List.length_append, List.length_cons] at ih ⊢
      omega
  | headForm _ _ _ ih => exact ih

/-- A focus puts any value in place of the value it inspects. -/
theorem InspectTree.Focus.retarget {n : Nat} {tree : InspectTree}
    {values values' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n}
    (focus : tree.Focus roles values values' kind a a') (b : Tm Head n) :
    ∃ values'', tree.Focus roles values values'' kind a b := by
  induction focus with
  | @here position kind next before after a a' lengthBefore =>
      exact ⟨_, .here lengthBefore⟩
  | @constructor position next before after fields before' after' fields' value value' key kind
      a a' lengthBefore _ _ view _ inner ih =>
      obtain ⟨vals, focus'⟩ := ih
      have total : vals.length = before.length + fields.length + after.length := by
        rw [focus'.length_eq]
        simp only [List.length_append]
      have split : vals = vals.take before.length ++
          (vals.drop before.length).take fields.length ++
          (vals.drop before.length).drop fields.length := by
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
      have lengthTake : (vals.take before.length).length = before.length := by
        rw [List.length_take]
        omega
      have lengthFields : ((vals.drop before.length).take fields.length).length =
          fields.length := by
        rw [List.length_take, List.length_drop]
        omega
      obtain ⟨value'', view''⟩ := view.rebuild lengthFields
      rw [split] at focus'
      exact ⟨_, .constructor lengthBefore (lengthTake.trans lengthBefore) lengthFields view view''
        focus'⟩
  | headForm lengthBefore view _ ih =>
      obtain ⟨vals, focus'⟩ := ih
      exact ⟨vals, .headForm lengthBefore view focus'⟩

/-- **The value a skeleton that inspects only constructor forms inspects next in
an instance by neutral terms is the instance of the value it inspects next in
the arguments.** -/
theorem InspectTree.Focus.of_neutralSub {n m : Nat} {σ : Sub Head n m}
    (neutral : NeutralSub roles σ) {tree : InspectTree} {values values' : List (Tm Head m)}
    {kind : Inspection} {a a' : Tm Head m} (focus : tree.Focus roles values values' kind a a')
    (only : tree.OnlyConstructors) :
    ∀ {args : List (Tm Head n)}, args.map (Presentation.subst σ) = values →
      ∃ b, Presentation.subst σ b = a ∧ tree.Focus roles args args kind b b := by
  induction focus with
  | @here position kind next before after a a' lengthBefore =>
      intro args hargs
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp hargs
      obtain ⟨b, l₃, rfl, hb, -⟩ := List.map_eq_cons_iff.mp h₂
      refine ⟨b, hb, .here ?_⟩
      rw [← lengthBefore, ← h₁, List.length_map]
  | @constructor position next before after fields before' after' fields' value value' key kind
      a a' lengthBefore _ _ view _ _ ih =>
      intro args hargs
      cases only with
      | split rest =>
          obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp hargs
          obtain ⟨v, l₃, rfl, hv, h₃⟩ := List.map_eq_cons_iff.mp h₂
          rw [← hv] at view
          obtain ⟨fields₀, view₀, hfields⟩ := view.of_neutralSub neutral
          obtain ⟨b, hb, inner⟩ := ih (rest key) (args := l₁ ++ fields₀ ++ l₃)
            (by rw [List.map_append, List.map_append, h₁, hfields, h₃])
          have lengthL : l₁.length = position := by
            rw [← lengthBefore, ← h₁, List.length_map]
          exact ⟨b, hb, .constructor lengthL lengthL rfl view₀ view₀ inner⟩
  | headForm _ _ _ _ => exact nomatch only

end Focus

/-! ## Root computations that reflect substitutions of neutral terms -/

/-- A root computation reflects substitutions of neutral terms when a root step
from the instance of a spine of a constant comes from a root step of the
spine. -/
def RootReflectsNeutral (roles : Roles Head) (C : RootComputation Head) : Prop :=
  ∀ ⦃n m : Nat⦄ ⦃σ : Sub Head n m⦄, NeutralSub roles σ →
    ∀ ⦃c : DeclName⦄ ⦃args : List (Tm Head n)⦄ ⦃u : Tm Head m⦄,
      C.step (appSpine (.const c) (args.map (Presentation.subst σ))) u →
        ∃ t', C.step (appSpine (.const c) args) t'

namespace RootReflectsNeutral

variable {roles : Roles Head}

theorem empty : RootReflectsNeutral roles (RootComputation.empty (Head := Head)) :=
  fun _ _ _ _ _ _ _ step => False.elim step

/-- A union of root computations that reflect substitutions of neutral terms
reflects them. -/
theorem union {first second : RootComputation Head} (h₁ : RootReflectsNeutral roles first)
    (h₂ : RootReflectsNeutral roles second) :
    RootReflectsNeutral roles (RootComputation.union first second) := by
  intro n m σ neutral c args u step
  rcases step with step | step
  · obtain ⟨t', s⟩ := h₁ neutral step
    exact ⟨t', .inl s⟩
  · obtain ⟨t', s⟩ := h₂ neutral step
    exact ⟨t', .inr s⟩

theorem unionAll :
    ∀ {cs : List (DeclName × RootComputation Head)},
      (∀ entry ∈ cs, RootReflectsNeutral roles entry.2) →
        RootReflectsNeutral roles (RootComputation.unionAll cs)
  | [], _ => empty
  | entry :: _, h =>
      union (h entry (List.mem_cons_self ..))
        (unionAll fun e mem => h e (List.mem_cons_of_mem _ mem))

end RootReflectsNeutral

/-- Arguments of an application to a telescope whose instances are the
arguments of a substitution come from a substitution of the telescope. -/
theorem telescopeArgs_subst_inv {m k : Nat} (σ : Sub Head m k) :
    ∀ {n : Nat} (Θ : Ctx Head n) {τ : Sub Head n k} {as : List (Tm Head m)},
      as.map (Presentation.subst σ) = telescopeArgs Θ τ →
        ∃ τ' : Sub Head n m, as = telescopeArgs Θ τ' ∧
          (fun i => Presentation.subst σ (τ' i)) = τ
  | _, .nil, _, _, h =>
      ⟨Fin.elim0, List.map_eq_nil_iff.mp h, funext fun i => Fin.elim0 i⟩
  | _, .snoc Θ _, τ, _, h => by
      change _ = telescopeArgs Θ (tailSub τ) ++ [τ 0] at h
      obtain ⟨init, last, rfl, hinit, hlast⟩ := List.map_eq_append_iff.mp h
      obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp hlast
      obtain ⟨τ', rfl, hτ⟩ := telescopeArgs_subst_inv σ Θ hinit
      refine ⟨consSub x τ', rfl, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hx
      · exact congrFun hτ j

/-- The scrutinee of an instance is the instance of the scrutinee. -/
theorem scrutOf_subst {m k s : Nat} (σ : Sub Head m k) :
    ∀ (d : Nat) (τ : Sub Head (s + 1 + d) m),
      scrutOf s d (fun i => Presentation.subst σ (τ i)) = Presentation.subst σ (scrutOf s d τ)
  | 0, _ => rfl
  | d + 1, τ => scrutOf_subst σ d (tailSub τ)

section Computations

variable {roles : Roles Head}

/-- The equation of a definition reflects substitutions of neutral terms. -/
theorem definitionComputation_reflectsNeutral (f : DeclName) {k : Nat} (Θ : Ctx Head k)
    (rhs : Tm Head k) : RootReflectsNeutral roles (definitionComputation f Θ rhs) := by
  intro n m σ _ c args u step
  obtain ⟨τ, hl, -⟩ := step
  rw [applyClosed_eq_appSpine] at hl
  obtain ⟨rfl, hmap⟩ := appSpine_const_injective hl
  obtain ⟨τ', rfl, -⟩ := telescopeArgs_subst_inv σ Θ hmap
  exact ⟨_, τ', (applyClosed_eq_appSpine Θ τ' _).symm, rfl⟩

/-- The identity eliminator's rule reflects substitutions of neutral terms. -/
theorem eliminatorComputation_reflectsNeutral (J : DeclName) :
    RootReflectsNeutral roles (eliminatorComputation (Head := Head) J) := by
  intro n m σ neutral c args u step
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, hl, -⟩ := step
  obtain ⟨rfl, hmap⟩ := appSpine_const_injective hl
  obtain ⟨b₀, l₀, rfl, -, h₀⟩ := List.map_eq_cons_iff.mp hmap
  obtain ⟨b₁, l₁, rfl, -, h₁⟩ := List.map_eq_cons_iff.mp h₀
  obtain ⟨b₂, l₂, rfl, -, h₂⟩ := List.map_eq_cons_iff.mp h₁
  obtain ⟨b₃, l₃, rfl, -, h₃⟩ := List.map_eq_cons_iff.mp h₂
  obtain ⟨b₄, l₄, rfl, -, h₄⟩ := List.map_eq_cons_iff.mp h₃
  obtain ⟨b₅, l₅, rfl, h₅, h₆⟩ := List.map_eq_cons_iff.mp h₄
  obtain rfl := List.map_eq_nil_iff.mp h₆
  rcases subst_eq_refl_or_var h₅ with ⟨i, rfl⟩ | ⟨x, rfl, -⟩
  · exact absurd h₅ (neutral i).ne_refl
  · exact ⟨b₃, b₀, b₁, b₂, b₃, b₄, x, rfl, rfl⟩

/-- The computation rules of a recursor reflect substitutions of neutral
terms. -/
theorem iotaComputation_reflectsNeutral {T rec : DeclName}
    {ctors : List (DeclName × List (Field Head))} (role : roles T = .inductive ctors)
    (declared : ConstructorsDeclared roles) :
    RootReflectsNeutral roles (iotaComputation rec ctors) := by
  intro n m σ neutral c args u step
  obtain ⟨p, ms, i, k, fields, as, mt, hms, hi, has, hm, hl, -⟩ := step
  obtain ⟨rfl, hmap⟩ := appSpine_const_injective hl
  obtain ⟨p', rest', rfl, rfl, hrest⟩ := List.map_eq_cons_iff.mp hmap
  obtain ⟨ms', xs', rfl, rfl, hx⟩ := List.map_eq_append_iff.mp hrest
  obtain ⟨x', rfl, hx'⟩ := List.map_eq_singleton_iff.mp hx
  obtain ⟨as', rfl, rfl⟩ :=
    neutral.constructorSpine (declared.arity role (List.mem_of_getElem? hi)) hx'
  have hmi : (ms'.map (Presentation.subst σ))[i]? = some mt := hm
  rw [List.getElem?_map] at hmi
  obtain ⟨mt', hmt', -⟩ := Option.map_eq_some_iff.mp hmi
  exact ⟨_, p', ms', i, k, fields, as', mt', by rw [← hms, List.length_map], hi,
    by rw [← has, List.length_map], hmt', rfl, rfl⟩

/-- The equations of a definition by structural recursion reflect
substitutions of neutral terms. -/
theorem recursionComputation_reflectsNeutral {T : DeclName} (f : DeclName)
    {ctors : List (DeclName × List (Field Head))} (role : roles T = .inductive ctors)
    (declared : ConstructorsDeclared roles) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) :
    RootReflectsNeutral roles (recursionComputation f ctors e s d body) := by
  intro n m σ neutral c args u step
  obtain ⟨k, fields, τ, as, mem, has, hl, -⟩ := step
  rw [applyClosed_eq_appSpine] at hl
  obtain ⟨rfl, hmap⟩ := appSpine_const_injective hl
  obtain ⟨τ', rfl, hτ⟩ := telescopeArgs_subst_inv σ _ hmap
  have hscrut : Presentation.subst σ (scrutOf s d τ') = appSpine (.const k) as := by
    rw [← scrutOf_subst, hτ, scrutOf_replaceScrut]
  obtain ⟨as', hx, hmapAs⟩ := neutral.constructorSpine (declared.arity role mem) hscrut
  refine ⟨_, k, fields, τ', as', mem, by rw [← has, ← hmapAs, List.length_map], ?_, rfl⟩
  rw [applyClosed_eq_appSpine, ← hx, replaceScrut_self]

/-- The decoding of codes reflects substitutions of neutral terms. -/
theorem decoderComputation_reflectsNeutral {D : Decoders Head} (declared : DecoderRoles roles D) :
    RootReflectsNeutral roles (decoderComputation D) := by
  intro n m σ neutral c args u step
  change DecoderStep D (appSpine (.const c) (args.map (Presentation.subst σ))) u at step
  generalize hs : appSpine (.const c) (args.map (Presentation.subst σ)) = s at step
  cases step with
  | imp p q =>
      obtain ⟨rfl, hmap⟩ := appSpine_const_injective
        (hs.trans (show _ = appSpine (.const D.holds) [appSpine (.const D.imp) [p, q]] from rfl))
      obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp hmap
      obtain ⟨as', rfl, hmapAs⟩ := neutral.constructorSpine declared.imp hx
      obtain ⟨p', l, rfl, -, hl⟩ := List.map_eq_cons_iff.mp hmapAs
      obtain ⟨q', l', rfl, -, hl'⟩ := List.map_eq_cons_iff.mp hl
      obtain rfl := List.map_eq_nil_iff.mp hl'
      exact ⟨_, DecoderStep.imp p' q'⟩
  | all carrier f =>
      obtain ⟨rfl, hmap⟩ := appSpine_const_injective
        (hs.trans (show _ = appSpine (.const D.holds) [appSpine (.const _) [f]] from rfl))
      obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp hmap
      obtain ⟨as', rfl, hmapAs⟩ := neutral.constructorSpine (declared.all carrier) hx
      obtain ⟨f', rfl, -⟩ := List.map_eq_singleton_iff.mp hmapAs
      exact ⟨_, DecoderStep.all carrier f'⟩
  | eq carrier x y =>
      obtain ⟨rfl, hmap⟩ := appSpine_const_injective
        (hs.trans (show _ = appSpine (.const D.holds) [appSpine (.const _) [x, y]] from rfl))
      obtain ⟨z, rfl, hz⟩ := List.map_eq_singleton_iff.mp hmap
      obtain ⟨as', rfl, hmapAs⟩ := neutral.constructorSpine (declared.eq carrier) hz
      obtain ⟨x', l, rfl, -, hl⟩ := List.map_eq_cons_iff.mp hmapAs
      obtain ⟨y', l', rfl, -, hl'⟩ := List.map_eq_cons_iff.mp hl
      obtain rfl := List.map_eq_nil_iff.mp hl'
      exact ⟨_, DecoderStep.eq carrier x' y'⟩

end Computations

/-! ## Weak-head steps of instances -/

/-- **Substituting neutral terms creates no weak-head redex**: a weak-head step
of an instance of a term by neutral terms comes from a weak-head step of the
term. -/
def NeutralReflecting (R : Rules Head) (roles : Roles Head) : Prop :=
  ∀ ⦃n m : Nat⦄ ⦃σ : Sub Head n m⦄, NeutralSub roles σ → ∀ ⦃t : Tm Head n⦄ ⦃u : Tm Head m⦄,
    WhStep R roles (Presentation.subst σ t) u → ∃ t', WhStep R roles t t'

section Reflection

variable {R : Rules Head} {roles : Roles Head}

/-- **Substituting neutral terms creates no weak-head redex** in a rule package
of root shape whose computing constants inspect only constructor forms and
whose root computation reflects substitutions of neutral terms. -/
theorem NeutralReflecting.of_constructors (shape : RootShape R roles)
    (only : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree},
      roles c = .computes arity inspect → inspect.OnlyConstructors)
    (reflects : RootReflectsNeutral roles R.computation) : NeutralReflecting R roles := by
  intro n m σ neutral
  have noVar : ∀ (i : Fin n) {s u : Tm Head m}, σ i = s → ¬ WhStep R roles s u :=
    fun i s u e step => (neutral i).whnf shape u (e ▸ step)
  have noVarSpine : ∀ (i : Fin n) (bs : List (Tm Head n)) {s u : Tm Head m},
      Presentation.subst σ (appSpine (.var i) bs) = s → ¬ WhStep R roles s u :=
    fun i bs s u e step => (neutral.varSpine i bs).whnf shape u (e ▸ step)
  suffices key : ∀ {s u : Tm Head m}, WhStep R roles s u →
      ∀ {t : Tm Head n}, Presentation.subst σ t = s → ∃ t', WhStep R roles t t' from
    fun t u step => key step rfl
  intro s u step
  induction step with
  | beta body a =>
      intro t ht
      rcases subst_eq_app_or_var ht with ⟨i, rfl⟩ | ⟨f', a', rfl, hf, -⟩
      · exact absurd (.beta body a) (noVar i ht)
      · rcases subst_eq_lam_or_var hf with ⟨i, rfl⟩ | ⟨b', rfl, -⟩
        · exact absurd hf (neutral i).ne_lam
        · exact ⟨_, .beta b' a'⟩
  | fstPair a b =>
      intro t ht
      rcases subst_eq_fst_or_var ht with ⟨i, rfl⟩ | ⟨p', rfl, hp⟩
      · exact absurd (.fstPair a b) (noVar i ht)
      · rcases subst_eq_pair_or_var hp with ⟨i, rfl⟩ | ⟨a', b', rfl, -, -⟩
        · exact absurd hp (neutral i).ne_pair
        · exact ⟨_, .fstPair a' b'⟩
  | sndPair a b =>
      intro t ht
      rcases subst_eq_snd_or_var ht with ⟨i, rfl⟩ | ⟨p', rfl, hp⟩
      · exact absurd (.sndPair a b) (noVar i ht)
      · rcases subst_eq_pair_or_var hp with ⟨i, rfl⟩ | ⟨a', b', rfl, -, -⟩
        · exact absurd hp (neutral i).ne_pair
        · exact ⟨_, .sndPair a' b'⟩
  | @root s u root =>
      intro t ht
      obtain ⟨c, _, _, args, _, hs, _⟩ := shape.spine root
      rcases subst_eq_constSpine_or_varSpine (ht.trans hs) with ⟨as', rfl, hmap⟩ | ⟨i, bs, rfl⟩
      · rw [hs, ← hmap] at root
        obtain ⟨t', step'⟩ := reflects neutral root
        exact ⟨t', .root step'⟩
      · exact absurd (.root root) (noVarSpine i bs ht)
  | appFun inner ih =>
      intro t ht
      rcases subst_eq_app_or_var ht with ⟨i, rfl⟩ | ⟨f', a', rfl, hf, -⟩
      · exact absurd (.appFun inner) (noVar i ht)
      · obtain ⟨f'', step'⟩ := ih hf
        exact ⟨_, .appFun step'⟩
  | fst inner ih =>
      intro t ht
      rcases subst_eq_fst_or_var ht with ⟨i, rfl⟩ | ⟨p', rfl, hp⟩
      · exact absurd (.fst inner) (noVar i ht)
      · obtain ⟨p'', step'⟩ := ih hp
        exact ⟨_, .fst step'⟩
  | snd inner ih =>
      intro t ht
      rcases subst_eq_snd_or_var ht with ⟨i, rfl⟩ | ⟨p', rfl, hp⟩
      · exact absurd (.snd inner) (noVar i ht)
      · obtain ⟨p'', step'⟩ := ih hp
        exact ⟨_, .snd step'⟩
  | @scrutinee c arity inspect args args' kind a a' role length focus inner ih =>
      intro t ht
      rcases subst_eq_constSpine_or_varSpine ht with ⟨as', rfl, hmap⟩ | ⟨i, bs, rfl⟩
      · obtain ⟨b, hb, focus₀⟩ := focus.of_neutralSub neutral (only role) hmap
        obtain ⟨b', step'⟩ := ih hb
        obtain ⟨vals, focus₁⟩ := focus₀.retarget b'
        exact ⟨_, .scrutinee role (by rw [← length, ← hmap, List.length_map]) focus₁ step'⟩
      · exact absurd (.scrutinee role length focus inner) (noVarSpine i bs ht)

variable (shape : RootShape R roles) (reflecting : NeutralReflecting R roles)
include shape reflecting

/-- A weak-head step of an instance by neutral terms is the instance of a
weak-head step of the term. -/
theorem WhStep.of_neutralSub {n m : Nat} {σ : Sub Head n m} (neutral : NeutralSub roles σ)
    {t : Tm Head n} {u : Tm Head m} (step : WhStep R roles (Presentation.subst σ t) u) :
    ∃ t', WhStep R roles t t' ∧ u = Presentation.subst σ t' := by
  obtain ⟨t', step'⟩ := reflecting neutral step
  exact ⟨t', step', WhStep.deterministic shape (step'.subst σ) step⟩

/-- **A weak-head reduction of an instance by neutral terms is the instance of a
weak-head reduction of the term.** -/
theorem WhRed.of_neutralSub {n m : Nat} {σ : Sub Head n m} (neutral : NeutralSub roles σ)
    {t : Tm Head n} {w : Tm Head m} (red : WhRed R roles (Presentation.subst σ t) w) :
    ∃ t', WhRed R roles t t' ∧ w = Presentation.subst σ t' := by
  generalize e : Presentation.subst σ t = s at red
  induction red using Relation.ReflTransGen.head_induction_on generalizing t with
  | refl => exact ⟨t, .refl, e.symm⟩
  | head step _ ih =>
      rw [← e] at step
      obtain ⟨t₁, step₁, rfl⟩ := WhStep.of_neutralSub shape reflecting neutral step
      obtain ⟨t', red', rfl⟩ := ih rfl
      exact ⟨t', .head step₁ red', rfl⟩

end Reflection

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
