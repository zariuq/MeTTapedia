import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Transport

/-!
# The transport table as root computations

On the value side the transport `coe X Y d` computes by the head forms of its
two type arguments, the target first. Its rows are root computations of fresh,
value-only constants, each of which inspects its type arguments for head forms
(`Inspection.headForm`):

* `coe X Y d` inspects the target `Y`. At a universe `U` it continues with
  `coeU U X d`; at `Π A' B'` with `coePi A' (λ B') X d`; at `Σ A' B'` with
  `coeSigma A' (λ B') X d`; at a type constant `C`, the codes or any inductive
  type, with `coeConst C X d`; at every other head form (a head that is no
  universe, an identity type, a rigid or constructor spine, a value) it returns
  the method.
* `coeU U X d` inspects the target universe and then the source: the method
  from a universe of at most the level of `U`, the daimon from any other head
  form.
* `coeConst C X d` inspects the source: the method from the type constant `C`
  itself, the daimon from any other head form. Which constants are type
  constants is read from the roles, so one row serves every inductive type.
* `coePi A' B'' X f` inspects the source: from `Π A B` the λ-abstraction whose
  body transports `f a₀` along the codomains, `a₀` being the bound variable
  transported back along the domains (`piBody`); the daimon from any other head
  form. `coeSigma A' B'' X p` returns, from `Σ A B`, the pair of the first
  projection transported along the domains and the second transported along the
  codomains.

Identity elimination on the value side transports its method along its motive:
`J A x P d y e ⟶ coe (P x (refl x)) (P y e) d` (`transportJ`).

Every row is stable under substitution: its conditions read head forms, which
substitution keeps. Its steps occur at spines of exact arity whose inspected
values are head forms, and it is deterministic. The rows read universe levels
in any level order.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Realizability

open Normalization
open Consistency (appSpine_const_ne_pi appSpine_const_ne_sigma appSpine_const_ne_id
  appSpine_const_eq_const)
open UniverseLevel (LevelOrder)
open ValueSide (coeApp coeArg subst_coeApp)

variable {Head L : Type}

/-- Levels are compared through the linear order's own projections: the rows
of the universes then need no propositional extensionality, which the order
of a lattice carries. -/
local instance levelPreorder [LevelOrder L] : Preorder L :=
  LevelOrder.toLinearOrder.toPartialOrder.toPreorder

/-! ## Names, parameters and skeletons -/

/-- The value-only constants of the transport. -/
structure CoeNames where
  coe : DeclName
  coeU : DeclName
  coeConst : DeclName
  coePi : DeclName
  coeSigma : DeclName

/-- What the rows of the transport read from a value side: its roles, which
heads are universes and their levels, the codes and the daimon. -/
structure CoeParams (Head L : Type) where
  roles : Roles Head
  isUniverse : Head → Prop
  level : Head → L
  prop : DeclName
  star : DeclName

/-- The type constants the transport reads by name: the codes and every
inductive type of the roles. -/
def CoeParams.TypeConst (P : CoeParams Head L) (c : DeclName) : Prop :=
  c = P.prop ∨ ∃ cs, P.roles c = .inductive cs

/-- A type constant does not compute, when the codes do not. -/
theorem CoeParams.TypeConst.stuck {P : CoeParams Head L} {c : DeclName} (hc : P.TypeConst c)
    (propStuck : ∀ arity inspect, P.roles P.prop ≠ .computes arity inspect) :
    ∀ arity inspect, P.roles c ≠ .computes arity inspect := by
  rcases hc with rfl | ⟨cs, role⟩
  · exact propStuck
  · intro _ _ h
    rw [role] at h
    cases h

/-- The parameters of the transport's rows in a consistency model with a
daimon. -/
def coeParamsOf [LevelOrder L] (M : Consistency.Model Head L) (star : DeclName) :
    CoeParams Head L where
  roles := M.roles
  isUniverse := M.rules.isUniverse
  level := M.levels.level
  prop := M.prop
  star := star

/-- The skeleton that inspects the argument at `k` for a head form. -/
def headAt (k : Nat) : InspectTree := .split k .headForm fun _ => .leaf

/-- The skeleton of `coeU`: the target universe, then the source. -/
def headAtBoth : InspectTree := .split 0 .headForm fun _ => .split 1 .headForm fun _ => .leaf

/-! ## The transport into a dependent function type -/

/-- The bound variable transported back along the domains: `coe A'↑ A↑ x`. -/
def piArg (coe : DeclName) {n : Nat} (A' A : Tm Head n) : Tm Head (n + 1) :=
  coeApp coe (rename wk A') (rename wk A) (.var 0)

/-- The body of the transport into a dependent function type:
`coe (B a₀) (B'' x) (f a₀)`, with `a₀` the bound variable transported back
along the domains. -/
def piBody (coe : DeclName) {n : Nat} (A' B'' A : Tm Head n) (B : Tm Head (n + 1))
    (f : Tm Head n) : Tm Head (n + 1) :=
  coeApp coe (inst0 (piArg coe A' A) (rename (liftRen wk) B)) (.app (rename wk B'') (.var 0))
    (.app (rename wk f) (piArg coe A' A))

/-- Weakening below one binder commutes with a substitution lifted past it. -/
theorem subst_liftSub_rename_liftRen_wk {n m : Nat} (σ : Sub Head n m) (t : Tm Head (n + 1)) :
    subst (liftSub (liftSub σ)) (rename (liftRen wk) t) =
      rename (liftRen wk) (subst (liftSub σ) t) := by
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show rename wk (rename wk (σ j)) = rename (liftRen wk) (rename wk (σ j))
    rw [rename_liftRen_wk]

/-- Opening the binder of a term weakened below it undoes the weakening. -/
theorem subst_liftSub_subst0_rename_liftRen_wk {n : Nat} (a : Tm Head n)
    (t : Tm Head (n + 1)) : subst (liftSub (subst0 a)) (rename (liftRen wk) t) = t := by
  rw [subst_rename]
  calc subst (fun i => liftSub (subst0 a) (liftRen wk i)) t = subst ids t := by
        apply subst_ext
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
    _ = t := subst_ids t

theorem subst_piArg (coe : DeclName) {n m : Nat} (σ : Sub Head n m) (A' A : Tm Head n) :
    subst (liftSub σ) (piArg coe A' A) = piArg coe (subst σ A') (subst σ A) := by
  rw [piArg, piArg, subst_coeApp, subst_liftSub_wk, subst_liftSub_wk]
  rfl

theorem subst_piBody (coe : DeclName) {n m : Nat} (σ : Sub Head n m) (A' B'' A : Tm Head n)
    (B : Tm Head (n + 1)) (f : Tm Head n) :
    subst (liftSub σ) (piBody coe A' B'' A B f) =
      piBody coe (subst σ A') (subst σ B'') (subst σ A) (subst (liftSub σ) B) (subst σ f) := by
  rw [piBody, piBody, subst_coeApp, subst_inst0, subst_piArg,
    subst_liftSub_rename_liftRen_wk]
  show coeApp coe _ (.app (subst (liftSub σ) (rename wk B'')) (.var 0))
      (.app (subst (liftSub σ) (rename wk f)) (subst (liftSub σ) (piArg coe A' A))) = _
  rw [subst_liftSub_wk, subst_liftSub_wk, subst_piArg]

theorem rename_piBody (coe : DeclName) {n m : Nat} (ρ : Ren n m) (A' B'' A : Tm Head n)
    (B : Tm Head (n + 1)) (f : Tm Head n) :
    rename (liftRen ρ) (piBody coe A' B'' A B f) =
      piBody coe (rename ρ A') (rename ρ B'') (rename ρ A) (rename (liftRen ρ) B)
        (rename ρ f) := by
  have h := subst_piBody coe (renSub ρ) A' B'' A B f
  rw [liftSub_renSub] at h
  simpa only [subst_renSub] using h

/-- Opening the body at `a`: the transport along the codomains of `f` applied
to `a` transported back along the domains. -/
theorem inst0_piBody (coe : DeclName) {n : Nat} (a A' B'' A : Tm Head n) (B : Tm Head (n + 1))
    (f : Tm Head n) :
    inst0 a (piBody coe A' B'' A B f) =
      coeApp coe (inst0 (coeApp coe A' A a) B) (.app B'' a) (.app f (coeApp coe A' A a)) := by
  have arg : inst0 a (piArg coe A' A) = coeApp coe A' A a := by
    show coeApp coe (inst0 a (rename wk A')) (inst0 a (rename wk A)) (inst0 a (.var 0)) = _
    rw [inst0_rename_wk, inst0_rename_wk]
    rfl
  have source : inst0 a (inst0 (piArg coe A' A) (rename (liftRen wk) B)) =
      inst0 (coeApp coe A' A a) B := by
    show subst (subst0 a) (inst0 (piArg coe A' A) (rename (liftRen wk) B)) = _
    rw [subst_inst0, subst_liftSub_subst0_rename_liftRen_wk]
    exact congrArg (fun x => inst0 x B) arg
  show coeApp coe (inst0 a (inst0 (piArg coe A' A) (rename (liftRen wk) B)))
      (.app (inst0 a (rename wk B'')) (inst0 a (.var 0)))
      (.app (inst0 a (rename wk f)) (inst0 a (piArg coe A' A))) = _
  rw [source, inst0_rename_wk, inst0_rename_wk, arg]
  rfl

/-- The body, renamed and opened at `a`, as the transport table's row for
dependent function types reads it. -/
theorem inst0_rename_piBody (coe : DeclName) {n m : Nat} (ρ : Ren n m) (a : Tm Head m)
    (A' B'' A : Tm Head n) (B : Tm Head (n + 1)) (f : Tm Head n) :
    inst0 a (rename (liftRen ρ) (piBody coe A' B'' A B f)) =
      coeApp coe (inst0 (coeArg coe ρ A A' a) (rename (liftRen ρ) B)) (.app (rename ρ B'') a)
        (.app (rename ρ f) (coeArg coe ρ A A' a)) := by
  rw [rename_piBody, inst0_piBody]

/-! ## Head forms under substitution -/

section HeadForms

variable {roles : Roles Head} {n m : Nat} {σ : Sub Head n m} {t : Tm Head n} {key : InspectKey}

/-- A head form is a head when its substitution instance is. -/
theorem headView_subst_eq_head (view : HeadView roles t key) {h : Head}
    (e : subst σ t = .head h) : t = .head h := by
  cases view with
  | spine args _ =>
      rw [subst_appSpine] at e
      exact absurd e appSpine_const_ne_head
  | head h' =>
      obtain rfl := Tm.head.inj e
      rfl
  | pi A B => cases e
  | sigma A B => cases e
  | id A a b => cases e
  | lam body => cases e
  | pair a b => cases e
  | refl a => cases e

/-- A head form is a dependent function type when its substitution instance
is. -/
theorem headView_subst_eq_pi (view : HeadView roles t key) {A : Tm Head m}
    {B : Tm Head (m + 1)} (e : subst σ t = .pi A B) : ∃ A₀ B₀, t = .pi A₀ B₀ := by
  cases view with
  | spine args _ =>
      rw [subst_appSpine] at e
      exact absurd e appSpine_const_ne_pi
  | head h' => cases e
  | pi A B => exact ⟨A, B, rfl⟩
  | sigma A B => cases e
  | id A a b => cases e
  | lam body => cases e
  | pair a b => cases e
  | refl a => cases e

/-- A head form is a dependent pair type when its substitution instance is. -/
theorem headView_subst_eq_sigma (view : HeadView roles t key) {A : Tm Head m}
    {B : Tm Head (m + 1)} (e : subst σ t = .sigma A B) : ∃ A₀ B₀, t = .sigma A₀ B₀ := by
  cases view with
  | spine args _ =>
      rw [subst_appSpine] at e
      exact absurd e appSpine_const_ne_sigma
  | head h' => cases e
  | pi A B => cases e
  | sigma A B => exact ⟨A, B, rfl⟩
  | id A a b => cases e
  | lam body => cases e
  | pair a b => cases e
  | refl a => cases e

/-- A head form is a constant when its substitution instance is. -/
theorem headView_subst_eq_const (view : HeadView roles t key) {c : DeclName}
    (e : subst σ t = .const c) : t = .const c := by
  cases view with
  | spine args _ =>
      rw [subst_appSpine] at e
      obtain ⟨rfl, empty⟩ := appSpine_const_eq_const e
      rw [List.map_eq_nil_iff.mp empty]
      rfl
  | head h' => cases e
  | pi A B => cases e
  | sigma A B => cases e
  | id A a b => cases e
  | lam body => cases e
  | pair a b => cases e
  | refl a => cases e

end HeadForms

/-- A spine of a constant is a head form only if the constant does not
compute. -/
theorem headView_constSpine_stuck {roles : Roles Head} {n : Nat} {c : DeclName}
    {args : List (Tm Head n)} {key : InspectKey}
    (view : HeadView roles (appSpine (.const c) args) key) :
    ∀ arity inspect, roles c ≠ .computes arity inspect := by
  generalize e : appSpine (.const c) args = t at view
  cases view with
  | spine args' notComputing =>
      obtain ⟨rfl, -⟩ := appSpine_const_injective e
      exact notComputing
  | head h => exact absurd e appSpine_const_ne_head
  | pi A B => exact absurd e appSpine_const_ne_pi
  | sigma A B => exact absurd e appSpine_const_ne_sigma
  | id A a b => exact absurd e appSpine_const_ne_id
  | lam body => exact absurd e appSpine_const_ne_lam'
  | pair a b => exact absurd e appSpine_const_ne_pair
  | refl a => exact absurd e appSpine_const_ne_refl

/-! ## The rows -/

variable (P : CoeParams Head L) (N : CoeNames)

/-- The head forms at which `coe` returns its method: those that are no head,
no dependent function or pair type, and no type constant. -/
structure MethodTarget {n : Nat} (Y : Tm Head n) : Prop where
  form : HeadForm P.roles Y
  notHead : ∀ h, Y ≠ .head h
  notPi : ∀ A B, Y ≠ .pi A B
  notSigma : ∀ A B, Y ≠ .sigma A B
  notConst : ∀ c, P.TypeConst c → Y ≠ .const c

/-- The rows of `coe X Y d`, read on the head form of the target `Y`. -/
inductive CoeTarget {n : Nat} : Tm Head n → Tm Head n → Tm Head n → Tm Head n → Prop where
  | univ {X d : Tm Head n} {u : Head} : P.isUniverse u →
      CoeTarget X (.head u) d (appSpine (.const N.coeU) [.head u, X, d])
  | ground {X d : Tm Head n} {h : Head} : ¬ P.isUniverse h → CoeTarget X (.head h) d d
  | pi {X d A' : Tm Head n} {B' : Tm Head (n + 1)} :
      CoeTarget X (.pi A' B') d (appSpine (.const N.coePi) [A', .lam B', X, d])
  | sigma {X d A' : Tm Head n} {B' : Tm Head (n + 1)} :
      CoeTarget X (.sigma A' B') d (appSpine (.const N.coeSigma) [A', .lam B', X, d])
  | const {X d : Tm Head n} {c : DeclName} : P.TypeConst c →
      CoeTarget X (.const c) d (appSpine (.const N.coeConst) [.const c, X, d])
  | method {X Y d : Tm Head n} : MethodTarget P Y → CoeTarget X Y d d

variable [LevelOrder L] in
/-- The rows of `coeU U X d`: the method from a universe of at most the level
of the target universe, the daimon from any other head form. -/
inductive CoeUniv {n : Nat} : Tm Head n → Tm Head n → Tm Head n → Tm Head n → Prop where
  | method {d : Tm Head n} {u u' : Head} : P.isUniverse u' → P.level u' ≤ P.level u →
      CoeUniv (.head u) (.head u') d d
  | star {T X d : Tm Head n} : HeadForm P.roles T → HeadForm P.roles X →
      (∀ u u', T = .head u → X = .head u' → P.isUniverse u' → P.level u < P.level u') →
      CoeUniv T X d (.const P.star)

/-- The rows of `coeConst C X d`, for the type constant `C`: the method from `C`,
the daimon from any other head form. -/
inductive CoeConst {n : Nat} : Tm Head n → Tm Head n → Tm Head n → Tm Head n → Prop where
  | method {c : DeclName} {d : Tm Head n} : P.TypeConst c → CoeConst (.const c) (.const c) d d
  | star {c : DeclName} {X d : Tm Head n} : HeadForm P.roles X → X ≠ .const c →
      CoeConst (.const c) X d (.const P.star)

/-- The rows of `coePi A' B'' X f`: from `Π A B` the λ-abstraction of the
transport along the codomains, the daimon from any other head form. -/
inductive CoePiRow {n : Nat} : Tm Head n → Tm Head n → Tm Head n → Tm Head n → Tm Head n →
    Prop where
  | lam {A' B'' A f : Tm Head n} {B : Tm Head (n + 1)} :
      CoePiRow A' B'' (.pi A B) f (.lam (piBody N.coe A' B'' A B f))
  | star {A' B'' X f : Tm Head n} : HeadForm P.roles X → (∀ A B, X ≠ .pi A B) →
      CoePiRow A' B'' X f (.const P.star)

/-- The rows of `coeSigma A' B'' X p`: from `Σ A B` the pair of the transported
projections, the daimon from any other head form. -/
inductive CoeSigmaRow {n : Nat} : Tm Head n → Tm Head n → Tm Head n → Tm Head n → Tm Head n →
    Prop where
  | pair {A' B'' A p : Tm Head n} {B : Tm Head (n + 1)} :
      CoeSigmaRow A' B'' (.sigma A B) p
        (.pair (coeApp N.coe A A' (.fst p))
          (coeApp N.coe (inst0 (.fst p) B) (.app B'' (coeApp N.coe A A' (.fst p))) (.snd p)))
  | star {A' B'' X p : Tm Head n} : HeadForm P.roles X → (∀ A B, X ≠ .sigma A B) →
      CoeSigmaRow A' B'' X p (.const P.star)

variable {P N}

/-! ## Stability under substitution -/

section Stability

variable {n m : Nat} (σ : Sub Head n m)

theorem MethodTarget.subst {Y : Tm Head n} (target : MethodTarget P Y) :
    MethodTarget P (Presentation.subst σ Y) := by
  obtain ⟨⟨key, view⟩, notHead, notPi, notSigma, notConst⟩ := target
  refine ⟨⟨key, view.subst σ⟩, fun h e => notHead h (headView_subst_eq_head view e), fun A B e => ?_,
    fun A B e => ?_, fun c hc e => notConst c hc (headView_subst_eq_const view e)⟩
  · obtain ⟨A₀, B₀, rfl⟩ := headView_subst_eq_pi view e
    exact notPi A₀ B₀ rfl
  · obtain ⟨A₀, B₀, rfl⟩ := headView_subst_eq_sigma view e
    exact notSigma A₀ B₀ rfl

theorem CoeTarget.subst {X Y d r : Tm Head n} (h : CoeTarget P N X Y d r) :
    CoeTarget P N (Presentation.subst σ X) (Presentation.subst σ Y) (Presentation.subst σ d)
      (Presentation.subst σ r) := by
  cases h with
  | univ hu => exact .univ hu
  | ground hh => exact .ground hh
  | pi => exact .pi
  | sigma => exact .sigma
  | const hc => exact .const hc
  | method target => exact .method (target.subst σ)

variable [LevelOrder L] in
theorem CoeUniv.subst {T X d r : Tm Head n} (h : CoeUniv P T X d r) :
    CoeUniv P (Presentation.subst σ T) (Presentation.subst σ X) (Presentation.subst σ d)
      (Presentation.subst σ r) := by
  cases h with
  | method hu le => exact .method hu le
  | star formT formX above =>
      obtain ⟨keyT, viewT⟩ := formT
      obtain ⟨keyX, viewX⟩ := formX
      exact .star ⟨keyT, viewT.subst σ⟩ ⟨keyX, viewX.subst σ⟩ fun u u' eT eX hu =>
        above u u' (headView_subst_eq_head viewT eT) (headView_subst_eq_head viewX eX) hu

theorem CoeConst.subst {C X d r : Tm Head n} (h : CoeConst P C X d r) :
    CoeConst P (Presentation.subst σ C) (Presentation.subst σ X) (Presentation.subst σ d)
      (Presentation.subst σ r) := by
  cases h with
  | method hc => exact .method hc
  | star form ne =>
      obtain ⟨key, view⟩ := form
      exact .star ⟨key, view.subst σ⟩ fun e => ne (headView_subst_eq_const view e)

theorem CoePiRow.subst_lam {A' B'' A f : Tm Head n} {B : Tm Head (n + 1)} :
    CoePiRow P N (Presentation.subst σ A') (Presentation.subst σ B'')
      (Presentation.subst σ (.pi A B)) (Presentation.subst σ f)
      (Presentation.subst σ (.lam (piBody N.coe A' B'' A B f))) := by
  show CoePiRow P N _ _ (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) _
    (.lam (Presentation.subst (liftSub σ) (piBody N.coe A' B'' A B f)))
  rw [subst_piBody]
  exact .lam

theorem CoePiRow.subst {A' B'' X f r : Tm Head n} (h : CoePiRow P N A' B'' X f r) :
    CoePiRow P N (Presentation.subst σ A') (Presentation.subst σ B'') (Presentation.subst σ X)
      (Presentation.subst σ f) (Presentation.subst σ r) := by
  cases h with
  | lam => exact CoePiRow.subst_lam σ
  | star form notPi =>
      obtain ⟨key, view⟩ := form
      exact .star ⟨key, view.subst σ⟩ fun A B e => by
        obtain ⟨A₀, B₀, rfl⟩ := headView_subst_eq_pi view e
        exact notPi A₀ B₀ rfl

theorem CoeSigmaRow.subst_pair {A' B'' A p : Tm Head n} {B : Tm Head (n + 1)} :
    CoeSigmaRow P N (Presentation.subst σ A') (Presentation.subst σ B'')
      (Presentation.subst σ (.sigma A B)) (Presentation.subst σ p)
      (Presentation.subst σ (.pair (coeApp N.coe A A' (.fst p))
        (coeApp N.coe (inst0 (.fst p) B) (.app B'' (coeApp N.coe A A' (.fst p))) (.snd p)))) := by
  show CoeSigmaRow P N _ _ (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) _
    (.pair (coeApp N.coe (Presentation.subst σ A) (Presentation.subst σ A')
        (.fst (Presentation.subst σ p)))
      (coeApp N.coe (Presentation.subst σ (inst0 (.fst p) B))
        (.app (Presentation.subst σ B'') (coeApp N.coe (Presentation.subst σ A)
          (Presentation.subst σ A') (.fst (Presentation.subst σ p))))
        (.snd (Presentation.subst σ p))))
  rw [subst_inst0]
  exact .pair

theorem CoeSigmaRow.subst {A' B'' X p r : Tm Head n} (h : CoeSigmaRow P N A' B'' X p r) :
    CoeSigmaRow P N (Presentation.subst σ A') (Presentation.subst σ B'') (Presentation.subst σ X)
      (Presentation.subst σ p) (Presentation.subst σ r) := by
  cases h with
  | pair => exact CoeSigmaRow.subst_pair σ
  | star form notSigma =>
      obtain ⟨key, view⟩ := form
      exact .star ⟨key, view.subst σ⟩ fun A B e => by
        obtain ⟨A₀, B₀, rfl⟩ := headView_subst_eq_sigma view e
        exact notSigma A₀ B₀ rfl

end Stability

/-! ## Determinism -/

section Determinism

variable {n : Nat}

theorem CoeTarget.deterministic {X Y d r X' Y' d' r' : Tm Head n}
    (h : CoeTarget P N X Y d r) (h' : CoeTarget P N X' Y' d' r') (hX : X = X') (hY : Y = Y')
    (hd : d = d') : r' = r := by
  cases h <;> cases h' <;>
    first
      | exact hd.symm
      | (subst hX hd; cases hY; rfl)
      | (cases hY; done)
      | (cases hY; contradiction)
      | exact absurd hY (‹MethodTarget P _›.notHead _)
      | exact absurd hY.symm (‹MethodTarget P _›.notHead _)
      | exact absurd hY (‹MethodTarget P _›.notPi _ _)
      | exact absurd hY.symm (‹MethodTarget P _›.notPi _ _)
      | exact absurd hY (‹MethodTarget P _›.notSigma _ _)
      | exact absurd hY.symm (‹MethodTarget P _›.notSigma _ _)
      | exact absurd hY (‹MethodTarget P _›.notConst _ ‹_›)
      | exact absurd hY.symm (‹MethodTarget P _›.notConst _ ‹_›)

variable [LevelOrder L] in
theorem CoeUniv.deterministic {T X d r T' X' d' r' : Tm Head n} (h : CoeUniv P T X d r)
    (h' : CoeUniv P T' X' d' r') (hT : T = T') (hX : X = X') (hd : d = d') : r' = r := by
  cases h with
  | method hu le =>
      cases h' with
      | method _ _ => exact hd.symm
      | star _ _ above =>
          exact absurd (lt_of_lt_of_le (above _ _ hT.symm hX.symm hu) le) (lt_irrefl _)
  | star _ _ above =>
      cases h' with
      | method hu le => exact absurd (lt_of_lt_of_le (above _ _ hT hX hu) le) (lt_irrefl _)
      | star _ _ _ => rfl

theorem CoeConst.deterministic {C X d r C' X' d' r' : Tm Head n}
    (h : CoeConst P C X d r) (h' : CoeConst P C' X' d' r') (hC : C = C') (hX : X = X')
    (hd : d = d') : r' = r := by
  cases h with
  | method =>
      cases h' with
      | method => exact hd.symm
      | star _ ne => exact absurd (hX.symm.trans hC) ne
  | star _ ne =>
      cases h' with
      | method => exact absurd (hX.trans hC.symm) ne
      | star _ _ => rfl

theorem CoePiRow.deterministic {A' B'' X f r A₂ B₂ X₂ f₂ r₂ : Tm Head n}
    (h : CoePiRow P N A' B'' X f r) (h' : CoePiRow P N A₂ B₂ X₂ f₂ r₂) (hA : A' = A₂)
    (hB : B'' = B₂) (hX : X = X₂) (hf : f = f₂) : r₂ = r := by
  cases h with
  | lam =>
      cases h' with
      | lam =>
          cases hX
          subst hA hB hf
          rfl
      | star _ notPi => exact absurd hX.symm (notPi _ _)
  | star _ notPi =>
      cases h' with
      | lam => exact absurd hX (notPi _ _)
      | star _ _ => rfl

theorem CoeSigmaRow.deterministic {A' B'' X p r A₂ B₂ X₂ p₂ r₂ : Tm Head n}
    (h : CoeSigmaRow P N A' B'' X p r) (h' : CoeSigmaRow P N A₂ B₂ X₂ p₂ r₂) (hA : A' = A₂)
    (hB : B'' = B₂) (hX : X = X₂) (hp : p = p₂) : r₂ = r := by
  cases h with
  | pair =>
      cases h' with
      | pair =>
          cases hX
          subst hA hB hp
          rfl
      | star _ notSigma => exact absurd hX.symm (notSigma _ _)
  | star _ notSigma =>
      cases h' with
      | pair => exact absurd hX (notSigma _ _)
      | star _ _ => rfl

end Determinism

/-! ## Root computations at spines of one constant -/

section Spines

/-- The steps at spines of the constant `c` whose arguments are related to the
reduct by `rel`. -/
def SpineStep (c : DeclName) (rel : ∀ {n : Nat}, List (Tm Head n) → Tm Head n → Prop)
    {n : Nat} (l r : Tm Head n) : Prop :=
  ∃ args, l = appSpine (.const c) args ∧ rel args r

/-- Arguments related to a reduct stay related under every substitution. -/
def SpineStable (rel : ∀ {n : Nat}, List (Tm Head n) → Tm Head n → Prop) : Prop :=
  ∀ {n m : Nat} (σ : Sub Head n m) {args : List (Tm Head n)} {r : Tm Head n}, rel args r →
    rel (args.map (subst σ)) (subst σ r)

theorem SpineStep.subst {c : DeclName} {rel : ∀ {n : Nat}, List (Tm Head n) → Tm Head n → Prop}
    (stable : SpineStable rel) {n m : Nat} (σ : Sub Head n m) {l r : Tm Head n}
    (step : SpineStep c rel l r) :
    SpineStep c rel (Presentation.subst σ l) (Presentation.subst σ r) := by
  obtain ⟨args, rfl, h⟩ := step
  exact ⟨_, subst_appSpine σ _ args, stable σ h⟩

/-- The root computation of the steps at spines of `c`. -/
def spineComputation (c : DeclName) (rel : ∀ {n : Nat}, List (Tm Head n) → Tm Head n → Prop)
    (stable : SpineStable rel) : RootComputation Head where
  step := SpineStep c rel
  rename := fun {_ _} ρ {_ _} step => by
    simpa only [subst_renSub] using SpineStep.subst stable (renSub ρ) step
  substitute := fun {_ _} σ {_ _} step => SpineStep.subst stable σ step

variable {c : DeclName} {rel : ∀ {n : Nat}, List (Tm Head n) → Tm Head n → Prop}
  {stable : SpineStable rel}

theorem spineComputation_headed : HeadedBy c (spineComputation c rel stable) :=
  fun _ _ _ ⟨args, e, _⟩ => ⟨args, e⟩

theorem spineComputation_deterministic
    (det : ∀ {n : Nat} {args : List (Tm Head n)} {r r' : Tm Head n}, rel args r → rel args r' →
      r' = r) :
    Deterministic (spineComputation c rel stable) := by
  intro n t u u' ⟨args, e, h⟩ ⟨args', e', h'⟩
  rw [e] at e'
  obtain ⟨-, rfl⟩ := appSpine_const_injective e'
  exact det h h'

theorem spineComputation_spine {roles : Roles Head} {arity : Nat} {inspect : InspectTree}
    (role : roles c = .computes arity inspect)
    (shape : ∀ {n : Nat} {args : List (Tm Head n)} {r : Tm Head n}, rel args r →
      args.length = arity ∧ inspect.Accepts roles args) :
    SpineShaped roles (spineComputation c rel stable) := by
  intro n t u ⟨args, e, h⟩
  exact ⟨c, arity, inspect, args, role, e, (shape h).1, (shape h).2⟩

end Spines

/-! ## The transport's computations -/

variable (P N)

/-- The arguments of `coe` and their reducts. -/
def CoeArgs {n : Nat} (args : List (Tm Head n)) (r : Tm Head n) : Prop :=
  ∃ X Y d, args = [X, Y, d] ∧ CoeTarget P N X Y d r

variable [LevelOrder L] in
/-- The arguments of `coeU` and their reducts. -/
def CoeUArgs {n : Nat} (args : List (Tm Head n)) (r : Tm Head n) : Prop :=
  ∃ T X d, args = [T, X, d] ∧ CoeUniv P T X d r

/-- The arguments of `coeConst` and their reducts. -/
def CoeConstArgs {n : Nat} (args : List (Tm Head n)) (r : Tm Head n) : Prop :=
  ∃ C X d, args = [C, X, d] ∧ CoeConst P C X d r

/-- The arguments of `coePi` and their reducts. -/
def CoePiArgs {n : Nat} (args : List (Tm Head n)) (r : Tm Head n) : Prop :=
  ∃ A' B'' X f, args = [A', B'', X, f] ∧ CoePiRow P N A' B'' X f r

/-- The arguments of `coeSigma` and their reducts. -/
def CoeSigmaArgs {n : Nat} (args : List (Tm Head n)) (r : Tm Head n) : Prop :=
  ∃ A' B'' X p, args = [A', B'', X, p] ∧ CoeSigmaRow P N A' B'' X p r

/-- The arguments of identity elimination and their reduct on the value side:
the transport of the method along the motive. -/
def TransportJArgs (coe : DeclName) {n : Nat} (args : List (Tm Head n)) (r : Tm Head n) :
    Prop :=
  ∃ a₀ a₁ a₂ a₃ a₄ a₅, args = [a₀, a₁, a₂, a₃, a₄, a₅] ∧
    r = coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃

variable {P N}

theorem coeArgs_stable : SpineStable (CoeArgs P N) := by
  intro n m σ args r ⟨X, Y, d, e, h⟩
  subst e
  exact ⟨_, _, _, rfl, h.subst σ⟩

variable [LevelOrder L] in
theorem coeUArgs_stable : SpineStable (CoeUArgs P) := by
  intro n m σ args r ⟨T, X, d, e, h⟩
  subst e
  exact ⟨_, _, _, rfl, h.subst σ⟩

theorem coeConstArgs_stable : SpineStable (CoeConstArgs P) := by
  intro n m σ args r ⟨C, X, d, e, h⟩
  subst e
  exact ⟨_, _, _, rfl, h.subst σ⟩

theorem coePiArgs_stable : SpineStable (CoePiArgs P N) := by
  intro n m σ args r ⟨A', B'', X, f, e, h⟩
  subst e
  exact ⟨_, _, _, _, rfl, h.subst σ⟩

theorem coeSigmaArgs_stable : SpineStable (CoeSigmaArgs P N) := by
  intro n m σ args r ⟨A', B'', X, p, e, h⟩
  subst e
  exact ⟨_, _, _, _, rfl, h.subst σ⟩

theorem transportJArgs_stable {coe : DeclName} : SpineStable (Head := Head) (TransportJArgs coe) := by
  intro n m σ args r ⟨a₀, a₁, a₂, a₃, a₄, a₅, e, er⟩
  subst e er
  exact ⟨_, _, _, _, _, _, rfl, rfl⟩

variable (P N)

/-- The rows of `coe`. -/
def coeComputation : RootComputation Head := spineComputation N.coe (CoeArgs P N) coeArgs_stable

variable [LevelOrder L] in
/-- The rows of `coeU`. -/
def coeUComputation : RootComputation Head := spineComputation N.coeU (CoeUArgs P) coeUArgs_stable

/-- The rows of `coeConst`, which transports into a type constant. -/
def coeConstComputation : RootComputation Head :=
  spineComputation N.coeConst (CoeConstArgs P) coeConstArgs_stable

/-- The rows of `coePi`. -/
def coePiComputation : RootComputation Head :=
  spineComputation N.coePi (CoePiArgs P N) coePiArgs_stable

/-- The rows of `coeSigma`. -/
def coeSigmaComputation : RootComputation Head :=
  spineComputation N.coeSigma (CoeSigmaArgs P N) coeSigmaArgs_stable

/-- Identity elimination on the value side: the transport of the method along
the motive, `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`. -/
def transportJ (J coe : DeclName) : RootComputation Head :=
  spineComputation J (TransportJArgs coe) transportJArgs_stable

variable {P N}

theorem transportJ_step {J coe : DeclName} {n : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head n) :
    (transportJ J coe).step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
      (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃) :=
  ⟨_, rfl, _, _, _, _, _, _, rfl, rfl⟩

/-! ## Heads, shapes and determinism of the computations -/

section Shapes

theorem coeComputation_headed : HeadedBy N.coe (coeComputation P N) := spineComputation_headed
variable [LevelOrder L] in
theorem coeUComputation_headed : HeadedBy N.coeU (coeUComputation P N) := spineComputation_headed
theorem coeConstComputation_headed : HeadedBy N.coeConst (coeConstComputation P N) :=
  spineComputation_headed
theorem coePiComputation_headed : HeadedBy N.coePi (coePiComputation P N) :=
  spineComputation_headed
theorem coeSigmaComputation_headed : HeadedBy N.coeSigma (coeSigmaComputation P N) :=
  spineComputation_headed
theorem transportJ_headed {J coe : DeclName} : HeadedBy J (transportJ (Head := Head) J coe) :=
  spineComputation_headed

theorem coeComputation_deterministic : Deterministic (coeComputation P N) :=
  spineComputation_deterministic fun ⟨_, _, _, e, h⟩ ⟨_, _, _, e', h'⟩ => by
    rw [e] at e'
    simp only [List.cons.injEq, and_true] at e'
    obtain ⟨hX, hY, hd⟩ := e'
    exact h.deterministic h' hX hY hd

variable [LevelOrder L] in
theorem coeUComputation_deterministic : Deterministic (coeUComputation P N) :=
  spineComputation_deterministic fun ⟨_, _, _, e, h⟩ ⟨_, _, _, e', h'⟩ => by
    rw [e] at e'
    simp only [List.cons.injEq, and_true] at e'
    obtain ⟨hT, hX, hd⟩ := e'
    exact h.deterministic h' hT hX hd

theorem coeConstComputation_deterministic : Deterministic (coeConstComputation P N) :=
  spineComputation_deterministic fun ⟨_, _, _, e, h⟩ ⟨_, _, _, e', h'⟩ => by
    rw [e] at e'
    simp only [List.cons.injEq, and_true] at e'
    obtain ⟨hC, hX, hd⟩ := e'
    exact h.deterministic h' hC hX hd

theorem coePiComputation_deterministic : Deterministic (coePiComputation P N) :=
  spineComputation_deterministic fun ⟨_, _, _, _, e, h⟩ ⟨_, _, _, _, e', h'⟩ => by
    rw [e] at e'
    simp only [List.cons.injEq, and_true] at e'
    obtain ⟨hA, hB, hX, hf⟩ := e'
    exact h.deterministic h' hA hB hX hf

theorem coeSigmaComputation_deterministic : Deterministic (coeSigmaComputation P N) :=
  spineComputation_deterministic fun ⟨_, _, _, _, e, h⟩ ⟨_, _, _, _, e', h'⟩ => by
    rw [e] at e'
    simp only [List.cons.injEq, and_true] at e'
    obtain ⟨hA, hB, hX, hp⟩ := e'
    exact h.deterministic h' hA hB hX hp

theorem transportJ_deterministic {J coe : DeclName} :
    Deterministic (transportJ (Head := Head) J coe) :=
  spineComputation_deterministic fun ⟨_, _, _, _, _, _, e, er⟩ ⟨_, _, _, _, _, _, e', er'⟩ => by
    rw [e] at e'
    simp only [List.cons.injEq, and_true] at e'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := e'
    rw [er, er']

/-- The target of a row of `coe` is a head form, when the codes do not compute. -/
theorem CoeTarget.headForm (propStuck : ∀ arity inspect, P.roles P.prop ≠ .computes arity inspect)
    {n : Nat} {X Y d r : Tm Head n} (h : CoeTarget P N X Y d r) : HeadForm P.roles Y := by
  cases h with
  | univ _ => exact ⟨_, .head _⟩
  | ground _ => exact ⟨_, .head _⟩
  | pi => exact ⟨_, .pi _ _⟩
  | sigma => exact ⟨_, .sigma _ _⟩
  | const hc => exact ⟨_, .spine [] (hc.stuck propStuck)⟩
  | method target => exact target.form

theorem coeComputation_spine (role : P.roles N.coe = .computes 3 (headAt 1))
    (propStuck : ∀ arity inspect, P.roles P.prop ≠ .computes arity inspect) :
    SpineShaped P.roles (coeComputation P N) :=
  spineComputation_spine role fun ⟨X, _, d, e, h⟩ => by
    subst e
    obtain ⟨key, view⟩ := h.headForm propStuck
    exact ⟨rfl, .headForm (before := [X]) (after := [d]) rfl view (.leaf _)⟩

variable [LevelOrder L] in
theorem coeUComputation_spine (role : P.roles N.coeU = .computes 3 headAtBoth) :
    SpineShaped P.roles (coeUComputation P N) :=
  spineComputation_spine role fun ⟨T, X, d, e, h⟩ => by
    subst e
    have forms : HeadForm P.roles T ∧ HeadForm P.roles X := by
      cases h with
      | method _ _ => exact ⟨⟨_, .head _⟩, ⟨_, .head _⟩⟩
      | star formT formX _ => exact ⟨formT, formX⟩
    obtain ⟨⟨keyT, viewT⟩, ⟨keyX, viewX⟩⟩ := forms
    exact ⟨rfl, .headForm (before := []) (after := [X, d]) rfl viewT
      (.headForm (before := [T]) (after := [d]) rfl viewX (.leaf _))⟩

theorem coeConstComputation_spine (role : P.roles N.coeConst = .computes 3 (headAt 1))
    (propStuck : ∀ arity inspect, P.roles P.prop ≠ .computes arity inspect) :
    SpineShaped P.roles (coeConstComputation P N) :=
  spineComputation_spine role fun ⟨C, X, d, e, h⟩ => by
    subst e
    have form : HeadForm P.roles X := by
      cases h with
      | method hc => exact ⟨_, .spine [] (hc.stuck propStuck)⟩
      | star form _ => exact form
    obtain ⟨key, view⟩ := form
    exact ⟨rfl, .headForm (before := [C]) (after := [d]) rfl view (.leaf _)⟩

theorem coePiComputation_spine (role : P.roles N.coePi = .computes 4 (headAt 2)) :
    SpineShaped P.roles (coePiComputation P N) :=
  spineComputation_spine role fun ⟨A', B'', X, f, e, h⟩ => by
    subst e
    have form : HeadForm P.roles X := by
      cases h with
      | lam => exact ⟨_, .pi _ _⟩
      | star form _ => exact form
    obtain ⟨key, view⟩ := form
    exact ⟨rfl, .headForm (before := [A', B'']) (after := [f]) rfl view (.leaf _)⟩

theorem coeSigmaComputation_spine (role : P.roles N.coeSigma = .computes 4 (headAt 2)) :
    SpineShaped P.roles (coeSigmaComputation P N) :=
  spineComputation_spine role fun ⟨A', B'', X, p, e, h⟩ => by
    subst e
    have form : HeadForm P.roles X := by
      cases h with
      | pair => exact ⟨_, .sigma _ _⟩
      | star form _ => exact form
    obtain ⟨key, view⟩ := form
    exact ⟨rfl, .headForm (before := [A', B'']) (after := [p]) rfl view (.leaf _)⟩

theorem transportJ_spine {roles : Roles Head} {J coe : DeclName}
    (role : roles J = .computes 6 .leaf) : SpineShaped roles (transportJ J coe) :=
  spineComputation_spine role fun ⟨_, _, _, _, _, _, e, _⟩ => by
    subst e
    exact ⟨rfl, .leaf _⟩

end Shapes

end Realizability
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
