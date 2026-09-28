import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup

/-!
# Weak-head reduction for rule packages with declared constants

A declared constant has a role. It is rigid (an assumption, a parameter, or a
type constant without constructors), the type constant of a simple inductive
type, a constructor, or a computing constant with an authored arity and an
inspection skeleton. Definitions by equations or case trees, recursors and the
identity eliminator are computing constants.

The skeleton lists the arguments the constant inspects, in order, and the shape
each must reach. At a constructor inspection the value must be a constructor
spine or reflexivity, which is then replaced by its fields; at a head-form
inspection it must be a head form (a head, a type or value former,
reflexivity, or a spine of a constant that does not compute, rigid spines
included), which stays in place.

Weak-head reduction contracts a beta redex, a projection of a pair, or a
declared root step at the head. Otherwise it reduces in the function position
of an application, under a projection, or at the value the skeleton of a
computing constant applied to exactly its arity inspects next, after the values
it accepts. That value may lie inside a constructor spine accepted earlier:
nested positions are reduced as the skeleton reaches them. The rule package
must place its root steps at spines whose inspected values all have the
required shapes; then reduction is deterministic, neutral terms and the
accepted forms do not reduce, and reduction commutes with renaming and
substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

/-! ## Inspection skeletons -/

/-- The shape an inspected argument must reach before inspection continues. -/
inductive Inspection where
  /-- A constructor spine or reflexivity: case trees, recursors, and `J` at `refl`. -/
  | constructor
  /-- Any head form, rigid spines included: the value-side type case only. -/
  | headForm
  deriving DecidableEq, Repr

/-- The type and value formers a head-form inspection distinguishes. -/
inductive FormerTag where
  | head
  | pi
  | sigma
  | id
  | lam
  | pair
  deriving DecidableEq, Repr

/-- What an inspection found: the constant heading a spine, a former, or
reflexivity. -/
inductive InspectKey where
  | const (name : DeclName)
  | former (tag : FormerTag)
  | refl
  deriving DecidableEq, Repr

/-- Which arguments a computing constant inspects, in order. A split inspects
the value at `position` and continues with `next` of what it found. Positions
index the current list of values, in which an inspected constructor spine has
been replaced by its arguments. -/
inductive InspectTree where
  | leaf
  | split (position : Nat) (shape : Inspection) (next : InspectKey → InspectTree)

namespace InspectTree

/-- The position a skeleton inspects first, if any. -/
def position? : InspectTree → Option Nat
  | .leaf => none
  | .split position _ _ => some position

/-- The rest of a skeleton once its first inspection has found `key`. -/
def child : InspectTree → InspectKey → InspectTree
  | .leaf, _ => .leaf
  | .split _ _ next, key => next key

end InspectTree

/-! ## Roles of declared constants -/

/-- A field of a constructor of a simple inductive type: the type itself, or a
closed type that does not mention it. -/
inductive Field (Head : Type) where
  | recursive
  | closed (type : Tm Head 0)

/-- How a declared constant behaves under reduction. -/
inductive Role (Head : Type) where
  /-- Never computes and has no constructors: a rigid head. -/
  | rigid
  /-- The type constant of a simple inductive type, with its constructors. -/
  | inductive (constructors : List (DeclName × List (Field Head)))
  /-- A constructor with the given number of fields. -/
  | constructor (arity : Nat)
  /-- Computes when applied to exactly `arity` arguments, once the values its
  inspection skeleton reaches have the shapes its splits require. -/
  | computes (arity : Nat) (inspect : InspectTree)

/-- The role of every constant of a rule package. -/
abbrev Roles (Head : Type) := DeclName → Role Head

/-- The constructors an inductive type lists are declared as constructors of
their number of fields, under distinct names. -/
structure ConstructorsDeclared (roles : Roles Head) : Prop where
  arity : ∀ {T : DeclName} {constructors : List (DeclName × List (Field Head))}
    {k : DeclName} {fields : List (Field Head)}, roles T = .inductive constructors →
    (k, fields) ∈ constructors → roles k = .constructor fields.length
  distinct : ∀ {T : DeclName} {constructors : List (DeclName × List (Field Head))},
    roles T = .inductive constructors → (constructors.map Prod.fst).Nodup

/-- A constructor's name determines its fields. -/
theorem ConstructorsDeclared.fields_unique {roles : Roles Head}
    (declared : ConstructorsDeclared roles) {T : DeclName}
    {constructors : List (DeclName × List (Field Head))}
    (role : roles T = .inductive constructors) {k : DeclName}
    {fields fields' : List (Field Head)} (mem : (k, fields) ∈ constructors)
    (mem' : (k, fields') ∈ constructors) : fields = fields' :=
  (Prod.mk.inj (List.inj_on_of_nodup_map (declared.distinct role) mem mem' rfl)).2

/-- No constant is an inductive type. -/
theorem ConstructorsDeclared.of_no_inductive {roles : Roles Head}
    (none : ∀ T constructors, roles T ≠ .inductive constructors) :
    ConstructorsDeclared roles where
  arity := fun role => absurd role (none _ _)
  distinct := fun role => absurd role (none _ _)

/-! ## Head spines -/

/-- Apply a head to arguments, left to right. -/
def appSpine {n : Nat} (f : Tm Head n) (as : List (Tm Head n)) : Tm Head n :=
  as.foldl Tm.app f

@[simp] theorem appSpine_nil {n : Nat} (f : Tm Head n) : appSpine f [] = f := rfl

@[simp] theorem appSpine_cons {n : Nat} (f a : Tm Head n) (as : List (Tm Head n)) :
    appSpine f (a :: as) = appSpine (.app f a) as := rfl

theorem appSpine_append {n : Nat} (f : Tm Head n) (as bs : List (Tm Head n)) :
    appSpine f (as ++ bs) = appSpine (appSpine f as) bs := by
  simp [appSpine, List.foldl_append]

@[simp] theorem appSpine_concat {n : Nat} (f : Tm Head n) (as : List (Tm Head n))
    (a : Tm Head n) : appSpine f (as ++ [a]) = .app (appSpine f as) a := by
  simp [appSpine, List.foldl_append]

theorem rename_appSpine {n m : Nat} (ρ : Ren n m) (f : Tm Head n)
    (as : List (Tm Head n)) :
    rename ρ (appSpine f as) = appSpine (rename ρ f) (as.map (rename ρ)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simpa [rename] using ih (.app f a)

theorem subst_appSpine {n m : Nat} (σ : Sub Head n m) (f : Tm Head n)
    (as : List (Tm Head n)) :
    subst σ (appSpine f as) = appSpine (subst σ f) (as.map (subst σ)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simpa [subst] using ih (.app f a)

/-- The head of a term and its arguments. -/
def headArgs : {n : Nat} → Tm Head n → Tm Head n × List (Tm Head n)
  | _, .app f a => ((headArgs f).1, (headArgs f).2 ++ [a])
  | _, t => (t, [])

/-- A term whose head is not an application. -/
def NotApp {n : Nat} : Tm Head n → Prop
  | .app _ _ => False
  | _ => True

theorem headArgs_appSpine {n : Nat} {f : Tm Head n} (notApp : NotApp f)
    (as : List (Tm Head n)) : headArgs (appSpine f as) = (f, as) := by
  induction as using List.reverseRecOn with
  | nil =>
      cases f <;> simp_all [NotApp, headArgs]
  | append_singleton as a ih =>
      rw [appSpine_concat]
      simp [headArgs, ih]

theorem appSpine_injective {n : Nat} {f g : Tm Head n} (hf : NotApp f) (hg : NotApp g)
    {as bs : List (Tm Head n)} (equal : appSpine f as = appSpine g bs) :
    f = g ∧ as = bs := by
  have := congrArg headArgs equal
  rw [headArgs_appSpine hf, headArgs_appSpine hg] at this
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem appSpine_const_injective {n : Nat} {c c' : DeclName} {as bs : List (Tm Head n)}
    (equal : appSpine (.const c) as = appSpine (.const c') bs) : c = c' ∧ as = bs := by
  obtain ⟨heads, args⟩ := appSpine_injective (by trivial) (by trivial) equal
  exact ⟨Tm.const.inj heads, args⟩

/-- A constant spine that is an application has a nonempty argument list. -/
theorem appSpine_const_eq_app {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {f a : Tm Head n} (equal : appSpine (.const c) as = .app f a) :
    ∃ init, as = init ++ [a] ∧ f = appSpine (.const c) init := by
  induction as using List.reverseRecOn with
  | nil => simp at equal
  | append_singleton init last _ =>
      rw [appSpine_concat] at equal
      obtain ⟨hf, ha⟩ := Tm.app.inj equal
      exact ⟨init, by rw [ha], hf.symm⟩

theorem appSpine_const_ne_lam {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {body : Tm Head (n + 1)} {a : Tm Head n} :
    appSpine (.const c) as ≠ .app (.lam body) a := by
  intro equal
  obtain ⟨init, _, hf⟩ := appSpine_const_eq_app equal
  cases init using List.reverseRecOn with
  | nil => simp at hf
  | append_singleton init last _ =>
      rw [appSpine_concat] at hf
      cases hf

/-- A constant spine is not a projection. -/
theorem appSpine_const_ne_fst {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {p : Tm Head n} : appSpine (.const c) as ≠ .fst p := by
  intro equal
  cases as using List.reverseRecOn with
  | nil => cases equal
  | append_singleton init last _ => rw [appSpine_concat] at equal; cases equal

theorem appSpine_const_ne_snd {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {p : Tm Head n} : appSpine (.const c) as ≠ .snd p := by
  intro equal
  cases as using List.reverseRecOn with
  | nil => cases equal
  | append_singleton init last _ => rw [appSpine_concat] at equal; cases equal

theorem appSpine_const_ne_var {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {i : Fin n} : appSpine (.const c) as ≠ .var i := by
  intro equal
  cases as using List.reverseRecOn with
  | nil => cases equal
  | append_singleton init last _ => rw [appSpine_concat] at equal; cases equal

theorem appSpine_const_ne_pair {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {a b : Tm Head n} : appSpine (.const c) as ≠ .pair a b := by
  intro equal
  cases as using List.reverseRecOn with
  | nil => cases equal
  | append_singleton init last _ => rw [appSpine_concat] at equal; cases equal

theorem appSpine_const_ne_refl {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {a : Tm Head n} : appSpine (.const c) as ≠ .refl a := by
  intro equal
  cases as using List.reverseRecOn with
  | nil => cases equal
  | append_singleton init last _ => rw [appSpine_concat] at equal; cases equal

theorem appSpine_const_ne_lam' {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {body : Tm Head (n + 1)} : appSpine (.const c) as ≠ .lam body := by
  intro equal
  cases as using List.reverseRecOn with
  | nil => cases equal
  | append_singleton init last _ => rw [appSpine_concat] at equal; cases equal

/-- A constant spine is the constant or an application. -/
theorem appSpine_const_cases {n : Nat} (c : DeclName) (as : List (Tm Head n)) :
    appSpine (.const c) as = .const c ∨ ∃ f a, appSpine (.const c) as = .app f a := by
  rcases List.eq_nil_or_concat as with rfl | ⟨init, last, rfl⟩
  · exact .inl rfl
  · rw [List.concat_eq_append, appSpine_concat]
    exact .inr ⟨_, _, rfl⟩

/-- A spine extended by one argument. The helpers below avoid `simp`, so that
their consequences stay free of axioms. -/
private theorem appSpine_snoc {n : Nat} :
    ∀ (f : Tm Head n) (as : List (Tm Head n)) (x : Tm Head n),
      appSpine f (as ++ [x]) = .app (appSpine f as) x
  | _, [], _ => rfl
  | f, a :: as, x => appSpine_snoc (.app f a) as x

/-- A spine with at least one argument is an application. -/
private theorem appSpine_app_isApp {n : Nat} :
    ∀ (f a : Tm Head n) (as : List (Tm Head n)), ∃ g y, appSpine (.app f a) as = .app g y
  | f, a, [] => ⟨f, a, rfl⟩
  | f, a, b :: as => appSpine_app_isApp (.app f a) b as

/-- A spine that is an application: no arguments and an application head, or
a last argument. -/
private theorem appSpine_eq_app {n : Nat} {g x : Tm Head n} :
    ∀ {f : Tm Head n} {as : List (Tm Head n)}, appSpine f as = .app g x →
      (as = [] ∧ f = .app g x) ∨ ∃ init, as = init ++ [x] ∧ g = appSpine f init
  | _, [], h => .inl ⟨rfl, h⟩
  | f, a :: as, h => by
      rcases appSpine_eq_app (f := .app f a) (as := as) h with ⟨rfl, e⟩ | ⟨init, rfl, rfl⟩
      · obtain ⟨hg, hx⟩ := Tm.app.inj e
        exact .inr ⟨[], congrArg (fun y => [y]) hx, hg.symm⟩
      · exact .inr ⟨a :: init, rfl, rfl⟩

/-- A term whose renaming is a spine of a constant is such a spine. -/
private theorem rename_eq_constSpine {c : DeclName} :
    ∀ {n m : Nat} {ρ : Ren n m} {t : Tm Head n} {as : List (Tm Head m)},
      rename ρ t = appSpine (.const c) as → ∃ as', t = appSpine (.const c) as'
  | _, _, ρ, .app g x, _, h => by
      have h' : appSpine (.const c) _ = .app (rename ρ g) (rename ρ x) := h.symm
      rcases appSpine_eq_app h' with ⟨_, e⟩ | ⟨init, _, hg⟩
      · cases e
      · obtain ⟨init', rfl⟩ := rename_eq_constSpine hg
        exact ⟨init' ++ [x], (appSpine_snoc _ _ _).symm⟩
  | _, _, _, .const _, [], h => by
      injection h with _ e
      exact ⟨[], by rw [e]; rfl⟩
  | _, _, _, .const _, a :: as, h => by
      obtain ⟨g, y, e⟩ := appSpine_app_isApp (.const c) a as
      cases h.trans e
  | _, _, _, .var _, as, h | _, _, _, .head _, as, h | _, _, _, .pi _ _, as, h
  | _, _, _, .sigma _ _, as, h | _, _, _, .id _ _ _, as, h | _, _, _, .lam _, as, h
  | _, _, _, .pair _ _, as, h | _, _, _, .fst _, as, h | _, _, _, .snd _, as, h
  | _, _, _, .refl _, as, h => by
      rcases as with _ | ⟨a, as⟩
      · cases h
      · obtain ⟨g, y, e⟩ := appSpine_app_isApp (.const c) a as
        cases h.trans e

/-- The length of a list split around one of its elements. -/
private theorem length_append_cons {α : Type _} (a : α) (after : List α) :
    ∀ before : List α, (before ++ a :: after).length = before.length + 1 + after.length
  | [] => (Nat.add_comm (0 + 1) after.length).symm
  | _ :: before => (congrArg (· + 1) (length_append_cons a after before)).trans
      (Nat.add_right_comm _ _ _)

/-! ## Canonical forms and head forms -/

/-- A canonical form an eliminator can inspect: reflexivity or a constructor
spine. -/
def Canonical (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  (∃ x, t = .refl x) ∨
    ∃ k arity args, roles k = .constructor arity ∧ t = appSpine (.const k) args

/-- A value a constructor inspection accepts: a constructor spine, whose key
is its constructor and whose fields are its arguments, or reflexivity, whose
field is its point. -/
inductive ConstructorView (roles : Roles Head) {n : Nat} :
    Tm Head n → InspectKey → List (Tm Head n) → Prop where
  | spine {c : DeclName} {arity : Nat} (args : List (Tm Head n)) :
      roles c = .constructor arity →
        ConstructorView roles (appSpine (.const c) args) (.const c) args
  | refl (a : Tm Head n) : ConstructorView roles (.refl a) .refl [a]

theorem ConstructorView.canonical {roles : Roles Head} {n : Nat} {t : Tm Head n}
    {key : InspectKey} {fields : List (Tm Head n)} (view : ConstructorView roles t key fields) :
    Canonical roles t := by
  cases view with
  | spine _ role => exact .inr ⟨_, _, _, role, rfl⟩
  | refl a => exact .inl ⟨a, rfl⟩

theorem Canonical.view {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (canonical : Canonical roles t) : ∃ key fields, ConstructorView roles t key fields := by
  rcases canonical with ⟨x, rfl⟩ | ⟨k, arity, args, role, rfl⟩
  · exact ⟨_, _, .refl x⟩
  · exact ⟨_, _, .spine args role⟩

private theorem ConstructorView.unique_of_eq {roles : Roles Head} {n : Nat} {t t' : Tm Head n}
    {key key' : InspectKey} {fields fields' : List (Tm Head n)}
    (view : ConstructorView roles t key fields) (view' : ConstructorView roles t' key' fields')
    (same : t = t') : key = key' ∧ fields = fields' := by
  cases view <;> cases view'
  · obtain ⟨rfl, rfl⟩ := appSpine_const_injective same
    exact ⟨rfl, rfl⟩
  · exact absurd same appSpine_const_ne_refl
  · exact absurd same.symm appSpine_const_ne_refl
  · cases same
    exact ⟨rfl, rfl⟩

/-- A constructor form determines its key and its fields. -/
theorem ConstructorView.unique {roles : Roles Head} {n : Nat} {t : Tm Head n}
    {key key' : InspectKey} {fields fields' : List (Tm Head n)}
    (view : ConstructorView roles t key fields) (view' : ConstructorView roles t key' fields') :
    key = key' ∧ fields = fields' :=
  view.unique_of_eq view' rfl

/-- The key and the fields determine a constructor form. -/
theorem ConstructorView.inj {roles : Roles Head} {n : Nat} {t t' : Tm Head n}
    {key : InspectKey} {fields : List (Tm Head n)} (view : ConstructorView roles t key fields)
    (view' : ConstructorView roles t' key fields) : t = t' := by
  cases view with
  | spine args role =>
      cases view' with
      | spine _ _ => rfl
  | refl a =>
      cases view' with
      | refl _ => rfl

theorem ConstructorView.rename {roles : Roles Head} {n : Nat} {t : Tm Head n}
    {key : InspectKey} {fields : List (Tm Head n)} (view : ConstructorView roles t key fields)
    {m : Nat} (ρ : Ren n m) :
    ConstructorView roles (Presentation.rename ρ t) key (fields.map (Presentation.rename ρ)) := by
  cases view with
  | spine args role =>
      rw [rename_appSpine]
      exact .spine _ role
  | refl a => exact .refl _

theorem ConstructorView.subst {roles : Roles Head} {n : Nat} {t : Tm Head n}
    {key : InspectKey} {fields : List (Tm Head n)} (view : ConstructorView roles t key fields)
    {m : Nat} (σ : Sub Head n m) :
    ConstructorView roles (Presentation.subst σ t) key (fields.map (Presentation.subst σ)) := by
  cases view with
  | spine args role =>
      rw [subst_appSpine]
      exact .spine _ role
  | refl a => exact .refl _

/-- A head form and the key a head-form inspection reads from it: a head, a
type or value former, reflexivity, or a spine of a constant that does not
compute, rigid spines included. -/
inductive HeadView (roles : Roles Head) {n : Nat} : Tm Head n → InspectKey → Prop where
  | head (h : Head) : HeadView roles (.head h) (.former .head)
  | pi (A : Tm Head n) (B : Tm Head (n + 1)) : HeadView roles (.pi A B) (.former .pi)
  | sigma (A : Tm Head n) (B : Tm Head (n + 1)) : HeadView roles (.sigma A B) (.former .sigma)
  | id (A a b : Tm Head n) : HeadView roles (.id A a b) (.former .id)
  | lam (body : Tm Head (n + 1)) : HeadView roles (.lam body) (.former .lam)
  | pair (a b : Tm Head n) : HeadView roles (.pair a b) (.former .pair)
  | refl (a : Tm Head n) : HeadView roles (.refl a) .refl
  | spine {c : DeclName} (args : List (Tm Head n)) :
      (∀ arity inspect, roles c ≠ .computes arity inspect) →
        HeadView roles (appSpine (.const c) args) (.const c)

/-- A head form: a head, a type or value former, reflexivity, or a spine of a
constant that does not compute, rigid spines included. -/
def HeadForm (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  ∃ key, HeadView roles t key


/-- The key a head-form inspection reads from a term, by the term's head. -/
private def headKey {n : Nat} (t : Tm Head n) : InspectKey :=
  match (headArgs t).1 with
  | .head _ => .former .head
  | .pi _ _ => .former .pi
  | .sigma _ _ => .former .sigma
  | .id _ _ _ => .former .id
  | .lam _ => .former .lam
  | .pair _ _ => .former .pair
  | .const c => .const c
  | _ => .refl

private theorem HeadView.key_eq {roles : Roles Head} {n : Nat} {t : Tm Head n}
    {key : InspectKey} (view : HeadView roles t key) : key = headKey t := by
  cases view with
  | spine args _ =>
      unfold headKey
      rw [headArgs_appSpine (show NotApp (.const _ : Tm Head n) by trivial)]
  | head _ => rfl
  | pi _ _ => rfl
  | sigma _ _ => rfl
  | id _ _ _ => rfl
  | lam _ => rfl
  | pair _ _ => rfl
  | refl _ => rfl

/-- A head form determines its key. -/
theorem HeadView.unique {roles : Roles Head} {n : Nat} {t : Tm Head n} {key key' : InspectKey}
    (view : HeadView roles t key) (view' : HeadView roles t key') : key = key' :=
  view.key_eq.trans view'.key_eq.symm

/-- Constructor forms are head forms, with the same key. -/
theorem ConstructorView.headView {roles : Roles Head} {n : Nat} {t : Tm Head n}
    {key : InspectKey} {fields : List (Tm Head n)} (view : ConstructorView roles t key fields) :
    HeadView roles t key := by
  cases view with
  | spine _ role => exact .spine _ fun _ _ computes => nomatch role.symm.trans computes
  | refl a => exact .refl a

theorem Canonical.headForm {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (canonical : Canonical roles t) : HeadForm roles t := by
  obtain ⟨key, _, view⟩ := canonical.view
  exact ⟨key, view.headView⟩

theorem HeadView.rename {roles : Roles Head} {n : Nat} {t : Tm Head n} {key : InspectKey}
    (view : HeadView roles t key) {m : Nat} (ρ : Ren n m) :
    HeadView roles (Presentation.rename ρ t) key := by
  cases view with
  | spine args notComputing =>
      rw [rename_appSpine]
      exact .spine _ notComputing
  | head h => exact .head h
  | pi A B => exact .pi _ _
  | sigma A B => exact .sigma _ _
  | id A a b => exact .id _ _ _
  | lam body => exact .lam _
  | pair a b => exact .pair _ _
  | refl a => exact .refl _

theorem HeadView.subst {roles : Roles Head} {n : Nat} {t : Tm Head n} {key : InspectKey}
    (view : HeadView roles t key) {m : Nat} (σ : Sub Head n m) :
    HeadView roles (Presentation.subst σ t) key := by
  cases view with
  | spine args notComputing =>
      rw [subst_appSpine]
      exact .spine _ notComputing
  | head h => exact .head h
  | pi A B => exact .pi _ _
  | sigma A B => exact .sigma _ _
  | id A a b => exact .id _ _ _
  | lam body => exact .lam _
  | pair a b => exact .pair _ _
  | refl a => exact .refl _

/-- Renaming creates no head form. -/
theorem HeadView.of_rename {roles : Roles Head} {n m : Nat} {ρ : Ren n m} {t : Tm Head n}
    {key : InspectKey} (view : HeadView roles (Presentation.rename ρ t) key) :
    HeadView roles t key := by
  generalize e : Presentation.rename ρ t = t' at view
  cases view with
  | spine args notComputing =>
      obtain ⟨args', rfl⟩ := rename_eq_constSpine e
      exact .spine _ notComputing
  | head h => cases t <;> cases e; exact .head _
  | pi A B => cases t <;> cases e; exact .pi _ _
  | sigma A B => cases t <;> cases e; exact .sigma _ _
  | id A a b => cases t <;> cases e; exact .id _ _ _
  | lam body => cases t <;> cases e; exact .lam _
  | pair a b => cases t <;> cases e; exact .pair _ _
  | refl a => cases t <;> cases e; exact .refl _

/-- The values an inspection accepts: constructor forms at a constructor
inspection, head forms at a head-form inspection. -/
def Inspection.Accepts (roles : Roles Head) {n : Nat} : Inspection → Tm Head n → Prop
  | .constructor, t => Canonical roles t
  | .headForm, t => HeadForm roles t

/-! ## Inspecting the arguments of a computing constant -/

/-- Every value a skeleton inspects has the shape its split requires, down to a
leaf. A constructor form is replaced by its fields; a head form stays in
place. -/
inductive InspectTree.Accepts (roles : Roles Head) {n : Nat} :
    InspectTree → List (Tm Head n) → Prop where
  | leaf (values : List (Tm Head n)) : InspectTree.Accepts roles .leaf values
  | constructor {position : Nat} {next : InspectKey → InspectTree}
      {before after fields : List (Tm Head n)} {value : Tm Head n} {key : InspectKey} :
      before.length = position → ConstructorView roles value key fields →
      InspectTree.Accepts roles (next key) (before ++ fields ++ after) →
        InspectTree.Accepts roles (.split position .constructor next) (before ++ value :: after)
  | headForm {position : Nat} {next : InspectKey → InspectTree}
      {before after : List (Tm Head n)} {value : Tm Head n} {key : InspectKey} :
      before.length = position → HeadView roles value key →
      InspectTree.Accepts roles (next key) (before ++ value :: after) →
        InspectTree.Accepts roles (.split position .headForm next) (before ++ value :: after)

/-- The next inspection of a skeleton, after the values it accepts: a split of
kind `kind` at the value `a`. Putting `a'` in its place turns `values` into
`values'`; a constructor form accepted on the way is rebuilt around its changed
field. -/
inductive InspectTree.Focus (roles : Roles Head) {n : Nat} :
    InspectTree → List (Tm Head n) → List (Tm Head n) → Inspection → Tm Head n →
      Tm Head n → Prop where
  | here {position : Nat} {kind : Inspection} {next : InspectKey → InspectTree}
      {before after : List (Tm Head n)} {a a' : Tm Head n} :
      before.length = position →
        InspectTree.Focus roles (.split position kind next) (before ++ a :: after)
          (before ++ a' :: after) kind a a'
  | constructor {position : Nat} {next : InspectKey → InspectTree}
      {before after fields before' after' fields' : List (Tm Head n)}
      {value value' : Tm Head n} {key : InspectKey} {kind : Inspection} {a a' : Tm Head n} :
      before.length = position → before'.length = position →
      fields'.length = fields.length →
      ConstructorView roles value key fields → ConstructorView roles value' key fields' →
      InspectTree.Focus roles (next key) (before ++ fields ++ after)
        (before' ++ fields' ++ after') kind a a' →
        InspectTree.Focus roles (.split position .constructor next) (before ++ value :: after)
          (before' ++ value' :: after') kind a a'
  | headForm {position : Nat} {next : InspectKey → InspectTree}
      {before after values' : List (Tm Head n)} {value : Tm Head n} {key : InspectKey}
      {kind : Inspection} {a a' : Tm Head n} :
      before.length = position → HeadView roles value key →
      InspectTree.Focus roles (next key) (before ++ value :: after) values' kind a a' →
        InspectTree.Focus roles (.split position .headForm next) (before ++ value :: after)
          values' kind a a'

/-- Two splittings of one list around positions of equal index agree. -/
theorem appendCons_inj {α : Type _} {before before' after after' : List α} {a a' : α}
    (equal : before ++ a :: after = before' ++ a' :: after')
    (length : before.length = before'.length) : before = before' ∧ a = a' ∧ after = after' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj equal length
  obtain ⟨h₃, h₄⟩ := List.cons.inj h₂
  exact ⟨h₁, h₃, h₄⟩

/-- A leaf inspects nothing. -/
theorem InspectTree.Focus.not_leaf {roles : Roles Head} {n : Nat}
    {values values' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n} :
    ¬ InspectTree.leaf.Focus roles values values' kind a a' := nofun

/-- The value a skeleton inspects next is accepted when the skeleton accepts
the values. -/
theorem InspectTree.Focus.accepted {roles : Roles Head} {n : Nat} {tree : InspectTree}
    {values values' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n}
    (focus : tree.Focus roles values values' kind a a') :
    tree.Accepts roles values → kind.Accepts roles a := by
  induction focus with
  | @here position kind next before after a a' lengthBefore =>
      intro accepts
      generalize hvals : before ++ a :: after = vals at accepts
      cases accepts with
      | constructor lengthBefore₂ view₂ _ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          exact view₂.canonical
      | headForm lengthBefore₂ view₂ _ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          exact ⟨_, view₂⟩
  | @constructor position next before after fields before' after' fields' value value' key kind
      a a' lengthBefore _ _ view _ _ ih =>
      intro accepts
      generalize hvals : before ++ value :: after = vals at accepts
      cases accepts with
      | constructor lengthBefore₂ view₂ inner₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          obtain ⟨rfl, rfl⟩ := view.unique view₂
          exact ih inner₂
  | @headForm position next before after values' value key kind a a' lengthBefore view _ ih =>
      intro accepts
      generalize hvals : before ++ value :: after = vals at accepts
      cases accepts with
      | headForm lengthBefore₂ view₂ inner₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          obtain rfl := view.unique view₂
          exact ih inner₂

/-- A skeleton inspects at most one value next that it does not accept, and
putting the same value in its place gives the same values. -/
theorem InspectTree.Focus.unique {roles : Roles Head} {n : Nat} {tree : InspectTree}
    {values values₁ values₂ : List (Tm Head n)} {kind₁ kind₂ : Inspection}
    {a a₁ b b₁ : Tm Head n}
    (first : tree.Focus roles values values₁ kind₁ a a₁)
    (second : tree.Focus roles values values₂ kind₂ b b₁)
    (notA : ¬ kind₁.Accepts roles a) (notB : ¬ kind₂.Accepts roles b) :
    a = b ∧ kind₁ = kind₂ ∧ (a₁ = b₁ → values₁ = values₂) := by
  induction first generalizing values₂ kind₂ b b₁ with
  | @here position kind next before after a a₁ lengthBefore =>
      generalize hvals : before ++ a :: after = vals at second
      cases second with
      | here lengthBefore₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          exact ⟨rfl, rfl, fun same => by rw [same]⟩
      | constructor lengthBefore₂ _ _ view₂ _ _ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          exact absurd view₂.canonical notA
      | headForm lengthBefore₂ view₂ _ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          exact absurd ⟨_, view₂⟩ notA
  | @constructor position next before after fields before' after' fields' value value' key kind
      a a₁ lengthBefore lengthBefore' lengthFields view view' _ ih =>
      generalize hvals : before ++ value :: after = vals at second
      cases second with
      | here lengthBefore₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          exact absurd view.canonical notB
      | constructor lengthBefore₂ lengthBefore₂' lengthFields₂ view₂ view₂' inner₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          obtain ⟨rfl, rfl⟩ := view.unique view₂
          obtain ⟨rfl, rfl, outputs⟩ := ih inner₂ notA notB
          refine ⟨rfl, rfl, fun same => ?_⟩
          obtain ⟨hfront, hafter⟩ := List.append_inj (outputs same)
            (by simp only [List.length_append]; omega)
          obtain ⟨hbefore, hfields⟩ := List.append_inj hfront (lengthBefore'.trans lengthBefore₂'.symm)
          subst hbefore hfields hafter
          rw [view'.inj view₂']
  | @headForm position next before after values' value key kind a a₁ lengthBefore view _ ih =>
      generalize hvals : before ++ value :: after = vals at second
      cases second with
      | here lengthBefore₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          exact absurd ⟨_, view⟩ notB
      | headForm lengthBefore₂ view₂ inner₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := appendCons_inj hvals (lengthBefore.trans lengthBefore₂.symm)
          obtain rfl := view.unique view₂
          exact ih inner₂ notA notB

theorem InspectTree.Focus.rename {roles : Roles Head} {n : Nat} {tree : InspectTree}
    {values values' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n}
    (focus : tree.Focus roles values values' kind a a') {m : Nat} (ρ : Ren n m) :
    tree.Focus roles (values.map (Presentation.rename ρ)) (values'.map (Presentation.rename ρ))
      kind (Presentation.rename ρ a) (Presentation.rename ρ a') := by
  induction focus with
  | here lengthBefore =>
      simp only [List.map_append, List.map_cons]
      exact .here (by rw [List.length_map]; exact lengthBefore)
  | constructor lengthBefore lengthBefore' lengthFields view view' _ ih =>
      simp only [List.map_append, List.map_cons] at ih ⊢
      exact .constructor (by rw [List.length_map]; exact lengthBefore)
        (by rw [List.length_map]; exact lengthBefore')
        (by rw [List.length_map, List.length_map]; exact lengthFields)
        (view.rename ρ) (view'.rename ρ) ih
  | headForm lengthBefore view _ ih =>
      simp only [List.map_append, List.map_cons] at ih ⊢
      exact .headForm (by rw [List.length_map]; exact lengthBefore) (view.rename ρ) ih

theorem InspectTree.Focus.subst {roles : Roles Head} {n : Nat} {tree : InspectTree}
    {values values' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n}
    (focus : tree.Focus roles values values' kind a a') {m : Nat} (σ : Sub Head n m) :
    tree.Focus roles (values.map (Presentation.subst σ)) (values'.map (Presentation.subst σ))
      kind (Presentation.subst σ a) (Presentation.subst σ a') := by
  induction focus with
  | here lengthBefore =>
      simp only [List.map_append, List.map_cons]
      exact .here (by rw [List.length_map]; exact lengthBefore)
  | constructor lengthBefore lengthBefore' lengthFields view view' _ ih =>
      simp only [List.map_append, List.map_cons] at ih ⊢
      exact .constructor (by rw [List.length_map]; exact lengthBefore)
        (by rw [List.length_map]; exact lengthBefore')
        (by rw [List.length_map, List.length_map]; exact lengthFields)
        (view.subst σ) (view'.subst σ) ih
  | headForm lengthBefore view _ ih =>
      simp only [List.map_append, List.map_cons] at ih ⊢
      exact .headForm (by rw [List.length_map]; exact lengthBefore) (view.subst σ) ih

/-- A position of a three-part list lies in one of the parts. -/
theorem append_three_cases {α : Type _} {before mid after B A : List α} {x : α}
    (equal : before ++ mid ++ after = B ++ x :: A) :
    (∃ C, before = B ++ x :: C ∧ A = C ++ mid ++ after) ∨
      (∃ F₁ F₂, mid = F₁ ++ x :: F₂ ∧ B = before ++ F₁ ∧ A = F₂ ++ after) ∨
      (∃ D, after = D ++ x :: A ∧ B = before ++ mid ++ D) := by
  rw [List.append_assoc] at equal
  rcases List.append_eq_append_iff.mp equal with ⟨a', hB, hrest⟩ | ⟨c', hbefore, hx⟩
  · rcases List.append_eq_append_iff.mp hrest with ⟨a'', ha', hafter⟩ | ⟨c'', hmid, hx⟩
    · exact .inr (.inr ⟨a'', hafter, by rw [hB, ha', List.append_assoc]⟩)
    · rcases List.cons_eq_append_iff.mp hx with ⟨rfl, hafter⟩ | ⟨c₃, rfl, hA⟩
      · refine .inr (.inr ⟨[], by rw [List.nil_append]; exact hafter, ?_⟩)
        rw [hB, hmid, List.append_nil, List.append_nil]
      · exact .inr (.inl ⟨a', c₃, hmid, hB, hA⟩)
  · rcases List.cons_eq_append_iff.mp hx with ⟨rfl, hrest⟩ | ⟨c₃, rfl, hA⟩
    · rw [List.append_nil] at hbefore
      subst hbefore
      rcases List.append_eq_cons_iff.mp hrest with ⟨rfl, hafter⟩ | ⟨m', rfl, hA⟩
      · refine .inr (.inr ⟨[], by rw [List.nil_append]; exact hafter, ?_⟩)
        rw [List.append_nil, List.append_nil]
      · exact .inr (.inl ⟨[], m', rfl, (List.append_nil _).symm, hA⟩)
    · exact .inl ⟨c₃, hbefore, by rw [hA, List.append_assoc]⟩

/-- A constructor form with one field changed, as a relation compatible with
the arguments of constructor spines and with reflexivity. -/
private theorem ConstructorView.change {roles : Roles Head} {n : Nat}
    {r : Tm Head n → Tm Head n → Prop}
    (spine : ∀ (c : DeclName) (before after : List (Tm Head n)) {x y : Tm Head n}, r x y →
      r (appSpine (.const c) (before ++ x :: after)) (appSpine (.const c) (before ++ y :: after)))
    (refl : ∀ {x y : Tm Head n}, r x y → r (.refl x) (.refl y))
    {value value' : Tm Head n} {key : InspectKey} {fields fields' F₁ F₂ : List (Tm Head n)}
    {x y : Tm Head n} (view : ConstructorView roles value key fields)
    (view' : ConstructorView roles value' key fields') (hfields : fields = F₁ ++ x :: F₂)
    (hfields' : fields' = F₁ ++ y :: F₂) (change : r x y) : r value value' := by
  cases view with
  | spine _ _ =>
      cases view' with
      | spine _ _ =>
          subst hfields hfields'
          exact spine _ F₁ F₂ change
  | refl p =>
      cases view' with
      | refl q =>
          rcases F₁ with _ | ⟨f, F₁⟩
          · obtain ⟨rfl, -⟩ := List.cons.inj hfields
            obtain ⟨rfl, -⟩ := List.cons.inj hfields'
            exact refl change
          · exact absurd (List.cons.inj hfields).2.symm
              (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))

/-- A focus changes one value of the list, reached through the constructor
forms accepted on the way: every relation that holds of the change and is
compatible with the arguments of constructor spines and with reflexivity holds
at one position of the old and new values. -/
theorem InspectTree.Focus.lift {roles : Roles Head} {n : Nat} {r : Tm Head n → Tm Head n → Prop}
    (spine : ∀ (c : DeclName) (before after : List (Tm Head n)) {x y : Tm Head n}, r x y →
      r (appSpine (.const c) (before ++ x :: after)) (appSpine (.const c) (before ++ y :: after)))
    (refl : ∀ {x y : Tm Head n}, r x y → r (.refl x) (.refl y))
    {tree : InspectTree} {values values' : List (Tm Head n)} {kind : Inspection}
    {a a' : Tm Head n} (focus : tree.Focus roles values values' kind a a') (change : r a a') :
    ∃ before after x y, values = before ++ x :: after ∧ values' = before ++ y :: after ∧
      r x y := by
  induction focus with
  | here _ => exact ⟨_, _, _, _, rfl, rfl, change⟩
  | headForm _ _ _ ih => exact ih change
  | @constructor position next before after fields before' after' fields' value value' key kind
      a a' lengthBefore lengthBefore' lengthFields view view' _ ih =>
      obtain ⟨B, A, x, y, e, e', rxy⟩ := ih change
      rcases append_three_cases e with ⟨C, rfl, rfl⟩ | ⟨F₁, F₂, hfields, rfl, rfl⟩ |
        ⟨D, rfl, rfl⟩
      · -- the change is in a value before the constructor form
        have e₁ : before' ++ fields' ++ after' = (B ++ y :: C) ++ fields ++ after := by
          rw [e']
          simp only [List.append_assoc, List.cons_append]
        obtain ⟨hfront, hafter⟩ := List.append_inj e₁ (by
          simp only [List.length_append, List.length_cons] at lengthBefore ⊢
          omega)
        obtain ⟨hbefore, hfields⟩ := List.append_inj hfront (by
          simp only [List.length_append, List.length_cons] at lengthBefore ⊢
          omega)
        subst after' fields' before'
        obtain rfl := view.inj view'
        refine ⟨B, C ++ value :: after, x, y, ?_, ?_, rxy⟩ <;>
          simp only [List.append_assoc, List.cons_append]
      · -- the change is in a field of the constructor form
        have e₁ : before' ++ fields' ++ after' = before ++ (F₁ ++ y :: F₂) ++ after := by
          rw [e']
          simp only [List.append_assoc, List.cons_append]
        obtain ⟨hfront, hafter⟩ := List.append_inj e₁ (by
          rw [hfields] at lengthFields
          simp only [List.length_append, List.length_cons] at lengthFields ⊢
          omega)
        obtain ⟨hbefore, hfields'⟩ := List.append_inj hfront (lengthBefore'.trans lengthBefore.symm)
        subst after' before'
        exact ⟨before, after, value, value', rfl, rfl,
          ConstructorView.change spine refl view view' hfields hfields' rxy⟩
      · -- the change is in a value after the constructor form
        have e₁ : before' ++ fields' ++ after' = before ++ fields ++ (D ++ y :: A) := by
          rw [e']
          simp only [List.append_assoc]
        obtain ⟨hfront, hafter⟩ := List.append_inj e₁ (by
          simp only [List.length_append]
          omega)
        obtain ⟨hbefore, hfields⟩ := List.append_inj hfront (lengthBefore'.trans lengthBefore.symm)
        subst after' fields' before'
        obtain rfl := view.inj view'
        refine ⟨before ++ value :: D, A, x, y, ?_, ?_, rxy⟩ <;>
          simp only [List.append_assoc, List.cons_append]

/-- A skeleton all of whose splits inspect constructor forms: the skeleton of
a case tree, a recursor or the identity eliminator. -/
inductive InspectTree.OnlyConstructors : InspectTree → Prop where
  | leaf : InspectTree.OnlyConstructors .leaf
  | split {position : Nat} {next : InspectKey → InspectTree} :
      (∀ key, InspectTree.OnlyConstructors (next key)) →
        InspectTree.OnlyConstructors (.split position .constructor next)

/-- A constructor form stays one under roles that keep the constructors. -/
theorem ConstructorView.of_constructors {roles roles' : Roles Head}
    (keep : ∀ {c : DeclName} {arity : Nat}, roles c = .constructor arity →
      roles' c = .constructor arity)
    {n : Nat} {t : Tm Head n} {key : InspectKey} {fields : List (Tm Head n)}
    (view : ConstructorView roles t key fields) : ConstructorView roles' t key fields := by
  cases view with
  | spine _ role => exact .spine _ (keep role)
  | refl a => exact .refl a

/-- Acceptance by a skeleton that inspects only constructor forms depends only
on the constructors' roles. -/
theorem InspectTree.Accepts.of_constructors {roles roles' : Roles Head}
    (keep : ∀ {c : DeclName} {arity : Nat}, roles c = .constructor arity →
      roles' c = .constructor arity)
    {n : Nat} {tree : InspectTree} {values : List (Tm Head n)}
    (accepts : tree.Accepts roles values) : tree.OnlyConstructors → tree.Accepts roles' values := by
  induction accepts with
  | leaf values => exact fun _ => .leaf values
  | constructor lengthBefore view _ ih =>
      intro only
      cases only with
      | split rest => exact .constructor lengthBefore (view.of_constructors keep) (ih (rest _))
  | headForm _ _ _ _ => exact fun only => nomatch only

/-- A skeleton that inspects only constructor forms inspects next at a
constructor inspection. -/
theorem InspectTree.Focus.kind_of_onlyConstructors {roles : Roles Head} {n : Nat}
    {tree : InspectTree} {values values' : List (Tm Head n)} {kind : Inspection}
    {a a' : Tm Head n} (focus : tree.Focus roles values values' kind a a') :
    tree.OnlyConstructors → kind = .constructor := by
  induction focus with
  | here _ => exact fun only => by cases only; rfl
  | constructor _ _ _ _ _ _ ih =>
      intro only
      cases only with
      | split rest => exact ih (rest _)
  | headForm _ _ _ _ => exact fun only => nomatch only

/-- A skeleton with one constructor inspection accepts exactly the arguments
with a canonical value at that position. -/
theorem InspectTree.accepts_single {roles : Roles Head} {n k : Nat}
    {args : List (Tm Head n)} :
    (InspectTree.split k .constructor fun _ => .leaf).Accepts roles args ↔
      ∃ a, args[k]? = some a ∧ Canonical roles a := by
  constructor
  · intro accepts
    cases accepts with
    | @constructor _ _ before after _ value _ lengthBefore view _ =>
        subst lengthBefore
        refine ⟨value, ?_, view.canonical⟩
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
  · rintro ⟨a, found, canonical⟩
    obtain ⟨key, fields, view⟩ := canonical.view
    obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp found
    have split : args.take k ++ a :: args.drop (k + 1) = args := by
      rw [← hget, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    rw [← split]
    exact .constructor (by rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hk)) view
      (.leaf _)

/-- A skeleton with one constructor inspection inspects the value at its
position, directly. -/
theorem InspectTree.Focus.single {roles : Roles Head} {n k : Nat}
    {values values' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n}
    (focus : (InspectTree.split k .constructor fun _ => .leaf).Focus roles values values' kind a a') :
    ∃ before after, before.length = k ∧ values = before ++ a :: after ∧
      values' = before ++ a' :: after ∧ kind = .constructor := by
  cases focus with
  | here lengthBefore => exact ⟨_, _, lengthBefore, rfl, rfl, rfl⟩
  | constructor _ _ _ _ _ inner => exact absurd inner InspectTree.Focus.not_leaf

/-! ## The obligations on root steps -/

/-- The rule package's root steps occur only at computing spines of exact
arity whose inspected values have the shapes their splits require, and are
deterministic. -/
structure RootShape (R : Rules Head) (roles : Roles Head) : Prop where
  spine : ∀ {n : Nat} {t u : Tm Head n}, R.computation.step t u →
    ∃ c arity inspect args, roles c = .computes arity inspect ∧
      t = appSpine (.const c) args ∧ args.length = arity ∧ inspect.Accepts roles args
  deterministic : ∀ {n : Nat} {t u u' : Tm Head n},
    R.computation.step t u → R.computation.step t u' → u = u'

/-! ## Weak-head steps -/

/-- One weak-head step. -/
inductive WhStep (R : Rules Head) (roles : Roles Head) :
    {n : Nat} → Tm Head n → Tm Head n → Prop where
  | beta {n : Nat} (body : Tm Head (n + 1)) (a : Tm Head n) :
      WhStep R roles (.app (.lam body) a) (inst0 a body)
  | fstPair {n : Nat} (a b : Tm Head n) : WhStep R roles (.fst (.pair a b)) a
  | sndPair {n : Nat} (a b : Tm Head n) : WhStep R roles (.snd (.pair a b)) b
  | root {n : Nat} {t u : Tm Head n} :
      R.computation.step t u → WhStep R roles t u
  | appFun {n : Nat} {f f' a : Tm Head n} :
      WhStep R roles f f' → WhStep R roles (.app f a) (.app f' a)
  | fst {n : Nat} {p p' : Tm Head n} :
      WhStep R roles p p' → WhStep R roles (.fst p) (.fst p')
  | snd {n : Nat} {p p' : Tm Head n} :
      WhStep R roles p p' → WhStep R roles (.snd p) (.snd p')
  /-- A step at the value the skeleton of a computing constant of exact arity
  inspects next. -/
  | scrutinee {n : Nat} {c : DeclName} {arity : Nat} {inspect : InspectTree}
      {args args' : List (Tm Head n)} {kind : Inspection} {a a' : Tm Head n} :
      roles c = .computes arity inspect →
      args.length = arity →
      inspect.Focus roles args args' kind a a' →
      WhStep R roles a a' →
      WhStep R roles (appSpine (.const c) args) (appSpine (.const c) args')

/-- Weak-head reduction: finitely many weak-head steps. -/
abbrev WhRed (R : Rules Head) (roles : Roles Head) {n : Nat} (t u : Tm Head n) : Prop :=
  Relation.ReflTransGen (WhStep R roles) t u

/-- A weak-head normal form: no weak-head step applies. -/
def Whnf (R : Rules Head) (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  ∀ u, ¬ WhStep R roles t u

/-- A step at the scrutinee of a constant that inspects one argument. -/
theorem WhStep.scrutinee_single {R : Rules Head} {roles : Roles Head} {n : Nat}
    {c : DeclName} {arity : Nat} {before after : List (Tm Head n)} {a a' : Tm Head n}
    (role : roles c = .computes arity (.split before.length .constructor fun _ => .leaf))
    (length : before.length + 1 + after.length = arity) (step : WhStep R roles a a') :
    WhStep R roles (appSpine (.const c) (before ++ a :: after))
      (appSpine (.const c) (before ++ a' :: after)) :=
  .scrutinee role ((length_append_cons a after before).trans length) (.here rfl) step

/-! ## Which terms can step -/

theorem appSpine_ne_nil_eq_app {n : Nat} {f : Tm Head n} {as : List (Tm Head n)}
    (nonempty : as ≠ []) : ∃ g a, appSpine f as = .app g a := by
  obtain ⟨init, last, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left nonempty
  exact ⟨appSpine f init, last, by rw [List.concat_eq_append]; exact appSpine_concat f init last⟩

/-- Only applications, projections and constants take weak-head steps. -/
theorem whStep_shape {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {t u : Tm Head n} (step : WhStep R roles t u) :
    (∃ f a, t = .app f a) ∨ (∃ p, t = .fst p) ∨ (∃ p, t = .snd p) ∨
      ∃ c, t = .const c := by
  cases step with
  | beta body a => exact .inl ⟨_, _, rfl⟩
  | fstPair a b => exact .inr (.inl ⟨_, rfl⟩)
  | sndPair a b => exact .inr (.inr (.inl ⟨_, rfl⟩))
  | root step =>
      obtain ⟨c, _, _, args, _, rfl, _⟩ := shape.spine step
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · exact .inr (.inr (.inr ⟨c, rfl⟩))
      · exact .inl ⟨_, _, by rw [List.concat_eq_append]; exact appSpine_concat _ init last⟩
  | appFun _ => exact .inl ⟨_, _, rfl⟩
  | fst _ => exact .inr (.inl ⟨_, rfl⟩)
  | snd _ => exact .inr (.inr (.inl ⟨_, rfl⟩))
  | @scrutinee c _ _ args _ _ _ _ _ _ _ _ =>
      rcases appSpine_const_cases c args with h | h
      · exact .inr (.inr (.inr ⟨c, h⟩))
      · exact .inl h

theorem lam_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (body : Tm Head (n + 1)) : Whnf R roles (.lam body) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

theorem pair_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (a b : Tm Head n) : Whnf R roles (.pair a b) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

theorem refl_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (a : Tm Head n) : Whnf R roles (.refl a) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

theorem var_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (i : Fin n) : Whnf R roles (.var i) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h

theorem head_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (h : Head) : Whnf R roles (.head h : Tm Head n) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> cases e

theorem pi_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) : Whnf R roles (.pi A B) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> cases e

theorem sigma_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) : Whnf R roles (.sigma A B) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> cases e

theorem id_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} (A a b : Tm Head n) : Whnf R roles (.id A a b) := by
  intro u step
  rcases whStep_shape shape step with ⟨_, _, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> cases e

/-! ## Steps of a constant spine -/

/-- A step of a constant spine happens in its prefix of exactly the constant's
arity, which must be a computing constant. -/
theorem constSpine_step_of_eq {R : Rules Head} {roles : Roles Head}
    (shape : RootShape R roles) {n : Nat} {t u : Tm Head n}
    (step : WhStep R roles t u) :
    ∀ {c : DeclName} {args : List (Tm Head n)}, t = appSpine (.const c) args →
      ∃ arity scrutinee pre post v, roles c = .computes arity scrutinee ∧
        args = pre ++ post ∧ pre.length = arity ∧
        WhStep R roles (appSpine (.const c) pre) v ∧ u = appSpine v post := by
  induction step with
  | beta body a =>
      intro c args equal
      exact absurd equal.symm appSpine_const_ne_lam
  | fstPair a b =>
      intro c args equal
      exact absurd equal.symm appSpine_const_ne_fst
  | sndPair a b =>
      intro c args equal
      exact absurd equal.symm appSpine_const_ne_snd
  | root step =>
      intro c args equal
      obtain ⟨c', arity, inspect, args', role, equal', length, _⟩ := shape.spine step
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective (equal.symm.trans equal')
      exact ⟨arity, inspect, args, [], _, role, by simp, length,
        by rw [← equal]; exact .root step, rfl⟩
  | @appFun f f' a inner ih =>
      intro c args equal
      obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app equal.symm
      obtain ⟨arity, inspect, pre, post, v, role, split, length, prefixStep, rfl⟩ :=
        ih rfl
      exact ⟨arity, inspect, pre, post ++ [a], v, role, by simp [split], length,
        prefixStep, by rw [appSpine_concat]⟩
  | fst _ _ =>
      intro c args equal
      exact absurd equal.symm appSpine_const_ne_fst
  | snd _ _ =>
      intro c args equal
      exact absurd equal.symm appSpine_const_ne_snd
  | @scrutinee c' arity inspect args args' kind a a' role length focus inner _ =>
      intro c args₀ equal
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective equal
      exact ⟨arity, inspect, args, [], _, role, (List.append_nil _).symm, length,
        .scrutinee role length focus inner, rfl⟩

theorem constSpine_step {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {c : DeclName} {args : List (Tm Head n)} {u : Tm Head n}
    (step : WhStep R roles (appSpine (.const c) args) u) :
    ∃ arity scrutinee pre post v, roles c = .computes arity scrutinee ∧
      args = pre ++ post ∧ pre.length = arity ∧
      WhStep R roles (appSpine (.const c) pre) v ∧ u = appSpine v post :=
  constSpine_step_of_eq shape step rfl

/-- A constant spine whose constant does not compute is a weak-head normal
form. -/
theorem constSpine_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {c : DeclName} (notComputing : ∀ arity scrutinee,
      roles c ≠ .computes arity scrutinee) (args : List (Tm Head n)) :
    Whnf R roles (appSpine (.const c) args) := by
  intro u step
  obtain ⟨arity, inspect, _, _, _, role, _⟩ := constSpine_step shape step
  exact notComputing arity inspect role

/-- A computing constant applied to fewer arguments than its arity is a
weak-head normal form. -/
theorem partialSpine_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {c : DeclName} {arity : Nat} {scrutinee : InspectTree}
    (role : roles c = .computes arity scrutinee) {args : List (Tm Head n)}
    (short : args.length < arity) : Whnf R roles (appSpine (.const c) args) := by
  intro u step
  obtain ⟨arity', inspect', pre, post, _, role', split, length, _⟩ :=
    constSpine_step shape step
  rw [role] at role'
  injection role' with same _
  subst same split
  simp at short
  omega

theorem canonical_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {t : Tm Head n} (canonical : Canonical roles t) : Whnf R roles t := by
  rcases canonical with ⟨x, rfl⟩ | ⟨k, arity, args, role, rfl⟩
  · exact refl_whnf shape x
  · exact constSpine_whnf shape (by intro a s h; rw [role] at h; cases h) args

/-- A head form is a weak-head normal form. -/
theorem headForm_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {t : Tm Head n} {key : InspectKey} (view : HeadView roles t key) :
    Whnf R roles t := by
  cases view with
  | head h => exact head_whnf shape h
  | pi A B => exact pi_whnf shape A B
  | sigma A B => exact sigma_whnf shape A B
  | id A a b => exact id_whnf shape A a b
  | lam body => exact lam_whnf shape body
  | pair a b => exact pair_whnf shape a b
  | refl a => exact refl_whnf shape a
  | spine args notComputing => exact constSpine_whnf shape notComputing args

/-- What an inspection accepts is a weak-head normal form: a value that still
reduces is never taken as inspected. -/
theorem Inspection.Accepts.whnf {R : Rules Head} {roles : Roles Head}
    (shape : RootShape R roles) {n : Nat} {kind : Inspection} {t : Tm Head n}
    (accepts : kind.Accepts roles t) : Whnf R roles t := by
  cases kind with
  | constructor => exact canonical_whnf shape accepts
  | headForm =>
      obtain ⟨key, view⟩ := accepts
      exact headForm_whnf shape view

/-- A step of a computing spine of exact arity is a root step, whose inspected
values are then accepted, or a step at the value its skeleton inspects next. -/
theorem exactSpine_step {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : roles c = .computes arity inspect) {args : List (Tm Head n)}
    (exact : args.length = arity) {u : Tm Head n}
    (step : WhStep R roles (appSpine (.const c) args) u) :
    inspect.Accepts roles args ∨
      ∃ args' kind a a', inspect.Focus roles args args' kind a a' ∧ WhStep R roles a a' ∧
        u = appSpine (.const c) args' := by
  generalize hterm : appSpine (.const c) args = term at step
  cases step with
  | beta body a => exact absurd hterm appSpine_const_ne_lam
  | fstPair a b => exact absurd hterm appSpine_const_ne_fst
  | sndPair a b => exact absurd hterm appSpine_const_ne_snd
  | root step =>
      obtain ⟨c', arity', inspect', args', role', equal, _, accepts⟩ := shape.spine step
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective (hterm.trans equal)
      rw [role] at role'
      injection role' with _ same
      subst same
      exact .inl accepts
  | appFun inner =>
      obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app hterm
      exfalso
      simp at exact
      exact partialSpine_whnf shape role (by omega) _ inner
  | fst _ => exact absurd hterm appSpine_const_ne_fst
  | snd _ => exact absurd hterm appSpine_const_ne_snd
  | @scrutinee c' arity' inspect' args₁ args₂ kind a a' role' length focus inner =>
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective hterm
      rw [role] at role'
      injection role' with _ same
      subst same
      exact .inr ⟨args₂, kind, a, a', focus, inner, rfl⟩

/-! ## Neutral terms -/

/-- Terms that are stuck forever: headed by a variable or a rigid constant, or
a computing constant of exact arity whose skeleton inspects a neutral value it
does not accept, and then eliminated. At a constructor inspection every neutral
value blocks; at a head-form inspection a rigid spine is accepted, so the
blocking value must not be a head form. -/
inductive Neutral (roles : Roles Head) : {n : Nat} → Tm Head n → Prop where
  | var {n : Nat} (i : Fin n) : Neutral roles (.var i)
  | app {n : Nat} {f a : Tm Head n} : Neutral roles f → Neutral roles (.app f a)
  | fst {n : Nat} {p : Tm Head n} : Neutral roles p → Neutral roles (.fst p)
  | snd {n : Nat} {p : Tm Head n} : Neutral roles p → Neutral roles (.snd p)
  | rigid {n : Nat} {c : DeclName} (args : List (Tm Head n)) :
      roles c = .rigid → Neutral roles (appSpine (.const c) args)
  | stuck {n : Nat} {c : DeclName} {arity : Nat} {inspect : InspectTree}
      {args : List (Tm Head n)} {kind : Inspection} {a : Tm Head n} :
      roles c = .computes arity inspect →
      args.length = arity →
      inspect.Focus roles args args kind a a →
      Neutral roles a →
      (kind = .headForm → ¬ HeadForm roles a) →
      Neutral roles (appSpine (.const c) args)

/-- A spine stuck on a neutral scrutinee of a constant that inspects one
argument. -/
theorem Neutral.stuck_single {roles : Roles Head} {n : Nat} {c : DeclName} {arity : Nat}
    {before after : List (Tm Head n)} {a : Tm Head n}
    (role : roles c = .computes arity (.split before.length .constructor fun _ => .leaf))
    (length : before.length + 1 + after.length = arity) (neutral : Neutral roles a) :
    Neutral roles (appSpine (.const c) (before ++ a :: after)) :=
  .stuck role ((length_append_cons a after before).trans length) (.here rfl) neutral nofun

theorem Neutral.ne_lam {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) {body : Tm Head (n + 1)} : t ≠ .lam body := by
  cases neutral with
  | var => intro h; cases h
  | app => intro h; cases h
  | fst => intro h; cases h
  | snd => intro h; cases h
  | rigid args _ => exact appSpine_const_ne_lam'
  | stuck => exact appSpine_const_ne_lam'

theorem Neutral.ne_pair {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) {a b : Tm Head n} : t ≠ .pair a b := by
  cases neutral with
  | var => intro h; cases h
  | app => intro h; cases h
  | fst => intro h; cases h
  | snd => intro h; cases h
  | rigid args _ => exact appSpine_const_ne_pair
  | stuck => exact appSpine_const_ne_pair

theorem Neutral.ne_refl {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) {a : Tm Head n} : t ≠ .refl a := by
  cases neutral with
  | var => intro h; cases h
  | app => intro h; cases h
  | fst => intro h; cases h
  | snd => intro h; cases h
  | rigid args _ => exact appSpine_const_ne_refl
  | stuck => exact appSpine_const_ne_refl

/-- A neutral constant spine is rigid, or computing and applied to at least its
arity, with a prefix of exactly the arity whose skeleton inspects a neutral
value it does not accept. -/
theorem Neutral.constSpine {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) :
    ∀ {c : DeclName} {args : List (Tm Head n)}, t = appSpine (.const c) args →
      roles c = .rigid ∨ ∃ arity inspect pre post kind a,
        roles c = .computes arity inspect ∧ args = pre ++ post ∧ pre.length = arity ∧
        inspect.Focus roles pre pre kind a a ∧ Neutral roles a ∧
        (kind = .headForm → ¬ HeadForm roles a) := by
  induction neutral with
  | var i =>
      intro c args h
      exact absurd h.symm appSpine_const_ne_var
  | @app f a _ ih =>
      intro c args h
      obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app h.symm
      rcases ih rfl with rigid | ⟨arity, inspect, pre, post, kind, x, role, split, length, rest⟩
      · exact .inl rigid
      · exact .inr ⟨arity, inspect, pre, post ++ [a], kind, x, role,
          by rw [split, List.append_assoc], length, rest⟩
  | fst _ _ =>
      intro c args h
      exact absurd h.symm appSpine_const_ne_fst
  | snd _ _ =>
      intro c args h
      exact absurd h.symm appSpine_const_ne_snd
  | rigid args role =>
      intro c args' h
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective h
      exact .inl role
  | @stuck c arity inspect args kind a role length focus na notHead _ =>
      intro c' args' h
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective h
      exact .inr ⟨arity, inspect, args, [], kind, a, role, (List.append_nil _).symm, length,
        focus, na, notHead⟩

theorem Neutral.not_canonical {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) : ¬ Canonical roles t := by
  rintro (⟨x, rfl⟩ | ⟨k, arity, args, role, rfl⟩)
  · exact neutral.ne_refl rfl
  · rcases neutral.constSpine rfl with rigid | ⟨_, _, _, _, _, _, computes, _⟩
    · rw [role] at rigid; cases rigid
    · rw [role] at computes; cases computes

/-- A neutral value that blocks an inspection is not accepted by it. -/
theorem Neutral.not_accepts {roles : Roles Head} {n : Nat} {a : Tm Head n}
    (neutral : Neutral roles a) {kind : Inspection}
    (notHead : kind = .headForm → ¬ HeadForm roles a) : ¬ kind.Accepts roles a := by
  cases kind with
  | constructor => exact neutral.not_canonical
  | headForm => exact notHead rfl

/-- Neutral terms are weak-head normal forms. -/
theorem Neutral.whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {t : Tm Head n} (neutral : Neutral roles t) : Whnf R roles t := by
  induction neutral with
  | var i => exact var_whnf shape i
  | @app f a nf ih =>
      intro u step
      generalize hterm : Tm.app f a = term at step
      cases step with
      | beta body x =>
          obtain ⟨hf, _⟩ := Tm.app.inj hterm
          exact nf.ne_lam hf
      | appFun inner =>
          obtain ⟨hf, _⟩ := Tm.app.inj hterm
          subst hf
          exact ih _ inner
      | root step =>
          obtain ⟨c, arity, inspect, args, role, equal, length, _⟩ := shape.spine step
          obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app (hterm.trans equal).symm
          rcases nf.constSpine rfl with rigid | ⟨arity', _, pre, post, _, _, computes, split, le, _⟩
          · rw [role] at rigid; cases rigid
          · rw [role] at computes
            injection computes with same _
            subst split
            simp only [List.length_append, List.length_singleton] at length
            omega
      | @scrutinee c arity inspect args args' kind x x' role length _ _ =>
          have e : appSpine (.const c) args = .app f a := hterm.symm
          obtain ⟨init, split, rfl⟩ := appSpine_const_eq_app e
          rcases nf.constSpine rfl with rigid | ⟨arity', _, pre, post, _, _, computes, split', le, _⟩
          · rw [role] at rigid; cases rigid
          · rw [role] at computes
            injection computes with same _
            subst split split'
            simp only [List.length_append, List.length_singleton] at length
            omega
      | fstPair => cases hterm
      | sndPair => cases hterm
      | fst => cases hterm
      | snd => cases hterm
  | @fst p np ih =>
      intro u step
      generalize hterm : Tm.fst p = term at step
      cases step with
      | fstPair a b =>
          exact np.ne_pair (Tm.fst.inj hterm)
      | fst inner =>
          have hp := Tm.fst.inj hterm
          subst hp
          exact ih _ inner
      | root step =>
          obtain ⟨_, _, _, _, _, equal, _⟩ := shape.spine step
          exact appSpine_const_ne_fst (hterm.trans equal).symm
      | scrutinee => exact appSpine_const_ne_fst hterm.symm
      | beta => cases hterm
      | sndPair => cases hterm
      | appFun => cases hterm
      | snd => cases hterm
  | @snd p np ih =>
      intro u step
      generalize hterm : Tm.snd p = term at step
      cases step with
      | sndPair a b =>
          exact np.ne_pair (Tm.snd.inj hterm)
      | snd inner =>
          have hp := Tm.snd.inj hterm
          subst hp
          exact ih _ inner
      | root step =>
          obtain ⟨_, _, _, _, _, equal, _⟩ := shape.spine step
          exact appSpine_const_ne_snd (hterm.trans equal).symm
      | scrutinee => exact appSpine_const_ne_snd hterm.symm
      | beta => cases hterm
      | fstPair => cases hterm
      | appFun => cases hterm
      | fst => cases hterm
  | rigid args role =>
      exact constSpine_whnf shape (by intro a s h; rw [role] at h; cases h) args
  | @stuck c arity inspect args kind a role length focus na notHead ih =>
      intro u step
      have blocked : ¬ kind.Accepts roles a := na.not_accepts notHead
      rcases exactSpine_step shape role length step with
        accepts | ⟨args', kind', b, b', focus', inner, _⟩
      · exact blocked (focus.accepted accepts)
      · obtain ⟨rfl, -, -⟩ := focus.unique focus' blocked
          (fun accepted => Inspection.Accepts.whnf shape accepted _ inner)
        exact ih _ inner

/-- A neutral term is a variable, a constant, an application or a projection. -/
theorem Neutral.shape {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) :
    (∃ i, t = .var i) ∨ (∃ c, t = .const c) ∨ (∃ f a, t = .app f a) ∨
      (∃ p, t = .fst p) ∨ (∃ p, t = .snd p) := by
  cases neutral with
  | var i => exact .inl ⟨i, rfl⟩
  | app => exact .inr (.inr (.inl ⟨_, _, rfl⟩))
  | fst => exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
  | snd => exact .inr (.inr (.inr (.inr ⟨_, rfl⟩)))
  | rigid args _ =>
      rcases appSpine_const_cases _ args with h | ⟨f, a, h⟩
      · exact .inr (.inl ⟨_, h⟩)
      · exact .inr (.inr (.inl ⟨f, a, h⟩))
  | stuck =>
      rcases appSpine_const_cases _ _ with h | ⟨f, a, h⟩
      · exact .inr (.inl ⟨_, h⟩)
      · exact .inr (.inr (.inl ⟨f, a, h⟩))

/-- The type constant of an inductive type is not neutral. -/
theorem Neutral.ne_inductive {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) {T : DeclName}
    {constructors : List (DeclName × List (Field Head))}
    (role : roles T = .inductive constructors) : t ≠ .const T := by
  rintro rfl
  rcases neutral.constSpine (args := []) rfl with rigid | ⟨_, _, _, _, _, _, computes, _⟩
  · rw [role] at rigid; cases rigid
  · rw [role] at computes; cases computes

/-- The type constant of an inductive type is a weak-head normal form. -/
theorem inductive_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {T : DeclName} {constructors : List (DeclName × List (Field Head))}
    (role : roles T = .inductive constructors) : Whnf R roles (.const T : Tm Head n) :=
  constSpine_whnf shape (args := []) (by intro a s h; rw [role] at h; cases h)

/-- A neutral term is not a type former or a head. -/
theorem Neutral.not_former {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) :
    (∀ h, t ≠ .head h) ∧ (∀ A B, t ≠ .pi A B) ∧ (∀ A B, t ≠ .sigma A B) ∧
      (∀ A a b, t ≠ .id A a b) := by
  rcases neutral.shape with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨f, a, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
    exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
      fun _ _ _ h => (nomatch h)⟩

/-! ## Determinism -/

theorem WhStep.deterministic {R : Rules Head} {roles : Roles Head}
    (shape : RootShape R roles) {n : Nat} {t u : Tm Head n}
    (first : WhStep R roles t u) : ∀ {u'}, WhStep R roles t u' → u' = u := by
  induction first with
  | beta body a =>
      intro u' second
      generalize hterm : Tm.app (.lam body) a = term at second
      cases second with
      | beta => obtain ⟨h1, h2⟩ := Tm.app.inj hterm; cases h1; subst h2; rfl
      | appFun inner =>
          obtain ⟨h1, _⟩ := Tm.app.inj hterm
          subst h1
          exact absurd inner (lam_whnf shape body _)
      | root step =>
          obtain ⟨_, _, _, _, _, equal, _⟩ := shape.spine step
          exact absurd (hterm.trans equal).symm appSpine_const_ne_lam
      | scrutinee => exact absurd hterm.symm appSpine_const_ne_lam
      | fstPair => cases hterm
      | sndPair => cases hterm
      | fst => cases hterm
      | snd => cases hterm
  | fstPair a b =>
      intro u' second
      generalize hterm : Tm.fst (.pair a b) = term at second
      cases second with
      | fstPair => have h := Tm.fst.inj hterm; cases h; rfl
      | fst inner =>
          have h := Tm.fst.inj hterm
          subst h
          exact absurd inner (pair_whnf shape a b _)
      | root step =>
          obtain ⟨_, _, _, _, _, equal, _⟩ := shape.spine step
          exact absurd (hterm.trans equal).symm appSpine_const_ne_fst
      | scrutinee => exact absurd hterm.symm appSpine_const_ne_fst
      | beta => cases hterm
      | sndPair => cases hterm
      | appFun => cases hterm
      | snd => cases hterm
  | sndPair a b =>
      intro u' second
      generalize hterm : Tm.snd (.pair a b) = term at second
      cases second with
      | sndPair => have h := Tm.snd.inj hterm; cases h; rfl
      | snd inner =>
          have h := Tm.snd.inj hterm
          subst h
          exact absurd inner (pair_whnf shape a b _)
      | root step =>
          obtain ⟨_, _, _, _, _, equal, _⟩ := shape.spine step
          exact absurd (hterm.trans equal).symm appSpine_const_ne_snd
      | scrutinee => exact absurd hterm.symm appSpine_const_ne_snd
      | beta => cases hterm
      | fstPair => cases hterm
      | appFun => cases hterm
      | fst => cases hterm
  | @root t u step =>
      intro u' second
      obtain ⟨c, arity, inspect, args, role, rfl, length, accepts⟩ := shape.spine step
      generalize hterm : appSpine (.const c) args = term at second
      cases second with
      | root step' => rw [← hterm] at step'; exact shape.deterministic step' step
      | appFun inner =>
          obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app hterm
          simp at length
          exact absurd inner (partialSpine_whnf shape role (by omega) _)
      | @scrutinee c' arity' inspect' args₁ args₂ kind b b' role' length' focus inner =>
          obtain ⟨rfl, rfl⟩ := appSpine_const_injective hterm
          rw [role] at role'
          injection role' with _ same
          subst same
          exact absurd inner (Inspection.Accepts.whnf shape (focus.accepted accepts) _)
      | beta => exact absurd hterm appSpine_const_ne_lam
      | fstPair => exact absurd hterm appSpine_const_ne_fst
      | sndPair => exact absurd hterm appSpine_const_ne_snd
      | fst => exact absurd hterm appSpine_const_ne_fst
      | snd => exact absurd hterm appSpine_const_ne_snd
  | @appFun f f' a inner ih =>
      intro u' second
      generalize hterm : Tm.app f a = term at second
      cases second with
      | appFun inner' =>
          obtain ⟨h1, h2⟩ := Tm.app.inj hterm
          subst h1 h2
          rw [ih inner']
      | beta body x =>
          obtain ⟨h1, _⟩ := Tm.app.inj hterm
          subst h1
          exact absurd inner (lam_whnf shape body _)
      | root step =>
          obtain ⟨c, arity, inspect, args, role, equal, length, _⟩ := shape.spine step
          obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app (hterm.trans equal).symm
          simp at length
          exact absurd inner (partialSpine_whnf shape role (by omega) _)
      | @scrutinee c arity inspect args args' kind x x' role length _ _ =>
          obtain ⟨init, split, rfl⟩ := appSpine_const_eq_app hterm.symm
          subst split
          simp at length
          exact absurd inner (partialSpine_whnf shape role (by omega) _)
      | fstPair => cases hterm
      | sndPair => cases hterm
      | fst => cases hterm
      | snd => cases hterm
  | @fst p p' inner ih =>
      intro u' second
      generalize hterm : Tm.fst p = term at second
      cases second with
      | fst inner' =>
          have h := Tm.fst.inj hterm
          subst h
          rw [ih inner']
      | fstPair =>
          obtain rfl := Tm.fst.inj hterm
          exact absurd inner (pair_whnf shape _ _ _)
      | root step =>
          obtain ⟨_, _, _, _, _, equal, _⟩ := shape.spine step
          exact absurd (hterm.trans equal).symm appSpine_const_ne_fst
      | scrutinee => exact absurd hterm.symm appSpine_const_ne_fst
      | beta => cases hterm
      | sndPair => cases hterm
      | appFun => cases hterm
      | snd => cases hterm
  | @snd p p' inner ih =>
      intro u' second
      generalize hterm : Tm.snd p = term at second
      cases second with
      | snd inner' =>
          have h := Tm.snd.inj hterm
          subst h
          rw [ih inner']
      | sndPair =>
          obtain rfl := Tm.snd.inj hterm
          exact absurd inner (pair_whnf shape _ _ _)
      | root step =>
          obtain ⟨_, _, _, _, _, equal, _⟩ := shape.spine step
          exact absurd (hterm.trans equal).symm appSpine_const_ne_snd
      | scrutinee => exact absurd hterm.symm appSpine_const_ne_snd
      | beta => cases hterm
      | fstPair => cases hterm
      | appFun => cases hterm
      | fst => cases hterm
  | @scrutinee c arity inspect args args' kind a a' role length focus inner ih =>
      intro u' second
      generalize hterm : appSpine (.const c) args = term at second
      cases second with
      | @scrutinee c₂ arity₂ inspect₂ args₂ args₂' kind₂ b b' role₂ length₂ focus₂ inner₂ =>
          obtain ⟨rfl, rfl⟩ := appSpine_const_injective hterm
          rw [role] at role₂
          injection role₂ with _ same
          subst same
          have notA : ¬ kind.Accepts roles a :=
            fun accepted => Inspection.Accepts.whnf shape accepted _ inner
          have notB : ¬ kind₂.Accepts roles b :=
            fun accepted => Inspection.Accepts.whnf shape accepted _ inner₂
          obtain ⟨rfl, -, outputs⟩ := focus₂.unique focus notB notA
          rw [outputs (ih inner₂)]
      | root step =>
          obtain ⟨c', arity', inspect', args₁, role', equal, _, accepts⟩ := shape.spine step
          obtain ⟨rfl, rfl⟩ := appSpine_const_injective (hterm.trans equal)
          rw [role] at role'
          injection role' with _ same
          subst same
          exact absurd inner (Inspection.Accepts.whnf shape (focus.accepted accepts) _)
      | appFun inner' =>
          obtain ⟨init, split, rfl⟩ := appSpine_const_eq_app hterm
          subst split
          simp at length
          exact absurd inner' (partialSpine_whnf shape role (by omega) _)
      | beta => exact absurd hterm appSpine_const_ne_lam
      | fstPair => exact absurd hterm appSpine_const_ne_fst
      | sndPair => exact absurd hterm appSpine_const_ne_snd
      | fst => exact absurd hterm appSpine_const_ne_fst
      | snd => exact absurd hterm appSpine_const_ne_snd

/-- A term has at most one weak-head normal form. -/
theorem WhRed.whnf_unique {R : Rules Head} {roles : Roles Head}
    (shape : RootShape R roles) {n : Nat} {t w w' : Tm Head n}
    (first : WhRed R roles t w) (second : WhRed R roles t w')
    (normal : Whnf R roles w) (normal' : Whnf R roles w') : w = w' := by
  induction first using Relation.ReflTransGen.head_induction_on generalizing w' with
  | refl =>
      cases second using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head step _ => exact absurd step (normal _)
  | head step _ ih =>
      cases second using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd step (normal' _)
      | head step' rest =>
          rw [WhStep.deterministic shape step step'] at rest
          exact ih rest normal'

/-- Reduction to a weak-head normal form cannot be continued, and every other
reduction of the source is an initial segment of it. -/
theorem WhRed.to_whnf {R : Rules Head} {roles : Roles Head}
    (shape : RootShape R roles) {n : Nat} {t w v : Tm Head n}
    (toNormal : WhRed R roles t w) (normal : Whnf R roles w)
    (other : WhRed R roles t v) : WhRed R roles v w := by
  induction other using Relation.ReflTransGen.head_induction_on generalizing w with
  | refl => exact toNormal
  | head step _ ih =>
      cases toNormal using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd step (normal _)
      | head step' rest =>
          rw [WhStep.deterministic shape step step'] at rest
          exact ih rest normal

/-! ## Congruence of reduction -/

theorem WhRed.app {R : Rules Head} {roles : Roles Head} {n : Nat} {f f' : Tm Head n}
    (red : WhRed R roles f f') (a : Tm Head n) :
    WhRed R roles (.app f a) (.app f' a) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appFun step)

theorem WhRed.fst {R : Rules Head} {roles : Roles Head} {n : Nat} {p p' : Tm Head n}
    (red : WhRed R roles p p') : WhRed R roles (.fst p) (.fst p') := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.fst step)

theorem WhRed.snd {R : Rules Head} {roles : Roles Head} {n : Nat} {p p' : Tm Head n}
    (red : WhRed R roles p p') : WhRed R roles (.snd p) (.snd p') := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.snd step)

theorem WhRed.scrutinee {R : Rules Head} {roles : Roles Head} {n : Nat} {c : DeclName}
    {arity : Nat} {before after : List (Tm Head n)} {a a' : Tm Head n}
    (role : roles c = .computes arity (.split before.length .constructor fun _ => .leaf))
    (length : before.length + 1 + after.length = arity)
    (red : WhRed R roles a a') :
    WhRed R roles (appSpine (.const c) (before ++ a :: after))
      (appSpine (.const c) (before ++ a' :: after)) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.scrutinee_single role length step)

/-! ## Renaming and substitution -/

theorem WhStep.rename {R : Rules Head} {roles : Roles Head} {n : Nat} {t u : Tm Head n}
    (step : WhStep R roles t u) : ∀ {m : Nat} (ρ : Ren n m),
      WhStep R roles (Presentation.rename ρ t) (Presentation.rename ρ u) := by
  induction step with
  | beta body a =>
      intro m ρ
      simpa [Presentation.rename, rename_inst0] using
        (WhStep.beta (R := R) (roles := roles) (Presentation.rename (liftRen ρ) body)
          (Presentation.rename ρ a))
  | fstPair a b => intro m ρ; exact .fstPair _ _
  | sndPair a b => intro m ρ; exact .sndPair _ _
  | root step => intro m ρ; exact .root (R.computation.rename ρ step)
  | appFun _ ih => intro m ρ; exact .appFun (ih ρ)
  | fst _ ih => intro m ρ; exact .fst (ih ρ)
  | snd _ ih => intro m ρ; exact .snd (ih ρ)
  | @scrutinee c arity inspect args args' kind a a' role length focus _ ih =>
      intro m ρ
      rw [rename_appSpine, rename_appSpine]
      exact .scrutinee role (by rw [List.length_map]; exact length) (focus.rename ρ) (ih ρ)

theorem WhStep.subst {R : Rules Head} {roles : Roles Head} {n : Nat} {t u : Tm Head n}
    (step : WhStep R roles t u) : ∀ {m : Nat} (σ : Sub Head n m),
      WhStep R roles (Presentation.subst σ t) (Presentation.subst σ u) := by
  induction step with
  | beta body a =>
      intro m σ
      simpa [Presentation.subst, subst_inst0] using
        (WhStep.beta (R := R) (roles := roles) (Presentation.subst (liftSub σ) body)
          (Presentation.subst σ a))
  | fstPair a b => intro m σ; exact .fstPair _ _
  | sndPair a b => intro m σ; exact .sndPair _ _
  | root step => intro m σ; exact .root (R.computation.substitute σ step)
  | appFun _ ih => intro m σ; exact .appFun (ih σ)
  | fst _ ih => intro m σ; exact .fst (ih σ)
  | snd _ ih => intro m σ; exact .snd (ih σ)
  | @scrutinee c arity inspect args args' kind a a' role length focus _ ih =>
      intro m σ
      rw [subst_appSpine, subst_appSpine]
      exact .scrutinee role (by rw [List.length_map]; exact length) (focus.subst σ) (ih σ)

theorem WhRed.rename {R : Rules Head} {roles : Roles Head} {n m : Nat} {t u : Tm Head n}
    (red : WhRed R roles t u) (ρ : Ren n m) :
    WhRed R roles (Presentation.rename ρ t) (Presentation.rename ρ u) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.rename ρ)

theorem WhRed.subst {R : Rules Head} {roles : Roles Head} {n m : Nat} {t u : Tm Head n}
    (red : WhRed R roles t u) (σ : Sub Head n m) :
    WhRed R roles (Presentation.subst σ t) (Presentation.subst σ u) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.subst σ)

theorem Neutral.rename {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) : ∀ {m : Nat} (ρ : Ren n m),
      Neutral roles (Presentation.rename ρ t) := by
  induction neutral with
  | var i => intro m ρ; exact .var _
  | app _ ih => intro m ρ; exact .app (ih ρ)
  | fst _ ih => intro m ρ; exact .fst (ih ρ)
  | snd _ ih => intro m ρ; exact .snd (ih ρ)
  | rigid args role =>
      intro m ρ
      rw [rename_appSpine]
      exact .rigid _ role
  | @stuck c arity inspect args kind a role length focus _ notHead ih =>
      intro m ρ
      rw [rename_appSpine]
      exact .stuck role (by rw [List.length_map]; exact length) (focus.rename ρ) (ih ρ)
        fun isHead ⟨key, view⟩ => notHead isHead ⟨key, view.of_rename⟩

theorem Canonical.rename {roles : Roles Head} {n m : Nat} {t : Tm Head n}
    (canonical : Canonical roles t) (ρ : Ren n m) :
    Canonical roles (Presentation.rename ρ t) := by
  rcases canonical with ⟨x, rfl⟩ | ⟨k, arity, args, role, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨k, arity, args.map (Presentation.rename ρ), role,
      by simp [rename_appSpine, Presentation.rename]⟩

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
