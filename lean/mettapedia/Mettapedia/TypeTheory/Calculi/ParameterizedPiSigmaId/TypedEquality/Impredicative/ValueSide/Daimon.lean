import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Realizers

/-!
# The daimon, the shapes of numbers, and the values of data carriers

The value side of the realizability model has a daimon: a rigid constant `⋆`
that inhabits every type, so that every context, including an inconsistent
one, has a valuation. A term is *daimonic* when it is `⋆` or is stuck on it:
`⋆` applied or projected, a computing constant of exact arity whose scrutinee
is daimonic, or a type case of exact arity whose skeleton inspects, for a head
form, a daimonic value that is none. Daimonic terms are neutral, no type
formers, and stay daimonic under every substitution, because the daimon is a
constant and a substitution keeps the head of a term whose head is no variable.

A term of the numbers has a *shape*: it reduces to `zero`, to the successor of
a term of a shape, or to a daimonic term. Terms with a common shape are
related at the numbers; with the daimon, this is the relation of the numbers
of the value side. It is a data setting whenever the daimon is rigid.

The values of a data carrier are classes of closed terms: a function between
data carriers is read at a value of its domain by applying representatives
(`appData`), and a function from a generic carrier by its application to a
fresh variable (`appGen`). The daimon is a value of every data carrier, and
every carrier has a meaning (`point`): a given meaning of codes, the point of a
rigid type, the daimon at a data carrier, and a constant function into a
generic carrier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Realizability

open Normalization
open Consistency
open StrongNormalization (NumShape)

variable {Head : Type}

/-! ## Daimonic terms -/

/-- Terms stuck on the daimon. -/
inductive Daimonic (roles : Roles Head) (star : DeclName) : {n : Nat} → Tm Head n → Prop where
  | star {n : Nat} : Daimonic roles star (.const star : Tm Head n)
  | app {n : Nat} {f a : Tm Head n} : Daimonic roles star f → Daimonic roles star (.app f a)
  | fst {n : Nat} {p : Tm Head n} : Daimonic roles star p → Daimonic roles star (.fst p)
  | snd {n : Nat} {p : Tm Head n} : Daimonic roles star p → Daimonic roles star (.snd p)
  | stuck {n : Nat} {c : DeclName} {arity : Nat} {before after : List (Tm Head n)}
      {a : Tm Head n} :
      roles c = .computes arity (.split before.length .constructor fun _ => .leaf) →
      before.length + 1 + after.length = arity →
      Daimonic roles star a →
      Daimonic roles star (appSpine (.const c) (before ++ a :: after))
  /-- A type case of exact arity whose skeleton inspects, for a head form, a
  daimonic value that is none. -/
  | typeStuck {n : Nat} {c : DeclName} {arity : Nat} {inspect : InspectTree}
      {args : List (Tm Head n)} {a : Tm Head n} :
      roles c = .computes arity inspect →
      args.length = arity →
      inspect.Focus roles args args .headForm a a →
      Daimonic roles star a →
      ¬ HeadForm roles a →
      Daimonic roles star (appSpine (.const c) args)

/-- A term whose head is no variable is a head form, with the same key, when a
substitution instance of it is: the substitution keeps its head. -/
theorem headView_of_subst {roles : Roles Head} :
    ∀ {n m : Nat} {σ : Sub Head n m} {t : Tm Head n} {key : InspectKey},
      (∀ i, (headArgs t).1 ≠ .var i) → HeadView roles (Presentation.subst σ t) key →
        HeadView roles t key
  | _, _, _, .var i, _, notVar, _ => absurd rfl (notVar i)
  | _, _, _, .const c, _, _, view => by
      change HeadView roles (.const c) _ at view
      generalize e : (Tm.const c : Tm Head _) = t' at view
      cases view with
      | spine args notComputing =>
          obtain ⟨rfl, -⟩ := appSpine_const_injective (as := []) e
          exact .spine [] notComputing
      | _ => cases e
  | _, _, _, .head h, _, _, view => by
      change HeadView roles (.head h) _ at view
      obtain rfl := view.unique (.head h)
      exact .head h
  | _, _, σ, .pi A B, _, _, view => by
      change HeadView roles (.pi (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) _
        at view
      obtain rfl := view.unique (.pi _ _)
      exact .pi A B
  | _, _, σ, .sigma A B, _, _, view => by
      change HeadView roles (.sigma (Presentation.subst σ A) (Presentation.subst (liftSub σ) B)) _
        at view
      obtain rfl := view.unique (.sigma _ _)
      exact .sigma A B
  | _, _, σ, .id A a b, _, _, view => by
      change HeadView roles (.id (Presentation.subst σ A) (Presentation.subst σ a)
        (Presentation.subst σ b)) _ at view
      obtain rfl := view.unique (.id _ _ _)
      exact .id A a b
  | _, _, σ, .lam body, _, _, view => by
      change HeadView roles (.lam (Presentation.subst (liftSub σ) body)) _ at view
      obtain rfl := view.unique (.lam _)
      exact .lam body
  | _, _, σ, .pair a b, _, _, view => by
      change HeadView roles (.pair (Presentation.subst σ a) (Presentation.subst σ b)) _ at view
      obtain rfl := view.unique (.pair _ _)
      exact .pair a b
  | _, _, σ, .refl a, _, _, view => by
      change HeadView roles (.refl (Presentation.subst σ a)) _ at view
      obtain rfl := view.unique (.refl _)
      exact .refl a
  | _, _, σ, .fst p, _, _, view => by
      change HeadView roles (.fst (Presentation.subst σ p)) _ at view
      exfalso
      generalize e : Tm.fst (Presentation.subst σ p) = t' at view
      cases view with
      | spine args _ => exact appSpine_const_ne_fst e.symm
      | _ => cases e
  | _, _, σ, .snd p, _, _, view => by
      change HeadView roles (.snd (Presentation.subst σ p)) _ at view
      exfalso
      generalize e : Tm.snd (Presentation.subst σ p) = t' at view
      cases view with
      | spine args _ => exact appSpine_const_ne_snd e.symm
      | _ => cases e
  | _, _, σ, .app f x, _, notVar, view => by
      change HeadView roles (.app (Presentation.subst σ f) (Presentation.subst σ x)) _ at view
      generalize e : Tm.app (Presentation.subst σ f) (Presentation.subst σ x) = t' at view
      cases view with
      | @spine c args notComputing =>
          obtain ⟨init, -, hf⟩ := appSpine_const_eq_app e.symm
          have viewF : HeadView roles (Presentation.subst σ f) (.const c) := by
            rw [hf]
            exact .spine init notComputing
          have back : HeadView roles f (.const c) := headView_of_subst notVar viewF
          cases back with
          | spine init' notComputing' =>
              rw [← appSpine_concat]
              exact .spine _ notComputing'
      | _ => cases e

namespace Daimonic

variable {roles : Roles Head} {star : DeclName}

section Formers

variable {n : Nat} {t : Tm Head n}

/-- A daimonic term is not a head. -/
theorem ne_head (daimonic : Daimonic roles star t) {h : Head} : t ≠ .head h := by
  cases daimonic with
  | star => intro e; cases e
  | app _ => intro e; cases e
  | fst _ => intro e; cases e
  | snd _ => intro e; cases e
  | stuck _ _ _ => exact Normalization.appSpine_const_ne_head
  | typeStuck _ _ _ _ _ => exact Normalization.appSpine_const_ne_head

/-- A daimonic term is not a dependent function type. -/
theorem ne_pi (daimonic : Daimonic roles star t) {A : Tm Head n} {B : Tm Head (n + 1)} :
    t ≠ .pi A B := by
  cases daimonic with
  | star => intro e; cases e
  | app _ => intro e; cases e
  | fst _ => intro e; cases e
  | snd _ => intro e; cases e
  | stuck _ _ _ => exact appSpine_const_ne_pi
  | typeStuck _ _ _ _ _ => exact appSpine_const_ne_pi

/-- A daimonic term is not a dependent pair type. -/
theorem ne_sigma (daimonic : Daimonic roles star t) {A : Tm Head n} {B : Tm Head (n + 1)} :
    t ≠ .sigma A B := by
  cases daimonic with
  | star => intro e; cases e
  | app _ => intro e; cases e
  | fst _ => intro e; cases e
  | snd _ => intro e; cases e
  | stuck _ _ _ => exact appSpine_const_ne_sigma
  | typeStuck _ _ _ _ _ => exact appSpine_const_ne_sigma

/-- A daimonic term is not an identity type. -/
theorem ne_id (daimonic : Daimonic roles star t) {A a b : Tm Head n} : t ≠ .id A a b := by
  cases daimonic with
  | star => intro e; cases e
  | app _ => intro e; cases e
  | fst _ => intro e; cases e
  | snd _ => intro e; cases e
  | stuck _ _ _ => exact appSpine_const_ne_id
  | typeStuck _ _ _ _ _ => exact appSpine_const_ne_id

end Formers

/-- A daimonic term is neutral when the daimon is rigid. -/
theorem neutral (rigid : roles star = .rigid) {n : Nat} {t : Tm Head n}
    (daimonic : Daimonic roles star t) : Neutral roles t := by
  induction daimonic with
  | star => exact Neutral.rigid (args := []) rigid
  | app _ ih => exact .app ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | stuck role length _ ih => exact .stuck_single role length ih
  | typeStuck role length focus _ notHead ih => exact .stuck role length focus ih fun _ => notHead

/-- A daimonic term has no variable at its head. -/
theorem head_ne_var {n : Nat} {t : Tm Head n} (daimonic : Daimonic roles star t) (i : Fin n) :
    (headArgs t).1 ≠ .var i := by
  induction daimonic with
  | star => intro e; cases e
  | app _ ih => exact ih
  | fst _ => intro e; cases e
  | snd _ => intro e; cases e
  | @stuck c _ before after a _ _ _ _ =>
      rw [headArgs_appSpine (show NotApp (.const c : Tm Head _) by trivial)]
      intro e
      cases e
  | @typeStuck c _ _ args _ _ _ _ _ _ _ =>
      rw [headArgs_appSpine (show NotApp (.const c : Tm Head _) by trivial)]
      intro e
      cases e

/-- A daimonic term is a head form when a substitution instance of it is. -/
theorem headForm_of_subst {n : Nat} {t : Tm Head n} (daimonic : Daimonic roles star t)
    {m : Nat} (σ : Sub Head n m) (head : HeadForm roles (Presentation.subst σ t)) :
    HeadForm roles t := by
  obtain ⟨key, view⟩ := head
  exact ⟨key, headView_of_subst (fun i => daimonic.head_ne_var i) view⟩

/-- Daimonic terms stay daimonic under every substitution. -/
theorem subst {n : Nat} {t : Tm Head n} (daimonic : Daimonic roles star t) :
    ∀ {m : Nat} (σ : Sub Head n m), Daimonic roles star (Presentation.subst σ t) := by
  induction daimonic with
  | star => intro m σ; exact .star
  | app _ ih => intro m σ; exact .app (ih σ)
  | fst _ ih => intro m σ; exact .fst (ih σ)
  | snd _ ih => intro m σ; exact .snd (ih σ)
  | @stuck c arity before after a role length _ ih =>
      intro m σ
      have role' : roles c = .computes arity
          (.split (before.map (Presentation.subst σ)).length .constructor fun _ => .leaf) := by
        simpa using role
      have length' : (before.map (Presentation.subst σ)).length + 1 +
          (after.map (Presentation.subst σ)).length = arity := by simpa using length
      simpa [subst_appSpine, Presentation.subst] using
        (Daimonic.stuck role' length' (ih σ))
  | @typeStuck c arity inspect args a role length focus daimonic notHead ih =>
      intro m σ
      rw [subst_appSpine]
      exact .typeStuck role (by rw [List.length_map]; exact length) (focus.subst σ) (ih σ)
        fun head => notHead (daimonic.headForm_of_subst σ head)

theorem rename {n m : Nat} {t : Tm Head n} (daimonic : Daimonic roles star t)
    (ρ : Ren n m) : Daimonic roles star (Presentation.rename ρ t) := by
  have h := daimonic.subst (renSub ρ)
  rwa [subst_renSub] at h

/-- A daimonic term is no spine of a constant other than the daimon and the
computing constants. -/
theorem constSpine {n : Nat} {t : Tm Head n} (daimonic : Daimonic roles star t)
    {c : DeclName} {args : List (Tm Head n)} (equal : t = appSpine (.const c) args) :
    c = star ∨ ∃ arity inspect, roles c = .computes arity inspect := by
  induction daimonic generalizing args with
  | star =>
      have e := appSpine_const_injective (as := []) equal
      exact .inl e.1.symm
  | @app f a _ ih =>
      obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app equal.symm
      exact ih rfl
  | fst _ _ => exact absurd equal.symm appSpine_const_ne_fst
  | snd _ _ => exact absurd equal.symm appSpine_const_ne_snd
  | @stuck c' arity before _ _ role _ _ _ =>
      obtain ⟨rfl, _⟩ := appSpine_const_injective equal
      exact .inr ⟨arity, _, role⟩
  | @typeStuck c' arity inspect _ _ role _ _ _ _ _ =>
      obtain ⟨rfl, _⟩ := appSpine_const_injective equal
      exact .inr ⟨arity, inspect, role⟩

end Daimonic

/-! ## Shapes of numbers -/

/-- A term of the numbers with its shape. -/
inductive HasShape (S : Consistency.Setting Head) (star : DeclName) {n : Nat} :
    Tm Head n → NumShape → Prop where
  | zero {t : Tm Head n} : WhRed S.rules S.roles t (.const S.zero) → HasShape S star t .zero
  | suc {t a : Tm Head n} {s : NumShape} :
      WhRed S.rules S.roles t (.app (.const S.suc) a) → HasShape S star a s →
      HasShape S star t (.suc s)
  | star {t u : Tm Head n} :
      WhRed S.rules S.roles t u → Daimonic S.roles star u → HasShape S star t .star

namespace HasShape

variable {S : Consistency.Setting Head} {star : DeclName}

theorem expand {n : Nat} {t t' : Tm Head n} {s : NumShape} (red : WhRed S.rules S.roles t t')
    (shape : HasShape S star t' s) : HasShape S star t s := by
  cases shape with
  | zero r => exact .zero (red.trans r)
  | suc r a => exact .suc (red.trans r) a
  | star r d => exact .star (red.trans r) d

theorem subst {n : Nat} {t : Tm Head n} {s : NumShape} (shape : HasShape S star t s) :
    ∀ {m : Nat} (σ : Sub Head n m), HasShape S star (Presentation.subst σ t) s := by
  induction shape with
  | zero red => intro m σ; exact .zero (red.subst σ)
  | suc red _ ih => intro m σ; exact .suc (red.subst σ) (ih σ)
  | star red daimonic => intro m σ; exact .star (red.subst σ) (daimonic.subst σ)

/-- The shape of a numeral. -/
def ofNat : Nat → NumShape
  | 0 => .zero
  | k + 1 => .suc (ofNat k)

theorem numeral {n : Nat} (k : Nat) :
    HasShape S star (numeral S k : Tm Head n) (ofNat k) := by
  induction k with
  | zero => exact .zero .refl
  | succ k ih => exact .suc .refl ih

theorem ofNat_injective : ∀ {k k' : Nat}, ofNat k = ofNat k' → k = k'
  | 0, 0, _ => rfl
  | 0, _ + 1, equal => by cases equal
  | _ + 1, 0, equal => by cases equal
  | _ + 1, _ + 1, equal => by
      injection equal with equal
      rw [ofNat_injective equal]

/-- A term has at most one shape, when the setting's codes and numerals are
weak-head normal and the daimon is rigid. -/
theorem deterministic (laws : S.Laws) (rigid : S.roles star = .rigid) {n : Nat}
    {t : Tm Head n} {s s' : NumShape} (first : HasShape S star t s)
    (second : HasShape S star t s') : s = s' := by
  have starNotZero : star ≠ S.zero := by
    intro e
    rw [e, laws.zero] at rigid
    cases rigid
  have starNotSuc : star ≠ S.suc := by
    intro e
    rw [e, laws.suc] at rigid
    cases rigid
  have zeroNotDaimonic : ¬ Daimonic S.roles star (.const S.zero : Tm Head n) := fun d => by
    rcases d.constSpine (args := []) rfl with e | ⟨_, _, role⟩
    · exact starNotZero e.symm
    · rw [laws.zero] at role; cases role
  have sucNotDaimonic : ∀ a : Tm Head n,
      ¬ Daimonic S.roles star (.app (.const S.suc) a) := fun a d => by
    rcases d.constSpine (args := [a]) rfl with e | ⟨_, _, role⟩
    · exact starNotSuc e.symm
    · rw [laws.suc] at role; cases role
  induction first generalizing s' with
  | zero red =>
      cases second with
      | zero _ => rfl
      | suc red' _ =>
          cases WhRed.whnf_unique laws.shape red red' laws.whnf_zero (laws.whnf_suc _)
      | star red' d =>
          have e := WhRed.whnf_unique laws.shape red red' laws.whnf_zero
            ((d.neutral rigid).whnf laws.shape)
          subst e
          exact absurd d zeroNotDaimonic
  | suc red _ ih =>
      cases second with
      | zero red' =>
          cases WhRed.whnf_unique laws.shape red red' (laws.whnf_suc _) laws.whnf_zero
      | suc red' shape' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_suc _) (laws.whnf_suc _)
          cases e
          rw [ih shape']
      | star red' d =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_suc _)
            ((d.neutral rigid).whnf laws.shape)
          subst e
          exact absurd d (sucNotDaimonic _)
  | star red d =>
      cases second with
      | zero red' =>
          have e := WhRed.whnf_unique laws.shape red red' ((d.neutral rigid).whnf laws.shape)
            laws.whnf_zero
          subst e
          exact absurd d zeroNotDaimonic
      | suc red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' ((d.neutral rigid).whnf laws.shape)
            (laws.whnf_suc _)
          subst e
          exact absurd d (sucNotDaimonic _)
      | star _ _ => rfl

end HasShape

/-- A daimonic term is no spine of a variable. -/
theorem Daimonic.ne_varSpine {roles : Roles Head} {star : DeclName} {n : Nat} {t : Tm Head n}
    (daimonic : Daimonic roles star t) {i : Fin n} {args : List (Tm Head n)} :
    t ≠ appSpine (.var i) args := by
  intro e
  have head := congrArg (fun t => (headArgs t).1) e
  simp only [headArgs_appSpine (show NotApp (.var i : Tm Head n) by trivial)] at head
  exact daimonic.head_ne_var i head

end Realizability

/-! ## The numbers with the daimon -/

namespace Consistency

open Realizability

variable {Head : Type}

/-- The relation of the numbers with the daimon: terms with a common shape. -/
def Setting.shapes (S : Setting Head) (star : DeclName) : DataSetting Head where
  toSetting := S
  base := fun t t' => ∃ s, HasShape S star t s ∧ HasShape S star t' s
  base_subst₂ := fun σ σ' ⟨s, h, h'⟩ => ⟨s, h.subst σ, h'.subst σ'⟩
  base_symm := fun ⟨s, h, h'⟩ => ⟨s, h', h⟩
  base_expand := fun red red' ⟨s, h, h'⟩ => ⟨s, h.expand red, h'.expand red'⟩
  base_zero := ⟨.zero, .zero .refl, .zero .refl⟩
  base_suc := fun ⟨s, h, h'⟩ => ⟨.suc s, .suc .refl h, .suc .refl h'⟩

theorem Setting.Laws.shapes {S : Setting Head} (laws : S.Laws) {star : DeclName}
    (rigid : S.roles star = .rigid) : (S.shapes star).Laws where
  toLaws := laws
  base_trans := fun ⟨s, h, h'⟩ ⟨_, g, g'⟩ => by
    obtain rfl := HasShape.deterministic laws rigid h' g
    exact ⟨s, h, g'⟩
  numeral_injective := fun ⟨_, first, second⟩ =>
    HasShape.ofNat_injective ((HasShape.deterministic laws rigid (HasShape.numeral _) first).trans
      (HasShape.deterministic laws rigid second (HasShape.numeral _)))

end Consistency

/-! ## Values of data carriers and the daimon -/

namespace Realizability

open Normalization
open Consistency

variable {Head : Type}

/-! ## Values of data carriers -/

section Values

variable {S : DataSetting Head} {P : Type}

/-- A value of a data carrier as a class of closed terms. -/
def toQ : {D : Carrier .data} → D.Val S P → Q S D
  | .num, v => v
  | @Carrier.arr _ .data _ _, v => v

/-- A closed function related to itself at a data carrier from a data carrier
sends related closed arguments to related results. -/
theorem DataEq.app_closed {A B : Carrier .data} {f f' : Tm Head 0}
    (related : DataEq S (.arr A B) f f') {s s' : Tm Head 0} (args : DataEq S A s s') :
    DataEq S B (.app f s) (.app f' s') := by
  have h := related (idRen : Ren 0 0) args
  simpa only [rename_id] using h

/-- The value of a function from a generic carrier into a data carrier: the
value of its application to a fresh variable, which does not depend on the
argument. -/
def appGen {A : Carrier .gen} {B : Carrier .data} (F : Q S (.arr A B)) : B.Val S P :=
  Quot.lift
    (fun f : Realizer (S := S) (.arr A B) =>
      dataValue S B (.app (Presentation.rename wk f.1) (.var 0)) f.2)
    (fun f g related => dataValue_sound (D := B) f.2 g.2 related) F

/-- The value of a function between data carriers at a value of its domain:
the value of the application of representatives. -/
def appData {A B : Carrier .data} (F : Q S (.arr A B)) (a : A.Val S P) : B.Val S P :=
  Quot.lift
    (fun f : Realizer (S := S) (.arr A B) =>
      Quot.lift
        (fun s : Realizer (S := S) A =>
          dataValue S B (.app f.1 s.1) (DataEq.app_closed (S := S) (A := A) (B := B) f.2 s.2))
        (fun _ _ related =>
          dataValue_sound _ _ (DataEq.app_closed (S := S) (A := A) (B := B) f.2 related))
        (toQ a))
    (fun f g related =>
      Quot.ind (β := fun q =>
          Quot.lift (fun s : Realizer (S := S) A =>
              dataValue (P := P) S B (.app f.1 s.1)
                (DataEq.app_closed (S := S) (A := A) (B := B) f.2 s.2))
            (fun _ _ related' => dataValue_sound _ _
              (DataEq.app_closed (S := S) (A := A) (B := B) f.2 related')) q =
          Quot.lift (fun s : Realizer (S := S) A =>
              dataValue (P := P) S B (.app g.1 s.1)
                (DataEq.app_closed (S := S) (A := A) (B := B) g.2 s.2))
            (fun _ _ related' => dataValue_sound _ _
              (DataEq.app_closed (S := S) (A := A) (B := B) g.2 related')) q)
        (fun s => dataValue_sound _ _
          (DataEq.app_closed (S := S) (A := A) (B := B) related s.2)) (toQ a))
    F

end Values

/-! ## The daimon at data carriers -/

section Daimon

variable (S : Consistency.Setting Head) (star : DeclName) {P : Type}

/-- Daimonic terms are related at every data carrier. -/
theorem DataEq.daimonic : ∀ {k : Kind} (D : Carrier k), k = .data → ∀ {n : Nat}
    {t t' : Tm Head n}, Daimonic S.roles star t → Daimonic S.roles star t' →
      DataEq (S.shapes star) D t t'
  | _, .num, _, _, _, _, daimonic, daimonic' =>
      ⟨.star, .star .refl daimonic, .star .refl daimonic'⟩
  | _, @Carrier.arr .gen .data _ B, _, _, _, _, daimonic, daimonic' =>
      DataEq.daimonic B rfl (.app (daimonic.rename wk)) (.app (daimonic'.rename wk))
  | _, @Carrier.arr .data .data _ B, _, _, _, _, daimonic, daimonic' => by
      intro ρ s s' _
      exact DataEq.daimonic B rfl (.app (daimonic.rename ρ)) (.app (daimonic'.rename ρ))
  | _, .prop, isData, _, _, _, _, _ => nomatch isData
  | _, .rigid _, isData, _, _, _, _, _ => nomatch isData
  | _, @Carrier.arr _ .gen _ _, isData, _, _, _, _, _ => nomatch isData

/-- The daimon as a value of a data carrier. -/
def daimonValue (D : Carrier .data) : D.Val (S.shapes star) P :=
  dataValue (S.shapes star) D (.const star : Tm Head 0)
    (DataEq.daimonic S star D rfl .star .star)

/-- A meaning of every carrier: a given meaning of codes at `prop`, the point
of a rigid type, the daimon at a data carrier, and a constant function into a
generic carrier. -/
def point (top : P) : {k : Kind} → (A : Carrier k) → A.Val (S.shapes star) P
  | _, .prop => top
  | _, .rigid _ => ()
  | _, .num => daimonValue S star .num
  | _, @Carrier.arr _ .gen _ B => fun _ => point top B
  | _, @Carrier.arr _ .data A B => daimonValue S star (.arr A B)

end Daimon

end Realizability

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
