import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Cast
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mathlib.Logic.Relation
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Carriers, data, readings and worlds

The quantifier and equation codes range over carriers: the simple types over
`prop`, the numbers and the rigid base types. A carrier has one of two kinds,
the kind of its final codomain:

* a *generic* carrier ends in `prop` or a rigid type;
* a *data* carrier ends in the numbers.

Data is interpreted by its terms. A *data setting* supplies the relation of
the numbers; two terms are then related at a data carrier when they compute
related numbers: at a function from a generic carrier, their applications to
a fresh variable are related; at a function from a data carrier, they send
related arguments to related results under every renaming. The relation is
defined before any meaning of codes and does not mention worlds. A value of a
data carrier is a class of closed terms related to themselves, and the value
of an open term is the class of its closure, so every value is the value of a
term.

A *reading* adds a type of meanings for codes with operations interpreting
implication, the quantifiers and the equations, and optionally a class of
neutral codes with a meaning of their own. A generic carrier means a meaning
at `prop`, one point at a rigid type, and a function of meanings at an arrow;
a predicate on a data carrier is a function on its values.

Terms are read in worlds: each free variable is a generic, a generic carrier
with a meaning.

The consistency model reads codes by truth values: its data setting relates
terms with a common numeral, its meanings are Lean propositions, and it has no
neutral codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization
open TelescopeAbstraction (subst_empty liftClosed_zero)

/-! ## Carriers -/

/-- The kinds of carriers: generic carriers end in `prop` or a rigid type,
data carriers end in the numbers. -/
inductive Kind where
  | gen
  | data
  deriving DecidableEq

/-- The carriers of the quantifier and equation codes, with their kinds: the
simple types over `prop`, the numbers and the rigid base types. A function
carrier has the kind of its codomain. -/
inductive Carrier : Kind → Type where
  | prop : Carrier .gen
  | rigid (T : DeclName) : Carrier .gen
  | num : Carrier .data
  | arr {k k' : Kind} (A : Carrier k) (B : Carrier k') : Carrier k'

/-! ## The setting -/

/-- What the model reads from a rule package: its reduction and roles, the
constructors of the numbers, and the names of the codes with the carriers of
the quantifier and equation instances. -/
structure Setting (Head : Type) where
  rules : Rules Head
  roles : Roles Head
  zero : DeclName
  suc : DeclName
  imp : DeclName
  allCarrier : DeclName → Option (Σ k, Carrier k)
  eqCarrier : DeclName → Option (Σ k, Carrier k)

section Numerals

variable {Head : Type} (S : Setting Head)

/-! ## Numerals -/

/-- A term of the numbers with its value: it reduces to a numeral. -/
inductive NumVal {n : Nat} : Tm Head n → Nat → Prop where
  | zero {t : Tm Head n} : WhRed S.rules S.roles t (.const S.zero) → NumVal t 0
  | suc {t a : Tm Head n} {k : Nat} :
      WhRed S.rules S.roles t (.app (.const S.suc) a) → NumVal a k → NumVal t (k + 1)

/-- The numeral of a natural number. -/
def numeral {n : Nat} : Nat → Tm Head n
  | 0 => .const S.zero
  | k + 1 => .app (.const S.suc) (numeral k)

variable {S}

theorem numVal_numeral {n : Nat} (k : Nat) : NumVal S (numeral S k : Tm Head n) k := by
  induction k with
  | zero => exact .zero .refl
  | succ k ih => exact .suc .refl ih

@[simp] theorem rename_numeral {n m : Nat} (ρ : Ren n m) (k : Nat) :
    Presentation.rename ρ (numeral S k) = numeral S k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [numeral, Presentation.rename, ih]

@[simp] theorem subst_numeral {n m : Nat} (σ : Sub Head n m) (k : Nat) :
    Presentation.subst σ (numeral S k) = numeral S k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [numeral, Presentation.subst, ih]

theorem NumVal.expand {n : Nat} {t t' : Tm Head n} {k : Nat}
    (red : WhRed S.rules S.roles t t') (value : NumVal S t' k) : NumVal S t k := by
  cases value with
  | zero r => exact .zero (red.trans r)
  | suc r a => exact .suc (red.trans r) a

theorem NumVal.rename {n m : Nat} {t : Tm Head n} {k : Nat} (value : NumVal S t k)
    (ρ : Ren n m) : NumVal S (Presentation.rename ρ t) k := by
  induction value with
  | zero red => exact .zero (red.rename ρ)
  | suc red _ ih => exact .suc (red.rename ρ) ih

theorem NumVal.subst {n m : Nat} {t : Tm Head n} {k : Nat} (value : NumVal S t k)
    (σ : Sub Head n m) : NumVal S (Presentation.subst σ t) k := by
  induction value with
  | zero red => exact .zero (red.subst σ)
  | suc red _ ih => exact .suc (red.subst σ) ih

/-! ## The laws of a setting -/

/-- The roles that make codes and numerals weak-head normal and
distinguishable. -/
structure Setting.Laws (S : Setting Head) : Prop where
  shape : RootShape S.rules S.roles
  zero : S.roles S.zero = .constructor 0
  suc : S.roles S.suc = .constructor 1
  imp : S.roles S.imp = .constructor 2
  all : ∀ {a : DeclName} {A : Σ k, Carrier k}, S.allCarrier a = some A →
    S.roles a = .constructor 1
  eq : ∀ {e : DeclName} {A : Σ k, Carrier k}, S.eqCarrier e = some A →
    S.roles e = .constructor 2
  impNotEq : S.eqCarrier S.imp = none

theorem Neutral.appSpine' {roles : Roles Head} {n : Nat} {f : Tm Head n}
    (neutral : Neutral roles f) : ∀ args : List (Tm Head n), Neutral roles (appSpine f args)
  | [] => neutral
  | _ :: args => Neutral.appSpine' (.app neutral) args

theorem constSpine_ne_varSpine {n : Nat} {c : DeclName} {i : Fin n}
    {as bs : List (Tm Head n)} : appSpine (.const c) as ≠ appSpine (.var i) bs := by
  intro equal
  have := (appSpine_injective (by trivial) (by trivial) equal).1
  cases this

namespace Setting.Laws

variable (laws : S.Laws)
include laws

theorem whnf_zero {n : Nat} : Whnf S.rules S.roles (.const S.zero : Tm Head n) :=
  canonical_whnf laws.shape (.inr ⟨S.zero, 0, [], laws.zero, rfl⟩)

theorem whnf_suc {n : Nat} (a : Tm Head n) : Whnf S.rules S.roles (.app (.const S.suc) a) :=
  canonical_whnf laws.shape (.inr ⟨S.suc, 1, [a], laws.suc, rfl⟩)

theorem whnf_imp {n : Nat} (p q : Tm Head n) :
    Whnf S.rules S.roles (.app (.app (.const S.imp) p) q) :=
  canonical_whnf laws.shape (.inr ⟨S.imp, 2, [p, q], laws.imp, rfl⟩)

theorem whnf_all {n : Nat} {a : DeclName} {A : Σ k, Carrier k} (carrier : S.allCarrier a = some A)
    (f : Tm Head n) : Whnf S.rules S.roles (.app (.const a) f) :=
  canonical_whnf laws.shape (.inr ⟨a, 1, [f], laws.all carrier, rfl⟩)

theorem whnf_eq {n : Nat} {e : DeclName} {A : Σ k, Carrier k} (carrier : S.eqCarrier e = some A)
    (x y : Tm Head n) : Whnf S.rules S.roles (.app (.app (.const e) x) y) :=
  canonical_whnf laws.shape (.inr ⟨e, 2, [x, y], laws.eq carrier, rfl⟩)

theorem whnf_generic {n : Nat} (i : Fin n) (args : List (Tm Head n)) :
    Whnf S.rules S.roles (appSpine (.var i) args) :=
  (Neutral.appSpine' (.var i) args).whnf laws.shape

end Setting.Laws

theorem NumVal.deterministic (laws : S.Laws) {n : Nat} {t : Tm Head n} {k k' : Nat}
    (first : NumVal S t k) (second : NumVal S t k') : k = k' := by
  induction first generalizing k' with
  | zero red =>
      cases second with
      | zero _ => rfl
      | suc red' _ =>
          have e := WhRed.whnf_unique laws.shape red red' laws.whnf_zero (laws.whnf_suc _)
          cases e
  | suc red _ ih =>
      cases second with
      | zero red' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_suc _) laws.whnf_zero
          cases e
      | suc red' value' =>
          have e := WhRed.whnf_unique laws.shape red red' (laws.whnf_suc _) (laws.whnf_suc _)
          cases e
          rw [ih value']

end Numerals

/-! ## Two contexts side by side -/

section Append

variable {Head : Type}

/-- The substitution that applies `σ` to the left variables and keeps the right
ones. -/
def appendSub {n m : Nat} (σ : Sub Head n m) : Sub Head (n + m) m :=
  Fin.append σ (fun j => .var j)

theorem subst_appendSub_castAdd {n m : Nat} (σ : Sub Head n m) (t : Tm Head n) :
    Presentation.subst (appendSub σ) (Presentation.rename (Fin.castAdd m) t) =
      Presentation.subst σ t := by
  rw [subst_rename]
  congr 1
  funext i
  simp only [appendSub, Fin.append_left]

theorem subst_appendSub_natAdd {n m : Nat} (σ : Sub Head n m) (s : Tm Head m) :
    Presentation.subst (appendSub σ) (Presentation.rename (Fin.natAdd n) s) = s := by
  rw [subst_rename]
  have : (fun j => appendSub σ (Fin.natAdd n j)) = (ids : Sub Head m m) := by
    funext j
    simp only [appendSub, Fin.append_right]
    rfl
  rw [this, subst_ids]

end Append

/-! ## Data settings -/

/-- A setting with the relation of the numbers. The relation is symmetric,
closed under reduction and under independent substitutions of its two sides,
relates `zero` to itself, and relates the successors of related terms. -/
structure DataSetting (Head : Type) extends Setting Head where
  base : ∀ {n : Nat}, Tm Head n → Tm Head n → Prop
  base_subst₂ : ∀ {n m : Nat} {t t' : Tm Head n} (σ σ' : Sub Head n m), base t t' →
    base (Presentation.subst σ t) (Presentation.subst σ' t')
  base_symm : ∀ {n : Nat} {t t' : Tm Head n}, base t t' → base t' t
  base_expand : ∀ {n : Nat} {t u t' u' : Tm Head n}, WhRed rules roles t u →
    WhRed rules roles t' u' → base u u' → base t t'
  base_zero : ∀ {n : Nat}, base (.const zero : Tm Head n) (.const zero)
  base_suc : ∀ {n : Nat} {a b : Tm Head n}, base a b →
    base (.app (.const suc) a) (.app (.const suc) b)

/-- The laws of a data setting: those of its setting, transitivity of the
relation of the numbers, and that the relation tells numerals apart. -/
structure DataSetting.Laws {Head : Type} (S : DataSetting Head) : Prop
    extends Setting.Laws S.toSetting where
  base_trans : ∀ {n : Nat} {t t' t'' : Tm Head n}, S.base t t' → S.base t' t'' → S.base t t''
  numeral_injective : ∀ {n : Nat} {k k' : Nat},
    S.base (numeral S.toSetting k : Tm Head n) (numeral S.toSetting k') → k = k'

instance {Head : Type} : CoeOut (DataSetting Head) (Setting Head) := ⟨DataSetting.toSetting⟩

section Data

variable {Head : Type} (S : DataSetting Head)

/-! ## Related data -/

/-- Terms related at a data carrier: at the numbers, terms related by the data
setting; at a function from a generic carrier, terms whose applications to a
fresh variable are related; at a function from a data carrier, terms that send
related arguments to related results, under every renaming. A generic carrier
relates no terms here: its relation depends on the meanings of codes. -/
def DataEq : {k : Kind} → Carrier k → {n : Nat} → Tm Head n → Tm Head n → Prop
  | _, .num, _, t, t' => S.base t t'
  | _, @Carrier.arr .gen .data _ B, _, t, t' =>
      DataEq B (.app (Presentation.rename wk t) (.var 0))
        (.app (Presentation.rename wk t') (.var 0))
  | _, @Carrier.arr .data .data A B, n, t, t' =>
      ∀ {m : Nat} (ρ : Ren n m) {s s' : Tm Head m}, DataEq A s s' →
        DataEq B (.app (Presentation.rename ρ t) s) (.app (Presentation.rename ρ t') s')
  | _, .prop, _, _, _ => False
  | _, .rigid _, _, _, _ => False
  | _, @Carrier.arr .gen .gen _ _, _, _, _ => False
  | _, @Carrier.arr .data .gen _ _, _, _, _ => False

variable {S}

/-- Related data stays related under independent substitutions of the two
sides: the numerals it computes are closed. -/
theorem DataEq.subst₂ : ∀ {k : Kind} (D : Carrier k) {n m : Nat} {t t' : Tm Head n},
    DataEq S D t t' → ∀ (σ σ' : Sub Head n m),
      DataEq S D (Presentation.subst σ t) (Presentation.subst σ' t')
  | _, .num, _, _, _, _, rel, σ, σ' => S.base_subst₂ σ σ' rel
  | _, @Carrier.arr .gen .data _ B, _, _, t, t', rel, σ, σ' => by
      have h := DataEq.subst₂ B rel (liftSub σ) (liftSub σ')
      simp only [Presentation.subst, subst_liftSub_wk] at h
      exact h
  | _, @Carrier.arr .data .data A B, n, _, t, t', rel, σ, σ' => by
      intro ρ s s' rs
      have rs' : DataEq S A (Presentation.rename (Fin.natAdd n) s)
          (Presentation.rename (Fin.natAdd n) s') := by
        have h := DataEq.subst₂ A rs (renSub (Fin.natAdd n)) (renSub (Fin.natAdd n))
        simp only [subst_renSub] at h
        exact h
      have h := DataEq.subst₂ B (rel (Fin.castAdd _) rs')
        (appendSub fun i => Presentation.rename ρ (σ i))
        (appendSub fun i => Presentation.rename ρ (σ' i))
      simp only [Presentation.subst, subst_appendSub_castAdd, subst_appendSub_natAdd] at h
      rw [rename_subst, rename_subst]
      exact h
  | _, .prop, _, _, _, _, rel, _, _ => rel.elim
  | _, .rigid _, _, _, _, _, rel, _, _ => rel.elim
  | _, @Carrier.arr .gen .gen _ _, _, _, _, _, rel, _, _ => rel.elim
  | _, @Carrier.arr .data .gen _ _, _, _, _, _, rel, _, _ => rel.elim

theorem DataEq.rename₂ {k : Kind} {D : Carrier k} {n m : Nat} {t t' : Tm Head n}
    (rel : DataEq S D t t') (ρ : Ren n m) :
    DataEq S D (Presentation.rename ρ t) (Presentation.rename ρ t') := by
  have h := DataEq.subst₂ D rel (renSub ρ) (renSub ρ)
  simp only [subst_renSub] at h
  exact h

theorem DataEq.symm : ∀ {k : Kind} {D : Carrier k} {n : Nat} {t t' : Tm Head n},
    DataEq S D t t' → DataEq S D t' t
  | _, .num, _, _, _, rel => S.base_symm rel
  | _, @Carrier.arr .gen .data _ B, _, _, _, rel => DataEq.symm (D := B) rel
  | _, @Carrier.arr .data .data A B, _, _, _, rel => fun ρ _ _ rs =>
      DataEq.symm (D := B) (rel ρ (DataEq.symm (D := A) rs))
  | _, .prop, _, _, _, rel => rel.elim
  | _, .rigid _, _, _, _, rel => rel.elim
  | _, @Carrier.arr .gen .gen _ _, _, _, _, rel => rel.elim
  | _, @Carrier.arr .data .gen _ _, _, _, _, rel => rel.elim

theorem DataEq.trans (laws : S.Laws) : ∀ {k : Kind} {D : Carrier k} {n : Nat}
    {t t' t'' : Tm Head n}, DataEq S D t t' → DataEq S D t' t'' → DataEq S D t t''
  | _, .num, _, _, _, _, first, second => laws.base_trans first second
  | _, @Carrier.arr .gen .data _ B, _, _, _, _, first, second =>
      DataEq.trans laws (D := B) first second
  | _, @Carrier.arr .data .data A B, _, _, _, _, first, second => fun ρ _ _ rs =>
      DataEq.trans laws (D := B) (first ρ rs)
        (second ρ (DataEq.trans laws (D := A) (DataEq.symm rs) rs))
  | _, .prop, _, _, _, _, rel, _ => rel.elim
  | _, .rigid _, _, _, _, _, rel, _ => rel.elim
  | _, @Carrier.arr .gen .gen _ _, _, _, _, _, rel, _ => rel.elim
  | _, @Carrier.arr .data .gen _ _, _, _, _, _, rel, _ => rel.elim

theorem DataEq.refl_left (laws : S.Laws) {k : Kind} {D : Carrier k} {n : Nat}
    {t t' : Tm Head n} (rel : DataEq S D t t') : DataEq S D t t :=
  DataEq.trans laws rel rel.symm

theorem DataEq.refl_right (laws : S.Laws) {k : Kind} {D : Carrier k} {n : Nat}
    {t t' : Tm Head n} (rel : DataEq S D t t') : DataEq S D t' t' :=
  DataEq.trans laws rel.symm rel

/-- Related data stays related along reduction. -/
theorem DataEq.expand : ∀ {k : Kind} {D : Carrier k} {n : Nat} {t u t' u' : Tm Head n},
    WhRed S.rules S.roles t u → WhRed S.rules S.roles t' u' → DataEq S D u u' →
      DataEq S D t t'
  | _, .num, _, _, _, _, _, red, red', rel => S.base_expand red red' rel
  | _, @Carrier.arr .gen .data _ B, _, _, _, _, _, red, red', rel =>
      DataEq.expand (D := B) ((red.rename wk).app _) ((red'.rename wk).app _) rel
  | _, @Carrier.arr .data .data _ B, _, _, _, _, _, red, red', rel => fun ρ _ _ rs =>
      DataEq.expand (D := B) ((red.rename ρ).app _) ((red'.rename ρ).app _) (rel ρ rs)
  | _, .prop, _, _, _, _, _, _, _, rel => rel.elim
  | _, .rigid _, _, _, _, _, _, _, _, rel => rel.elim
  | _, @Carrier.arr .gen .gen _ _, _, _, _, _, _, _, _, rel => rel.elim
  | _, @Carrier.arr .data .gen _ _, _, _, _, _, _, _, _, rel => rel.elim

/-! ## Closures -/

variable (S) in
/-- The closure of a term: every free variable replaced by `zero`. -/
def close {n : Nat} (t : Tm Head n) : Tm Head 0 :=
  Presentation.subst (fun _ => .const S.zero) t

theorem close_rename {n m : Nat} (ρ : Ren n m) (t : Tm Head n) :
    close S (Presentation.rename ρ t) = close S t := by
  simp only [close, subst_rename]

theorem close_closed (t : Tm Head 0) : close S t = t := by
  rw [close, subst_empty, liftClosed_zero]

theorem close_liftClosed {n : Nat} (t : Tm Head 0) : close S (liftClosed t : Tm Head n) = t := by
  rw [close, subst_liftClosed, liftClosed_zero]

theorem liftClosed_close {n : Nat} (t : Tm Head n) :
    (liftClosed (close S t) : Tm Head n) = Presentation.subst (fun _ => .const S.zero) t := by
  simp only [close, liftClosed, rename_subst]
  rfl

theorem DataEq.closure {D : Carrier .data} {n : Nat} {t t' : Tm Head n}
    (rel : DataEq S D t t') : DataEq S D (close S t) (close S t') :=
  DataEq.subst₂ D rel _ _

/-- A term related to itself is related to its closure. -/
theorem DataEq.to_close {D : Carrier .data} {n : Nat} {t : Tm Head n}
    (rel : DataEq S D t t) : DataEq S D t (liftClosed (close S t)) := by
  rw [liftClosed_close]
  have h := DataEq.subst₂ D rel ids (fun _ => (.const S.zero : Tm Head n))
  rwa [subst_ids] at h

/-- Instances of a term related to itself are related to its closure. -/
theorem DataEq.subst_close {D : Carrier .data} {n m : Nat} {t : Tm Head n}
    (rel : DataEq S D t t) (σ : Sub Head n m) :
    DataEq S D (close S (Presentation.subst σ t)) (close S t) := by
  have h := DataEq.subst₂ D rel
    (fun i => Presentation.subst (fun _ => (.const S.zero : Tm Head 0)) (σ i))
    (fun _ => (.const S.zero : Tm Head 0))
  simp only [close, subst_comp]
  exact h

/-! ## Values of data carriers -/

/-- The closed terms related to themselves at a data carrier. -/
def Realizer (D : Carrier .data) : Type := {t : Tm Head 0 // DataEq S D t t}

variable (S) in
/-- The values of a data carrier: its closed terms related to themselves, up to
the relation of the carrier. -/
def Q (D : Carrier .data) : Type :=
  Quot fun (a b : Realizer (S := S) D) => DataEq S D a.1 b.1

theorem Q.exact (laws : S.Laws) {D : Carrier .data} {a b : Realizer (S := S) D}
    (equal : (Quot.mk _ a : Q S D) = Quot.mk _ b) : DataEq S D a.1 b.1 := by
  have h := Quot.eqvGen_exact equal
  clear equal
  induction h with
  | rel _ _ h => exact h
  | refl a => exact a.2
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact DataEq.trans laws ih ih'

/-! ## Meanings -/

variable (S) in
/-- The meanings of a carrier, given the meanings `P` of codes: a value at a
data carrier; a meaning at `prop`, one point at a rigid type, and a function of
meanings at a function into a generic carrier. -/
@[reducible] def Carrier.Val (P : Type) : {k : Kind} → Carrier k → Type
  | _, .prop => P
  | _, .rigid _ => Unit
  | _, .num => Q S .num
  | _, @Carrier.arr _ .gen A B => Carrier.Val P A → Carrier.Val P B
  | _, @Carrier.arr _ .data A B => Q S (.arr A B)

variable {P : Type}

variable (S) in
/-- The value of a term related to itself at a data carrier: the class of its
closure. -/
def dataValue : (D : Carrier .data) → {n : Nat} → (t : Tm Head n) → DataEq S D t t →
    D.Val S P
  | .num, _, t, rel => Quot.mk _ ⟨close S t, rel.closure⟩
  | @Carrier.arr _ .data _ _, _, t, rel => Quot.mk _ ⟨close S t, rel.closure⟩

/-- Related terms have one value. -/
theorem dataValue_sound {D : Carrier .data} {n : Nat} {t t' : Tm Head n}
    (rel : DataEq S D t t) (rel' : DataEq S D t' t') (related : DataEq S D t t') :
    dataValue (P := P) S D t rel = dataValue S D t' rel' := by
  cases D with
  | num => exact Quot.sound related.closure
  | arr => exact Quot.sound related.closure

/-- Terms with one value are related. -/
theorem dataValue_exact (laws : S.Laws) {D : Carrier .data} {n : Nat} {t t' : Tm Head n}
    {rel : DataEq S D t t} {rel' : DataEq S D t' t'}
    (equal : dataValue (P := P) S D t rel = dataValue S D t' rel') : DataEq S D t t' := by
  have closed : DataEq S D (close S t) (close S t') := by
    cases D with
    | num => exact Q.exact laws equal
    | arr => exact Q.exact laws equal
  have h := DataEq.trans laws (DataEq.to_close rel)
    (DataEq.trans laws (closed.rename₂ Fin.elim0) (DataEq.to_close rel').symm)
  exact h

theorem dataValue_rename {D : Carrier .data} {n m : Nat} {t : Tm Head n}
    (rel : DataEq S D t t) (ρ : Ren n m) (rel' : DataEq S D (Presentation.rename ρ t)
      (Presentation.rename ρ t)) :
    dataValue (P := P) S D (Presentation.rename ρ t) rel' = dataValue S D t rel := by
  cases D with
  | num => exact congrArg (Quot.mk _) (Subtype.ext (close_rename ρ t))
  | arr => exact congrArg (Quot.mk _) (Subtype.ext (close_rename ρ t))

theorem dataValue_subst {D : Carrier .data} {n m : Nat} {t : Tm Head n}
    (rel : DataEq S D t t) (σ : Sub Head n m) (rel' : DataEq S D (Presentation.subst σ t)
      (Presentation.subst σ t)) :
    dataValue (P := P) S D (Presentation.subst σ t) rel' = dataValue S D t rel := by
  cases D with
  | num => exact Quot.sound (DataEq.subst_close rel σ)
  | arr => exact Quot.sound (DataEq.subst_close rel σ)

/-- The closure of a term related to itself has its value. -/
theorem dataValue_close {D : Carrier .data} {n : Nat} {t : Tm Head n}
    (rel : DataEq S D t t) (rel' : DataEq S D (close S t) (close S t)) :
    dataValue (P := P) S D (close S t) rel' = dataValue S D t rel := by
  cases D with
  | num => exact congrArg (Quot.mk _) (Subtype.ext (close_closed (close S t)))
  | arr => exact congrArg (Quot.mk _) (Subtype.ext (close_closed (close S t)))

/-- A closed term related to itself, as a term of any world, has its value. -/
theorem dataValue_liftClosed {D : Carrier .data} {n : Nat} {s : Tm Head 0}
    (related : DataEq S D s s) :
    dataValue (P := P) S D (liftClosed s : Tm Head n) (related.rename₂ Fin.elim0) =
      dataValue S D s related :=
  dataValue_rename related (Fin.elim0 : Ren 0 n) (related.rename₂ Fin.elim0)

/-- Every value of a data carrier is the value of a closed term. -/
theorem dataValue_surjective {D : Carrier .data} (v : D.Val S P) :
    ∃ (t : Tm Head 0) (rel : DataEq S D t t), dataValue S D t rel = v := by
  cases D with
  | num =>
      induction v using Quot.ind with
      | mk a => exact ⟨a.1, a.2, congrArg (Quot.mk _) (Subtype.ext (close_closed a.1))⟩
  | arr =>
      induction v using Quot.ind with
      | mk a => exact ⟨a.1, a.2, congrArg (Quot.mk _) (Subtype.ext (close_closed a.1))⟩

/-! ## Values of the numbers -/

theorem DataEq.zero {n : Nat} : DataEq S .num (.const S.zero : Tm Head n) (.const S.zero) :=
  S.base_zero

theorem DataEq.suc {n : Nat} {a b : Tm Head n} (related : DataEq S .num a b) :
    DataEq S .num (.app (.const S.suc) a) (.app (.const S.suc) b) :=
  S.base_suc related

/-- Every numeral is related to itself. -/
theorem DataEq.numeral {n : Nat} (k : Nat) :
    DataEq S .num (numeral S.toSetting k : Tm Head n) (numeral S.toSetting k) := by
  induction k with
  | zero => exact DataEq.zero
  | succ k ih => exact DataEq.suc ih

variable (S) in
/-- The value of a numeral. -/
def numClass (k : Nat) : Q S .num :=
  Quot.mk _ ⟨numeral S.toSetting k, DataEq.numeral k⟩

variable (S) in
/-- The successor of a value of the numbers: the class of the successor of a
representative. -/
def sucClass : Q S .num → Q S .num :=
  Quot.lift (fun a => Quot.mk _ ⟨.app (.const S.suc) a.1, DataEq.suc a.2⟩)
    (fun _ _ related => Quot.sound (DataEq.suc related))

theorem sucClass_numClass (k : Nat) : sucClass S (numClass S k) = numClass S (k + 1) := rfl

theorem dataValue_zero {n : Nat} (related : DataEq S .num (.const S.zero : Tm Head n)
    (.const S.zero)) :
    dataValue (P := P) S .num (.const S.zero : Tm Head n) related = numClass S 0 := rfl

theorem dataValue_suc {n : Nat} {s : Tm Head n} (related : DataEq S .num s s)
    (related' : DataEq S .num (.app (.const S.suc) s) (.app (.const S.suc) s)) :
    dataValue (P := P) S .num (.app (.const S.suc) s) related' =
      sucClass S (dataValue (P := P) S .num s related) :=
  rfl

/-- Numerals of different numbers have different values. -/
theorem numClass_injective (laws : S.Laws) {k k' : Nat}
    (equal : numClass S k = numClass S k') : k = k' := by
  exact laws.numeral_injective (Q.exact laws equal)

end Data

/-! ## Readings -/

/-- A reading of the codes: a data setting, a type `P` of meanings of codes
with the meanings of implication, of the quantifiers and of the equations, a
class of neutral codes with their meaning, and a meet of any family of
meanings with a greatest meaning. -/
structure Reading (Head : Type) extends DataSetting Head where
  P : Type
  impMeaning : P → P → P
  allMeaning : ∀ {k : Kind} (A : Carrier k), (Carrier.Val toDataSetting P A → P) → P
  eqMeaning : ∀ {k : Kind} (A : Carrier k), Carrier.Val toDataSetting P A →
    Carrier.Val toDataSetting P A → P
  neutral : ∀ {n : Nat}, Tm Head n → Prop
  neutral_subst : ∀ {n m : Nat} {s : Tm Head n} (σ : Sub Head n m), neutral s →
    neutral (Presentation.subst σ s)
  neutralMeaning : P
  meet : ∀ {ι : Type}, (ι → P) → P
  top : P

instance {Head : Type} : CoeOut (Reading Head) (DataSetting Head) := ⟨Reading.toDataSetting⟩

/-- The meanings of a carrier under a reading. -/
@[reducible] def Carrier.V {Head : Type} (S : Reading Head) {k : Kind} (A : Carrier k) : Type :=
  Carrier.Val S.toDataSetting S.P A

/-- The laws of a reading: those of its data setting; neutral codes are weak-head
normal and are neither codes nor generics applied to arguments; and the meet of
a nonempty family of one meaning is that meaning. -/
structure Reading.Laws {Head : Type} (S : Reading Head) : Prop
    extends toDataLaws : DataSetting.Laws S.toDataSetting where
  neutral_whnf : ∀ {n : Nat} {s : Tm Head n}, S.neutral s → Whnf S.rules S.roles s
  neutral_ne_imp : ∀ {n : Nat} {s p q : Tm Head n}, S.neutral s →
    s ≠ .app (.app (.const S.imp) p) q
  neutral_ne_all : ∀ {n : Nat} {s f : Tm Head n} {a : DeclName} {A : Σ k, Carrier k},
    S.neutral s → S.allCarrier a = some A → s ≠ .app (.const a) f
  neutral_ne_eq : ∀ {n : Nat} {s x y : Tm Head n} {e : DeclName} {A : Σ k, Carrier k},
    S.neutral s → S.eqCarrier e = some A → s ≠ .app (.app (.const e) x) y
  neutral_ne_var : ∀ {n : Nat} {s : Tm Head n} {i : Fin n} {args : List (Tm Head n)},
    S.neutral s → s ≠ appSpine (.var i) args
  meet_const : ∀ {ι : Type} (f : ι → S.P) (x : S.P), (∀ i, f i = x) → Nonempty ι →
    S.meet f = x

theorem Reading.neutral_rename {Head : Type} (S : Reading Head) {n m : Nat} {s : Tm Head n}
    (ρ : Ren n m) (neutral : S.neutral s) : S.neutral (Presentation.rename ρ s) := by
  have h := S.neutral_subst (renSub ρ) neutral
  rwa [subst_renSub] at h

section Worlds

variable {Head : Type} {S : Reading Head}

/-! ## Worlds -/

variable (S) in
/-- A generic: a generic carrier and a meaning in it. -/
abbrev Gen := Σ A : Carrier .gen, A.V S

variable (S) in
/-- A world gives each free variable of its terms a generic. -/
abbrev World (n : Nat) := Fin n → Gen S

/-- A world extended by a newest generic, which is variable `0`. -/
def World.snoc {n : Nat} (ξ : World S n) (g : Gen S) : World S (n + 1) :=
  Fin.cases g ξ

@[simp] theorem World.snoc_zero {n : Nat} (ξ : World S n) (g : Gen S) : ξ.snoc g 0 = g := rfl

@[simp] theorem World.snoc_succ {n : Nat} (ξ : World S n) (g : Gen S) (i : Fin n) :
    ξ.snoc g i.succ = ξ i := rfl

/-- The world without generics. -/
def World.closed : World S 0 := fun i => Fin.elim0 i

/-- A renaming between worlds that keeps every generic. -/
def Morph {n m : Nat} (ξ : World S n) (ξ' : World S m) (ρ : Ren n m) : Prop :=
  ∀ i, ξ' (ρ i) = ξ i

theorem Morph.id {n : Nat} (ξ : World S n) : Morph ξ ξ idRen := fun _ => rfl

theorem Morph.comp {n m k : Nat} {ξ : World S n} {ξ' : World S m} {ξ'' : World S k}
    {ρ : Ren n m} {ρ' : Ren m k} (first : Morph ξ ξ' ρ) (second : Morph ξ' ξ'' ρ') :
    Morph ξ ξ'' (ρ' ∘ ρ) := fun i => (second (ρ i)).trans (first i)

theorem Morph.comp' {n m k : Nat} {ξ : World S n} {ξ' : World S m} {ξ'' : World S k}
    {ρ : Ren n m} {ρ' : Ren m k} (first : Morph ξ ξ' ρ) (second : Morph ξ' ξ'' ρ') :
    Morph ξ ξ'' (fun i => ρ' (ρ i)) := fun i => (second (ρ i)).trans (first i)

theorem Morph.wk {n : Nat} (ξ : World S n) (g : Gen S) : Morph ξ (ξ.snoc g) wk := fun _ => rfl

theorem Morph.lift {n m : Nat} {ξ : World S n} {ξ' : World S m} {ρ : Ren n m}
    (morph : Morph ξ ξ' ρ) (g : Gen S) : Morph (ξ.snoc g) (ξ'.snoc g) (liftRen ρ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact morph j

/-- Two worlds side by side. -/
def World.append {n m : Nat} (ξ : World S n) (ξ' : World S m) : World S (n + m) :=
  Fin.append ξ ξ'

theorem Morph.castAdd {n m : Nat} (ξ : World S n) (ξ' : World S m) :
    Morph ξ (ξ.append ξ') (Fin.castAdd m) :=
  fun i => Fin.append_left ξ ξ' i

theorem Morph.natAdd {n m : Nat} (ξ : World S n) (ξ' : World S m) :
    Morph ξ' (ξ.append ξ') (Fin.natAdd n) :=
  fun j => Fin.append_right ξ ξ' j

end Worlds

/-! ## Truth values as meanings -/

section Truth

variable {Head : Type} (S : Setting Head)

/-- The numerals as the relation of the numbers: terms with a common
numeral. -/
def Setting.numerals : DataSetting Head where
  toSetting := S
  base := fun t t' => ∃ k, NumVal S t k ∧ NumVal S t' k
  base_subst₂ := fun σ σ' ⟨k, v, v'⟩ => ⟨k, v.subst σ, v'.subst σ'⟩
  base_symm := fun ⟨k, v, v'⟩ => ⟨k, v', v⟩
  base_expand := fun red red' ⟨k, v, v'⟩ => ⟨k, v.expand red, v'.expand red'⟩
  base_zero := ⟨0, .zero .refl, .zero .refl⟩
  base_suc := fun ⟨k, v, v'⟩ => ⟨k + 1, .suc .refl v, .suc .refl v'⟩

/-- The reading of codes by truth values: implication, quantification and
equality of Lean propositions, and no neutral codes. -/
def Setting.truthReading : Reading Head where
  toDataSetting := S.numerals
  P := Prop
  impMeaning := fun P Q => P → Q
  allMeaning := fun _ φ => ∀ v, φ v
  eqMeaning := fun _ v w => v = w
  neutral := fun _ => False
  neutral_subst := fun _ neutral => neutral
  neutralMeaning := False
  meet := fun f => ∀ i, f i
  top := True

variable {S}

theorem Setting.Laws.numerals (laws : S.Laws) : S.numerals.Laws where
  toLaws := laws
  base_trans := fun ⟨k, v, v'⟩ ⟨_, w, w'⟩ => by
    obtain rfl := NumVal.deterministic laws v' w
    exact ⟨k, v, w'⟩
  numeral_injective := fun ⟨_, first, second⟩ =>
    (NumVal.deterministic laws (numVal_numeral _) first).trans
      (NumVal.deterministic laws second (numVal_numeral _))

theorem Setting.Laws.truthReading (laws : S.Laws) : S.truthReading.Laws where
  toDataLaws := laws.numerals
  neutral_whnf := fun neutral => neutral.elim
  neutral_ne_imp := fun neutral => neutral.elim
  neutral_ne_all := fun neutral => neutral.elim
  neutral_ne_eq := fun neutral => neutral.elim
  neutral_ne_var := fun neutral => neutral.elim
  meet_const := fun _ _ all ⟨i⟩ =>
    propext ⟨fun h => (all i).mp (h i), fun hx j => (all j).mpr hx⟩

end Truth

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
