import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Tower
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

/-!
# Coherence of silent conversions: the condition, its converse, and which conversions may be silent

**A language over a tower of numeric types** (`Language`): types ordered by inclusion (a join
semilattice), a carrier for each type, a **silent conversion** along each inclusion, and generic
operations and tests, each defined at some of the types with a meaning at each. **Expressions**
(`Expr`, `Test`) carry no conversion; an **elaboration** (`Elab`, `ElabTest`) is a fully annotated
term: each operation at one type, and every silent conversion made explicit (`Elab.up`). Its value is
computed from the annotations (`Elab.eval`).

**Coherence** (`Coherent`): all elaborations of one expression at one type have one value, and all
elaborations of one test one truth value. The theorem (`coherent_iff`), for a language whose
operations and tests are each defined on a set of types closed under joins (`DomainsJoin`):

  coherent ⇔ the conversions compose (`Functorial`) ∧ every operation commutes with every conversion
  between types where it is defined (`OpsCommute`) ∧ so does every test (`RelsCommute`).

The forward direction peels the conversions off an elaboration (`peel`) and compares two
elaborations at the join of their types (`agree`). **The converse is in general form**: a conversion
that is not the identity along `a ≤ a`, two conversions that do not compose, an operation that fails
to commute with one conversion, or a test that does, each gives an expression or a test with two
elaborations of different value (`refl_needed`, `trans_needed`, `commute_needed`, `relCommute_needed`).

**Which conversions may be silent** (`eq_commutes_iff_injective`): with an equality test in scope at
every type, it commutes with the conversions exactly when every conversion is injective. So in a
language with equality the criterion is: the conversions compose and are **injective homomorphisms**
of the operations and tests in scope (`criterion`).

**The tower** (`Level`, `tower`): the naturals, the whole numbers and the rationals with their casts
as conversions, addition and multiplication at every level, subtraction at the whole numbers and the
rationals, exact division at the rationals, the named quotient and remainder at the naturals and the
whole numbers, and the tests `==` and `<=` everywhere. **It is coherent** (`named_coherent`).
Division at the rationals is Lean's total division; division by zero is not modelled here.

**Controls.** Allowing truncated subtraction at the naturals breaks coherence: `1 - 2` at the whole
numbers has the elaborations `0` and `-1` (`truncated_two_values`, `truncated_incoherent`).
Allowing the storage-dependent division (truncating at the whole numbers, exact at the rationals)
breaks it: `5 / 2` at the rationals has the elaborations `2` and `5/2` (`storageDiv_two_values`,
`storageDiv_incoherent`).

**Rounding, in general form.** For every finite set of rationals (the representable values):

* no conversion from the whole numbers into it is injective (`rounding_not_injective`), so with `==`
  in scope it cannot be silent: two different whole numbers become equal (`rounding_merges`);
* an addition on it that commutes with the inclusion into the rationals makes it closed under
  addition (`closed_of_commutes`), which no finite set with a nonzero element is
  (`finite_not_closed`); so no addition on it commutes with the inclusion
  (`no_commuting_addition`).

So a type of finitely many representable values (floating point, for instance) is a separate type:
its conversion from the whole numbers is named and lossy, and its operations are specified by an
error bound rather than an equation. A nearest rounding exists onto every nonempty finite set
(`exists_nearest`, `exists_rounding`), and with it the rounded sum equals the exact sum exactly when
the exact sum is representable (`roundedAdd_exact_iff`); elsewhere only the distance to the nearest
representable value bounds the error. No floating-point arithmetic is modelled.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Coherence

/-! ## The language -/

/-- **A language over a tower of numeric types.** -/
structure Language (Ty : Type) [SemilatticeSup Ty] where
  /-- The numbers of each type. -/
  D : Ty → Type
  /-- The silent conversion along each inclusion of types. -/
  conv : ∀ {a b : Ty}, a ≤ b → D a → D b
  /-- The operation names. -/
  Op : Type
  /-- Where an operation is defined. -/
  opAt : Op → Ty → Prop
  /-- Its meaning at each type (used only where it is defined). -/
  op : (o : Op) → (a : Ty) → D a → D a → D a
  /-- The test names. -/
  Rel : Type
  /-- Where a test is defined. -/
  relAt : Rel → Ty → Prop
  /-- Its meaning at each type. -/
  rel : (r : Rel) → (a : Ty) → D a → D a → Bool

namespace Language

variable {Ty : Type} [SemilatticeSup Ty] (L : Language Ty)

/-- **Expressions**: literals carrying their type, and operations on two expressions. No conversion
is written. -/
inductive Expr : Type
  | lit (a : Ty) (v : L.D a)
  | app (o : L.Op) (left right : Expr)

/-- **Tests** of two expressions. -/
inductive Test : Type
  | rel (r : L.Rel) (left right : L.Expr)

/-- **Elaborations**: every operation at one type, every silent conversion explicit. -/
inductive Elab : L.Expr → Ty → Type
  | lit (a : Ty) (v : L.D a) : Elab (.lit a v) a
  | app (o : L.Op) (a : Ty) (defined : L.opAt o a) {left right : L.Expr} :
      Elab left a → Elab right a → Elab (.app o left right) a
  | up {e : L.Expr} {a b : Ty} (le : a ≤ b) : Elab e a → Elab e b

/-- **Elaborations of a test**: the test at one type where it is defined. -/
inductive ElabTest : L.Test → Type
  | rel (r : L.Rel) (a : Ty) (defined : L.relAt r a) {left right : L.Expr} :
      L.Elab left a → L.Elab right a → ElabTest (.rel r left right)

/-- An elaboration that does not end in a conversion. -/
inductive Head : L.Expr → Ty → Type
  | lit (a : Ty) (v : L.D a) : Head (.lit a v) a
  | app (o : L.Op) (a : Ty) (defined : L.opAt o a) {left right : L.Expr} :
      L.Elab left a → L.Elab right a → Head (.app o left right) a

variable {L}

/-- **The value of an elaboration.** -/
def Elab.eval : {e : L.Expr} → {a : Ty} → L.Elab e a → L.D a
  | _, _, .lit _ v => v
  | _, _, .app o a _ left right => L.op o a left.eval right.eval
  | _, _, .up le d => L.conv le d.eval

/-- The truth value of an elaborated test. -/
def ElabTest.eval : {t : L.Test} → L.ElabTest t → Bool
  | _, .rel r a _ left right => L.rel r a left.eval right.eval

/-- The value of a head. -/
def Head.eval : {e : L.Expr} → {a : Ty} → L.Head e a → L.D a
  | _, _, .lit _ v => v
  | _, _, .app o a _ left right => L.op o a left.eval right.eval

variable (L)

/-- **Coherence**: all elaborations of one expression at one type have one value, and all
elaborations of one test have one truth value. -/
def Coherent : Prop :=
  (∀ (e : L.Expr) (a : Ty) (d d' : L.Elab e a), d.eval = d'.eval) ∧
    ∀ (t : L.Test) (d d' : L.ElabTest t), d.eval = d'.eval

/-- **The conversions compose**: along `a ≤ a` the identity, and two conversions are one. -/
def Functorial : Prop :=
  (∀ (a : Ty) (h : a ≤ a) (x : L.D a), L.conv h x = x) ∧
    ∀ (a b c : Ty) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : a ≤ c) (x : L.D a),
      L.conv h₂ (L.conv h₁ x) = L.conv h₃ x

/-- **Every operation commutes with every conversion** between types where it is defined. -/
def OpsCommute : Prop :=
  ∀ (o : L.Op) (a b : Ty) (h : a ≤ b), L.opAt o a → L.opAt o b → ∀ x y : L.D a,
    L.conv h (L.op o a x y) = L.op o b (L.conv h x) (L.conv h y)

/-- **Every test commutes with every conversion** between types where it is defined. -/
def RelsCommute : Prop :=
  ∀ (r : L.Rel) (a b : Ty) (h : a ≤ b), L.relAt r a → L.relAt r b → ∀ x y : L.D a,
    L.rel r a x y = L.rel r b (L.conv h x) (L.conv h y)

/-- **The types of each operation and test are closed under joins.** -/
def DomainsJoin : Prop :=
  (∀ (o : L.Op) (a b : Ty), L.opAt o a → L.opAt o b → L.opAt o (a ⊔ b)) ∧
    ∀ (r : L.Rel) (a b : Ty), L.relAt r a → L.relAt r b → L.relAt r (a ⊔ b)

/-! ## Coherence from commuting -/

/-- **Peeling the conversions**: every elaboration is a head at a smaller type, converted. -/
theorem peel (functorial : L.Functorial) {e : L.Expr} {a : Ty} (d : L.Elab e a) :
    ∃ (a₀ : Ty) (le : a₀ ≤ a) (h : L.Head e a₀), d.eval = L.conv le h.eval := by
  induction d with
  | lit a v => exact ⟨a, le_refl a, .lit a v, (functorial.1 a _ v).symm⟩
  | app o a defined left right _ _ =>
      exact ⟨a, le_refl a, .app o a defined left right, (functorial.1 a _ _).symm⟩
  | up le d ih =>
      obtain ⟨a₀, le₀, h, equal⟩ := ih
      refine ⟨a₀, le₀.trans le, h, ?_⟩
      show L.conv le d.eval = _
      rw [equal, functorial.2 _ _ _ le₀ le (le₀.trans le)]

theorem peel_lit (functorial : L.Functorial) {a₁ a : Ty} {v : L.D a₁} (d : L.Elab (.lit a₁ v) a) :
    ∃ le : a₁ ≤ a, d.eval = L.conv le v := by
  obtain ⟨a₀, le, h, equal⟩ := L.peel functorial d
  cases h with
  | lit _ _ => exact ⟨le, equal⟩

theorem peel_app (functorial : L.Functorial) {o : L.Op} {left right : L.Expr} {a : Ty}
    (d : L.Elab (.app o left right) a) :
    ∃ (a₀ : Ty) (le : a₀ ≤ a) (_ : L.opAt o a₀) (dl : L.Elab left a₀) (dr : L.Elab right a₀),
      d.eval = L.conv le (L.op o a₀ dl.eval dr.eval) := by
  obtain ⟨a₀, le, h, equal⟩ := L.peel functorial d
  cases h with
  | app _ _ defined dl dr => exact ⟨_, le, defined, dl, dr, equal⟩

/-- **Two elaborations agree at every common upper type.** -/
theorem agree (functorial : L.Functorial) (commute : L.OpsCommute) (joins : L.DomainsJoin) :
    ∀ (e : L.Expr) {a b c : Ty} (d : L.Elab e a) (d' : L.Elab e b) (ha : a ≤ c) (hb : b ≤ c),
      L.conv ha d.eval = L.conv hb d'.eval := by
  intro e
  induction e with
  | lit a₁ v =>
      intro a b c d d' ha hb
      obtain ⟨le, equal⟩ := L.peel_lit functorial d
      obtain ⟨le', equal'⟩ := L.peel_lit functorial d'
      rw [equal, equal', functorial.2 _ _ _ le ha (le.trans ha),
        functorial.2 _ _ _ le' hb (le'.trans hb)]
  | app o left right ihl ihr =>
      intro a b c d d' ha hb
      obtain ⟨a₀, le, defined, dl, dr, equal⟩ := L.peel_app functorial d
      obtain ⟨b₀, le', defined', dl', dr', equal'⟩ := L.peel_app functorial d'
      have hm : a₀ ⊔ b₀ ≤ c := sup_le (le.trans ha) (le'.trans hb)
      have la : a₀ ≤ a₀ ⊔ b₀ := le_sup_left
      have lb : b₀ ≤ a₀ ⊔ b₀ := le_sup_right
      have definedJoin : L.opAt o (a₀ ⊔ b₀) := joins.1 o a₀ b₀ defined defined'
      have leftAgree : L.conv la dl.eval = L.conv lb dl'.eval := ihl dl dl' la lb
      have rightAgree : L.conv la dr.eval = L.conv lb dr'.eval := ihr dr dr' la lb
      rw [equal, equal', functorial.2 _ _ _ le ha (le.trans ha),
        functorial.2 _ _ _ le' hb (le'.trans hb), ← functorial.2 _ _ _ la hm (le.trans ha),
        ← functorial.2 _ _ _ lb hm (le'.trans hb), commute o a₀ _ la defined definedJoin,
        commute o b₀ _ lb defined' definedJoin, leftAgree, rightAgree]

/-- **Coherence from commuting.** -/
theorem coherent_of (functorial : L.Functorial) (commute : L.OpsCommute)
    (relsCommute : L.RelsCommute) (joins : L.DomainsJoin) : L.Coherent := by
  refine ⟨fun e a d d' => ?_, fun t d d' => ?_⟩
  · have both := L.agree functorial commute joins e d d' (le_refl a) (le_refl a)
    rwa [functorial.1, functorial.1] at both
  · cases d with
    | rel r a defined dl dr =>
      cases d' with
      | rel _ b defined' dl' dr' =>
        have la : a ≤ a ⊔ b := le_sup_left
        have lb : b ≤ a ⊔ b := le_sup_right
        have definedJoin : L.relAt r (a ⊔ b) := joins.2 r a b defined defined'
        show L.rel r a dl.eval dr.eval = L.rel r b dl'.eval dr'.eval
        rw [relsCommute r a _ la defined definedJoin, relsCommute r b _ lb defined' definedJoin,
          L.agree functorial commute joins _ dl dl' la lb,
          L.agree functorial commute joins _ dr dr' la lb]

/-! ## The converse, in general form -/

/-- A conversion that is not the identity along `a ≤ a` gives a literal two values. -/
theorem refl_needed {a : Ty} (h : a ≤ a) {x : L.D a} (differ : L.conv h x ≠ x) :
    ∃ (e : L.Expr) (d d' : L.Elab e a), d.eval ≠ d'.eval :=
  ⟨.lit a x, .up h (.lit a x), .lit a x, differ⟩

/-- Two conversions that are not one give a literal two values. -/
theorem trans_needed {a b c : Ty} (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : a ≤ c) {x : L.D a}
    (differ : L.conv h₂ (L.conv h₁ x) ≠ L.conv h₃ x) :
    ∃ (e : L.Expr) (d d' : L.Elab e c), d.eval ≠ d'.eval :=
  ⟨.lit a x, .up h₂ (.up h₁ (.lit a x)), .up h₃ (.lit a x), differ⟩

/-- **The converse**: an operation that fails to commute with one conversion gives an expression
with two elaborations of different value: the operation before the conversion, and after it. -/
theorem commute_needed {o : L.Op} {a b : Ty} (h : a ≤ b) (da : L.opAt o a) (db : L.opAt o b)
    {x y : L.D a} (differ : L.conv h (L.op o a x y) ≠ L.op o b (L.conv h x) (L.conv h y)) :
    ∃ (e : L.Expr) (d d' : L.Elab e b), d.eval ≠ d'.eval :=
  ⟨.app o (.lit a x) (.lit a y), .up h (.app o a da (.lit a x) (.lit a y)),
    .app o b db (.up h (.lit a x)) (.up h (.lit a y)), differ⟩

/-- A test that fails to commute with one conversion gives a test with two elaborations of
different truth value. -/
theorem relCommute_needed {r : L.Rel} {a b : Ty} (h : a ≤ b) (da : L.relAt r a)
    (db : L.relAt r b) {x y : L.D a} (differ : L.rel r a x y ≠ L.rel r b (L.conv h x) (L.conv h y)) :
    ∃ (t : L.Test) (d d' : L.ElabTest t), d.eval ≠ d'.eval :=
  ⟨.rel r (.lit a x) (.lit a y), .rel r a da (.lit a x) (.lit a y),
    .rel r b db (.up h (.lit a x)) (.up h (.lit a y)), differ⟩

/-- **Coherence is exactly commuting**: for a language whose operations and tests are defined on
types closed under joins, all elaborations agree exactly when the conversions compose and every
operation and test commutes with every conversion. -/
theorem coherent_iff (joins : L.DomainsJoin) :
    L.Coherent ↔ L.Functorial ∧ L.OpsCommute ∧ L.RelsCommute := by
  constructor
  · intro coherent
    refine ⟨⟨fun a h x => ?_, fun a b c h₁ h₂ h₃ x => ?_⟩, fun o a b h da db x y => ?_,
      fun r a b h da db x y => ?_⟩
    · exact coherent.1 _ _ (.up h (.lit a x)) (.lit a x)
    · exact coherent.1 _ _ (.up h₂ (.up h₁ (.lit a x))) (.up h₃ (.lit a x))
    · exact coherent.1 _ _ (.up h (.app o a da (.lit a x) (.lit a y)))
        (.app o b db (.up h (.lit a x)) (.up h (.lit a y)))
    · exact coherent.2 _ (.rel r a da (.lit a x) (.lit a y))
        (.rel r b db (.up h (.lit a x)) (.up h (.lit a y)))
  · rintro ⟨functorial, commute, relsCommute⟩
    exact L.coherent_of functorial commute relsCommute joins

/-- In a linear order of types, every set of types is closed under joins. -/
theorem domainsJoin_of_linear {T : Type} [LinearOrder T] (M : Language T) : M.DomainsJoin := by
  refine ⟨fun o a b da db => ?_, fun r a b da db => ?_⟩
  · rcases le_total a b with le | le
    · rw [sup_eq_right.mpr le]
      exact db
    · rw [sup_eq_left.mpr le]
      exact da
  · rcases le_total a b with le | le
    · rw [sup_eq_right.mpr le]
      exact db
    · rw [sup_eq_left.mpr le]
      exact da

/-! ## Which conversions may be silent -/

/-- **With an equality test everywhere, it commutes with the conversions exactly when every
conversion is injective.** -/
theorem eq_commutes_iff_injective (eqRel : L.Rel)
    (isEq : ∀ (a : Ty) (x y : L.D a), L.rel eqRel a x y = true ↔ x = y) :
    (∀ (a b : Ty) (h : a ≤ b) (x y : L.D a),
        L.rel eqRel a x y = L.rel eqRel b (L.conv h x) (L.conv h y)) ↔
      ∀ (a b : Ty) (h : a ≤ b), Function.Injective (L.conv h) := by
  constructor
  · intro commutes a b h x y equal
    have converted : L.rel eqRel b (L.conv h x) (L.conv h y) = true := (isEq b _ _).mpr equal
    rw [← commutes a b h x y] at converted
    exact (isEq a x y).mp converted
  · intro injective a b h x y
    rw [Bool.eq_iff_iff, isEq, isEq]
    exact ⟨fun equal => congrArg _ equal, fun equal => injective a b h equal⟩

/-- **The criterion**: in a language with an equality test everywhere, coherence holds exactly when
the conversions compose, are injective, and commute with every operation and every other test. -/
theorem criterion (joins : L.DomainsJoin) (eqRel : L.Rel) (everywhere : ∀ a, L.relAt eqRel a)
    (isEq : ∀ (a : Ty) (x y : L.D a), L.rel eqRel a x y = true ↔ x = y) :
    L.Coherent ↔ L.Functorial ∧ (∀ (a b : Ty) (h : a ≤ b), Function.Injective (L.conv h)) ∧
      L.OpsCommute ∧
      ∀ (r : L.Rel), r ≠ eqRel → ∀ (a b : Ty) (h : a ≤ b), L.relAt r a → L.relAt r b →
        ∀ x y : L.D a, L.rel r a x y = L.rel r b (L.conv h x) (L.conv h y) := by
  rw [L.coherent_iff joins]
  constructor
  · rintro ⟨functorial, commute, relsCommute⟩
    refine ⟨functorial, (L.eq_commutes_iff_injective eqRel isEq).mp fun a b h =>
      relsCommute eqRel a b h (everywhere a) (everywhere b), commute,
      fun r _ => relsCommute r⟩
  · rintro ⟨functorial, injective, commute, others⟩
    refine ⟨functorial, commute, fun r a b h da db x y => ?_⟩
    by_cases isEqRel : r = eqRel
    · subst isEqRel
      exact (L.eq_commutes_iff_injective r isEq).mpr injective a b h x y
    · exact others r isEqRel a b h da db x y

end Language

/-! ## The tower: naturals, whole numbers, rationals -/

/-- **The levels of the tower.** -/
inductive Level
  | nat
  | int
  | rat
  deriving DecidableEq

/-- The rank of a level. -/
def Level.rank : Level → ℕ
  | .nat => 0
  | .int => 1
  | .rat => 2

theorem Level.rank_injective : Function.Injective Level.rank := by
  intro a b equal
  cases a <;> cases b <;> first | rfl | exact absurd equal (by decide)

instance : LinearOrder Level := LinearOrder.lift' Level.rank Level.rank_injective

/-- The numbers of each level. -/
abbrev Carrier : Level → Type
  | .nat => ℕ
  | .int => ℤ
  | .rat => ℚ

/-- **The silent conversions are the casts.** -/
def cast : (a b : Level) → a ≤ b → Carrier a → Carrier b
  | .nat, .nat, _ => fun n => n
  | .nat, .int, _ => fun (n : ℕ) => (n : ℤ)
  | .nat, .rat, _ => fun (n : ℕ) => (n : ℚ)
  | .int, .int, _ => fun z => z
  | .int, .rat, _ => fun (z : ℤ) => (z : ℚ)
  | .rat, .rat, _ => fun q => q
  | .int, .nat, h => absurd h (by decide)
  | .rat, .nat, h => absurd h (by decide)
  | .rat, .int, h => absurd h (by decide)

/-- The operations of the tower. -/
inductive TowerOp
  | add
  | sub
  | mul
  | div
  | quot
  | rem

/-- The tests of the tower. -/
inductive TowerRel
  | eq
  | le

/-- Where each operation is defined: subtraction at the naturals only if `subNat`, division at the
whole numbers and the naturals only if `divWhole`; the quotient and the remainder at the naturals and
the whole numbers. -/
def towerAt (subNat divWhole : Bool) : TowerOp → Level → Prop
  | .add, _ => True
  | .mul, _ => True
  | .sub, .nat => subNat = true
  | .sub, _ => True
  | .div, .rat => True
  | .div, _ => divWhole = true
  | .quot, .rat => False
  | .quot, _ => True
  | .rem, .rat => False
  | .rem, _ => True

/-- The meaning of each operation at each level. Subtraction at the naturals is truncated; division
at the naturals and the whole numbers truncates toward zero; at the rationals it is exact. The
quotient and the remainder are not defined at the rationals; their meaning there is never used. -/
def towerOp : TowerOp → (a : Level) → Carrier a → Carrier a → Carrier a
  | .add, .nat => fun (x y : ℕ) => x + y
  | .add, .int => fun (x y : ℤ) => x + y
  | .add, .rat => fun (x y : ℚ) => x + y
  | .sub, .nat => fun (x y : ℕ) => x - y
  | .sub, .int => fun (x y : ℤ) => x - y
  | .sub, .rat => fun (x y : ℚ) => x - y
  | .mul, .nat => fun (x y : ℕ) => x * y
  | .mul, .int => fun (x y : ℤ) => x * y
  | .mul, .rat => fun (x y : ℚ) => x * y
  | .div, .nat => fun (x y : ℕ) => x / y
  | .div, .int => fun (x y : ℤ) => Int.tdiv x y
  | .div, .rat => fun (x y : ℚ) => x / y
  | .quot, .nat => fun (x y : ℕ) => x / y
  | .quot, .int => fun (x y : ℤ) => Int.tdiv x y
  | .quot, .rat => fun (x _ : ℚ) => x
  | .rem, .nat => fun (x y : ℕ) => x % y
  | .rem, .int => fun (x y : ℤ) => Int.tmod x y
  | .rem, .rat => fun (x _ : ℚ) => x

/-- The meaning of each test at each level. -/
def towerRel : TowerRel → (a : Level) → Carrier a → Carrier a → Bool
  | .eq, .nat => fun (x y : ℕ) => decide (x = y)
  | .eq, .int => fun (x y : ℤ) => decide (x = y)
  | .eq, .rat => fun (x y : ℚ) => decide (x = y)
  | .le, .nat => fun (x y : ℕ) => decide (x ≤ y)
  | .le, .int => fun (x y : ℤ) => decide (x ≤ y)
  | .le, .rat => fun (x y : ℚ) => decide (x ≤ y)

/-- **The tower as a language.** -/
def tower (subNat divWhole : Bool) : Language Level where
  D := Carrier
  conv := fun {a b} h => cast a b h
  Op := TowerOp
  opAt := towerAt subNat divWhole
  op := towerOp
  Rel := TowerRel
  relAt := fun _ _ => True
  rel := towerRel

/-- **The named tower**: exact division only at the rationals, the quotient named. -/
abbrev named : Language Level := tower false false

theorem cast_refl (a : Level) (h : a ≤ a) (x : Carrier a) : cast a a h x = x := by
  cases a <;> rfl

theorem cast_trans (a b c : Level) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : a ≤ c) (x : Carrier a) :
    cast b c h₂ (cast a b h₁ x) = cast a c h₃ x := by
  cases a <;> cases b <;> cases c <;>
    first
    | rfl
    | exact absurd h₁ (by decide)
    | exact absurd h₂ (by decide)

theorem towerRel_commutes (r : TowerRel) (a b : Level) (h : a ≤ b) (x y : Carrier a) :
    towerRel r a x y = towerRel r b (cast a b h x) (cast a b h y) := by
  cases r <;> cases a <;> cases b <;>
    first
    | exact absurd h (by decide)
    | rfl
    | simp [towerRel, cast]

theorem towerRel_eq_iff (a : Level) (x y : Carrier a) : towerRel TowerRel.eq a x y = true ↔ x = y := by
  cases a <;> simp [towerRel]

theorem towerOp_commutes (o : TowerOp) (a b : Level) (h : a ≤ b) (da : towerAt false false o a)
    (db : towerAt false false o b) (x y : Carrier a) :
    cast a b h (towerOp o a x y) = towerOp o b (cast a b h x) (cast a b h y) := by
  cases o <;> cases a <;> cases b <;>
    first
    | exact absurd h (by decide)
    | exact False.elim da
    | exact False.elim db
    | exact (Bool.false_ne_true da).elim
    | rfl
    | simp [towerOp, cast]

theorem tower_functorial (subNat divWhole : Bool) : (tower subNat divWhole).Functorial :=
  ⟨cast_refl, cast_trans⟩

theorem tower_relsCommute (subNat divWhole : Bool) : (tower subNat divWhole).RelsCommute :=
  fun r a b h _ _ x y => towerRel_commutes r a b h x y

theorem named_opsCommute : named.OpsCommute :=
  fun o a b h da db x y => towerOp_commutes o a b h da db x y

/-- **The named tower is coherent.** -/
theorem named_coherent : named.Coherent :=
  (named.coherent_iff (Language.domainsJoin_of_linear named)).mpr
    ⟨tower_functorial false false, named_opsCommute, tower_relsCommute false false⟩

/-- **Its conversions are injective**, as the criterion requires with `==` in scope. -/
theorem named_injective : ∀ (a b : Level) (h : a ≤ b), Function.Injective (named.conv h) :=
  ((named.criterion (Language.domainsJoin_of_linear named) TowerRel.eq (fun _ => trivial)
    towerRel_eq_iff).mp named_coherent).2.1

/-! ## Controls -/

theorem nat_le_int : Level.nat ≤ Level.int := by decide

theorem int_le_rat : Level.int ≤ Level.rat := by decide

/-- `1 - 2` over the naturals. -/
def oneMinusTwo (subNat divWhole : Bool) : (tower subNat divWhole).Expr :=
  .app TowerOp.sub (.lit Level.nat (1 : ℕ)) (.lit Level.nat (2 : ℕ))

/-- The literal `n` at the naturals. -/
def natLit (subNat divWhole : Bool) (n : ℕ) :
    (tower subNat divWhole).Elab (.lit Level.nat (n : ℕ)) Level.nat :=
  Language.Elab.lit (L := tower subNat divWhole) Level.nat (n : ℕ)

/-- The literal `z` at the whole numbers. -/
def intLit (subNat divWhole : Bool) (z : ℤ) :
    (tower subNat divWhole).Elab (.lit Level.int (z : ℤ)) Level.int :=
  Language.Elab.lit (L := tower subNat divWhole) Level.int (z : ℤ)

/-- `1 - 2` at the naturals, then converted. -/
def truncatedFirst : (tower true false).Elab (oneMinusTwo true false) Level.int :=
  Language.Elab.up (L := tower true false) nat_le_int
    (Language.Elab.app (L := tower true false) TowerOp.sub Level.nat rfl
      (natLit true false 1) (natLit true false 2))

/-- `1` and `2` converted, then subtracted at the whole numbers. -/
def truncatedLater : (tower true false).Elab (oneMinusTwo true false) Level.int :=
  Language.Elab.app (L := tower true false) TowerOp.sub Level.int trivial
    (Language.Elab.up (L := tower true false) nat_le_int (natLit true false 1))
    (Language.Elab.up (L := tower true false) nat_le_int (natLit true false 2))

theorem truncatedFirst_eval : truncatedFirst.eval = (0 : ℤ) := by
  show (((1 - 2 : ℕ) : ℤ)) = 0
  norm_num

theorem truncatedLater_eval : truncatedLater.eval = (-1 : ℤ) := by
  show ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) = -1
  norm_num

/-- **Truncated subtraction at the naturals: `1 - 2` at the whole numbers is `0` or `-1`.** -/
theorem truncated_two_values :
    ∃ d d' : (tower true false).Elab (oneMinusTwo true false) Level.int,
      d.eval = (0 : ℤ) ∧ d'.eval = (-1 : ℤ) :=
  ⟨truncatedFirst, truncatedLater, truncatedFirst_eval, truncatedLater_eval⟩

theorem truncated_incoherent : ¬ (tower true false).Coherent := by
  intro coherent
  have same : truncatedFirst.eval = truncatedLater.eval := coherent.1 _ _ _ _
  have differ : (0 : ℤ) ≠ -1 := by decide
  exact differ (truncatedFirst_eval.symm.trans (same.trans truncatedLater_eval))

/-- `5 / 2` over the whole numbers. -/
def fiveByTwo (subNat divWhole : Bool) : (tower subNat divWhole).Expr :=
  .app TowerOp.div (.lit Level.int (5 : ℤ)) (.lit Level.int (2 : ℤ))

/-- `5 / 2` at the whole numbers, then converted. -/
def divisionFirst : (tower false true).Elab (fiveByTwo false true) Level.rat :=
  Language.Elab.up (L := tower false true) int_le_rat
    (Language.Elab.app (L := tower false true) TowerOp.div Level.int rfl
      (intLit false true 5) (intLit false true 2))

/-- `5` and `2` converted, then divided at the rationals. -/
def divisionLater : (tower false true).Elab (fiveByTwo false true) Level.rat :=
  Language.Elab.app (L := tower false true) TowerOp.div Level.rat trivial
    (Language.Elab.up (L := tower false true) int_le_rat (intLit false true 5))
    (Language.Elab.up (L := tower false true) int_le_rat (intLit false true 2))

theorem divisionFirst_eval : divisionFirst.eval = (2 : ℚ) := by
  show (((Int.tdiv 5 2 : ℤ)) : ℚ) = 2
  have quotient : Int.tdiv 5 2 = 2 := by decide
  rw [quotient]
  norm_num

theorem divisionLater_eval : divisionLater.eval = (5 / 2 : ℚ) := by
  show ((5 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) = 5 / 2
  norm_num

/-- **The storage-dependent division: `5 / 2` at the rationals is `2` or `5/2`.** -/
theorem storageDiv_two_values :
    ∃ d d' : (tower false true).Elab (fiveByTwo false true) Level.rat,
      d.eval = (2 : ℚ) ∧ d'.eval = (5 / 2 : ℚ) :=
  ⟨divisionFirst, divisionLater, divisionFirst_eval, divisionLater_eval⟩

theorem storageDiv_incoherent : ¬ (tower false true).Coherent := by
  intro coherent
  have same : divisionFirst.eval = divisionLater.eval := coherent.1 _ _ _ _
  have differ : (2 : ℚ) ≠ 5 / 2 := by norm_num
  exact differ (divisionFirst_eval.symm.trans (same.trans divisionLater_eval))

/-! ## Rounding into finitely many values -/

/-- **No conversion from the whole numbers into a finite set of values is injective.** -/
theorem rounding_not_injective (F : Finset ℚ) (round : ℤ → F) : ¬ Function.Injective round :=
  not_injective_infinite_finite round

/-- **So two different whole numbers become equal**: with `==` in scope the conversion cannot be
silent. -/
theorem rounding_merges (F : Finset ℚ) (round : ℤ → F) : ∃ m n : ℤ, m ≠ n ∧ round m = round n := by
  by_contra none
  apply rounding_not_injective F round
  intro m n equal
  by_contra differ
  exact none ⟨m, n, differ, equal⟩

/-- **An addition that commutes with the inclusion into the rationals closes the set under
addition.** -/
theorem closed_of_commutes (P : ℚ → Prop) (add : {q // P q} → {q // P q} → {q // P q})
    (commutes : ∀ a b, (add a b : ℚ) = (a : ℚ) + b) : ∀ x, P x → ∀ y, P y → P (x + y) := by
  intro x inX y inY
  have member := (add ⟨x, inX⟩ ⟨y, inY⟩).2
  rw [commutes] at member
  exact member

/-- **No finite set of rationals with a nonzero element is closed under addition.** -/
theorem finite_not_closed (F : Finset ℚ) {x : ℚ} (inF : x ∈ F) (nonzero : x ≠ 0) :
    ¬ ∀ a, a ∈ F → ∀ b, b ∈ F → a + b ∈ F := by
  intro closed
  have multiples : ∀ n : ℕ, ((n : ℚ) + 1) * x ∈ F := by
    intro n
    induction n with
    | zero => simpa using inF
    | succ n ih =>
        have sum := closed _ ih x inF
        have equal : ((n : ℚ) + 1) * x + x = (((n + 1 : ℕ) : ℚ) + 1) * x := by
          push_cast
          ring
        rw [equal] at sum
        exact sum
  let g : ℕ → {q : ℚ // q ∈ F} := fun n => ⟨((n : ℚ) + 1) * x, multiples n⟩
  have injective : Function.Injective g := by
    intro m n equal
    have values : ((m : ℚ) + 1) * x = ((n : ℚ) + 1) * x := congrArg Subtype.val equal
    have casts : (m : ℚ) + 1 = (n : ℚ) + 1 := mul_right_cancel₀ nonzero values
    exact_mod_cast add_right_cancel casts
  exact not_injective_infinite_finite g injective

/-- **No addition on a finite set of rationals with a nonzero element commutes with the inclusion
into the rationals.** -/
theorem no_commuting_addition (F : Finset ℚ) {x : ℚ} (inF : x ∈ F) (nonzero : x ≠ 0) :
    ¬ ∃ add : {q : ℚ // q ∈ F} → {q : ℚ // q ∈ F} → {q : ℚ // q ∈ F},
      ∀ a b, (add a b : ℚ) = (a : ℚ) + b := by
  rintro ⟨add, commutes⟩
  exact finite_not_closed F inF nonzero (closed_of_commutes (· ∈ F) add commutes)

/-- **A nearest representable value exists** in every nonempty finite set. -/
theorem exists_nearest (F : Finset ℚ) (nonempty : F.Nonempty) (q : ℚ) :
    ∃ f ∈ F, ∀ g ∈ F, |f - q| ≤ |g - q| :=
  F.exists_min_image (fun f => |f - q|) nonempty

/-- **A nearest rounding exists** onto every nonempty finite set of rationals. -/
theorem exists_rounding (F : Finset ℚ) (nonempty : F.Nonempty) :
    ∃ round : ℚ → ℚ, (∀ q, round q ∈ F) ∧ ∀ q, ∀ g ∈ F, |round q - q| ≤ |g - q| := by
  choose round inF nearest using exists_nearest F nonempty
  exact ⟨round, inF, nearest⟩

/-- **With a nearest rounding, the rounded sum equals the exact sum exactly when the exact sum is
representable**; elsewhere the error is bounded by the distance to the nearest representable value,
and no equation holds. -/
theorem roundedAdd_exact_iff (F : Finset ℚ) (round : ℚ → ℚ) (inF : ∀ q, round q ∈ F)
    (nearest : ∀ q, ∀ g ∈ F, |round q - q| ≤ |g - q|) (x y : ℚ) :
    round (x + y) = x + y ↔ x + y ∈ F := by
  constructor
  · intro exact
    rw [← exact]
    exact inF (x + y)
  · intro representable
    have bound := nearest (x + y) (x + y) representable
    rw [sub_self, abs_zero] at bound
    exact sub_eq_zero.mp (abs_nonpos_iff.mp bound)

#print axioms Language.peel
#print axioms Language.agree
#print axioms Language.coherent_of
#print axioms Language.refl_needed
#print axioms Language.trans_needed
#print axioms Language.commute_needed
#print axioms Language.relCommute_needed
#print axioms Language.coherent_iff
#print axioms Language.domainsJoin_of_linear
#print axioms Language.eq_commutes_iff_injective
#print axioms Language.criterion
#print axioms cast_trans
#print axioms towerRel_commutes
#print axioms towerOp_commutes
#print axioms tower_functorial
#print axioms tower_relsCommute
#print axioms named_opsCommute
#print axioms named_coherent
#print axioms named_injective
#print axioms truncated_two_values
#print axioms truncated_incoherent
#print axioms storageDiv_two_values
#print axioms storageDiv_incoherent
#print axioms rounding_not_injective
#print axioms rounding_merges
#print axioms closed_of_commutes
#print axioms finite_not_closed
#print axioms no_commuting_addition
#print axioms exists_nearest
#print axioms exists_rounding
#print axioms roundedAdd_exact_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Coherence
