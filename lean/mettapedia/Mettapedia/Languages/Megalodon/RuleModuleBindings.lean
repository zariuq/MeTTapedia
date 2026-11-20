import Mettapedia.Languages.HOLLight.RuleModuleInterning

/-!
# Components answering judgments of the Megalodon kernel rule module

The Megalodon kernel is stated as a rule module (`MegalodonKernel`): big-step rewrite rules over
constructor data.  When the module is compiled to C, six of its judgments are answered by generic
components instead of their compiled rules: `nat.cmp`, `nat.eq`, `nat.add`, `name.eq`, `tp.eq` and
`tm.eq`.  The rules stay the contract.  This file transcribes the rules of these judgments and of
the judgments they call, and proves that each component computes what the rules compute.

* **The judgments** are inductive relations with one constructor per rule, named after the rule's
  label and carrying the rule's variables, its premises in order and its result: `NatCmp`,
  `NatEq`, `NatAdd`, `BoolAnd`, `NameEq`, `TpTag`, `TpEq`, `TmTag`, `TmEq`.  A rule applies
  whenever its premises hold.  The left side of `TP-EQ-HEADS` (and of `TM-EQ-HEADS`) matches every
  pair of arguments, so it overlaps the left side of every other rule of its judgment; no priority
  among the rules is assumed.
* **Naturals.**  The sort `Nat` (`UNat`: `nat.z`, `nat.s`) is represented by immediates: the
  number `v` stands for the numeral `s^v z` (`UNat.ofNat`, with inverse `UNat.toNat`:
  `UNat.toNat_ofNat`, `UNat.ofNat_toNat`).  The generated views read and build numerals as the
  constructors do: `Unary.tag` and `Unary.kid` (`RC_TAG_unary`, `RC_KID_unary`) match `nat.z` and
  `nat.s m` exactly when the numeral does (`Unary.tag_eq_z_iff`, `Unary.tag_eq_s_iff`);
  `Unary.zero` and `Unary.succ` (`RC_NUL_unary`, `RC_MK1_unary`) build `nat.z` and `nat.s`, the
  latter refusing at the bound of the immediates (`Unary.succ_eq_some_iff`, `Unary.succ_refines`).
* **`nat.cmp`** is the order of the numbers (`natCmp_iff`), so it has exactly one result
  (`natCmp_total`, `natCmp_functional`); `rc_nat_cmp` with the glue of its binding computes it
  (`natCmp_binding`).
* **`nat.eq`** is equality (`natEq_iff`, `natEq_iff_toNat`); comparing the immediates computes it
  (`natEq_binding`).
* **`nat.add`** is addition (`natAdd_iff`).  `rc_nat_add` (`cNatAdd`) answers the sum when it is
  at most the bound of the immediates and refuses otherwise (`cNatAdd_eq_some_iff`,
  `cNatAdd_some_iff_in_range`); every answer is the rules' result (`cNatAdd_refines`,
  `cNatAdd_binding`).
* **`name.eq`, `tp.eq`, `tm.eq`** are syntactic equality (`nameEq_iff`, `tpEq_iff`, `tmEq_iff`).
  The premises of `TP-EQ-HEADS` hold exactly on arguments with different head constructors
  (`tpEq_heads_premises_iff`), so that rule never applies where the left side of another rule of
  `tp.eq` matches (`tpEq_heads_excluded_same_head`, `tpEq_heads_excludes_sameHead`); likewise
  `TM-EQ-HEADS` (`tmEq_heads_premises_iff`, `tmEq_heads_excluded_same_head`,
  `tmEq_heads_excludes_sameHead`).
* **Interned nodes.**  Names, types and terms are hash-consed nodes of one interning store
  (`Store MgLabel`, the store of `RuleModuleInterning`).  The read-back of a node encodes a value
  (`encName`, `encTp`, `encTm`, all injective); the numerals of `Tp.var`, `Tp.base`, `Tm.db` and
  `Tm.prim` are immediates, held in the label of their node.  In an interning store, the three
  equality judgments on the values of two nodes answer `bool.t` exactly when the nodes are the
  same node (`nameEq_binding`, `tpEq_binding`, `tmEq_binding`): this is the pointer test
  `a0 == a1` of the components.  Interning a value bottom-up, as the generated constructors do
  (`internName`, `internTp`, `internTm`), keeps the store interning and gives a node that reads
  back as the value's encoding (`builds_internName`, `builds_internTp`, `builds_internTm`), so the
  binding holds for any two values interned into an interning store (`nameEq_interned`,
  `tpEq_interned`, `tmEq_interned`).

What the models leave out.

* An immediate is a word.  That two immediates are the same word exactly when they hold the same
  number, and that the `uint64_t` arithmetic of `rc_nat_cmp` and `rc_nat_add` is the arithmetic of
  `Nat` on the numbers it is given (the range checks of `rc_nat_add` come before its addition, so
  nothing wraps), are trusted.
* A refusal (`none`) stops the run; it is never an answer.  `rc_nat_add` and `RC_MK1_unary` refuse
  exactly the results above `natLimit`.
* The interning store is the model of `RuleModuleInterning`, and what that model leaves out (the
  probing of the hash table, the collector) is left out here too.  A node's id stands for its
  pointer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.RuleModuleBindings

open Mettapedia.Languages.HOLLight.RuleModuleInterning
  (Tree Store Node readback Interning interning_eq_iff intern interning_intern prefix_intern
    lt_length_intern readback_intern readback_of_prefix interning_nil)

/-! ## The module's data -/

/-- Sort `Nat` of the module: a unary numeral. -/
inductive UNat
  /-- `"nat.z"`. -/
  | z
  /-- `"nat.s"`. -/
  | s (n : UNat)
  deriving DecidableEq, Repr

/-- Sort `Bool` of the module (not Lean's `Bool`). -/
inductive MBool
  /-- `"bool.t"`. -/
  | t
  /-- `"bool.f"`. -/
  | f
  deriving DecidableEq, Repr

/-- Sort `Cmp`: the result of a comparison. -/
inductive Cmp
  /-- `"cmp.lt"`. -/
  | lt
  /-- `"cmp.eq"`. -/
  | eq
  /-- `"cmp.gt"`. -/
  | gt
  deriving DecidableEq, Repr

/-- Sort `Name`: a bit string, compared by structure. -/
inductive Name
  /-- `"nm.nil"`: the empty string. -/
  | nil
  /-- `"nm.o"`. -/
  | o (n : Name)
  /-- `"nm.i"`. -/
  | i (n : Name)
  deriving DecidableEq, Repr

/-- Sort `Tp`: types with prefix polymorphism; type variables are de Bruijn indices. -/
inductive Tp
  /-- `"Tp.var"`. -/
  | var (i : UNat)
  /-- `"Tp.prop"`. -/
  | prop
  /-- `"Tp.base"`. -/
  | base (i : UNat)
  /-- `"Tp.arr"`. -/
  | arr (a b : Tp)
  /-- `"Tp.all"`. -/
  | all (a : Tp)
  deriving DecidableEq, Repr

/-- Sort `Tm`: terms and propositions; term variables are de Bruijn indices. -/
inductive Tm
  /-- `"Tm.db"`. -/
  | db (i : UNat)
  /-- `"Tm.named"`. -/
  | named (n : Name)
  /-- `"Tm.prim"`. -/
  | prim (i : UNat)
  /-- `"Tm.app"`. -/
  | app (f x : Tm)
  /-- `"Tm.lam"`. -/
  | lam (a : Tp) (b : Tm)
  /-- `"Tm.imp"`. -/
  | imp (p q : Tm)
  /-- `"Tm.all"`. -/
  | all (a : Tp) (b : Tm)
  /-- `"Tm.typeApp"`. -/
  | typeApp (f : Tm) (a : Tp)
  /-- `"Tm.typeLam"`. -/
  | typeLam (b : Tm)
  /-- `"Tm.typeAll"`. -/
  | typeAll (b : Tm)
  deriving DecidableEq, Repr

/-! ## Numerals and immediates -/

namespace UNat

/-- The number a numeral stands for. -/
def toNat : UNat → Nat
  | z => 0
  | s n => n.toNat + 1

/-- The numeral of a number `v`: `s^v z`.  An immediate holding `v` stands for it. -/
def ofNat : Nat → UNat
  | 0 => z
  | v + 1 => s (ofNat v)

@[simp] theorem toNat_z : z.toNat = 0 := rfl

@[simp] theorem toNat_s (n : UNat) : (s n).toNat = n.toNat + 1 := rfl

@[simp] theorem ofNat_zero : ofNat 0 = z := rfl

@[simp] theorem ofNat_succ (v : Nat) : ofNat (v + 1) = s (ofNat v) := rfl

/-- `toNat` is a left inverse of `ofNat`. -/
@[simp] theorem toNat_ofNat : ∀ v : Nat, (ofNat v).toNat = v
  | 0 => rfl
  | v + 1 => congrArg (· + 1) (toNat_ofNat v)

/-- `ofNat` is a left inverse of `toNat`. -/
@[simp] theorem ofNat_toNat : ∀ a : UNat, ofNat a.toNat = a
  | z => rfl
  | s a => congrArg s (ofNat_toNat a)

theorem toNat_injective : Function.Injective toNat := fun a b h => by
  rw [← ofNat_toNat a, h, ofNat_toNat]

theorem ofNat_injective : Function.Injective ofNat := fun v w h => by
  rw [← toNat_ofNat v, h, toNat_ofNat]

theorem toNat_surjective : Function.Surjective toNat := fun v => ⟨ofNat v, toNat_ofNat v⟩

theorem ofNat_surjective : Function.Surjective ofNat := fun a => ⟨a.toNat, ofNat_toNat a⟩

@[simp] theorem toNat_inj {a b : UNat} : a.toNat = b.toNat ↔ a = b := toNat_injective.eq_iff

theorem ofNat_eq_z_iff {v : Nat} : ofNat v = z ↔ v = 0 := by
  cases v <;> simp

theorem ofNat_eq_s_iff {v : Nat} {m : UNat} : ofNat v = s m ↔ v ≠ 0 ∧ ofNat (v - 1) = m := by
  cases v <;> simp

end UNat

/-- The constructors of sort `Nat`. -/
inductive NatCtor
  /-- `"nat.z"`. -/
  | z
  /-- `"nat.s"`. -/
  | s
  deriving DecidableEq, Repr

/-- The constructor a numeral is made by. -/
def UNat.ctor : UNat → NatCtor
  | .z => .z
  | .s _ => .s

/-- The bound of the immediates, `UINT64_MAX >> 3`: an immediate holds a number at most
`natLimit`, and the components refuse to build a larger one. -/
def natLimit : Nat := 2 ^ 61 - 1

theorem natLimit_eq : natLimit = (2 ^ 64 - 1) >>> 3 := rfl

/-! ### The views of an immediate -/

namespace Unary

/-- `RC_TAG_unary`: an immediate `v` is made by `nat.z` when `v = 0`, by `nat.s` otherwise. -/
def tag (v : Nat) : NatCtor := if v = 0 then .z else .s

/-- `RC_KID_unary`: the argument of the `nat.s` that makes an immediate `v`; it is read only when
`tag v = .s`. -/
def kid (v : Nat) : Nat := v - 1

/-- `RC_NUL_unary`: `nat.z`. -/
def zero : Nat := 0

/-- `RC_MK1_unary`: `nat.s` of an immediate; refused (`none`) from `natLimit` on. -/
def succ (v : Nat) : Option Nat := if natLimit ≤ v then none else some (v + 1)

/-- The tag of an immediate is the constructor of its numeral. -/
theorem tag_eq_ctor (v : Nat) : tag v = (UNat.ofNat v).ctor := by
  cases v <;> simp [tag, UNat.ctor]

/-- An immediate matches `nat.z` through the views exactly when its numeral is `nat.z`. -/
theorem tag_eq_z_iff {v : Nat} : tag v = .z ↔ UNat.ofNat v = .z := by
  cases v <;> simp [tag]

/-- An immediate matches `nat.s m` through the views exactly when its numeral is `nat.s m`. -/
theorem tag_eq_s_iff {v : Nat} {m : UNat} :
    (tag v = .s ∧ UNat.ofNat (kid v) = m) ↔ UNat.ofNat v = .s m := by
  cases v <;> simp [tag, kid]

theorem ofNat_of_tag_z {v : Nat} (h : tag v = .z) : UNat.ofNat v = .z :=
  tag_eq_z_iff.mp h

theorem ofNat_of_tag_s {v : Nat} (h : tag v = .s) : UNat.ofNat v = .s (UNat.ofNat (kid v)) :=
  tag_eq_s_iff.mp ⟨h, rfl⟩

/-- `Unary.zero` builds `nat.z`. -/
theorem ofNat_zero : UNat.ofNat zero = .z := rfl

theorem succ_eq_some_iff {v w : Nat} : succ v = some w ↔ v < natLimit ∧ w = v + 1 := by
  unfold succ
  by_cases h : natLimit ≤ v
  · rw [if_pos h]
    exact ⟨nofun, fun ⟨h', _⟩ => absurd h' (Nat.not_lt.mpr h)⟩
  · rw [if_neg h, Option.some.injEq]
    exact ⟨fun e => ⟨by omega, e.symm⟩, fun ⟨_, e⟩ => e.symm⟩

/-- `Unary.succ` builds `nat.s` whenever it answers. -/
theorem succ_refines {v w : Nat} (h : succ v = some w) : UNat.ofNat w = .s (UNat.ofNat v) := by
  obtain ⟨-, rfl⟩ := succ_eq_some_iff.mp h
  rfl

end Unary

/-! ## Comparison and booleans -/

/-- The comparison that a Lean `Ordering` names. -/
def cmpOfOrdering : Ordering → Cmp
  | .lt => .lt
  | .eq => .eq
  | .gt => .gt

theorem cmpOfOrdering_compare (m n : Nat) :
    cmpOfOrdering (compare m n) = if m < n then .lt else if m = n then .eq else .gt := by
  by_cases h₁ : m < n
  · rw [Nat.compare_eq_lt.mpr h₁, if_pos h₁]
    rfl
  · by_cases h₂ : m = n
    · rw [Nat.compare_eq_eq.mpr h₂, if_neg h₁, if_pos h₂]
      rfl
    · rw [Nat.compare_eq_gt.mpr (by omega), if_neg h₁, if_neg h₂]
      rfl

/-- `"bool.and"`. -/
inductive BoolAnd : MBool → MBool → MBool → Prop
  /-- `"AND-T". b:Bool |- "bool.and"("bool.t"(), b) ~> b;` -/
  | t {b : MBool} : BoolAnd .t b b
  /-- `"AND-F". b:Bool |- "bool.and"("bool.f"(), b) ~> "bool.f"();` -/
  | f {b : MBool} : BoolAnd .f b .f

/-- `bool.and` of two truth values of propositions is the truth value of their conjunction. -/
theorem boolAnd_ite_iff {p q : Prop} [Decidable p] [Decidable q] {r : MBool} :
    BoolAnd (if p then .t else .f) (if q then .t else .f) r ↔ r = if p ∧ q then .t else .f := by
  by_cases hp : p
  · by_cases hq : q
    · rw [if_pos hp, if_pos hq, if_pos (show p ∧ q from ⟨hp, hq⟩)]
      exact ⟨fun h => by cases h; rfl, fun h => by subst h; exact .t⟩
    · rw [if_pos hp, if_neg hq, if_neg (show ¬ (p ∧ q) from fun h => hq h.2)]
      exact ⟨fun h => by cases h; rfl, fun h => by subst h; exact .t⟩
  · rw [if_neg hp, if_neg (show ¬ (p ∧ q) from fun h => hp h.1)]
    exact ⟨fun h => by cases h; rfl, fun h => by subst h; exact .f⟩

/-! ## `nat.cmp` -/

/-- `"nat.cmp"`. -/
inductive NatCmp : UNat → UNat → Cmp → Prop
  /-- `"NAT-CMP-ZZ". |- "nat.cmp"("nat.z"(), "nat.z"()) ~> "cmp.eq"();` -/
  | zz : NatCmp .z .z .eq
  /-- `"NAT-CMP-ZS". b:Nat |- "nat.cmp"("nat.z"(), "nat.s"(b)) ~> "cmp.lt"();` -/
  | zs {b : UNat} : NatCmp .z (.s b) .lt
  /-- `"NAT-CMP-SZ". a:Nat |- "nat.cmp"("nat.s"(a), "nat.z"()) ~> "cmp.gt"();` -/
  | sz {a : UNat} : NatCmp (.s a) .z .gt
  /-- `"NAT-CMP-SS". a:Nat, b:Nat, r:Cmp | "nat.cmp"(a, b) ~> r |- "nat.cmp"("nat.s"(a),
  "nat.s"(b)) ~> r;` -/
  | ss {a b : UNat} {r : Cmp} : NatCmp a b r → NatCmp (.s a) (.s b) r

/-- **`nat.cmp` is the order of the numbers**: its one result is the comparison of the numbers the
numerals stand for. -/
theorem natCmp_iff {a b : UNat} {c : Cmp} :
    NatCmp a b c ↔ c = cmpOfOrdering (compare a.toNat b.toNat) := by
  rw [cmpOfOrdering_compare]
  constructor
  · intro h
    induction h with
    | zz => simp
    | zs => simp
    | sz => simp
    | ss _ ih => simpa using ih
  · intro h
    subst h
    induction a generalizing b with
    | z =>
      cases b with
      | z => simpa using NatCmp.zz
      | s b => simpa using NatCmp.zs (b := b)
    | s a ih =>
      cases b with
      | z => simpa using NatCmp.sz (a := a)
      | s b => simpa using NatCmp.ss (ih (b := b))

/-- `nat.cmp` has a result on every pair of numerals. -/
theorem natCmp_total (a b : UNat) : ∃ c, NatCmp a b c := ⟨_, natCmp_iff.mpr rfl⟩

/-- `nat.cmp` has at most one result. -/
theorem natCmp_functional {a b : UNat} {c c' : Cmp} (h : NatCmp a b c) (h' : NatCmp a b c') :
    c = c' :=
  (natCmp_iff.mp h).trans (natCmp_iff.mp h').symm

theorem natCmp_eq_iff {a b : UNat} : NatCmp a b .eq ↔ a = b := by
  rw [natCmp_iff, cmpOfOrdering_compare]
  by_cases h₁ : a.toNat < b.toNat
  · rw [if_pos h₁]
    exact ⟨nofun, fun h => absurd (h ▸ h₁) (Nat.lt_irrefl _)⟩
  · by_cases h₂ : a.toNat = b.toNat
    · rw [if_neg h₁, if_pos h₂]
      exact ⟨fun _ => UNat.toNat_injective h₂, fun _ => rfl⟩
    · rw [if_neg h₁, if_neg h₂]
      exact ⟨nofun, fun h => absurd (congrArg UNat.toNat h) h₂⟩

/-- `rc_nat_cmp`: `x < y ? -1 : x > y ? 1 : 0`. -/
def rcNatCmp (x y : Nat) : Int := if x < y then -1 else if y < x then 1 else 0

/-- The glue of the binding of `nat.cmp`: `c < 0 ? cmp.lt : c > 0 ? cmp.gt : cmp.eq`. -/
def cmpOfSign (c : Int) : Cmp := if c < 0 then .lt else if 0 < c then .gt else .eq

/-- **The `nat.cmp` component**: `rc_nat_cmp` on two immediates, with its glue, is the one result
of `nat.cmp` on their numerals. -/
theorem natCmp_binding {x y : Nat} {c : Cmp} :
    NatCmp (UNat.ofNat x) (UNat.ofNat y) c ↔ c = cmpOfSign (rcNatCmp x y) := by
  rw [natCmp_iff, UNat.toNat_ofNat, UNat.toNat_ofNat, cmpOfOrdering_compare]
  unfold cmpOfSign rcNatCmp
  by_cases h₁ : x < y
  · simp [h₁]
  · by_cases h₂ : y < x
    · have h₃ : x ≠ y := by omega
      simp [h₁, h₂, h₃]
    · have h₃ : x = y := by omega
      subst h₃
      simp

/-! ## `nat.eq` -/

/-- `"nat.eq"`. -/
inductive NatEq : UNat → UNat → MBool → Prop
  /-- `"NAT-EQ-EQ". a:Nat, b:Nat | "nat.cmp"(a, b) ~> "cmp.eq"() |- "nat.eq"(a, b) ~>
  "bool.t"();` -/
  | eq {a b : UNat} : NatCmp a b .eq → NatEq a b .t
  /-- `"NAT-EQ-LT". a:Nat, b:Nat | "nat.cmp"(a, b) ~> "cmp.lt"() |- "nat.eq"(a, b) ~>
  "bool.f"();` -/
  | lt {a b : UNat} : NatCmp a b .lt → NatEq a b .f
  /-- `"NAT-EQ-GT". a:Nat, b:Nat | "nat.cmp"(a, b) ~> "cmp.gt"() |- "nat.eq"(a, b) ~>
  "bool.f"();` -/
  | gt {a b : UNat} : NatCmp a b .gt → NatEq a b .f

/-- **`nat.eq` is equality of numerals.** -/
theorem natEq_iff {a b : UNat} {r : MBool} : NatEq a b r ↔ r = if a = b then .t else .f := by
  constructor
  · rintro (h | h | h)
    · rw [if_pos (natCmp_eq_iff.mp h)]
    · rw [if_neg]
      rintro rfl
      exact nomatch natCmp_functional h (natCmp_eq_iff.mpr rfl)
    · rw [if_neg]
      rintro rfl
      exact nomatch natCmp_functional h (natCmp_eq_iff.mpr rfl)
  · rintro rfl
    by_cases hab : a = b
    · rw [if_pos hab]
      exact .eq (natCmp_eq_iff.mpr hab)
    · rw [if_neg hab]
      obtain ⟨c, hc⟩ := natCmp_total a b
      cases c with
      | lt => exact .lt hc
      | eq => exact absurd (natCmp_eq_iff.mp hc) hab
      | gt => exact .gt hc

/-- `nat.eq` is equality of the numbers the numerals stand for. -/
theorem natEq_iff_toNat {a b : UNat} {r : MBool} :
    NatEq a b r ↔ r = if a.toNat = b.toNat then .t else .f := by
  rw [natEq_iff]
  by_cases h : a = b
  · rw [if_pos h, if_pos (congrArg UNat.toNat h)]
  · rw [if_neg h, if_neg (fun e => h (UNat.toNat_injective e))]

/-- **The `nat.eq` component**: comparing two immediates gives the one result of `nat.eq` on their
numerals. -/
theorem natEq_binding {x y : Nat} {r : MBool} :
    NatEq (UNat.ofNat x) (UNat.ofNat y) r ↔ r = if x = y then .t else .f := by
  rw [natEq_iff_toNat, UNat.toNat_ofNat, UNat.toNat_ofNat]

/-! ## `nat.add` -/

/-- `"nat.add"`. -/
inductive NatAdd : UNat → UNat → UNat → Prop
  /-- `"NAT-ADD-Z". b:Nat |- "nat.add"("nat.z"(), b) ~> b;` -/
  | z {b : UNat} : NatAdd .z b b
  /-- `"NAT-ADD-S". a:Nat, b:Nat, c:Nat | "nat.add"(a, b) ~> c |- "nat.add"("nat.s"(a), b) ~>
  "nat.s"(c);` -/
  | s {a b c : UNat} : NatAdd a b c → NatAdd (.s a) b (.s c)

/-- **`nat.add` is addition**: its one result is the numeral of the sum of the numbers. -/
theorem natAdd_iff {a b c : UNat} : NatAdd a b c ↔ c = UNat.ofNat (a.toNat + b.toNat) := by
  constructor
  · intro h
    induction h with
    | z => simp
    | s _ ih =>
      rw [ih, UNat.toNat_s, Nat.add_right_comm]
      rfl
  · intro h
    subst h
    induction a with
    | z => simpa using NatAdd.z (b := b)
    | s a ih =>
      rw [UNat.toNat_s, Nat.add_right_comm]
      exact .s ih

/-- `rc_nat_add`: `x + y`, refused (`none`) when `x > natLimit` or `y > natLimit - x`. -/
def cNatAdd (x y : Nat) : Option Nat :=
  if x > natLimit ∨ y > natLimit - x then none else some (x + y)

theorem cNatAdd_eq_some_iff {x y z : Nat} :
    cNatAdd x y = some z ↔ x + y ≤ natLimit ∧ z = x + y := by
  unfold cNatAdd
  by_cases h : x > natLimit ∨ y > natLimit - x
  · rw [if_pos h]
    exact ⟨nofun, fun ⟨h', _⟩ => by omega⟩
  · rw [if_neg h, Option.some.injEq]
    exact ⟨fun e => ⟨by omega, e.symm⟩, fun ⟨_, e⟩ => e.symm⟩

/-- `rc_nat_add` answers exactly when the sum is at most `natLimit`, the largest value that
`RC_MK1_unary` builds. -/
theorem cNatAdd_some_iff_in_range {x y : Nat} :
    (∃ z, cNatAdd x y = some z) ↔ x + y ≤ natLimit :=
  ⟨fun ⟨_, hz⟩ => (cNatAdd_eq_some_iff.mp hz).1,
    fun h => ⟨x + y, cNatAdd_eq_some_iff.mpr ⟨h, rfl⟩⟩⟩

/-- **The `nat.add` component**: every answer of `rc_nat_add` on two immediates is a result of
`nat.add` on their numerals. -/
theorem cNatAdd_refines {x y z : Nat} (h : cNatAdd x y = some z) :
    NatAdd (UNat.ofNat x) (UNat.ofNat y) (UNat.ofNat z) := by
  obtain ⟨-, rfl⟩ := cNatAdd_eq_some_iff.mp h
  exact natAdd_iff.mpr (by rw [UNat.toNat_ofNat, UNat.toNat_ofNat])

/-- An answer of `rc_nat_add` is the only result of `nat.add`. -/
theorem cNatAdd_binding {x y z : Nat} (h : cNatAdd x y = some z) {c : UNat} :
    NatAdd (UNat.ofNat x) (UNat.ofNat y) c ↔ c = UNat.ofNat z := by
  obtain ⟨-, rfl⟩ := cNatAdd_eq_some_iff.mp h
  rw [natAdd_iff, UNat.toNat_ofNat, UNat.toNat_ofNat]

/-! ## `name.eq` -/

/-- `"name.eq"`. -/
inductive NameEq : Name → Name → MBool → Prop
  /-- `"NAME-EQ-NN". |- "name.eq"("nm.nil"(), "nm.nil"()) ~> "bool.t"();` -/
  | nn : NameEq .nil .nil .t
  /-- `"NAME-EQ-NO". b:Name |- "name.eq"("nm.nil"(), "nm.o"(b)) ~> "bool.f"();` -/
  | no {b : Name} : NameEq .nil (.o b) .f
  /-- `"NAME-EQ-NI". b:Name |- "name.eq"("nm.nil"(), "nm.i"(b)) ~> "bool.f"();` -/
  | ni {b : Name} : NameEq .nil (.i b) .f
  /-- `"NAME-EQ-ON". a:Name |- "name.eq"("nm.o"(a), "nm.nil"()) ~> "bool.f"();` -/
  | on {a : Name} : NameEq (.o a) .nil .f
  /-- `"NAME-EQ-OO". a:Name, b:Name, r:Bool | "name.eq"(a, b) ~> r |- "name.eq"("nm.o"(a),
  "nm.o"(b)) ~> r;` -/
  | oo {a b : Name} {r : MBool} : NameEq a b r → NameEq (.o a) (.o b) r
  /-- `"NAME-EQ-OI". a:Name, b:Name |- "name.eq"("nm.o"(a), "nm.i"(b)) ~> "bool.f"();` -/
  | oi {a b : Name} : NameEq (.o a) (.i b) .f
  /-- `"NAME-EQ-IN". a:Name |- "name.eq"("nm.i"(a), "nm.nil"()) ~> "bool.f"();` -/
  | «in» {a : Name} : NameEq (.i a) .nil .f
  /-- `"NAME-EQ-IO". a:Name, b:Name |- "name.eq"("nm.i"(a), "nm.o"(b)) ~> "bool.f"();` -/
  | io {a b : Name} : NameEq (.i a) (.o b) .f
  /-- `"NAME-EQ-II". a:Name, b:Name, r:Bool | "name.eq"(a, b) ~> r |- "name.eq"("nm.i"(a),
  "nm.i"(b)) ~> r;` -/
  | ii {a b : Name} {r : MBool} : NameEq a b r → NameEq (.i a) (.i b) r

/-- **`name.eq` is equality of names.** -/
theorem nameEq_iff {a b : Name} {r : MBool} : NameEq a b r ↔ r = if a = b then .t else .f := by
  constructor
  · intro h
    induction h with
    | oo _ ih => rw [ih]; simp
    | ii _ ih => rw [ih]; simp
    | nn => simp
    | no => simp
    | ni => simp
    | on => simp
    | oi => simp
    | «in» => simp
    | io => simp
  · rintro rfl
    induction a generalizing b with
    | nil =>
      cases b with
      | nil => simpa using NameEq.nn
      | o b => simpa using NameEq.no (b := b)
      | i b => simpa using NameEq.ni (b := b)
    | o a ih =>
      cases b with
      | nil => simpa using NameEq.on (a := a)
      | o b => simpa using NameEq.oo (ih (b := b))
      | i b => simpa using NameEq.oi (a := a) (b := b)
    | i a ih =>
      cases b with
      | nil => simpa using NameEq.«in» (a := a)
      | o b => simpa using NameEq.io (a := a) (b := b)
      | i b => simpa using NameEq.ii (ih (b := b))

/-! ## `tp.tag` and `tp.eq` -/

/-- `"tp.tag"`. -/
inductive TpTag : Tp → UNat → Prop
  /-- `"TP-TAG-VAR". i:Nat |- "tp.tag"("Tp.var"(i)) ~> "nat.z"();` -/
  | var {i : UNat} : TpTag (.var i) .z
  /-- `"TP-TAG-PROP". |- "tp.tag"("Tp.prop"()) ~> "nat.s"("nat.z"());` -/
  | prop : TpTag .prop (.s .z)
  /-- `"TP-TAG-BASE". i:Nat |- "tp.tag"("Tp.base"(i)) ~> "nat.s"("nat.s"("nat.z"()));` -/
  | base {i : UNat} : TpTag (.base i) (.s (.s .z))
  /-- `"TP-TAG-ARR". a:Tp, b:Tp |- "tp.tag"("Tp.arr"(a, b)) ~>
  "nat.s"("nat.s"("nat.s"("nat.z"())));` -/
  | arr {a b : Tp} : TpTag (.arr a b) (.s (.s (.s .z)))
  /-- `"TP-TAG-ALL". a:Tp |- "tp.tag"("Tp.all"(a)) ~>
  "nat.s"("nat.s"("nat.s"("nat.s"("nat.z"()))));` -/
  | all {a : Tp} : TpTag (.all a) (.s (.s (.s (.s .z))))

/-- `"tp.eq"`. -/
inductive TpEq : Tp → Tp → MBool → Prop
  /-- `"TP-EQ-HEADS". a:Tp, b:Tp, i:Nat, j:Nat | "tp.tag"(a) ~> i, "tp.tag"(b) ~> j, "nat.eq"(i,
  j) ~> "bool.f"() |- "tp.eq"(a, b) ~> "bool.f"();` -/
  | heads {a b : Tp} {i j : UNat} : TpTag a i → TpTag b j → NatEq i j .f → TpEq a b .f
  /-- `"TP-EQ-VAR". i:Nat, j:Nat, r:Bool | "nat.eq"(i, j) ~> r |- "tp.eq"("Tp.var"(i),
  "Tp.var"(j)) ~> r;` -/
  | var {i j : UNat} {r : MBool} : NatEq i j r → TpEq (.var i) (.var j) r
  /-- `"TP-EQ-PROP". |- "tp.eq"("Tp.prop"(), "Tp.prop"()) ~> "bool.t"();` -/
  | prop : TpEq .prop .prop .t
  /-- `"TP-EQ-BASE". i:Nat, j:Nat, r:Bool | "nat.eq"(i, j) ~> r |- "tp.eq"("Tp.base"(i),
  "Tp.base"(j)) ~> r;` -/
  | base {i j : UNat} {r : MBool} : NatEq i j r → TpEq (.base i) (.base j) r
  /-- `"TP-EQ-ARR". a:Tp, b:Tp, c:Tp, d:Tp, x:Bool, y:Bool, r:Bool | "tp.eq"(a, c) ~> x,
  "tp.eq"(b, d) ~> y, "bool.and"(x, y) ~> r |- "tp.eq"("Tp.arr"(a, b), "Tp.arr"(c, d)) ~> r;` -/
  | arr {a b c d : Tp} {x y r : MBool} :
      TpEq a c x → TpEq b d y → BoolAnd x y r → TpEq (.arr a b) (.arr c d) r
  /-- `"TP-EQ-ALL". a:Tp, b:Tp, r:Bool | "tp.eq"(a, b) ~> r |- "tp.eq"("Tp.all"(a), "Tp.all"(b))
  ~> r;` -/
  | all {a b : Tp} {r : MBool} : TpEq a b r → TpEq (.all a) (.all b) r

/-- The numeral `tp.tag` gives each constructor of `Tp`. -/
def Tp.tag : Tp → UNat
  | .var _ => .z
  | .prop => .s .z
  | .base _ => .s (.s .z)
  | .arr _ _ => .s (.s (.s .z))
  | .all _ => .s (.s (.s (.s .z)))

/-- `tp.tag` has exactly one result, the numeral of the head constructor. -/
theorem tpTag_iff {a : Tp} {i : UNat} : TpTag a i ↔ i = a.tag := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · rintro rfl
    cases a <;> constructor

/-- The left sides of the rules of `tp.eq` other than `TP-EQ-HEADS`, which require the two
arguments to be made by the same constructor. -/
inductive TpEqSameHead : Tp → Tp → Prop
  /-- The left side of `TP-EQ-VAR`. -/
  | var {i j : UNat} : TpEqSameHead (.var i) (.var j)
  /-- The left side of `TP-EQ-PROP`. -/
  | prop : TpEqSameHead .prop .prop
  /-- The left side of `TP-EQ-BASE`. -/
  | base {i j : UNat} : TpEqSameHead (.base i) (.base j)
  /-- The left side of `TP-EQ-ARR`. -/
  | arr {a b c d : Tp} : TpEqSameHead (.arr a b) (.arr c d)
  /-- The left side of `TP-EQ-ALL`. -/
  | all {a b : Tp} : TpEqSameHead (.all a) (.all b)

/-- A rule of `tp.eq` other than `TP-EQ-HEADS` matches exactly the pairs with equal tags. -/
theorem tpEqSameHead_iff {a b : Tp} : TpEqSameHead a b ↔ a.tag = b.tag := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · intro h
    cases a <;> cases b <;> first | constructor | exact absurd h (by simp [Tp.tag])

/-- **The premises of `TP-EQ-HEADS`** hold exactly on arguments with different head constructors. -/
theorem tpEq_heads_premises_iff {a b : Tp} :
    (∃ i j, TpTag a i ∧ TpTag b j ∧ NatEq i j .f) ↔ a.tag ≠ b.tag := by
  constructor
  · rintro ⟨i, j, hi, hj, hij⟩ h
    rw [tpTag_iff] at hi hj
    subst hi hj
    have e := natEq_iff.mp hij
    rw [if_pos h] at e
    exact nomatch e
  · intro h
    exact ⟨a.tag, b.tag, tpTag_iff.mpr rfl, tpTag_iff.mpr rfl, natEq_iff.mpr (by rw [if_neg h])⟩

/-- **`TP-EQ-HEADS` never fires on equal heads.** -/
theorem tpEq_heads_excluded_same_head {a b : Tp} (h : a.tag = b.tag) {i j : UNat}
    (hi : TpTag a i) (hj : TpTag b j) : ¬ NatEq i j .f :=
  fun hij => tpEq_heads_premises_iff.mp ⟨i, j, hi, hj, hij⟩ h

/-- **`TP-EQ-HEADS` and the other rules of `tp.eq` never both apply**: where the left side of
another rule matches, the premises of `TP-EQ-HEADS` fail. -/
theorem tpEq_heads_excludes_sameHead {a b : Tp} (h : TpEqSameHead a b) :
    ¬ ∃ i j, TpTag a i ∧ TpTag b j ∧ NatEq i j .f :=
  fun hp => tpEq_heads_premises_iff.mp hp (tpEqSameHead_iff.mp h)

/-- Every derivation of `tp.eq` gives the truth value of the equality of its arguments. -/
theorem tpEq_eq_ite {a b : Tp} {r : MBool} (h : TpEq a b r) : r = if a = b then .t else .f := by
  induction h with
  | heads hi hj hij =>
    rw [if_neg]
    rintro rfl
    exact tpEq_heads_excluded_same_head rfl hi hj hij
  | var h => rw [natEq_iff.mp h]; simp
  | prop => simp
  | base h => rw [natEq_iff.mp h]; simp
  | arr _ _ h ih₁ ih₂ =>
    subst ih₁ ih₂
    rw [boolAnd_ite_iff.mp h]
    simp
  | all _ ih => rw [ih]; simp

/-- On arguments with different head constructors, `TP-EQ-HEADS` derives `bool.f`. -/
theorem tpEq_ite_of_tag_ne {a b : Tp} (h : a.tag ≠ b.tag) :
    TpEq a b (if a = b then .t else .f) := by
  rw [if_neg (fun e => h (congrArg Tp.tag e))]
  obtain ⟨i, j, hi, hj, hij⟩ := tpEq_heads_premises_iff.mpr h
  exact .heads hi hj hij

/-- `tp.eq` derives the truth value of the equality of its arguments. -/
theorem tpEq_ite : ∀ a b : Tp, TpEq a b (if a = b then .t else .f) := by
  intro a
  induction a with
  | var i =>
    intro b
    cases b
    case var j => simpa using TpEq.var (natEq_iff.mpr rfl : NatEq i j _)
    all_goals exact tpEq_ite_of_tag_ne (by simp [Tp.tag])
  | prop =>
    intro b
    cases b
    case prop => simpa using TpEq.prop
    all_goals exact tpEq_ite_of_tag_ne (by simp [Tp.tag])
  | base i =>
    intro b
    cases b
    case base j => simpa using TpEq.base (natEq_iff.mpr rfl : NatEq i j _)
    all_goals exact tpEq_ite_of_tag_ne (by simp [Tp.tag])
  | arr a₁ a₂ ih₁ ih₂ =>
    intro b
    cases b
    case arr c d => simpa using TpEq.arr (ih₁ c) (ih₂ d) (boolAnd_ite_iff.mpr rfl)
    all_goals exact tpEq_ite_of_tag_ne (by simp [Tp.tag])
  | all a ih =>
    intro b
    cases b
    case all c => simpa using TpEq.all (ih c)
    all_goals exact tpEq_ite_of_tag_ne (by simp [Tp.tag])

/-- **`tp.eq` is equality of types**: its one result is `bool.t` on equal types and `bool.f`
otherwise. -/
theorem tpEq_iff {a b : Tp} {r : MBool} : TpEq a b r ↔ r = if a = b then .t else .f :=
  ⟨tpEq_eq_ite, fun h => h ▸ tpEq_ite a b⟩

theorem tpEq_total (a b : Tp) : ∃ r, TpEq a b r := ⟨_, tpEq_ite a b⟩

theorem tpEq_functional {a b : Tp} {r r' : MBool} (h : TpEq a b r) (h' : TpEq a b r') : r = r' :=
  (tpEq_iff.mp h).trans (tpEq_iff.mp h').symm

/-! ## `tm.tag` and `tm.eq` -/

/-- `"tm.tag"`. -/
inductive TmTag : Tm → UNat → Prop
  /-- `"TM-TAG-DB". i:Nat |- "tm.tag"("Tm.db"(i)) ~> "nat.z"();` -/
  | db {i : UNat} : TmTag (.db i) .z
  /-- `"TM-TAG-NAMED". n:Name |- "tm.tag"("Tm.named"(n)) ~> "nat.s"("nat.z"());` -/
  | named {n : Name} : TmTag (.named n) (.s .z)
  /-- `"TM-TAG-PRIM". i:Nat |- "tm.tag"("Tm.prim"(i)) ~> "nat.s"("nat.s"("nat.z"()));` -/
  | prim {i : UNat} : TmTag (.prim i) (.s (.s .z))
  /-- `"TM-TAG-APP". f:Tm, x:Tm |- "tm.tag"("Tm.app"(f, x)) ~>
  "nat.s"("nat.s"("nat.s"("nat.z"())));` -/
  | app {f x : Tm} : TmTag (.app f x) (.s (.s (.s .z)))
  /-- `"TM-TAG-LAM". a:Tp, b:Tm |- "tm.tag"("Tm.lam"(a, b)) ~>
  "nat.s"("nat.s"("nat.s"("nat.s"("nat.z"()))));` -/
  | lam {a : Tp} {b : Tm} : TmTag (.lam a b) (.s (.s (.s (.s .z))))
  /-- `"TM-TAG-IMP". p:Tm, q:Tm |- "tm.tag"("Tm.imp"(p, q)) ~>
  "nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.z"())))));` -/
  | imp {p q : Tm} : TmTag (.imp p q) (.s (.s (.s (.s (.s .z)))))
  /-- `"TM-TAG-ALL". a:Tp, b:Tm |- "tm.tag"("Tm.all"(a, b)) ~>
  "nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.z"()))))));` -/
  | all {a : Tp} {b : Tm} : TmTag (.all a b) (.s (.s (.s (.s (.s (.s .z))))))
  /-- `"TM-TAG-TAPP". f:Tm, a:Tp |- "tm.tag"("Tm.typeApp"(f, a)) ~>
  "nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.z"())))))));` -/
  | tapp {f : Tm} {a : Tp} : TmTag (.typeApp f a) (.s (.s (.s (.s (.s (.s (.s .z)))))))
  /-- `"TM-TAG-TLAM". b:Tm |- "tm.tag"("Tm.typeLam"(b)) ~>
  "nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.z"()))))))));` -/
  | tlam {b : Tm} : TmTag (.typeLam b) (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))
  /-- `"TM-TAG-TALL". b:Tm |- "tm.tag"("Tm.typeAll"(b)) ~>
  "nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.s"("nat.z"())))))))));` -/
  | tall {b : Tm} : TmTag (.typeAll b) (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))

/-- `"tm.eq"`. -/
inductive TmEq : Tm → Tm → MBool → Prop
  /-- `"TM-EQ-HEADS". a:Tm, b:Tm, i:Nat, j:Nat | "tm.tag"(a) ~> i, "tm.tag"(b) ~> j, "nat.eq"(i,
  j) ~> "bool.f"() |- "tm.eq"(a, b) ~> "bool.f"();` -/
  | heads {a b : Tm} {i j : UNat} : TmTag a i → TmTag b j → NatEq i j .f → TmEq a b .f
  /-- `"TM-EQ-DB". i:Nat, j:Nat, r:Bool | "nat.eq"(i, j) ~> r |- "tm.eq"("Tm.db"(i), "Tm.db"(j))
  ~> r;` -/
  | db {i j : UNat} {r : MBool} : NatEq i j r → TmEq (.db i) (.db j) r
  /-- `"TM-EQ-NAMED". n:Name, m:Name, r:Bool | "name.eq"(n, m) ~> r |- "tm.eq"("Tm.named"(n),
  "Tm.named"(m)) ~> r;` -/
  | named {n m : Name} {r : MBool} : NameEq n m r → TmEq (.named n) (.named m) r
  /-- `"TM-EQ-PRIM". i:Nat, j:Nat, r:Bool | "nat.eq"(i, j) ~> r |- "tm.eq"("Tm.prim"(i),
  "Tm.prim"(j)) ~> r;` -/
  | prim {i j : UNat} {r : MBool} : NatEq i j r → TmEq (.prim i) (.prim j) r
  /-- `"TM-EQ-APP". f:Tm, x:Tm, g:Tm, y:Tm, a:Bool, b:Bool, r:Bool | "tm.eq"(f, g) ~> a,
  "tm.eq"(x, y) ~> b, "bool.and"(a, b) ~> r |- "tm.eq"("Tm.app"(f, x), "Tm.app"(g, y)) ~> r;` -/
  | app {f x g y : Tm} {a b r : MBool} :
      TmEq f g a → TmEq x y b → BoolAnd a b r → TmEq (.app f x) (.app g y) r
  /-- `"TM-EQ-LAM". s:Tp, b:Tm, t:Tp, c:Tm, x:Bool, y:Bool, r:Bool | "tp.eq"(s, t) ~> x,
  "tm.eq"(b, c) ~> y, "bool.and"(x, y) ~> r |- "tm.eq"("Tm.lam"(s, b), "Tm.lam"(t, c)) ~> r;` -/
  | lam {s : Tp} {b : Tm} {t : Tp} {c : Tm} {x y r : MBool} :
      TpEq s t x → TmEq b c y → BoolAnd x y r → TmEq (.lam s b) (.lam t c) r
  /-- `"TM-EQ-IMP". p:Tm, q:Tm, u:Tm, v:Tm, a:Bool, b:Bool, r:Bool | "tm.eq"(p, u) ~> a,
  "tm.eq"(q, v) ~> b, "bool.and"(a, b) ~> r |- "tm.eq"("Tm.imp"(p, q), "Tm.imp"(u, v)) ~> r;` -/
  | imp {p q u v : Tm} {a b r : MBool} :
      TmEq p u a → TmEq q v b → BoolAnd a b r → TmEq (.imp p q) (.imp u v) r
  /-- `"TM-EQ-ALL". s:Tp, b:Tm, t:Tp, c:Tm, x:Bool, y:Bool, r:Bool | "tp.eq"(s, t) ~> x,
  "tm.eq"(b, c) ~> y, "bool.and"(x, y) ~> r |- "tm.eq"("Tm.all"(s, b), "Tm.all"(t, c)) ~> r;` -/
  | all {s : Tp} {b : Tm} {t : Tp} {c : Tm} {x y r : MBool} :
      TpEq s t x → TmEq b c y → BoolAnd x y r → TmEq (.all s b) (.all t c) r
  /-- `"TM-EQ-TAPP". f:Tm, s:Tp, g:Tm, t:Tp, a:Bool, b:Bool, r:Bool | "tm.eq"(f, g) ~> a,
  "tp.eq"(s, t) ~> b, "bool.and"(a, b) ~> r |- "tm.eq"("Tm.typeApp"(f, s), "Tm.typeApp"(g, t)) ~>
  r;` -/
  | tapp {f : Tm} {s : Tp} {g : Tm} {t : Tp} {a b r : MBool} :
      TmEq f g a → TpEq s t b → BoolAnd a b r → TmEq (.typeApp f s) (.typeApp g t) r
  /-- `"TM-EQ-TLAM". b:Tm, c:Tm, r:Bool | "tm.eq"(b, c) ~> r |- "tm.eq"("Tm.typeLam"(b),
  "Tm.typeLam"(c)) ~> r;` -/
  | tlam {b c : Tm} {r : MBool} : TmEq b c r → TmEq (.typeLam b) (.typeLam c) r
  /-- `"TM-EQ-TALL". b:Tm, c:Tm, r:Bool | "tm.eq"(b, c) ~> r |- "tm.eq"("Tm.typeAll"(b),
  "Tm.typeAll"(c)) ~> r;` -/
  | tall {b c : Tm} {r : MBool} : TmEq b c r → TmEq (.typeAll b) (.typeAll c) r

/-- The numeral `tm.tag` gives each constructor of `Tm`. -/
def Tm.tag : Tm → UNat
  | .db _ => .z
  | .named _ => .s .z
  | .prim _ => .s (.s .z)
  | .app _ _ => .s (.s (.s .z))
  | .lam _ _ => .s (.s (.s (.s .z)))
  | .imp _ _ => .s (.s (.s (.s (.s .z))))
  | .all _ _ => .s (.s (.s (.s (.s (.s .z)))))
  | .typeApp _ _ => .s (.s (.s (.s (.s (.s (.s .z))))))
  | .typeLam _ => .s (.s (.s (.s (.s (.s (.s (.s .z)))))))
  | .typeAll _ => .s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))

/-- `tm.tag` has exactly one result, the numeral of the head constructor. -/
theorem tmTag_iff {a : Tm} {i : UNat} : TmTag a i ↔ i = a.tag := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · rintro rfl
    cases a <;> constructor

/-- The left sides of the rules of `tm.eq` other than `TM-EQ-HEADS`, which require the two
arguments to be made by the same constructor. -/
inductive TmEqSameHead : Tm → Tm → Prop
  /-- The left side of `TM-EQ-DB`. -/
  | db {i j : UNat} : TmEqSameHead (.db i) (.db j)
  /-- The left side of `TM-EQ-NAMED`. -/
  | named {n m : Name} : TmEqSameHead (.named n) (.named m)
  /-- The left side of `TM-EQ-PRIM`. -/
  | prim {i j : UNat} : TmEqSameHead (.prim i) (.prim j)
  /-- The left side of `TM-EQ-APP`. -/
  | app {f x g y : Tm} : TmEqSameHead (.app f x) (.app g y)
  /-- The left side of `TM-EQ-LAM`. -/
  | lam {s : Tp} {b : Tm} {t : Tp} {c : Tm} : TmEqSameHead (.lam s b) (.lam t c)
  /-- The left side of `TM-EQ-IMP`. -/
  | imp {p q u v : Tm} : TmEqSameHead (.imp p q) (.imp u v)
  /-- The left side of `TM-EQ-ALL`. -/
  | all {s : Tp} {b : Tm} {t : Tp} {c : Tm} : TmEqSameHead (.all s b) (.all t c)
  /-- The left side of `TM-EQ-TAPP`. -/
  | tapp {f : Tm} {s : Tp} {g : Tm} {t : Tp} : TmEqSameHead (.typeApp f s) (.typeApp g t)
  /-- The left side of `TM-EQ-TLAM`. -/
  | tlam {b c : Tm} : TmEqSameHead (.typeLam b) (.typeLam c)
  /-- The left side of `TM-EQ-TALL`. -/
  | tall {b c : Tm} : TmEqSameHead (.typeAll b) (.typeAll c)

/-- A rule of `tm.eq` other than `TM-EQ-HEADS` matches exactly the pairs with equal tags. -/
theorem tmEqSameHead_iff {a b : Tm} : TmEqSameHead a b ↔ a.tag = b.tag := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · intro h
    cases a <;> cases b <;> first | constructor | exact absurd h (by simp [Tm.tag])

/-- **The premises of `TM-EQ-HEADS`** hold exactly on arguments with different head constructors. -/
theorem tmEq_heads_premises_iff {a b : Tm} :
    (∃ i j, TmTag a i ∧ TmTag b j ∧ NatEq i j .f) ↔ a.tag ≠ b.tag := by
  constructor
  · rintro ⟨i, j, hi, hj, hij⟩ h
    rw [tmTag_iff] at hi hj
    subst hi hj
    have e := natEq_iff.mp hij
    rw [if_pos h] at e
    exact nomatch e
  · intro h
    exact ⟨a.tag, b.tag, tmTag_iff.mpr rfl, tmTag_iff.mpr rfl, natEq_iff.mpr (by rw [if_neg h])⟩

/-- **`TM-EQ-HEADS` never fires on equal heads.** -/
theorem tmEq_heads_excluded_same_head {a b : Tm} (h : a.tag = b.tag) {i j : UNat}
    (hi : TmTag a i) (hj : TmTag b j) : ¬ NatEq i j .f :=
  fun hij => tmEq_heads_premises_iff.mp ⟨i, j, hi, hj, hij⟩ h

/-- **`TM-EQ-HEADS` and the other rules of `tm.eq` never both apply**: where the left side of
another rule matches, the premises of `TM-EQ-HEADS` fail. -/
theorem tmEq_heads_excludes_sameHead {a b : Tm} (h : TmEqSameHead a b) :
    ¬ ∃ i j, TmTag a i ∧ TmTag b j ∧ NatEq i j .f :=
  fun hp => tmEq_heads_premises_iff.mp hp (tmEqSameHead_iff.mp h)

/-- Every derivation of `tm.eq` gives the truth value of the equality of its arguments. -/
theorem tmEq_eq_ite {a b : Tm} {r : MBool} (h : TmEq a b r) : r = if a = b then .t else .f := by
  induction h with
  | heads hi hj hij =>
    rw [if_neg]
    rintro rfl
    exact tmEq_heads_excluded_same_head rfl hi hj hij
  | db h => rw [natEq_iff.mp h]; simp
  | named h => rw [nameEq_iff.mp h]; simp
  | prim h => rw [natEq_iff.mp h]; simp
  | app _ _ h ih₁ ih₂ =>
    subst ih₁ ih₂
    rw [boolAnd_ite_iff.mp h]
    simp
  | lam h₁ _ h ih =>
    rw [tpEq_iff] at h₁
    subst h₁ ih
    rw [boolAnd_ite_iff.mp h]
    simp
  | imp _ _ h ih₁ ih₂ =>
    subst ih₁ ih₂
    rw [boolAnd_ite_iff.mp h]
    simp
  | all h₁ _ h ih =>
    rw [tpEq_iff] at h₁
    subst h₁ ih
    rw [boolAnd_ite_iff.mp h]
    simp
  | tapp _ h₂ h ih =>
    rw [tpEq_iff] at h₂
    subst h₂ ih
    rw [boolAnd_ite_iff.mp h]
    simp
  | tlam _ ih => rw [ih]; simp
  | tall _ ih => rw [ih]; simp

/-- On arguments with different head constructors, `TM-EQ-HEADS` derives `bool.f`. -/
theorem tmEq_ite_of_tag_ne {a b : Tm} (h : a.tag ≠ b.tag) :
    TmEq a b (if a = b then .t else .f) := by
  rw [if_neg (fun e => h (congrArg Tm.tag e))]
  obtain ⟨i, j, hi, hj, hij⟩ := tmEq_heads_premises_iff.mpr h
  exact .heads hi hj hij

/-- `tm.eq` derives the truth value of the equality of its arguments. -/
theorem tmEq_ite : ∀ a b : Tm, TmEq a b (if a = b then .t else .f) := by
  intro a
  induction a with
  | db i =>
    intro b
    cases b
    case db j => simpa using TmEq.db (natEq_iff.mpr rfl : NatEq i j _)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | named n =>
    intro b
    cases b
    case named m => simpa using TmEq.named (nameEq_iff.mpr rfl : NameEq n m _)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | prim i =>
    intro b
    cases b
    case prim j => simpa using TmEq.prim (natEq_iff.mpr rfl : NatEq i j _)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | app f x ih₁ ih₂ =>
    intro b
    cases b
    case app g y => simpa using TmEq.app (ih₁ g) (ih₂ y) (boolAnd_ite_iff.mpr rfl)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | lam s b ih =>
    intro b'
    cases b'
    case lam t c =>
      simpa using TmEq.lam (tpEq_ite s t) (ih c) (boolAnd_ite_iff.mpr rfl)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | imp p q ih₁ ih₂ =>
    intro b
    cases b
    case imp u v => simpa using TmEq.imp (ih₁ u) (ih₂ v) (boolAnd_ite_iff.mpr rfl)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | all s b ih =>
    intro b'
    cases b'
    case all t c =>
      simpa using TmEq.all (tpEq_ite s t) (ih c) (boolAnd_ite_iff.mpr rfl)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | typeApp f s ih =>
    intro b
    cases b
    case typeApp g t =>
      simpa using TmEq.tapp (ih g) (tpEq_ite s t) (boolAnd_ite_iff.mpr rfl)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | typeLam b ih =>
    intro b'
    cases b'
    case typeLam c => simpa using TmEq.tlam (ih c)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])
  | typeAll b ih =>
    intro b'
    cases b'
    case typeAll c => simpa using TmEq.tall (ih c)
    all_goals exact tmEq_ite_of_tag_ne (by simp [Tm.tag])

/-- **`tm.eq` is equality of terms**: its one result is `bool.t` on equal terms and `bool.f`
otherwise. -/
theorem tmEq_iff {a b : Tm} {r : MBool} : TmEq a b r ↔ r = if a = b then .t else .f :=
  ⟨tmEq_eq_ite, fun h => h ▸ tmEq_ite a b⟩

theorem tmEq_total (a b : Tm) : ∃ r, TmEq a b r := ⟨_, tmEq_ite a b⟩

theorem tmEq_functional {a b : Tm} {r r' : MBool} (h : TmEq a b r) (h' : TmEq a b r') : r = r' :=
  (tmEq_iff.mp h).trans (tmEq_iff.mp h').symm

/-! ## Interned nodes -/

/-- The label of a node of the interning store: a constructor of `Name`, `Tp` or `Tm`, with the
immediates among its arguments.  The other arguments are the node's children. -/
inductive MgLabel
  /-- `"nm.nil"`; no children. -/
  | nmNil
  /-- `"nm.o"`; one child, the rest of the name. -/
  | nmO
  /-- `"nm.i"`; one child, the rest of the name. -/
  | nmI
  /-- `"Tp.var"` with its index, an immediate; no children. -/
  | tpVar (i : Nat)
  /-- `"Tp.prop"`; no children. -/
  | tpProp
  /-- `"Tp.base"` with its index, an immediate; no children. -/
  | tpBase (i : Nat)
  /-- `"Tp.arr"`; two children. -/
  | tpArr
  /-- `"Tp.all"`; one child. -/
  | tpAll
  /-- `"Tm.db"` with its index, an immediate; no children. -/
  | tmDb (i : Nat)
  /-- `"Tm.named"`; one child, the name. -/
  | tmNamed
  /-- `"Tm.prim"` with its index, an immediate; no children. -/
  | tmPrim (i : Nat)
  /-- `"Tm.app"`; two children. -/
  | tmApp
  /-- `"Tm.lam"`; two children, the type and the body. -/
  | tmLam
  /-- `"Tm.imp"`; two children. -/
  | tmImp
  /-- `"Tm.all"`; two children, the type and the body. -/
  | tmAll
  /-- `"Tm.typeApp"`; two children, the term and the type. -/
  | tmTypeApp
  /-- `"Tm.typeLam"`; one child. -/
  | tmTypeLam
  /-- `"Tm.typeAll"`; one child. -/
  | tmTypeAll
  deriving DecidableEq, Repr, Inhabited

/-- The tree of a name. -/
def encName : Name → Tree MgLabel
  | .nil => .node .nmNil []
  | .o n => .node .nmO [encName n]
  | .i n => .node .nmI [encName n]

/-- The tree of a type. -/
def encTp : Tp → Tree MgLabel
  | .var i => .node (.tpVar i.toNat) []
  | .prop => .node .tpProp []
  | .base i => .node (.tpBase i.toNat) []
  | .arr a b => .node .tpArr [encTp a, encTp b]
  | .all a => .node .tpAll [encTp a]

/-- The tree of a term. -/
def encTm : Tm → Tree MgLabel
  | .db i => .node (.tmDb i.toNat) []
  | .named n => .node .tmNamed [encName n]
  | .prim i => .node (.tmPrim i.toNat) []
  | .app f x => .node .tmApp [encTm f, encTm x]
  | .lam a b => .node .tmLam [encTp a, encTm b]
  | .imp p q => .node .tmImp [encTm p, encTm q]
  | .all a b => .node .tmAll [encTp a, encTm b]
  | .typeApp f a => .node .tmTypeApp [encTm f, encTp a]
  | .typeLam b => .node .tmTypeLam [encTm b]
  | .typeAll b => .node .tmTypeAll [encTm b]

theorem encName_injective : Function.Injective encName := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b
    case nil => rfl
    all_goals simp [encName] at h
  | o a ih =>
    intro b h
    cases b
    case o b => exact congrArg Name.o (ih (by simpa [encName] using h))
    all_goals simp [encName] at h
  | i a ih =>
    intro b h
    cases b
    case i b => exact congrArg Name.i (ih (by simpa [encName] using h))
    all_goals simp [encName] at h

theorem encTp_injective : Function.Injective encTp := by
  intro a
  induction a with
  | var i =>
    intro b h
    cases b
    case var j => exact congrArg Tp.var (UNat.toNat_injective (by simpa [encTp] using h))
    all_goals simp [encTp] at h
  | prop =>
    intro b h
    cases b
    case prop => rfl
    all_goals simp [encTp] at h
  | base i =>
    intro b h
    cases b
    case base j => exact congrArg Tp.base (UNat.toNat_injective (by simpa [encTp] using h))
    all_goals simp [encTp] at h
  | arr a₁ a₂ ih₁ ih₂ =>
    intro b h
    cases b
    case arr c d =>
      simp only [encTp, Tree.node.injEq, List.cons.injEq, true_and, and_true] at h
      rw [ih₁ h.1, ih₂ h.2]
    all_goals simp [encTp] at h
  | all a ih =>
    intro b h
    cases b
    case all c => exact congrArg Tp.all (ih (by simpa [encTp] using h))
    all_goals simp [encTp] at h

theorem encTm_injective : Function.Injective encTm := by
  intro a
  induction a with
  | db i =>
    intro b h
    cases b
    case db j => exact congrArg Tm.db (UNat.toNat_injective (by simpa [encTm] using h))
    all_goals simp [encTm] at h
  | named n =>
    intro b h
    cases b
    case named m => exact congrArg Tm.named (encName_injective (by simpa [encTm] using h))
    all_goals simp [encTm] at h
  | prim i =>
    intro b h
    cases b
    case prim j => exact congrArg Tm.prim (UNat.toNat_injective (by simpa [encTm] using h))
    all_goals simp [encTm] at h
  | app f x ih₁ ih₂ =>
    intro b h
    cases b
    case app g y =>
      simp only [encTm, Tree.node.injEq, List.cons.injEq, true_and, and_true] at h
      rw [ih₁ h.1, ih₂ h.2]
    all_goals simp [encTm] at h
  | lam s b ih =>
    intro b' h
    cases b'
    case lam t c =>
      simp only [encTm, Tree.node.injEq, List.cons.injEq, true_and, and_true] at h
      rw [encTp_injective h.1, ih h.2]
    all_goals simp [encTm] at h
  | imp p q ih₁ ih₂ =>
    intro b h
    cases b
    case imp u v =>
      simp only [encTm, Tree.node.injEq, List.cons.injEq, true_and, and_true] at h
      rw [ih₁ h.1, ih₂ h.2]
    all_goals simp [encTm] at h
  | all s b ih =>
    intro b' h
    cases b'
    case all t c =>
      simp only [encTm, Tree.node.injEq, List.cons.injEq, true_and, and_true] at h
      rw [encTp_injective h.1, ih h.2]
    all_goals simp [encTm] at h
  | typeApp f s ih =>
    intro b h
    cases b
    case typeApp g t =>
      simp only [encTm, Tree.node.injEq, List.cons.injEq, true_and, and_true] at h
      rw [ih h.1, encTp_injective h.2]
    all_goals simp [encTm] at h
  | typeLam b ih =>
    intro b' h
    cases b'
    case typeLam c => exact congrArg Tm.typeLam (ih (by simpa [encTm] using h))
    all_goals simp [encTm] at h
  | typeAll b ih =>
    intro b' h
    cases b'
    case typeAll c => exact congrArg Tm.typeAll (ih (by simpa [encTm] using h))
    all_goals simp [encTm] at h

/-! ### The equality components on interned nodes -/

/-- **The `name.eq` component**: in an interning store, `name.eq` on the names that two nodes in
range read back as answers `bool.t` exactly when the nodes are the same node. -/
theorem nameEq_binding {s : Store MgLabel} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) {x y : Name} (hx : readback s i = encName x)
    (hy : readback s j = encName y) {r : MBool} :
    NameEq x y r ↔ r = if i = j then .t else .f := by
  have e : x = y ↔ i = j := by
    rw [← interning_eq_iff hs hi hj, hx, hy, encName_injective.eq_iff]
  rw [nameEq_iff]
  by_cases h : i = j
  · rw [if_pos h, if_pos (e.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

/-- **The `tp.eq` component**: in an interning store, `tp.eq` on the types that two nodes in range
read back as answers `bool.t` exactly when the nodes are the same node. -/
theorem tpEq_binding {s : Store MgLabel} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) {x y : Tp} (hx : readback s i = encTp x) (hy : readback s j = encTp y)
    {r : MBool} :
    TpEq x y r ↔ r = if i = j then .t else .f := by
  have e : x = y ↔ i = j := by
    rw [← interning_eq_iff hs hi hj, hx, hy, encTp_injective.eq_iff]
  rw [tpEq_iff]
  by_cases h : i = j
  · rw [if_pos h, if_pos (e.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

/-- **The `tm.eq` component**: in an interning store, `tm.eq` on the terms that two nodes in range
read back as answers `bool.t` exactly when the nodes are the same node. -/
theorem tmEq_binding {s : Store MgLabel} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) {x y : Tm} (hx : readback s i = encTm x) (hy : readback s j = encTm y)
    {r : MBool} :
    TmEq x y r ↔ r = if i = j then .t else .f := by
  have e : x = y ↔ i = j := by
    rw [← interning_eq_iff hs hi hj, hx, hy, encTm_injective.eq_iff]
  rw [tmEq_iff]
  by_cases h : i = j
  · rw [if_pos h, if_pos (e.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

/-! ### Interning values bottom-up -/

/-- A name interned bottom-up from the store `s` (`RC_NUL_intern`, `RC_MK1_intern`): the store
after the run and the id of the name's node. -/
def internName (s : Store MgLabel) : Name → Store MgLabel × Nat
  | .nil => intern s ⟨.nmNil, []⟩
  | .o n => let p := internName s n; intern p.1 ⟨.nmO, [p.2]⟩
  | .i n => let p := internName s n; intern p.1 ⟨.nmI, [p.2]⟩

/-- A type interned bottom-up, its children from left to right. -/
def internTp : Store MgLabel → Tp → Store MgLabel × Nat
  | s, .var i => intern s ⟨.tpVar i.toNat, []⟩
  | s, .prop => intern s ⟨.tpProp, []⟩
  | s, .base i => intern s ⟨.tpBase i.toNat, []⟩
  | s, .arr a b =>
    let p := internTp s a
    let q := internTp p.1 b
    intern q.1 ⟨.tpArr, [p.2, q.2]⟩
  | s, .all a => let p := internTp s a; intern p.1 ⟨.tpAll, [p.2]⟩

/-- A term interned bottom-up, its children from left to right. -/
def internTm : Store MgLabel → Tm → Store MgLabel × Nat
  | s, .db i => intern s ⟨.tmDb i.toNat, []⟩
  | s, .named n => let p := internName s n; intern p.1 ⟨.tmNamed, [p.2]⟩
  | s, .prim i => intern s ⟨.tmPrim i.toNat, []⟩
  | s, .app f x =>
    let p := internTm s f
    let q := internTm p.1 x
    intern q.1 ⟨.tmApp, [p.2, q.2]⟩
  | s, .lam a b =>
    let p := internTp s a
    let q := internTm p.1 b
    intern q.1 ⟨.tmLam, [p.2, q.2]⟩
  | s, .imp p q =>
    let p' := internTm s p
    let q' := internTm p'.1 q
    intern q'.1 ⟨.tmImp, [p'.2, q'.2]⟩
  | s, .all a b =>
    let p := internTp s a
    let q := internTm p.1 b
    intern q.1 ⟨.tmAll, [p.2, q.2]⟩
  | s, .typeApp f a =>
    let p := internTm s f
    let q := internTp p.1 a
    intern q.1 ⟨.tmTypeApp, [p.2, q.2]⟩
  | s, .typeLam b => let p := internTm s b; intern p.1 ⟨.tmTypeLam, [p.2]⟩
  | s, .typeAll b => let p := internTm s b; intern p.1 ⟨.tmTypeAll, [p.2]⟩

/-- `Builds s s' k t`: the store `s'` is an interning store that extends `s`, and its node `k`
reads back as `t`. -/
structure Builds (s s' : Store MgLabel) (k : Nat) (t : Tree MgLabel) : Prop where
  interning : Interning s'
  isPrefix : s <+: s'
  lt_length : k < s'.length
  readback_eq : readback s' k = t

theorem Builds.of_prefix {s₀ s s' : Store MgLabel} {k : Nat} {t : Tree MgLabel}
    (h : Builds s s' k t) (h₀ : s₀ <+: s) : Builds s₀ s' k t :=
  ⟨h.interning, h₀.trans h.isPrefix, h.lt_length, h.readback_eq⟩

/-- A node built in a store stays in range and reads back alike in every extension. -/
theorem Builds.mono {s s₁ s₂ : Store MgLabel} {k : Nat} {t : Tree MgLabel}
    (h : Builds s s₁ k t) (h' : s₁ <+: s₂) : k < s₂.length ∧ readback s₂ k = t :=
  ⟨Nat.lt_of_lt_of_le h.lt_length h'.length_le,
    (readback_of_prefix h' h.lt_length).trans h.readback_eq⟩

/-- Interning a node whose children are in range builds the label over their read-backs. -/
theorem builds_intern {s : Store MgLabel} (hs : Interning s) (l : MgLabel) {ks : List Nat}
    {ts : List (Tree MgLabel)} (hk : ∀ k ∈ ks, k < s.length) (ht : ks.map (readback s) = ts) :
    Builds s (intern s ⟨l, ks⟩).1 (intern s ⟨l, ks⟩).2 (.node l ts) :=
  ⟨interning_intern (n := ⟨l, ks⟩) hs hk, prefix_intern s _, lt_length_intern s _, by
    rw [readback_intern (n := ⟨l, ks⟩) hs hk]
    exact congrArg (Tree.node l) ht⟩

/-- Interning a name builds a node that reads back as the name's tree. -/
theorem builds_internName (n : Name) {s : Store MgLabel} (hs : Interning s) :
    Builds s (internName s n).1 (internName s n).2 (encName n) := by
  induction n with
  | nil => exact builds_intern hs _ (by simp) rfl
  | o n ih =>
    exact (builds_intern ih.interning .nmO (ks := [(internName s n).2])
      (by simpa using ih.lt_length) (by simp [ih.readback_eq])).of_prefix ih.isPrefix
  | i n ih =>
    exact (builds_intern ih.interning .nmI (ks := [(internName s n).2])
      (by simpa using ih.lt_length) (by simp [ih.readback_eq])).of_prefix ih.isPrefix

/-- Interning a type builds a node that reads back as the type's tree. -/
theorem builds_internTp (t : Tp) {s : Store MgLabel} (hs : Interning s) :
    Builds s (internTp s t).1 (internTp s t).2 (encTp t) := by
  induction t generalizing s with
  | var i => exact builds_intern hs _ (by simp) rfl
  | prop => exact builds_intern hs _ (by simp) rfl
  | base i => exact builds_intern hs _ (by simp) rfl
  | arr a b iha ihb =>
    have ha := iha hs
    have hb := ihb ha.interning
    obtain ⟨hka, hra⟩ := ha.mono hb.isPrefix
    exact (builds_intern hb.interning .tpArr
      (ks := [(internTp s a).2, (internTp (internTp s a).1 b).2])
      (by simp [hka, hb.lt_length]) (by simp [hra, hb.readback_eq])).of_prefix
      (ha.isPrefix.trans hb.isPrefix)
  | all a ih =>
    have h := ih hs
    exact (builds_intern h.interning .tpAll (ks := [(internTp s a).2])
      (by simpa using h.lt_length) (by simp [h.readback_eq])).of_prefix h.isPrefix

/-- Interning a term builds a node that reads back as the term's tree. -/
theorem builds_internTm (t : Tm) {s : Store MgLabel} (hs : Interning s) :
    Builds s (internTm s t).1 (internTm s t).2 (encTm t) := by
  induction t generalizing s with
  | db i => exact builds_intern hs _ (by simp) rfl
  | named n =>
    have h := builds_internName n hs
    exact (builds_intern h.interning .tmNamed (ks := [(internName s n).2])
      (by simpa using h.lt_length) (by simp [h.readback_eq])).of_prefix h.isPrefix
  | prim i => exact builds_intern hs _ (by simp) rfl
  | app f x ihf ihx =>
    have hf := ihf hs
    have hx := ihx hf.interning
    obtain ⟨hkf, hrf⟩ := hf.mono hx.isPrefix
    exact (builds_intern hx.interning .tmApp
      (ks := [(internTm s f).2, (internTm (internTm s f).1 x).2])
      (by simp [hkf, hx.lt_length]) (by simp [hrf, hx.readback_eq])).of_prefix
      (hf.isPrefix.trans hx.isPrefix)
  | lam a b ih =>
    have ha := builds_internTp a hs
    have hb := ih ha.interning
    obtain ⟨hka, hra⟩ := ha.mono hb.isPrefix
    exact (builds_intern hb.interning .tmLam
      (ks := [(internTp s a).2, (internTm (internTp s a).1 b).2])
      (by simp [hka, hb.lt_length]) (by simp [hra, hb.readback_eq])).of_prefix
      (ha.isPrefix.trans hb.isPrefix)
  | imp p q ihp ihq =>
    have hp := ihp hs
    have hq := ihq hp.interning
    obtain ⟨hkp, hrp⟩ := hp.mono hq.isPrefix
    exact (builds_intern hq.interning .tmImp
      (ks := [(internTm s p).2, (internTm (internTm s p).1 q).2])
      (by simp [hkp, hq.lt_length]) (by simp [hrp, hq.readback_eq])).of_prefix
      (hp.isPrefix.trans hq.isPrefix)
  | all a b ih =>
    have ha := builds_internTp a hs
    have hb := ih ha.interning
    obtain ⟨hka, hra⟩ := ha.mono hb.isPrefix
    exact (builds_intern hb.interning .tmAll
      (ks := [(internTp s a).2, (internTm (internTp s a).1 b).2])
      (by simp [hka, hb.lt_length]) (by simp [hra, hb.readback_eq])).of_prefix
      (ha.isPrefix.trans hb.isPrefix)
  | typeApp f a ih =>
    have hf := ih hs
    have ha := builds_internTp a hf.interning
    obtain ⟨hkf, hrf⟩ := hf.mono ha.isPrefix
    exact (builds_intern ha.interning .tmTypeApp
      (ks := [(internTm s f).2, (internTp (internTm s f).1 a).2])
      (by simp [hkf, ha.lt_length]) (by simp [hrf, ha.readback_eq])).of_prefix
      (hf.isPrefix.trans ha.isPrefix)
  | typeLam b ih =>
    have h := ih hs
    exact (builds_intern h.interning .tmTypeLam (ks := [(internTm s b).2])
      (by simpa using h.lt_length) (by simp [h.readback_eq])).of_prefix h.isPrefix
  | typeAll b ih =>
    have h := ih hs
    exact (builds_intern h.interning .tmTypeAll (ks := [(internTm s b).2])
      (by simpa using h.lt_length) (by simp [h.readback_eq])).of_prefix h.isPrefix

/-- **`name.eq` on interned names**: for two names interned one after the other into an interning
store, `name.eq` answers `bool.t` exactly when the two ids are equal. -/
theorem nameEq_interned {s : Store MgLabel} (hs : Interning s) (x y : Name) {r : MBool} :
    NameEq x y r ↔
      r = if (internName s x).2 = (internName (internName s x).1 y).2 then .t else .f := by
  have hx := builds_internName x hs
  have hy := builds_internName y hx.interning
  obtain ⟨hkx, hrx⟩ := hx.mono hy.isPrefix
  exact nameEq_binding hy.interning hkx hy.lt_length hrx hy.readback_eq

/-- **`tp.eq` on interned types.** -/
theorem tpEq_interned {s : Store MgLabel} (hs : Interning s) (x y : Tp) {r : MBool} :
    TpEq x y r ↔ r = if (internTp s x).2 = (internTp (internTp s x).1 y).2 then .t else .f := by
  have hx := builds_internTp x hs
  have hy := builds_internTp y hx.interning
  obtain ⟨hkx, hrx⟩ := hx.mono hy.isPrefix
  exact tpEq_binding hy.interning hkx hy.lt_length hrx hy.readback_eq

/-- **`tm.eq` on interned terms.** -/
theorem tmEq_interned {s : Store MgLabel} (hs : Interning s) (x y : Tm) {r : MBool} :
    TmEq x y r ↔ r = if (internTm s x).2 = (internTm (internTm s x).1 y).2 then .t else .f := by
  have hx := builds_internTm x hs
  have hy := builds_internTm y hx.interning
  obtain ⟨hkx, hrx⟩ := hx.mono hy.isPrefix
  exact tmEq_binding hy.interning hkx hy.lt_length hrx hy.readback_eq

/-! ## Examples -/

section Examples

/-- `nat.cmp(s z, s (s z))` is `cmp.lt`, by `NAT-CMP-SS` over `NAT-CMP-ZS`. -/
example : NatCmp (.s .z) (.s (.s .z)) .lt := .ss .zs

/-- No rule derives `nat.cmp(s z, z) ~> cmp.eq`. -/
example : ¬ NatCmp (.s .z) .z .eq := nofun

/-- `nat.eq(z, s z)` is `bool.f`, through `NAT-EQ-LT`. -/
example : NatEq .z (.s .z) .f := .lt .zs

/-- No rule derives `nat.eq(z, z) ~> bool.f`. -/
example : ¬ NatEq .z .z .f := by
  rintro (_ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩)

/-- `nat.add(s z, s z) ~> s (s z)`. -/
example : NatAdd (.s .z) (.s .z) (.s (.s .z)) := .s .z

/-- No rule derives `nat.add(s z, z) ~> z`. -/
example : ¬ NatAdd (.s .z) .z .z := nofun

/-- The C comparison, with its glue, answers `nat.cmp` on immediates. -/
example : NatCmp (UNat.ofNat 2) (UNat.ofNat 5) .lt := natCmp_binding.mpr rfl
example : NatCmp (UNat.ofNat 7) (UNat.ofNat 7) .eq := natCmp_binding.mpr rfl
example : ¬ NatCmp (UNat.ofNat 7) (UNat.ofNat 2) .lt := fun h => nomatch natCmp_binding.mp h

/-- The views read an immediate as its numeral. -/
example : UNat.ofNat 3 = .s (.s (.s .z)) := rfl
example : Unary.tag 0 = .z ∧ Unary.tag 3 = .s ∧ Unary.kid 3 = 2 := ⟨rfl, rfl, rfl⟩

/-- The C addition answers the sum up to `natLimit`, the largest value the successor builds, and
refuses just past it. -/
example : cNatAdd 2 3 = some 5 := rfl
example : cNatAdd (natLimit - 1) 1 = some natLimit := rfl
example : cNatAdd natLimit 1 = none := rfl
example : Unary.succ (natLimit - 1) = some natLimit := rfl
example : Unary.succ natLimit = none := rfl

/-- `tp.eq(arr prop prop, arr prop prop) ~> bool.t`, through `TP-EQ-ARR`. -/
example : TpEq (.arr .prop .prop) (.arr .prop .prop) .t := .arr .prop .prop .t

/-- No rule derives `tp.eq(prop, base z) ~> bool.t`. -/
example : ¬ TpEq .prop (.base .z) .t := nofun

/-- `tp.eq(prop, base z) ~> bool.f`, through `TP-EQ-HEADS`. -/
example : TpEq .prop (.base .z) .f := .heads .prop .base (.lt (.ss .zs))

/-- `TP-EQ-HEADS` cannot derive `tp.eq(var z, var (s z))`: the tags are equal. -/
example : ¬ ∃ i j, TpTag (.var .z) i ∧ TpTag (.var (.s .z)) j ∧ NatEq i j .f :=
  tpEq_heads_excludes_sameHead .var

/-- The same, by inversion of the premises. -/
example : ¬ ∃ i j, TpTag (.var .z) i ∧ TpTag (.var (.s .z)) j ∧ NatEq i j .f := by
  rintro ⟨i, j, ⟨⟩, ⟨⟩, _ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩⟩

/-- `tp.eq(var z, var (s z)) ~> bool.f` goes through `TP-EQ-VAR`. -/
example : TpEq (.var .z) (.var (.s .z)) .f := .var (.lt .zs)

/-- `tm.eq` of two different named constants is `bool.f`, through `TM-EQ-NAMED`. -/
example : TmEq (.named (.o .nil)) (.named (.i .nil)) .f := .named .oi

/-- No rule derives `tm.eq` of two different named constants to `bool.t`. -/
example : ¬ TmEq (.named (.o .nil)) (.named (.i .nil)) .t := by
  intro h
  cases h with
  | named h => cases h

/-- `tm.eq` of a named constant and itself is `bool.t`. -/
example : TmEq (.named (.i .nil)) (.named (.i .nil)) .t := .named (.ii .nn)

/-- `TM-EQ-HEADS` on an application and an abstraction. -/
example : TmEq (.app (.db .z) (.db .z)) (.lam .prop (.db .z)) .f :=
  .heads .app .lam (.lt (.ss (.ss (.ss .zs))))

/-- Interning one name twice gives one node; two names, two nodes. -/
example : (internName [] (.o .nil)).2 = (internName (internName [] (.o .nil)).1 (.o .nil)).2 := rfl
example : (internName [] (.o .nil)).2 ≠ (internName (internName [] (.o .nil)).1 (.i .nil)).2 := by
  decide

/-- The pointer test answers `tm.eq` on interned terms. -/
example : TmEq (.named (.o .nil)) (.named (.i .nil)) .f :=
  (tmEq_interned interning_nil _ _).mpr (by decide)

end Examples

end Mettapedia.Languages.Megalodon.RuleModuleBindings

/-! ## Axioms -/

#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.UNat.toNat_ofNat
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.UNat.ofNat_toNat
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.UNat.toNat_injective
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.UNat.ofNat_injective
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.UNat.ofNat_eq_z_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.UNat.ofNat_eq_s_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.Unary.tag_eq_ctor
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.Unary.tag_eq_z_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.Unary.tag_eq_s_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.Unary.succ_eq_some_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.Unary.succ_refines
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.boolAnd_ite_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natCmp_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natCmp_total
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natCmp_functional
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natCmp_eq_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natCmp_binding
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natEq_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natEq_iff_toNat
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natEq_binding
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.natAdd_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.cNatAdd_eq_some_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.cNatAdd_refines
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.cNatAdd_some_iff_in_range
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.cNatAdd_binding
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.nameEq_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpTag_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_total
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_functional
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEqSameHead_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_heads_premises_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_heads_excluded_same_head
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_heads_excludes_sameHead
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmTag_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_total
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_functional
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEqSameHead_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_heads_premises_iff
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_heads_excluded_same_head
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_heads_excludes_sameHead
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.encName_injective
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.encTp_injective
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.encTm_injective
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.nameEq_binding
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_binding
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_binding
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.builds_internName
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.builds_internTp
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.builds_internTm
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.nameEq_interned
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tpEq_interned
#print axioms Mettapedia.Languages.Megalodon.RuleModuleBindings.tmEq_interned
