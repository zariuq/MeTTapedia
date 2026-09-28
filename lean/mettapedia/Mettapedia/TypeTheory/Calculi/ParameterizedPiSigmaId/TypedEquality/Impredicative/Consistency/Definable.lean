import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Data
import Mathlib.Data.Countable.Defs

/-!
# Definable functions on the numbers, and choice

In the consistency model a value of the numbers is a class of closed terms
computing one numeral, so it is the value of a numeral; and a value of the data
carrier `num → num` is a class of closed terms that send numerals to numerals.
Such a value applies to a value of the numbers by applying representatives. The
functions on the numbers obtained this way are the *definable* ones.

When the terms are countably many, so are the definable functions, while the
functions `ℕ → ℕ` are not. A diagonal function escapes them: at the number `k`
encoding a closed term it differs from what the term computes at the numeral
`k`.
Deciding whether a term computes a given numeral is not effective, so the
diagonal is defined classically; everything else here is constructive.

The diagonal refutes choice read in the model: its graph is a total and
functional relation on the numbers, and no definable function follows it. So
neither choice nor unique choice holds when relations range over all
predicates while functions range over the definable ones.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

variable {Head : Type}

/-! ## Application of definable functions -/

section Apply

variable {S : DataSetting Head}

/-- A closed function on the numbers applied to a closed number computes a
number. -/
theorem DataEq.app_closed {f a : Tm Head 0} (rf : DataEq S (.arr .num .num) f f)
    (ra : DataEq S .num a a) : DataEq S .num (.app f a) (.app f a) := by
  have h := rf idRen ra
  rwa [rename_id] at h

/-- A value of `num → num` applied to a value of the numbers: the class of the
application of representatives. -/
def Q.apply : Q S (.arr .num .num) → Q S .num → Q S .num :=
  Quot.lift₂ (fun f a => Quot.mk _ ⟨.app f.1 a.1, DataEq.app_closed f.2 a.2⟩)
    (fun f _ _ related => Quot.sound (by
      have h := f.2 idRen related
      rwa [rename_id] at h))
    (fun _ _ a related => Quot.sound (by
      have h := related idRen a.2
      rwa [rename_id, rename_id] at h))

/-- The value of an application is the application of the values. -/
theorem dataValue_app {P : Type} {n : Nat} {f a : Tm Head n}
    (rf : DataEq S (.arr .num .num) f f) (ra : DataEq S .num a a)
    (related : DataEq S .num (.app f a) (.app f a)) :
    dataValue (P := P) S .num (.app f a) related =
      Q.apply (dataValue (P := P) S (.arr .num .num) f rf) (dataValue (P := P) S .num a ra) :=
  rfl

/-- The value of an application of a renamed function is the application of the
values. -/
theorem dataValue_app_rename {P : Type} {n m : Nat} {f : Tm Head n} {a : Tm Head m}
    (ρ : Ren n m) (rf : DataEq S (.arr .num .num) f f) (ra : DataEq S .num a a)
    (related : DataEq S .num (.app (Presentation.rename ρ f) a)
      (.app (Presentation.rename ρ f) a)) :
    dataValue (P := P) S .num (.app (Presentation.rename ρ f) a) related =
      Q.apply (dataValue (P := P) S (.arr .num .num) f rf) (dataValue (P := P) S .num a ra) :=
  congrArg (Quot.mk _) (Subtype.ext (congrArg (fun t => Tm.app t (close S a))
    (close_rename ρ f)))

end Apply

/-! ## The numbers and the definable functions of a setting -/

section Numerals

variable {T : Setting Head}

/-- Every value of the numbers is the value of a numeral. -/
theorem Q.eq_numClass (q : Q T.numerals .num) : ∃ k, q = numClass T.numerals k := by
  induction q using Quot.ind with
  | mk a =>
      obtain ⟨k, value, _⟩ := a.2
      exact ⟨k, Quot.sound ⟨k, value, numVal_numeral k⟩⟩

/-- A value of `num → num` sends the value of the numeral `k` to that of `j`
only when a representative computes `j` at the numeral `k`. -/
theorem Q.numVal_of_apply (laws : T.Laws) {f : Realizer (S := T.numerals) (.arr .num .num)}
    {k j : Nat} (h : Q.apply (Quot.mk _ f) (numClass T.numerals k) = numClass T.numerals j) :
    NumVal T (.app f.1 (numeral T k)) j := by
  obtain ⟨i, value, numeralValue⟩ := Q.exact laws.numerals h
  rw [NumVal.deterministic laws numeralValue (numVal_numeral j)] at value
  exact value

/-- **The diagonal.** When the closed terms are countably many, some function on
the natural numbers is computed by no closed term. Deciding whether a term
computes `0` at a numeral is classical. -/
theorem exists_undefinable (laws : T.Laws) [Countable (Tm Head 0)] :
    ∃ D : Nat → Nat, ∀ t : Tm Head 0, ∃ k, ¬ NumVal T (.app t (numeral T k)) (D k) := by
  classical
  obtain ⟨encode, injective⟩ := Countable.exists_injective_nat (Tm Head 0)
  refine ⟨fun k => if ∃ t, encode t = k ∧ NumVal T (.app t (numeral T k)) 0 then 1 else 0,
    fun t => ⟨encode t, fun value => ?_⟩⟩
  beta_reduce at value
  split_ifs at value with h
  · obtain ⟨t', same, zero⟩ := h
    rw [injective same] at zero
    exact absurd (NumVal.deterministic laws zero value) (by decide)
  · exact h ⟨t, rfl, value⟩

/-- Some function on the natural numbers is the application of no value of
`num → num`. -/
theorem exists_not_apply (laws : T.Laws) [Countable (Tm Head 0)] :
    ∃ D : Nat → Nat, ∀ f : Q T.numerals (.arr .num .num), ∃ k,
      Q.apply f (numClass T.numerals k) ≠ numClass T.numerals (D k) := by
  obtain ⟨D, undefinable⟩ := exists_undefinable laws
  refine ⟨D, fun f => ?_⟩
  induction f using Quot.ind with
  | mk f =>
      obtain ⟨k, notValue⟩ := undefinable f.1
      exact ⟨k, fun h => notValue (Q.numVal_of_apply laws h)⟩

/-! ## Choice read with definable functions -/

variable (T)

/-- A relation on the numbers is total, with existence written impredicatively:
at each number, every proposition that follows from each witness holds. -/
def TotalRelation (R : Q T.numerals .num → Q T.numerals .num → Prop) : Prop :=
  ∀ x, ∀ C : Prop, (∀ y, R x y → C) → C

/-- A relation on the numbers relates each number to at most one number. -/
def FunctionalRelation (R : Q T.numerals .num → Q T.numerals .num → Prop) : Prop :=
  ∀ x y y', R x y → R x y' → y = y'

/-- Some value of `num → num` follows the relation, with existence written
impredicatively. -/
def HasDefinableChoice (R : Q T.numerals .num → Q T.numerals .num → Prop) : Prop :=
  ∀ C : Prop, (∀ f : Q T.numerals (.arr .num .num), (∀ x, R x (Q.apply f x)) → C) → C

/-- Choice with definable functions: every total relation on the numbers is
followed by a value of `num → num`. -/
def DefinableChoice : Prop :=
  ∀ R : Q T.numerals .num → Q T.numerals .num → Prop,
    TotalRelation T R → HasDefinableChoice T R

/-- Unique choice with definable functions: every total functional relation on
the numbers is followed by a value of `num → num`. -/
def DefinableUniqueChoice : Prop :=
  ∀ R : Q T.numerals .num → Q T.numerals .num → Prop,
    TotalRelation T R → FunctionalRelation T R → HasDefinableChoice T R

variable {T}

/-- The impredicative existentials are the existentials. -/
theorem totalRelation_iff (R : Q T.numerals .num → Q T.numerals .num → Prop) :
    TotalRelation T R ↔ ∀ x, ∃ y, R x y :=
  ⟨fun total x => total x _ fun y h => ⟨y, h⟩,
    fun total x _ h => (total x).elim fun y hy => h y hy⟩

/-- A definable choice function, written impredicatively, is one that exists. -/
theorem hasDefinableChoice_iff (R : Q T.numerals .num → Q T.numerals .num → Prop) :
    HasDefinableChoice T R ↔ ∃ f : Q T.numerals (.arr .num .num), ∀ x, R x (Q.apply f x) :=
  ⟨fun chosen => chosen _ fun f h => ⟨f, h⟩, fun ⟨f, h⟩ _ k => k f h⟩

theorem DefinableChoice.unique (choice : DefinableChoice T) : DefinableUniqueChoice T :=
  fun R total _ => choice R total

/-- **Unique choice fails with definable functions.** The graph of the
diagonal is total and functional, and no value of `num → num` follows it. -/
theorem not_definableUniqueChoice (laws : T.Laws) [Countable (Tm Head 0)] :
    ¬ DefinableUniqueChoice T := by
  intro choice
  obtain ⟨D, escapes⟩ := exists_not_apply laws
  refine choice (fun x y => ∃ k, x = numClass T.numerals k ∧ y = numClass T.numerals (D k))
    (fun x C h => ?_) (fun _ _ _ ⟨k, hx, hy⟩ ⟨k', hx', hy'⟩ => ?_) False
    (fun f chosen => ?_)
  · obtain ⟨k, rfl⟩ := Q.eq_numClass x
    exact h _ ⟨k, rfl, rfl⟩
  · obtain rfl := numClass_injective laws.numerals (hx.symm.trans hx')
    exact hy.trans hy'.symm
  · obtain ⟨k, differs⟩ := escapes f
    obtain ⟨k', same, value⟩ := chosen (numClass T.numerals k)
    rw [← numClass_injective laws.numerals same] at value
    exact differs value

/-- **Choice fails with definable functions.** -/
theorem not_definableChoice (laws : T.Laws) [Countable (Tm Head 0)] : ¬ DefinableChoice T :=
  fun choice => not_definableUniqueChoice laws choice.unique

end Numerals

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
