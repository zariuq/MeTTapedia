import Mettapedia.Logic.HOL.Embedding.ZFSetListClosure
import Mettapedia.SetTheory.ZFSet.OrderedPair
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetEliminators

/-!
# Carriers of simple inductive signatures

A signature is a finite list of constructors, and a constructor is a finite list of
fields. A field is either recursive or one fixed set. The value of constructor `i` at
an argument list is the Kuratowski pair of the numeral `i` with the tuple of the
arguments. The carrier is the least set closed under those values: arguments of
recursive fields lie in the carrier, and arguments of set fields lie in the named set.
It is built as the union of the iterates of one step, starting from the empty set.

Recursion along the constructors, membership in a closed universe that contains `ω`
and every field set, and the natural numbers, lists and leaf-labelled binary trees are
proved from that construction. The numerals, `ω`, and the failure of the least closed
universe around the empty set to contain `ω` are the ones already constructed for the
set tower.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetInductive

open ZFSetHenkinInterpretation ZFSetUniverseClosure ZFSetDependentProducts
open ZFSetIndexedClosure
open Mettapedia.SetTheory.ZFSetOrderedPair
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
  (numeral numeral_injective numeral_mem_omega numeral_succ mem_omega_iff range_numeral
    natOf numeral_natOf natOf_numeral omega_not_mem_univOf_empty finiteSets)
open scoped ZFSet Ordinal

universe u

/-! ## Signatures -/

/-- A field of a simple constructor: recursive, or one fixed set.
`ZFSet` lives one universe above its parameter, so a field does too. -/
inductive Field : Type (u + 1) where
  | recursive : Field
  | ofSet : ZFSet.{u} → Field

/-- A constructor is a list of fields. -/
abbrev Constructor := List Field

/-- A signature is a list of constructors. Constructor `i` is entry `i`. -/
abbrev Signature := List Constructor

/-- The tuple of a list of sets: the empty tuple is `∅`, and cons is a pair. -/
def tuple : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs => ZFSet.pair x (tuple xs)

theorem tuple_cons_ne_empty (x : ZFSet.{u}) (xs : List ZFSet.{u}) : tuple (x :: xs) ≠ ∅ := by
  intro equal
  have member : ({x} : ZFSet.{u}) ∈ tuple (x :: xs) := ZFSet.mem_pair.mpr (Or.inl rfl)
  rw [equal] at member
  exact ZFSet.notMem_empty _ member

theorem tuple_injective : Function.Injective (tuple : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs
  induction xs with
  | nil =>
      intro ys equal
      cases ys with
      | nil => rfl
      | cons y ys => exact (tuple_cons_ne_empty y ys equal.symm).elim
  | cons x xs ih =>
      intro ys equal
      cases ys with
      | nil => exact (tuple_cons_ne_empty x xs equal).elim
      | cons y ys =>
          obtain ⟨head, tail⟩ := ZFSet.pair_inj.mp equal
          exact congrArg₂ List.cons head (ih tail)

/-- The value of constructor `i` at an argument list: the numeral of `i` paired with
the tuple of the arguments. -/
def constructorValue (i : Nat) (args : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (numeral i) (tuple args)

theorem constructorValue_first (i : Nat) (args : List ZFSet.{u}) :
    first (constructorValue i args) = numeral i := by
  rw [constructorValue, first_pair]

theorem constructorValue_second (i : Nat) (args : List ZFSet.{u}) :
    second (constructorValue i args) = tuple args := by
  rw [constructorValue, second_pair]

theorem constructorValue_index {i j : Nat} {args args' : List ZFSet.{u}}
    (equal : constructorValue i args = constructorValue j args') : i = j := by
  have tags := congrArg first equal
  rw [constructorValue_first, constructorValue_first] at tags
  exact numeral_injective tags

theorem constructorValue_args {i j : Nat} {args args' : List ZFSet.{u}}
    (equal : constructorValue i args = constructorValue j args') : args = args' := by
  have tuples := congrArg second equal
  rw [constructorValue_second, constructorValue_second] at tuples
  exact tuple_injective tuples

/-- Constructor values are injective in the index and in the argument list. -/
theorem constructorValue_injective {i j : Nat} {args args' : List ZFSet.{u}} :
    constructorValue i args = constructorValue j args' ↔ i = j ∧ args = args' := by
  constructor
  · intro equal
    exact ⟨constructorValue_index equal, constructorValue_args equal⟩
  · intro ⟨hi, ha⟩
    cases hi
    cases ha
    rfl

/-- Constructors with different indices have different values. -/
theorem constructorValue_ne_of_index_ne {i j : Nat} (distinct : i ≠ j)
    (args args' : List ZFSet.{u}) : constructorValue i args ≠ constructorValue j args' :=
  fun equal => distinct (constructorValue_index equal)

theorem constructorValue_ne_empty (i : Nat) (args : List ZFSet.{u}) :
    constructorValue i args ≠ ∅ := by
  intro equal
  have member : ({numeral i} : ZFSet.{u}) ∈ constructorValue i args :=
    ZFSet.mem_pair.mpr (Or.inl rfl)
  rw [equal] at member
  exact ZFSet.notMem_empty _ member

theorem some_index_lt {α : Type*} {l : List α} {i : Nat} {a : α}
    (present : l[i]? = some a) : i < l.length := by
  induction l generalizing i with
  | nil => cases present
  | cons head tail ih =>
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i => exact Nat.succ_lt_succ (ih present)

/-! ## Fitting arguments -/

/-- Arguments fit a constructor relative to a set of recursive values when the lists
have the same length, each recursive argument lies in that set, and each set-field
argument lies in the field's set. -/
inductive Fits (X : ZFSet.{u}) : List Field → List ZFSet.{u} → Prop where
  | nil : Fits X [] []
  | recursive {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      a ∈ X → Fits X fs args → Fits X (Field.recursive :: fs) (a :: args)
  | ofSet {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      a ∈ A → Fits X fs args → Fits X (Field.ofSet A :: fs) (a :: args)

/-- The same relation with a predicate in place of the set of recursive values. -/
inductive FitsPred (P : ZFSet.{u} → Prop) : List Field → List ZFSet.{u} → Prop where
  | nil : FitsPred P [] []
  | recursive {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      P a → FitsPred P fs args → FitsPred P (Field.recursive :: fs) (a :: args)
  | ofSet {A : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}} {a : ZFSet.{u}} :
      a ∈ A → FitsPred P fs args → FitsPred P (Field.ofSet A :: fs) (a :: args)

theorem Fits.mono {X Y : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}}
    (fitting : Fits X fs args) (subset : X ⊆ Y) : Fits Y fs args := by
  induction fitting with
  | nil => exact Fits.nil
  | recursive member _ ih => exact Fits.recursive (subset member) ih
  | ofSet member _ ih => exact Fits.ofSet member ih

theorem fitsPred_of_fits {X : ZFSet.{u}} {P : ZFSet.{u} → Prop}
    {fs : List Field.{u}} {args : List ZFSet.{u}}
    (fitting : Fits X fs args) (holds : ∀ a, a ∈ X → P a) : FitsPred P fs args := by
  induction fitting with
  | nil => exact FitsPred.nil
  | recursive member _ ih => exact FitsPred.recursive (holds _ member) ih
  | ofSet member _ ih => exact FitsPred.ofSet member ih

theorem fits_of_fitsPred {X : ZFSet.{u}} {fs : List Field.{u}} {args : List ZFSet.{u}}
    (fitting : FitsPred (fun a => a ∈ X) fs args) : Fits X fs args := by
  induction fitting with
  | nil => exact Fits.nil
  | recursive member _ ih => exact Fits.recursive member ih
  | ofSet member _ ih => exact Fits.ofSet member ih

/-! ## One step, as a set -/

/-- Sets of tuples that fit a constructor, with recursive fields drawn from `X`. -/
def argumentSet : List Field.{u} → ZFSet.{u} → ZFSet.{u}
  | [], _ => {∅}
  | Field.recursive :: fs, X => ZFSet.prod X (argumentSet fs X)
  | Field.ofSet A :: fs, X => ZFSet.prod A (argumentSet fs X)

theorem tuple_mem_argumentSet {fs : List Field.{u}} {X : ZFSet.{u}} {args : List ZFSet.{u}}
    (fitting : Fits X fs args) : tuple args ∈ argumentSet fs X := by
  induction fitting with
  | nil => exact ZFSet.mem_singleton.mpr rfl
  | recursive member _ ih => exact ZFSet.pair_mem_prod.mpr ⟨member, ih⟩
  | ofSet member _ ih => exact ZFSet.pair_mem_prod.mpr ⟨member, ih⟩

theorem exists_fits_of_mem_argumentSet {fs : List Field.{u}} {X t : ZFSet.{u}}
    (member : t ∈ argumentSet fs X) : ∃ args, Fits X fs args ∧ tuple args = t := by
  induction fs generalizing t with
  | nil =>
      exact ⟨[], Fits.nil, (ZFSet.mem_singleton.mp member).symm⟩
  | cons field fs ih =>
      cases field with
      | recursive =>
          obtain ⟨a, ha, s, hs, rfl⟩ := ZFSet.mem_prod.mp member
          obtain ⟨args, fitting, rfl⟩ := ih hs
          exact ⟨a :: args, Fits.recursive ha fitting, rfl⟩
      | ofSet A =>
          obtain ⟨a, ha, s, hs, rfl⟩ := ZFSet.mem_prod.mp member
          obtain ⟨args, fitting, rfl⟩ := ih hs
          exact ⟨a :: args, Fits.ofSet ha fitting, rfl⟩

/-- The set of values of one constructor at arguments fitting `X`. -/
noncomputable def constructorImage (i : Nat) (fs : List Field.{u}) (X : ZFSet.{u}) : ZFSet.{u} :=
  replacement (argumentSet fs X) (fun t => ZFSet.pair (numeral i) t)

theorem mem_constructorImage {i : Nat} {fs : List Field.{u}} {X z : ZFSet.{u}} :
    z ∈ constructorImage i fs X ↔
      ∃ args, Fits X fs args ∧ constructorValue i args = z := by
  constructor
  · intro member
    rw [constructorImage, mem_replacement] at member
    obtain ⟨t, ht, hz⟩ := member
    obtain ⟨args, fitting, htuple⟩ := exists_fits_of_mem_argumentSet ht
    exact ⟨args, fitting, (congrArg (fun s => ZFSet.pair (numeral i) s) htuple).trans hz⟩
  · rintro ⟨args, fitting, hz⟩
    rw [constructorImage, mem_replacement]
    exact ⟨tuple args, tuple_mem_argumentSet fitting, hz⟩

/-- Number the constructors from `k`. -/
def enumFrom (k : Nat) : List Constructor.{u} → List (Nat × Constructor.{u})
  | [] => []
  | c :: cs => (k, c) :: enumFrom (k + 1) cs

noncomputable def stepIndexed : List (Nat × Constructor.{u}) → ZFSet.{u} → ZFSet.{u}
  | [], _ => ∅
  | (i, c) :: rest, X => constructorImage i c X ∪ stepIndexed rest X

theorem mem_stepIndexed {k : Nat} {cs : List Constructor.{u}} {X z : ZFSet.{u}} :
    z ∈ stepIndexed (enumFrom k cs) X ↔
      ∃ j c args, cs[j]? = some c ∧ Fits X c args ∧ constructorValue (k + j) args = z := by
  induction cs generalizing k with
  | nil =>
      constructor
      · intro member
        rw [enumFrom, stepIndexed] at member
        exact (ZFSet.notMem_empty z member).elim
      · intro ⟨j, _, _, present, _, _⟩
        exact (Nat.not_lt_zero j (some_index_lt present)).elim
  | cons d ds ih =>
      constructor
      · intro member
        rw [enumFrom] at member
        rw [stepIndexed] at member
        rcases ZFSet.mem_union.mp member with member | member
        · obtain ⟨args, fitting, equal⟩ := mem_constructorImage.mp member
          exact ⟨0, d, args, rfl, fitting, equal⟩
        · obtain ⟨j, c, args, present, fitting, equal⟩ := (ih (k := k + 1)).mp member
          refine ⟨j + 1, c, args, present, fitting, ?_⟩
          rw [show (k + 1) + j = k + (j + 1) by rw [Nat.add_assoc, Nat.add_comm 1 j]] at equal
          exact equal
      · intro ⟨j, c, args, present, fitting, equal⟩
        rw [enumFrom, stepIndexed]
        cases j with
        | zero =>
            have hc : c = d := (Option.some_inj).mp present.symm
            cases hc
            exact ZFSet.mem_union.mpr (Or.inl (mem_constructorImage.mpr ⟨args, fitting, equal⟩))
        | succ j =>
            apply ZFSet.mem_union.mpr ∘ Or.inr
            apply (ih (k := k + 1)).mpr
            refine ⟨j, c, args, present, fitting, ?_⟩
            rw [show k + (j + 1) = (k + 1) + j by rw [Nat.add_assoc, Nat.add_comm 1 j]] at equal
            exact equal

/-- One step of a signature at a set of values already obtained. -/
noncomputable def stepSet (sig : Signature.{u}) (X : ZFSet.{u}) : ZFSet.{u} :=
  stepIndexed (enumFrom 0 sig) X

theorem mem_stepSet {sig : Signature.{u}} {X z : ZFSet.{u}} :
    z ∈ stepSet sig X ↔
      ∃ i c args, sig[i]? = some c ∧ Fits X c args ∧ constructorValue i args = z := by
  rw [stepSet, mem_stepIndexed]
  constructor
  · intro ⟨j, c, args, present, fitting, equal⟩
    exact ⟨j, c, args, present, fitting, by simpa [Nat.zero_add] using equal⟩
  · intro ⟨i, c, args, present, fitting, equal⟩
    exact ⟨i, c, args, present, fitting, by simpa [Nat.zero_add] using equal⟩

theorem stepIndexed_mono {ctors : List (Nat × Constructor.{u})} {X Y : ZFSet.{u}}
    (subset : X ⊆ Y) : stepIndexed ctors X ⊆ stepIndexed ctors Y := by
  induction ctors with
  | nil =>
      intro z member
      rw [stepIndexed] at member
      exact (ZFSet.notMem_empty z member).elim
  | cons head rest ih =>
      cases head with
      | mk i c =>
          intro z member
          rw [stepIndexed] at member
          rw [stepIndexed]
          rcases ZFSet.mem_union.mp member with member | member
          · obtain ⟨args, fitting, equal⟩ := mem_constructorImage.mp member
            exact ZFSet.mem_union.mpr
              (Or.inl (mem_constructorImage.mpr ⟨args, fitting.mono subset, equal⟩))
          · exact ZFSet.mem_union.mpr (Or.inr (ih member))

theorem stepSet_mono {sig : Signature.{u}} {X Y : ZFSet.{u}} (subset : X ⊆ Y) :
    stepSet sig X ⊆ stepSet sig Y :=
  stepIndexed_mono subset

/-! ## The carrier -/

/-- The iterates of one step, starting from the empty set. -/
noncomputable def iterate (sig : Signature.{u}) : Nat → ZFSet.{u}
  | 0 => ∅
  | n + 1 => stepSet sig (iterate sig n)

/-- The carrier: the union of the iterates. -/
noncomputable def carrier (sig : Signature.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (iterate sig))

variable {sig : Signature.{u}}

theorem mem_carrier {x : ZFSet.{u}} : x ∈ carrier sig ↔ ∃ n, x ∈ iterate sig n := by
  constructor
  · intro member
    rw [carrier, ZFSet.mem_sUnion] at member
    obtain ⟨s, hs, hx⟩ := member
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hs
    exact ⟨n, hx⟩
  · intro ⟨n, hx⟩
    rw [carrier, ZFSet.mem_sUnion]
    exact ⟨iterate sig n, ZFSet.mem_range_self (f := iterate sig) n, hx⟩

theorem iterate_succ_subset (n : Nat) : iterate sig n ⊆ iterate sig (n + 1) := by
  induction n with
  | zero =>
      intro x member
      exact (ZFSet.notMem_empty x member).elim
  | succ n ih =>
      intro x member
      rw [iterate] at member
      rw [iterate]
      exact stepSet_mono ih member

theorem iterate_mono {m n : Nat} (hle : m ≤ n) : iterate sig m ⊆ iterate sig n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  subst hk
  clear hle
  induction k with
  | zero =>
      exact fun _ member => member
  | succ k ih =>
      exact fun x member => iterate_succ_subset (m + k) (ih member)

theorem iterate_subset_carrier (n : Nat) : iterate sig n ⊆ carrier sig :=
  fun _ member => mem_carrier.mpr ⟨n, member⟩

theorem exists_bound {c : Constructor.{u}} {args : List ZFSet.{u}}
    (fitting : Fits (carrier sig) c args) : ∃ n, Fits (iterate sig n) c args := by
  induction fitting with
  | nil => exact ⟨0, Fits.nil⟩
  | recursive member _ ih =>
      obtain ⟨k, hk⟩ := mem_carrier.mp member
      obtain ⟨n, hn⟩ := ih
      exact ⟨max k n, Fits.recursive (iterate_mono (Nat.le_max_left k n) hk)
        ((hn).mono (iterate_mono (Nat.le_max_right k n)))⟩
  | ofSet member _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, Fits.ofSet member hn⟩

theorem exists_presentation {n : Nat} {x : ZFSet.{u}} (member : x ∈ iterate sig (n + 1)) :
    ∃ i c args, sig[i]? = some c ∧ Fits (iterate sig n) c args ∧ constructorValue i args = x := by
  rw [iterate, mem_stepSet] at member
  exact member

/-- A constructor at fitting arguments lies in the next iterate. -/
theorem constructor_mem_iterate {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}} {n : Nat}
    (atIndex : sig[i]? = some c) (fitting : Fits (iterate sig n) c args) :
    constructorValue i args ∈ iterate sig (n + 1) := by
  rw [iterate, mem_stepSet]
  exact ⟨i, c, args, atIndex, fitting, rfl⟩

/-- Closure: a constructor at arguments fitting the carrier lies in the carrier. -/
theorem constructor_mem_carrier {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c args) :
    constructorValue i args ∈ carrier sig := by
  obtain ⟨n, hn⟩ := exists_bound fitting
  exact mem_carrier.mpr ⟨n + 1, constructor_mem_iterate atIndex hn⟩

/-- Inversion: every member of the carrier is a constructor at fitting arguments. -/
theorem exists_inversion {x : ZFSet.{u}} (member : x ∈ carrier sig) :
    ∃ i c args, sig[i]? = some c ∧ Fits (carrier sig) c args ∧ constructorValue i args = x := by
  obtain ⟨n, hn⟩ := mem_carrier.mp member
  cases n with
  | zero => exact (ZFSet.notMem_empty x hn).elim
  | succ n =>
      obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_presentation hn
      exact ⟨i, c, args, atIndex, fitting.mono (iterate_subset_carrier n), rfl⟩

/-- The index, the constructor and the argument list in an inversion are unique. -/
theorem inversion_unique {x : ZFSet.{u}} {i j : Nat} {c d : Constructor.{u}}
    {args args' : List ZFSet.{u}}
    (atI : sig[i]? = some c) (atJ : sig[j]? = some d)
    (_fitting : Fits (carrier sig) c args) (_fitting' : Fits (carrier sig) d args')
    (left : constructorValue i args = x) (right : constructorValue j args' = x) :
    i = j ∧ c = d ∧ args = args' := by
  have equal := left.trans right.symm
  have hi := constructorValue_index equal
  have ha := constructorValue_args equal
  cases hi
  cases ha
  have hc : c = d := (Option.some_inj).mp (atI.symm.trans atJ)
  exact ⟨rfl, hc, rfl⟩

theorem iterate_induct {P : ZFSet.{u} → Prop}
    (closed : ∀ i c args, sig[i]? = some c → FitsPred P c args → P (constructorValue i args)) :
    ∀ n x, x ∈ iterate sig n → P x
  | 0, x, member => (ZFSet.notMem_empty x member).elim
  | n + 1, x, member => by
      obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_presentation member
      exact closed i c args atIndex
        (fitsPred_of_fits fitting fun a ha => iterate_induct closed n a ha)

/-- Induction: a predicate closed under the constructors holds on the carrier. -/
theorem carrier_induct {P : ZFSet.{u} → Prop}
    (closed : ∀ i c args, sig[i]? = some c → FitsPred P c args → P (constructorValue i args))
    {x : ZFSet.{u}} (member : x ∈ carrier sig) : P x := by
  obtain ⟨n, hn⟩ := mem_carrier.mp member
  exact iterate_induct closed n x hn

/-- The carrier is the least set closed under the constructors. -/
theorem carrier_subset_of_closed {X : ZFSet.{u}}
    (closed : ∀ i c args, sig[i]? = some c → Fits X c args → constructorValue i args ∈ X) :
    carrier sig ⊆ X := by
  intro x member
  refine carrier_induct (P := fun y => y ∈ X) ?_ member
  intro i c args atIndex fitting
  exact closed i c args atIndex (fits_of_fitsPred fitting)

/-! ## Recursion -/

/-- The results of `f` at the recursive arguments, in order. -/
def mapRec (f : ZFSet.{u} → ZFSet.{u}) : List Field.{u} → List ZFSet.{u} → List ZFSet.{u}
  | Field.recursive :: fs, a :: as => f a :: mapRec f fs as
  | Field.ofSet _ :: fs, _ :: as => mapRec f fs as
  | _, _ => []

theorem mapRec_recursive (f : ZFSet.{u} → ZFSet.{u}) (fs : List Field) (a : ZFSet.{u})
    (as : List ZFSet.{u}) :
    mapRec f (Field.recursive :: fs) (a :: as) = f a :: mapRec f fs as := rfl

theorem mapRec_ofSet (f : ZFSet.{u} → ZFSet.{u}) (A : ZFSet.{u}) (fs : List Field)
    (a : ZFSet.{u}) (as : List ZFSet.{u}) :
    mapRec f (Field.ofSet A :: fs) (a :: as) = mapRec f fs as := rfl

theorem mapRec_nil (f : ZFSet.{u} → ZFSet.{u}) (args : List ZFSet.{u}) :
    mapRec f [] args = [] := rfl

theorem mapRec_congr {f g : ZFSet.{u} → ZFSet.{u}} {X : ZFSet.{u}}
    {fs : List Field.{u}} {args : List ZFSet.{u}}
    (fitting : Fits X fs args) (agree : ∀ a, a ∈ X → f a = g a) :
    mapRec f fs args = mapRec g fs args := by
  induction fitting with
  | nil => rfl
  | recursive member _ ih =>
      have head := agree _ member
      rw [mapRec, mapRec, head, ih]
  | ofSet _ _ ih =>
      rw [mapRec, mapRec, ih]

/-- A presentation of a set as a constructor value over a given stage. -/
structure ConstructorPresentation (sig : Signature.{u}) (X x : ZFSet.{u}) where
  index : Nat
  ctor : Constructor.{u}
  args : List ZFSet.{u}
  atIndex : sig[index]? = some ctor
  fitting : Fits X ctor args
  valueEq : constructorValue index args = x

theorem presentation_unique {X x : ZFSet.{u}}
    (p q : ConstructorPresentation sig X x) :
    p.index = q.index ∧ p.ctor = q.ctor ∧ p.args = q.args := by
  have equal : constructorValue p.index p.args = constructorValue q.index q.args :=
    p.valueEq.trans q.valueEq.symm
  refine ⟨constructorValue_index equal, ?_, constructorValue_args equal⟩
  have sameIndex := constructorValue_index equal
  have tags : some p.ctor = some q.ctor := by
    rw [← p.atIndex, ← q.atIndex, sameIndex]
  exact (Option.some_inj).mp tags

/-- The value of a recursion at stage `n`. Off the iterate the value is unused. -/
noncomputable def evalAt (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) :
    Nat → ZFSet.{u} → ZFSet.{u}
  | 0, _ => ∅
  | n + 1, x =>
      let previous := evalAt onConstructor n
      @Classical.epsilon ZFSet.{u} ⟨∅⟩ fun y =>
        ∀ p : ConstructorPresentation sig (iterate sig n) x,
          y = onConstructor p.index p.args (mapRec previous p.ctor p.args)

theorem evalAt_presentation
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {n : Nat} {x : ZFSet.{u}} (p : ConstructorPresentation sig (iterate sig n) x) :
    evalAt (sig := sig) onConstructor (n + 1) x =
      onConstructor p.index p.args (mapRec (evalAt (sig := sig) onConstructor n) p.ctor p.args) := by
  let pred : ZFSet.{u} → Prop := fun y =>
    ∀ q : ConstructorPresentation sig (iterate sig n) x,
      y = onConstructor q.index q.args (mapRec (evalAt (sig := sig) onConstructor n) q.ctor q.args)
  have existsValue : ∃ y, pred y := by
    refine ⟨onConstructor p.index p.args (mapRec (evalAt (sig := sig) onConstructor n) p.ctor p.args), ?_⟩
    intro q
    obtain ⟨hi, hc, ha⟩ := presentation_unique p q
    rw [hi, hc, ha]
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩ pred existsValue
  change @Classical.epsilon ZFSet.{u} ⟨∅⟩ pred = _
  exact spec p

theorem evalAt_stable (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) :
    ∀ n x, x ∈ iterate sig n → ∀ m, n ≤ m →
      evalAt (sig := sig) onConstructor m x = evalAt (sig := sig) onConstructor n x
  | 0, x, member, _, _ => (ZFSet.notMem_empty x member).elim
  | n + 1, x, member, 0, hle => (Nat.not_succ_le_zero n hle).elim
  | n + 1, x, member, m + 1, hle => by
      have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
      obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_presentation member
      have later : Fits (iterate sig m) c args := fitting.mono (iterate_mono hnm)
      rw [evalAt_presentation onConstructor ⟨i, c, args, atIndex, fitting, rfl⟩,
        evalAt_presentation onConstructor ⟨i, c, args, atIndex, later, rfl⟩]
      apply congrArg (onConstructor i args)
      exact mapRec_congr fitting fun a ha => evalAt_stable onConstructor n a ha m hnm

theorem evalAt_eq_mem (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {m n : Nat} {x : ZFSet.{u}} (hm : x ∈ iterate sig m) (hn : x ∈ iterate sig n) :
    evalAt (sig := sig) onConstructor m x = evalAt (sig := sig) onConstructor n x := by
  rcases Nat.le_total m n with hle | hle
  · exact (evalAt_stable onConstructor m x hm n hle).symm
  · exact evalAt_stable onConstructor n x hn m hle

noncomputable def recOn (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) (member : x ∈ carrier sig) : ZFSet.{u} :=
  evalAt (sig := sig) onConstructor (Classical.choose (mem_carrier.mp member)) x

theorem recOn_spec (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (member : x ∈ carrier sig) {n : Nat} (atStage : x ∈ iterate sig n) :
    recOn (sig := sig) onConstructor x member = evalAt (sig := sig) onConstructor n x :=
  evalAt_eq_mem onConstructor (Classical.choose_spec (mem_carrier.mp member)) atStage

theorem recOn_independent (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (left right : x ∈ carrier sig) :
    recOn (sig := sig) onConstructor x left = recOn (sig := sig) onConstructor x right := by
  unfold recOn
  exact evalAt_eq_mem onConstructor
    (Classical.choose_spec (mem_carrier.mp left))
    (Classical.choose_spec (mem_carrier.mp right))

/-- The recursive function on every set. On the carrier it is the recursion; the value
off the carrier is not used. -/
noncomputable def recFun (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ fun y => ∀ member : x ∈ carrier sig, y = recOn (sig := sig) onConstructor x member

theorem recFun_eq (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (member : x ∈ carrier sig) :
    recFun (sig := sig) onConstructor x = recOn (sig := sig) onConstructor x member := by
  have existsValue : ∃ y, ∀ other : x ∈ carrier sig, y = recOn (sig := sig) onConstructor x other :=
    ⟨recOn (sig := sig) onConstructor x member, fun other => recOn_independent onConstructor member other⟩
  exact Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
    (fun y => ∀ other : x ∈ carrier sig, y = recOn (sig := sig) onConstructor x other) existsValue member

/-- The computation equation at a constructor. -/
theorem recFun_constructor (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c args) :
    recFun (sig := sig) onConstructor (constructorValue i args) =
      onConstructor i args (mapRec (recFun (sig := sig) onConstructor) c args) := by
  obtain ⟨n, atStage⟩ := exists_bound fitting
  have inCarrier := constructor_mem_carrier atIndex fitting
  have inIterate := constructor_mem_iterate atIndex atStage
  rw [recFun_eq onConstructor inCarrier, recOn_spec onConstructor inCarrier inIterate]
  rw [evalAt_presentation onConstructor ⟨i, c, args, atIndex, atStage, rfl⟩]
  apply congrArg (onConstructor i args)
  apply mapRec_congr atStage
  intro a ha
  have aCarrier := iterate_subset_carrier n ha
  rw [recFun_eq onConstructor aCarrier]
  exact (recOn_spec onConstructor aCarrier ha).symm

/-- A function that satisfies the constructor equations agrees with the recursion on
the carrier. -/
theorem recFun_unique (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (g : ZFSet.{u} → ZFSet.{u})
    (equations : ∀ i c args, sig[i]? = some c → Fits (carrier sig) c args →
      g (constructorValue i args) = onConstructor i args (mapRec g c args))
    {x : ZFSet.{u}} (member : x ∈ carrier sig) : g x = recFun (sig := sig) onConstructor x := by
  have agree : ∀ n x, x ∈ iterate sig n → g x = evalAt (sig := sig) onConstructor n x := by
    intro n
    induction n with
    | zero =>
        intro x memberZero
        exact (ZFSet.notMem_empty x memberZero).elim
    | succ n ih =>
        intro x memberSucc
        obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_presentation memberSucc
        have fittingCarrier := fitting.mono (iterate_subset_carrier n)
        rw [equations i c args atIndex fittingCarrier,
          evalAt_presentation onConstructor ⟨i, c, args, atIndex, fitting, rfl⟩]
        apply congrArg (onConstructor i args)
        exact mapRec_congr fitting fun a ha => ih a ha
  obtain ⟨n, atStage⟩ := mem_carrier.mp member
  rw [agree n x atStage, recFun_eq onConstructor member, recOn_spec onConstructor member atStage]

/-! ## Closed universes -/

theorem argumentSet_mem {U X : ZFSet.{u}} (closed : Closed U) (hX : X ∈ U)
    (fs : List Field.{u}) (fields : ∀ A, Field.ofSet A ∈ fs → A ∈ U) :
    argumentSet fs X ∈ U := by
  induction fs with
  | nil => exact closed.singleton_mem (closed.empty_mem hX)
  | cons field fs ih =>
      cases field with
      | recursive =>
          exact closed.product_mem hX
            (ih fun A hA => fields A (List.mem_cons_of_mem _ hA))
      | ofSet A =>
          exact closed.product_mem (fields A List.mem_cons_self)
            (ih fun B hB => fields B (List.mem_cons_of_mem _ hB))

theorem numeral_mem_of_omega {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (i : Nat) : numeral i ∈ U :=
  closed.transitive ZFSet.omega hω (numeral_mem_omega i)

theorem constructorImage_mem {U X : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (hX : X ∈ U) (i : Nat) (fs : List Field.{u}) (fields : ∀ A, Field.ofSet A ∈ fs → A ∈ U) :
    constructorImage i fs X ∈ U := by
  have arguments := argumentSet_mem closed hX fs fields
  refine closed.replacement_mem arguments (fun t => ZFSet.pair (numeral i) t) ?_
  intro t ht
  exact closed.pair_mem (numeral_mem_of_omega closed hω i)
    (closed.transitive (argumentSet fs X) arguments ht)

theorem stepIndexed_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (k : Nat) {cs : List Constructor.{u}} {X : ZFSet.{u}} (hX : X ∈ U)
    (fields : ∀ c, c ∈ cs → ∀ A, Field.ofSet A ∈ c → A ∈ U) :
    stepIndexed (enumFrom k cs) X ∈ U :=
  match cs, fields with
  | [], _ => by
      rw [enumFrom, stepIndexed]
      exact closed.empty_mem hω
  | c :: cs, fields => by
      rw [enumFrom, stepIndexed]
      exact closed.binaryUnion_mem
        (constructorImage_mem closed hω hX k c fun A hA => fields c List.mem_cons_self A hA)
        (stepIndexed_mem closed hω (k + 1) hX
          fun d hd A hA => fields d (List.mem_cons_of_mem _ hd) A hA)

theorem iterate_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (fields : ∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c → A ∈ U) :
    ∀ n, iterate sig n ∈ U
  | 0 => closed.empty_mem hω
  | n + 1 => by
      rw [iterate]
      exact stepIndexed_mem closed hω 0 (iterate_mem closed hω fields n) fields

/-- If `U` is closed, contains `ω`, and contains every field set, the carrier is a member. -/
theorem carrier_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (fields : ∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c → A ∈ U) : carrier sig ∈ U := by
  rw [carrier]
  refine closed.union_mem ?_
  refine range_mem_of_index closed numeral numeral_injective ?_ (iterate sig)
    (iterate_mem closed hω fields)
  rw [range_numeral]
  exact hω

/-! ## The natural numbers -/

/-- Zero, and successor of one recursive argument. -/
def natSignature : Signature.{u} := [[], [Field.recursive]]

def natEmbed : Nat → ZFSet.{u}
  | 0 => constructorValue 0 []
  | n + 1 => constructorValue 1 [natEmbed n]

def natStep (i : Nat) (_args recs : List ZFSet.{u}) : ZFSet.{u} :=
  if i = 0 then numeral 0
  else
    match recs with
    | r :: _ => insert r r
    | [] => ∅

theorem natStep_zero (args recs : List ZFSet.{u}) : natStep 0 args recs = numeral 0 := rfl

theorem natStep_one (a r : ZFSet.{u}) (args recs : List ZFSet.{u}) :
    natStep 1 (a :: args) (r :: recs) = insert r r := rfl

theorem natEmbed_mem : ∀ n, natEmbed n ∈ carrier natSignature
  | 0 => constructor_mem_carrier rfl Fits.nil
  | n + 1 => constructor_mem_carrier rfl (Fits.recursive (natEmbed_mem n) Fits.nil)

theorem natSignature_no_set_field {c : Constructor.{u}} {A : ZFSet.{u}}
    (inSignature : c ∈ natSignature) (inConstructor : Field.ofSet A ∈ c) : False := by
  rcases List.mem_cons.mp inSignature with rfl | inSignature
  · cases inConstructor
  · rcases List.mem_cons.mp inSignature with rfl | inSignature
    · rcases List.mem_cons.mp inConstructor with bad | inConstructor
      · cases bad
      · cases inConstructor
    · cases inSignature

theorem natCarrier_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) :
    carrier natSignature ∈ U :=
  carrier_mem closed hω fun _ hc _ hA => (natSignature_no_set_field hc hA).elim

theorem rec_natEmbed : ∀ n, recFun (sig := natSignature) natStep (natEmbed n) = numeral n
  | 0 => by
      rw [natEmbed, recFun_constructor natStep rfl Fits.nil]
      rfl
  | n + 1 => by
      rw [natEmbed, recFun_constructor natStep rfl (Fits.recursive (natEmbed_mem n) Fits.nil),
        mapRec_recursive, mapRec_nil, rec_natEmbed n, natStep_one, numeral_succ]

theorem exists_natEmbed {x : ZFSet.{u}} (member : x ∈ carrier natSignature) :
    ∃ n, natEmbed n = x := by
  refine carrier_induct (P := fun y => ∃ n, natEmbed n = y) ?_ member
  intro i c args atIndex fitting
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = [] := (Option.some_inj).mp atIndex.symm
      cases hc
      cases fitting
      exact ⟨0, rfl⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = [Field.recursive] := (Option.some_inj).mp atIndex.symm
          cases hc
          cases fitting with
          | recursive memberPred rest =>
              cases rest
              obtain ⟨n, hn⟩ := memberPred
              exact ⟨n + 1, by rw [natEmbed, hn]⟩
      | succ i =>
          exact (Nat.not_lt.mpr (Nat.le_add_left 2 i) bound).elim

theorem natRec_mem {x : ZFSet.{u}} (member : x ∈ carrier natSignature) :
    recFun (sig := natSignature) natStep x ∈ ZFSet.omega := by
  obtain ⟨n, hn⟩ := exists_natEmbed member
  rw [← hn, rec_natEmbed]
  exact numeral_mem_omega n

/-- The carrier of the natural numbers is in bijection with `ω`. Zero is sent to the
empty numeral and successor to successor. -/
noncomputable def natCarrierEquiv :
    Elements (carrier natSignature) ≃ Elements ZFSet.omega.{u} where
  toFun x := ⟨recFun (sig := natSignature) natStep x.1, natRec_mem x.2⟩
  invFun n := ⟨natEmbed (natOf n.1), natEmbed_mem (natOf n.1)⟩
  left_inv x := by
    obtain ⟨n, hn⟩ := exists_natEmbed x.2
    apply Subtype.ext
    change natEmbed (natOf (recFun (sig := natSignature) natStep x.1)) = x.1
    rw [hn.symm, rec_natEmbed, natOf_numeral]
  right_inv n := by
    apply Subtype.ext
    exact (rec_natEmbed (natOf n.1)).trans (numeral_natOf n.2)

theorem natCarrierEquiv_zero :
    (natCarrierEquiv ⟨natEmbed 0, natEmbed_mem 0⟩).1 = numeral 0 :=
  rec_natEmbed 0

theorem natCarrierEquiv_zero_empty :
    (natCarrierEquiv ⟨natEmbed 0, natEmbed_mem 0⟩).1 = ∅ := by
  rw [natCarrierEquiv_zero]
  rfl

theorem natCarrierEquiv_succ (n : Nat) :
    (natCarrierEquiv ⟨natEmbed (n + 1), natEmbed_mem (n + 1)⟩).1 =
      insert (natCarrierEquiv ⟨natEmbed n, natEmbed_mem n⟩).1
        (natCarrierEquiv ⟨natEmbed n, natEmbed_mem n⟩).1 := by
  change recFun (sig := natSignature) natStep (natEmbed (n + 1)) =
    insert (recFun (sig := natSignature) natStep (natEmbed n))
      (recFun (sig := natSignature) natStep (natEmbed n))
  rw [rec_natEmbed, rec_natEmbed, numeral_succ]

theorem rank_gt_first (x y : ZFSet.{u}) : x.rank < (ZFSet.pair x y).rank := by
  calc
    x.rank < ({x} : ZFSet.{u}).rank := ZFSet.rank_lt_of_mem (ZFSet.mem_singleton.mpr rfl)
    _ < (ZFSet.pair x y).rank := ZFSet.rank_lt_of_mem (ZFSet.mem_pair.mpr (Or.inl rfl))

theorem rank_gt_second (x y : ZFSet.{u}) : y.rank < (ZFSet.pair x y).rank := by
  calc
    y.rank < ({x, y} : ZFSet.{u}).rank := ZFSet.rank_lt_of_mem (ZFSet.mem_pair.mpr (Or.inr rfl))
    _ < (ZFSet.pair x y).rank := ZFSet.rank_lt_of_mem (ZFSet.mem_pair.mpr (Or.inr rfl))

theorem natEmbed_rank : ∀ n : Nat, (n : Ordinal.{u}) ≤ (natEmbed n).rank
  | 0 => zero_le
  | n + 1 =>
      (Order.succ_le_succ (natEmbed_rank n)).trans (Order.succ_le_of_lt
        ((rank_gt_first (natEmbed n) ∅).trans
          (rank_gt_second (numeral 1) (ZFSet.pair (natEmbed n) ∅))))

/-- The carrier of the natural numbers is not hereditarily finite: it has members of
every finite rank. -/
theorem natCarrier_not_mem_finiteSets : carrier natSignature ∉ finiteSets.{u} := by
  intro member
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp member)
  have below := ZFSet.rank_lt_of_mem (natEmbed_mem k)
  rw [hk] at below
  exact not_lt_of_ge (natEmbed_rank k) below

/-- Without `ω` in the universe, the carrier of the natural numbers need not be a
member. The least closed universe around the empty set is closed and this signature
has no field set, but that universe lies inside the hereditarily finite sets. -/
theorem natCarrier_not_mem_univOf_empty (h : CofinalInaccessibles.{u}) :
    carrier natSignature ∉ univOf h ∅ :=
  fun member => natCarrier_not_mem_finiteSets (univOf_minimal h
    (ZFSet.mem_vonNeumann.mpr (by rw [ZFSet.rank_empty]; exact Ordinal.omega0_pos))
    finite_universe_closed member)

/-- The same universe fails to contain `ω` (`omega_not_mem_univOf_empty`) and fails to
contain the carrier. -/
theorem nat_carrier_and_omega_outside_least_empty (h : CofinalInaccessibles.{u}) :
    ZFSet.omega ∉ univOf h ∅ ∧ carrier natSignature ∉ univOf h ∅ :=
  ⟨omega_not_mem_univOf_empty h, natCarrier_not_mem_univOf_empty h⟩

/-! ## Lists -/

/-- The empty list, and cons of an element of `A` with a recursive tail. -/
def listSignature (A : ZFSet.{u}) : Signature.{u} := [[], [Field.ofSet A, Field.recursive]]

def ofList {A : ZFSet.{u}} : List (Elements A) → ZFSet.{u}
  | [] => constructorValue 0 []
  | x :: xs => constructorValue 1 [x.1, ofList xs]

def listStep (i : Nat) (args recs : List ZFSet.{u}) : ZFSet.{u} :=
  if i = 0 then ∅
  else
    match args, recs with
    | head :: _, result :: _ => ZFSet.pair head result
    | _, _ => ∅

theorem listStep_zero (args recs : List ZFSet.{u}) : listStep 0 args recs = ∅ := rfl

theorem listStep_one (head result : ZFSet.{u}) (args recs : List ZFSet.{u}) :
    listStep 1 (head :: args) (result :: recs) = ZFSet.pair head result := rfl

theorem ofList_mem {A : ZFSet.{u}} : ∀ xs : List (Elements A), ofList xs ∈ carrier (listSignature A)
  | [] => constructor_mem_carrier rfl Fits.nil
  | x :: xs => constructor_mem_carrier rfl
      (Fits.ofSet x.2 (Fits.recursive (ofList_mem xs) Fits.nil))

theorem rec_ofList {A : ZFSet.{u}} :
    ∀ xs : List (Elements A), recFun (sig := listSignature A) listStep (ofList xs) = ZFSetList.encode xs
  | [] => by
      rw [ofList, ZFSetList.encode_nil, recFun_constructor listStep rfl Fits.nil, mapRec_nil,
        listStep_zero]
  | x :: xs => by
      rw [ofList, ZFSetList.encode_cons,
        recFun_constructor listStep rfl (Fits.ofSet x.2 (Fits.recursive (ofList_mem xs) Fits.nil)),
        mapRec_ofSet, mapRec_recursive, mapRec_nil, rec_ofList xs, listStep_one]

theorem exists_ofList {A x : ZFSet.{u}} (member : x ∈ carrier (listSignature A)) :
    ∃ xs : List (Elements A), ofList xs = x := by
  refine carrier_induct (sig := listSignature A) (P := fun y => ∃ xs, ofList xs = y) ?_ member
  intro i c args atIndex fitting
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = [] := (Option.some_inj).mp atIndex.symm
      cases hc
      cases fitting
      exact ⟨[], rfl⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = [Field.ofSet A, Field.recursive] := (Option.some_inj).mp atIndex.symm
          cases hc
          cases fitting with
          | ofSet headMember tailFit =>
              cases tailFit with
              | recursive tailMember nilFit =>
                  cases nilFit
                  obtain ⟨xs, hxs⟩ := tailMember
                  exact ⟨⟨_, headMember⟩ :: xs, by rw [ofList, hxs]⟩
      | succ i =>
          exact (Nat.not_lt.mpr (Nat.le_add_left 2 i) bound).elim

theorem listRec_mem {A x : ZFSet.{u}} (member : x ∈ carrier (listSignature A)) :
    recFun (sig := listSignature A) listStep x ∈ ZFSetList.listCode A := by
  obtain ⟨xs, hx⟩ := exists_ofList member
  rw [← hx, rec_ofList]
  exact ZFSet.mem_range_self xs

theorem listSignature_field {A B : ZFSet.{u}} {c : Constructor.{u}}
    (inSignature : c ∈ listSignature A) (inConstructor : Field.ofSet B ∈ c) : B = A := by
  rcases List.mem_cons.mp inSignature with rfl | inSignature
  · cases inConstructor
  · rcases List.mem_cons.mp inSignature with rfl | inSignature
    · rcases List.mem_cons.mp inConstructor with same | inConstructor
      · cases same
        rfl
      · rcases List.mem_cons.mp inConstructor with bad | inConstructor
        · cases bad
        · cases inConstructor
    · cases inSignature

/-- Lists lie in any closed universe that contains `ω` and the element set. -/
theorem listCarrier_mem {U A : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (hA : A ∈ U) : carrier (listSignature A) ∈ U :=
  carrier_mem closed hω fun c hc B hB => by
    rw [listSignature_field hc hB]
    exact hA

/-- The carrier is in bijection with the existing list codes, and the bijection sends
the empty constructor to the empty list and cons to cons. -/
noncomputable def listCarrierEquiv (A : ZFSet.{u}) :
    Elements (carrier (listSignature A)) ≃ Elements (ZFSetList.listCode A) where
  toFun x := ⟨recFun (sig := listSignature A) listStep x.1, listRec_mem x.2⟩
  invFun code := ⟨ofList (ZFSetList.decode code), ofList_mem (ZFSetList.decode code)⟩
  left_inv x := by
    obtain ⟨xs, hx⟩ := exists_ofList x.2
    apply Subtype.ext
    change ofList (ZFSetList.decode
      ⟨recFun (sig := listSignature A) listStep x.1, listRec_mem x.2⟩) = x.1
    have recovered : recFun (sig := listSignature A) listStep x.1 = ZFSetList.encode xs := by
      rw [hx.symm]
      exact rec_ofList xs
    have sameCode :
        (⟨recFun (sig := listSignature A) listStep x.1, listRec_mem x.2⟩ :
          Elements (ZFSetList.listCode A)) =
        ZFSetList.encodeValue xs :=
      Subtype.ext recovered
    rw [sameCode, ZFSetList.decode_encode, hx.symm]
  right_inv code := by
    apply Subtype.ext
    exact (rec_ofList (ZFSetList.decode code)).trans (ZFSetList.encode_decode code)

theorem listCarrierEquiv_nil (A : ZFSet.{u}) :
    (listCarrierEquiv A ⟨ofList ([] : List (Elements A)), ofList_mem []⟩).1 =
      (ZFSetList.nil A).1 := by
  change recFun (sig := listSignature A) listStep (ofList ([] : List (Elements A))) =
    ZFSetList.encode ([] : List (Elements A))
  exact rec_ofList []

theorem listCarrierEquiv_cons (A : ZFSet.{u}) (x : Elements A) (xs : List (Elements A)) :
    (listCarrierEquiv A ⟨ofList (x :: xs), ofList_mem (x :: xs)⟩).1 =
      (ZFSetList.cons x (listCarrierEquiv A ⟨ofList xs, ofList_mem xs⟩)).1 := by
  change recFun (sig := listSignature A) listStep (ofList (x :: xs)) =
    ZFSet.pair x.1 (recFun (sig := listSignature A) listStep (ofList xs))
  rw [rec_ofList, rec_ofList, ZFSetList.encode_cons]

/-- The tagged carrier is not the existing list code: the empty set is a list code and
is not a tagged constructor value. The bijection is the relation between them. -/
theorem listCarrier_ne_listCode (A : ZFSet.{u}) :
    carrier (listSignature A) ≠ ZFSetList.listCode A := by
  intro equal
  have emptyCode : (∅ : ZFSet.{u}) ∈ ZFSetList.listCode A :=
    ZFSetList.mem_listCode.mpr ⟨[], ZFSetList.encode_nil⟩
  rw [← equal] at emptyCode
  obtain ⟨i, _, args, _, _, value⟩ := exists_inversion emptyCode
  exact constructorValue_ne_empty i args value

/-! ## Binary trees with a number at each leaf -/

/-- A leaf carries a member of `ω`, and a node has two recursive children. -/
def treeSignature : Signature.{u} := [[Field.ofSet ZFSet.omega], [Field.recursive, Field.recursive]]

def leafValue (n : ZFSet.{u}) : ZFSet.{u} := constructorValue 0 [n]

def nodeValue (left right : ZFSet.{u}) : ZFSet.{u} := constructorValue 1 [left, right]

theorem leafValue_mem {n : ZFSet.{u}} (number : n ∈ ZFSet.omega) :
    leafValue n ∈ carrier treeSignature :=
  constructor_mem_carrier rfl (Fits.ofSet number Fits.nil)

theorem nodeValue_mem {left right : ZFSet.{u}}
    (leftMember : left ∈ carrier treeSignature) (rightMember : right ∈ carrier treeSignature) :
    nodeValue left right ∈ carrier treeSignature :=
  constructor_mem_carrier rfl (Fits.recursive leftMember (Fits.recursive rightMember Fits.nil))

/-- A node whose leaves are the numerals `0` and `1`. -/
def exampleTree : ZFSet.{u} := nodeValue (leafValue (numeral 0)) (leafValue (numeral 1))

theorem exampleTree_mem : exampleTree ∈ carrier treeSignature :=
  nodeValue_mem (leafValue_mem (numeral_mem_omega 0)) (leafValue_mem (numeral_mem_omega 1))

theorem tree_cases {x : ZFSet.{u}} (member : x ∈ carrier treeSignature) :
    (∃ n, n ∈ ZFSet.omega ∧ x = leafValue n) ∨
      (∃ left right, left ∈ carrier treeSignature ∧ right ∈ carrier treeSignature ∧
        x = nodeValue left right) := by
  obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_inversion member
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = [Field.ofSet ZFSet.omega] := (Option.some_inj).mp atIndex.symm
      cases hc
      cases fitting with
      | ofSet number rest =>
          cases rest
          exact Or.inl ⟨_, number, rfl⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = [Field.recursive, Field.recursive] := (Option.some_inj).mp atIndex.symm
          cases hc
          cases fitting with
          | recursive leftMember rest =>
              cases rest with
              | recursive rightMember nilFit =>
                  cases nilFit
                  exact Or.inr ⟨_, _, leftMember, rightMember, rfl⟩
      | succ i =>
          exact (Nat.not_lt.mpr (Nat.le_add_left 2 i) bound).elim

theorem treeSignature_field {B : ZFSet.{u}} {c : Constructor.{u}}
    (inSignature : c ∈ treeSignature) (inConstructor : Field.ofSet B ∈ c) : B = ZFSet.omega := by
  rcases List.mem_cons.mp inSignature with rfl | inSignature
  · rcases List.mem_cons.mp inConstructor with same | inConstructor
    · cases same
      rfl
    · cases inConstructor
  · rcases List.mem_cons.mp inSignature with rfl | inSignature
    · rcases List.mem_cons.mp inConstructor with bad | inConstructor
      · cases bad
      · rcases List.mem_cons.mp inConstructor with bad | inConstructor
        · cases bad
        · cases inConstructor
    · cases inSignature

theorem treeCarrier_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) :
    carrier treeSignature ∈ U :=
  carrier_mem closed hω fun c hc B hB => by
    rw [treeSignature_field hc hB]
    exact hω

/-! ## Negative signatures -/

/-- The signature whose only constructor asks for one recursive argument. -/
def loopSignature : Signature.{u} := [[Field.recursive]]

theorem carrier_eq_empty_of_iterate (emptyIterates : ∀ n, iterate sig n = ∅) :
    carrier sig = ∅ := by
  apply ZFSet.ext
  intro x
  constructor
  · intro member
    obtain ⟨n, atStage⟩ := mem_carrier.mp member
    rw [emptyIterates n] at atStage
    exact (ZFSet.notMem_empty x atStage).elim
  · intro member
    exact (ZFSet.notMem_empty x member).elim

theorem stepSet_loop_empty : stepSet loopSignature ∅ = ∅ := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    rw [stepSet, mem_stepIndexed] at member
    obtain ⟨j, c, args, atIndex, fitting, _⟩ := member
    have jZero : j = 0 := by
      have lengthOne : loopSignature.length = 1 := rfl
      have bound := some_index_lt atIndex
      rw [lengthOne] at bound
      cases j with
      | zero => rfl
      | succ j => exact (Nat.not_succ_le_zero j (Nat.le_of_lt_succ bound)).elim
    cases jZero
    have hc : c = [Field.recursive] := (Option.some_inj).mp atIndex.symm
    cases hc
    cases fitting with
    | recursive inEmpty _ => exact (ZFSet.notMem_empty _ inEmpty).elim
  · intro member
    exact (ZFSet.notMem_empty z member).elim

theorem iterate_loop : ∀ n, iterate loopSignature n = ∅
  | 0 => rfl
  | n + 1 => by rw [iterate, iterate_loop n, stepSet_loop_empty]

theorem loop_carrier_empty : carrier loopSignature = ∅ :=
  carrier_eq_empty_of_iterate iterate_loop

theorem stepSet_no_constructor (X : ZFSet.{u}) : stepSet [] X = ∅ := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    rw [stepSet, mem_stepIndexed] at member
    obtain ⟨j, _, _, atIndex, _, _⟩ := member
    exact (Nat.not_lt_zero j (some_index_lt atIndex)).elim
  · intro member
    exact (ZFSet.notMem_empty z member).elim

theorem iterate_no_constructor : ∀ n, iterate ([] : Signature.{u}) n = ∅
  | 0 => rfl
  | n + 1 => by rw [iterate, stepSet_no_constructor]

/-- A signature with no constructor has the empty carrier. -/
theorem empty_carrier_empty : carrier ([] : Signature.{u}) = ∅ :=
  carrier_eq_empty_of_iterate iterate_no_constructor

/-- A constructor value whose set-field argument lies outside the field set is not in
the carrier. -/
theorem outside_field_not_mem {A x : ZFSet.{u}} (outside : x ∉ A) :
    constructorValue 0 [x] ∉ carrier [[Field.ofSet A]] := by
  intro member
  obtain ⟨i, c, args, atIndex, fitting, equal⟩ := exists_inversion member
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = [Field.ofSet A] := (Option.some_inj).mp atIndex.symm
      cases hc
      have hargs : args = [x] := constructorValue_args equal
      cases hargs
      cases fitting with
      | ofSet inside rest =>
          cases rest
          exact outside inside
  | succ i =>
      exact (Nat.not_succ_le_zero i (Nat.le_of_lt_succ bound)).elim

#print axioms constructorValue_injective
#print axioms constructorValue_ne_of_index_ne
#print axioms constructor_mem_carrier
#print axioms exists_inversion
#print axioms inversion_unique
#print axioms carrier_induct
#print axioms carrier_subset_of_closed
#print axioms recFun_constructor
#print axioms recFun_unique
#print axioms carrier_mem
#print axioms natCarrierEquiv_zero
#print axioms natCarrierEquiv_succ
#print axioms natCarrier_not_mem_univOf_empty
#print axioms nat_carrier_and_omega_outside_least_empty
#print axioms listCarrierEquiv_nil
#print axioms listCarrierEquiv_cons
#print axioms listCarrier_ne_listCode
#print axioms exampleTree_mem
#print axioms tree_cases
#print axioms loop_carrier_empty
#print axioms empty_carrier_empty
#print axioms outside_field_not_mem

end Mettapedia.Logic.HOL.Embedding.ZFSetInductive
