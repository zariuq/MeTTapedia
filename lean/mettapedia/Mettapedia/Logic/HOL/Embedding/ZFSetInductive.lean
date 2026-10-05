import Mettapedia.Logic.HOL.Embedding.ZFSetListClosure
import Mettapedia.SetTheory.ZFSet.OrderedPair
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetEliminators

/-!
# Carriers of simple inductive signatures

A signature is a finite list of constructors. A constructor has a tag, which is a set, and
a finite list of fields; a field is either recursive or one fixed set. The value of a
constructor at an argument list is the Kuratowski pair of its tag with the tuple of the
arguments. Nothing else enters the value: not the position of the constructor in its
signature, and not the signature. The carrier is the least set closed under those values:
arguments of recursive fields lie in the carrier, and arguments of set fields lie in the
named set. It is built as the union of the iterates of one step, starting from the empty
set.

Constructors are addressed by their position in the signature. Closure, inversion,
induction, and membership of the carrier in a closed universe that contains `ω`, every tag
and every field set, hold for every signature. That a member is the value of one
constructor at one argument list, and recursion along the constructors, need that no two
constructors carry one tag (`DistinctTags`). A constructor value whose tag the signature
does not have is outside the carrier (`constructorValue_not_mem_carrier`), so the carriers
of two signatures with no tag in common are disjoint (`carrier_disjoint`).

The natural numbers, lists and leaf-labelled binary trees are proved from that
construction; their constructors carry the numerals `0` and `1`. The numerals, `ω`, and the
failure of the least closed universe around the empty set to contain `ω` are the ones
already constructed for the set tower.

Negative examples: a signature whose only constructor is recursive, and a signature with no
constructor, have the empty carrier; an argument outside a field's set gives no member; and
with one tag on two constructors a member is the value of both, and the equations of a
recursion that tells the two apart have no solution (`sharedTag_two_presentations`,
`sharedTag_no_recursion`).

**Names as tags.** A tag may be any set. The code of a name (`nameCode`) is built from
numerals and pairs by recursion on the name, a string being read through the bytes of its
UTF-8 encoding (`stringCode`); different names have different codes
(`nameCode_injective`), and the code is a member of every closed universe that has `ω` as a
member (`nameCode_mem`). A first-order data term is a name applied to a list of data terms
(`DataTerm`). Its set is the constructor value of the code of its name at the sets of its
arguments (`DataTerm.toSet`), and two data terms have one set exactly when they are the same
term (`DataTerm.toSet_eq_iff`). No signature and no typing enters that reading.
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

/-- A constructor: the tag its values carry, and its fields. -/
structure Constructor : Type (u + 1) where
  tag : ZFSet.{u}
  fields : List Field.{u}

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

/-- The value of a constructor with tag `t` at an argument list: the tag paired with the
tuple of the arguments. -/
def constructorValue (t : ZFSet.{u}) (args : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair t (tuple args)

theorem constructorValue_first (t : ZFSet.{u}) (args : List ZFSet.{u}) :
    first (constructorValue t args) = t := by
  rw [constructorValue, first_pair]

theorem constructorValue_second (t : ZFSet.{u}) (args : List ZFSet.{u}) :
    second (constructorValue t args) = tuple args := by
  rw [constructorValue, second_pair]

theorem constructorValue_tag {s t : ZFSet.{u}} {args args' : List ZFSet.{u}}
    (equal : constructorValue s args = constructorValue t args') : s = t := by
  have tags := congrArg first equal
  rw [constructorValue_first, constructorValue_first] at tags
  exact tags

theorem constructorValue_args {s t : ZFSet.{u}} {args args' : List ZFSet.{u}}
    (equal : constructorValue s args = constructorValue t args') : args = args' := by
  have tuples := congrArg second equal
  rw [constructorValue_second, constructorValue_second] at tuples
  exact tuple_injective tuples

/-- Constructor values are injective in the tag and in the argument list. -/
theorem constructorValue_injective {s t : ZFSet.{u}} {args args' : List ZFSet.{u}} :
    constructorValue s args = constructorValue t args' ↔ s = t ∧ args = args' := by
  constructor
  · intro equal
    exact ⟨constructorValue_tag equal, constructorValue_args equal⟩
  · intro ⟨hs, ha⟩
    cases hs
    cases ha
    rfl

/-- Different tags give different values. -/
theorem constructorValue_ne_of_tag_ne {s t : ZFSet.{u}} (distinct : s ≠ t)
    (args args' : List ZFSet.{u}) : constructorValue s args ≠ constructorValue t args' :=
  fun equal => distinct (constructorValue_tag equal)

theorem constructorValue_ne_empty (t : ZFSet.{u}) (args : List ZFSet.{u}) :
    constructorValue t args ≠ ∅ := by
  intro equal
  have member : ({t} : ZFSet.{u}) ∈ constructorValue t args :=
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

/-- The set of values of a constructor with tag `t` and fields `fs` at arguments fitting
`X`. -/
noncomputable def constructorImage (t : ZFSet.{u}) (fs : List Field.{u}) (X : ZFSet.{u}) :
    ZFSet.{u} :=
  replacement (argumentSet fs X) (fun s => ZFSet.pair t s)

theorem mem_constructorImage {t : ZFSet.{u}} {fs : List Field.{u}} {X z : ZFSet.{u}} :
    z ∈ constructorImage t fs X ↔
      ∃ args, Fits X fs args ∧ constructorValue t args = z := by
  constructor
  · intro member
    rw [constructorImage, mem_replacement] at member
    obtain ⟨s, hs, hz⟩ := member
    obtain ⟨args, fitting, htuple⟩ := exists_fits_of_mem_argumentSet hs
    exact ⟨args, fitting, (congrArg (fun r => ZFSet.pair t r) htuple).trans hz⟩
  · rintro ⟨args, fitting, hz⟩
    rw [constructorImage, mem_replacement]
    exact ⟨tuple args, tuple_mem_argumentSet fitting, hz⟩

/-- One step of a signature at a set of values already obtained: the values of every
constructor at arguments that fit. -/
noncomputable def stepSet : Signature.{u} → ZFSet.{u} → ZFSet.{u}
  | [], _ => ∅
  | c :: cs, X => constructorImage c.tag c.fields X ∪ stepSet cs X

theorem mem_stepSet {sig : Signature.{u}} {X z : ZFSet.{u}} :
    z ∈ stepSet sig X ↔
      ∃ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
        sig[i]? = some c ∧ Fits X c.fields args ∧ constructorValue c.tag args = z := by
  induction sig with
  | nil =>
      constructor
      · intro member
        rw [stepSet] at member
        exact (ZFSet.notMem_empty z member).elim
      · intro ⟨i, _, _, present, _, _⟩
        exact (Nat.not_lt_zero i (some_index_lt present)).elim
  | cons d ds ih =>
      constructor
      · intro member
        rw [stepSet] at member
        rcases ZFSet.mem_union.mp member with member | member
        · obtain ⟨args, fitting, equal⟩ := mem_constructorImage.mp member
          exact ⟨0, d, args, rfl, fitting, equal⟩
        · obtain ⟨j, c, args, present, fitting, equal⟩ := ih.mp member
          exact ⟨j + 1, c, args, present, fitting, equal⟩
      · intro ⟨j, c, args, present, fitting, equal⟩
        rw [stepSet]
        cases j with
        | zero =>
            have hc : c = d := (Option.some_inj).mp present.symm
            cases hc
            exact ZFSet.mem_union.mpr (Or.inl (mem_constructorImage.mpr ⟨args, fitting, equal⟩))
        | succ j =>
            exact ZFSet.mem_union.mpr (Or.inr (ih.mpr ⟨j, c, args, present, fitting, equal⟩))

theorem stepSet_mono {sig : Signature.{u}} {X Y : ZFSet.{u}} (subset : X ⊆ Y) :
    stepSet sig X ⊆ stepSet sig Y := by
  intro z member
  obtain ⟨i, c, args, present, fitting, equal⟩ := mem_stepSet.mp member
  exact mem_stepSet.mpr ⟨i, c, args, present, fitting.mono subset, equal⟩

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

theorem exists_bound {fs : List Field.{u}} {args : List ZFSet.{u}}
    (fitting : Fits (carrier sig) fs args) : ∃ n, Fits (iterate sig n) fs args := by
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
    ∃ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
      sig[i]? = some c ∧ Fits (iterate sig n) c.fields args ∧ constructorValue c.tag args = x := by
  rw [iterate, mem_stepSet] at member
  exact member

/-- A constructor at fitting arguments lies in the next iterate. -/
theorem constructor_mem_iterate {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}} {n : Nat}
    (atIndex : sig[i]? = some c) (fitting : Fits (iterate sig n) c.fields args) :
    constructorValue c.tag args ∈ iterate sig (n + 1) := by
  rw [iterate, mem_stepSet]
  exact ⟨i, c, args, atIndex, fitting, rfl⟩

/-- Closure: a constructor at arguments fitting the carrier lies in the carrier. -/
theorem constructor_mem_carrier {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c.fields args) :
    constructorValue c.tag args ∈ carrier sig := by
  obtain ⟨n, hn⟩ := exists_bound fitting
  exact mem_carrier.mpr ⟨n + 1, constructor_mem_iterate atIndex hn⟩

/-- Inversion: every member of the carrier is a constructor at fitting arguments. -/
theorem exists_inversion {x : ZFSet.{u}} (member : x ∈ carrier sig) :
    ∃ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
      sig[i]? = some c ∧ Fits (carrier sig) c.fields args ∧ constructorValue c.tag args = x := by
  obtain ⟨n, hn⟩ := mem_carrier.mp member
  cases n with
  | zero => exact (ZFSet.notMem_empty x hn).elim
  | succ n =>
      obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_presentation hn
      exact ⟨i, c, args, atIndex, fitting.mono (iterate_subset_carrier n), rfl⟩

/-- A constructor value whose tag no constructor of the signature carries is not in the
carrier. -/
theorem constructorValue_not_mem_carrier {t : ZFSet.{u}} {args : List ZFSet.{u}}
    (foreign : ∀ c, c ∈ sig → c.tag ≠ t) : constructorValue t args ∉ carrier sig := by
  intro member
  obtain ⟨_, c, _, atIndex, _, equal⟩ := exists_inversion member
  exact foreign c (List.mem_of_getElem? atIndex) (constructorValue_tag equal)

/-- **The carriers of two signatures with no tag in common are disjoint.** -/
theorem carrier_disjoint {sig₁ sig₂ : Signature.{u}}
    (apart : ∀ c, c ∈ sig₁ → ∀ d, d ∈ sig₂ → c.tag ≠ d.tag) {x : ZFSet.{u}}
    (member : x ∈ carrier sig₁) : x ∉ carrier sig₂ := by
  obtain ⟨_, c, _, atIndex, _, rfl⟩ := exists_inversion member
  exact constructorValue_not_mem_carrier fun d inSecond same =>
    apart c (List.mem_of_getElem? atIndex) d inSecond same.symm

/-! ## Distinct tags -/

/-- **No two constructors of the signature carry one tag.** With this, a member of the
carrier is the value of one constructor at one argument list, and recursion along the
constructors is defined. -/
def DistinctTags (sig : Signature.{u}) : Prop :=
  (sig.map Constructor.tag).Nodup

/-- With distinct tags, two constructors of the signature with one tag stand at one
position. -/
theorem DistinctTags.index_eq (distinct : DistinctTags sig) {i j : Nat} {c d : Constructor.{u}}
    (atI : sig[i]? = some c) (atJ : sig[j]? = some d) (sameTag : c.tag = d.tag) : i = j := by
  have bound : i < (sig.map Constructor.tag).length := by
    rw [List.length_map]
    exact some_index_lt atI
  have tagI : (sig.map Constructor.tag)[i]? = some c.tag := by
    rw [List.getElem?_map, atI]
    rfl
  have tagJ : (sig.map Constructor.tag)[j]? = some d.tag := by
    rw [List.getElem?_map, atJ]
    rfl
  exact (List.getElem?_inj bound distinct).mp (by rw [tagI, tagJ, sameTag])

/-- Two constructors with different tags have distinct tags. -/
theorem distinctTags_pair {c d : Constructor.{u}} (distinct : c.tag ≠ d.tag) :
    DistinctTags [c, d] :=
  List.nodup_cons.mpr
    ⟨fun member => distinct (List.mem_singleton.mp member), List.nodup_singleton d.tag⟩

/-- With distinct tags, the index, the constructor and the argument list in an inversion are
unique. -/
theorem inversion_unique (distinct : DistinctTags sig) {x : ZFSet.{u}} {i j : Nat}
    {c d : Constructor.{u}} {args args' : List ZFSet.{u}}
    (atI : sig[i]? = some c) (atJ : sig[j]? = some d)
    (_fitting : Fits (carrier sig) c.fields args) (_fitting' : Fits (carrier sig) d.fields args')
    (left : constructorValue c.tag args = x) (right : constructorValue d.tag args' = x) :
    i = j ∧ c = d ∧ args = args' := by
  have equal := left.trans right.symm
  have hi := distinct.index_eq atI atJ (constructorValue_tag equal)
  have ha := constructorValue_args equal
  cases hi
  cases ha
  have hc : c = d := (Option.some_inj).mp (atI.symm.trans atJ)
  exact ⟨rfl, hc, rfl⟩

/-! ## Induction -/

theorem iterate_induct {P : ZFSet.{u} → Prop}
    (closed : ∀ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
      sig[i]? = some c → FitsPred P c.fields args → P (constructorValue c.tag args)) :
    ∀ n x, x ∈ iterate sig n → P x
  | 0, x, member => (ZFSet.notMem_empty x member).elim
  | n + 1, x, member => by
      obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_presentation member
      exact closed i c args atIndex
        (fitsPred_of_fits fitting fun a ha => iterate_induct closed n a ha)

/-- Induction: a predicate closed under the constructors holds on the carrier. -/
theorem carrier_induct {P : ZFSet.{u} → Prop}
    (closed : ∀ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
      sig[i]? = some c → FitsPred P c.fields args → P (constructorValue c.tag args))
    {x : ZFSet.{u}} (member : x ∈ carrier sig) : P x := by
  obtain ⟨n, hn⟩ := mem_carrier.mp member
  exact iterate_induct closed n x hn

/-- The carrier is the least set closed under the constructors. -/
theorem carrier_subset_of_closed {X : ZFSet.{u}}
    (closed : ∀ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
      sig[i]? = some c → Fits X c.fields args → constructorValue c.tag args ∈ X) :
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
  fitting : Fits X ctor.fields args
  valueEq : constructorValue ctor.tag args = x

/-- With distinct tags, a set has one presentation over a stage. -/
theorem presentation_unique (distinct : DistinctTags sig) {X x : ZFSet.{u}}
    (p q : ConstructorPresentation sig X x) :
    p.index = q.index ∧ p.ctor = q.ctor ∧ p.args = q.args := by
  have equal : constructorValue p.ctor.tag p.args = constructorValue q.ctor.tag q.args :=
    p.valueEq.trans q.valueEq.symm
  have sameIndex := distinct.index_eq p.atIndex q.atIndex (constructorValue_tag equal)
  refine ⟨sameIndex, ?_, constructorValue_args equal⟩
  have ctors : some p.ctor = some q.ctor := by
    rw [← p.atIndex, ← q.atIndex, sameIndex]
  exact (Option.some_inj).mp ctors

/-- The value of a recursion at stage `n`. Off the iterate the value is unused. -/
noncomputable def evalAt (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) :
    Nat → ZFSet.{u} → ZFSet.{u}
  | 0, _ => ∅
  | n + 1, x =>
      let previous := evalAt onConstructor n
      @Classical.epsilon ZFSet.{u} ⟨∅⟩ fun y =>
        ∀ p : ConstructorPresentation sig (iterate sig n) x,
          y = onConstructor p.index p.args (mapRec previous p.ctor.fields p.args)

theorem evalAt_presentation (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {n : Nat} {x : ZFSet.{u}} (p : ConstructorPresentation sig (iterate sig n) x) :
    evalAt (sig := sig) onConstructor (n + 1) x =
      onConstructor p.index p.args
        (mapRec (evalAt (sig := sig) onConstructor n) p.ctor.fields p.args) := by
  let pred : ZFSet.{u} → Prop := fun y =>
    ∀ q : ConstructorPresentation sig (iterate sig n) x,
      y = onConstructor q.index q.args
        (mapRec (evalAt (sig := sig) onConstructor n) q.ctor.fields q.args)
  have existsValue : ∃ y, pred y := by
    refine ⟨onConstructor p.index p.args
      (mapRec (evalAt (sig := sig) onConstructor n) p.ctor.fields p.args), ?_⟩
    intro q
    obtain ⟨hi, hc, ha⟩ := presentation_unique distinct p q
    rw [hi, hc, ha]
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩ pred existsValue
  change @Classical.epsilon ZFSet.{u} ⟨∅⟩ pred = _
  exact spec p

theorem evalAt_stable (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}) :
    ∀ n x, x ∈ iterate sig n → ∀ m, n ≤ m →
      evalAt (sig := sig) onConstructor m x = evalAt (sig := sig) onConstructor n x
  | 0, x, member, _, _ => (ZFSet.notMem_empty x member).elim
  | n + 1, x, member, 0, hle => (Nat.not_succ_le_zero n hle).elim
  | n + 1, x, member, m + 1, hle => by
      have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
      obtain ⟨i, c, args, atIndex, fitting, rfl⟩ := exists_presentation member
      have later : Fits (iterate sig m) c.fields args := fitting.mono (iterate_mono hnm)
      rw [evalAt_presentation distinct onConstructor ⟨i, c, args, atIndex, fitting, rfl⟩,
        evalAt_presentation distinct onConstructor ⟨i, c, args, atIndex, later, rfl⟩]
      apply congrArg (onConstructor i args)
      exact mapRec_congr fitting fun a ha => evalAt_stable distinct onConstructor n a ha m hnm

theorem evalAt_eq_mem (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {m n : Nat} {x : ZFSet.{u}} (hm : x ∈ iterate sig m) (hn : x ∈ iterate sig n) :
    evalAt (sig := sig) onConstructor m x = evalAt (sig := sig) onConstructor n x := by
  rcases Nat.le_total m n with hle | hle
  · exact (evalAt_stable distinct onConstructor m x hm n hle).symm
  · exact evalAt_stable distinct onConstructor n x hn m hle

noncomputable def recOn (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) (member : x ∈ carrier sig) : ZFSet.{u} :=
  evalAt (sig := sig) onConstructor (Classical.choose (mem_carrier.mp member)) x

theorem recOn_spec (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (member : x ∈ carrier sig) {n : Nat} (atStage : x ∈ iterate sig n) :
    recOn (sig := sig) onConstructor x member = evalAt (sig := sig) onConstructor n x :=
  evalAt_eq_mem distinct onConstructor (Classical.choose_spec (mem_carrier.mp member)) atStage

theorem recOn_independent (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (left right : x ∈ carrier sig) :
    recOn (sig := sig) onConstructor x left = recOn (sig := sig) onConstructor x right := by
  unfold recOn
  exact evalAt_eq_mem distinct onConstructor
    (Classical.choose_spec (mem_carrier.mp left))
    (Classical.choose_spec (mem_carrier.mp right))

/-- The recursive function on every set. On the carrier it is the recursion; the value
off the carrier is not used. -/
noncomputable def recFun (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ fun y => ∀ member : x ∈ carrier sig, y = recOn (sig := sig) onConstructor x member

theorem recFun_eq (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (member : x ∈ carrier sig) :
    recFun (sig := sig) onConstructor x = recOn (sig := sig) onConstructor x member := by
  have existsValue : ∃ y, ∀ other : x ∈ carrier sig, y = recOn (sig := sig) onConstructor x other :=
    ⟨recOn (sig := sig) onConstructor x member,
      fun other => recOn_independent distinct onConstructor member other⟩
  exact Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
    (fun y => ∀ other : x ∈ carrier sig, y = recOn (sig := sig) onConstructor x other) existsValue member

/-- The computation equation at a constructor, for a signature with distinct tags. -/
theorem recFun_constructor (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    {i : Nat} {c : Constructor.{u}} {args : List ZFSet.{u}}
    (atIndex : sig[i]? = some c) (fitting : Fits (carrier sig) c.fields args) :
    recFun (sig := sig) onConstructor (constructorValue c.tag args) =
      onConstructor i args (mapRec (recFun (sig := sig) onConstructor) c.fields args) := by
  obtain ⟨n, atStage⟩ := exists_bound fitting
  have inCarrier := constructor_mem_carrier atIndex fitting
  have inIterate := constructor_mem_iterate atIndex atStage
  rw [recFun_eq distinct onConstructor inCarrier,
    recOn_spec distinct onConstructor inCarrier inIterate]
  rw [evalAt_presentation distinct onConstructor ⟨i, c, args, atIndex, atStage, rfl⟩]
  apply congrArg (onConstructor i args)
  apply mapRec_congr atStage
  intro a ha
  have aCarrier := iterate_subset_carrier n ha
  rw [recFun_eq distinct onConstructor aCarrier]
  exact (recOn_spec distinct onConstructor aCarrier ha).symm

/-- A function that satisfies the constructor equations agrees with the recursion on
the carrier, for a signature with distinct tags. -/
theorem recFun_unique (distinct : DistinctTags sig)
    (onConstructor : Nat → List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u})
    (g : ZFSet.{u} → ZFSet.{u})
    (equations : ∀ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
      sig[i]? = some c → Fits (carrier sig) c.fields args →
        g (constructorValue c.tag args) = onConstructor i args (mapRec g c.fields args))
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
          evalAt_presentation distinct onConstructor ⟨i, c, args, atIndex, fitting, rfl⟩]
        apply congrArg (onConstructor i args)
        exact mapRec_congr fitting fun a ha => ih a ha
  obtain ⟨n, atStage⟩ := mem_carrier.mp member
  rw [agree n x atStage, recFun_eq distinct onConstructor member,
    recOn_spec distinct onConstructor member atStage]

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

/-- The tuple of members of a closed universe that has the empty set is a member. -/
theorem tuple_mem {U : ZFSet.{u}} (closed : Closed U) (seed : (∅ : ZFSet.{u}) ∈ U) :
    ∀ args : List ZFSet.{u}, (∀ a, a ∈ args → a ∈ U) → tuple args ∈ U
  | [], _ => seed
  | a :: args, h =>
      closed.pair_mem (h a List.mem_cons_self)
        (tuple_mem closed seed args (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem constructorImage_mem {U X t : ZFSet.{u}} (closed : Closed U) (hX : X ∈ U) (ht : t ∈ U)
    (fs : List Field.{u}) (fields : ∀ A, Field.ofSet A ∈ fs → A ∈ U) :
    constructorImage t fs X ∈ U := by
  have arguments := argumentSet_mem closed hX fs fields
  refine closed.replacement_mem arguments (fun s => ZFSet.pair t s) ?_
  intro s hs
  exact closed.pair_mem ht (closed.transitive (argumentSet fs X) arguments hs)

theorem stepSet_mem {U X : ZFSet.{u}} (closed : Closed U) (hX : X ∈ U) :
    ∀ sig : Signature.{u}, (∀ c, c ∈ sig → c.tag ∈ U) →
      (∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c.fields → A ∈ U) → stepSet sig X ∈ U
  | [], _, _ => closed.empty_mem hX
  | c :: cs, tags, fields => by
      rw [stepSet]
      exact closed.binaryUnion_mem
        (constructorImage_mem closed hX (tags c List.mem_cons_self) c.fields
          fun A hA => fields c List.mem_cons_self A hA)
        (stepSet_mem closed hX cs (fun d hd => tags d (List.mem_cons_of_mem _ hd))
          fun d hd A hA => fields d (List.mem_cons_of_mem _ hd) A hA)

theorem iterate_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (tags : ∀ c, c ∈ sig → c.tag ∈ U)
    (fields : ∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c.fields → A ∈ U) :
    ∀ n, iterate sig n ∈ U
  | 0 => closed.empty_mem hω
  | n + 1 => by
      rw [iterate]
      exact stepSet_mem closed (iterate_mem closed hω tags fields n) sig tags fields

/-- If `U` is closed and contains `ω`, every tag and every field set, the carrier is a
member. -/
theorem carrier_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (tags : ∀ c, c ∈ sig → c.tag ∈ U)
    (fields : ∀ c, c ∈ sig → ∀ A, Field.ofSet A ∈ c.fields → A ∈ U) : carrier sig ∈ U := by
  rw [carrier]
  refine closed.union_mem ?_
  refine range_mem_of_index closed numeral numeral_injective ?_ (iterate sig)
    (iterate_mem closed hω tags fields)
  rw [range_numeral]
  exact hω

/-- The tags of two constructors lie in a set that has both. -/
theorem tags_mem_pair {U : ZFSet.{u}} {c d : Constructor.{u}} (hc : c.tag ∈ U) (hd : d.tag ∈ U) :
    ∀ e, e ∈ [c, d] → e.tag ∈ U := by
  intro e member
  rcases List.mem_cons.mp member with rfl | member
  · exact hc
  · rcases List.mem_cons.mp member with rfl | member
    · exact hd
    · cases member

/-! ## The natural numbers -/

/-- The numerals `0` and `1` are different sets. -/
theorem numeral_zero_ne_one : (numeral 0 : ZFSet.{u}) ≠ numeral 1 :=
  numeral_injective.ne Nat.zero_ne_one

/-- Zero, and successor of one recursive argument. The tags are the numerals `0` and `1`. -/
def natSignature : Signature.{u} := [⟨numeral 0, []⟩, ⟨numeral 1, [Field.recursive]⟩]

theorem natSignature_distinct : DistinctTags natSignature.{u} :=
  distinctTags_pair numeral_zero_ne_one

def natEmbed : Nat → ZFSet.{u}
  | 0 => constructorValue (numeral 0) []
  | n + 1 => constructorValue (numeral 1) [natEmbed n]

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
  | 0 => constructor_mem_carrier (i := 0) (c := ⟨numeral 0, []⟩) rfl Fits.nil
  | n + 1 => constructor_mem_carrier (i := 1) (c := ⟨numeral 1, [Field.recursive]⟩) rfl
      (Fits.recursive (natEmbed_mem n) Fits.nil)

theorem natSignature_no_set_field {c : Constructor.{u}} {A : ZFSet.{u}}
    (inSignature : c ∈ natSignature) (inConstructor : Field.ofSet A ∈ c.fields) : False := by
  rcases List.mem_cons.mp inSignature with rfl | inSignature
  · exact nomatch (inConstructor : Field.ofSet A ∈ ([] : List Field.{u}))
  · rcases List.mem_cons.mp inSignature with rfl | inSignature
    · rcases List.mem_cons.mp (inConstructor : Field.ofSet A ∈ [Field.recursive]) with
        bad | inConstructor
      · cases bad
      · cases inConstructor
    · cases inSignature

theorem natCarrier_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) :
    carrier natSignature ∈ U :=
  carrier_mem closed hω
    (tags_mem_pair (numeral_mem_of_omega closed hω 0) (numeral_mem_of_omega closed hω 1))
    fun _ hc _ hA => (natSignature_no_set_field hc hA).elim

theorem rec_natEmbed : ∀ n, recFun (sig := natSignature) natStep (natEmbed n) = numeral n
  | 0 => by
      rw [natEmbed, recFun_constructor natSignature_distinct natStep (i := 0)
        (c := ⟨numeral 0, []⟩) rfl Fits.nil]
      rfl
  | n + 1 => by
      rw [natEmbed, recFun_constructor natSignature_distinct natStep (i := 1)
          (c := ⟨numeral 1, [Field.recursive]⟩) rfl (Fits.recursive (natEmbed_mem n) Fits.nil),
        mapRec_recursive, mapRec_nil, rec_natEmbed n, natStep_one, numeral_succ]

theorem exists_natEmbed {x : ZFSet.{u}} (member : x ∈ carrier natSignature) :
    ∃ n, natEmbed n = x := by
  refine carrier_induct (P := fun y => ∃ n, natEmbed n = y) ?_ member
  intro i c args atIndex fitting
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = ⟨numeral 0, []⟩ := (Option.some_inj).mp atIndex.symm
      cases hc
      cases (fitting : FitsPred _ [] args)
      exact ⟨0, rfl⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = ⟨numeral 1, [Field.recursive]⟩ := (Option.some_inj).mp atIndex.symm
          cases hc
          cases (fitting : FitsPred _ [Field.recursive] args) with
          | recursive memberPred rest =>
              cases rest
              obtain ⟨n, hn⟩ := memberPred
              exact ⟨n + 1, by rw [← hn]; rfl⟩
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

/-- The empty list, and cons of an element of `A` with a recursive tail. The tags are the
numerals `0` and `1`. -/
def listSignature (A : ZFSet.{u}) : Signature.{u} :=
  [⟨numeral 0, []⟩, ⟨numeral 1, [Field.ofSet A, Field.recursive]⟩]

theorem listSignature_distinct (A : ZFSet.{u}) : DistinctTags (listSignature A) :=
  distinctTags_pair numeral_zero_ne_one

def ofList {A : ZFSet.{u}} : List (Elements A) → ZFSet.{u}
  | [] => constructorValue (numeral 0) []
  | x :: xs => constructorValue (numeral 1) [x.1, ofList xs]

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
  | [] => constructor_mem_carrier (i := 0) (c := ⟨numeral 0, []⟩) rfl Fits.nil
  | x :: xs => constructor_mem_carrier (i := 1)
      (c := ⟨numeral 1, [Field.ofSet A, Field.recursive]⟩) rfl
      (Fits.ofSet x.2 (Fits.recursive (ofList_mem xs) Fits.nil))

theorem rec_ofList {A : ZFSet.{u}} :
    ∀ xs : List (Elements A), recFun (sig := listSignature A) listStep (ofList xs) = ZFSetList.encode xs
  | [] => by
      rw [ofList, ZFSetList.encode_nil,
        recFun_constructor (listSignature_distinct A) listStep (i := 0) (c := ⟨numeral 0, []⟩)
          rfl Fits.nil,
        mapRec_nil, listStep_zero]
  | x :: xs => by
      rw [ofList, ZFSetList.encode_cons,
        recFun_constructor (listSignature_distinct A) listStep (i := 1)
          (c := ⟨numeral 1, [Field.ofSet A, Field.recursive]⟩) rfl
          (Fits.ofSet x.2 (Fits.recursive (ofList_mem xs) Fits.nil)),
        mapRec_ofSet, mapRec_recursive, mapRec_nil, rec_ofList xs, listStep_one]

theorem exists_ofList {A x : ZFSet.{u}} (member : x ∈ carrier (listSignature A)) :
    ∃ xs : List (Elements A), ofList xs = x := by
  refine carrier_induct (sig := listSignature A) (P := fun y => ∃ xs, ofList xs = y) ?_ member
  intro i c args atIndex fitting
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = ⟨numeral 0, []⟩ := (Option.some_inj).mp atIndex.symm
      cases hc
      cases (fitting : FitsPred _ [] args)
      exact ⟨[], rfl⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = ⟨numeral 1, [Field.ofSet A, Field.recursive]⟩ :=
            (Option.some_inj).mp atIndex.symm
          cases hc
          cases (fitting : FitsPred _ [Field.ofSet A, Field.recursive] args) with
          | ofSet headMember tailFit =>
              cases tailFit with
              | recursive tailMember nilFit =>
                  cases nilFit
                  obtain ⟨xs, hxs⟩ := tailMember
                  exact ⟨⟨_, headMember⟩ :: xs, by rw [← hxs]; rfl⟩
      | succ i =>
          exact (Nat.not_lt.mpr (Nat.le_add_left 2 i) bound).elim

theorem listRec_mem {A x : ZFSet.{u}} (member : x ∈ carrier (listSignature A)) :
    recFun (sig := listSignature A) listStep x ∈ ZFSetList.listCode A := by
  obtain ⟨xs, hx⟩ := exists_ofList member
  rw [← hx, rec_ofList]
  exact ZFSet.mem_range_self xs

theorem listSignature_field {A B : ZFSet.{u}} {c : Constructor.{u}}
    (inSignature : c ∈ listSignature A) (inConstructor : Field.ofSet B ∈ c.fields) : B = A := by
  rcases List.mem_cons.mp inSignature with rfl | inSignature
  · exact nomatch (inConstructor : Field.ofSet B ∈ ([] : List Field.{u}))
  · rcases List.mem_cons.mp inSignature with rfl | inSignature
    · rcases List.mem_cons.mp
        (inConstructor : Field.ofSet B ∈ [Field.ofSet A, Field.recursive]) with
        same | inConstructor
      · cases same
        rfl
      · rcases List.mem_cons.mp inConstructor with bad | inConstructor
        · cases bad
        · cases inConstructor
    · cases inSignature

/-- Lists lie in any closed universe that contains `ω` and the element set. -/
theorem listCarrier_mem {U A : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (hA : A ∈ U) : carrier (listSignature A) ∈ U :=
  carrier_mem closed hω
    (tags_mem_pair (numeral_mem_of_omega closed hω 0) (numeral_mem_of_omega closed hω 1))
    fun c hc B hB => by
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
  obtain ⟨_, c, args, _, _, value⟩ := exists_inversion emptyCode
  exact constructorValue_ne_empty c.tag args value

/-! ## Binary trees with a number at each leaf -/

/-- A leaf carries a member of `ω`, and a node has two recursive children. The tags are the
numerals `0` and `1`. -/
def treeSignature : Signature.{u} :=
  [⟨numeral 0, [Field.ofSet ZFSet.omega]⟩, ⟨numeral 1, [Field.recursive, Field.recursive]⟩]

theorem treeSignature_distinct : DistinctTags treeSignature.{u} :=
  distinctTags_pair numeral_zero_ne_one

def leafValue (n : ZFSet.{u}) : ZFSet.{u} := constructorValue (numeral 0) [n]

def nodeValue (left right : ZFSet.{u}) : ZFSet.{u} := constructorValue (numeral 1) [left, right]

theorem leafValue_mem {n : ZFSet.{u}} (number : n ∈ ZFSet.omega) :
    leafValue n ∈ carrier treeSignature :=
  constructor_mem_carrier (i := 0) (c := ⟨numeral 0, [Field.ofSet ZFSet.omega]⟩) rfl
    (Fits.ofSet number Fits.nil)

theorem nodeValue_mem {left right : ZFSet.{u}}
    (leftMember : left ∈ carrier treeSignature) (rightMember : right ∈ carrier treeSignature) :
    nodeValue left right ∈ carrier treeSignature :=
  constructor_mem_carrier (i := 1) (c := ⟨numeral 1, [Field.recursive, Field.recursive]⟩) rfl
    (Fits.recursive leftMember (Fits.recursive rightMember Fits.nil))

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
      have hc : c = ⟨numeral 0, [Field.ofSet ZFSet.omega]⟩ := (Option.some_inj).mp atIndex.symm
      cases hc
      cases (fitting : Fits _ [Field.ofSet ZFSet.omega] args) with
      | ofSet number rest =>
          cases rest
          exact Or.inl ⟨_, number, rfl⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = ⟨numeral 1, [Field.recursive, Field.recursive]⟩ :=
            (Option.some_inj).mp atIndex.symm
          cases hc
          cases (fitting : Fits _ [Field.recursive, Field.recursive] args) with
          | recursive leftMember rest =>
              cases rest with
              | recursive rightMember nilFit =>
                  cases nilFit
                  exact Or.inr ⟨_, _, leftMember, rightMember, rfl⟩
      | succ i =>
          exact (Nat.not_lt.mpr (Nat.le_add_left 2 i) bound).elim

theorem treeSignature_field {B : ZFSet.{u}} {c : Constructor.{u}}
    (inSignature : c ∈ treeSignature) (inConstructor : Field.ofSet B ∈ c.fields) :
    B = ZFSet.omega := by
  rcases List.mem_cons.mp inSignature with rfl | inSignature
  · rcases List.mem_cons.mp (inConstructor : Field.ofSet B ∈ [Field.ofSet ZFSet.omega]) with
      same | inConstructor
    · cases same
      rfl
    · cases inConstructor
  · rcases List.mem_cons.mp inSignature with rfl | inSignature
    · rcases List.mem_cons.mp
        (inConstructor : Field.ofSet B ∈ [Field.recursive, Field.recursive]) with
        bad | inConstructor
      · cases bad
      · rcases List.mem_cons.mp inConstructor with bad | inConstructor
        · cases bad
        · cases inConstructor
    · cases inSignature

theorem treeCarrier_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) :
    carrier treeSignature ∈ U :=
  carrier_mem closed hω
    (tags_mem_pair (numeral_mem_of_omega closed hω 0) (numeral_mem_of_omega closed hω 1))
    fun c hc B hB => by
      rw [treeSignature_field hc hB]
      exact hω

/-! ## Negative signatures -/

/-- The signature whose only constructor asks for one recursive argument. -/
def loopSignature : Signature.{u} := [⟨numeral 0, [Field.recursive]⟩]

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
    obtain ⟨j, c, args, atIndex, fitting, _⟩ := mem_stepSet.mp member
    have jZero : j = 0 := by
      have lengthOne : loopSignature.length = 1 := rfl
      have bound := some_index_lt atIndex
      rw [lengthOne] at bound
      cases j with
      | zero => rfl
      | succ j => exact (Nat.not_succ_le_zero j (Nat.le_of_lt_succ bound)).elim
    cases jZero
    have hc : c = ⟨numeral 0, [Field.recursive]⟩ := (Option.some_inj).mp atIndex.symm
    cases hc
    cases (fitting : Fits _ [Field.recursive] args) with
    | recursive inEmpty _ => exact (ZFSet.notMem_empty _ inEmpty).elim
  · intro member
    exact (ZFSet.notMem_empty z member).elim

theorem iterate_loop : ∀ n, iterate loopSignature n = ∅
  | 0 => rfl
  | n + 1 => by rw [iterate, iterate_loop n, stepSet_loop_empty]

theorem loop_carrier_empty : carrier loopSignature = ∅ :=
  carrier_eq_empty_of_iterate iterate_loop

theorem stepSet_no_constructor (X : ZFSet.{u}) : stepSet [] X = ∅ := rfl

theorem iterate_no_constructor : ∀ n, iterate ([] : Signature.{u}) n = ∅
  | 0 => rfl
  | n + 1 => by rw [iterate, stepSet_no_constructor]

/-- A signature with no constructor has the empty carrier. -/
theorem empty_carrier_empty : carrier ([] : Signature.{u}) = ∅ :=
  carrier_eq_empty_of_iterate iterate_no_constructor

/-- A constructor value whose set-field argument lies outside the field set is not in
the carrier. -/
theorem outside_field_not_mem {t A x : ZFSet.{u}} (outside : x ∉ A) :
    constructorValue t [x] ∉ carrier [⟨t, [Field.ofSet A]⟩] := by
  intro member
  obtain ⟨i, c, args, atIndex, fitting, equal⟩ := exists_inversion member
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = ⟨t, [Field.ofSet A]⟩ := (Option.some_inj).mp atIndex.symm
      cases hc
      have hargs : args = [x] := constructorValue_args equal
      cases hargs
      cases (fitting : Fits _ [Field.ofSet A] [x]) with
      | ofSet inside rest =>
          cases rest
          exact outside inside
  | succ i =>
      exact (Nat.not_succ_le_zero i (Nat.le_of_lt_succ bound)).elim

/-! ## One tag on two constructors -/

/-- Two constructors with the one tag `∅`: the first takes a member of `{∅}`, the second a
natural number. -/
def sharedTagSignature : Signature.{u} :=
  [⟨∅, [Field.ofSet {∅}]⟩, ⟨∅, [Field.ofSet ZFSet.omega]⟩]

/-- Its tags are not distinct. -/
theorem sharedTag_not_distinct : ¬ DistinctTags sharedTagSignature.{u} := by
  intro distinct
  have twice : [(∅ : ZFSet.{u}), ∅].Nodup := distinct
  exact (List.nodup_cons.mp twice).1 (List.mem_singleton.mpr rfl)

/-- The set whose only member is the empty set is not the set of the natural numbers. -/
theorem singleton_empty_ne_omega : ({∅} : ZFSet.{u}) ≠ ZFSet.omega := by
  intro same
  have one : numeral 1 ∈ ({∅} : ZFSet.{u}) := same ▸ numeral_mem_omega 1
  exact numeral_zero_ne_one (ZFSet.mem_singleton.mp one).symm

/-- **A member with two presentations.** With one tag on two constructors with different
fields, one set is the value of the first and of the second at one argument list. So the
conclusion of `inversion_unique` fails without distinct tags. -/
theorem sharedTag_two_presentations :
    ∃ (x : ZFSet.{u}) (c d : Constructor.{u}) (args : List ZFSet.{u}),
      sharedTagSignature[0]? = some c ∧ sharedTagSignature[1]? = some d ∧ c ≠ d ∧
        Fits (carrier sharedTagSignature) c.fields args ∧
        Fits (carrier sharedTagSignature) d.fields args ∧
        constructorValue c.tag args = x ∧ constructorValue d.tag args = x := by
  refine ⟨constructorValue ∅ [∅], ⟨∅, [Field.ofSet {∅}]⟩, ⟨∅, [Field.ofSet ZFSet.omega]⟩, [∅],
    rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · intro same
    injection same with _ fields
    injection fields with field _
    injection field with sets
    exact singleton_empty_ne_omega sets
  · exact Fits.ofSet (ZFSet.mem_singleton.mpr rfl) Fits.nil
  · exact Fits.ofSet ZFSet.omega_zero Fits.nil

/-- **A recursion that tells the two constructors apart has no solution**: no function has
the value `numeral i` at every value of constructor `i`. So the computation equation of
`recFun_constructor` fails without distinct tags. -/
theorem sharedTag_no_recursion :
    ¬ ∃ g : ZFSet.{u} → ZFSet.{u},
      ∀ (i : Nat) (c : Constructor.{u}) (args : List ZFSet.{u}),
        sharedTagSignature[i]? = some c → Fits (carrier sharedTagSignature) c.fields args →
          g (constructorValue c.tag args) = numeral i := by
  rintro ⟨g, equations⟩
  have first := equations 0 ⟨∅, [Field.ofSet {∅}]⟩ [∅] rfl
    (Fits.ofSet (ZFSet.mem_singleton.mpr rfl) Fits.nil)
  have second := equations 1 ⟨∅, [Field.ofSet ZFSet.omega]⟩ [∅] rfl
    (Fits.ofSet ZFSet.omega_zero Fits.nil)
  exact numeral_zero_ne_one (first.symm.trans second)

/-! ## Names as tags, and data terms -/

/-- The bytes of a string, its UTF-8 encoding, determine it. -/
theorem string_eq_of_bytes {s t : String}
    (same : s.toByteArray.data.toList = t.toByteArray.data.toList) : s = t := by
  cases s with
  | ofByteArray b _ =>
    cases t with
    | ofByteArray c _ =>
      cases b with
      | mk x =>
        cases c with
        | mk y =>
          cases x with
          | mk l =>
            cases y with
            | mk m =>
              cases same
              rfl

/-- The code of a string: the tuple of the numerals of the bytes of its UTF-8 encoding. -/
def stringCode (s : String) : ZFSet.{u} :=
  tuple (s.toByteArray.data.toList.map fun b => numeral b.toNat)

/-- Different strings have different codes. -/
theorem stringCode_injective : Function.Injective stringCode.{u} := by
  intro s t same
  have bytes : (s.toByteArray.data.toList.map fun b => numeral.{u} b.toNat) =
      t.toByteArray.data.toList.map fun b => numeral.{u} b.toNat := tuple_injective same
  exact string_eq_of_bytes
    ((List.map_inj_right fun _ _ equal => UInt8.toNat_inj.mp (numeral_injective equal)).mp bytes)

/-- The code of a string is a member of every closed universe that has `ω` as a member. -/
theorem stringCode_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) (s : String) :
    stringCode s ∈ U :=
  tuple_mem closed (closed.empty_mem hω) _ fun a member => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp member
    exact numeral_mem_of_omega closed hω b.toNat

/-- **The code of a name.** The anonymous name is the empty set. A name extended by a string
is the numeral `0` paired with the pair of the code of the name and the code of the string. A
name extended by a number is the numeral `1` paired with the pair of the code of the name and
the numeral of the number. -/
def nameCode : Lean.Name → ZFSet.{u}
  | .anonymous => ∅
  | .str p s => ZFSet.pair (numeral 0) (ZFSet.pair (nameCode p) (stringCode s))
  | .num p i => ZFSet.pair (numeral 1) (ZFSet.pair (nameCode p) (numeral i))

/-- **Different names have different codes.** -/
theorem nameCode_injective : Function.Injective nameCode.{u} := by
  intro k
  induction k with
  | anonymous =>
      intro l same
      cases l with
      | anonymous => rfl
      | str q t => exact (ZFSetList.pair_ne_empty _ _ same.symm).elim
      | num q j => exact (ZFSetList.pair_ne_empty _ _ same.symm).elim
  | str p s ih =>
      intro l same
      cases l with
      | anonymous => exact (ZFSetList.pair_ne_empty _ _ same).elim
      | str q t =>
          obtain ⟨names, strings⟩ := ZFSet.pair_inj.mp (ZFSet.pair_inj.mp same).2
          rw [ih names, stringCode_injective strings]
      | num q j => exact (numeral_zero_ne_one (ZFSet.pair_inj.mp same).1).elim
  | num p i ih =>
      intro l same
      cases l with
      | anonymous => exact (ZFSetList.pair_ne_empty _ _ same).elim
      | str q t => exact (numeral_zero_ne_one (ZFSet.pair_inj.mp same).1.symm).elim
      | num q j =>
          obtain ⟨names, numbers⟩ := ZFSet.pair_inj.mp (ZFSet.pair_inj.mp same).2
          rw [ih names, numeral_injective numbers]

/-- **The code of a name is a member of every closed universe that has `ω` as a member.** -/
theorem nameCode_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) :
    ∀ k : Lean.Name, nameCode k ∈ U
  | .anonymous => closed.empty_mem hω
  | .str p s =>
      closed.pair_mem (numeral_mem_of_omega closed hω 0)
        (closed.pair_mem (nameCode_mem closed hω p) (stringCode_mem closed hω s))
  | .num p i =>
      closed.pair_mem (numeral_mem_of_omega closed hω 1)
        (closed.pair_mem (nameCode_mem closed hω p) (numeral_mem_of_omega closed hω i))

/-! The two codes are kept folded from here on. What the readings use of them is that
different names have different codes and that the codes lie in the closed universes; unfolding
the code of a name would unfold the numeral of each of its characters. -/

attribute [irreducible] stringCode nameCode

/-- **A first-order data term**: a name applied to a list of data terms. -/
inductive DataTerm where
  | app (name : Lean.Name) (args : List DataTerm)

mutual

/-- **The set of a data term**: the constructor value of the code of its name at the sets of
its arguments. -/
def DataTerm.toSet : DataTerm → ZFSet.{u}
  | .app k args => constructorValue (nameCode k) (DataTerm.toSets args)

/-- The sets of a list of data terms. -/
def DataTerm.toSets : List DataTerm → List ZFSet.{u}
  | [] => []
  | d :: ds => d.toSet :: DataTerm.toSets ds

end

theorem DataTerm.toSet_app (k : Lean.Name) (args : List DataTerm) :
    (DataTerm.app k args).toSet = constructorValue (nameCode.{u} k) (DataTerm.toSets args) := by
  rw [DataTerm.toSet]

theorem DataTerm.toSets_nil : DataTerm.toSets.{u} [] = [] := by
  rw [DataTerm.toSets]

theorem DataTerm.toSets_cons (d : DataTerm) (ds : List DataTerm) :
    DataTerm.toSets.{u} (d :: ds) = d.toSet :: DataTerm.toSets ds := by
  rw [DataTerm.toSets]

/-- The sets of a list of data terms are the sets of its terms. -/
theorem DataTerm.toSets_eq_map : ∀ ds : List DataTerm,
    DataTerm.toSets.{u} ds = ds.map DataTerm.toSet
  | [] => DataTerm.toSets_nil
  | d :: ds => by
      rw [DataTerm.toSets_cons, DataTerm.toSets_eq_map ds]
      rfl

/-- The set of a data term, with the sets of its arguments as a mapped list. -/
theorem DataTerm.toSet_app_map (k : Lean.Name) (args : List DataTerm) :
    (DataTerm.app k args).toSet =
      constructorValue (nameCode.{u} k) (args.map DataTerm.toSet) := by
  rw [DataTerm.toSet_app, DataTerm.toSets_eq_map]

mutual

theorem DataTerm.eq_of_toSet_eq : ∀ d e : DataTerm, d.toSet = e.toSet.{u} → d = e
  | .app k ds, .app l es, same => by
      rw [DataTerm.toSet_app, DataTerm.toSet_app] at same
      obtain ⟨names, sets⟩ := constructorValue_injective.mp same
      rw [nameCode_injective names, DataTerm.eq_of_toSets_eq ds es sets]

theorem DataTerm.eq_of_toSets_eq : ∀ ds es : List DataTerm,
    DataTerm.toSets ds = DataTerm.toSets.{u} es → ds = es
  | [], [], _ => rfl
  | [], e :: es, same => by
      rw [DataTerm.toSets_nil, DataTerm.toSets_cons] at same
      exact nomatch same
  | d :: ds, [], same => by
      rw [DataTerm.toSets_nil, DataTerm.toSets_cons] at same
      exact nomatch same
  | d :: ds, e :: es, same => by
      rw [DataTerm.toSets_cons, DataTerm.toSets_cons] at same
      obtain ⟨head, tail⟩ := List.cons.inj same
      rw [DataTerm.eq_of_toSet_eq d e head, DataTerm.eq_of_toSets_eq ds es tail]

end

/-- **The reading of data terms is injective.** -/
theorem DataTerm.toSet_injective : Function.Injective DataTerm.toSet.{u} :=
  fun d e same => DataTerm.eq_of_toSet_eq d e same

/-- **Two data terms have one set exactly when they are the same term.** -/
theorem DataTerm.toSet_eq_iff {d e : DataTerm} : d.toSet = e.toSet.{u} ↔ d = e :=
  DataTerm.toSet_injective.eq_iff

/-- Data terms with different names are different sets, at any arguments. -/
theorem DataTerm.toSet_ne_of_name_ne {k l : Lean.Name} (distinct : k ≠ l)
    (ds es : List DataTerm) : (DataTerm.app k ds).toSet ≠ (DataTerm.app l es).toSet.{u} :=
  fun same => distinct (DataTerm.app.inj (DataTerm.toSet_injective same)).1

mutual

/-- **The set of a data term is a member of every closed universe that has `ω` as a
member.** -/
theorem DataTerm.toSet_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) :
    ∀ d : DataTerm, d.toSet ∈ U
  | .app k ds => by
      rw [DataTerm.toSet_app]
      exact closed.pair_mem (nameCode_mem closed hω k)
        (tuple_mem closed (closed.empty_mem hω) _ (DataTerm.toSets_mem closed hω ds))

theorem DataTerm.toSets_mem {U : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U) :
    ∀ ds : List DataTerm, ∀ a, a ∈ DataTerm.toSets ds → a ∈ U
  | [], a, member => by
      rw [DataTerm.toSets_nil] at member
      exact nomatch member
  | d :: ds, a, member => by
      rw [DataTerm.toSets_cons] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact DataTerm.toSet_mem closed hω d
      · exact DataTerm.toSets_mem closed hω ds a member

end

/-- Positive example: the two-element list of the constants `a` and `b`, as a data term. -/
def DataTerm.exampleList : DataTerm :=
  .app `cons [.app `a [], .app `cons [.app `b [], .app `nil []]]

/-- Its set is the value of `cons` at the set of `a` and the set of the rest. -/
theorem DataTerm.exampleList_toSet :
    DataTerm.exampleList.toSet.{u} =
      constructorValue (nameCode `cons)
        [constructorValue (nameCode `a) [],
          constructorValue (nameCode `cons)
            [constructorValue (nameCode `b) [], constructorValue (nameCode `nil) []]] := by
  simp only [DataTerm.exampleList, DataTerm.toSet_app, DataTerm.toSets_cons, DataTerm.toSets_nil]

/-- Negative example: the constants `zero` and `nil` are different sets. No declaration is
needed to tell them apart. -/
theorem DataTerm.zero_ne_nil :
    (DataTerm.app `zero []).toSet ≠ (DataTerm.app `nil []).toSet.{u} :=
  DataTerm.toSet_ne_of_name_ne (by decide) [] []

#print axioms constructorValue_injective
#print axioms constructorValue_ne_of_tag_ne
#print axioms constructor_mem_carrier
#print axioms exists_inversion
#print axioms constructorValue_not_mem_carrier
#print axioms carrier_disjoint
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
#print axioms sharedTag_two_presentations
#print axioms sharedTag_no_recursion
#print axioms stringCode
#print axioms nameCode
#print axioms nameCode_injective
#print axioms nameCode_mem
#print axioms DataTerm.toSet_injective
#print axioms DataTerm.toSet_mem
#print axioms DataTerm.zero_ne_nil

end Mettapedia.Logic.HOL.Embedding.ZFSetInductive
