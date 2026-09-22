import Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation
import Mathlib.Logic.Small.List

/-!
# Finite lists as actual sets in the same ambient universe

The empty list is the empty set and a cons cell is an actual Kuratowski pair.
Injectivity of this recursive encoding supplies a decoding equivalence. The
range exists at the original ZFSet universe using smallness of a set's element
type and its finite lists. Membership in a particular closed universe is a
separate question; no closure under finite lists is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetList

open ZFSetDependentProducts

universe u v

theorem pair_ne_empty (x y : ZFSet.{u}) : ZFSet.pair x y ≠ ∅ := by
  intro equal
  have member : ({x} : ZFSet.{u}) ∈ ZFSet.pair x y :=
    ZFSet.mem_pair.mpr (Or.inl rfl)
  rw [equal] at member
  exact ZFSet.notMem_empty _ member

def encode {a : ZFSet.{u}} : List (Elements a) → ZFSet.{u}
  | [] => ∅
  | x :: xs => ZFSet.pair x.1 (encode xs)

@[simp] theorem encode_nil {a : ZFSet.{u}} : encode (a := a) [] = ∅ := rfl
@[simp] theorem encode_cons {a : ZFSet.{u}} (x : Elements a) (xs : List (Elements a)) :
    encode (x :: xs) = ZFSet.pair x.1 (encode xs) := rfl

theorem encode_injective (a : ZFSet.{u}) : Function.Injective (encode (a := a)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys equal
      cases ys with
      | nil => rfl
      | cons y ys => exact False.elim (pair_ne_empty y.1 (encode ys) equal.symm)
  | cons x xs ih =>
      intro ys equal
      cases ys with
      | nil => exact False.elim (pair_ne_empty x.1 (encode xs) equal)
      | cons y ys =>
          obtain ⟨headEqual, tailEqual⟩ := ZFSet.pair_inj.mp equal
          exact congrArg₂ List.cons (Subtype.ext headEqual) (ih tailEqual)

noncomputable def listCode (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (encode (a := a))

theorem mem_listCode {a code : ZFSet.{u}} :
    code ∈ listCode a ↔ ∃ xs : List (Elements a), encode xs = code := ZFSet.mem_range

noncomputable def encodeValue {a : ZFSet.{u}} (xs : List (Elements a)) :
    Elements (listCode a) := ⟨encode xs, ZFSet.mem_range_self xs⟩

noncomputable def decode {a : ZFSet.{u}} (value : Elements (listCode a)) : List (Elements a) :=
  Classical.choose (mem_listCode.mp value.2)

@[simp] theorem encode_decode {a : ZFSet.{u}} (value : Elements (listCode a)) :
    encode (decode value) = value.1 := Classical.choose_spec (mem_listCode.mp value.2)

@[simp] theorem decode_encode {a : ZFSet.{u}} (xs : List (Elements a)) :
    decode (encodeValue xs) = xs :=
  encode_injective a (encode_decode (encodeValue xs))

@[simp] theorem encodeValue_decode {a : ZFSet.{u}} (value : Elements (listCode a)) :
    encodeValue (decode value) = value := Subtype.ext (encode_decode value)

noncomputable def listEquiv (a : ZFSet.{u}) : Elements (listCode a) ≃ List (Elements a) where
  toFun := decode
  invFun := encodeValue
  left_inv := encodeValue_decode
  right_inv := decode_encode

noncomputable def nil (a : ZFSet.{u}) : Elements (listCode a) := encodeValue []

noncomputable def cons {a : ZFSet.{u}} (x : Elements a) (xs : Elements (listCode a)) :
    Elements (listCode a) :=
  ⟨ZFSet.pair x.1 xs.1, mem_listCode.mpr ⟨x :: decode xs, by simp⟩⟩

@[simp] theorem encodeValue_cons {a : ZFSet.{u}} (x : Elements a) (xs : List (Elements a)) :
    encodeValue (x :: xs) = cons x (encodeValue xs) := rfl

@[simp] theorem decode_nil (a : ZFSet.{u}) : decode (nil a) = [] := decode_encode []

@[simp] theorem decode_cons {a : ZFSet.{u}} (x : Elements a) (xs : Elements (listCode a)) :
    decode (cons x xs) = x :: decode xs := by
  apply encode_injective a
  simp
  rfl

theorem cons_ne_nil {a : ZFSet.{u}} (x : Elements a) (xs : Elements (listCode a)) :
    cons x xs ≠ nil a := by
  intro equal
  exact pair_ne_empty x.1 xs.1 (congrArg Subtype.val equal)

theorem cons_injective {a : ZFSet.{u}} {x y : Elements a} {xs ys : Elements (listCode a)}
    (equal : cons x xs = cons y ys) : x = y ∧ xs = ys := by
  obtain ⟨headEqual, tailEqual⟩ := ZFSet.pair_inj.mp (congrArg Subtype.val equal)
  exact ⟨Subtype.ext headEqual, Subtype.ext tailEqual⟩

theorem pair_mem_listCode {a x tail : ZFSet.{u}} :
    ZFSet.pair x tail ∈ listCode a ↔ x ∈ a ∧ tail ∈ listCode a := by
  constructor
  · intro member
    obtain ⟨values, equal⟩ := mem_listCode.mp member
    cases values with
    | nil => exact False.elim (pair_ne_empty x tail equal.symm)
    | cons head rest =>
        obtain ⟨headEqual, tailEqual⟩ := ZFSet.pair_inj.mp equal
        exact ⟨headEqual ▸ head.2, mem_listCode.mpr ⟨rest, tailEqual⟩⟩
  · rintro ⟨headMember, tailMember⟩
    obtain ⟨rest, equal⟩ := mem_listCode.mp tailMember
    exact mem_listCode.mpr ⟨⟨x, headMember⟩ :: rest, congrArg (ZFSet.pair x) equal⟩

/-- Finite closure puts each individual encoding in U. This is weaker than
putting their whole collecting set in U. -/
theorem encode_mem {U a : ZFSet.{u}} (closed : ZFSetUniverseClosure.Closed U)
    (carrierMember : a ∈ U) (xs : List (Elements a)) : encode xs ∈ U := by
  induction xs with
  | nil => exact closed.empty_mem carrierMember
  | cons x xs ih =>
      exact closed.pair_mem (closed.transitive _ carrierMember x.2) ih

theorem listCode_subset {U a : ZFSet.{u}} (closed : ZFSetUniverseClosure.Closed U)
    (carrierMember : a ∈ U) : listCode a ⊆ U := by
  intro value member
  obtain ⟨xs, rfl⟩ := mem_listCode.mp member
  exact encode_mem closed carrierMember xs

theorem invalid_head_not_list {a x : ZFSet.{u}} (invalid : x ∉ a) (tail : ZFSet.{u}) :
    ZFSet.pair x tail ∉ listCode a := fun member => invalid (pair_mem_listCode.mp member).1

/-! ## Actual graph mapping -/

noncomputable def map {a b : ZFSet.{u}} (f : Elements a → Elements b)
    (xs : Elements (listCode a)) : Elements (listCode b) :=
  encodeValue ((decode xs).map f)

@[simp] theorem map_nil {a b : ZFSet.{u}} (f : Elements a → Elements b) :
    map f (nil a) = nil b := by simp [map, nil]

@[simp] theorem map_cons {a b : ZFSet.{u}} (f : Elements a → Elements b)
    (x : Elements a) (xs : Elements (listCode a)) :
    map f (cons x xs) = cons (f x) (map f xs) := by simp [map]

theorem map_identity {a : ZFSet.{u}} (xs : Elements (listCode a)) : map id xs = xs := by
  simp [map]

theorem map_composition {a b c : ZFSet.{u}} (f : Elements b → Elements c)
    (g : Elements a → Elements b) (xs : Elements (listCode a)) :
    map f (map g xs) = map (f ∘ g) xs := by simp [map, List.map_map]

noncomputable def mapGraph {a b : ZFSet.{u}} (f : Elements a → Elements b) :
    Elements (piSet (listCode a) (fun _ => listCode b)) := encodeFunction (map f)

@[simp] theorem mapGraph_apply {a b : ZFSet.{u}} (f : Elements a → Elements b)
    (xs : Elements (listCode a)) : graphValue (mapGraph f) xs = map f xs := by
  unfold mapGraph
  exact congrFun (decode_encode_function (a := listCode a) (b := fun _ => listCode b) (map f)) xs

/-! ## Dependent elimination on the actual list carrier -/

noncomputable def recurseEncoded {a : ZFSet.{u}} (motive : Elements (listCode a) → Sort v)
    (zero : motive (nil a))
    (step : (x : Elements a) → (xs : Elements (listCode a)) → motive xs → motive (cons x xs)) :
    (xs : List (Elements a)) → motive (encodeValue xs)
  | [] => zero
  | x :: xs => step x (encodeValue xs) (recurseEncoded motive zero step xs)

noncomputable def eliminate {a : ZFSet.{u}} (motive : Elements (listCode a) → Sort v)
    (zero : motive (nil a))
    (step : (x : Elements a) → (xs : Elements (listCode a)) → motive xs → motive (cons x xs))
    (xs : Elements (listCode a)) : motive xs :=
  cast (congrArg motive (encodeValue_decode xs)) (recurseEncoded motive zero step (decode xs))

@[simp] theorem eliminate_encodeValue {a : ZFSet.{u}}
    (motive : Elements (listCode a) → Sort v) (zero : motive (nil a))
    (step : (x : Elements a) → (xs : Elements (listCode a)) → motive xs → motive (cons x xs))
    (xs : List (Elements a)) :
    eliminate motive zero step (encodeValue xs) = recurseEncoded motive zero step xs := by
  have dependentCongruence (ys zs : List (Elements a)) (equal : ys = zs) :
      HEq (recurseEncoded motive zero step ys) (recurseEncoded motive zero step zs) := by
    cases equal
    rfl
  exact eq_of_heq ((cast_heq _ _).trans
    (dependentCongruence _ _ (decode_encode xs)))

@[simp] theorem eliminate_nil {a : ZFSet.{u}}
    (motive : Elements (listCode a) → Sort v) (zero : motive (nil a))
    (step : (x : Elements a) → (xs : Elements (listCode a)) → motive xs → motive (cons x xs)) :
    eliminate motive zero step (nil a) = zero := eliminate_encodeValue motive zero step []

@[simp] theorem eliminate_cons {a : ZFSet.{u}}
    (motive : Elements (listCode a) → Sort v) (zero : motive (nil a))
    (step : (x : Elements a) → (xs : Elements (listCode a)) → motive xs → motive (cons x xs))
    (x : Elements a) (xs : Elements (listCode a)) :
    eliminate motive zero step (cons x xs) = step x xs (eliminate motive zero step xs) := by
  obtain ⟨values, rfl⟩ := (listEquiv a).symm.surjective xs
  change eliminate motive zero step (encodeValue (x :: values)) =
    step x (encodeValue values) (eliminate motive zero step (encodeValue values))
  rw [eliminate_encodeValue, eliminate_encodeValue]
  rfl

noncomputable def eliminateGraph {a : ZFSet.{u}}
    (motive : Elements (listCode a) → ZFSet.{u})
    (zero : Elements (motive (nil a)))
    (step : (x : Elements a) → (xs : Elements (listCode a)) →
      Elements (motive xs) → Elements (motive (cons x xs))) :
    Elements (piSet (listCode a) (ZFSetContextualInterpretation.totalFamily (listCode a) motive)) :=
  encodeFunction (fun xs => ⟨(eliminate (fun ys => Elements (motive ys)) zero step xs).1, by
    rw [ZFSetContextualInterpretation.totalFamily_at]
    exact (eliminate (fun ys => Elements (motive ys)) zero step xs).2⟩)

theorem eliminateGraph_apply {a : ZFSet.{u}}
    (motive : Elements (listCode a) → ZFSet.{u})
    (zero : Elements (motive (nil a)))
    (step : (x : Elements a) → (xs : Elements (listCode a)) →
      Elements (motive xs) → Elements (motive (cons x xs)))
    (xs : Elements (listCode a)) :
    (graphValue (eliminateGraph motive zero step) xs).1 =
      (eliminate (fun ys => Elements (motive ys)) zero step xs).1 :=
  congrArg Subtype.val (congrFun (decode_encode_function _) xs)

theorem eliminateGraph_nil {a : ZFSet.{u}}
    (motive : Elements (listCode a) → ZFSet.{u})
    (zero : Elements (motive (nil a)))
    (step : (x : Elements a) → (xs : Elements (listCode a)) →
      Elements (motive xs) → Elements (motive (cons x xs))) :
    (graphValue (eliminateGraph motive zero step) (nil a)).1 = zero.1 := by
  rw [eliminateGraph_apply, eliminate_nil]

theorem eliminateGraph_cons {a : ZFSet.{u}}
    (motive : Elements (listCode a) → ZFSet.{u})
    (zero : Elements (motive (nil a)))
    (step : (x : Elements a) → (xs : Elements (listCode a)) →
      Elements (motive xs) → Elements (motive (cons x xs)))
    (x : Elements a) (xs : Elements (listCode a)) :
    (graphValue (eliminateGraph motive zero step) (cons x xs)).1 =
      (step x xs (eliminate (fun ys => Elements (motive ys)) zero step xs)).1 := by
  rw [eliminateGraph_apply, eliminate_cons]

/-- The dependent computation clauses determine every value, since every
member of the list code has a finite constructor presentation. -/
theorem eliminate_unique {a : ZFSet.{u}}
    (motive : Elements (listCode a) → Sort v) (zero : motive (nil a))
    (step : (x : Elements a) → (xs : Elements (listCode a)) → motive xs → motive (cons x xs))
    (candidate : (xs : Elements (listCode a)) → motive xs)
    (atNil : candidate (nil a) = zero)
    (atCons : ∀ x xs, candidate (cons x xs) = step x xs (candidate xs)) :
    candidate = eliminate motive zero step := by
  have agrees (values : List (Elements a)) :
      candidate (encodeValue values) = recurseEncoded motive zero step values := by
    induction values with
    | nil => exact atNil
    | cons x values ih =>
        change candidate (cons x (encodeValue values)) =
          step x (encodeValue values) (recurseEncoded motive zero step values)
        rw [atCons, ih]
  funext xs
  obtain ⟨values, rfl⟩ := (listEquiv a).symm.surjective xs
  exact (agrees values).trans (eliminate_encodeValue motive zero step values).symm

namespace Controls

def carrier : ZFSet.{u} := {∅}
def head : Elements carrier.{u} := ⟨∅, ZFSet.mem_singleton.mpr rfl⟩

/-- The empty-list fibre is a singleton; every cons fibre has two elements. -/
noncomputable def varying (xs : Elements (listCode carrier.{u})) : ZFSet.{u} := by
  classical
  exact if xs = nil carrier then {∅} else {∅, ZFSet.powerset ∅}

noncomputable def zero : Elements (varying (nil carrier.{u})) :=
  ⟨∅, by simp [varying]⟩

noncomputable def step (x : Elements carrier.{u}) (xs : Elements (listCode carrier))
    (_ : Elements (varying xs)) : Elements (varying (cons x xs)) :=
  ⟨ZFSet.powerset ∅, by simp only [varying, if_neg (cons_ne_nil x xs)]; simp⟩

theorem dependent_graph_nil :
    (graphValue (eliminateGraph varying.{u} zero step) (nil carrier)).1 = ∅ :=
  eliminateGraph_nil _ _ _

theorem dependent_graph_cons :
    (graphValue (eliminateGraph varying.{u} zero step) (cons head (nil carrier))).1 =
      ZFSet.powerset ∅ := by
  rw [eliminateGraph_cons]
  rfl

theorem wrong_constant_result :
    (graphValue (eliminateGraph varying.{u} zero step) (cons head (nil carrier))).1 ≠ ∅ := by
  rw [dependent_graph_cons]
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [equal] at member
  exact ZFSet.notMem_empty _ member

end Controls

#print axioms encode_injective
#print axioms listEquiv
#print axioms cons_ne_nil
#print axioms pair_mem_listCode
#print axioms listCode_subset
#print axioms invalid_head_not_list
#print axioms mapGraph_apply
#print axioms map_composition
#print axioms eliminate_nil
#print axioms eliminate_cons
#print axioms eliminateGraph_apply
#print axioms eliminateGraph_nil
#print axioms eliminateGraph_cons
#print axioms eliminate_unique
#print axioms Controls.dependent_graph_nil
#print axioms Controls.dependent_graph_cons
#print axioms Controls.wrong_constant_result

end Mettapedia.Logic.HOL.Embedding.ZFSetList
