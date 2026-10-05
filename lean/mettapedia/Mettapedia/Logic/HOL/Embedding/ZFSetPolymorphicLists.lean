import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
import Mettapedia.Logic.HOL.Embedding.ZFSetInductive
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

/-!
# Lists over an arbitrary set

The set of lists over a set `A` is the carrier of a signature of two constructors: the empty
list, and an element of `A` before a list. The least set closed under the two is the set of
lists. The two constructors carry two tags, `s` for the empty list and `t` for an element
before a list, and the tags are parameters: with the numerals `0` and `1` the signature is the
list signature of `ZFSetInductive` (`taggedListSignature_numerals`), and a declared `nil` and
`cons` are read with the codes of their names.

Membership, induction and monotonicity hold for every two tags. Append is the recursion of
that carrier, and its equations hold when the two tags are different. It is defined on sets
alone.

In a closed universe that has `ω` and the two tags as members, the lists over a member are a
member. The lists over the singleton of a closed universe are not a member of that universe:
the one-element list of the universe would put the universe inside itself.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetPolymorphicLists

open ZFSetUniverseClosure (Closed)
open ZFSetInductive (Fits Field Signature Constructor DistinctTags constructorValue carrier
  listSignature recFun constructor_mem_carrier carrier_induct recFun_constructor carrier_mem
  distinctTags_pair tags_mem_pair some_index_lt tuple)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation (numeral)
open scoped ZFSet

universe u

variable {s t : ZFSet.{u}}

/-! ## The set of lists -/

/-- The signature of the lists over `A`: the empty list with the tag `s`, and an element of
`A` before a list with the tag `t`. -/
def taggedListSignature (s t A : ZFSet.{u}) : Signature.{u} :=
  [⟨s, []⟩, ⟨t, [Field.ofSet A, Field.recursive]⟩]

/-- With the numerals `0` and `1` as tags it is the list signature. -/
theorem taggedListSignature_numerals (A : ZFSet.{u}) :
    taggedListSignature (numeral 0) (numeral 1) A = listSignature A := rfl

/-- Two different tags are distinct tags of the signature. -/
theorem taggedListSignature_distinct (distinct : s ≠ t) (A : ZFSet.{u}) :
    DistinctTags (taggedListSignature s t A) :=
  distinctTags_pair distinct

/-- The one set field of the signature is `A`. -/
theorem taggedListSignature_field {A B : ZFSet.{u}} {c : Constructor.{u}}
    (inSignature : c ∈ taggedListSignature s t A) (inConstructor : Field.ofSet B ∈ c.fields) :
    B = A := by
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

/-- The set of lists over `A`: the least set closed under the empty list and an element of `A`
before a list, the two carrying the tags `s` and `t`. -/
noncomputable abbrev listSet (s t A : ZFSet.{u}) : ZFSet.{u} := carrier (taggedListSignature s t A)

/-- The empty list: the value of the constructor with tag `s` at no argument. -/
def nilSet (s : ZFSet.{u}) : ZFSet.{u} := constructorValue s []

/-- An element before a list: the value of the constructor with tag `t` at the two. -/
def consSet (t a l : ZFSet.{u}) : ZFSet.{u} := constructorValue t [a, l]

/-- The empty list is a list over every set. -/
theorem nilSet_mem {A : ZFSet.{u}} : nilSet s ∈ listSet s t A :=
  constructor_mem_carrier (sig := taggedListSignature s t A) (i := 0) (c := ⟨s, []⟩)
    (args := []) rfl Fits.nil

/-- An element of `A` before a list over `A` is a list over `A`. -/
theorem consSet_mem {A a l : ZFSet.{u}} (ha : a ∈ A) (hl : l ∈ listSet s t A) :
    consSet t a l ∈ listSet s t A :=
  constructor_mem_carrier (sig := taggedListSignature s t A) (i := 1)
    (c := ⟨t, [Field.ofSet A, Field.recursive]⟩)
    (args := [a, l]) rfl (Fits.ofSet ha (Fits.recursive hl Fits.nil))

/-- Induction on the lists over `A`: a property of the empty list that passes from a list to an
element of `A` before it holds of every list over `A`. -/
theorem list_induct {A : ZFSet.{u}} {P : ZFSet.{u} → Prop} (nil : P (nilSet s))
    (cons : ∀ a l, a ∈ A → l ∈ listSet s t A → P l → P (consSet t a l)) :
    ∀ l, l ∈ listSet s t A → P l := by
  intro l member
  refine (carrier_induct (sig := taggedListSignature s t A)
    (P := fun y => y ∈ listSet s t A ∧ P y) ?_ member).2
  intro i c args atIndex fitting
  have bound := some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = ⟨s, []⟩ := (Option.some_inj).mp atIndex.symm
      subst hc
      cases (fitting : ZFSetInductive.FitsPred _ [] args)
      exact ⟨nilSet_mem, nil⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = ⟨t, [Field.ofSet A, Field.recursive]⟩ :=
            (Option.some_inj).mp atIndex.symm
          subst hc
          cases (fitting : ZFSetInductive.FitsPred _ [Field.ofSet A, Field.recursive] args) with
          | ofSet headMember tailFit =>
              cases tailFit with
              | recursive tail rest =>
                  cases rest
                  exact ⟨consSet_mem headMember tail.1, cons _ _ headMember tail.1 tail.2⟩
      | succ i => exact (Nat.not_lt.mpr (Nat.le_add_left 2 i) bound).elim

/-- Lists over a smaller set of elements are lists over a larger one. -/
theorem listSet_mono {A B : ZFSet.{u}} (sub : A ⊆ B) : listSet s t A ⊆ listSet s t B :=
  list_induct (P := fun l => l ∈ listSet s t B) nilSet_mem
    (fun _ _ ha _ ih => consSet_mem (sub ha) ih)

/-- In a closed universe that has `ω` and the two tags as members, the lists over a member are
a member. -/
theorem listSet_mem_of_closed {U A : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (hs : s ∈ U) (ht : t ∈ U) (hA : A ∈ U) : listSet s t A ∈ U :=
  carrier_mem closed hω (tags_mem_pair hs ht) fun c hc B hB => by
    rw [taggedListSignature_field hc hB]
    exact hA

/-- The lists over the singleton of a closed universe are not a member of that universe: the
one-element list of the universe would put the universe inside itself. -/
theorem listSet_singleton_not_mem {U : ZFSet.{u}} (closed : Closed U) :
    listSet s t ({U} : ZFSet.{u}) ∉ U := by
  intro member
  have one : consSet t U (nilSet s) ∈ listSet s t ({U} : ZFSet.{u}) :=
    consSet_mem (ZFSet.mem_singleton.mpr rfl) nilSet_mem
  have oneU : consSet t U (nilSet s) ∈ U := closed.transitive.mem_trans one member
  have shell : ({t, tuple [U, nilSet s]} : ZFSet.{u}) ∈ consSet t U (nilSet s) :=
    ZFSet.mem_pair.mpr (Or.inr rfl)
  have shellU : ({t, tuple [U, nilSet s]} : ZFSet.{u}) ∈ U :=
    closed.transitive.mem_trans shell oneU
  have tupleMem : tuple [U, nilSet s] ∈ ({t, tuple [U, nilSet s]} : ZFSet.{u}) :=
    ZFSet.mem_pair.mpr (Or.inr rfl)
  have tupleU : tuple [U, nilSet s] ∈ U := closed.transitive.mem_trans tupleMem shellU
  have inner : ({U, tuple [nilSet s]} : ZFSet.{u}) ∈ tuple [U, nilSet s] :=
    ZFSet.mem_pair.mpr (Or.inr rfl)
  have innerU : ({U, tuple [nilSet s]} : ZFSet.{u}) ∈ U :=
    closed.transitive.mem_trans inner tupleU
  have uMem : U ∈ ({U, tuple [nilSet s]} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
  exact ZFSet.mem_irrefl _ (closed.transitive.mem_trans uMem innerU)

/-! ## Append -/

/-- What the recursion of append does at a constructor: the identity at the empty list, and at
an element `a` before a list the function that puts `a` before the value of the recursive
function. -/
noncomputable def appendCase (s t A : ZFSet.{u}) (i : Nat) (args recs : List ZFSet.{u}) :
    ZFSet.{u} :=
  if i = 0 then traceLam (graph (listSet s t A) fun ys => ys)
  else
    match args, recs with
    | a :: _, r :: _ => traceLam (graph (listSet s t A) fun ys => consSet t a (traceApp r ys))
    | _, _ => ∅

/-- The function of a list, by the recursion of the set of lists over `A`. -/
noncomputable def appendFun (s t A : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  recFun (sig := taggedListSignature s t A) (appendCase s t A)

/-- The append of two sets: the function of the first, applied to the second. -/
noncomputable def setAppend (s t A l ys : ZFSet.{u}) : ZFSet.{u} :=
  traceApp (appendFun s t A l) ys

/-- The function of the empty list is the identity on lists. -/
theorem appendFun_nil (distinct : s ≠ t) (A : ZFSet.{u}) :
    appendFun s t A (nilSet s) = traceLam (graph (listSet s t A) fun ys => ys) :=
  recFun_constructor (sig := taggedListSignature s t A) (taggedListSignature_distinct distinct A)
    (appendCase s t A) (i := 0) (c := ⟨s, []⟩) (args := []) rfl Fits.nil

/-- The function of an element before a list puts the element before the values of the function
of the list. -/
theorem appendFun_cons (distinct : s ≠ t) {A a l : ZFSet.{u}} (ha : a ∈ A)
    (hl : l ∈ listSet s t A) :
    appendFun s t A (consSet t a l) =
      traceLam (graph (listSet s t A) fun ys => consSet t a (traceApp (appendFun s t A l) ys)) :=
  recFun_constructor (sig := taggedListSignature s t A) (taggedListSignature_distinct distinct A)
    (appendCase s t A) (i := 1) (c := ⟨t, [Field.ofSet A, Field.recursive]⟩)
    (args := [a, l]) rfl (Fits.ofSet ha (Fits.recursive hl Fits.nil))

/-- The empty list appended to a list is the list. -/
theorem setAppend_nil (distinct : s ≠ t) {A ys : ZFSet.{u}} (hys : ys ∈ listSet s t A) :
    setAppend s t A (nilSet s) ys = ys := by
  rw [setAppend, appendFun_nil distinct A, traceApp_graph_beta _ hys]

/-- An element before a list, appended to a list, is the element before the append. -/
theorem setAppend_cons (distinct : s ≠ t) {A a l ys : ZFSet.{u}} (ha : a ∈ A)
    (hl : l ∈ listSet s t A) (hys : ys ∈ listSet s t A) :
    setAppend s t A (consSet t a l) ys = consSet t a (setAppend s t A l ys) := by
  rw [setAppend, appendFun_cons distinct ha hl, traceApp_graph_beta _ hys]
  rfl

/-- The append of two lists over `A` is a list over `A`. -/
theorem setAppend_mem (distinct : s ≠ t) {A : ZFSet.{u}} :
    ∀ l, l ∈ listSet s t A → ∀ ys, ys ∈ listSet s t A → setAppend s t A l ys ∈ listSet s t A :=
  list_induct (P := fun l => ∀ ys, ys ∈ listSet s t A → setAppend s t A l ys ∈ listSet s t A)
    (fun ys hys => by
      rw [setAppend_nil distinct hys]
      exact hys)
    (fun _ _ ha hl ih ys hys => by
      rw [setAppend_cons distinct ha hl hys]
      exact consSet_mem ha (ih ys hys))

/-- Append is the only function on lists over `A` with the two equations. -/
theorem setAppend_unique (distinct : s ≠ t) {A : ZFSet.{u}}
    (g : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (nil : ∀ ys, ys ∈ listSet s t A → g (nilSet s) ys = ys)
    (cons : ∀ a l ys, a ∈ A → l ∈ listSet s t A → ys ∈ listSet s t A →
      g (consSet t a l) ys = consSet t a (g l ys)) :
    ∀ l, l ∈ listSet s t A → ∀ ys, ys ∈ listSet s t A → g l ys = setAppend s t A l ys :=
  list_induct (P := fun l => ∀ ys, ys ∈ listSet s t A → g l ys = setAppend s t A l ys)
    (fun ys hys => by rw [nil ys hys, setAppend_nil distinct hys])
    (fun a l ha hl ih ys hys => by
      rw [cons a l ys ha hl hys, setAppend_cons distinct ha hl hys, ih ys hys])

/-- A list appended to the empty list is the list. -/
theorem setAppend_nil_right (distinct : s ≠ t) {A : ZFSet.{u}} :
    ∀ l, l ∈ listSet s t A → setAppend s t A l (nilSet s) = l :=
  list_induct (P := fun l => setAppend s t A l (nilSet s) = l)
    (setAppend_nil distinct nilSet_mem)
    (fun _ _ ha hl ih => by rw [setAppend_cons distinct ha hl nilSet_mem, ih])

/-- Append is associative on lists over `A`. -/
theorem setAppend_assoc (distinct : s ≠ t) {A : ZFSet.{u}} :
    ∀ xs, xs ∈ listSet s t A → ∀ ys, ys ∈ listSet s t A → ∀ zs, zs ∈ listSet s t A →
      setAppend s t A (setAppend s t A xs ys) zs =
        setAppend s t A xs (setAppend s t A ys zs) :=
  list_induct
    (P := fun xs => ∀ ys, ys ∈ listSet s t A → ∀ zs, zs ∈ listSet s t A →
      setAppend s t A (setAppend s t A xs ys) zs =
        setAppend s t A xs (setAppend s t A ys zs))
    (fun ys hys zs hzs => by
      rw [setAppend_nil distinct hys,
        setAppend_nil distinct (setAppend_mem distinct ys hys zs hzs)])
    (fun _ xs ha hxs ih ys hys zs hzs => by
      have appended : setAppend s t A xs ys ∈ listSet s t A :=
        setAppend_mem distinct xs hxs ys hys
      rw [setAppend_cons distinct ha hxs hys, setAppend_cons distinct ha appended hzs,
        setAppend_cons distinct ha hxs (setAppend_mem distinct ys hys zs hzs), ih ys hys zs hzs])

/-- Negative example: with one tag on the two constructors the empty list is not told apart
from an element before a list by its tag, and the tags of the signature are not distinct. -/
theorem taggedListSignature_not_distinct (s A : ZFSet.{u}) :
    ¬ DistinctTags (taggedListSignature s s A) := by
  intro distinct
  have twice : [s, s].Nodup := distinct
  exact (List.nodup_cons.mp twice).1 (List.mem_singleton.mpr rfl)

end Mettapedia.Logic.HOL.Embedding.ZFSetPolymorphicLists
