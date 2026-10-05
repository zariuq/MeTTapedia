import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Lists
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates

/-!
# A stream over a set, by an equation that calls itself

Over the tower inside the sets, one family declares streams at a set:

* `Stream : set → set`
* `scons : Π (A : set). A → Stream A → Stream A`
* `shead : Π (A : set). Stream A → A`
* `stail : Π (A : set). Stream A → Stream A`
* `iter : Π (A : set). (A → A) → A → Stream A`

with

* `shead A (scons A a s) ⟶ a`
* `stail A (scons A a s) ⟶ s`
* `iter A f a ⟶ scons A a (iter A f (f a))`

The third equation produces a new `iter` on every use. Its meaning is a set that satisfies
the equation. Streams over `A` are the functions from `ω` into `A`. `iter A f a` is the
sequence `n ↦ fⁿ a`. The same process read as a labelled graph with one edge out of every node
is a hyperset, and the two readings determine each other: the hyperset of the graph and the
stream of its labels (`MegalodonHOTG.Hypersets`, `solveLabelledValue_eq_iff_labelCodeStream_eq`).

The typings of the five constants hold in every package over the family (`OverStreams`).
In a package that also contains the steps of the family (`ComputesAsStreams`), the three
equations hold at all typed instances. The package is formed, a set model satisfies its
equations, no closed term has type `Π (A : set). A`, and the erasure of `iter` is not
strongly normalizing, also where `iter` is typed in a formed context (`iter_typed_not_sn`):
the strong normalization of families of constants with no equation (`constants_sn`) does not
extend to a family with equations. A finite run of `shead` on `iter` still reaches the value
the set model gives it. The observation `shead A (iter A f a)` is the two-step run, and
`shead A (stail A (iter A f a))` is the four-step run.

Two members of `Stream A` that hold the same element at every position are equal
(`streams_ext`). The element at position `k` is `shead` after `stail` has been used `k` times
(`observeSet`); the model reads that as the value of the function at the numeral `k`. The
positions are also the pairs reached from the two streams by applying `stail` to both. That
is the least relation holding of the pair and closed under the two tails (`TailReach`). A
pair lies in it exactly when the two components are the tails at one common count
(`tailReach_iff`), and agreement of `shead` at every such pair is the same equality
(`streams_ext_tailReach`). The relation leaves some pairs out (`tailReach_not_all`). Two
streams that differ at one position are different (`streams_ne_of_observe_ne`). The numbers
from zero, and zero in front of the numbers from five, agree at the first position and differ
at the next, so agreement at the first position is not enough (`not_streams_ext_at_first`).
The judgment of the package states an equality of two typed terms. It does not put "at every
position" into one hypothesis; that quantification is this fact about the values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace Streams

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.StrongNormalization
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetPolymorphicLists
open ZFSetInductive (tuple rank_gt_first rank_gt_second)
open ZFSetUniverseClosure (Closed CofinalInaccessibles)
open ZFSetUniverseLift (carrierCode carrierCode_closed omega_mem_carrierCode)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open ZFSetDependentProducts (graph graph_congr)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta tracePiSet_congr)

universe u

variable {L : Type}

/-! ## Streams as sets -/

section InSets

/-- A stream over `A`: a function from the natural numbers into `A`. -/
noncomputable def streamSet (A : ZFSet.{u}) : ZFSet.{u} :=
  tracePiSet ZFSet.omega (fun _ => A)

/-- The element at the front of a stream, and the stream shifted by one, read at a number. -/
noncomputable def sconsAt (a s n : ZFSet.{u}) : ZFSet.{u} :=
  if natOf n = 0 then a else traceApp s (numeral (natOf n - 1))

/-- A stream with one element in front. -/
noncomputable def sconsSet (a s : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega (sconsAt a s))

/-- The first element of a stream. -/
noncomputable def sheadSet (s : ZFSet.{u}) : ZFSet.{u} :=
  traceApp s (numeral 0)

/-- A stream with the first element dropped. -/
noncomputable def stailSet (s : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega (fun n => traceApp s (insert n n)))

/-- Iteration of a set function: the value, then the function applied to the previous value. -/
noncomputable def iterate (f a : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => a
  | k + 1 => traceApp f (iterate f a k)

/-- The stream of iterates of a function at a value. -/
noncomputable def iterSet (f a : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega (fun n => iterate f a (natOf n)))

/-- In a closed universe that has `ω` and `A`, the streams over `A` are a member. -/
theorem streamSet_mem {U A : ZFSet.{u}} (closed : Closed U) (hω : ZFSet.omega ∈ U)
    (hA : A ∈ U) : streamSet A ∈ U :=
  closed.tracePiSet_mem hω (fun _ => A) (fun _ _ => hA)

/-- The successor of a number, read as a numeral, is one larger. -/
theorem natOf_insert {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    natOf (insert n n) = natOf n + 1 := by
  rw [← numeral_natOf hn, ← numeral_succ, natOf_numeral, natOf_numeral]

/-- At zero, the front element is the element put in front. -/
theorem sconsAt_zero (a s : ZFSet.{u}) : sconsAt a s (numeral 0) = a := by
  rw [sconsAt, natOf_numeral, if_pos rfl]

/-- One step later, the front of a stream is the previous stream. -/
theorem sconsAt_succ {a s n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    sconsAt a s (insert n n) = traceApp s n := by
  rw [sconsAt, natOf_insert hn, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel,
    numeral_natOf hn]

/-- An element of `A` in front of a stream over `A` is a stream over `A`. -/
theorem sconsSet_mem {A a s : ZFSet.{u}} (ha : a ∈ A) (hs : s ∈ streamSet A) :
    sconsSet a s ∈ streamSet A := by
  refine traceLam_graph_mem fun n _ => ?_
  cases hk : natOf n with
  | zero =>
      rw [sconsAt, hk, if_pos rfl]
      exact ha
  | succ k =>
      rw [sconsAt, hk, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
      exact traceApp_mem_fibre hs (numeral_mem_omega k)

/-- The first element of a stream over `A` lies in `A`. -/
theorem sheadSet_mem {A s : ZFSet.{u}} (hs : s ∈ streamSet A) : sheadSet s ∈ A :=
  traceApp_mem_fibre hs (numeral_mem_omega 0)

/-- The tail of a stream over `A` is a stream over `A`. -/
theorem stailSet_mem {A s : ZFSet.{u}} (hs : s ∈ streamSet A) : stailSet s ∈ streamSet A :=
  traceLam_graph_mem fun _ hn => traceApp_mem_fibre hs (insert_mem_omega hn)

/-- Iterates of a function that preserves `A` stay in `A`. -/
theorem iterate_mem {A f a : ZFSet.{u}} (hf : ∀ x ∈ A, traceApp f x ∈ A) (ha : a ∈ A) :
    ∀ k, iterate f a k ∈ A
  | 0 => ha
  | k + 1 => hf _ (iterate_mem hf ha k)

/-- The stream of iterates of a function that preserves `A`, at an element of `A`, is a stream
over `A`. -/
theorem iterSet_mem {A f a : ZFSet.{u}} (hf : ∀ x ∈ A, traceApp f x ∈ A) (ha : a ∈ A) :
    iterSet f a ∈ streamSet A :=
  traceLam_graph_mem fun _ _ => iterate_mem hf ha _

/-- Applying a function and then iterating is iterating and then applying the function. -/
theorem iterate_after (f a : ZFSet.{u}) :
    ∀ k, iterate f (traceApp f a) k = traceApp f (iterate f a k)
  | 0 => rfl
  | k + 1 => by rw [iterate, iterate_after f a k, iterate]

/-- The first element of an element put in front is that element. -/
theorem shead_scons_sets (a s : ZFSet.{u}) : sheadSet (sconsSet a s) = a := by
  unfold sheadSet sconsSet
  rw [traceApp_graph_beta _ (numeral_mem_omega 0), sconsAt_zero]

/-- The tail of an element put in front of a stream over `A` is that stream. -/
theorem stail_scons_sets {A a s : ZFSet.{u}} (ha : a ∈ A) (hs : s ∈ streamSet A) :
    stailSet (sconsSet a s) = s := by
  apply tracePiSet_ext (stailSet_mem (sconsSet_mem ha hs)) hs
  intro n hn
  rw [stailSet, traceApp_graph_beta _ hn, sconsSet,
    traceApp_graph_beta _ (insert_mem_omega hn), sconsAt_succ hn]

/-- Iteration satisfies the stream equation: the value, then the iterates of the next value. -/
theorem iter_scons_sets (f a : ZFSet.{u}) :
    iterSet f a = sconsSet a (iterSet f (traceApp f a)) := by
  have point : ∀ n ∈ ZFSet.omega, iterate f a (natOf n) =
      sconsAt a (iterSet f (traceApp f a)) n := by
    intro n _
    cases hk : natOf n with
    | zero =>
        rw [sconsAt, hk, if_pos rfl]
        rfl
    | succ k =>
        rw [sconsAt, hk, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, iterate]
        rw [iterSet, traceApp_graph_beta _ (numeral_mem_omega k), natOf_numeral, ← iterate_after]
  unfold iterSet sconsSet
  exact congrArg traceLam (graph_congr point)

/-- No set is the cons of an element onto itself, whatever tag the cons carries: the element
would sit inside its own rank. -/
theorem consSet_ne_self (t a l : ZFSet.{u}) : l ≠ consSet t a l := by
  intro same
  have lt : l.rank < (consSet t a l).rank :=
    calc
      l.rank < (tuple [l]).rank := rank_gt_first l ∅
      _ < (tuple [a, l]).rank := rank_gt_second a (tuple [l])
      _ < (consSet t a l).rank := rank_gt_second t (tuple [a, l])
  exact (ne_of_lt lt) (congrArg (fun z : ZFSet.{u} => z.rank) same)

/-- The element a stream holds at a position: `shead` after `stail` has been used that many
times. -/
noncomputable def observeSet : ℕ → ZFSet.{u} → ZFSet.{u}
  | 0, s => sheadSet s
  | k + 1, s => observeSet k (stailSet s)

theorem observeSet_succ (k : ℕ) (s : ZFSet.{u}) :
    observeSet (k + 1) s = observeSet k (stailSet s) := rfl

/-- Shifting a stream `k` times and reading the first element is reading the function at the
numeral `k`. -/
theorem observeSet_eq_app {A s : ZFSet.{u}} (hs : s ∈ streamSet A) :
    ∀ k, observeSet k s = traceApp s (numeral k)
  | 0 => rfl
  | k + 1 => by
      rw [observeSet_succ, observeSet_eq_app (stailSet_mem hs), stailSet,
        traceApp_graph_beta _ (numeral_mem_omega k), numeral_succ]

/-- **Streams are their observations.** Two streams over one set whose elements agree at every
position are equal. The element at a position is `shead` of the stream shifted by `stail` that
many times. -/
theorem streams_ext {A s t : ZFSet.{u}} (hs : s ∈ streamSet A) (ht : t ∈ streamSet A)
    (agree : ∀ k, observeSet k s = observeSet k t) : s = t := by
  refine tracePiSet_ext hs ht fun x hx => ?_
  have same := agree (natOf x)
  rwa [observeSet_eq_app hs, observeSet_eq_app ht, numeral_natOf hx] at same

/-- A stream after `stail` has been used `k` times. -/
noncomputable def tailSet : ℕ → ZFSet.{u} → ZFSet.{u}
  | 0, s => s
  | k + 1, s => stailSet (tailSet k s)

theorem tailSet_succ (k : ℕ) (s : ZFSet.{u}) :
    tailSet (k + 1) s = stailSet (tailSet k s) := rfl

/-- Shifting first and then `k` times is the same stream as shifting `k` times and then once. -/
theorem tailSet_stail (k : ℕ) (s : ZFSet.{u}) :
    tailSet k (stailSet s) = stailSet (tailSet k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [tailSet_succ, tailSet_succ, ih]

/-- The element at position `k` is the head of the stream shifted `k` times. -/
theorem observeSet_eq_shead_tail (k : ℕ) (s : ZFSet.{u}) :
    observeSet k s = sheadSet (tailSet k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [observeSet_succ, ih, tailSet_stail, tailSet_succ]

/-- `(u, v)` lies in the least relation that holds of `(s, t)` and is closed under applying
`stail` to both components. -/
def TailReach (s t u v : ZFSet.{u}) : Prop :=
  ∀ Q : ZFSet.{u} → ZFSet.{u} → Prop,
    Q s t → (∀ x y, Q x y → Q (stailSet x) (stailSet y)) → Q u v

/-- **The pairs reached by the two tails are the tails at a common count.** `(u, v)` lies in
`TailReach s t` exactly when one `k` shifts `s` to `u` and `t` to `v`. -/
theorem tailReach_iff {s t u v : ZFSet.{u}} :
    TailReach s t u v ↔ ∃ k, u = tailSet k s ∧ v = tailSet k t := by
  constructor
  · intro reach
    exact reach (fun a b => ∃ k, a = tailSet k s ∧ b = tailSet k t) ⟨0, rfl, rfl⟩
      (fun x y ⟨k, hx, hy⟩ =>
        ⟨k + 1, by rw [tailSet_succ, hx], by rw [tailSet_succ, hy]⟩)
  · intro reached
    rcases reached with ⟨k, rfl, rfl⟩
    intro Q base step
    induction k with
    | zero => exact base
    | succ k ih => exact step _ _ ih

/-- **Streams that agree at every pair reached by `stail` are equal.** Agreement of `shead`
on `TailReach` is agreement of the observations at every position, and `streams_ext` gives
the two streams. -/
theorem streams_ext_tailReach {A s t : ZFSet.{u}} (hs : s ∈ streamSet A) (ht : t ∈ streamSet A)
    (agree : ∀ u v, TailReach s t u v → sheadSet u = sheadSet v) : s = t := by
  refine streams_ext hs ht fun k => ?_
  rw [observeSet_eq_shead_tail, observeSet_eq_shead_tail]
  exact agree _ _ (tailReach_iff.mpr ⟨k, rfl, rfl⟩)

/-- Two streams that hold different elements at one position are different streams. -/
theorem streams_ne_of_observe_ne {s t : ZFSet.{u}} {k : ℕ}
    (diff : observeSet k s ≠ observeSet k t) : s ≠ t :=
  fun same => diff (congrArg (observeSet k) same)

/-- The numbers from `n` on: position `k` holds `n + k`. -/
noncomputable def numbersFromSet (n : ℕ) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun x => numeral (n + natOf x))

theorem numbersFromSet_mem (n : ℕ) : numbersFromSet n ∈ streamSet ZFSet.omega :=
  traceLam_graph_mem fun _ _ => numeral_mem_omega _

theorem observe_numbersFromSet (n k : ℕ) :
    observeSet k (numbersFromSet n) = numeral (n + k) := by
  rw [observeSet_eq_app (numbersFromSet_mem n), numbersFromSet,
    traceApp_graph_beta _ (numeral_mem_omega k), natOf_numeral]

/-- The number `a` in front of the numbers from `n` on. -/
noncomputable def sconsFromSet (a n : ℕ) : ZFSet.{u} :=
  sconsSet (numeral a) (numbersFromSet n)

theorem sconsFromSet_mem (a n : ℕ) : sconsFromSet a n ∈ streamSet ZFSet.omega :=
  sconsSet_mem (numeral_mem_omega a) (numbersFromSet_mem n)

theorem sconsFrom_stail (a n : ℕ) : stailSet (sconsFromSet a n) = numbersFromSet n :=
  stail_scons_sets (numeral_mem_omega a) (numbersFromSet_mem n)

theorem observe_sconsFromSet_zero (a n : ℕ) :
    observeSet 0 (sconsFromSet a n) = numeral a := by
  unfold observeSet sconsFromSet
  rw [shead_scons_sets]

theorem observe_sconsFromSet_succ (a n k : ℕ) :
    observeSet (k + 1) (sconsFromSet a n) = numeral (n + k) := by
  rw [observeSet_succ, sconsFrom_stail, observe_numbersFromSet]

/-- **One unfolding is the same stream.** The numbers from `n` on, and `n` in front of the
numbers from `n + 1` on, agree at every position. -/
theorem numbersFrom_eq_sconsFrom (n : ℕ) :
    numbersFromSet n = sconsFromSet n (n + 1) :=
  streams_ext (numbersFromSet_mem n) (sconsFromSet_mem n (n + 1)) fun k => by
    cases k with
    | zero => rw [observe_numbersFromSet, observe_sconsFromSet_zero, Nat.add_zero]
    | succ k =>
        rw [observe_numbersFromSet, observe_sconsFromSet_succ, Nat.add_comm k 1, ← Nat.add_assoc]

/-- The numbers from zero and zero in front of the numbers from five agree at the first
position. -/
theorem from0_agrees_at_first :
    observeSet 0 (numbersFromSet 0) = observeSet 0 (sconsFromSet 0 5) := by
  rw [observe_numbersFromSet, observe_sconsFromSet_zero, Nat.add_zero]

/-- They differ at the next position: one holds one, the other holds five. -/
theorem from0_differs_at_one :
    observeSet 1 (numbersFromSet 0) ≠ observeSet 1 (sconsFromSet 0 5) := by
  rw [observe_numbersFromSet, observe_sconsFromSet_succ, Nat.zero_add, Nat.add_zero]
  intro same
  exact absurd (numeral_injective same) (by decide : (1 : ℕ) ≠ 5)

/-- So the two streams are not equal. -/
theorem from0_ne_scons0_from5 : numbersFromSet (0 : ℕ) ≠ sconsFromSet 0 5 :=
  streams_ne_of_observe_ne from0_differs_at_one

/-- **Agreement at the first position is not enough.** The same statement as `streams_ext`
with the hypothesis cut down to position zero is false. -/
theorem not_streams_ext_at_first :
    ¬ ∀ s t : ZFSet.{u},
      s ∈ streamSet ZFSet.omega → t ∈ streamSet ZFSet.omega →
      observeSet 0 s = observeSet 0 t → s = t := by
  intro claim
  exact from0_ne_scons0_from5
    (claim _ _ (numbersFromSet_mem 0) (sconsFromSet_mem 0 5) from0_agrees_at_first)

/-- **The tail relation is not every pair.** From the numbers from zero paired with
themselves, the pairs reached are a tail with that same tail. The numbers from zero with
the numbers from one lie outside it: the two streams differ at the first position. -/
theorem tailReach_not_all :
    ¬ TailReach (numbersFromSet 0) (numbersFromSet 0)
        (numbersFromSet 0) (numbersFromSet 1) := by
  intro reach
  obtain ⟨_k, hu, hv⟩ := tailReach_iff.mp reach
  have same : numbersFromSet 0 = numbersFromSet 1 := hu.trans hv.symm
  have heads := congrArg (observeSet 0) same
  rw [observe_numbersFromSet, observe_numbersFromSet, Nat.zero_add, Nat.add_zero] at heads
  exact absurd (numeral_injective heads) (by decide : (0 : ℕ) ≠ 1)

end InSets

/-! ## The constants and their types -/

variable [LevelOrder L]

section Terms

variable {n : Nat}

/-- The set of streams over a set. -/
def streamN : DeclName := .str .anonymous "Stream"

/-- An element before a stream. -/
def sconsN : DeclName := .str .anonymous "scons"

/-- The first element of a stream. -/
def sheadN : DeclName := .str .anonymous "shead"

/-- A stream with the first element dropped. -/
def stailN : DeclName := .str .anonymous "stail"

/-- The stream of iterates of a function. -/
def iterN : DeclName := .str .anonymous "iter"

/-- `Stream A`. -/
abbrev cStream (A : CTm (Head L) n) : CTm (Head L) n := .app (.const streamN) A

/-- `scons A a s`. -/
abbrev cScons (A a s : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const sconsN) A) a) s

/-- `shead A s`. -/
abbrev cShead (A s : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.const sheadN) A) s

/-- `stail A s`. -/
abbrev cStail (A s : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.const stailN) A) s

/-- `iter A f a`. -/
abbrev cIter (A f a : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const iterN) A) f) a

/-- The type of `Stream`: a set gives a set. -/
abbrev streamType : CTm (Head L) n := .pi allSets allSets

/-- The type of `scons`. -/
abbrev sconsType : CTm (Head L) n :=
  .pi allSets (.pi (.var 0) (.pi (cStream (.var 1)) (cStream (.var 2))))

/-- The type of `shead`. -/
abbrev sheadType : CTm (Head L) n :=
  .pi allSets (.pi (cStream (.var 0)) (.var 1))

/-- The type of `stail`. -/
abbrev stailType : CTm (Head L) n :=
  .pi allSets (.pi (cStream (.var 0)) (cStream (.var 1)))

/-- The type of `iter`. -/
abbrev iterType : CTm (Head L) n :=
  .pi allSets (.pi (.pi (.var 0) (.var 1)) (.pi (.var 1) (cStream (.var 2))))

end Terms

variable (L) in
/-- The table of the family: each constant with its type. -/
def streamTable : List (DeclName × CTm (Head L) 0) :=
  [(streamN, streamType), (sconsN, sconsType), (sheadN, sheadType), (stailN, stailType),
    (iterN, iterType)]

variable (L) in
/-- The declarations of the family. -/
def streamDecls : DeclName → Option (CTm (Head L) 0) := tableLookup (streamTable L)

variable (L) in
/-- `shead A (scons A a s) ⟶ a`. -/
def sheadScons : DefiningEquation (Head L) where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil allSets) (.var 0)) (cStream (.var 1))
  left := cShead (.var 2) (cScons (.var 2) (.var 1) (.var 0))
  right := .var 1

variable (L) in
/-- `stail A (scons A a s) ⟶ s`. -/
def stailScons : DefiningEquation (Head L) where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil allSets) (.var 0)) (cStream (.var 1))
  left := cStail (.var 2) (cScons (.var 2) (.var 1) (.var 0))
  right := .var 0

variable (L) in
/-- `iter A f a ⟶ scons A a (iter A f (f a))`. -/
def iterEquation : DefiningEquation (Head L) where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil allSets) (.pi (.var 0) (.var 1))) (.var 1)
  left := cIter (.var 2) (.var 1) (.var 0)
  right := cScons (.var 2) (.var 0) (cIter (.var 2) (.var 1) (.app (.var 1) (.var 0)))

variable (L) in
/-- The equations of the family. -/
def streamEquations : List (DefiningEquation (Head L)) :=
  [sheadScons L, stailScons L, iterEquation L]

variable (L) in
/-- The tower inside the sets with the stream family. -/
abbrev streamFamily := withFamily (bare L) (streamDecls L) (streamEquations L)

variable (L) in
/-- The rules of the package: the tower, and the erased equations of the family. -/
abbrev streamRules : Rules (Head L) :=
  Rules.sum (rules L) (familyRules (rules L) (streamDecls L) (streamEquations L))

section Declared

omit [LevelOrder L]

/-- `Stream` is declared at `set → set`. -/
theorem streamDecls_stream : streamDecls L streamN = some streamType := rfl

/-- `scons` is declared at its type. -/
theorem streamDecls_scons : streamDecls L sconsN = some sconsType := rfl

/-- `shead` is declared at its type. -/
theorem streamDecls_shead : streamDecls L sheadN = some sheadType := rfl

/-- `stail` is declared at its type. -/
theorem streamDecls_stail : streamDecls L stailN = some stailType := rfl

/-- `iter` is declared at its type. -/
theorem streamDecls_iter : streamDecls L iterN = some iterType := rfl

/-- The equation of `shead` on `scons` is one of the family's equations. -/
theorem sheadScons_member : sheadScons L ∈ streamEquations L :=
  List.mem_cons_self

/-- The equation of `stail` on `scons` is one of the family's equations. -/
theorem stailScons_member : stailScons L ∈ streamEquations L :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- The equation of `iter` is one of the family's equations. -/
theorem iterEquation_member : iterEquation L ∈ streamEquations L :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

end Declared

/-! ## The values -/

section Values

variable (all : ZFSet.{u})

/-- `Stream` as a set: the trace function sending a set to its streams. -/
noncomputable def streamValue : ZFSet.{u} := traceLam (graph all streamSet)

/-- `scons` as a set. -/
noncomputable def sconsValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph A fun a =>
    traceLam (graph (streamSet A) fun s => sconsSet a s)))

/-- `shead` as a set. -/
noncomputable def sheadValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph (streamSet A) fun s => sheadSet s))

/-- `stail` as a set. -/
noncomputable def stailValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph (streamSet A) fun s => stailSet s))

/-- `iter` as a set. -/
noncomputable def iterValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph (tracePiSet A fun _ => A) fun f =>
    traceLam (graph A fun a => iterSet f a)))

/-- The table of the values. -/
noncomputable def streamValueTable : List (DeclName × ZFSet.{u}) :=
  [(streamN, streamValue all), (sconsN, sconsValue all), (sheadN, sheadValue all),
    (stailN, stailValue all), (iterN, iterValue all)]

/-- The values of the constants. -/
noncomputable def streamValues : DeclName → ZFSet.{u} := fun c =>
  (tableLookup (streamValueTable all) c).getD ∅

/-- The value of `Stream`. -/
theorem streamValues_stream : streamValues all streamN = streamValue all := rfl

/-- The value of `scons`. -/
theorem streamValues_scons : streamValues all sconsN = sconsValue all := rfl

/-- The value of `shead`. -/
theorem streamValues_shead : streamValues all sheadN = sheadValue all := rfl

/-- The value of `stail`. -/
theorem streamValues_stail : streamValues all stailN = stailValue all := rfl

/-- The value of `iter`. -/
theorem streamValues_iter : streamValues all iterN = iterValue all := rfl

/-- `iter` at a set, a function on that set and an element is the stream of iterates. -/
theorem iterValue_at {A f a : ZFSet.{u}} (hA : A ∈ all)
    (hf : f ∈ tracePiSet A (fun _ => A)) (ha : a ∈ A) :
    traceApp (traceApp (traceApp (iterValue all) A) f) a = iterSet f a := by
  unfold iterValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hf, traceApp_graph_beta _ ha]

end Values

/-! ## The set model -/

section Model

variable {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}} {ν : Nat → Above L}
  {consts : DeclName → ZFSet.{u}}

/-- An assignment that gives the constants of the family their values on a universe of sets. -/
abbrev Reads (all : ZFSet.{u}) (consts : DeclName → ZFSet.{u}) : Prop :=
  ∀ c, streamDecls L c ≠ none → consts c = streamValues all c

omit [LevelOrder L] in
/-- The value an assignment gives a constant of the family. -/
theorem Reads.at {all : ZFSet.{u}} (reads : Reads (L := L) all consts) {c : DeclName}
    {T : CTm (Head L) 0} {value : ZFSet.{u}} (declared : streamDecls L c = some T)
    (known : streamValues all c = value) : consts c = value :=
  (reads c (by rw [declared]; exact Option.some_ne_none T)).trans known

section Readings

variable {all : ZFSet.{u}} (reads : Reads (L := L) all consts)

include reads

omit [LevelOrder L] in
/-- The assignment reads `Stream` as `streamSet`. -/
theorem Reads.stream : consts streamN = streamValue all :=
  Reads.at reads streamDecls_stream rfl

omit [LevelOrder L] in
/-- The assignment reads `scons` as cons of streams. -/
theorem Reads.scons : consts sconsN = sconsValue all :=
  Reads.at reads streamDecls_scons rfl

omit [LevelOrder L] in
/-- The assignment reads `shead` as the first element. -/
theorem Reads.shead : consts sheadN = sheadValue all :=
  Reads.at reads streamDecls_shead rfl

omit [LevelOrder L] in
/-- The assignment reads `stail` as the tail. -/
theorem Reads.stail : consts stailN = stailValue all :=
  Reads.at reads streamDecls_stail rfl

omit [LevelOrder L] in
/-- The assignment reads `iter` as iteration. -/
theorem Reads.iter : consts iterN = iterValue all :=
  Reads.at reads streamDecls_iter rfl

include reads in
omit [LevelOrder L] in
/-- `Stream` applied to a set is the set of streams over it. -/
theorem Reads.streamBeta {x : ZFSet.{u}} (hx : x ∈ all) :
    traceApp (consts streamN) x = streamSet x := by
  rw [reads.stream]
  unfold streamValue
  rw [traceApp_graph_beta _ hx]

end Readings

variable (reads : Reads (L := L) (V (.above 0)) consts) (chain : ClosedChain V)
  (omegaMem : ZFSet.omega ∈ V (.above 0))

include reads chain omegaMem in
/-- Every value lies in the set of its constant's type. -/
theorem streamValues_typed {c : DeclName} {T : CTm (Head L) 0}
    (declared : streamDecls L c = some T) :
    streamValues (V (.above 0)) c ∈ ev (chainHead V ground ν) consts T Fin.elim0 := by
  have row := tableLookup_mem declared
  simp only [streamTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | row
  · exact traceLam_graph_mem fun A hA =>
      streamSet_mem (chain.closed (.above 0)) omegaMem hA
  rcases row with ⟨rfl, rfl⟩ | row
  · change sconsValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun A =>
        tracePiSet A (fun _ => tracePiSet (traceApp (consts streamN) A)
          (fun _ => traceApp (consts streamN) A)))
    rw [reads.stream]
    exact traceLam_graph_mem fun A hA => by
      have beta : traceApp (streamValue (V (.above 0))) A = streamSet A :=
        traceApp_graph_beta _ hA
      have fibres : tracePiSet (traceApp (streamValue (V (.above 0))) A)
          (fun _ => traceApp (streamValue (V (.above 0))) A) =
          tracePiSet (streamSet A) (fun _ => streamSet A) := by
        rw [beta]
      refine traceLam_graph_mem fun a ha => ?_
      rw [fibres]
      exact traceLam_graph_mem fun s hs => sconsSet_mem ha hs
  rcases row with ⟨rfl, rfl⟩ | row
  · change sheadValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun A =>
        tracePiSet (traceApp (consts streamN) A) (fun _ => A))
    rw [reads.stream]
    exact traceLam_graph_mem fun A hA => by
      have beta : traceApp (streamValue (V (.above 0))) A = streamSet A :=
        traceApp_graph_beta _ hA
      rw [beta]
      exact traceLam_graph_mem fun s hs => sheadSet_mem hs
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change stailValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun A =>
        tracePiSet (traceApp (consts streamN) A)
          (fun _ => traceApp (consts streamN) A))
    rw [reads.stream]
    exact traceLam_graph_mem fun A hA => by
      have beta : traceApp (streamValue (V (.above 0))) A = streamSet A :=
        traceApp_graph_beta _ hA
      have fibres : tracePiSet (traceApp (streamValue (V (.above 0))) A)
          (fun _ => traceApp (streamValue (V (.above 0))) A) =
          tracePiSet (streamSet A) (fun _ => streamSet A) := by
        rw [beta]
      rw [fibres]
      exact traceLam_graph_mem fun s hs => stailSet_mem hs
  · change iterValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun A =>
        tracePiSet (tracePiSet A (fun _ => A)) (fun _ =>
          tracePiSet A (fun _ => traceApp (consts streamN) A)))
    rw [reads.stream]
    exact traceLam_graph_mem fun A hA => by
      have beta : traceApp (streamValue (V (.above 0))) A = streamSet A :=
        traceApp_graph_beta _ hA
      refine traceLam_graph_mem fun f hf => ?_
      rw [beta]
      exact traceLam_graph_mem fun a ha =>
        iterSet_mem (fun x hx => traceApp_mem_fibre hf hx) ha

include reads in
/-- The first element of an element put in front is that element, as values. -/
theorem sheadScons_valid (η : Env.{u} 3)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc (.snoc .nil allSets) (.var 0)) (cStream (.var 1)) : CCtx (Head L) 3) η) :
    ev (chainHead V ground ν) consts
        (cShead (.var 2) (cScons (.var 2) (.var 1) (.var 0)) : CTm (Head L) 3) η =
      ev (chainHead V ground ν) consts (.var (1 : Fin 3)) η := by
  have hA : η 2 ∈ V (.above 0) := sat 2
  have ha : η 1 ∈ η 2 := sat 1
  have hs : η 0 ∈ streamSet (η 2) := by
    have member := sat 0
    change η 0 ∈ traceApp (consts streamN) (η 2) at member
    rw [reads.streamBeta hA] at member
    exact member
  show traceApp (traceApp (consts sheadN) (η 2))
      (traceApp (traceApp (traceApp (consts sconsN) (η 2)) (η 1)) (η 0)) = η 1
  rw [reads.shead, reads.scons]
  unfold sheadValue sconsValue
  rw [traceApp_graph_beta _ hA]
  rw [traceApp_graph_beta _ hA]
  rw [traceApp_graph_beta _ ha, traceApp_graph_beta _ hs]
  have consed : sconsSet (η 1) (η 0) ∈ streamSet (η 2) := sconsSet_mem ha hs
  rw [traceApp_graph_beta _ consed]
  exact shead_scons_sets (η 1) (η 0)

include reads in
/-- The tail of an element put in front is the stream, as values. -/
theorem stailScons_valid (η : Env.{u} 3)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc (.snoc .nil allSets) (.var 0)) (cStream (.var 1)) : CCtx (Head L) 3) η) :
    ev (chainHead V ground ν) consts
        (cStail (.var 2) (cScons (.var 2) (.var 1) (.var 0)) : CTm (Head L) 3) η =
      ev (chainHead V ground ν) consts (.var (0 : Fin 3)) η := by
  have hA : η 2 ∈ V (.above 0) := sat 2
  have ha : η 1 ∈ η 2 := sat 1
  have hs : η 0 ∈ streamSet (η 2) := by
    have member := sat 0
    change η 0 ∈ traceApp (consts streamN) (η 2) at member
    rw [reads.streamBeta hA] at member
    exact member
  have consed : sconsSet (η 1) (η 0) ∈ streamSet (η 2) := sconsSet_mem ha hs
  show traceApp (traceApp (consts stailN) (η 2))
      (traceApp (traceApp (traceApp (consts sconsN) (η 2)) (η 1)) (η 0)) = η 0
  rw [reads.stail, reads.scons]
  unfold stailValue sconsValue
  rw [traceApp_graph_beta _ hA]
  rw [traceApp_graph_beta _ hA]
  rw [traceApp_graph_beta _ ha, traceApp_graph_beta _ hs, traceApp_graph_beta _ consed]
  exact stail_scons_sets ha hs

include reads in
/-- Iteration is the element in front of the iterates of the next value, as values. -/
theorem iter_valid (η : Env.{u} 3)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc (.snoc .nil allSets) (.pi (.var 0) (.var 1))) (.var 1) :
        CCtx (Head L) 3) η) :
    ev (chainHead V ground ν) consts
        (cIter (.var 2) (.var 1) (.var 0) : CTm (Head L) 3) η =
      ev (chainHead V ground ν) consts
        (cScons (.var 2) (.var 0) (cIter (.var 2) (.var 1) (.app (.var 1) (.var 0))) :
          CTm (Head L) 3) η := by
  have hA : η 2 ∈ V (.above 0) := sat 2
  have ha : η 0 ∈ η 2 := sat 0
  have hf : η 1 ∈ tracePiSet (η 2) (fun _ => η 2) := by
    have member := sat 1
    change η 1 ∈ tracePiSet (η 2) (fun _ => η 2) at member
    exact member
  have hfa : traceApp (η 1) (η 0) ∈ η 2 := traceApp_mem_fibre hf ha
  have tailMem : iterSet (η 1) (traceApp (η 1) (η 0)) ∈ streamSet (η 2) :=
    iterSet_mem (fun x hx => traceApp_mem_fibre hf hx) hfa
  show traceApp (traceApp (traceApp (consts iterN) (η 2)) (η 1)) (η 0) =
    traceApp (traceApp (traceApp (consts sconsN) (η 2)) (η 0))
      (traceApp (traceApp (traceApp (consts iterN) (η 2)) (η 1)) (traceApp (η 1) (η 0)))
  rw [reads.iter, reads.scons]
  unfold iterValue sconsValue
  rw [traceApp_graph_beta _ hA]
  rw [traceApp_graph_beta _ hA]
  rw [traceApp_graph_beta _ hf]
  rw [traceApp_graph_beta _ ha]
  rw [traceApp_graph_beta _ ha]
  rw [traceApp_graph_beta _ hfa, traceApp_graph_beta _ tailMem]
  exact iter_scons_sets (η 1) (η 0)

include reads in
/-- The three equations hold between sets, at every environment of their telescope. -/
theorem streamEquations_valid :
    ∀ e ∈ streamEquations L, ∀ η : Env.{u} e.arity,
      Sat (chainHead V ground ν) consts e.telescope η →
        ev (chainHead V ground ν) consts e.left η =
          ev (chainHead V ground ν) consts e.right η := by
  intro e member η sat
  have cases : e = sheadScons L ∨ e = stailScons L ∨ e = iterEquation L := by
    simpa [streamEquations] using member
  rcases cases with rfl | rest
  · exact sheadScons_valid reads η sat
  rcases rest with rfl | rfl
  · exact stailScons_valid reads η sat
  · exact iter_valid reads η sat

include chain omegaMem ν in
/-- The stream family has a set model over every chain of closed universes that has `ω` in the
universe of the sets. -/
theorem streamFamily_setModel (groundTyped : ground ∈ V LevelOrder.bot)
    (base : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν)
      (familyConsts base (streamDecls L) (streamValues (V (.above 0)))) (streamFamily L) :=
  family_setModel_read (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts) (fun _ _ => rfl)
    (streamValues (V (.above 0)))
    (fun _ _ reads {_ _} declared => streamValues_typed reads chain omegaMem declared)
    (fun _ _ reads => streamEquations_valid reads)

include chain omegaMem ν in
/-- No closed term has type `Π (A : set). A`: the empty set is a set, so no trace function
picks an element of every set. -/
theorem no_closed_element_of_every_set (groundTyped : ground ∈ V LevelOrder.bot)
    (base : DeclName → ZFSet.{u}) (t : CTm (Head L) 0) :
    ¬ CTyped (streamFamily L) .nil t (.pi allSets (.var 0)) := by
  refine family_no_closed_inhabitant (base := base) (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts) (fun _ _ => rfl)
    (streamValues (V (.above 0)))
    (fun _ _ reads {_ _} declared => streamValues_typed reads chain omegaMem declared)
    (fun _ _ reads => streamEquations_valid reads) (fun z hz => ?_) t
  change z ∈ tracePiSet (V (.above 0)) (fun A => A) at hz
  exact ZFSet.notMem_empty _
    (traceApp_mem_fibre hz (chain.empty_mem groundTyped (.above 0)))

end Model

/-! ## The stages -/

section LowerSets

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

include small in
/-- The stream family has a set model on the stages that read the type of all sets as every set
of the lower universe. -/
theorem lowerSets_streamFamily_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts base (streamDecls L) (streamValues carrierCode.{u})) (streamFamily L) :=
  streamFamily_setModel (stages_closedChain small large) omega_mem_carrierCode groundTyped base

/-- The context `(A : set) (a : A) (b : A)`. -/
def twoPoint : CCtx (Head L) 3 :=
  .snoc (.snoc (.snoc .nil allSets) (.var 0)) (.var 1)

/-- The identity function on the set read by the environment. -/
def idOn : CTm (Head L) 3 := .lam (.var 2) (.var 0)

include small ν in
/-- The iterates of the identity at two distinct elements are streams the package cannot
identify. -/
theorem iter_seeds_distinct
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    ¬ CEqual (streamFamily L) twoPoint (cIter (.var 2) idOn (.var 1))
        (cIter (.var 2) idOn (.var 0)) (cStream (.var 2)) := by
  intro derived
  let heads := lowerSetsHeads (L := L) large ground ν
  let consts := familyConsts base (streamDecls L) (streamValues carrierCode.{u})
  have model := lowerSets_streamFamily_setModel small large ν groundTyped base
  let A : ZFSet.{u + 1} := ZFSet.omega
  let a0 : ZFSet.{u + 1} := numeral 0
  let a1 : ZFSet.{u + 1} := numeral 1
  let ρ : Env.{u + 1} 3 := extend (extend (extend Fin.elim0 A) a0) a1
  have setsEval : ev heads consts allSets Fin.elim0 = carrierCode.{u} := by
    simp only [heads]
    unfold allSets ev lowerSetsHeads chainHead LevelExpr.eval stages
    rfl
  have sat : Sat heads consts twoPoint ρ := by
    refine (sat_snoc heads consts).mpr ⟨(sat_snoc heads consts).mpr
      ⟨(sat_snoc heads consts).mpr ⟨sat_nil heads consts _, ?_⟩, ?_⟩, ?_⟩
    · rw [setsEval]
      exact omega_mem_carrierCode
    · exact numeral_mem_omega 0
    · exact numeral_mem_omega 1
  have reads : Reads (L := L) carrierCode.{u} consts :=
    fun _ declared => familyConsts_declared declared
  have same := CDerivable.sound_equality model derived ρ sat
  have ρ2 : ρ 2 = A := rfl
  have ρ1 : ρ 1 = a0 := rfl
  have ρ0 : ρ 0 = a1 := rfl
  have idFun : ev heads consts idOn ρ = traceLam (graph A (fun x => x)) := by
    unfold idOn
    simp only [ev, ρ2, extend_zero]
  have at0 : ev heads consts (cIter (.var 2) idOn (.var 1)) ρ =
      iterSet (traceLam (graph A (fun x => x))) a0 := by
    show traceApp (traceApp (traceApp (consts iterN) (ρ 2)) (ev heads consts idOn ρ)) (ρ 1) = _
    rw [ρ2, ρ1, reads.iter, idFun]
    exact iterValue_at carrierCode.{u} omega_mem_carrierCode
      (traceLam_graph_mem fun _ hx => hx) (numeral_mem_omega 0)
  have at1 : ev heads consts (cIter (.var 2) idOn (.var 0)) ρ =
      iterSet (traceLam (graph A (fun x => x))) a1 := by
    show traceApp (traceApp (traceApp (consts iterN) (ρ 2)) (ev heads consts idOn ρ)) (ρ 0) = _
    rw [ρ2, ρ0, reads.iter, idFun]
    exact iterValue_at carrierCode.{u} omega_mem_carrierCode
      (traceLam_graph_mem fun _ hx => hx) (numeral_mem_omega 1)
  rw [at0, at1] at same
  have heads0 := congrArg (fun s => traceApp s (numeral 0)) same
  rw [iterSet, iterSet] at heads0
  rw [traceApp_graph_beta _ (numeral_mem_omega 0)] at heads0
  rw [traceApp_graph_beta _ (numeral_mem_omega 0)] at heads0
  rw [natOf_numeral] at heads0
  unfold iterate at heads0
  exact Nat.zero_ne_one (numeral_injective heads0)

end LowerSets

/-! ## In the judgment -/

section Judgment

/-- A constant of the family is declared in the package as the family declares it. -/
theorem streamFamily_declared {c : DeclName} {T : CTm (Head L) 0}
    (declared : streamDecls L c = some T) : (streamFamily L).constantType c = some T :=
  (withFamily_declared (bare L) rfl).trans declared

/-- **A package over the stream family**: it contains the rules of the tower and declares the
five constants at their types. The typings of this section hold in every such package. -/
structure OverStreams {R' : Rules (Head L)} (Q : ChurchRules R') : Prop where
  contains : Contains R'
  declared : ∀ {c : DeclName} {T : CTm (Head L) 0}, streamDecls L c = some T →
    Q.constantType c = some T

/-- The package of the family is over the stream family. -/
theorem streamFamily_over : OverStreams (streamFamily L) :=
  ⟨package_contains, streamFamily_declared⟩

/-- A package that contains the package of the family is over the stream family. -/
theorem OverStreams.of_sub {R' : Rules (Head L)} {Q : ChurchRules R'}
    (sub : ChurchRulesSub (streamFamily L) Q) : OverStreams Q :=
  ⟨⟨sub.headTyping, sub.isUniverse, sub.join, sub.cumulative⟩,
    fun declared => sub.constantType (streamFamily_declared declared)⟩

/-- **A package computes as the stream family** when it contains the steps of the three
equations, with their premises. -/
abbrev ComputesAsStreams {R' : Rules (Head L)} (Q : ChurchRules R') : Prop :=
  StepsWithin (familyChurch (rules L) (streamDecls L) (streamEquations L)) Q

/-- The package of the family computes as the stream family. -/
theorem streamFamily_computes : ComputesAsStreams (streamFamily L) :=
  StepsWithin.sum_right (bare L) (familyChurch (rules L) (streamDecls L) (streamEquations L))

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}
  (covers : OverStreams Q)

include covers in
/-- The type of `Stream` is a type of `allClasses`. -/
theorem streamType_formed : CTyped Q Γ streamType allClasses :=
  setFunctions_typed covers.contains

include covers in
/-- `Stream` has its type. -/
theorem streamConst_typed : CTyped Q Γ (.const streamN) streamType :=
  definition_typed (covers.declared streamDecls_stream) (streamType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- For `A : set`, `Stream A : set`. -/
theorem cStream_typed {A : CTm (Head L) n} (hA : CTyped Q Γ A allSets) :
    CTyped Q Γ (cStream A) allSets :=
  .appElim (streamConst_typed covers) hA

include covers in
/-- The type of `scons` is a type of `allClasses`. -/
theorem sconsType_formed : CTyped Q Γ sconsType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.contains
      (CDerivable.var (P := Q) 0)
      (family_isSet (n := n + 2) (Γ := .snoc (.snoc Γ allSets) (.var 0))
        covers.contains
        (cStream_typed covers (n := n + 2) (Γ := .snoc (.snoc Γ allSets) (.var 0))
          (CDerivable.var (P := Q) 1))
        (cStream_typed covers (n := n + 3)
          (Γ := .snoc (.snoc (.snoc Γ allSets) (.var 0)) (cStream (.var 1)))
          (CDerivable.var (P := Q) 2))))

include covers in
/-- `scons` has its type. -/
theorem sconsConst_typed : CTyped Q Γ (.const sconsN) sconsType :=
  definition_typed (covers.declared streamDecls_scons) (sconsType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- `scons A a s` is a stream over `A`. -/
theorem cScons_typed {A a s : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (ha : CTyped Q Γ a A) (hs : CTyped Q Γ s (cStream A)) :
    CTyped Q Γ (cScons A a s) (cStream A) := by
  have first : CTyped Q Γ (.app (.const sconsN) A)
      (.pi A (.pi (cStream (A.rename wk))
        (cStream ((A.rename wk).rename wk)))) :=
    .appElim (B := .pi (.var 0) (.pi (cStream (.var 1)) (cStream (.var 2))))
      (sconsConst_typed covers) hA
  have second := CDerivable.appElim first ha
  have same : CTm.inst0 a (.pi (cStream (A.rename wk))
        (cStream ((A.rename wk).rename wk))) =
      .pi (cStream A) (cStream (A.rename wk)) := by
    show CTm.pi (cStream (CTm.inst0 a (CTm.rename wk A)))
        (cStream (CTm.subst (CTm.liftSub (CTm.subst0 a))
          (CTm.rename wk (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk a A, CTm.subst_liftSub_wk (CTm.subst0 a) (A.rename wk)]
    change (cStream A).pi (cStream (CTm.rename wk (CTm.inst0 a (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk a A]
  rw [same] at second
  have third := CDerivable.appElim (B := cStream (A.rename wk)) second hs
  have last : CTm.inst0 s (cStream (A.rename wk)) = cStream A := by
    show cStream (CTm.inst0 s (CTm.rename wk A)) = _
    rw [CTm.inst0_rename_wk s A]
  rw [last] at third
  exact third

include covers in
/-- The type of `shead` is a type of `allClasses`. -/
theorem sheadType_formed : CTyped Q Γ sheadType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.contains
      (cStream_typed covers (n := n + 1) (Γ := .snoc Γ allSets)
        (CDerivable.var (P := Q) 0))
      (CDerivable.var (P := Q) 1))

include covers in
/-- `shead` has its type. -/
theorem sheadConst_typed : CTyped Q Γ (.const sheadN) sheadType :=
  definition_typed (covers.declared streamDecls_shead) (sheadType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- `shead A`, before the stream, has type `Stream A → A`. -/
theorem cShead_fun {A : CTm (Head L) n} (hA : CTyped Q Γ A allSets) :
    CTyped Q Γ (.app (.const sheadN) A) (.pi (cStream A) (A.rename wk)) :=
  .appElim (B := .pi (cStream (.var 0)) (.var 1)) (sheadConst_typed covers) hA

include covers in
/-- `shead A s` is an element of `A`. -/
theorem cShead_typed {A s : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hs : CTyped Q Γ s (cStream A)) : CTyped Q Γ (cShead A s) A := by
  have raw := CDerivable.appElim (B := A.rename wk) (cShead_fun covers hA) hs
  rwa [CTm.inst0_rename_wk s A] at raw

include covers in
/-- The type of `stail` is a type of `allClasses`. -/
theorem stailType_formed : CTyped Q Γ stailType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.contains
      (cStream_typed covers (n := n + 1) (Γ := .snoc Γ allSets)
        (CDerivable.var (P := Q) 0))
      (cStream_typed covers (n := n + 2)
        (Γ := .snoc (.snoc Γ allSets) (cStream (.var 0)))
        (CDerivable.var (P := Q) 1)))

include covers in
/-- `stail` has its type. -/
theorem stailConst_typed : CTyped Q Γ (.const stailN) stailType :=
  definition_typed (covers.declared streamDecls_stail) (stailType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- `stail A`, before the stream, has type `Stream A → Stream A`. -/
theorem cStail_fun {A : CTm (Head L) n} (hA : CTyped Q Γ A allSets) :
    CTyped Q Γ (.app (.const stailN) A) (.pi (cStream A) (cStream (A.rename wk))) :=
  .appElim (B := .pi (cStream (.var 0)) (cStream (.var 1))) (stailConst_typed covers) hA

include covers in
/-- `stail A s` is a stream over `A`. -/
theorem cStail_typed {A s : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hs : CTyped Q Γ s (cStream A)) : CTyped Q Γ (cStail A s) (cStream A) := by
  have raw := CDerivable.appElim (B := cStream (A.rename wk)) (cStail_fun covers hA) hs
  have last : CTm.inst0 s (cStream (A.rename wk)) = cStream A := by
    show cStream (CTm.inst0 s (CTm.rename wk A)) = _
    rw [CTm.inst0_rename_wk s A]
  rwa [last] at raw

include covers in
/-- The type of `iter` is a type of `allClasses`. -/
theorem iterType_formed : CTyped Q Γ iterType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.contains
      (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.contains
        (CDerivable.var (P := Q) 0)
        (CDerivable.var (P := Q) 1))
      (family_isSet (n := n + 2)
        (Γ := .snoc (.snoc Γ allSets) (.pi (.var 0) (.var 1))) covers.contains
        (CDerivable.var (P := Q) 1)
        (cStream_typed covers (n := n + 3)
          (Γ := .snoc (.snoc (.snoc Γ allSets) (.pi (.var 0) (.var 1))) (.var 1))
          (CDerivable.var (P := Q) 2))))

include covers in
/-- `iter` has its type. -/
theorem iterConst_typed : CTyped Q Γ (.const iterN) iterType :=
  definition_typed (covers.declared streamDecls_iter) (iterType_formed covers)
    (covers.contains.isUniverse (.sort _))

omit [LevelOrder L] in
/-- Applying an endomorphism to an element stays in the set. -/
theorem endomorphism_applied {A f a : CTm (Head L) n}
    (hf : CTyped Q Γ f (.pi A (A.rename wk))) (ha : CTyped Q Γ a A) :
    CTyped Q Γ (.app f a) A := by
  have raw := CDerivable.appElim (B := A.rename wk) hf ha
  rwa [CTm.inst0_rename_wk a A] at raw

include covers in
/-- `iter A f a` is a stream over `A`. -/
theorem cIter_typed {A f a : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hf : CTyped Q Γ f (.pi A (A.rename wk))) (ha : CTyped Q Γ a A) :
    CTyped Q Γ (cIter A f a) (cStream A) := by
  have first : CTyped Q Γ (.app (.const iterN) A)
      (.pi (.pi A (A.rename wk))
        (.pi (A.rename wk) (cStream ((A.rename wk).rename wk)))) :=
    .appElim (B := .pi (.pi (.var 0) (.var 1)) (.pi (.var 1) (cStream (.var 2))))
      (iterConst_typed covers) hA
  have second := CDerivable.appElim first hf
  have same : CTm.inst0 f (.pi (A.rename wk) (cStream ((A.rename wk).rename wk))) =
      .pi A (cStream (A.rename wk)) := by
    show CTm.pi (CTm.inst0 f (CTm.rename wk A))
        (cStream (CTm.subst (CTm.liftSub (CTm.subst0 f))
          (CTm.rename wk (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk f A, CTm.subst_liftSub_wk (CTm.subst0 f) (A.rename wk)]
    change A.pi (cStream (CTm.rename wk (CTm.inst0 f (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk f A]
  rw [same] at second
  have third := CDerivable.appElim (B := cStream (A.rename wk)) second ha
  have last : CTm.inst0 a (cStream (A.rename wk)) = cStream A := by
    show cStream (CTm.inst0 a (CTm.rename wk A)) = _
    rw [CTm.inst0_rename_wk a A]
  rw [last] at third
  exact third

variable (computes : ComputesAsStreams Q)

include covers computes in
/-- **The first element of an element put in front is that element**, at every typed instance. -/
theorem shead_scons_rule {A a s : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (ha : CTyped Q Γ a A) (hs : CTyped Q Γ s (cStream A)) :
    CEqual Q Γ (cShead A (cScons A a s)) a A :=
  have typed : CSubstMor Q (sheadScons L).telescope Γ
      (fun j : Fin 3 => match j with
        | ⟨0, _⟩ => s
        | ⟨1, _⟩ => a
        | ⟨2, _⟩ => A) :=
    fun j => match j with
      | ⟨0, _⟩ => hs
      | ⟨1, _⟩ => ha
      | ⟨2, _⟩ => hA
  family_equation_holds (rules L) computes sheadScons_member _ typed
    (cShead_typed covers hA (cScons_typed covers hA ha hs)) ha

include covers computes in
/-- **The tail of an element put in front is the stream**, at every typed instance. -/
theorem stail_scons_rule {A a s : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (ha : CTyped Q Γ a A) (hs : CTyped Q Γ s (cStream A)) :
    CEqual Q Γ (cStail A (cScons A a s)) s (cStream A) :=
  have typed : CSubstMor Q (stailScons L).telescope Γ
      (fun j : Fin 3 => match j with
        | ⟨0, _⟩ => s
        | ⟨1, _⟩ => a
        | ⟨2, _⟩ => A) :=
    fun j => match j with
      | ⟨0, _⟩ => hs
      | ⟨1, _⟩ => ha
      | ⟨2, _⟩ => hA
  family_equation_holds (rules L) computes stailScons_member _ typed
    (cStail_typed covers hA (cScons_typed covers hA ha hs)) hs

include covers computes in
/-- **Iteration unfolds one step**, at every typed instance. -/
theorem iter_rule {A f a : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hf : CTyped Q Γ f (.pi A (A.rename wk))) (ha : CTyped Q Γ a A) :
    CEqual Q Γ (cIter A f a)
      (cScons A a (cIter A f (.app f a))) (cStream A) :=
  have typed : CSubstMor Q (iterEquation L).telescope Γ
      (fun j : Fin 3 => match j with
        | ⟨0, _⟩ => a
        | ⟨1, _⟩ => f
        | ⟨2, _⟩ => A) :=
    fun j => match j with
      | ⟨0, _⟩ => ha
      | ⟨1, _⟩ => hf
      | ⟨2, _⟩ => hA
  family_equation_holds (rules L) computes iterEquation_member _ typed
    (cIter_typed covers hA hf ha)
    (cScons_typed covers hA ha
      (cIter_typed covers hA hf (endomorphism_applied hf ha)))

include covers computes in
/-- In the judgment, the first element of the iterates is the starting value. -/
theorem shead_iter_equation {A f a : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hf : CTyped Q Γ f (.pi A (A.rename wk))) (ha : CTyped Q Γ a A) :
    CEqual Q Γ (cShead A (cIter A f a)) a A := by
  have unfolded := iter_rule covers computes hA hf ha
  have tail : CTyped Q Γ (cIter A f (.app f a)) (cStream A) :=
    cIter_typed covers hA hf (endomorphism_applied hf ha)
  have atCons : CEqual Q Γ (cShead A (cIter A f a))
      (cShead A (cScons A a (cIter A f (.app f a)))) A := by
    have cong := CDerivable.appCong (CDerivable.refl (cShead_fun covers hA)) unfolded
    rwa [CTm.inst0_rename_wk (cIter A f a) A] at cong
  exact atCons.trans (shead_scons_rule covers computes hA ha tail)

include covers computes in
/-- In the judgment, the element after the first of the iterates is the function at the
starting value. -/
theorem shead_stail_iter_equation {A f a : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hf : CTyped Q Γ f (.pi A (A.rename wk))) (ha : CTyped Q Γ a A) :
    CEqual Q Γ (cShead A (cStail A (cIter A f a))) (.app f a) A := by
  have next : CTyped Q Γ (.app f a) A := endomorphism_applied hf ha
  have unfolded := iter_rule covers computes hA hf ha
  have tail : CTyped Q Γ (cIter A f (.app f a)) (cStream A) :=
    cIter_typed covers hA hf next
  have stailCong : CEqual Q Γ (cStail A (cIter A f a))
      (cStail A (cScons A a (cIter A f (.app f a)))) (cStream A) := by
    have cong := CDerivable.appCong (CDerivable.refl (cStail_fun covers hA)) unfolded
    have same : CTm.inst0 (cIter A f a) (cStream (A.rename wk)) = cStream A := by
      show cStream (CTm.inst0 (cIter A f a) (CTm.rename wk A)) = _
      rw [CTm.inst0_rename_wk]
    rwa [same] at cong
  have sheadStail : CEqual Q Γ (cShead A (cStail A (cIter A f a)))
      (cShead A (cStail A (cScons A a (cIter A f (.app f a))))) A := by
    have cong := CDerivable.appCong (CDerivable.refl (cShead_fun covers hA)) stailCong
    rwa [CTm.inst0_rename_wk (cStail A (cIter A f a)) A] at cong
  have atTail : CEqual Q Γ (cStail A (cScons A a (cIter A f (.app f a))))
      (cIter A f (.app f a)) (cStream A) :=
    stail_scons_rule covers computes hA ha tail
  have sheadAtTail : CEqual Q Γ
      (cShead A (cStail A (cScons A a (cIter A f (.app f a)))))
      (cShead A (cIter A f (.app f a))) A := by
    have cong := CDerivable.appCong (CDerivable.refl (cShead_fun covers hA)) atTail
    rwa [CTm.inst0_rename_wk (cStail A (cScons A a (cIter A f (.app f a)))) A] at cong
  exact (sheadStail.trans sheadAtTail).trans (shead_iter_equation covers computes hA hf next)

end Judgment

/-! ## Reduction -/

section Reduction

variable {n : Nat}

/-- The erasure of `iter A f a`. -/
abbrev eIter (A f a : Tm (Head L) n) : Tm (Head L) n :=
  .app (.app (.app (.const iterN) A) f) a

/-- The erasure of `scons A a s`. -/
abbrev eScons (A a s : Tm (Head L) n) : Tm (Head L) n :=
  .app (.app (.app (.const sconsN) A) a) s

/-- The erasure of `shead A s`. -/
abbrev eShead (A s : Tm (Head L) n) : Tm (Head L) n :=
  .app (.app (.const sheadN) A) s

/-- The erasure of `stail A s`. -/
abbrev eStail (A s : Tm (Head L) n) : Tm (Head L) n :=
  .app (.app (.const stailN) A) s

/-- A substitution of three terms, last variable first. -/
def sub3 (x0 x1 x2 : Tm (Head L) n) : Sub (Head L) 3 n :=
  Fin.cases x0 (Fin.cases x1 (Fin.cases x2 Fin.elim0))

omit [LevelOrder L] in
/-- The first substituted term. -/
theorem sub3_zero (x0 x1 x2 : Tm (Head L) n) : sub3 x0 x1 x2 0 = x0 := rfl

omit [LevelOrder L] in
/-- The second substituted term. -/
theorem sub3_one (x0 x1 x2 : Tm (Head L) n) : sub3 x0 x1 x2 1 = x1 := rfl

omit [LevelOrder L] in
/-- The third substituted term. -/
theorem sub3_two (x0 x1 x2 : Tm (Head L) n) : sub3 x0 x1 x2 2 = x2 := rfl

/-- One use of the third equation, on erasures. -/
theorem iter_reduces (A f a : Tm (Head L) n) :
    StrongNormalization.Reduces (streamRules L) (eIter A f a)
      (eScons A a (eIter A f (.app f a))) := by
  refine Step.root ?_
  refine Or.inr ?_
  refine ⟨iterEquation L, iterEquation_member, sub3 a f A, ?_, ?_⟩
  · rfl
  · rfl

/-- The equation of `shead` on `scons`, on erasures. -/
theorem shead_scons_reduces (A a s : Tm (Head L) n) :
    StrongNormalization.Reduces (streamRules L) (eShead A (eScons A a s)) a := by
  refine Step.root ?_
  refine Or.inr ?_
  refine ⟨sheadScons L, sheadScons_member, sub3 s a A, ?_, ?_⟩
  · rfl
  · rfl

/-- The equation of `stail` on `scons`, on erasures. -/
theorem stail_scons_reduces (A a s : Tm (Head L) n) :
    StrongNormalization.Reduces (streamRules L) (eStail A (eScons A a s)) s := by
  refine Step.root ?_
  refine Or.inr ?_
  refine ⟨stailScons L, stailScons_member, sub3 s a A, ?_, ?_⟩
  · rfl
  · rfl

/-- Unfolding `iter` one step at a time: the starting value stays in front, and the call moves
one application of the function inward. -/
def iterUnfold (k : Nat) (A f a : Tm (Head L) n) : Tm (Head L) n :=
  match k with
  | 0 => eIter A f a
  | k + 1 => eScons A a (iterUnfold k A f (.app f a))

/-- Each unfold is one step of the package. -/
theorem iterUnfold_step (k : Nat) (A f a : Tm (Head L) n) :
    StrongNormalization.Reduces (streamRules L) (iterUnfold k A f a)
      (iterUnfold (k + 1) A f a) := by
  induction k generalizing a with
  | zero =>
      simpa [iterUnfold] using iter_reduces A f a
  | succ k ih =>
      simpa [iterUnfold] using Step.congAppArg (ih (.app f a))

omit [LevelOrder L] in
/-- A term that steps to the next term of an infinite sequence is not strongly normalizing. -/
theorem not_acc_of_steps {α : Sort _} {r : α → α → Prop} (seq : Nat → α)
    (step : ∀ k, r (seq k) (seq (k + 1))) (k : Nat)
    (acc : Acc (fun u t => r t u) (seq k)) : False :=
  Acc.rec (motive := fun t _ => ∀ k, t = seq k → False)
    (fun _ _ ih k eq => ih (seq (k + 1)) (eq.symm ▸ step k) (k + 1) rfl) acc k rfl

/-- The erasure of `iter A f a` is not strongly normalizing: every unfold produces another. -/
theorem iter_not_sn (A f a : CTm (Head L) n) :
    ¬ SN (streamRules L) (cIter A f a).erase := by
  intro sn
  have eq : (cIter A f a).erase = iterUnfold 0 A.erase f.erase a.erase := by
    simp [iterUnfold, eIter, CTm.erase]
  rw [eq] at sn
  exact not_acc_of_steps (iterUnfold · A.erase f.erase a.erase)
    (fun k => iterUnfold_step k A.erase f.erase a.erase) 0 sn

/-- **A term typed in a formed context of the stream package that is not strongly
normalizing**: `iter X (λ y. y) a`, over a set `X` and an element `a` of it. -/
theorem iter_typed_not_sn :
    ∃ (Θ : CCtx (Head L) 2) (t T : CTm (Head L) 2), CCtxFormed (streamFamily L) Θ ∧
      CTyped (streamFamily L) Θ t T ∧ ¬ SN (streamRules L) t.erase := by
  have c := (streamFamily_over (L := L)).contains
  have hA : CTyped (streamFamily L) (.snoc (.snoc .nil allSets) (.var 0)) (.var 1) allSets :=
    .var 1
  have hf : CTyped (streamFamily L) (.snoc (.snoc .nil allSets) (.var 0))
      (.lam (.var 1) (.var 0)) (.pi (.var 1) ((.var 1 : CTm (Head L) 2).rename wk)) :=
    .lamIntro hA (c.isUniverse (.sort _)) (family_isSet c hA (.var 2))
      (c.isUniverse (.sort _)) (.var 0)
  exact ⟨_, _, _,
    .snoc (.snoc .nil ⟨_, c.isUniverse (.sort _), sets_typed c⟩)
      ⟨_, c.isUniverse (.sort _), .var 0⟩,
    cIter_typed streamFamily_over hA hf (.var 0), iter_not_sn _ _ _⟩

/-- Run: the observation `shead A (iter A f a)` reaches the starting value `a` in two steps. -/
theorem shead_iter_runs (A f a : CTm (Head L) n) :
    ReducesStar (streamRules L) (cShead A (cIter A f a)).erase a.erase := by
  have start : (cShead A (cIter A f a)).erase =
      eShead A.erase (eIter A.erase f.erase a.erase) := by
    simp [eShead, eIter, CTm.erase]
  rw [start]
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail .refl
      (Step.congAppArg (iter_reduces A.erase f.erase a.erase)))
    (shead_scons_reduces A.erase a.erase (eIter A.erase f.erase (.app f.erase a.erase)))

/-- Run: the observation `shead A (stail A (iter A f a))` reaches `f a` in four steps. -/
theorem shead_stail_iter_runs (A f a : CTm (Head L) n) :
    ReducesStar (streamRules L) (cShead A (cStail A (cIter A f a))).erase
      (f.app a).erase := by
  have start : (cShead A (cStail A (cIter A f a))).erase =
      eShead A.erase (eStail A.erase (eIter A.erase f.erase a.erase)) := by
    simp [eShead, eStail, eIter, CTm.erase]
  rw [start]
  let A' := A.erase
  let f' := f.erase
  let a' := a.erase
  let once := eIter A' f' (.app f' a')
  let twice := eIter A' f' (.app f' (.app f' a'))
  have s1 : StrongNormalization.Reduces (streamRules L)
      (eShead A' (eStail A' (eIter A' f' a')))
      (eShead A' (eStail A' (eScons A' a' once))) :=
    Step.congAppArg (Step.congAppArg (iter_reduces A' f' a'))
  have s2 : StrongNormalization.Reduces (streamRules L)
      (eShead A' (eStail A' (eScons A' a' once)))
      (eShead A' once) :=
    Step.congAppArg (stail_scons_reduces A' a' once)
  have s3 : StrongNormalization.Reduces (streamRules L)
      (eShead A' once)
      (eShead A' (eScons A' (.app f' a') twice)) :=
    Step.congAppArg (iter_reduces A' f' (.app f' a'))
  have s4 : StrongNormalization.Reduces (streamRules L)
      (eShead A' (eScons A' (.app f' a') twice))
      (.app f' a') :=
    shead_scons_reduces A' (.app f' a') twice
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail .refl s1) s2) s3) s4

end Reduction

/-! ## The same equation at lists -/

section ListsLoop

variable (L) in
/-- The constant of iteration into a list. -/
def iterListN : DeclName := .str .anonymous "iterList"

section Terms

variable {n : Nat}

/-- `iterList A f a`. -/
abbrev cIterList (A f a : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const iterListN) A) f) a

/-- The type of `iterList`. -/
abbrev iterListType : CTm (Head L) n :=
  .pi allSets (.pi (.pi (.var 0) (.var 1)) (.pi (.var 1) (Lists.cList (.var 2))))

end Terms

variable (L) in
/-- The declaration of `iterList`. -/
def iterListDecls : DeclName → Option (CTm (Head L) 0) :=
  fun c => if c = iterListN then some iterListType else none

variable (L) in
/-- `iterList A f a ⟶ cons A a (iterList A f (f a))`. -/
def iterListUnfold : DefiningEquation (Head L) where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil allSets) (.pi (.var 0) (.var 1))) (.var 1)
  left := cIterList (.var 2) (.var 1) (.var 0)
  right := Lists.cCons (.var 2) (.var 0)
    (cIterList (.var 2) (.var 1) (.app (.var 1) (.var 0)))

variable (L) in
/-- The list family extended by the stream equation at lists. -/
abbrev iterListFamily :=
  withFamily (Lists.listFamily L) (iterListDecls L) [iterListUnfold L]

omit [LevelOrder L] in
/-- The list family does not declare `iterList`. -/
theorem iterList_not_listed : Lists.listDecls L iterListN = none := by
  simp [Lists.listDecls, Lists.listTable, tableLookup, iterListN, Lists.listN, Lists.nilN,
    Lists.consN, Lists.appendN]

/-- The list package does not declare `iterList`. -/
theorem listFamily_misses_iterList : (Lists.listFamily L).constantType iterListN = none := by
  show sumDecls (bare L).constantType (Lists.listDecls L) iterListN = none
  rw [sumDecls_right (by rfl : (bare L).constantType iterListN = none)]
  exact iterList_not_listed (L := L)

/-- The extended package declares `iterList` at its type. -/
theorem iterListFamily_iterList :
    (iterListFamily L).constantType iterListN = some iterListType := by
  show sumDecls (Lists.listFamily L).constantType (iterListDecls L) iterListN = some iterListType
  rw [sumDecls_right (listFamily_misses_iterList (L := L))]
  simp [iterListDecls, iterListN]

variable (large : CofinalInaccessibles.{u + 1}) {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

/-- No assignment that reads `List` as the set of lists and `cons` as an element before a list
is a set model of the list family extended by the stream equation: at `ω`, the identity, and
`0`, the equation puts a list in front of itself. -/
theorem iterList_no_setModel (consts : DeclName → ZFSet.{u + 1})
    (readsList : consts Lists.listN = Lists.listValue carrierCode.{u})
    (readsCons : consts Lists.consN = Lists.consValue carrierCode.{u}) :
    ¬ SetModel (lowerSetsHeads (L := L) large ground ν) consts (iterListFamily L) := by
  intro model
  let heads := lowerSetsHeads (L := L) large ground ν
  let A : ZFSet.{u + 1} := ZFSet.omega
  let a : ZFSet.{u + 1} := numeral 0
  let idFun : ZFSet.{u + 1} := traceLam (graph A (fun x => x))
  let e := iterListUnfold L
  let ρ : Env.{u + 1} 3 := extend (extend (extend Fin.elim0 A) idFun) a
  have setsEval : ev heads consts allSets Fin.elim0 = carrierCode.{u} := by
    simp only [heads]
    unfold allSets ev lowerSetsHeads chainHead LevelExpr.eval stages
    rfl
  have sat : Sat heads consts e.telescope ρ := by
    refine (sat_snoc heads consts).mpr ⟨(sat_snoc heads consts).mpr
      ⟨(sat_snoc heads consts).mpr ⟨sat_nil heads consts _, ?_⟩, ?_⟩, ?_⟩
    · rw [setsEval]
      exact omega_mem_carrierCode
    · exact traceLam_graph_mem fun _ hx => hx
    · exact numeral_mem_omega 0
  have step : (iterListFamily L).computation.step e.left e.right :=
    Or.inr ⟨e, List.mem_cons_self, CTm.ids, by simp [CTm.subst_ids], by simp [CTm.subst_ids]⟩
  have required : (iterListFamily L).computation.requires e.left e.right
      (telescopePremises e.telescope CTm.ids) :=
    Or.inr ⟨⟨e, List.mem_cons_self, CTm.ids, by simp [CTm.subst_ids], by simp [CTm.subst_ids]⟩,
      ⟨e, List.mem_cons_self, CTm.ids, by simp [CTm.subst_ids], by simp [CTm.subst_ids], rfl⟩⟩
  have holds : ∀ premise ∈ telescopePremises e.telescope CTm.ids,
      Holds heads consts (premise.statement e.telescope) := by
    intro premise among
    obtain ⟨i, rfl⟩ := mem_telescopePremises.mp among
    intro ρ' sat'
    simpa only [CTm.ids, CTm.subst_ids, ev] using sat' i
  have eqv := model.steps step required holds ρ sat
  have ρ2 : ρ 2 = A := rfl
  have ρ1 : ρ 1 = idFun := rfl
  have ρ0 : ρ 0 = a := rfl
  have happ : ev heads consts (.app (.var 1) (.var 0)) ρ = a := by
    show traceApp (ρ 1) (ρ 0) = a
    rw [ρ1, ρ0]
    unfold idFun
    rw [traceApp_graph_beta _ (numeral_mem_omega 0)]
  have left : ev heads consts e.left ρ =
      traceApp (traceApp (traceApp (consts iterListN) A) idFun) a := by
    unfold e iterListUnfold
    simp only [ev, ρ2, ρ1, ρ0]
  have declared := iterListFamily_iterList (L := L)
  have inType := model.constants declared
  have raw : consts iterListN ∈ tracePiSet carrierCode.{u} (fun B =>
      tracePiSet (tracePiSet B (fun _ => B)) (fun _ =>
        tracePiSet B (fun _ => traceApp (consts Lists.listN) B))) := by
    have typed : consts iterListN ∈
        tracePiSet (ev heads consts allSets Fin.elim0) (fun B =>
          ev heads consts (.pi (.pi (.var 0) (.var 1))
            (.pi (.var 1) (Lists.cList (.var 2)))) (extend Fin.elim0 B)) := by
      change _ at inType
      simpa [iterListType, ev] using inType
    rw [setsEval] at typed
    refine cast ?_ typed
    apply congrArg (fun fibre => consts iterListN ∈ tracePiSet carrierCode.{u} fibre)
    funext B
    simp only [ev, extend_zero]
    rfl
  have lMemPi : traceApp (traceApp (consts iterListN) A) idFun ∈
      tracePiSet A (fun _ => traceApp (consts Lists.listN) A) := by
    have first := traceApp_mem_fibre raw omega_mem_carrierCode
    have idMem : idFun ∈ tracePiSet A (fun _ => A) :=
      traceLam_graph_mem fun _ hx => hx
    simpa [idFun] using traceApp_mem_fibre first idMem
  have lMem : traceApp (traceApp (traceApp (consts iterListN) A) idFun) a ∈
      listSet Lists.nilTag Lists.consTag A := by
    have fibre := traceApp_mem_fibre lMemPi (numeral_mem_omega 0)
    rw [readsList] at fibre
    unfold Lists.listValue at fibre
    rwa [traceApp_graph_beta _ omega_mem_carrierCode] at fibre
  let l : ZFSet.{u + 1} := traceApp (traceApp (traceApp (consts iterListN) A) idFun) a
  have right : ev heads consts e.right ρ = consSet Lists.consTag a l := by
    show traceApp (traceApp (traceApp (consts Lists.consN) (ρ 2)) (ρ 0))
        (traceApp (traceApp (traceApp (consts iterListN) (ρ 2)) (ρ 1))
          (ev heads consts (.app (.var 1) (.var 0)) ρ)) = _
    rw [ρ2, ρ1, ρ0, happ, readsCons]
    unfold Lists.consValue
    rw [traceApp_graph_beta _ omega_mem_carrierCode, traceApp_graph_beta _ (numeral_mem_omega 0),
      traceApp_graph_beta _ lMem]
  rw [left, right] at eqv
  exact consSet_ne_self Lists.consTag a l eqv

end ListsLoop

end Streams
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
