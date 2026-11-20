import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# `new` makes a fresh space only when the supply is injective

`new` binds its handle to the supply's value at the handle counter. The query

```
(new $a (add-atom $a x)
  (new $b (match $b x found)))
```

makes two spaces, adds `x` to the first, and asks the second for `x`.

* **With an injective supply** (`fun n => n`) the second space is not the first: the query finds
  nothing and the bag is empty (`injective_fresh`).
* **The control, with a constant supply** (`fun _ => space`), both handles are the same address: the
  second `new` sees the row the first alternative added, and the bag is `{found}` (`constant_shared`).

* **In general** (`later_handles_differ`): no move lowers the handle counter and a `new` raises it, so
  with an injective supply the address a `new` binds differs from the supply's value at the counter
  of every world the run reaches afterwards, which is the address a later `new` would bind.

So with an injective supply a `new` gives a space no other `new` of the run has made; with a supply
that repeats a value it need not. The space is an empty one only if, further, nothing else addresses
the supply's values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleNew

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

def program : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

def a : MData := mvar [3, 1] 0
def b : MData := mvar [3, 2] 0
def x : MData := sym "x"

def inner : Comp mkeys [] () MTy := .new [3, 2] b (.query b x (.ret (sym "found")))
def query : Comp mkeys [] () MTy := .new [3, 1] a (.add a x inner)

theorem query_wellFormed : QueryWellFormed program [3] query := by decide

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) query

def a0 : MData := foD [0] [3, 1] 0
def b1 : MData := foD [1] [3, 2] 0

/-- The run for a supply `s`, up to the query of the second space. -/
def Ka (s : ℕ → MClosed) : List (Constraint mkeys [] ()) := [] ++ [(a0, Rigid.includeTerm (fam mkeys) (s 0))]
def Kb (s : ℕ → MClosed) : List (Constraint mkeys [] ()) := Ka s ++ [(b1, Rigid.includeTerm (fam mkeys) (s 1))]

/-- The spaces after the addition. -/
noncomputable def spA (s : ℕ → MClosed) : MClosed → Multiset (Row mkeys [] ()) :=
  setSpace (fun _ => 0) (s 0) ((fun _ : MClosed => (0 : Multiset (Row mkeys [] ()))) (s 0) + {⟨x, Ka s⟩})

theorem a0_determined (s : ℕ → MClosed) : Determines (Ka s) a0 (s 0) := by
  refine ⟨⟨Empty, noNames, closeNames [(([0], [3, 1], 0), s 0)] (csym "a"), fun e member => ?_⟩, ?_⟩
  · simp only [Ka, List.nil_append, List.mem_singleton] at member
    subst member
    show instantiate _ (foD [0] [3, 1] 0) = instantiate _ (Rigid.includeTerm (fam mkeys) (s 0))
    rw [instantiate_foD, Rigid.instantiate_include]
    rfl
  · intro X target σ solved
    have e := solved (a0, Rigid.includeTerm (fam mkeys) (s 0)) (by simp [Ka])
    rw [Rigid.instantiate_include] at e
    exact e

theorem Kb_live (s : ℕ → MClosed) : Solvable (Kb s) :=
  ⟨Empty, noNames, closeNames [(([0], [3, 1], 0), s 0), (([1], [3, 2], 0), s 1)] (csym "a"), fun e member => by
    simp only [Kb, Ka, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · show instantiate _ (foD [0] [3, 1] 0) = instantiate _ (Rigid.includeTerm (fam mkeys) (s 0))
      rw [instantiate_foD, Rigid.instantiate_include]
      rfl
    · show instantiate _ (foD [1] [3, 2] 0) = instantiate _ (Rigid.includeTerm (fam mkeys) (s 1))
      rw [instantiate_foD, Rigid.instantiate_include]
      rfl⟩

theorem Ka_live (s : ℕ → MClosed) : Solvable (Ka s) := solvable_of_append (Kb_live s)

theorem b1_determined (s : ℕ → MClosed) : Determines (Kb s) b1 (s 1) := by
  refine ⟨Kb_live s, fun target σ solved => ?_⟩
  have e := solved (b1, Rigid.includeTerm (fam mkeys) (s 1)) (by simp [Kb])
  rw [Rigid.instantiate_include] at e
  exact e

/-- The configuration about to query the second space. -/
noncomputable def atQuery (s : ℕ → MClosed) : Config mkeys [] () MTy :=
  ⟨⟨2, 2, spA s⟩, {⟨Kb s, .eval (.query b1 x (.ret (sym "found"))), [], []⟩}⟩

theorem runs_atQuery (s : ℕ → MClosed) : Runs D program s start (atQuery s) := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 1, spA s⟩, {⟨Ka s, .eval inner, [], []⟩}⟩) ?_
    (step_one (Ka_live s) (.new _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 1, fun _ => 0⟩, {⟨Ka s, .eval (.add a0 x inner), [], []⟩}⟩) ?_
    (step_one (Ka_live s) (.add _ _ _ _ _ _ _ (s 0) (a0_determined s)))
  exact Relation.ReflTransGen.single (step_one live_nil (.new _ _ _ _ _ _ _))

/-! ## An injective supply: the second space is empty -/

def injective : ℕ → MClosed := fun n => cnum n

theorem injective_injective : Function.Injective injective := by
  intro m n same
  have := congrArg (fun g : MClosed => (match g with | .op (.num k) _ => k | _ => (0 : Int))) same
  simpa [injective, cnum] using this

noncomputable def emptyEnd : Config mkeys [] () MTy := ⟨⟨3, 2, spA injective⟩, 0⟩

theorem injective_fresh :
    Function.Injective injective ∧ Runs D program injective start emptyEnd ∧
      Config.Quiescent (D := D) program injective emptyEnd ∧ Config.answers (D := D) emptyEnd = 0 := by
  refine ⟨injective_injective, (runs_atQuery injective).tail ?_,
    fun _ member => absurd member (Multiset.notMem_zero _), answers_zero⟩
  have none : spA injective (injective 1) = 0 := by
    simp only [spA]
    rw [setSpace_other _ _ (by decide)]
  refine Step.of_eq (D := D) (P := program) (supply := injective) (rest := 0) rfl ?_ (Kb_live injective)
    (.query _ _ _ _ _ _ _ (injective 1) (b1_determined injective))
  show (0 : Multiset (Branch mkeys [] () MTy)) = (spA injective (injective 1)).map _ + 0
  rw [none, Multiset.map_zero, add_zero]

/-! ## The control: a constant supply makes one space twice -/

def constant : ℕ → MClosed := fun _ => csym "space"

theorem constant_not_injective : ¬ Function.Injective constant := by
  intro injective'
  exact absurd (injective' (show constant 0 = constant 1 from rfl)) (by decide)

def KF : List (Constraint mkeys [] ()) := Kb constant ++ rowUse 2 ⟨x, Ka constant⟩ x

theorem KF_live : Solvable KF :=
  ⟨Empty, noNames, closeNames [(([0], [3, 1], 0), csym "space"), (([1], [3, 2], 0), csym "space"),
      (([2, 0], [3, 1], 0), csym "space")] (csym "a"), by
    intro e member
    simp only [KF, Kb, Ka, rowUse, copyStore, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · show instantiate _ (foD [0] [3, 1] 0) = instantiate _ (Rigid.includeTerm (fam mkeys) (csym "space"))
      rw [instantiate_foD, Rigid.instantiate_include]
      rfl
    · show instantiate _ (foD [1] [3, 2] 0) = instantiate _ (Rigid.includeTerm (fam mkeys) (csym "space"))
      rw [instantiate_foD, Rigid.instantiate_include]
      rfl
    · show instantiate _ (instantiate (copyAt mkeys 2) (foD [0] [3, 1] 0)) =
        instantiate _ (instantiate (copyAt mkeys 2) (Rigid.includeTerm (fam mkeys) (csym "space")))
      rw [instantiate_foD, Rigid.instantiate_include, Rigid.instantiate_include]
      show instantiate _ (generator (fam mkeys) (fo [2, 0] [3, 1] 0)) = _
      rw [instantiate_generator]
      rfl
    · rfl⟩

noncomputable def sharedEnd : Config mkeys [] () MTy :=
  ⟨⟨3, 2, spA constant⟩, {⟨KF, .value (sym "found"), [], []⟩}⟩

theorem constant_shared :
    ¬ Function.Injective constant ∧ Runs D program constant start sharedEnd ∧
      Config.Quiescent (D := D) program constant sharedEnd ∧
      Config.answers (D := D) sharedEnd = {{csym "found"}} := by
  refine ⟨constant_not_injective, ?_, Config.quiescent_single, ?_⟩
  · refine ((runs_atQuery constant).tail ?_).tail (step_one KF_live (.ret _ _ _ _ _))
    have rows : spA constant (constant 1) = {⟨x, Ka constant⟩} := by
      simp only [spA, constant, setSpace_same, zero_add]
    refine Step.of_eq (D := D) (P := program) (supply := constant) (rest := 0) rfl ?_ (Kb_live constant)
      (.query _ _ _ _ _ _ _ (constant 1) (b1_determined constant))
    show ({⟨KF, .eval (.ret (sym "found")), [], []⟩} : Multiset (Branch mkeys [] () MTy)) =
      (spA constant (constant 1)).map _ + 0
    rw [rows, Multiset.map_singleton, add_zero]
    rfl
  · show Config.answers (D := D)
      (⟨⟨3, 2, spA constant⟩, {⟨KF, .value (sym "found"), [], []⟩}⟩ : Config mkeys [] () MTy) = _
    rw [answers_singleton (D := D) ⟨rfl, _, rfl⟩ KF_live,
      answer_of_determines (g := csym "found") rfl ⟨KF_live, fun _ _ _ => rfl⟩]

/-! ## The general statement: later handles differ under an injective supply -/

/-- A move never lowers the handle counter. -/
theorem move_handles_le {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {D' : Discipline S Γ star}
    {P' : Program κ Γ star D'.Ty} {supply' : ℕ → Term S Γ star} {w w' : World κ Γ star}
    {br : Branch κ Γ star D'.Ty} {bs : Multiset (Branch κ Γ star D'.Ty)}
    (moved : Move D' P' supply' w br w' bs) : w.handles ≤ w'.handles := by
  cases moved <;> simp [World.fresh]

/-- A run never lowers the handle counter. -/
theorem runs_handles_le {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {D' : Discipline S Γ star}
    {P' : Program κ Γ star D'.Ty} {supply' : ℕ → Term S Γ star} {C C' : Config κ Γ star D'.Ty}
    (runs : Runs D' P' supply' C C') : C.world.handles ≤ C'.world.handles := by
  induction runs with
  | refl => exact le_rfl
  | tail _ step ih =>
      cases step with
      | move w w' br rest bs live moved => exact ih.trans (move_handles_le moved)

/-- **With an injective supply, a `new` gets an address that no later `new` of the run gets**: a `new`
at the world `w` binds its handle to the supply's value at `w.handles` and leaves the counter at
`w.handles + 1`; at every world a run reaches from there, the supply's value at the counter, which
is what a `new` there would bind, is a different address. -/
theorem later_handles_differ {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    {D' : Discipline S Γ star} {P' : Program κ Γ star D'.Ty} {supply' : ℕ → Term S Γ star}
    (inj : Function.Injective supply') (w : World κ Γ star) {w₂ : World κ Γ star}
    {B B' : Multiset (Branch κ Γ star D'.Ty)}
    (later : Runs D' P' supply' ⟨⟨w.scope + 1, w.handles + 1, w.spaces⟩, B⟩ ⟨w₂, B'⟩) :
    supply' w.handles ≠ supply' w₂.handles := by
  intro same
  have le : w.handles + 1 ≤ w₂.handles := runs_handles_le later
  have eq : w.handles = w₂.handles := inj same
  omega

/-- The instance on the run above: after the first `new` and the addition, the counter is at `1`, and
the address the second `new` binds there is not the first one's. -/
theorem second_handle_differs : injective 0 ≠ injective 1 :=
  later_handles_differ (D' := D) (P' := program) injective_injective ⟨0, 0, fun _ => 0⟩
    (Relation.ReflTransGen.single
      (step_one (Ka_live injective)
        (.add ⟨1, 1, fun _ => 0⟩ (Ka injective) a0 x inner [] [] (injective 0) (a0_determined injective))))

#print axioms injective_fresh
#print axioms constant_shared
#print axioms later_handles_differ
#print axioms second_handle_differs

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleNew
