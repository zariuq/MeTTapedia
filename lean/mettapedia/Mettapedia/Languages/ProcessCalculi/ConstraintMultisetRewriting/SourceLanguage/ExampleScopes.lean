import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Outcomes

/-!
# Two alternatives that take fresh scopes commute only up to exchanging the scopes

Two alternatives, each about to bind a value to its own arrow, write no space and touch no name of the
other. Moved in the two orders, the first to move opens its arrow at scope `0` and the second at
scope `1`, so the two runs end in configurations that differ, by the exchange of the two scopes
(`orders_differ`), with the same bag of answers (`orders_answer_alike`). A confluence theorem for
programs without races has to identify configurations up to such exchanges: that every move is
equivariant under an exchange of scopes is the lemma it needs, and it is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleScopes

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

def program : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩
def supply : ℕ → MClosed := fun _ => csym "space"

def bx : Branch mkeys [] () MTy := ⟨[], .value (num 1), [.bindTo [3, 1] (mvar [3, 1] 0) (.ret (mvar [3, 1] 0))], []⟩
def bY : Branch mkeys [] () MTy := ⟨[], .value (num 2), [.bindTo [3, 2] (mvar [3, 2] 0) (.ret (mvar [3, 2] 0))], []⟩

/-- Two alternatives, each about to bind. -/
def X : Config mkeys [] () MTy := ⟨⟨0, 0, fun _ => 0⟩, bx ::ₘ bY ::ₘ 0⟩

/-- The alternative of `x` bound at scope `n`, finished. -/
def fx (n : ℕ) : Branch mkeys [] () MTy :=
  ⟨[] ++ [(foD [n] [3, 1] 0, num 1)], .value (foD [n] [3, 1] 0), [], []⟩
def fy (n : ℕ) : Branch mkeys [] () MTy :=
  ⟨[] ++ [(foD [n] [3, 2] 0, num 2)], .value (foD [n] [3, 2] 0), [], []⟩

theorem live_fx (n : ℕ) : Solvable (fx n).store :=
  ⟨Empty, noNames, closeNames [(([n], [3, 1], 0), cnum 1)] (csym "a"), fun e member => by
    simp only [fx, List.nil_append, List.mem_singleton] at member
    subst member
    show instantiate _ (foD [n] [3, 1] 0) = _
    rw [instantiate_foD]
    simp [closeNames]
    rfl⟩

theorem live_fy (n : ℕ) : Solvable (fy n).store :=
  ⟨Empty, noNames, closeNames [(([n], [3, 2], 0), cnum 2)] (csym "a"), fun e member => by
    simp only [fy, List.nil_append, List.mem_singleton] at member
    subst member
    show instantiate _ (foD [n] [3, 2] 0) = _
    rw [instantiate_foD]
    simp [closeNames]
    rfl⟩

/-- `x` first: `x` at scope `0`, `y` at scope `1`. -/
def C12 : Config mkeys [] () MTy := ⟨⟨2, 0, fun _ => 0⟩, fy 1 ::ₘ fx 0 ::ₘ 0⟩

/-- `y` first: `y` at scope `0`, `x` at scope `1`. -/
def C21 : Config mkeys [] () MTy := ⟨⟨2, 0, fun _ => 0⟩, fx 1 ::ₘ fy 0 ::ₘ 0⟩

theorem runs12 : Runs D program supply X C12 := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
      ⟨[] ++ [(foD [1] [3, 2] 0, num 2)], .eval (.ret (foD [1] [3, 2] 0)), [], []⟩ ::ₘ fx 0 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply)
      (b := ⟨[] ++ [(foD [1] [3, 2] 0, num 2)], .eval (.ret (foD [1] [3, 2] 0)), [], []⟩) rfl rfl (live_fy 1)
      (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
      ⟨[] ++ [(foD [1] [3, 2] 0, num 2)], .eval (.ret (foD [1] [3, 2] 0)), [], []⟩ ::ₘ
      ⟨[] ++ [(foD [0] [3, 1] 0, num 1)], .eval (.ret (foD [0] [3, 1] 0)), [], []⟩ ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (b := ⟨[] ++ [(foD [0] [3, 1] 0, num 1)], .eval (.ret (foD [0] [3, 1] 0)), [], []⟩)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) (live_fx 0) (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
      ⟨[] ++ [(foD [0] [3, 1] 0, num 1)], .eval (.ret (foD [0] [3, 1] 0)), [], []⟩ ::ₘ bY ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add]; rfl) live_nil (.letBind _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) rfl
      (by rw [Multiset.singleton_add]; rfl) live_nil (.letBind _ _ _ _ _ _ _ _))

theorem runs21 : Runs D program supply X C21 := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
      ⟨[] ++ [(foD [1] [3, 1] 0, num 1)], .eval (.ret (foD [1] [3, 1] 0)), [], []⟩ ::ₘ fy 0 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply)
      (b := ⟨[] ++ [(foD [1] [3, 1] 0, num 1)], .eval (.ret (foD [1] [3, 1] 0)), [], []⟩) rfl rfl (live_fx 1)
      (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
      ⟨[] ++ [(foD [1] [3, 1] 0, num 1)], .eval (.ret (foD [1] [3, 1] 0)), [], []⟩ ::ₘ
      ⟨[] ++ [(foD [0] [3, 2] 0, num 2)], .eval (.ret (foD [0] [3, 2] 0)), [], []⟩ ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (b := ⟨[] ++ [(foD [0] [3, 2] 0, num 2)], .eval (.ret (foD [0] [3, 2] 0)), [], []⟩)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) (live_fy 0) (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
      ⟨[] ++ [(foD [0] [3, 2] 0, num 2)], .eval (.ret (foD [0] [3, 2] 0)), [], []⟩ ::ₘ bx ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add]; rfl) live_nil (.letBind _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add]; rfl) live_nil (.letBind _ _ _ _ _ _ _ _))

/-- The name a finished alternative's store binds first, if any. -/
def boundName (b : Branch mkeys [] () MTy) : Option (Name mkeys) :=
  match b.store with
  | (.op (.inr (.mk x)) _, _) :: _ => some x
  | _ => none

/-- **The two orders reach different configurations**: the scopes of `x` and `y` are exchanged. -/
theorem orders_differ : C12 ≠ C21 := by
  intro same
  have names := congrArg (fun C : Config mkeys [] () MTy => C.branches.map boundName) same
  exact absurd names (by decide)

theorem fx_answer (n : ℕ) : Branch.answer (D := D) (fx n) = {cnum 1} := by
  refine answer_of_determines rfl ⟨live_fx n, fun target σ solved => ?_⟩
  have e := solved (foD [n] [3, 1] 0, num 1) (by simp [fx])
  exact e

theorem fy_answer (n : ℕ) : Branch.answer (D := D) (fy n) = {cnum 2} := by
  refine answer_of_determines rfl ⟨live_fy n, fun target σ solved => ?_⟩
  have e := solved (foD [n] [3, 2] 0, num 2) (by simp [fy])
  exact e

/-- **With the same bag of answers.** -/
theorem orders_answer_alike : Config.answers (D := D) C12 = Config.answers (D := D) C21 := by
  show Config.answers (D := D) (⟨⟨2, 0, fun _ => 0⟩, fy 1 ::ₘ fx 0 ::ₘ 0⟩ : Config mkeys [] () MTy) =
    Config.answers (D := D) (⟨⟨2, 0, fun _ => 0⟩, fx 1 ::ₘ fy 0 ::ₘ 0⟩ : Config mkeys [] () MTy)
  rw [answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ (live_fy 1), answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ (live_fx 0),
    answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ (live_fx 1), answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ (live_fy 0),
    answers_zero, fx_answer, fy_answer, fx_answer, fy_answer, Multiset.cons_swap]

/-- **Moves that leave the world as it is commute** (an instance of `SharedWorld.moves_commute`): the
two `ret`s of the alternatives after both binds, `x` then `y` or `y` then `x`. -/
theorem rets_commute :
    let rx : Branch mkeys [] () MTy := ⟨[] ++ [(foD [1] [3, 1] 0, num 1)], .eval (.ret (foD [1] [3, 1] 0)), [], []⟩
    let ry : Branch mkeys [] () MTy := ⟨[] ++ [(foD [0] [3, 2] 0, num 2)], .eval (.ret (foD [0] [3, 2] 0)), [], []⟩
    (Step D program supply ⟨⟨2, 0, fun _ => 0⟩, rx ::ₘ ry ::ₘ 0⟩ ⟨⟨2, 0, fun _ => 0⟩, {fx 1} + (ry ::ₘ 0)⟩ ∧
        Step D program supply ⟨⟨2, 0, fun _ => 0⟩, {fx 1} + (ry ::ₘ 0)⟩
          ⟨⟨2, 0, fun _ => 0⟩, {fx 1} + {fy 0} + 0⟩) ∧
      (Step D program supply ⟨⟨2, 0, fun _ => 0⟩, rx ::ₘ ry ::ₘ 0⟩ ⟨⟨2, 0, fun _ => 0⟩, {fy 0} + (rx ::ₘ 0)⟩ ∧
        Step D program supply ⟨⟨2, 0, fun _ => 0⟩, {fy 0} + (rx ::ₘ 0)⟩
          ⟨⟨2, 0, fun _ => 0⟩, {fx 1} + {fy 0} + 0⟩) :=
  SharedWorld.moves_commute (live_fx 1) (live_fy 0) (.ret _ _ _ _ _) (.ret _ _ _ _ _)

#print axioms runs12
#print axioms runs21
#print axioms rets_commute
#print axioms orders_differ
#print axioms orders_answer_alike

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleScopes
