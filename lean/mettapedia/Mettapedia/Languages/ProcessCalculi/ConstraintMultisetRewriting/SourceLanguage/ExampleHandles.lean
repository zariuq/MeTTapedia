import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Outcomes

/-!
# Alternatives share the handle counter: two bags without a race on a space

Two alternatives that each make a space take the supply's values in the order in which they move. The
well-formed query (over the empty program, with an injective supply)

```
(choice (new $a $a) (new $b 7))
```

touches no space: no alternative of any configuration it reaches reads or writes one, so no
configuration it reaches is a race on a space (`raceFree`). Moved left first, the left alternative's
handle is the supply's value at `0` and the bag is `{7, supply 0}`; moved right first, the right
alternative takes that value, the left one gets the supply's value at `1`, and the bag is
`{7, supply 1}` (`two_bags`).

So a query with no race on a space can have two bags of answers: the handle counter is shared as the
spaces are, and answers see the supply's values. A statement that programs without races have one bag
has to count `new` as a write of the counter, or compare bags up to a permutation of the supply's
values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHandles

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit SharedWorld

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

/-- The empty program. -/
def program : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

/-- An injective supply. -/
def supply : ℕ → MClosed := fun n => cnum n

def a : MData := mvar [3, 1] 0
def b : MData := mvar [3, 2] 0

/-- `(new $a $a)`: make a space and answer its handle. -/
def mkA : Comp mkeys [] () MTy := .new [3, 1] a (.ret a)

/-- `(new $b 7)`: make a space and answer `7`. -/
def mkB : Comp mkeys [] () MTy := .new [3, 2] b (.ret (num 7))

def query : Comp mkeys [] () MTy := .choice mkA mkB

theorem query_wellFormed : QueryWellFormed program [3] query := by decide

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) query

/-! ## No alternative touches a space -/

/-- Computations made of `ret`, `choice` and `new` only. -/
def Calm {Ty : Type} : Comp mkeys [] () Ty → Prop
  | .ret _ => True
  | .choice c d => Calm c ∧ Calm d
  | .new _ _ k => Calm k
  | _ => False

theorem calm_mapData {Ty : Type} (f : MData → MData) :
    ∀ c : Comp mkeys [] () Ty, Calm c → Calm (c.mapData f)
  | .ret _, _ => trivial
  | .choice c d, ⟨hc, hd⟩ => ⟨calm_mapData f c hc, calm_mapData f d hd⟩
  | .new _ _ k, hk => calm_mapData f k hk
  | .apply _, h => False.elim h
  | .run _, h => False.elim h
  | .let_ _ _ _ _, h => False.elim h
  | .fail, h => False.elim h
  | .query _ _ _, h => False.elim h
  | .add _ _ _, h => False.elim h
  | .remove _ _ _, h => False.elim h
  | .check _ _, h => False.elim h
  | .delay _ _ _ _, h => False.elim h
  | .force _, h => False.elim h

def CalmFocus {Ty : Type} : Focus mkeys [] () Ty → Prop
  | .eval c => Calm c
  | .value _ => True
  | .refused _ _ => True

/-- An alternative with no frame whose computation is made of `ret`, `choice` and `new` only. -/
def CalmBranch {Ty : Type} (br : Branch mkeys [] () Ty) : Prop := br.frames = [] ∧ CalmFocus br.focus

/-- **A move of a calm alternative makes calm alternatives**, under every program. -/
theorem calm_move {D' : Discipline MSig [] ()} {P' : Program mkeys [] () D'.Ty} {supply' : ℕ → MClosed}
    {w w' : World mkeys [] ()} {br : Branch mkeys [] () D'.Ty}
    {bs : Multiset (Branch mkeys [] () D'.Ty)} (moved : Move D' P' supply' w br w' bs)
    (calm : CalmBranch br) : ∀ br' ∈ bs, CalmBranch br' := by
  intro br' child
  cases moved with
  | ret K t fs ps =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨calm.1, trivial⟩
  | choice K c d fs ps =>
      rcases Multiset.mem_cons.mp child with rfl | other
      · exact ⟨calm.1, calm.2.1⟩
      · rw [Multiset.mem_singleton.mp other]
        exact ⟨calm.1, calm.2.2⟩
  | new K s x k fs ps =>
      rw [Multiset.mem_singleton.mp child]
      exact ⟨calm.1, calm_mapData _ k calm.2⟩
  | letBind => exact absurd calm.1 (List.cons_ne_nil _ _)
  | admitted => exact absurd calm.1 (List.cons_ne_nil _ _)
  | refused => exact absurd calm.1 (List.cons_ne_nil _ _)
  | memo => exact absurd calm.1 (List.cons_ne_nil _ _)
  | _ => exact False.elim calm.2

theorem calm_step {D' : Discipline MSig [] ()} {P' : Program mkeys [] () D'.Ty} {supply' : ℕ → MClosed}
    {C C' : Config mkeys [] () D'.Ty} (step : Step D' P' supply' C C')
    (all : ∀ br ∈ C.branches, CalmBranch br) : ∀ br ∈ C'.branches, CalmBranch br := by
  cases step with
  | move w w' br rest bs live moved =>
      intro br' member
      rcases Multiset.mem_add.mp member with made | kept
      · exact calm_move moved (all br (Multiset.mem_cons_self _ _)) br' made
      · exact all br' (Multiset.mem_cons_of_mem kept)

/-- **Every alternative of every configuration the query reaches is calm.** -/
theorem calm_runs {C : Config mkeys [] () D.Ty} (runs : Runs D program supply start C) :
    ∀ br ∈ C.branches, CalmBranch br := by
  induction runs with
  | refl =>
      intro br member
      rw [Multiset.mem_singleton.mp member]
      exact ⟨rfl, trivial, trivial⟩
  | tail _ step ih => exact calm_step step ih

/-- **No configuration the query reaches is a race on a space.** -/
theorem raceFree : RaceFree (D := D) program supply start := by
  intro C runs race
  obtain ⟨b₁, _, _, _, split, _, _, ⟨_, _, _, focus, _⟩, _⟩ := race
  have calm := (calm_runs runs b₁ (by rw [split]; exact Multiset.mem_cons_self _ _)).2
  rcases focus with focus | focus
  · rw [focus] at calm
    exact calm
  · rw [focus] at calm
    exact calm

/-! ## The two orders -/

def W (n h : ℕ) : World mkeys [] () := ⟨n, h, fun _ => 0⟩

/-- The store of the left alternative after its `new` at scope `n` with the handle counter at `h`. -/
def KA (n h : ℕ) : List (Constraint mkeys [] ()) :=
  [] ++ [(foD [n] [3, 1] 0, Rigid.includeTerm (fam mkeys) (supply h))]

/-- The store of the right alternative after its `new` at scope `n` with the handle counter at `h`. -/
def KB (n h : ℕ) : List (Constraint mkeys [] ()) :=
  [] ++ [(foD [n] [3, 2] 0, Rigid.includeTerm (fam mkeys) (supply h))]

/-- A store that binds one first-order name to a closed datum determines it. -/
theorem determined (n : ℕ) (site : List ℕ) (g : MClosed) :
    Determines ([] ++ [(foD [n] site 0, Rigid.includeTerm (fam mkeys) g)]) (foD [n] site 0) g := by
  refine ⟨⟨Empty, noNames, closeNames [] g, fun e member => ?_⟩, ?_⟩
  · simp only [List.nil_append, List.mem_singleton] at member
    subst member
    show instantiate _ (foD [n] site 0) = instantiate _ (Rigid.includeTerm (fam mkeys) g)
    rw [instantiate_foD, Rigid.instantiate_include]
    rfl
  · intro X target σ solved
    have e := solved (foD [n] site 0, Rigid.includeTerm (fam mkeys) g) (by simp)
    rw [Rigid.instantiate_include] at e
    exact e

theorem KA_live (n h : ℕ) : Solvable (KA n h) := (determined n [3, 1] (supply h)).1
theorem KB_live (n h : ℕ) : Solvable (KB n h) := (determined n [3, 2] (supply h)).1

def bA : Branch mkeys [] () MTy := ⟨[], .eval mkA, [], []⟩
def bB : Branch mkeys [] () MTy := ⟨[], .eval mkB, [], []⟩
def rA (n h : ℕ) : Branch mkeys [] () MTy := ⟨KA n h, .eval (.ret (foD [n] [3, 1] 0)), [], []⟩
def vA (n h : ℕ) : Branch mkeys [] () MTy := ⟨KA n h, .value (foD [n] [3, 1] 0), [], []⟩
def rB (n h : ℕ) : Branch mkeys [] () MTy := ⟨KB n h, .eval (.ret (num 7)), [], []⟩
def vB (n h : ℕ) : Branch mkeys [] () MTy := ⟨KB n h, .value (num 7), [], []⟩

/-- After the `choice`. -/
def C1 : Config mkeys [] () MTy := ⟨W 0 0, bA ::ₘ bB ::ₘ 0⟩

/-- The left alternative moved first: its handle is the supply's value at `0`. -/
def endAB : Config mkeys [] () MTy := ⟨W 2 2, vB 1 1 ::ₘ vA 0 0 ::ₘ 0⟩

/-- The right alternative moved first: the left one's handle is the supply's value at `1`. -/
def endBA : Config mkeys [] () MTy := ⟨W 2 2, vA 1 1 ::ₘ vB 0 0 ::ₘ 0⟩

theorem step_choice : Step D program supply start C1 :=
  Step.of_eq (D := D) (P := program) (supply := supply) (b := ⟨[], .eval query, [], []⟩) (rest := 0) rfl
    (by rfl) live_nil (.choice (W 0 0) [] _ _ [] [])

theorem runsAB : Runs D program supply C1 endAB := by
  refine Relation.ReflTransGen.tail (b := ⟨W 2 2, rB 1 1 ::ₘ vA 0 0 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := rB 1 1) rfl rfl (KB_live 1 1)
      (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W 2 2, rB 1 1 ::ₘ rA 0 0 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _) (b := rA 0 0)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) (KA_live 0 0) (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W 1 1, rA 0 0 ::ₘ bB ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add]; rfl) live_nil (.new _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) rfl
      (by rw [Multiset.singleton_add]; rfl) live_nil (.new _ _ _ _ _ _ _))

theorem runsBA : Runs D program supply C1 endBA := by
  refine Relation.ReflTransGen.tail (b := ⟨W 2 2, rA 1 1 ::ₘ vB 0 0 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := rA 1 1) rfl rfl (KA_live 1 1)
      (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W 2 2, rA 1 1 ::ₘ rB 0 0 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _) (b := rB 0 0)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) (KB_live 0 0) (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W 1 1, rB 0 0 ::ₘ bA ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add]; rfl) live_nil (.new _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add]; rfl) live_nil (.new _ _ _ _ _ _ _))

theorem endAB_quiescent : Config.Quiescent (D := D) program supply endAB :=
  Config.quiescent_of_finished fun br member _ => by
    have member' : br ∈ vB 1 1 ::ₘ vA 0 0 ::ₘ 0 := member
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member'
    rcases member' with rfl | rfl
    · exact ⟨rfl, _, rfl⟩
    · exact ⟨rfl, _, rfl⟩

theorem endBA_quiescent : Config.Quiescent (D := D) program supply endBA :=
  Config.quiescent_of_finished fun br member _ => by
    have member' : br ∈ vA 1 1 ::ₘ vB 0 0 ::ₘ 0 := member
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member'
    rcases member' with rfl | rfl
    · exact ⟨rfl, _, rfl⟩
    · exact ⟨rfl, _, rfl⟩

/-- The left alternative answers its handle: the supply's value at the counter it met. -/
theorem answer_A (n h : ℕ) : Branch.answer (D := D) (vA n h) = {supply h} :=
  answer_of_determines rfl (determined n [3, 1] (supply h))

theorem answer_B (n h : ℕ) : Branch.answer (D := D) (vB n h) = {cnum 7} :=
  answer_of_determines rfl ⟨KB_live n h, fun _ _ _ => rfl⟩

theorem answersAB : Config.answers (D := D) endAB = {{cnum 7}, {supply 0}} := by
  show Config.answers (D := D) (⟨W 2 2, vB 1 1 ::ₘ vA 0 0 ::ₘ 0⟩ : Config mkeys [] () MTy) = _
  rw [answers_cons_finished (D := D) (b := vB 1 1) ⟨rfl, _, rfl⟩ (KB_live 1 1),
    answers_cons_finished (D := D) (b := vA 0 0) ⟨rfl, _, rfl⟩ (KA_live 0 0), answers_zero, answer_A,
    answer_B]
  rfl

theorem answersBA : Config.answers (D := D) endBA = {{cnum 7}, {supply 1}} := by
  show Config.answers (D := D) (⟨W 2 2, vA 1 1 ::ₘ vB 0 0 ::ₘ 0⟩ : Config mkeys [] () MTy) = _
  rw [answers_cons_finished (D := D) (b := vA 1 1) ⟨rfl, _, rfl⟩ (KA_live 1 1),
    answers_cons_finished (D := D) (b := vB 0 0) ⟨rfl, _, rfl⟩ (KB_live 0 0), answers_zero, answer_A,
    answer_B]
  exact Multiset.cons_swap _ _ _

/-- The two bags differ: the supply is injective, and its value at `0` is not `7`. -/
theorem bags_differ :
    ({{cnum 7}, {supply 0}} : Multiset (Set MClosed)) ≠ {{cnum 7}, {supply 1}} := by
  intro same
  have member : ({supply 0} : Set MClosed) ∈ ({{cnum 7}, {supply 0}} : Multiset (Set MClosed)) :=
    Multiset.mem_cons.mpr (Or.inr (Multiset.mem_singleton_self _))
  rw [same] at member
  rcases Multiset.mem_cons.mp member with h | h
  · exact absurd (Set.singleton_eq_singleton_iff.mp h) (by decide)
  · exact absurd (Set.singleton_eq_singleton_iff.mp (Multiset.mem_singleton.mp h)) (by decide)

/-- **Two bags without a race on a space**: a well-formed query none of whose configurations is a race
on a space, with two runs that end, in two different bags of answers. -/
theorem two_bags :
    QueryWellFormed program [3] query ∧ RaceFree (D := D) program supply start ∧
      {{cnum 7}, {supply 0}} ∈ Outcomes D program supply start ∧
      {{cnum 7}, {supply 1}} ∈ Outcomes D program supply start ∧
      ({{cnum 7}, {supply 0}} : Multiset (Set MClosed)) ≠ {{cnum 7}, {supply 1}} :=
  ⟨query_wellFormed, raceFree,
    ⟨endAB, (Relation.ReflTransGen.single step_choice).trans runsAB, endAB_quiescent, answersAB⟩,
    ⟨endBA, (Relation.ReflTransGen.single step_choice).trans runsBA, endBA_quiescent, answersBA⟩,
    bags_differ⟩

#print axioms calm_runs
#print axioms raceFree
#print axioms runsAB
#print axioms runsBA
#print axioms two_bags

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHandles
