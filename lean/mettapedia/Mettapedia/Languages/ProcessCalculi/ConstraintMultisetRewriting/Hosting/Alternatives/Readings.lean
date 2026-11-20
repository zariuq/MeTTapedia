import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls

/-!
# Two readings of a space shared by alternatives

The source language's spaces live in the world, and a step moves any live alternative. Two coherent
readings of what a row that one alternative adds means for the others:

* **The shared reading** (`SourceLanguage.Step`, as defined): one world for all alternatives; a row
  is visible to every alternative at once. The observation of a query is then a **set of bags**
  (`sharedObservations`), one per order in which alternatives move. `shared_race`: the query
  `(choice (add s a (ret 1)) (query s a (ret 2)))` over the empty program and an empty space has
  the two observations `{2, 1}` (the addition moves first) and `{1}` (the query moves first); so no
  single bag is its observation (`shared_not_one_bag`), and a host whose runs determine one bag
  cannot host this reading.
* **The separate reading** (`SepConfig`, `SepStep`): every alternative has its own world, the spaces
  as they were when it was made together with its own writes. `sep_commute`: **moves of two
  distinct alternatives commute**: both orders reach one configuration. `sep_race`: the same query
  ends with `{1}` whichever of the addition and the query moves first.

Neither reading is wired into the elaboration; the separate reading is stated here as a candidate.
Under the separate reading a write is never seen by a sibling. A merge of writes where alternatives
are collected would change no bag of answers here, since the source language has no collection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Readings

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

/-! ## The two readings, in general -/

section General

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
variable (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty) (supply : ℕ → Term S Γ star)

/-- **The observations of a query under the shared reading**: the bags of answers of the
configurations in which its runs end. -/
def sharedObservations (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty) :
    Set (Multiset (Set (Term S Γ star))) :=
  {A | ∃ C, Runs D P supply (Config.initial spaces q) C ∧ C.Quiescent (D := D) P supply ∧ C.answers (D := D) = A}

/-- **A configuration under the separate reading**: each alternative with its own world. -/
abbrev SepConfig (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) :=
  Multiset (World κ Γ star × Branch κ Γ star Ty)

/-- **A step under the separate reading**: a live alternative moves in its own world, and the
alternatives it makes inherit the world the move leaves. -/
inductive SepStep : SepConfig κ Γ star D.Ty → SepConfig κ Γ star D.Ty → Prop
  | move (w w' : World κ Γ star) (b : Branch κ Γ star D.Ty) (rest : SepConfig κ Γ star D.Ty)
      (bs : Multiset (Branch κ Γ star D.Ty)) (live : Solvable b.store) (moved : Move D P supply w b w' bs) :
      SepStep ((w, b) ::ₘ rest) (bs.map (fun b' => (w', b')) + rest)

/-- The start of a query under the separate reading. -/
def SepConfig.initial (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty) :
    SepConfig κ Γ star D.Ty :=
  {(⟨0, 0, spaces⟩, ⟨[], .eval q, [], []⟩)}

open Classical in
/-- The answers under the separate reading: the reading sets of the finished live alternatives. -/
noncomputable def SepConfig.answers (C : SepConfig κ Γ star D.Ty) : Multiset (Set (Term S Γ star)) :=
  (C.filter fun x => x.2.Finished (D := D) ∧ Solvable x.2.store).map fun x => x.2.answer (D := D)

/-- No live alternative can move in its own world. -/
def SepConfig.Quiescent (C : SepConfig κ Γ star D.Ty) : Prop :=
  ∀ x ∈ C, Solvable x.2.store → ∀ w' bs, ¬ Move D P supply x.1 x.2 w' bs

variable {D P supply}

theorem SepStep.of_eq {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {C C' rest : SepConfig κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (hC : C = (w, b) ::ₘ rest) (hC' : C' = bs.map (fun b' => (w', b')) + rest)
    (live : Solvable b.store) (moved : Move D P supply w b w' bs) : SepStep D P supply C C' := by
  subst hC hC'
  exact .move w w' b rest bs live moved

/-- **Under the separate reading, moves of two distinct alternatives commute**: whichever moves
first, the two moves reach one configuration. -/
theorem sep_commute {w w' v v' : World κ Γ star} {b c : Branch κ Γ star D.Ty}
    {bs cs : Multiset (Branch κ Γ star D.Ty)} (rest : SepConfig κ Γ star D.Ty)
    (liveB : Solvable b.store) (moveB : Move D P supply w b w' bs)
    (liveC : Solvable c.store) (moveC : Move D P supply v c v' cs) :
    Relation.ReflTransGen (SepStep D P supply) ((w, b) ::ₘ (v, c) ::ₘ rest)
        (bs.map (fun b' => (w', b')) + cs.map (fun c' => (v', c')) + rest) ∧
      Relation.ReflTransGen (SepStep D P supply) ((v, c) ::ₘ (w, b) ::ₘ rest)
        (bs.map (fun b' => (w', b')) + cs.map (fun c' => (v', c')) + rest) := by
  refine ⟨.tail (.single (.move w w' b _ bs liveB moveB)) ?_, .tail (.single (.move v v' c _ cs liveC moveC)) ?_⟩
  · exact SepStep.of_eq (Multiset.add_cons _ _ _) (by abel) liveC moveC
  · exact SepStep.of_eq (Multiset.add_cons _ _ _) (by abel) liveB moveB

end General

/-! ## The race -/

section Race

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls
  (D emptyP supply W0)

/-- The address of the space. -/
def h0 : MClosed := csym "s0"

def H : MData := Rigid.includeTerm (fam mkeys) h0

def a : MData := sym "a"

/-- **The race**: one alternative adds `a` to the space, the other queries the space for `a`. -/
def race : Comp mkeys [] () MTy := .choice (.add H a (.ret (num 1))) (.query H a (.ret (num 2)))

theorem H_determined : Determines ([] : List (Constraint mkeys [] ())) H h0 :=
  ⟨live_nil, fun _ σ _ => Rigid.instantiate_include σ h0⟩

def row : Row mkeys [] () := ⟨a, []⟩

/-- The space after the addition. -/
noncomputable def S1 : MClosed → Multiset (Row mkeys [] ()) :=
  setSpace (fun _ => 0) h0 ((fun _ : MClosed => (0 : Multiset (Row mkeys [] ()))) h0 + {row})

theorem S1_at : S1 h0 = {row} := by
  simp only [S1, setSpace_same, zero_add]

abbrev bAdd : Branch mkeys [] () MTy := ⟨[], .eval (.add H a (.ret (num 1))), [], []⟩
abbrev bQuery : Branch mkeys [] () MTy := ⟨[], .eval (.query H a (.ret (num 2))), [], []⟩
abbrev bRet1 : Branch mkeys [] () MTy := ⟨[], .eval (.ret (num 1)), [], []⟩
abbrev bOne : Branch mkeys [] () MTy := ⟨[], .value (num 1), [], []⟩

def K2 : List (Constraint mkeys [] ()) := [] ++ rowUse 0 row a
abbrev bRet2 : Branch mkeys [] () MTy := ⟨K2, .eval (.ret (num 2)), [], []⟩
abbrev bTwo : Branch mkeys [] () MTy := ⟨K2, .value (num 2), [], []⟩

theorem K2_live : Solvable K2 :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun e member => by
    simp only [K2, rowUse, copyStore, row, List.map_nil, List.nil_append, List.mem_singleton] at member
    subst member
    rfl⟩

theorem one_finished : Branch.Finished (D := D) bOne := ⟨rfl, _, rfl⟩
theorem two_finished : Branch.Finished (D := D) bTwo := ⟨rfl, _, rfl⟩

theorem one_answer : Branch.answer (D := D) bOne = {cnum 1} :=
  answer_of_determines rfl ⟨live_nil, fun _ _ _ => rfl⟩

theorem two_answer : Branch.answer (D := D) bTwo = {cnum 2} :=
  answer_of_determines rfl ⟨K2_live, fun _ _ _ => rfl⟩

/-- The world after the addition. -/
noncomputable abbrev Wadd : World mkeys [] () := ⟨0, 0, S1⟩

/-! ### The shared reading: two observations -/

theorem shared_choice :
    SourceLanguage.Step D emptyP supply (Config.initial (fun _ => 0) race) ⟨W0, bAdd ::ₘ bQuery ::ₘ 0⟩ :=
  Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := ⟨[], .eval race, [], []⟩) (rest := 0) rfl (by rfl)
    live_nil (.choice W0 [] _ _ [] [])

/-- The addition first: the query sees the row. -/
theorem shared_add_first :
    Runs D emptyP supply (Config.initial (fun _ => 0) race) ⟨⟨1, 0, S1⟩, bTwo ::ₘ bOne ::ₘ 0⟩ := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, S1⟩, bTwo ::ₘ bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := bRet1) (rest := bTwo ::ₘ 0) (bs := bOne ::ₘ 0)
      (Multiset.cons_swap _ _ _) (by rw [Multiset.cons_add, zero_add, Multiset.cons_swap]) live_nil (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, S1⟩, bRet2 ::ₘ bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := bRet2) (rest := bRet1 ::ₘ 0) (bs := bTwo ::ₘ 0) rfl
      (by rw [Multiset.cons_add, zero_add]) K2_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨Wadd, bQuery ::ₘ bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := bQuery) (rest := bRet1 ::ₘ 0) rfl
      (by
        show bRet2 ::ₘ bRet1 ::ₘ 0 = ((S1 h0).map fun r =>
          (⟨[] ++ rowUse 0 r a, .eval (.ret (num 2)), [], []⟩ : Branch mkeys [] () MTy)) + (bRet1 ::ₘ 0)
        rw [S1_at, Multiset.map_singleton, Multiset.singleton_add]
        rfl)
      live_nil (.query Wadd [] H a (.ret (num 2)) [] [] h0 H_determined))
  refine Relation.ReflTransGen.tail (b := ⟨W0, bAdd ::ₘ bQuery ::ₘ 0⟩) (.single shared_choice) ?_
  exact Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := bAdd) (rest := bQuery ::ₘ 0) (bs := bRet1 ::ₘ 0) rfl
    (by rw [Multiset.cons_add, zero_add, Multiset.cons_swap]) live_nil
    (.add W0 [] H a (.ret (num 1)) [] [] h0 H_determined)

/-- The query first: it sees an empty space. -/
theorem shared_query_first :
    Runs D emptyP supply (Config.initial (fun _ => 0) race) ⟨⟨1, 0, S1⟩, bOne ::ₘ 0⟩ := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, S1⟩, bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := bRet1) (rest := 0) (bs := bOne ::ₘ 0) rfl
      (by rw [add_zero]) live_nil (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, bAdd ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := bAdd) (rest := 0) (bs := bRet1 ::ₘ 0) rfl
      (by rw [add_zero]) live_nil (.add ⟨1, 0, fun _ => 0⟩ [] H a (.ret (num 1)) [] [] h0 H_determined))
  refine Relation.ReflTransGen.tail (b := ⟨W0, bAdd ::ₘ bQuery ::ₘ 0⟩) (.single shared_choice) ?_
  exact Step.of_eq (D := D) (P := emptyP) (supply := supply) (b := bQuery) (rest := bAdd ::ₘ 0) (Multiset.cons_swap _ _ _)
    (by
      show bAdd ::ₘ 0 = (((fun _ : MClosed => (0 : Multiset (Row mkeys [] ()))) h0).map fun r =>
        (⟨[] ++ rowUse 0 r a, .eval (.ret (num 2)), [], []⟩ : Branch mkeys [] () MTy)) + (bAdd ::ₘ 0)
      rw [Multiset.map_zero, zero_add])
    live_nil (.query W0 [] H a (.ret (num 2)) [] [] h0 H_determined)

theorem shared_add_first_ends :
    Config.Quiescent (D := D) emptyP supply (⟨⟨1, 0, S1⟩, bTwo ::ₘ bOne ::ₘ 0⟩ : Config mkeys [] () MTy) :=
  Config.quiescent_of_finished fun b member _ => by
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
    rcases member with rfl | rfl
    · exact two_finished
    · exact one_finished

theorem shared_query_first_ends :
    Config.Quiescent (D := D) emptyP supply (⟨⟨1, 0, S1⟩, bOne ::ₘ 0⟩ : Config mkeys [] () MTy) :=
  Config.quiescent_single

theorem shared_add_first_answers :
    Config.answers (D := D) (⟨⟨1, 0, S1⟩, bTwo ::ₘ bOne ::ₘ 0⟩ : Config mkeys [] () MTy) = {{cnum 2}, {cnum 1}} := by
  rw [answers_cons_finished two_finished K2_live, answers_cons_finished one_finished live_nil, answers_zero,
    one_answer, two_answer]
  rfl

theorem shared_query_first_answers :
    Config.answers (D := D) (⟨⟨1, 0, S1⟩, bOne ::ₘ 0⟩ : Config mkeys [] () MTy) = {{cnum 1}} := by
  rw [answers_cons_finished one_finished live_nil, answers_zero, one_answer]
  rfl

/-- **The shared reading observes two bags of the race.** -/
theorem shared_race :
    {{cnum 2}, {cnum 1}} ∈ sharedObservations D emptyP supply (fun _ => 0) race ∧
      {{cnum 1}} ∈ sharedObservations D emptyP supply (fun _ => 0) race ∧
      ({{cnum 2}, {cnum 1}} : Multiset (Set MClosed)) ≠ {{cnum 1}} := by
  refine ⟨⟨_, shared_add_first, shared_add_first_ends, shared_add_first_answers⟩,
    ⟨_, shared_query_first, shared_query_first_ends, shared_query_first_answers⟩, fun same => ?_⟩
  have := congrArg Multiset.card same
  simp at this

/-- **No single bag is the shared reading's observation of the race**: a host whose runs of one query
determine one bag cannot show every observation of the shared reading. -/
theorem shared_not_one_bag :
    ¬ ∃ B : Multiset (Set MClosed), ∀ A ∈ sharedObservations D emptyP supply (fun _ => 0) race, A = B := by
  rintro ⟨B, every⟩
  obtain ⟨two, one, different⟩ := shared_race
  exact different ((every _ two).trans (every _ one).symm)

/-! ### The separate reading: one configuration, whichever moves first -/

theorem sep_choice :
    SepStep D emptyP supply (SepConfig.initial D (fun _ => 0) race) {(W0, bAdd), (W0, bQuery)} :=
  SepStep.of_eq (rest := 0) rfl (by simp) live_nil (.choice W0 [] _ _ [] [])

/-- The addition, in the adding alternative's own world. -/
theorem sep_add_move : Move D emptyP supply W0 bAdd Wadd {bRet1} :=
  .add W0 [] H a (.ret (num 1)) [] [] h0 H_determined

/-- The query, in the querying alternative's own world: the space there is empty. -/
theorem sep_query_move : Move D emptyP supply W0 bQuery W0.fresh 0 :=
  .query W0 [] H a (.ret (num 2)) [] [] h0 H_determined

theorem sep_ret_move : Move D emptyP supply Wadd bRet1 Wadd {bOne} :=
  .ret Wadd [] (num 1) [] []

/-- Both orders of the addition and the query reach one configuration. -/
theorem sep_race_orders :
    Relation.ReflTransGen (SepStep D emptyP supply) {(W0, bAdd), (W0, bQuery)} {(Wadd, bRet1)} ∧
      Relation.ReflTransGen (SepStep D emptyP supply) {(W0, bQuery), (W0, bAdd)} {(Wadd, bRet1)} := by
  have both := sep_commute (D := D) (P := emptyP) (supply := supply) 0 live_nil sep_add_move live_nil sep_query_move
  simp only [Multiset.map_singleton, Multiset.map_zero, add_zero] at both
  exact both

theorem sep_end : SepConfig.Quiescent D emptyP supply {(Wadd, bOne)} := by
  intro x member _ w' bs moved
  rw [Multiset.mem_singleton] at member
  subst member
  exact Move.value_still moved

theorem sep_end_answers : SepConfig.answers D {(Wadd, bOne)} = {{cnum 1}} := by
  classical
  unfold SepConfig.answers
  rw [Multiset.filter_eq_self.mpr]
  · rw [Multiset.map_singleton]
    show {bOne.answer (D := D)} = _
    rw [one_answer]
  · intro x member
    rw [Multiset.mem_singleton] at member
    subst member
    exact ⟨one_finished, live_nil⟩

/-- **The separate reading of the race**: whichever of the addition and the query moves first, the
run ends in one configuration, whose bag of answers is `{1}`. -/
theorem sep_race :
    Relation.ReflTransGen (SepStep D emptyP supply) (SepConfig.initial D (fun _ => 0) race) {(Wadd, bOne)} ∧
      SepConfig.Quiescent D emptyP supply {(Wadd, bOne)} ∧ SepConfig.answers D {(Wadd, bOne)} = {{cnum 1}} ∧
      Relation.ReflTransGen (SepStep D emptyP supply) {(W0, bAdd), (W0, bQuery)} {(Wadd, bRet1)} ∧
      Relation.ReflTransGen (SepStep D emptyP supply) {(W0, bQuery), (W0, bAdd)} {(Wadd, bRet1)} := by
  have ret : SepStep D emptyP supply {(Wadd, bRet1)} {(Wadd, bOne)} :=
    SepStep.of_eq (rest := 0) rfl (by simp) live_nil sep_ret_move
  exact ⟨(Relation.ReflTransGen.single sep_choice).trans (sep_race_orders.1.tail ret), sep_end, sep_end_answers,
    sep_race_orders.1, sep_race_orders.2⟩

end Race

#print axioms sep_commute
#print axioms shared_race
#print axioms shared_not_one_bag
#print axioms sep_race_orders
#print axioms sep_race

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Readings
