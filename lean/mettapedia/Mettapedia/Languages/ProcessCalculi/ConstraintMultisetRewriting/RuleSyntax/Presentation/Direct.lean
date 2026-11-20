import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Possibility

/-!
# The generated possibility is the firing possibility of `RuleSyntax.step` itself

`Possibility.generated_possibility_keeping` reaches `RuleSyntax.step` through the one-frame instance, for its
label-keeping firings at embedded states. Here the comparison is made directly, for every admitted firing of
`RuleSyntax.step` at the one frame over ground rows (`groundStep`), at every state with trivial knowledge, when
there are infinitely many occurrence identities (`generated_possibility_direct`; in OSLF's form as derived
diamonds of the step's firing span, `pulled_back_diamond_direct`).

The bag of a state is the labels of its present rows (`stateBag`). An admitted firing takes its rule's consumed
rows out of the bag and puts its yielded rows in (`bag_of_admitted`): its made identities are relabelled by the
made rows, and every other present identity keeps its label. Conversely every way of finding a rule's consumed
rows in the bag is an admitted firing (`admitted_of_bag`), with fresh made identities (`exists_fresh`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.TypeSynthesis (langDiamondUsing langGSLTUsing)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationPredicate)
open Mettapedia.OSLF.Framework.DerivedModalities (derivedDiamond pb)
open Interface (Frames)
open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground)
open LogicOverTheStep.StepSpan (firingSpan)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (frames ext)

universe uO

/-- **The step of a program over ground rows**, at the one frame: `RuleSyntax.step` itself. -/
abbrev groundStep (O : Type uO) [DecidableEq O] (rules : List (Rule Rows)) :=
  step (frames ground) O (ext ground) {r | r ∈ rules}

variable {O : Type uO} [DecidableEq O] {rules : List (Rule Rows)}

/-- **The bag of a state**: the labels of its present rows. -/
def stateBag (s : State Rows O) : Multiset Expr := s.present.val.map s.label

omit [DecidableEq O] in
theorem coe_stateRows (s : State Rows O) :
    ((s.present.toList.map s.label : List Expr) : Multiset Expr) = stateBag s := by
  rw [← Multiset.map_coe, Finset.coe_toList]
  rfl

theorem map_eq_of_zip {α β : Type*} (f : α → β) : ∀ (as : List α) (bs : List β), as.length = bs.length →
    (∀ x ∈ as.zip bs, f x.1 = x.2) → as.map f = bs
  | [], [], _, _ => rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | a :: as, b :: bs, lengths, each => by
      rw [List.map_cons, each (a, b) List.mem_cons_self,
        map_eq_of_zip f as bs (Nat.succ.inj lengths) fun x member => each x (List.mem_cons_of_mem _ member)]

/-- **Fresh distinct identities of every number**, when there are infinitely many. -/
theorem exists_fresh [Infinite O] : ∀ (used : Finset O) (n : ℕ),
    ∃ l : List O, l.Nodup ∧ l.length = n ∧ ∀ o ∈ l, o ∉ used
  | _, 0 => ⟨[], List.nodup_nil, rfl, fun _ member => absurd member List.not_mem_nil⟩
  | used, n + 1 => by
      obtain ⟨o, fresh⟩ := Infinite.exists_notMem_finset used
      obtain ⟨l, nodup, length, outside⟩ := exists_fresh (insert o used) n
      refine ⟨o :: l, List.nodup_cons.mpr ⟨fun member => outside o member (Finset.mem_insert_self o used), nodup⟩,
        by rw [List.length_cons, length], ?_⟩
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact fresh
      · exact fun inUsed => outside p member (Finset.mem_insert_of_mem inUsed)

section Firing

variable {s : State Rows O} (g : Firing O (ext ground) {r | r ∈ rules} s.frame)

omit [DecidableEq O] in
theorem opened_ground : g.opened (frames ground) = g.rule.body :=
  OneFrame.map_fixed g.rule _ fun _ _ => rfl

omit [DecidableEq O] in
/-- **The information of a firing over ground rows**: the knowledge, the take and read equations, the tells. -/
theorem information_ground : g.information (frames ground) s =
    s.knowledge ++ Selection.equations s.label g.rule.body.take g.selection.taken ++
      Selection.equations s.label g.rule.body.read g.selection.read ++ g.rule.body.tell := by
  have known : (frames ground).applyStore ((ext ground).weaken g.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := frames ground) s.knowledge
  unfold Firing.information Firing.matching
  rw [known, opened_ground]
  rfl

omit [DecidableEq O] in
theorem map_of_trivial {patterns : List Expr} {selected : List O} (lengths : patterns.length = selected.length)
    (trivial : Trivial (Selection.equations s.label patterns selected)) : selected.map s.label = patterns :=
  map_eq_of_forall₂ s.label ((Selection.models_equations_iff ground () s.label lengths).mp trivial)

/-- The bag of the result: what was not taken, and the made rows. -/
theorem stateBag_result (admitted : (groundStep O rules).Admits (s := s) g) :
    stateBag ((groundStep O rules).result g admitted) =
      (s.present \ g.selection.taken.toFinset).val.map s.label + (g.rule.body.produce : Multiset Expr) := by
  obtain ⟨_, ⟨_, madeNodup, _, _, produceLength, _⟩, enabled, _⟩ := (admits_iff g).mp admitted
  have apart : Disjoint (s.present \ g.selection.taken.toFinset) g.selection.made.toFinset :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset enabled.fresh.symm
  show (fire s.present (g.selection.commit (T := Unit))).val.map (g.result (frames ground) s).label = _
  unfold fire
  show ((s.present \ g.selection.taken.toFinset) ∪ g.selection.made.toFinset).val.map
    (g.result (frames ground) s).label = _
  rw [val_union_of_disjoint apart, Multiset.map_add, toFinset_val_of_nodup madeNodup, Multiset.map_coe]
  congr 1
  · refine Multiset.map_congr rfl fun o member => ?_
    have notMade : o ∉ g.selection.made := fun made =>
      Finset.disjoint_left.mp apart (Finset.mem_val.mp member) (List.mem_toFinset.mpr made)
    exact g.result_label_other notMade
  · have lengths : g.selection.made.length = (g.opened (frames ground)).produce.length := by
      rw [opened_ground]
      exact produceLength.symm
    have mapped := map_eq_of_zip _ g.selection.made (g.opened (frames ground)).produce lengths
      (Firing.relabel_zip (g.row (frames ground) s) g.selection.made (g.opened (frames ground)).produce madeNodup
        lengths)
    show ((g.selection.made.map (relabel (g.row (frames ground) s) g.selection.made
      (g.opened (frames ground)).produce) : List Expr) : Multiset Expr) = _
    rw [mapped, opened_ground]

/-- **An admitted firing takes its rule's consumed rows out of the bag and puts its yielded rows in**, its guards
hold, and the result's knowledge stays trivial. -/
theorem bag_of_admitted (admitted : (groundStep O rules).Admits (s := s) g) :
    g.rule ∈ rules ∧ guardsHold g.rule = true ∧ ∃ rest : Multiset Expr,
      ((consumes g.rule : List Expr) : Multiset Expr) + rest = stateBag s ∧
      stateBag ((groundStep O rules).result g admitted) = ((yields g.rule : List Expr) : Multiset Expr) + rest ∧
      Trivial ((groundStep O rules).result g admitted).knowledge := by
  obtain ⟨_, ⟨takenNodup, _, takeLength, readLength, _, _⟩, enabled, solvable, checks, _⟩ :=
    (admits_iff g).mp admitted
  have trivialInfo : Trivial (g.information (frames ground) s) :=
    (consistent_iff_trivial _).mp ((Frames.ofSubstitution_solvable_iff ground _).mp solvable)
  have split := trivialInfo
  rw [information_ground] at split
  have takes : Trivial (Selection.equations s.label g.rule.body.take g.selection.taken) :=
    fun e member => split e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))
  have reads : Trivial (Selection.equations s.label g.rule.body.read g.selection.read) :=
    fun e member => split e (List.mem_append_left _ (List.mem_append_right _ member))
  have tells : Trivial g.rule.body.tell := fun e member => split e (List.mem_append_right _ member)
  have takenLabels := map_of_trivial takeLength takes
  have readLabels := map_of_trivial readLength reads
  refine ⟨g.member, ?_, ?_⟩
  · simp only [guardsHold, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨tells, fun c member => ?_⟩
    cases c with
    | equal left right =>
        have holds := checks (.equal left right) (by rw [opened_ground]; exact member) PUnit.unit () trivialInfo
        simp only [groundCheck, decide_eq_true_eq]
        exact holds
    | predicate quantifier _ => rfl
    | count _ _ => rfl
  · have readInD : ∀ x ∈ g.rule.body.read, x ∈ (s.present \ g.selection.taken.toFinset).val.map s.label := by
      intro x member
      rw [← readLabels] at member
      obtain ⟨o, inRead, rfl⟩ := List.mem_map.mp member
      have readO : o ∈ (g.selection.commit (T := Unit)).kept := List.mem_toFinset.mpr inRead
      have present : o ∈ s.present := enabled.kept_subset readO
      have notTaken : o ∉ g.selection.taken.toFinset := fun taken =>
        Finset.disjoint_left.mp enabled.apart taken readO
      exact Multiset.mem_map_of_mem s.label (Finset.mem_val.mpr (Finset.mem_sdiff.mpr ⟨present, notTaken⟩))
    have dedupLe : ((g.rule.body.read.dedup : List Expr) : Multiset Expr) ≤
        (s.present \ g.selection.taken.toFinset).val.map s.label := by
      refine (Multiset.le_iff_subset (Multiset.coe_nodup.mpr (List.nodup_dedup _))).mpr ?_
      intro x member
      exact readInD x (List.mem_dedup.mp (Multiset.mem_coe.mp member))
    refine ⟨(s.present \ g.selection.taken.toFinset).val.map s.label - (g.rule.body.read.dedup : Multiset Expr),
      ?_, ?_, trivialInfo⟩
    · rw [show stateBag s = bagOf s.label ⟨s.knowledge, s.present⟩ from rfl,
        bagOf_split s.label (C := ⟨s.knowledge, s.present⟩) takenNodup enabled.taken_subset, takenLabels]
      rw [consumes, ← Multiset.coe_add, add_assoc, add_tsub_cancel_of_le dedupLe]
    · rw [stateBag_result g admitted, yields, ← Multiset.coe_add, add_assoc, add_tsub_cancel_of_le dedupLe]
      exact add_comm _ _

end Firing

/-- **For a rule of the fragment whose guards hold, every way of finding its consumed rows in the bag of a state
with trivial knowledge is an admitted firing of `RuleSyntax.step`**, when identities are infinitely many. -/
theorem admitted_of_bag [Infinite O] {r : Rule Rows} (member : r ∈ rules) (positive : Positive r)
    (holds : guardsHold r = true) {s : State Rows O} (knowledge : Trivial s.knowledge) {rest : Multiset Expr}
    (split : ((consumes r : List Expr) : Multiset Expr) + rest = stateBag s) :
    ∃ (g : Firing O (ext ground) {r | r ∈ rules} s.frame) (admitted : (groundStep O rules).Admits (s := s) g),
      stateBag ((groundStep O rules).result g admitted) = ((yields r : List Expr) : Multiset Expr) + rest := by
  rw [consumes, ← Multiset.coe_add, add_assoc] at split
  obtain ⟨taken, takenNodup, takenIn, takenLabels⟩ :=
    exists_taken s.label r.body.take s.present
      (show (r.body.take : Multiset Expr) ≤ s.present.val.map s.label from (le_add_right le_rfl).trans_eq split)
  have takenSub : taken.toFinset ⊆ s.present := fun o member => takenIn o (List.mem_toFinset.mp member)
  have restEq : ((r.body.read.dedup : List Expr) : Multiset Expr) + rest =
      (s.present \ taken.toFinset).val.map s.label := by
    have whole := bagOf_split s.label (C := ⟨s.knowledge, s.present⟩) takenNodup takenSub
    rw [takenLabels] at whole
    exact add_left_cancel (split.trans whole)
  obtain ⟨read, readIn, readLabels⟩ := exists_read s.label r.body.read (s.present \ taken.toFinset) (by
    intro x member
    rw [← restEq]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr (List.mem_dedup.mpr member))))
  obtain ⟨made, madeNodup, madeLength, madeFresh⟩ := exists_fresh s.present r.body.produce.length
  have collectEmpty : r.collect = [] := positive.1
  let g : Firing O (ext ground) {r | r ∈ rules} s.frame := ⟨r, member, PUnit.unit, (), ⟨taken, read, made⟩, []⟩
  have info : g.information (frames ground) s = s.knowledge ++ Selection.equations s.label r.body.take taken ++
      Selection.equations s.label r.body.read read ++ r.body.tell := information_ground g
  have trivialInfo : Trivial (g.information (frames ground) s) := by
    have tells : Trivial r.body.tell := by
      simp only [guardsHold, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at holds
      exact holds.1
    rw [info]
    intro e member
    simp only [List.mem_append] at member
    rcases member with ((old | taking) | reading) | told
    · exact knowledge e old
    · rw [← takenLabels] at taking
      exact equations_trivial s.label taken e taking
    · rw [← readLabels] at reading
      exact equations_trivial s.label read e reading
    · exact tells e told
  have admitted : (groundStep O rules).Admits (s := s) g := by
    refine (admits_iff g).mpr ⟨RuleSyntax.Examples.fresh_of_ground ground s g fun _ _ _ => rfl,
      ⟨takenNodup, madeNodup, by rw [← takenLabels, List.length_map], by rw [← readLabels, List.length_map],
        madeLength.symm, by rw [collectEmpty]; rfl⟩, ?_,
      (Frames.ofSubstitution_solvable_iff ground _).mpr ((consistent_iff_trivial _).mpr trivialInfo), ?_, ?_⟩
    · exact ⟨takenSub, fun o member => (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp member))).1,
        Finset.disjoint_left.mpr fun o taking reading =>
          (Finset.mem_sdiff.mp (readIn o (List.mem_toFinset.mp reading))).2 taking,
        Finset.disjoint_left.mpr fun o member present => madeFresh o (List.mem_toFinset.mp member) present,
        fun query member => by simp [Selection.commit] at member⟩
    · intro c member _ _ _
      rw [opened_ground] at member
      obtain ⟨t, rfl⟩ := checks_trivial positive holds c member
      rfl
    · intro q member
      have none : (g.collectOpened (frames ground)).zip g.seen = [] := by
        simp [Firing.collectOpened, g, collectEmpty]
      rw [none] at member
      exact absurd member List.not_mem_nil
  refine ⟨g, admitted, ?_⟩
  rw [stateBag_result g admitted]
  show (s.present \ taken.toFinset).val.map s.label + _ = _
  rw [← restEq, yields, ← Multiset.coe_add]
  exact (add_comm _ _).trans (add_assoc _ _ _).symm

/-! ## The theorem -/

/-- **The generated possibility is the firing possibility of `RuleSyntax.step`**: for a program of the positive
fragment, at the store of a state with trivial knowledge, the framework's derived possibility of an
equation-invariant property holds exactly when some admitted firing of `RuleSyntax.step` reaches a state whose
store has the property. -/
theorem generated_possibility_direct [Infinite O] {relEnv : RelationEnv} (positive : ∀ r ∈ rules, Positive r)
    {s : State Rows O} (knowledge : Trivial s.knowledge)
    (φ : EquationPredicate (langGSLTUsing relEnv (present rules))) :
    (langDiamondUsing relEnv (present rules) φ).1 (stateStore s) ↔
      ∃ (g : Firing O (ext ground) {r | r ∈ rules} s.frame) (admitted : (groundStep O rules).Admits (s := s) g),
        φ.1 (stateStore ((groundStep O rules).result g admitted)) := by
  refine (diamond_storeCode_iff φ _).trans ?_
  constructor
  · rintro ⟨r, member, holds, rest, split, satisfied⟩
    have bag : ((consumes r : List Expr) : Multiset Expr) + (rest : Multiset Expr) = stateBag s := by
      rw [Multiset.coe_add, ← coe_stateRows s]
      exact Multiset.coe_eq_coe.mpr split
    obtain ⟨g, admitted, after⟩ := admitted_of_bag member (positive r member) holds knowledge bag
    refine ⟨g, admitted, (φ.2 ?_).mp satisfied⟩
    refine equationEquiv_storeCode_of_perm presentWith_formers presentWith_store (Multiset.coe_eq_coe.mp ?_)
    rw [← Multiset.coe_add, coe_stateRows, after]
    rfl
  · rintro ⟨g, admitted, satisfied⟩
    obtain ⟨member, holds, rest, before, after, -⟩ := bag_of_admitted g admitted
    have before' : ((standard.consumed g.rule : List Expr) : Multiset Expr) + rest = stateBag s := before
    have after' : stateBag ((groundStep O rules).result g admitted) =
        ((standard.yielded g.rule : List Expr) : Multiset Expr) + rest := after
    refine ⟨g.rule, member, holds, rest.toList, ?_, (φ.2 ?_).mpr satisfied⟩
    · refine Multiset.coe_eq_coe.mp ?_
      rw [← Multiset.coe_add, Multiset.coe_toList, before', coe_stateRows]
    · refine equationEquiv_storeCode_of_perm presentWith_formers presentWith_store (Multiset.coe_eq_coe.mp ?_)
      rw [← Multiset.coe_add, Multiset.coe_toList, coe_stateRows, after']

/-- **In OSLF's form**: pulled back along the store map, the generated diamond is the derived diamond of the firing
span of `RuleSyntax.step`, at every state with trivial knowledge. -/
theorem pulled_back_diamond_direct [Infinite O] {relEnv : RelationEnv} (positive : ∀ r ∈ rules, Positive r)
    {s : State Rows O} (knowledge : Trivial s.knowledge)
    (φ : EquationPredicate (langGSLTUsing relEnv (present rules))) :
    pb stateStore (langDiamondUsing relEnv (present rules) φ).1 s ↔
      derivedDiamond (firingSpan (groundStep O rules).toStep) (pb stateStore φ.1) s := by
  refine (generated_possibility_direct positive knowledge φ).trans ?_
  constructor
  · rintro ⟨g, admitted, holds⟩
    exact ⟨⟨s, g, admitted⟩, rfl, holds⟩
  · rintro ⟨⟨_, g, admitted⟩, rfl, holds⟩
    exact ⟨g, admitted, holds⟩

namespace Examples

open Presentation.Examples (demo demo_positive isTwo consume consume_member)

/-- One token `1` at identity `0`, every identity labelled `1`: a label with no supply of fresh identities for
other rows. -/
def tokenState : State Rows ℕ := ⟨PUnit.unit, [], {0}, fun _ => .sym 1⟩

theorem stateStore_tokenState : stateStore tokenState = storeCode [.sym 1] := by
  simp [stateStore, tokenState, Finset.toList_singleton]

/-- **Existence for the direct form**: at the token state the generated possibility of "the store is `{2}`"
holds, and so `RuleSyntax.step` has an admitted firing there whose result's store is `{2}` up to the
equations. -/
theorem direct_holds {relEnv : RelationEnv} :
    (langDiamondUsing relEnv (present demo) (isTwo relEnv demo)).1 (stateStore tokenState) ∧
      ∃ (g : Firing ℕ (ext ground) {r | r ∈ demo} tokenState.frame)
        (admitted : (groundStep ℕ demo).Admits (s := tokenState) g),
        (isTwo relEnv demo).1 (stateStore ((groundStep ℕ demo).result g admitted)) := by
  have holds : (langDiamondUsing relEnv (present demo) (isTwo relEnv demo)).1 (stateStore tokenState) := by
    rw [stateStore_tokenState]
    exact (diamond_storeCode_iff _ _).mpr ⟨consume, consume_member, by decide, [], by decide,
      ⟨_, Relation.EqvGen.refl _, rfl⟩⟩
  exact ⟨holds, (generated_possibility_direct demo_positive (s := tokenState)
    (fun _ member => absurd member List.not_mem_nil) (isTwo relEnv demo)).mp holds⟩

#print axioms direct_holds

end Examples

#print axioms exists_fresh
#print axioms information_ground
#print axioms stateBag_result
#print axioms bag_of_admitted
#print axioms admitted_of_bag
#print axioms generated_possibility_direct
#print axioms pulled_back_diamond_direct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
