import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflPacking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNameTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution

/-!
# One source step at a child location

The located program (`ReflLocated.located`) gives a child location `l = Child(m, x, P)` the token
`Pending(l, m)` when it opens; a source step at `l` (the located COMM `commChild`, or an inner close
`closeChild`) takes `Pending(l, _)` and makes `Done(l, _, 0)`; cooling keeps a `Done(l, _, _)`; the close of
`l` takes it. Here, at the name frame `QN`, for a fixed child `l = childLoc m x p`:

* **the phases** (`PendingPhase`, `DonePhase`): before the step, one row may read as `Pending(l, _)` and it
  reads as `Pending(l, m)` at every solution, and no row may read as `Done(l, _, _)`; after the step, no row may
  read as `Pending(l, _)`, and a row reads as `Done(l, m, _)` at every solution;
* **one firing** (`pending_phase_step`, `done_phase_step`): from the first phase every admitted firing of the
  located program that is no close of `l` is either no source step at `l` and keeps the first phase, or a source
  step at `l` and reaches the second; from the second phase every such firing is no source step at `l` and keeps
  the second phase;
* **at most one** (`at_most_one_step`): along every run from the first phase in which `l` is not closed, at most
  one source step at `l` fires;
* **exactly one before the close** (`close_refused_before_step`, `exactly_one_before_close`): a close of `l` is
  refused in the first phase, so a close of `l` after such a run comes after exactly one source step at `l`;
* **the step is the token's** (`step_reads_token`): a source step at `l` takes the row `Pending(l, m)`.

A firing is a source step at `l` when its rule is `commChild` or `closeChild` and its location `L` reads as `l`
at some solution of its information; it is a close of `l` when its rule is `closeRoot` or `closeChild` and the
child it closes reads as `l` at some solution. Both are the most inclusive readings: counting every possible
source step makes "at most one" the stronger statement.

That the child can step when its process can is `ReflLocated.heatChild_admitted` (heating) and, for the step
itself, `child_comm_admitted` and `child_steps_once` (the located COMM at a redex), `child_close_admitted` and
`child_closes_once` (the inner close, once no row is left at the grandchild): in the first phase each is admitted
at every fresh opening, is a source step at `l`, and reaches the second phase.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedStep

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect applyDot)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open MeTTaOperationsComm (psubst PSubst pvars psubst_none psubst_comp psubst_congr psubst_of_pvars_nil
  commSelection)
open MeTTaCalculus.Corrected (psubstList_eq_map)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open FiniteProgram (commRule heatRule clearRule program mem_program leftPart rightPart firstPattern secondPattern
  channelUnknown firstBody secondBody)
open Comm (Tm)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE nameLaws_heads nameLaws_apply_iff IsQuote)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC anyY anyZ atRule rootRules
  childRules openRules located commChild commChild_mem heatChild cool closeRoot closeChild openRoot openChild
  exists_mem_zip psubst_apply psubst_atLoc_any psubst_pendingTok)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff)

/-! ## The rules of the located program, by shape -/

theorem located_cases {r : Rule Tm} (member : r ∈ located) :
    r = atRule rootLoc commRule ∨ r = atRule rootLoc heatRule ∨ r = atRule rootLoc clearRule ∨
      r = commChild ∨ r = heatChild ∨ r = cool ∨ r = closeRoot ∨ r = closeChild ∨ r = openRoot ∨
      r = openChild := by
  rcases (Set.mem_union _ _ _).mp member with front | opens
  · rcases (Set.mem_union _ _ _).mp front with root | child
    · obtain ⟨r', member', rfl⟩ := (Set.mem_image _ _ _).mp root
      rcases mem_program.mp member' with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
    · simp only [childRules, Set.mem_insert_iff, Set.mem_singleton_iff] at child
      rcases child with rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [openRules, Set.mem_insert_iff, Set.mem_singleton_iff] at opens
    rcases opens with rfl | rfl <;> simp

/-- **What the located program makes**: rows at a location, the `Pending` token of an opening, or a `Done`
token at the rule's `L` and `M`. -/
theorem produce_shapes {r : Rule Tm} (member : r ∈ located) {t : Pattern} (inside : t ∈ r.body.produce) :
    (∃ args, t = .apply "At" args) ∨
      (r = openRoot ∧ t = pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc) ∨
      (r = openChild ∧ t = pendingTok (childLoc locL channelUnknown reflP) locL) ∨
      ((r = commChild ∨ r = cool ∨ r = closeChild) ∧ ∃ c, t = doneTok locL locM c) := by
  rcases located_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [atRule, RuleInstance.map, commRule, heatRule, clearRule, commChild, heatChild, cool, closeRoot,
      closeChild, openRoot, openChild, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at inside
  all_goals
    rcases inside with rfl | rfl | rfl <;> first
      | exact .inl ⟨_, rfl⟩
      | exact .inr (.inr (.inr ⟨by simp, _, rfl⟩))
      | exact .inr (.inl ⟨rfl, rfl⟩)
      | exact .inr (.inr (.inl ⟨rfl, rfl⟩))

/-- **What the located program takes**: rows at a location, the `Pending` token at a source step, the `Done`
token when cooling, or the `Done` token of the closed child. -/
theorem take_shapes {r : Rule Tm} (member : r ∈ located) {t : Pattern} (inside : t ∈ r.body.take) :
    (∃ args, t = .apply "At" args) ∨
      ((r = commChild ∨ r = closeChild) ∧ t = pendingTok locL locM) ∨
      (r = cool ∧ t = doneTok locL locM accC) ∨
      (r = closeRoot ∧ t = doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC) ∨
      (r = closeChild ∧ t = doneTok (childLoc locL channelUnknown reflP) locL accC) := by
  rcases located_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [atRule, RuleInstance.map, commRule, heatRule, clearRule, commChild, heatChild, cool, closeRoot,
      closeChild, openRoot, openChild, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at inside
  all_goals
    rcases inside with rfl | rfl | rfl <;> first
      | exact .inl ⟨_, rfl⟩
      | exact .inr (.inl ⟨by simp, rfl⟩)
      | exact .inr (.inr (.inl ⟨rfl, rfl⟩))
      | exact .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))
      | exact .inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))

/-- **What the located program reads**: rows at a location, or a `Pending` token. -/
theorem read_shapes {r : Rule Tm} (member : r ∈ located) {t : Pattern} (inside : t ∈ r.body.read) :
    (∃ args, t = .apply "At" args) ∨ t = pendingTok locL locM := by
  rcases located_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [atRule, RuleInstance.map, commRule, heatRule, clearRule, commChild, heatChild, cool, closeRoot,
      closeChild, openRoot, openChild, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at inside
  all_goals
    rcases inside with rfl | rfl <;> first
      | exact .inl ⟨_, rfl⟩
      | exact .inr rfl

/-! ## Readings of terms at the name frame -/

/-- A reading keeps its head. -/
theorem head_of_reading {σ : PSubst} {c d : String} {args args' : List Pattern}
    (same : NameLaws (psubst σ (.apply c args)) (.apply d args')) : c = d := by
  rw [psubst_apply] at same
  exact nameLaws_heads same

theorem psubst_childLoc (σ : PSubst) (m x p : Pattern) :
    psubst σ (childLoc m x p) = childLoc (psubst σ m) (psubst σ x) (psubst σ p) := by
  simp only [childLoc, psubst, psubstList_eq_map, List.map_cons, List.map_nil]

theorem nameLaws_pendingTok_iff {l m l' m' : Pattern} :
    NameLaws (pendingTok l m) (pendingTok l' m') ↔ NameLaws l l' ∧ NameLaws m m' := by
  rw [pendingTok, pendingTok, nameLaws_apply_iff (by unfold IsQuote; decide)]
  simp

theorem nameLaws_childLoc_iff {m x p m' x' p' : Pattern} :
    NameLaws (childLoc m x p) (childLoc m' x' p') ↔ NameLaws m m' ∧ NameLaws x x' ∧ NameLaws p p' := by
  rw [childLoc, childLoc, nameLaws_apply_iff (by unfold IsQuote; decide)]
  simp

theorem exists_mem_zip_right {α β : Type*} {xs : List α} {ys : List β} (lengths : xs.length = ys.length) {y : β}
    (inside : y ∈ ys) : ∃ x, (x, y) ∈ xs.zip ys := by
  obtain ⟨x, zipped⟩ := exists_mem_zip lengths.symm inside
  refine ⟨x, ?_⟩
  rw [← List.zip_swap]
  exact List.mem_map.mpr ⟨(y, x), zipped, rfl⟩

/-! ## Firings of the located program at the name frame -/

section Firings

variable {O : Type*} [DecidableEq O]

/-- Shorthand: the result of a firing at an embedded state. -/
abbrev res (label : O → Pattern) (C : Configuration Pattern O) (g : Firing O QNE located PUnit.unit) :
    State Tm O :=
  g.result QN (embed label C)

/-- The configuration of a result. -/
abbrev resConf (label : O → Pattern) (C : Configuration Pattern O) (g : Firing O QNE located PUnit.unit) :
    Configuration Pattern O :=
  ⟨(res label C g).knowledge, (res label C g).present⟩

omit [DecidableEq O] in
theorem info_known {label : O → Pattern} {C : Configuration Pattern O} {P : Program Tm}
    (g : Firing O QNE P PUnit.unit)
    {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C))) :
    nameAction.Models σ C.equations := by
  rw [OneFrame.information_eq] at solved
  exact fun e member => solved e (by simp [Selection.problem, member])

omit [DecidableEq O] in
theorem take_reads {label : O → Pattern} {C : Configuration Pattern O} {P : Program Tm}
    (g : Firing O QNE P PUnit.unit) {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C))) {t : Pattern} {o : O}
    (inside : (t, o) ∈ g.rule.body.take.zip g.selection.taken) :
    NameLaws (psubst σ (psubst g.opening t)) (psubst σ (label o)) := by
  have zipped : (QN.act (a := PUnit.unit) (b := PUnit.unit) g.opening t, o) ∈
      (g.opened QN).take.zip g.selection.taken := by
    show _ ∈ (g.rule.body.take.map _).zip _
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨_, inside, rfl⟩
  have equal := Firing.take_solved (X := QN) (s := embed label C) g (b := PUnit.unit) solved zipped
  rw [OneFrame.row_eq] at equal
  exact equal

omit [DecidableEq O] in
theorem read_reads {label : O → Pattern} {C : Configuration Pattern O} {P : Program Tm}
    (g : Firing O QNE P PUnit.unit) {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C))) {t : Pattern} {o : O}
    (inside : (t, o) ∈ g.rule.body.read.zip g.selection.read) :
    NameLaws (psubst σ (psubst g.opening t)) (psubst σ (label o)) := by
  have zipped : (QN.act (a := PUnit.unit) (b := PUnit.unit) g.opening t, o) ∈
      (g.opened QN).read.zip g.selection.read := by
    show _ ∈ (g.rule.body.read.map _).zip _
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨_, inside, rfl⟩
  have equal := Firing.read_solved (X := QN) (s := embed label C) g (b := PUnit.unit) solved zipped
  rw [OneFrame.row_eq] at equal
  exact equal

/-- An admitted firing selects, for every take pattern, a present row. -/
theorem taken_row {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) {t : Pattern}
    (inside : t ∈ g.rule.body.take) : ∃ o, (t, o) ∈ g.rule.body.take.zip g.selection.taken ∧ o ∈ C.present := by
  obtain ⟨_, shapes, enabled, _, _, _⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨o, zipped⟩ := exists_mem_zip shapes.2.2.1 inside
  refine ⟨o, zipped, enabled.taken_subset ?_⟩
  simp only [Selection.commit, List.mem_toFinset]
  exact (List.of_mem_zip zipped).2

/-- An admitted firing has a solution of its information. -/
theorem solution_of_admitted {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) := by
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff g).mp admitted).2.2.2.1
  exact ⟨σ, solved⟩

theorem result_present {label : O → Pattern} {C : Configuration Pattern O} (g : Firing O QNE located PUnit.unit)
    (o : O) : o ∈ (res label C g).present ↔ (o ∈ C.present ∧ o ∉ g.selection.taken) ∨ o ∈ g.selection.made := by
  show o ∈ fire C.present (g.selection.commit (T := Unit)) ↔ _
  simp [fire, Selection.commit]

theorem result_label_old {label : O → Pattern} {C : Configuration Pattern O} (g : Firing O QNE located PUnit.unit)
    {o : O} (notMade : o ∉ g.selection.made) : (res label C g).label o = label o :=
  (Firing.result_label_other (X := QN) (s := embed label C) g notMade).trans (congrFun (OneFrame.row_eq C g) o)

theorem result_label_made_from_shapes {label : O → Pattern} {C : Configuration Pattern O}
    {g : Firing O QNE located PUnit.unit} (shapes : g.Shapes QN (embed label C)) {o : O} {t : Pattern}
    (inside : (o, t) ∈ g.selection.made.zip g.rule.body.produce) :
    (res label C g).label o = psubst g.opening t := by
  have zipped : (o, QN.act (a := PUnit.unit) (b := PUnit.unit) g.opening t) ∈
      g.selection.made.zip (g.opened QN).produce := by
    show _ ∈ List.zip g.selection.made (g.rule.body.produce.map _)
    rw [List.zip_map_right]
    exact List.mem_map.mpr ⟨_, inside, rfl⟩
  exact Firing.result_label_made (X := QN) (s := embed label C) g shapes zipped

theorem result_label_made {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) {o : O} {t : Pattern}
    (inside : (o, t) ∈ g.selection.made.zip g.rule.body.produce) :
    (res label C g).label o = psubst g.opening t :=
  result_label_made_from_shapes admitted.1 inside

/-- Every made row carries an opened made pattern. -/
theorem made_label {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) {o : O}
    (made : o ∈ g.selection.made) : ∃ t ∈ g.rule.body.produce, (res label C g).label o = psubst g.opening t := by
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨t, zipped⟩ := exists_mem_zip shapes.2.2.2.2.1.symm made
  exact ⟨t, (List.of_mem_zip zipped).2, result_label_made admitted zipped⟩

/-- A made identity is not a present one. -/
theorem made_not_present {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) {o : O}
    (made : o ∈ g.selection.made) : o ∉ C.present := by
  obtain ⟨_, _, enabled, _, _, _⟩ := (RuleSyntax.admits_iff g).mp admitted
  exact Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using made)

/-- A row is a made one, or an old one with its label. -/
theorem result_row {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    {o : O} (present : o ∈ (res label C g).present) :
    o ∈ g.selection.made ∨ (o ∈ C.present ∧ o ∉ g.selection.taken ∧ o ∉ g.selection.made ∧
      (res label C g).label o = label o) := by
  by_cases made : o ∈ g.selection.made
  · exact .inl made
  · rcases (result_present g o).mp present with ⟨old, notTaken⟩ | made'
    · exact .inr ⟨old, notTaken, made, result_label_old g made⟩
    · exact absurd made' made

end Firings

/-! ## The phases of a child -/

section Phases

variable {O : Type*} [DecidableEq O]

/-- A row may read as the `Pending` token of `l`: at some solution of the knowledge. -/
def MayPend (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (o : O) : Prop :=
  ∃ σ : PSubst, nameAction.Models σ C.equations ∧ ∃ m', NameLaws (psubst σ (label o)) (pendingTok l m')

/-- A row may read as a `Done` token of `l`: at some solution of the knowledge. -/
def MayDone (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (o : O) : Prop :=
  ∃ σ : PSubst, nameAction.Models σ C.equations ∧ ∃ m' c, NameLaws (psubst σ (label o)) (doneTok l m' c)

/-- **Before the step**: the row `q` reads as `Pending(l, m)` at every solution, it is the only row that may
read as a `Pending` token of `l`, and no row may read as a `Done` token of `l`. -/
structure PendingPhase (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (q : O) : Prop where
  present : q ∈ C.present
  reads : ∀ σ : PSubst, nameAction.Models σ C.equations → NameLaws (psubst σ (label q)) (pendingTok l m)
  unique : ∀ o ∈ C.present, MayPend l label C o → o = q
  noDone : ∀ o ∈ C.present, ¬ MayDone l label C o

/-- **After the step**: no row may read as a `Pending` token of `l`, and the row `d` reads as `Done(l, m, _)` at
every solution. -/
structure DonePhase (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (d : O) : Prop where
  present : d ∈ C.present
  reads : ∀ σ : PSubst, nameAction.Models σ C.equations → ∃ c, NameLaws (psubst σ (label d)) (doneTok l m c)
  noPend : ∀ o ∈ C.present, ¬ MayPend l label C o

/-- **A source step at `l`**: a located COMM or an inner close whose location reads as `l` at some solution of
its information. -/
def StepAt (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (g : Firing O QNE located PUnit.unit) :
    Prop :=
  (g.rule = commChild ∨ g.rule = closeChild) ∧
    ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening locL)) l

/-- **A close of `l`**: a close whose child reads as `l` at some solution of its information. -/
def CloseAt (l : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (g : Firing O QNE located PUnit.unit) :
    Prop :=
  (g.rule = closeRoot ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening (childLoc rootLoc channelUnknown reflP))) l) ∨
    (g.rule = closeChild ∧ ∃ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) ∧
      NameLaws (psubst σ (psubst g.opening (childLoc locL channelUnknown reflP))) l)

end Phases

/-! ## Readings of tokens -/

theorem head_of_reading₂ {σ ρ : PSubst} {c d : String} {args args' : List Pattern}
    (same : NameLaws (psubst σ (psubst ρ (.apply c args))) (.apply d args')) : c = d := by
  rw [psubst_apply, psubst_apply] at same
  exact nameLaws_heads same

theorem pending_reading {σ ρ : PSubst} {a b l m : Pattern}
    (same : NameLaws (psubst σ (psubst ρ (pendingTok a b))) (pendingTok l m)) :
    NameLaws (psubst σ (psubst ρ a)) l ∧ NameLaws (psubst σ (psubst ρ b)) m := by
  rw [psubst_pendingTok, psubst_pendingTok] at same
  exact nameLaws_pendingTok_iff.mp same

theorem done_reading {σ ρ : PSubst} {a b c l m c' : Pattern}
    (same : NameLaws (psubst σ (psubst ρ (doneTok a b c))) (doneTok l m c')) :
    NameLaws (psubst σ (psubst ρ a)) l ∧ NameLaws (psubst σ (psubst ρ b)) m ∧ NameLaws (psubst σ (psubst ρ c)) c' := by
  rw [psubst_doneTok, psubst_doneTok] at same
  exact nameLaws_doneTok_iff.mp same

theorem child_reading {σ ρ : PSubst} {par m x p : Pattern}
    (same : NameLaws (psubst σ (psubst ρ (childLoc par channelUnknown reflP))) (childLoc m x p)) :
    NameLaws (psubst σ (psubst ρ par)) m := by
  rw [psubst_childLoc, psubst_childLoc] at same
  exact (nameLaws_childLoc_iff.mp same).1

/-! ## Opening is refused while the child is alive -/

section Opening

variable {O : Type*} [DecidableEq O]

omit [DecidableEq O] in
theorem opened_check_mem {g : Firing O QNE located PUnit.unit} {c : Check Pattern} (inside : c ∈ g.rule.body.checks) :
    c.map (QN.act (a := PUnit.unit) (b := PUnit.unit) g.opening) ∈ (g.opened QN).checks := by
  show _ ∈ g.rule.body.checks.map _
  exact List.mem_map_of_mem inside

/-- **An opening of `l` is refused while `l` has a `Pending` token**: the opening asks that its child have no
`Pending` token; at a solution where its child reads as `l = Child(m, x, p)`, the row reading `Pending(l, m)`
is one. -/
theorem check_fails_pending {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) {par : Pattern}
    (hasCheck : Check.predicate .none (pendingTok (childLoc par channelUnknown reflP) par) ∈ g.rule.body.checks)
    {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C))) {m x p : Pattern}
    (child : NameLaws (psubst σ (psubst g.opening (childLoc par channelUnknown reflP))) (childLoc m x p))
    {q : O} (present : q ∈ C.present) (reads : NameLaws (psubst σ (label q)) (pendingTok (childLoc m x p) m)) :
    False := by
  have checks := ((RuleSyntax.admits_iff g).mp admitted).2.2.2.2.1
  have holds : ∀ o ∈ C.present, ¬ NameLaws
      (psubst σ (psubst g.opening (pendingTok (childLoc par channelUnknown reflP) par)))
      (psubst σ (g.row QN (embed label C) o)) :=
    checks _ (opened_check_mem hasCheck) PUnit.unit σ solved
  apply holds q present
  rw [OneFrame.row_eq, psubst_pendingTok, psubst_pendingTok]
  exact (nameLaws_pendingTok_iff.mpr ⟨child, child_reading child⟩).trans reads.symm

/-- **An opening of `l` is refused while `l` has a `Done` token**: the opening asks that its child have no
`Done(_, _, Z)` token, `Z` an unknown of its own; moving `Z` onto the accumulator of the row reading
`Done(l, m, c)` gives a solution of the information at which the absence fails. -/
theorem check_fails_done {label : O → Pattern} {C : Configuration Pattern O} {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) {par : Pattern}
    (hasCheck : Check.predicate .none (doneTok (childLoc par channelUnknown reflP) par anyZ) ∈ g.rule.body.checks)
    (noTakes : g.rule.body.take = []) (noTells : g.rule.body.tell = [])
    (readsApart : ∀ t ∈ g.rule.body.read, "Z" ∉ pvars t)
    (parApart : "Z" ∉ pvars (childLoc par channelUnknown reflP) ∧ "Z" ∉ pvars par)
    {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C))) {m x p c : Pattern}
    (child : NameLaws (psubst σ (psubst g.opening (childLoc par channelUnknown reflP))) (childLoc m x p))
    {d : O} (present : d ∈ C.present) (reads : NameLaws (psubst σ (label d)) (doneTok (childLoc m x p) m c)) :
    False := by
  obtain ⟨fresh, _, enabled, _, checks, _⟩ := (RuleSyntax.admits_iff g).mp admitted
  let h : PSubst := fun v => if v = "Z" then some c else some (psubst σ (psubst g.opening (.fvar v)))
  have away : ∀ t : Pattern, "Z" ∉ pvars t → psubst h t = psubst σ (psubst g.opening t) := by
    intro t apart
    rw [psubst_comp]
    apply MeTTaCalculus.Corrected.psubst_getD_congr_on
    intro v occurs
    have notZ : v ≠ "Z" := fun same => apart (same ▸ occurs)
    simp only [h, if_neg notZ, Option.getD_some]
    rw [psubst_comp]
    rfl
  obtain ⟨u, solvedU, onState, onRule⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C) g
    fresh (b := PUnit.unit) σ h (info_known g solved)
    (by rw [noTells]; exact fun _ member => absurd member List.not_mem_nil)
    (fun o member => enabled.taken_subset (by simpa [Selection.commit] using member))
    (fun o member => enabled.kept_subset (by simpa [Selection.commit] using member))
    (fun qq member => by rw [noTakes] at member; simp at member)
    (fun qq member => by
      have apart := readsApart qq.1 (List.of_mem_zip member).1
      show NameLaws (psubst h qq.1) (psubst σ (label qq.2))
      rw [away qq.1 apart]
      exact read_reads g solved member)
  have holds : ∀ o ∈ C.present, ¬ NameLaws
      (psubst u (psubst g.opening (doneTok (childLoc par channelUnknown reflP) par anyZ)))
      (psubst u (g.row QN (embed label C) o)) :=
    checks _ (opened_check_mem hasCheck) PUnit.unit u solvedU
  apply holds d present
  rw [OneFrame.row_eq]
  have term : doneTok (childLoc par channelUnknown reflP) par anyZ ∈ g.rule.terms := by
    simp only [Rule.terms, List.mem_append]
    exact .inl (.inl (.inr (List.mem_flatMap.mpr ⟨_, hasCheck, by simp [checkTerms]⟩)))
  have ruleSide : NameLaws (psubst u (psubst g.opening (doneTok (childLoc par channelUnknown reflP) par anyZ)))
      (psubst h (doneTok (childLoc par channelUnknown reflP) par anyZ)) := onRule _ term
  have stateSide : NameLaws (psubst u (psubst (fun _ => none) (label d))) (psubst σ (label d)) :=
    onState (label d) (Or.inr (Or.inr ⟨d, present, rfl⟩))
  rw [psubst_none] at stateSide
  have hCheck : psubst h (doneTok (childLoc par channelUnknown reflP) par anyZ) =
      doneTok (psubst σ (psubst g.opening (childLoc par channelUnknown reflP))) (psubst σ (psubst g.opening par)) c := by
    rw [psubst_doneTok, away _ parApart.1, away _ parApart.2]
    simp [h, anyZ, psubst]
  refine ruleSide.trans ?_
  rw [hCheck]
  exact (nameLaws_doneTok_iff.mpr ⟨child, child_reading child, NameLaws.refl _⟩).trans (reads.symm.trans stateSide.symm)

end Opening

/-! ## One firing in each phase -/

section Steps

variable {O : Type*} [DecidableEq O] {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O}

theorem openRoot_checks : Check.predicate .none (pendingTok (childLoc rootLoc channelUnknown reflP) rootLoc) ∈ openRoot.body.checks ∧
    Check.predicate .none (doneTok (childLoc rootLoc channelUnknown reflP) rootLoc anyZ) ∈ openRoot.body.checks := by
  simp [openRoot]

theorem openChild_checks : Check.predicate .none (pendingTok (childLoc locL channelUnknown reflP) locL) ∈ openChild.body.checks ∧
    Check.predicate .none (doneTok (childLoc locL channelUnknown reflP) locL anyZ) ∈ openChild.body.checks := by
  simp [openChild]

/-- In the first phase no made row may read as a `Pending` token of `l`. -/
theorem made_not_pending_first {q : O} (phase : PendingPhase (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit} (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    {o : O} (made : o ∈ g.selection.made) {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C)))
    (m' : Pattern) : ¬ NameLaws (psubst σ ((res label C g).label o)) (pendingTok (childLoc m x p) m') := by
  intro same
  obtain ⟨t, inside, labelEq⟩ := made_label admitted made
  rw [labelEq] at same
  rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨-, c₀, rfl⟩
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact check_fails_pending admitted (by rw [isOpen]; exact openRoot_checks.1) solved (pending_reading same).1
      phase.present (phase.reads σ (info_known g solved))
  · exact check_fails_pending admitted (by rw [isOpen]; exact openChild_checks.1) solved (pending_reading same).1
      phase.present (phase.reads σ (info_known g solved))
  · exact absurd (head_of_reading₂ same) (by decide)

/-- In the second phase no made row may read as a `Pending` token of `l`. -/
theorem made_not_pending_second {d : O} (phase : DonePhase (childLoc m x p) m label C d)
    {g : Firing O QNE located PUnit.unit} (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    {o : O} (made : o ∈ g.selection.made) {σ : PSubst} (solved : nameAction.Models σ (g.information QN (embed label C)))
    (m' : Pattern) : ¬ NameLaws (psubst σ ((res label C g).label o)) (pendingTok (childLoc m x p) m') := by
  intro same
  obtain ⟨t, inside, labelEq⟩ := made_label admitted made
  rw [labelEq] at same
  obtain ⟨c, token⟩ := phase.reads σ (info_known g solved)
  rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨isOpen, rfl⟩ | ⟨-, c₀, rfl⟩
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact check_fails_done admitted (by rw [isOpen]; exact openRoot_checks.2) (by rw [isOpen]; rfl)
      (by rw [isOpen]; rfl) (by rw [isOpen]; decide) (by decide) solved (pending_reading same).1 phase.present token
  · exact check_fails_done admitted (by rw [isOpen]; exact openChild_checks.2) (by rw [isOpen]; rfl)
      (by rw [isOpen]; rfl) (by rw [isOpen]; decide) (by decide) solved (pending_reading same).1 phase.present token
  · exact absurd (head_of_reading₂ same) (by decide)

/-- In the first phase, a firing that is no source step at `l` makes no row that may read as a `Done` token
of `l`. -/
theorem made_not_done_first {q : O} (phase : PendingPhase (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit} (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notStep : ¬ StepAt (childLoc m x p) label C g) {o : O} (made : o ∈ g.selection.made) {σ : PSubst}
    (solved : nameAction.Models σ (g.information QN (embed label C))) (m' c : Pattern) :
    ¬ NameLaws (psubst σ ((res label C g).label o)) (doneTok (childLoc m x p) m' c) := by
  intro same
  obtain ⟨t, inside, labelEq⟩ := made_label admitted made
  rw [labelEq] at same
  rcases produce_shapes g.member inside with ⟨args, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rule, c₀, rfl⟩
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact absurd (head_of_reading₂ same) (by decide)
  · exact absurd (head_of_reading₂ same) (by decide)
  · have loc := (done_reading same).1
    rcases rule with isComm | isCool | isClose
    · exact notStep ⟨.inl isComm, σ, solved, loc⟩
    · obtain ⟨o₁, zipped, present₁⟩ := taken_row admitted (t := doneTok locL locM accC)
        (by rw [isCool]; simp [cool])
      have read := take_reads g solved zipped
      rw [psubst_doneTok, psubst_doneTok] at read
      exact phase.noDone o₁ present₁ ⟨σ, info_known g solved, _, _,
        read.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc, NameLaws.refl _, NameLaws.refl _⟩)⟩
    · exact notStep ⟨.inr isClose, σ, solved, loc⟩

/-- In the first phase, a firing that is no source step at `l` does not take the token. -/
theorem token_kept_first {q : O} (phase : PendingPhase (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit} (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notStep : ¬ StepAt (childLoc m x p) label C g) : q ∉ g.selection.taken := by
  intro taken
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
  obtain ⟨σ, solved⟩ := solution_of_admitted admitted
  have both := (take_reads g solved zipped).trans (phase.reads σ (info_known g solved))
  rcases take_shapes g.member (List.of_mem_zip zipped).1 with ⟨args, rfl⟩ | ⟨rule, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩
  · exact absurd (head_of_reading₂ both) (by decide)
  · exact notStep ⟨rule, σ, solved, (pending_reading both).1⟩
  · exact absurd (head_of_reading₂ both) (by decide)
  · exact absurd (head_of_reading₂ both) (by decide)
  · exact absurd (head_of_reading₂ both) (by decide)

/-- **A source step at `l` takes the token**: in the first phase, a source step at `l` takes the row `q`, and at
every solution of its information its location reads as `l` and its parent as `m`. -/
theorem step_reads_token {q : O} (phase : PendingPhase (childLoc m x p) m label C q)
    {g : Firing O QNE located PUnit.unit} (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (step : StepAt (childLoc m x p) label C g) :
    (pendingTok locL locM, q) ∈ g.rule.body.take.zip g.selection.taken ∧
      ∀ σ : PSubst, nameAction.Models σ (g.information QN (embed label C)) →
        NameLaws (psubst σ (psubst g.opening locL)) (childLoc m x p) ∧ NameLaws (psubst σ (psubst g.opening locM)) m := by
  obtain ⟨rule, σ₀, solved₀, loc₀⟩ := step
  have inside : pendingTok locL locM ∈ g.rule.body.take := by
    rcases rule with isComm | isClose
    · rw [isComm]; simp [commChild]
    · rw [isClose]; simp [closeChild]
  obtain ⟨o₃, zipped, present₃⟩ := taken_row admitted inside
  have read₀ := take_reads g solved₀ zipped
  rw [psubst_pendingTok, psubst_pendingTok] at read₀
  have isQ : o₃ = q := phase.unique o₃ present₃ ⟨σ₀, info_known g solved₀, psubst σ₀ (psubst g.opening locM),
    read₀.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc₀, NameLaws.refl _⟩)⟩
  subst isQ
  exact ⟨zipped, fun σ solved => pending_reading ((take_reads g solved zipped).trans (phase.reads σ (info_known g solved)))⟩

/-- **From the first phase, one firing**: every admitted firing is either no source step at `l` and keeps the
first phase, or a source step at `l` and reaches the second. -/
theorem pending_phase_step {q : O} (phase : PendingPhase (childLoc m x p) m label C q)
    (g : Firing O QNE located PUnit.unit) (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g) :
    (¬ StepAt (childLoc m x p) label C g ∧
        PendingPhase (childLoc m x p) m (res label C g).label (resConf label C g) q) ∨
      (StepAt (childLoc m x p) label C g ∧
        ∃ d, DonePhase (childLoc m x p) m (res label C g).label (resConf label C g) d) := by
  by_cases step : StepAt (childLoc m x p) label C g
  · right
    refine ⟨step, ?_⟩
    obtain ⟨tokenTaken, reads⟩ := step_reads_token phase admitted step
    obtain ⟨rule, -⟩ := step
    have produceIn : doneTok locL locM pZero ∈ g.rule.body.produce := by
      rcases rule with isComm | isClose
      · rw [isComm]; simp [commChild]
      · rw [isClose]; simp [closeChild]
    obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
    obtain ⟨d, zippedMade⟩ := exists_mem_zip_right shapes.2.2.2.2.1.symm produceIn
    have qTaken : q ∈ g.selection.taken := (List.of_mem_zip tokenTaken).2
    refine ⟨d, ⟨(result_present g d).mpr (.inr (List.of_mem_zip zippedMade).1), fun σ solved => ?_, ?_⟩⟩
    · rw [result_label_made admitted zippedMade, psubst_doneTok, psubst_doneTok]
      obtain ⟨loc, parent⟩ := reads σ solved
      exact ⟨_, nameLaws_doneTok_iff.mpr ⟨loc, parent, NameLaws.refl _⟩⟩
    · rintro o present ⟨σ, solved, m', same⟩
      rcases result_row present with made | ⟨old, notTaken, -, labelOld⟩
      · exact made_not_pending_first phase admitted made solved m' same
      · rw [labelOld] at same
        have isQ := phase.unique o old ⟨σ, info_known g solved, m', same⟩
        subst isQ
        exact notTaken qTaken
  · left
    refine ⟨step, ⟨?_, fun σ solved => ?_, ?_, ?_⟩⟩
    · exact (result_present g q).mpr (.inl ⟨phase.present, token_kept_first phase admitted step⟩)
    · rw [result_label_old g (fun made => made_not_present admitted made phase.present)]
      exact phase.reads σ (info_known g solved)
    · rintro o present ⟨σ, solved, m', same⟩
      rcases result_row present with made | ⟨old, -, -, labelOld⟩
      · exact absurd same (made_not_pending_first phase admitted made solved m')
      · rw [labelOld] at same
        exact phase.unique o old ⟨σ, info_known g solved, m', same⟩
    · rintro o present ⟨σ, solved, m', c, same⟩
      rcases result_row present with made | ⟨old, -, -, labelOld⟩
      · exact made_not_done_first phase admitted step made solved m' c same
      · rw [labelOld] at same
        exact phase.noDone o old ⟨σ, info_known g solved, m', c, same⟩

/-- **From the second phase, one firing**: every admitted firing that is no close of `l` is no source step at
`l` and keeps the second phase. -/
theorem done_phase_step {d : O} (phase : DonePhase (childLoc m x p) m label C d)
    (g : Firing O QNE located PUnit.unit) (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (notClose : ¬ CloseAt (childLoc m x p) label C g) :
    ¬ StepAt (childLoc m x p) label C g ∧
      ∃ d', DonePhase (childLoc m x p) m (res label C g).label (resConf label C g) d' := by
  have noStep : ¬ StepAt (childLoc m x p) label C g := by
    rintro ⟨rule, σ₀, solved₀, loc₀⟩
    have inside : pendingTok locL locM ∈ g.rule.body.take := by
      rcases rule with isComm | isClose
      · rw [isComm]; simp [commChild]
      · rw [isClose]; simp [closeChild]
    obtain ⟨o₃, zipped, present₃⟩ := taken_row admitted inside
    have read₀ := take_reads g solved₀ zipped
    rw [psubst_pendingTok, psubst_pendingTok] at read₀
    exact phase.noPend o₃ present₃ ⟨σ₀, info_known g solved₀, psubst σ₀ (psubst g.opening locM),
      read₀.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc₀, NameLaws.refl _⟩)⟩
  have noPend : ∀ o ∈ (resConf label C g).present, ¬ MayPend (childLoc m x p) (res label C g).label (resConf label C g) o := by
    rintro o present ⟨σ, solved, m', same⟩
    rcases result_row present with made | ⟨old, -, -, labelOld⟩
    · exact made_not_pending_second phase admitted made solved m' same
    · rw [labelOld] at same
      exact phase.noPend o old ⟨σ, info_known g solved, m', same⟩
  refine ⟨noStep, ?_⟩
  by_cases taken : d ∈ g.selection.taken
  · obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
    obtain ⟨t, zipped⟩ := exists_mem_zip_right shapes.2.2.1 taken
    obtain ⟨σ₀, solved₀⟩ := solution_of_admitted admitted
    obtain ⟨c₀, token₀⟩ := phase.reads σ₀ (info_known g solved₀)
    have both₀ := (take_reads g solved₀ zipped).trans token₀
    rcases take_shapes g.member (List.of_mem_zip zipped).1 with ⟨args, rfl⟩ | ⟨-, rfl⟩ | ⟨isCool, rfl⟩ |
      ⟨isRoot, rfl⟩ | ⟨isChild, rfl⟩
    · exact absurd (head_of_reading₂ both₀) (by decide)
    · exact absurd (head_of_reading₂ both₀) (by decide)
    · have produceIn : doneTok locL locM (par accC leftPart) ∈ g.rule.body.produce := by
        rw [isCool]; simp [cool]
      obtain ⟨d₁, zippedMade⟩ := exists_mem_zip_right shapes.2.2.2.2.1.symm produceIn
      refine ⟨d₁, ⟨(result_present g d₁).mpr (.inr (List.of_mem_zip zippedMade).1), fun σ solved => ?_, noPend⟩⟩
      rw [result_label_made admitted zippedMade, psubst_doneTok, psubst_doneTok]
      obtain ⟨c, token⟩ := phase.reads σ (info_known g solved)
      obtain ⟨loc, parent, -⟩ := done_reading ((take_reads g solved zipped).trans token)
      exact ⟨_, nameLaws_doneTok_iff.mpr ⟨loc, parent, NameLaws.refl _⟩⟩
    · exact absurd (.inl ⟨isRoot, σ₀, solved₀, (done_reading both₀).1⟩) notClose
    · exact absurd (.inr ⟨isChild, σ₀, solved₀, (done_reading both₀).1⟩) notClose
  · refine ⟨d, ⟨(result_present g d).mpr (.inl ⟨phase.present, taken⟩), fun σ solved => ?_, noPend⟩⟩
    rw [result_label_old g (fun made => made_not_present admitted made phase.present)]
    exact phase.reads σ (info_known g solved)

/-- **No close of `l` before the step**: in the first phase every close of `l` is refused. -/
theorem close_refused_before_step {q : O} (phase : PendingPhase (childLoc m x p) m label C q)
    (g : Firing O QNE located PUnit.unit) (close : CloseAt (childLoc m x p) label C g) :
    ¬ (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g := by
  intro admitted
  rcases close with ⟨isRoot, σ₀, solved₀, child₀⟩ | ⟨isChild, σ₀, solved₀, child₀⟩
  · obtain ⟨o₂, zipped, present₂⟩ := taken_row admitted
      (t := doneTok (childLoc rootLoc channelUnknown reflP) rootLoc accC) (by rw [isRoot]; simp [closeRoot])
    have read := take_reads g solved₀ zipped
    rw [psubst_doneTok, psubst_doneTok] at read
    exact phase.noDone o₂ present₂ ⟨σ₀, info_known g solved₀, _, _,
      read.symm.trans (nameLaws_doneTok_iff.mpr ⟨child₀, NameLaws.refl _, NameLaws.refl _⟩)⟩
  · obtain ⟨o₂, zipped, present₂⟩ := taken_row admitted
      (t := doneTok (childLoc locL channelUnknown reflP) locL accC) (by rw [isChild]; simp [closeChild])
    have read := take_reads g solved₀ zipped
    rw [psubst_doneTok, psubst_doneTok] at read
    exact phase.noDone o₂ present₂ ⟨σ₀, info_known g solved₀, _, _,
      read.symm.trans (nameLaws_doneTok_iff.mpr ⟨child₀, NameLaws.refl _, NameLaws.refl _⟩)⟩

end Steps

/-! ## Runs of a child -/

section Runs

variable {O : Type*} [DecidableEq O]

/-- **A run of the located program in which `l` is not closed**, counting the source steps at `l`. -/
inductive ChildRun (l : Pattern) :
    (O → Pattern) → Configuration Pattern O → (O → Pattern) → Configuration Pattern O → ℕ → Prop where
  | refl (label : O → Pattern) (C : Configuration Pattern O) : ChildRun l label C label C 0
  | source {label : O → Pattern} {C : Configuration Pattern O} {label' : O → Pattern}
      {C' : Configuration Pattern O} {n : ℕ} (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (notClose : ¬ CloseAt l label C g) (isStep : StepAt l label C g)
      (rest : ChildRun l (res label C g).label (resConf label C g) label' C' n) :
      ChildRun l label C label' C' (n + 1)
  | other {label : O → Pattern} {C : Configuration Pattern O} {label' : O → Pattern}
      {C' : Configuration Pattern O} {n : ℕ} (g : Firing O QNE located PUnit.unit)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
      (notClose : ¬ CloseAt l label C g) (notStep : ¬ StepAt l label C g)
      (rest : ChildRun l (res label C g).label (resConf label C g) label' C' n) :
      ChildRun l label C label' C' n

/-- From the second phase, no source step at `l` until its close. -/
theorem done_run {m x p : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O} {n : ℕ}
    (run : ChildRun (childLoc m x p) label C label' C' n) :
    ∀ {d : O}, DonePhase (childLoc m x p) m label C d → n = 0 ∧ ∃ d', DonePhase (childLoc m x p) m label' C' d' := by
  induction run with
  | refl label C => exact fun phase => ⟨rfl, _, phase⟩
  | source g admitted notClose isStep rest ih =>
      intro d phase
      exact absurd isStep (done_phase_step phase g admitted notClose).1
  | other g admitted notClose notStep rest ih =>
      intro d phase
      obtain ⟨d', phase'⟩ := (done_phase_step phase g admitted notClose).2
      exact ih phase'

/-- **From the first phase**: along every run in which `l` is not closed, either no source step at `l` fired and
the first phase holds, or exactly one fired and the second phase holds. -/
theorem pending_run {m x p : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O} {n : ℕ}
    (run : ChildRun (childLoc m x p) label C label' C' n) :
    ∀ {q : O}, PendingPhase (childLoc m x p) m label C q →
      (n = 0 ∧ ∃ q', PendingPhase (childLoc m x p) m label' C' q') ∨
        (n = 1 ∧ ∃ d, DonePhase (childLoc m x p) m label' C' d) := by
  induction run with
  | refl label C => exact fun phase => .inl ⟨rfl, _, phase⟩
  | source g admitted notClose isStep rest ih =>
      intro q phase
      rcases pending_phase_step phase g admitted with ⟨notStep, -⟩ | ⟨-, d, phase'⟩
      · exact absurd isStep notStep
      · obtain ⟨zero, d', phase''⟩ := done_run rest phase'
        exact .inr ⟨by omega, d', phase''⟩
  | other g admitted notClose notStep rest ih =>
      intro q phase
      rcases pending_phase_step phase g admitted with ⟨-, phase'⟩ | ⟨isStep, -⟩
      · exact ih phase'
      · exact absurd isStep notStep

/-- **At most one source step at `l`** along every run from the first phase in which `l` is not closed. -/
theorem at_most_one_step {m x p : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O} {n : ℕ}
    {q : O} (phase : PendingPhase (childLoc m x p) m label C q) (run : ChildRun (childLoc m x p) label C label' C' n) :
    n ≤ 1 := by
  rcases pending_run run phase with ⟨zero, -⟩ | ⟨one, -⟩ <;> omega

/-- **Exactly one source step before the close**: after a run from the first phase in which `l` is not closed,
a close of `l` is admitted only if exactly one source step at `l` fired. -/
theorem exactly_one_before_close {m x p : Pattern} {label label' : O → Pattern} {C C' : Configuration Pattern O}
    {n : ℕ} {q : O} (phase : PendingPhase (childLoc m x p) m label C q)
    (run : ChildRun (childLoc m x p) label C label' C' n) (g : Firing O QNE located PUnit.unit)
    (close : CloseAt (childLoc m x p) label' C' g)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label' C') g) : n = 1 := by
  rcases pending_run run phase with ⟨-, q', phase'⟩ | ⟨one, -⟩
  · exact absurd admitted (close_refused_before_step phase' g close)
  · exact one

end Runs

/-! ## The child steps when it can -/

section Progress

variable {O : Type*} [DecidableEq O]

/-- The located COMM at a child: take the inputs `first`, `second` and the token `token`; make `made₁`, `made₂`
and the token `madeTok`. -/
def commChildAt (ρ : PSubst) (first second token made₁ made₂ madeTok : O) : Firing O QNE located PUnit.unit :=
  ⟨commChild, commChild_mem, PUnit.unit, ρ, ⟨[first, second, token], [], [made₁, made₂, madeTok]⟩, []⟩

/-- The instance of the located COMM's unknowns. -/
def childInstance (t u channel left right l m : Pattern) : PSubst := fun v =>
  if v = "T1" then some t else if v = "T2" then some u else if v = "X" then some channel
  else if v = "K1" then some left else if v = "K2" then some right else if v = "L" then some l
  else if v = "M" then some m else none

/-- **The located COMM is admitted when the child holds a redex and its token**: two rows that read as inputs at
`l` on one channel at every solution of the knowledge, a row that reads as `Pending(l, m)`, a solution of the
knowledge unifying the patterns modulo the name laws, distinct taken and made identities, fresh made identities,
and a fresh opening. -/
theorem child_comm_admitted (label : O → Pattern) (C : Configuration Pattern O) (t u channel K₁ K₂ l m : Pattern)
    (first second token made₁ made₂ madeTok : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel K₁) l)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel K₂) l)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m)))
    (distinct : [first, second, token].Nodup) (madeDistinct : [made₁, made₂, madeTok].Nodup)
    (present : first ∈ C.present ∧ second ∈ C.present ∧ token ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ made₂ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commChildAt ρ first second token made₁ made₂ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (commChildAt ρ first second token made₁ made₂ madeTok) := by
  let h : PSubst := childInstance (psubst σ₀ t) (psubst σ₀ u) (psubst σ₀ channel) (psubst σ₀ K₁) (psubst σ₀ K₂)
    (psubst σ₀ l) (psubst σ₀ m)
  have hFirst : psubst h (atLoc (pFor firstPattern channelUnknown firstBody) locL) =
      psubst σ₀ (atLoc (pFor t channel K₁) l) := by
    simp [h, childInstance, atLoc, pFor, firstPattern, channelUnknown, firstBody, locL, psubst, psubstList_eq_map]
  have hSecond : psubst h (atLoc (pFor secondPattern channelUnknown secondBody) locL) =
      psubst σ₀ (atLoc (pFor u channel K₂) l) := by
    simp [h, childInstance, atLoc, pFor, secondPattern, channelUnknown, secondBody, locL, psubst, psubstList_eq_map]
  have hToken : psubst h (pendingTok locL locM) = psubst σ₀ (pendingTok l m) := by
    simp [h, childInstance, pendingTok, locL, locM, psubst, psubstList_eq_map]
  have hTell : NameLaws (psubst h (atLoc firstPattern locL)) (psubst h (atLoc secondPattern locL)) := by
    have left : psubst h (atLoc firstPattern locL) = atLoc (psubst σ₀ t) (psubst σ₀ l) := by
      simp [h, childInstance, atLoc, firstPattern, locL, psubst, psubstList_eq_map]
    have right : psubst h (atLoc secondPattern locL) = atLoc (psubst σ₀ u) (psubst σ₀ l) := by
      simp [h, childInstance, atLoc, secondPattern, locL, psubst, psubstList_eq_map]
    rw [left, right]
    exact (ReflLocated.locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨unifies, NameLaws.refl _⟩
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (commChildAt ρ first second token made₁ made₂ madeTok) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun e member => by
      obtain rfl := List.mem_singleton.mp member
      exact hTell)
    (fun o member => by
      simp only [commChildAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact present.1
      · exact present.2.1
      · exact present.2.2)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      simp only [commChildAt, commChild, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · show NameLaws (psubst h (atLoc (pFor firstPattern channelUnknown firstBody) locL)) (psubst σ₀ (label first))
        rw [hFirst]
        exact (readsFirst σ₀ known).symm
      · show NameLaws (psubst h (atLoc (pFor secondPattern channelUnknown secondBody) locL))
          (psubst σ₀ (label second))
        rw [hSecond]
        exact (readsSecond σ₀ known).symm
      · show NameLaws (psubst h (pendingTok locL locM)) (psubst σ₀ (label token))
        rw [hToken]
        exact (readsToken σ₀ known).symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly, ⟨distinct, madeDistinct, rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [commChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact present.1
    · exact present.2.1
    · exact present.2.2
  · intro o member
    simp [commChildAt, Selection.commit] at member
  · simp [commChildAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [commChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact fresh.1
    · exact fresh.2.1
    · exact fresh.2.2

/-- **The child takes its one step when it can**: in the first phase, with a redex at `l` (two rows that read
as inputs at `l` on one channel, unifiable at a solution) beside the token, the located COMM is admitted at
every fresh opening, it is a source step at `l`, and its result is in the second phase. -/
theorem child_steps_once {m x p : Pattern} (label : O → Pattern) (C : Configuration Pattern O) {q : O}
    (phase : PendingPhase (childLoc m x p) m label C q) (t u channel K₁ K₂ : Pattern)
    (first second made₁ made₂ madeTok : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t channel K₁) (childLoc m x p))))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u channel K₂) (childLoc m x p))))
    (ground : pvars (pendingTok (childLoc m x p) m) = [])
    (distinct : [first, second, q].Nodup) (madeDistinct : [made₁, made₂, madeTok].Nodup)
    (present : first ∈ C.present ∧ second ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ made₂ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commChildAt ρ first second q made₁ made₂ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (commChildAt ρ first second q made₁ made₂ madeTok) ∧
      StepAt (childLoc m x p) label C (commChildAt ρ first second q made₁ made₂ madeTok) ∧
      ∃ d, DonePhase (childLoc m x p) m (res label C (commChildAt ρ first second q made₁ made₂ madeTok)).label
        (resConf label C (commChildAt ρ first second q made₁ made₂ madeTok)) d := by
  have admitted := child_comm_admitted label C t u channel K₁ K₂ (childLoc m x p) m first second q made₁ made₂
    madeTok readsFirst readsSecond
    (fun σ solved => by rw [psubst_of_pvars_nil σ _ ground]; exact phase.reads σ solved)
    distinct madeDistinct ⟨present.1, present.2, phase.present⟩ fresh known unifies opensFreshly
  obtain ⟨σ, solved⟩ := solution_of_admitted admitted
  have zipped : (pendingTok locL locM, q) ∈ (commChildAt ρ first second q made₁ made₂ madeTok).rule.body.take.zip
      (commChildAt ρ first second q made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, commChild]
  have loc := (pending_reading ((take_reads _ solved zipped).trans (phase.reads σ (info_known _ solved)))).1
  have step : StepAt (childLoc m x p) label C (commChildAt ρ first second q made₁ made₂ madeTok) :=
    ⟨.inl rfl, σ, solved, loc⟩
  rcases pending_phase_step phase _ admitted with ⟨notStep, -⟩ | ⟨-, done⟩
  · exact absurd step notStep
  · exact ⟨admitted, step, done⟩

theorem closeChild_mem : closeChild ∈ located :=
  Or.inl (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))))))

/-- The inner close at a child: take the reflection `reflection`, the grandchild's token `innerToken` and the
token `token`; make the row `made₁` and the token `madeTok`. -/
def closeChildAt (ρ : PSubst) (reflection innerToken token made₁ madeTok : O) : Firing O QNE located PUnit.unit :=
  ⟨closeChild, closeChild_mem, PUnit.unit, ρ, ⟨[reflection, innerToken, token], [], [made₁, madeTok]⟩, []⟩

/-- The instance of the inner close's unknowns. -/
def innerCloseInstance (x p c l m : Pattern) : PSubst := fun v =>
  if v = "X" then some x else if v = "P" then some p else if v = "C" then some c else if v = "L" then some l
  else if v = "M" then some m else none

theorem psubst_pReflect (σ : PSubst) (x p : Pattern) : psubst σ (pReflect x p) = pReflect (psubst σ x) (psubst σ p) := by
  simp only [pReflect, psubst, psubstList_eq_map, List.map_cons, List.map_nil]

/-- A reflection modulo the name laws is a reflection, part by part. -/
theorem nameLaws_pReflect_iff {x p x' p' : Pattern} :
    NameLaws (pReflect x p) (pReflect x' p') ↔ NameLaws x x' ∧ NameLaws p p' := by
  rw [pReflect, pReflect, nameLaws_apply_iff (by unfold IsQuote; decide)]
  simp

/-- **The inner close is admitted when the grandchild is packed**: at the child `l` of `m`, a row that reads as
the reflection `x'?(p') @ l`, a row that reads as the grandchild's token `Done(Child(l, x', p'), l, c)` and a row
that reads as `Pending(l, m)`, at every solution of the knowledge; no row that reads as a row at the grandchild at
any solution; distinct taken and made identities, fresh made identities, a solution of the knowledge, and a fresh
opening. -/
theorem child_close_admitted (label : O → Pattern) (C : Configuration Pattern O) (x' p' c l m : Pattern)
    (reflection innerToken token made₁ madeTok : O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x' p') l)))
    (readsInner : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label innerToken)) (psubst σ (doneTok (childLoc l x' p') l c)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m)))
    (packed : ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations → ∀ y : Pattern,
      ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc l x' p'))))
    (distinct : [reflection, innerToken, token].Nodup) (madeDistinct : [made₁, madeTok].Nodup)
    (present : reflection ∈ C.present ∧ innerToken ∈ C.present ∧ token ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (closeChildAt ρ reflection innerToken token made₁ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (closeChildAt ρ reflection innerToken token made₁ madeTok) := by
  let h : PSubst := innerCloseInstance (psubst σ₀ x') (psubst σ₀ p') (psubst σ₀ c) (psubst σ₀ l) (psubst σ₀ m)
  have hReflection : psubst h (atLoc (pReflect channelUnknown reflP) locL) = psubst σ₀ (atLoc (pReflect x' p') l) := by
    simp [h, innerCloseInstance, atLoc, pReflect, channelUnknown, reflP, locL, psubst, psubstList_eq_map]
  have hInner : psubst h (doneTok (childLoc locL channelUnknown reflP) locL accC) =
      psubst σ₀ (doneTok (childLoc l x' p') l c) := by
    simp [h, innerCloseInstance, doneTok, childLoc, channelUnknown, reflP, locL, accC, psubst, psubstList_eq_map]
  have hToken : psubst h (pendingTok locL locM) = psubst σ₀ (pendingTok l m) := by
    simp [h, innerCloseInstance, pendingTok, locL, locM, psubst, psubstList_eq_map]
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (closeChildAt ρ reflection innerToken token made₁ madeTok) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun o member => by
      simp only [closeChildAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact present.1
      · exact present.2.1
      · exact present.2.2)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      simp only [closeChildAt, closeChild, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · show NameLaws (psubst h (atLoc (pReflect channelUnknown reflP) locL)) (psubst σ₀ (label reflection))
        rw [hReflection]
        exact (readsReflection σ₀ known).symm
      · show NameLaws (psubst h (doneTok (childLoc locL channelUnknown reflP) locL accC))
          (psubst σ₀ (label innerToken))
        rw [hInner]
        exact (readsInner σ₀ known).symm
      · show NameLaws (psubst h (pendingTok locL locM)) (psubst σ₀ (label token))
        rw [hToken]
        exact (readsToken σ₀ known).symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly, ⟨distinct, madeDistinct, rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, ?_, fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [closeChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact present.1
    · exact present.2.1
    · exact present.2.2
  · intro o member
    simp [closeChildAt, Selection.commit] at member
  · simp [closeChildAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [closeChildAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh.1
    · exact fresh.2
  · intro check member _ σ solvedσ
    have only : ((closeChildAt ρ reflection innerToken token made₁ madeTok).opened QN).checks =
        [.predicate .none (psubst ρ (atLoc anyY (childLoc locL channelUnknown reflP)))] := rfl
    rw [only, List.mem_singleton] at member
    subst member
    intro o presentO same
    rw [OneFrame.row_eq] at same
    have knownσ := info_known _ solvedσ
    have zipped : (atLoc (pReflect channelUnknown reflP) locL, reflection) ∈
        (closeChildAt ρ reflection innerToken token made₁ madeTok).rule.body.take.zip
          (closeChildAt ρ reflection innerToken token made₁ madeTok).selection.taken := by
      simp [closeChildAt, closeChild]
    have read := (take_reads _ solvedσ zipped).trans (readsReflection σ knownσ)
    rw [psubst_atLoc_any, psubst_atLoc_any, psubst_atLoc_any, psubst_pReflect, psubst_pReflect,
      psubst_pReflect] at read
    obtain ⟨parts, loc⟩ := (ReflLocated.locatedFrame_name.atLoc_iff _ _ _ _).mp read
    obtain ⟨chan, proc⟩ := nameLaws_pReflect_iff.mp parts
    change NameLaws (psubst σ (psubst ρ (atLoc anyY (childLoc locL channelUnknown reflP)))) (psubst σ (label o))
      at same
    rw [psubst_atLoc_any, psubst_atLoc_any, psubst_childLoc, psubst_childLoc] at same
    apply packed o presentO σ knownσ (psubst σ (psubst ρ anyY))
    refine same.symm.trans ((ReflLocated.locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨NameLaws.refl _, ?_⟩)
    rw [psubst_childLoc]
    exact nameLaws_childLoc_iff.mpr ⟨loc, chan, proc⟩

/-- **The child takes its one step by an inner close when it can**: in the first phase, with a reflection
`x'?(p') @ l`, the grandchild's token `Done(Child(l, x', p'), l, c)` and no row left at the grandchild, the inner
close is admitted at every fresh opening, it is a source step at `l`, and its result is in the second phase. -/
theorem child_closes_once {m x p : Pattern} (label : O → Pattern) (C : Configuration Pattern O) {q : O}
    (phase : PendingPhase (childLoc m x p) m label C q) (x' p' c : Pattern) (reflection innerToken made₁ madeTok : O)
    (readsReflection : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label reflection)) (psubst σ (atLoc (pReflect x' p') (childLoc m x p))))
    (readsInner : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label innerToken))
        (psubst σ (doneTok (childLoc (childLoc m x p) x' p') (childLoc m x p) c)))
    (packed : ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations → ∀ y : Pattern,
      ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ (childLoc (childLoc m x p) x' p'))))
    (ground : pvars (pendingTok (childLoc m x p) m) = [])
    (distinct : [reflection, innerToken, q].Nodup) (madeDistinct : [made₁, madeTok].Nodup)
    (present : reflection ∈ C.present ∧ innerToken ∈ C.present)
    (fresh : made₁ ∉ C.present ∧ madeTok ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (closeChildAt ρ reflection innerToken q made₁ madeTok).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (closeChildAt ρ reflection innerToken q made₁ madeTok) ∧
      StepAt (childLoc m x p) label C (closeChildAt ρ reflection innerToken q made₁ madeTok) ∧
      ∃ d, DonePhase (childLoc m x p) m (res label C (closeChildAt ρ reflection innerToken q made₁ madeTok)).label
        (resConf label C (closeChildAt ρ reflection innerToken q made₁ madeTok)) d := by
  have admitted := child_close_admitted label C x' p' c (childLoc m x p) m reflection innerToken q made₁ madeTok
    readsReflection readsInner (fun σ solved => by rw [psubst_of_pvars_nil σ _ ground]; exact phase.reads σ solved)
    packed distinct madeDistinct ⟨present.1, present.2, phase.present⟩ fresh known opensFreshly
  obtain ⟨σ, solved⟩ := solution_of_admitted admitted
  have zipped : (pendingTok locL locM, q) ∈ (closeChildAt ρ reflection innerToken q made₁ madeTok).rule.body.take.zip
      (closeChildAt ρ reflection innerToken q made₁ madeTok).selection.taken := by
    simp [closeChildAt, closeChild]
  have loc := (pending_reading ((take_reads _ solved zipped).trans (phase.reads σ (info_known _ solved)))).1
  have step : StepAt (childLoc m x p) label C (closeChildAt ρ reflection innerToken q made₁ madeTok) :=
    ⟨.inr rfl, σ, solved, loc⟩
  rcases pending_phase_step phase _ admitted with ⟨notStep, -⟩ | ⟨-, done⟩
  · exact absurd step notStep
  · exact ⟨admitted, step, done⟩

end Progress

/-! ## The phases are inhabited -/

/-- A state holding only the token `Pending(l, m)`. -/
def pendingOnly (l m : Pattern) : ℕ → Pattern := fun _ => pendingTok l m

/-- A state holding only the token `Done(l, m, 0)`. -/
def doneOnly (l m : Pattern) : ℕ → Pattern := fun _ => doneTok l m pZero

theorem pendingOnly_phase (m x p : Pattern) (ground : pvars (pendingTok (childLoc m x p) m) = []) :
    PendingPhase (childLoc m x p) m (pendingOnly (childLoc m x p) m) ⟨[], {0}⟩ 0 := by
  refine ⟨by simp, fun σ _ => ?_, fun o present _ => by simpa using present, ?_⟩
  · rw [pendingOnly, psubst_of_pvars_nil σ _ ground]
    exact NameLaws.refl _
  · rintro o - ⟨σ, -, m', c, same⟩
    rw [pendingOnly, psubst_of_pvars_nil σ _ ground] at same
    exact absurd (nameLaws_heads same) (by decide)

theorem doneOnly_phase (m x p : Pattern) (ground : pvars (doneTok (childLoc m x p) m pZero) = []) :
    DonePhase (childLoc m x p) m (doneOnly (childLoc m x p) m) ⟨[], {0}⟩ 0 := by
  refine ⟨by simp, fun σ _ => ⟨pZero, ?_⟩, ?_⟩
  · rw [doneOnly, psubst_of_pvars_nil σ _ ground]
    exact NameLaws.refl _
  · rintro o - ⟨σ, -, m', same⟩
    rw [doneOnly, psubst_of_pvars_nil σ _ ground] at same
    exact absurd (nameLaws_heads same) (by decide)

/-! ## Rigid child routing on the located step

The term-shaped location is not a capability. The selected occurrences
also have physical routing tags. A child's first pending occurrence
supplies a private key; later token replacements carry that same key,
parent and opening occurrence. The equations act on the underlying
terms, not on any of these three identities.
-/

namespace Ownership

open LocatedSubstitution.Authority (Ledger Ticket)

/-- The tag selects a routing clause for an existing rule; it does not
select a different evaluator or a different term-level match. -/
inductive Operation where
  | rootComm | rootHeat | rootClear
  | openRoot | openChild | childComm | childHeat | cool | closeRoot | closeChild

def Operation.rule : Operation → Rule Tm
  | .rootComm => atRule rootLoc commRule
  | .rootHeat => atRule rootLoc heatRule
  | .rootClear => atRule rootLoc clearRule
  | .openRoot => ReflLocated.openRoot
  | .openChild => ReflLocated.openChild
  | .childComm => commChild
  | .childHeat => heatChild
  | .cool => ReflLocated.cool
  | .closeRoot => ReflLocated.closeRoot
  | .closeChild => ReflLocated.closeChild

theorem Operation.exists_of_member {rule : Rule Tm} (member : rule ∈ located) :
    ∃ op : Operation, rule = op.rule := by
  rcases located_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.rootComm, rfl⟩
  · exact ⟨.rootHeat, rfl⟩
  · exact ⟨.rootClear, rfl⟩
  · exact ⟨.childComm, rfl⟩
  · exact ⟨.childHeat, rfl⟩
  · exact ⟨.cool, rfl⟩
  · exact ⟨.closeRoot, rfl⟩
  · exact ⟨.closeChild, rfl⟩
  · exact ⟨.openRoot, rfl⟩
  · exact ⟨.openChild, rfl⟩

inductive Phase where
  | pending | done
  deriving DecidableEq

abbrev Mark (O : Type*) := LocatedSubstitution.Authority.Mark O Phase

/-- The authored label form for a physical mark. This does not
identify two physical regions just because their terms compare equal. -/
def MarkForm {O : Type*} : Mark O → Pattern → Prop
  | .cell none, label => ∃ body, label = atLoc body rootLoc
  | .cell (some _), label => ∃ body place, label = atLoc body place
  | .control _ .pending, label => ∃ place parent, label = pendingTok place parent
  | .control _ .done, label => ∃ place parent acc, label = doneTok place parent acc

theorem MarkForm.instantiate {O : Type*} {mark : Mark O} {label : Pattern}
    (form : MarkForm mark label) (σ : PSubst) : MarkForm mark (psubst σ label) := by
  cases mark with
  | cell place =>
    cases place with
    | none =>
      obtain ⟨body, rfl⟩ := form
      exact ⟨psubst σ body, by rw [psubst_atLoc_any, ReflLocated.psubst_rootLoc]⟩
    | some _ =>
      obtain ⟨body, l, rfl⟩ := form
      exact ⟨psubst σ body, psubst σ l, psubst_atLoc_any σ body l⟩
  | control ticket phase =>
    cases phase with
    | pending =>
      obtain ⟨l, m, rfl⟩ := form
      exact ⟨psubst σ l, psubst σ m, psubst_pendingTok σ l m⟩
    | done =>
      obtain ⟨l, m, a, rfl⟩ := form
      exact ⟨psubst σ l, psubst σ m, psubst σ a, psubst_doneTok σ l m a⟩

theorem MarkForm.control_not_row {O : Type*} {ticket : Ticket O} {phase : Phase} {label : Pattern}
    (form : MarkForm (.control ticket phase) label) (body loc : Pattern) :
    ¬ NameLaws label (atLoc body loc) := by
  cases phase with
  | pending =>
    obtain ⟨_, _, rfl⟩ := form
    exact fun same => absurd (nameLaws_heads same) (by decide)
  | done =>
    obtain ⟨_, _, _, rfl⟩ := form
    exact fun same => absurd (nameLaws_heads same) (by decide)

structure Store (O : Type*) where
  raw : State Tm O
  ledger : Ledger O Phase
  authored : O → Option Pattern

abbrev Store.plain {O : Type*} (raw : State Tm O) (ledger : Ledger O Phase) : Store O :=
  ⟨raw, ledger, fun _ => none⟩

abbrev Store.route {O : Type*} (s : Store O) := s.ledger.mark
abbrev Store.issued {O : Type*} (s : Store O) := s.ledger.issued

/-- Every live mark is backed by a label of its authored kind. -/
def LabelForms {O : Type*} (s : Store O) : Prop :=
  ∀ ⦃slot mark⦄, s.route slot = some mark → MarkForm mark (s.raw.label slot)

structure Candidate {O : Type*} (s : Store O) where
  raw : Firing O QNE located s.raw.frame
  op : Operation
  describes : raw.rule = op.rule

variable {O : Type*} [DecidableEq O]

/-- An initial root store has no private addresses or return tickets. -/
def start (s : State Tm O) : Store O :=
  Store.plain s (Ledger.root s.present)

/-- Initialize immutable source syntax for the live root occurrences.
An initial slot not present in the root store is not published. -/
def startAuthored (s : State Tm O) (syntaxAt : O → Pattern) : Store O :=
  ⟨s, Ledger.root s.present, fun slot => if slot ∈ s.present then some (syntaxAt slot) else none⟩

theorem start_labelForms (s : State Tm O)
    (root : ∀ slot ∈ s.present, ∃ body, s.label slot = atLoc body rootLoc) :
    LabelForms (start s) := by
  intro slot mark observed
  by_cases present : slot ∈ s.present
  · simp [Store.route, start, Ledger.root, present] at observed
    rw [← observed]
    exact root slot present
  · simp [Store.route, start, Ledger.root, present] at observed

def Store.reserved (s : Store O) (owner : O) : Finset O :=
  s.raw.present.filter fun o =>
    ((s.route o).bind LocatedSubstitution.Authority.Mark.ticket).map Ticket.owner = some owner

def Store.childRows (s : Store O) (key : O) : Finset O :=
  s.raw.present.filter fun o => s.route o = some (.cell (some key))

def Store.nested (s : Store O) (key : O) : Finset O :=
  s.raw.present.filter fun o =>
    ((s.route o).bind LocatedSubstitution.Authority.Mark.ticket).map Ticket.parent = some (some key)

/-- A mark belongs to the region as a row, its own ticket, or the
ticket of an outstanding immediate child. -/
def AtRegion (key : O) : Mark O → Prop
  | .cell place => place = some key
  | .control t _ => t.key = key ∨ t.parent = some key

instance (key : O) (tag : Mark O) : Decidable (AtRegion key tag) := by
  cases tag <;> unfold AtRegion <;> infer_instance

def Store.region (s : Store O) (key : O) : Finset O :=
  s.raw.present.filter fun slot => (s.route slot).any fun tag => decide (AtRegion key tag)

theorem mem_region_iff {s : Store O} {key slot : O} :
    slot ∈ s.region key ↔
      slot ∈ s.raw.present ∧ ∃ tag, s.route slot = some tag ∧ AtRegion key tag := by
  simp only [Store.region, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  cases s.route slot <;> simp

/-- For a row absence check the full region and its row bucket agree.
Ticket labels, including those of nested children, cannot count as
data rows under any symbolic solution. -/
theorem region_row_absence_iff {s : Store O} (formed : LabelForms s) (key : O)
    (σ : PSubst) (body loc : Pattern) :
    (∀ slot ∈ s.childRows key, ¬ NameLaws (psubst σ (atLoc body loc)) (psubst σ (s.raw.label slot))) ↔
    ∀ slot ∈ s.region key, ¬ NameLaws (psubst σ (atLoc body loc)) (psubst σ (s.raw.label slot)) := by
  constructor
  · intro absent slot seen matchRow
    obtain ⟨live, mark, tagged, region⟩ := mem_region_iff.mp seen
    cases mark with
    | cell place =>
      change place = some key at region
      subst place
      exact absent slot (Finset.mem_filter.mpr ⟨live, tagged⟩) matchRow
    | control t phase =>
      rw [psubst_atLoc_any] at matchRow
      exact (MarkForm.instantiate (formed tagged) σ).control_not_row _ _ matchRow.symm
  · intro absent slot seen
    obtain ⟨live, tagged⟩ := Finset.mem_filter.mp seen
    exact absent slot (mem_region_iff.mpr ⟨live, .cell (some key), tagged, rfl⟩)

/-- A cell reserved by an outstanding child is no longer available
to other firings. The exact owner close uses a different check. -/
def Store.available (s : Store O) (place : Option O) (o : O) : Prop :=
  s.route o = some (.cell place) ∧ s.reserved o = ∅

instance (s : Store O) (place : Option O) (o : O) : Decidable (s.available place o) := by
  unfold Store.available
  infer_instance

private def controlAt (s : Store O) (slot : O) (phase : Phase) : Option (Ticket O) :=
  match s.route slot with
  | some (.control t found) => if found = phase then some t else none
  | _ => none

omit [DecidableEq O] in
private theorem control_at_some {s : Store O} {slot : O} {phase : Phase} {t : Ticket O} :
    controlAt s slot phase = some t ↔ s.route slot = some (.control t phase) := by
  cases actual : s.route slot with
  | none => simp [controlAt, actual]
  | some tag =>
    cases tag with
    | cell place => simp [controlAt, actual]
    | control stamp found =>
      by_cases equal : found = phase
      · subst found
        simp [controlAt, actual]
      · simp [controlAt, actual, equal]

private def checked {A : Type*} (gate : Prop) [Decidable gate] (out : A) : Option A :=
  if gate then some out else none

private theorem checked_some {A : Type*} {gate : Prop} [Decidable gate] {built out : A} :
    checked gate built = some out ↔ gate ∧ built = out := by
  by_cases enabled : gate <;> simp [checked, enabled]

/-- Compute the route tags, in made-occurrence order. A checked schema
cannot route using a term-equality witness in place of a selected key.
This is the physical part of admission, independent of the guard view. -/
def routes (s : Store O) : Operation → List O → List O → (made : List O) →
    Option (Vector (Mark O) made.length)
  | .rootComm, [a, b], [], [_, _] =>
      checked (s.available none a ∧ s.available none b) #v[.cell none, .cell none]
  | .rootHeat, [a], [], [_, _] =>
      checked (s.available none a) #v[.cell none, .cell none]
  | .rootClear, [a], [], [] =>
      checked (s.available none a) #v[]
  | .openRoot, [], [owner], [_, child] =>
      checked (s.available none owner) #v[.cell (some child), .control ⟨child, owner, none⟩ .pending]
  | .openChild, [], [owner, parent], [_, child] => (controlAt s parent .pending).bind fun p =>
      checked (s.available (some p.key) owner ∧ s.nested p.key = ∅)
        #v[.cell (some child), .control ⟨child, owner, some p.key⟩ .pending]
  | .childComm, [a, b, token], [], [_, _, _] => (controlAt s token .pending).bind fun t =>
      let home := .cell (some t.key)
      checked (s.available (some t.key) a ∧ s.available (some t.key) b ∧ s.nested t.key = ∅)
        #v[home, home, .control t .done]
  | .childHeat, [a], [token], [_, _] => (controlAt s token .pending).bind fun t =>
      let home := .cell (some t.key)
      checked (s.available (some t.key) a) #v[home, home]
  | .cool, [token, a], [], [_] => (controlAt s token .done).bind fun t =>
      checked (s.available (some t.key) a) #v[.control t .done]
  | .closeRoot, [owner, token], [], [_] => (controlAt s token .done).bind fun t =>
      checked (t.owner = owner ∧ t.parent = none ∧ s.route owner = some (.cell none) ∧
        s.reserved owner = {token} ∧ s.childRows t.key = ∅ ∧ s.nested t.key = ∅) #v[.cell none]
  | .closeChild, [owner, token, parent], [], [_, _] => (controlAt s token .done).bind fun t =>
      (controlAt s parent .pending).bind fun p =>
        checked (t.owner = owner ∧ t.parent = some p.key ∧ s.route owner = some (.cell (some p.key)) ∧
          s.reserved owner = {token} ∧ s.childRows t.key = ∅ ∧
          s.nested t.key = ∅ ∧ s.nested p.key = {token}) #v[.cell (some p.key), .control p .done]
  | _, _, _, _ => none

private theorem routes_output_forms {s : Store O} {op : Operation} {taken read made : List O}
    {out : Vector (Mark O) made.length} (plan : routes s op taken read made = some out) :
    List.Forall₂ MarkForm out.toList op.rule.body.produce := by
  unfold routes at plan
  split at plan <;> simp only [checked_some, Option.bind_eq_some_iff, control_at_some, reduceCtorEq] at plan
  case h_1 =>
    obtain ⟨_, rfl⟩ := plan
    exact .cons ⟨_, rfl⟩ (.cons ⟨_, rfl⟩ .nil)
  case h_2 =>
    obtain ⟨_, rfl⟩ := plan
    exact .cons ⟨_, rfl⟩ (.cons ⟨_, rfl⟩ .nil)
  case h_3 =>
    obtain ⟨_, rfl⟩ := plan
    exact .nil
  case h_4 =>
    obtain ⟨_, rfl⟩ := plan
    exact .cons ⟨_, _, rfl⟩ (.cons ⟨_, _, rfl⟩ .nil)
  case h_5 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    exact .cons ⟨_, _, rfl⟩ (.cons ⟨_, _, rfl⟩ .nil)
  case h_6 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    exact .cons ⟨_, _, rfl⟩ (.cons ⟨_, _, rfl⟩ (.cons ⟨_, _, _, rfl⟩ .nil))
  case h_7 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    exact .cons ⟨_, _, rfl⟩ (.cons ⟨_, _, rfl⟩ .nil)
  case h_8 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    exact .cons ⟨_, _, _, rfl⟩ .nil
  case h_9 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    exact .cons ⟨_, rfl⟩ .nil
  case h_10 =>
    obtain ⟨_, _, _, _, _, rfl⟩ := plan
    exact .cons ⟨_, _, rfl⟩ (.cons ⟨_, _, _, rfl⟩ .nil)

omit [DecidableEq O] in
private theorem paired_mark_form {marks : List (Mark O)} {labels : List Pattern}
    (forms : List.Forall₂ MarkForm marks labels) {slots : List O} {slot : O} {mark : Mark O}
    (tagged : (slot, mark) ∈ slots.zip marks) :
    ∃ label, (slot, label) ∈ slots.zip labels ∧ MarkForm mark label := by
  induction forms generalizing slots with
  | nil => simp at tagged
  | @cons tag label _ _ head _ ih =>
    cases slots with
    | nil => simp at tagged
    | cons k slots =>
      simp only [List.zip_cons_cons, List.mem_cons] at tagged
      rcases tagged with same | tagged
      · cases same
        exact ⟨label, List.mem_cons_self, head⟩
      · obtain ⟨later, seen, kind⟩ := ih tagged
        exact ⟨later, List.mem_cons_of_mem _ seen, kind⟩

/-- Routing sees the live occurrences and their ledger, never term
labels, frame substitutions or accumulated equations. -/
theorem routes_eq_of_footprint {s t : Store O} (live : s.raw.present = t.raw.present)
    (tags : s.ledger = t.ledger) (op : Operation) (taken read made : List O) :
    routes s op taken read made = routes t op taken read made := by
  cases s with
  | mk left old =>
    cases t with
    | mk right new =>
      cases left with
      | mk lf lk lp ll =>
        cases right with
        | mk rf rk rp rl =>
          dsimp only at live tags
          subst rp
          subst new
          unfold routes
          split <;> rfl

def Candidate.plan {s : Store O} (f : Candidate s) : Option (Vector (Mark O) f.raw.selection.made.length) :=
  routes s f.op f.raw.selection.taken f.raw.selection.read f.raw.selection.made

def Candidate.information {s : Store O} (f : Candidate s) (tells : Option (EquationStore Pattern)) :
    EquationStore Pattern :=
  match tells with
  | none => f.raw.information QN s.raw
  | some eqs => f.raw.information QN s.raw ++ eqs

omit [DecidableEq O] in
theorem Candidate.models_information {s : Store O} (f : Candidate s) {σ : PSubst}
    (tells : Option (EquationStore Pattern)) :
    nameAction.Models σ (f.information tells) ↔
      nameAction.Models σ (f.raw.information QN s.raw) ∧ nameAction.Models σ (tells.getD []) := by
  cases tells with
  | none => simp [Candidate.information]
  | some eqs => exact nameAction.models_append σ (f.raw.information QN s.raw) eqs

def update {s : Store O} (f : Candidate s) (route : Vector (Mark O) f.raw.selection.made.length)
    (tells : Option (EquationStore Pattern) := none)
    (origins : Option (Vector (Option Pattern) f.raw.selection.made.length) := none) : Store O :=
  ⟨{f.raw.result QN s.raw with knowledge := f.information tells},
    s.ledger.advance s.raw.present f.raw.selection route,
    fun slot => match origins with
      | none => none
      | some published =>
        if slot ∈ (f.raw.result QN s.raw).present then
          ((f.raw.selection.made.zip published.toList).lookup slot).getD (s.authored slot)
        else none⟩

/-- The old symbolic comparison uses the whole store. The scoped
guard policy asks absence of the selected or newly allocated child. -/
inductive GuardPolicy where
  | whole | physical

private def childCheckRows (s : Store O) : Operation → List O → List O → List O → Finset O
  | .openRoot, [], [_], [_, key] => s.region key
  | .openChild, [], [_, _], [_, key] => s.region key
  | .closeRoot, [_, token], [], [_] =>
      ((controlAt s token .done).map fun t => s.childRows t.key).getD s.raw.present
  | .closeChild, [_, token, _], [], [_, _] =>
      ((controlAt s token .done).map fun t => s.childRows t.key).getD s.raw.present
  | _, _, _, _ => s.raw.present

def Candidate.guardRows {s : Store O} (f : Candidate s) : GuardPolicy → Finset O
  | .whole => s.raw.present
  | .physical => childCheckRows s f.op f.raw.selection.taken f.raw.selection.read f.raw.selection.made

private theorem close_guard_subset (s : Store O) (token : O) :
    ((controlAt s token .done).map fun t => s.childRows t.key).getD s.raw.present ⊆ s.raw.present := by
  cases controlAt s token .done with
  | none => exact Finset.Subset.refl _
  | some _ => exact Finset.filter_subset _ _

private theorem child_checks_subset (s : Store O) (op : Operation) (taken read made : List O) :
    childCheckRows s op taken read made ⊆ s.raw.present := by
  unfold childCheckRows
  split <;> first
    | exact Finset.Subset.refl _
    | exact Finset.filter_subset _ _
    | exact close_guard_subset s _

theorem Candidate.guardRows_subset {s : Store O} (f : Candidate s) (policy : GuardPolicy) :
    f.guardRows policy ⊆ s.raw.present := by
  cases policy
  · exact Finset.Subset.refl _
  · exact child_checks_subset s _ _ _ _

private theorem Operation.absence_checks (op : Operation) :
    ∀ c ∈ op.rule.body.checks, ∃ pattern, c = .predicate .none pattern := by
  cases op <;> intro c member <;>
    simp [Operation.rule, atRule, RuleInstance.map, commRule, heatRule, clearRule,
      ReflLocated.openRoot, ReflLocated.openChild, ReflLocated.commChild, ReflLocated.heatChild,
      ReflLocated.cool, ReflLocated.closeRoot, ReflLocated.closeChild] at member
  all_goals
    first
    | subst c; exact ⟨_, rfl⟩
    | rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

omit [DecidableEq O] in
private theorem Candidate.opened_absence_checks {s : Store O} (f : Candidate s)
    {c : Check (Tm (QNE.target f.raw.ext))} (member : c ∈ (f.raw.opened QN).checks) :
    ∃ pattern, c = .predicate .none pattern := by
  have authored : ∀ c ∈ f.raw.rule.body.checks, ∃ pattern, c = .predicate .none pattern := by
    rw [f.describes]
    exact f.op.absence_checks
  change c ∈ f.raw.rule.body.checks.map (Check.map (QN.act f.raw.opening)) at member
  obtain ⟨original, appears, rfl⟩ := List.mem_map.mp member
  obtain ⟨pattern, rfl⟩ := authored original appears
  exact ⟨_, rfl⟩

omit [DecidableEq O] in
private theorem Candidate.collect_empty {s : Store O} (f : Candidate s) :
    f.raw.rule.collect = [] := by
  rw [f.describes]
  cases f.op <;> rfl

/-- Only the domain of the existing guard interpreter changes.
Matching, freshness, shapes, and all the equations used by the solver
still refer to the actual store. -/
def Candidate.SymbolicAdmits {s : Store O} (f : Candidate s) (policy : GuardPolicy)
    (tells : Option (EquationStore Pattern) := none) : Prop :=
  f.raw.Shapes QN s.raw ∧ Enabled (fun _ : O => ()) s.raw.present (f.raw.selection.commit (T := Unit)) ∧
    QN.Solvable (a := QNE.target f.raw.ext) (f.information tells) ∧
    QN.Entails (a := QNE.target f.raw.ext) (f.information tells) fun b σ =>
      f.raw.Holds QN {s.raw with present := f.guardRows policy} (b := b) σ

/-- Actual located firings with a declared guard view and optional
commit equations at the target frame. No extra equations means exactly
the original located step. -/
def step (policy : GuardPolicy := .whole)
    (tells : {s : Store O} → Candidate s → Option (EquationStore Pattern) := fun _ => none)
    (origins : {s : Store O} → (f : Candidate s) →
      Option (Vector (Option Pattern) f.raw.selection.made.length) := fun _ => none) :
    Interface.Step.Standard QN O (Store O) (fun s => Candidate s) where
  frame s := s.raw.frame
  knowledge s := s.raw.knowledge
  present s := s.raw.present
  selection f := f.raw.selection
  target f := QNE.target f.raw.ext
  extension f := QNE.weaken f.raw.ext
  information f := f.information (tells f)
  transported {s} f e member := by
    have old := (RuleSyntax.step QN O QNE located).transported (s := s.raw) f.raw e member
    cases tells f with
    | none => exact old
    | some extra => exact List.mem_append_left extra old
  Shapes {s} f := f.raw.Shapes QN s.raw ∧ f.plan.isSome
  Holds {s} f b σ :=
    f.raw.Holds QN {s.raw with present := f.guardRows policy} (b := b) σ ∧ s.ledger.Fresh f.raw.selection
  Admits {s} f := f.SymbolicAdmits policy (tells f) ∧ f.plan.isSome ∧ s.ledger.Fresh f.raw.selection
  admits_iff := by
    intro s f
    constructor
    · rintro ⟨⟨shape, enabled, consistent, solved⟩, planned, fresh⟩
      exact ⟨⟨shape, planned⟩, enabled, consistent, fun b σ model => ⟨solved b σ model, fresh⟩⟩
    · rintro ⟨⟨shape, planned⟩, enabled, consistent, solved⟩
      obtain ⟨b, σ, model⟩ := consistent
      exact ⟨⟨shape, enabled, ⟨b, σ, model⟩, fun c τ h => (solved c τ h).1⟩, planned,
        (solved b σ model).2⟩
  preparedResult f h := update f (f.plan.get h.1.2) (tells f) (origins f)
  present_preparedResult _ _ := rfl
  preparedSettle f _ := QN.id (QNE.target f.raw.ext)
  knowledge_preparedResult f _ :=
    (Interface.Frames.applyStore_id (X := QN) (f.information (tells f))).symm

/-- Extra tells preserve every old guard that was already entailed.
Admitting the stronger commit additionally requires a solution of its
actual information. -/
theorem admits_with_tells (policy : GuardPolicy)
    (tells : {s : Store O} → Candidate s → Option (EquationStore Pattern))
    {s : Store O} {f : Candidate s} (before : (step (O := O) policy).Admits f)
    (consistent : QN.Solvable (a := QNE.target f.raw.ext) (f.information (tells f))) :
    (step policy tells).Admits f := by
  obtain ⟨⟨shape, enabled, _, guards⟩, planned, fresh⟩ := before
  exact ⟨⟨shape, enabled, consistent,
    fun b σ solved => guards b σ ((f.models_information (tells f)).mp solved).1⟩, planned, fresh⟩

theorem admits_without_comm_tells (policy : GuardPolicy)
    (tells : {s : Store O} → Candidate s → Option (EquationStore Pattern))
    {s : Store O} {f : Candidate s}
    (comm : f.op = .rootComm ∨ f.op = .childComm) (after : (step policy tells).Admits f) :
    (step (O := O) policy).Admits f := by
  obtain ⟨⟨shape, enabled, ⟨b, σ, solved⟩, _⟩, planned, fresh⟩ := after
  refine ⟨⟨shape, enabled, ⟨b, σ, ((f.models_information (tells f)).mp solved).1⟩, ?_⟩, planned, fresh⟩
  have noChecks : f.raw.rule.body.checks = [] := by
    rw [f.describes]
    rcases comm with same | same <;> rw [same] <;> rfl
  intro b' τ _
  constructor
  · intro c member
    change c ∈ f.raw.rule.body.checks.map (Check.map (QN.act f.raw.opening)) at member
    rw [noChecks] at member
    exact (List.not_mem_nil member).elim
  · simp [Firing.collectOpened, f.collect_empty]

/-- Whole-store admission implies admission on the physical view for
these rules: their only observations are absences. Neither equality
matching nor enabledness is weakened. -/
theorem physical_admits_of_whole {s : Store O} {f : Candidate s}
    (a : (step (O := O) .whole).Admits f) : (step (O := O) .physical).Admits f := by
  obtain ⟨⟨shape, enabled, solves, checks⟩, plan, fresh⟩ := a
  refine ⟨⟨shape, enabled, solves, fun b σ models => ?_⟩, plan, fresh⟩
  constructor
  · intro c member
    obtain ⟨p, rfl⟩ := f.opened_absence_checks member
    intro slot seen
    exact (checks b σ models).1 (.predicate .none p) member slot (f.guardRows_subset .physical seen)
  · simp [Firing.collectOpened, f.collect_empty]

/-- Transfer an actual run without changing any selected occurrence or
result state. This direction is not an equivalence: absence can fail
on foreign equal-looking regions in the whole-store policy. -/
def usePhysicalGuards {s : Store O} :
    (step (O := O) .whole).toStep.Run s → (step (O := O) .physical).toStep.Run s
  | .nil _ => .nil _
  | .cons f a rest => .cons f (physical_admits_of_whole a) (usePhysicalGuards rest)

theorem usePhysicalGuards_last {s : Store O} (run : (step (O := O) .whole).toStep.Run s) :
    (usePhysicalGuards run).last = run.last := by
  induction run with
  | nil => rfl
  | cons _ _ _ ih => exact ih

private def namesAvoid (xs ys : List String) : Bool :=
  xs.all fun x => !(ys.contains x)

private theorem namesAvoid_iff (xs ys : List String) :
    namesAvoid xs ys = true ↔ ∀ x ∈ xs, x ∉ ys := by
  simp [namesAvoid, List.all_eq_true]

private def conventionalPair (t a u b : Pattern) : Bool :=
  let tv := pvars t
  let uv := pvars u
  namesAvoid tv uv && namesAvoid tv (pvars b) && namesAvoid uv (pvars a) &&
    namesAvoid tv (MeTTaCalculus.Corrected.binders a) &&
    namesAvoid uv (MeTTaCalculus.Corrected.binders b)

private theorem conventionalPair_iff (t a u b : Pattern) :
    conventionalPair t a u b = true ↔ MeTTaCalculus.Corrected.Apart t a u b := by
  simp only [conventionalPair, Bool.and_eq_true, namesAvoid_iff]
  constructor
  · rintro ⟨⟨⟨⟨patterns, left⟩, right⟩, leftKept⟩, rightKept⟩
    exact ⟨patterns, left, right, leftKept, rightKept⟩
  · intro h
    exact ⟨⟨⟨⟨h.patterns, h.leftOutside⟩, h.rightOutside⟩, h.leftKept⟩, h.rightKept⟩

/-- Match *authored inputs*, not their current instances in the
name frame. This is the existing finite-term principal solver with
the conventional channel and variable-convention checks. -/
def writtenComm (left right : Pattern) : Option Bindings :=
  match left, right with
  | .apply "MFor" [t, x, a], .apply "MFor" [u, y, b] =>
    if x = y ∧ conventionalPair t a u b = true then MeTTaCalculus.Corrected.unify t u else none
  | _, _ => none

theorem writtenComm_pFor_iff (t x a u y b : Pattern) (bs : Bindings) :
    writtenComm (pFor t x a) (pFor u y b) = some bs ↔
      x = y ∧ MeTTaCalculus.Corrected.Apart t a u b ∧ MeTTaCalculus.Corrected.unify t u = some bs := by
  change (if x = y ∧ conventionalPair t a u b = true then MeTTaCalculus.Corrected.unify t u else none) =
    some bs ↔ _
  by_cases good : x = y ∧ conventionalPair t a u b = true
  · rw [if_pos good]
    exact ⟨fun found => ⟨good.1, (conventionalPair_iff t a u b).mp good.2, found⟩,
      fun found => found.2.2⟩
  · rw [if_neg good]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨names, apart, _⟩
      exact (good ⟨names, (conventionalPair_iff t a u b).mpr apart⟩).elim

/-- Use the authored rows supplied by the source representation at this cut,
indexed by physical region. Selection uses the actual two input IDs;
inside a child the third ID determines the region, not its label. -/
def readWrittenPair {R : Type} {s : Store O} (rows : Option O → List (O × Pattern)) (f : Candidate s)
    (inspect : Pattern → Pattern → Option R) : Option R :=
  let pair (place : Option O) (first second : O) := do
    let left ← (rows place).lookup first
    let right ← (rows place).lookup second
    inspect left right
  match f.op, f.raw.selection.taken with
  | .rootComm, [first, second] => pair none first second
  | .childComm, [first, second, slot] =>
    match controlAt s slot .pending with
    | some parent => pair (some parent.key) first second
    | none => none
  | _, _ => none

theorem readWrittenPair_root {R : Type} {s : Store O} (rows : Option O → List (O × Pattern))
    {f : Candidate s} {first second : O} {left right : Pattern}
    (inspect : Pattern → Pattern → Option R)
    (op : f.op = .rootComm) (taken : f.raw.selection.taken = [first, second])
    (readsFirst : (rows none).lookup first = some left)
    (readsSecond : (rows none).lookup second = some right) :
    readWrittenPair rows f inspect = inspect left right := by
  rw [readWrittenPair, op, taken]
  simp [readsFirst, readsSecond]

theorem readWrittenPair_child {R : Type} {s : Store O} (rows : Option O → List (O × Pattern))
    {f : Candidate s} {first second slot : O} {ticket : Ticket O} {left right : Pattern}
    (inspect : Pattern → Pattern → Option R)
    (op : f.op = .childComm) (taken : f.raw.selection.taken = [first, second, slot])
    (route : s.route slot = some (.control ticket .pending))
    (readsFirst : (rows (some ticket.key)).lookup first = some left)
    (readsSecond : (rows (some ticket.key)).lookup second = some right) :
    readWrittenPair rows f inspect = inspect left right := by
  rw [readWrittenPair, op, taken]
  simp [control_at_some.mpr route, readsFirst, readsSecond]

abbrev writtenBinding {s : Store O} (rows : Option O → List (O × Pattern)) (f : Candidate s) :
    Option Bindings := readWrittenPair rows f writtenComm

theorem writtenBinding_root {s : Store O} (rows : Option O → List (O × Pattern))
    {f : Candidate s} {first second : O} {left right : Pattern}
    (op : f.op = .rootComm) (taken : f.raw.selection.taken = [first, second])
    (readsFirst : (rows none).lookup first = some left)
    (readsSecond : (rows none).lookup second = some right) :
    writtenBinding rows f = writtenComm left right :=
  readWrittenPair_root rows writtenComm op taken readsFirst readsSecond

theorem writtenBinding_child {s : Store O} (rows : Option O → List (O × Pattern))
    {f : Candidate s} {first second slot : O} {ticket : Ticket O} {left right : Pattern}
    (op : f.op = .childComm) (taken : f.raw.selection.taken = [first, second, slot])
    (route : s.route slot = some (.control ticket .pending))
    (readsFirst : (rows (some ticket.key)).lookup first = some left)
    (readsSecond : (rows (some ticket.key)).lookup second = some right) :
    writtenBinding rows f = writtenComm left right :=
  readWrittenPair_child rows writtenComm op taken route readsFirst readsSecond

/-- Completing the written binding preserves names left unresolved by the MGU. -/
def writtenReduct (left right : Pattern) : Option (Pattern × Pattern) :=
  match left, right with
  | .apply "MFor" [t, x, a], .apply "MFor" [u, y, b] =>
    (writtenComm (pFor t x a) (pFor u y b)).map fun bs =>
      let completed := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bs
      (applyDot completed a, applyDot completed b)
  | _, _ => none

/-- Tell the two authored continuation values into the selected COMM's actual
output slots. The location and any phase token still come from the ordinary effect. -/
def writtenPairTells (opening : PSubst) (left right : Pattern) : Option (EquationStore Pattern) :=
  (writtenReduct left right).map fun (a, b) =>
    [(psubst opening firstBody, ReflUniform.predotU a), (psubst opening secondBody, ReflUniform.predotU b)]

def writtenTells {s : Store O} (rows : Option O → List (O × Pattern)) (f : Candidate s) :
    Option (EquationStore Pattern) :=
  readWrittenPair rows f (writtenPairTells f.raw.opening)

theorem writtenPairTells_at {t x a u y b : Pattern} {bs : Bindings}
    (opener : PSubst) (found : writtenComm (pFor t x a) (pFor u y b) = some bs) :
    let completed := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bs
    writtenPairTells opener (pFor t x a) (pFor u y b) =
      some [(psubst opener firstBody, ReflUniform.predotU (applyDot completed a)),
        (psubst opener secondBody, ReflUniform.predotU (applyDot completed b))] := by
  intro completed
  change ((writtenComm (pFor t x a) (pFor u y b)).map _).map _ = _
  simp only [found, Option.map_some]
  rfl

/-- Only communication uses the written match; the base step
continues to own the route, physical commit and guards. -/
def WrittenCommAllowed (rows : Store O → Option O → List (O × Pattern)) {s : Store O}
    (f : Candidate s) : Prop :=
  match f.op with
  | .rootComm | .childComm => (writtenBinding (rows s) f).isSome
  | _ => True

/-- A written-match commit uses the same occurrence effect. It must solve
the ordinary match equations and the selected authored publication
equations in one state, before the continuation becomes available. -/
def withWrittenComm (policy : GuardPolicy) (rows : Store O → Option O → List (O × Pattern)) :
    Interface.Step QN O (Store O) (fun s => Candidate s) :=
  Spaces.restrict (step policy (fun {s} f => writtenTells (rows s) f)).toStep (WrittenCommAllowed rows)

theorem written_comm_admits_iff (policy : GuardPolicy) (rows : Store O → Option O → List (O × Pattern))
    {s : Store O} (f : Candidate s) :
    (withWrittenComm policy rows).Admits f ↔
      (step policy (fun {s} g => writtenTells (rows s) g)).Admits f ∧ WrittenCommAllowed rows f := Iff.rfl

theorem written_result_models (policy : GuardPolicy) (rows : Store O → Option O → List (O × Pattern))
    {s : Store O} {f : Candidate s} (admitted : (withWrittenComm policy rows).Admits f)
    {σ : PSubst} (solved : nameAction.Models σ ((withWrittenComm policy rows).result f admitted).raw.knowledge) :
    nameAction.Models σ (f.raw.information QN s.raw) ∧
      nameAction.Models σ ((writtenTells (rows s) f).getD []) :=
  (f.models_information _).mp solved

theorem written_result_label (policy : GuardPolicy) (rows : Store O → Option O → List (O × Pattern))
    {s : Store O} {f : Candidate s} (admitted : (withWrittenComm policy rows).Admits f) (o : O) :
    ((withWrittenComm policy rows).result f admitted).raw.label o = (f.raw.result QN s.raw).label o := rfl

/-- Read both authored outputs using the same location as the prepared
publications. Knowledge transport preserves the equations under every
result solution; location identity still belongs to the physical route. -/
theorem written_result_publications (policy : GuardPolicy) (rows : Store O → Option O → List (O × Pattern))
    {s : Store O} {f : Candidate s} (admitted : (withWrittenComm policy rows).Admits f)
    {l a b : Pattern} {first second : O}
    (told : writtenTells (rows s) f =
      some [(psubst f.raw.opening firstBody, a), (psubst f.raw.opening secondBody, b)])
    (left : (f.raw.result QN s.raw).label first = psubst f.raw.opening (atLoc firstBody l))
    (right : (f.raw.result QN s.raw).label second = psubst f.raw.opening (atLoc secondBody l))
    {σ : PSubst} (solved : nameAction.Models σ ((withWrittenComm policy rows).result f admitted).raw.knowledge) :
    let loc := psubst σ (psubst f.raw.opening l)
    let after := (withWrittenComm policy rows).result f admitted
    NameLaws (psubst σ (after.raw.label first)) (atLoc (psubst σ a) loc) ∧
      NameLaws (psubst σ (after.raw.label second)) (atLoc (psubst σ b) loc) := by
  have authoritative := (written_result_models policy rows admitted solved).2
  rw [told] at authoritative
  have one := authoritative (psubst f.raw.opening firstBody, a) (by simp)
  have two := authoritative (psubst f.raw.opening secondBody, b) (by simp)
  change NameLaws (psubst σ ((f.raw.result QN s.raw).label first)) _ ∧
    NameLaws (psubst σ ((f.raw.result QN s.raw).label second)) _
  rw [left, right]
  simp only [psubst_atLoc_any]
  exact ⟨(ReflLocated.locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨one, NameLaws.refl _⟩,
    (ReflLocated.locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨two, NameLaws.refl _⟩⟩

/-! The authoritative source syntax travels with the corresponding
occurrence. Physical routing and symbolic guard admission remain the
existing checks; neither can be supplied by an authored spelling. -/

private def writtenParallel : Pattern → Option (Pattern × Pattern)
  | .collection .hashBag [a, b] none => some (a, b)
  | _ => none

private def writtenReflection : Pattern → Option (Pattern × Pattern)
  | .apply "MRef" [channel, body] => some (channel, body)
  | _ => none

/-- The source texts installed by the existing rules, in made-slot order.
Pending tickets have no payload; a done ticket carries the authored packed
process. Slots not mentioned by the physical effect cannot be written. -/
def authoredOutputs (authored : O → Option Pattern) :
    Operation → List O → List O → (made : List O) → Option (Vector (Option Pattern) made.length)
  | .rootComm, [left, right], [], [_, _] => do
    let (a, b) ← writtenReduct (← authored left) (← authored right)
    pure #v[some a, some b]
  | .childComm, [left, right, _], [], [_, _, _] => do
    let (a, b) ← writtenReduct (← authored left) (← authored right)
    pure #v[some a, some b, some pZero]
  | .rootHeat, [row], [], [_, _] | .childHeat, [row], [_], [_, _] => do
    let (a, b) ← writtenParallel (← authored row)
    pure #v[some a, some b]
  | .rootClear, [row], [], [] =>
    if authored row = some pZero then some #v[] else none
  | .openRoot, [], [owner], [_, _] | .openChild, [], [owner, _], [_, _] => do
    let (_, body) ← writtenReflection (← authored owner)
    pure #v[some body, none]
  | .cool, [done, row], [], [_] => do
    let acc ← authored done
    let body ← authored row
    pure #v[some (par acc body)]
  | .closeRoot, [owner, done], [], [_] => do
    let (channel, _) ← writtenReflection (← authored owner)
    let acc ← authored done
    pure #v[some (pFor (tProc acc) channel pZero)]
  | .closeChild, [owner, done, _], [], [_, _] => do
    let (channel, _) ← writtenReflection (← authored owner)
    let acc ← authored done
    pure #v[some (pFor (tProc acc) channel pZero), some pZero]
  | _, _, _, _ => none

/-- Payload syntax is read under the outer publication constructor, not
by solving the symbolic label and then guessing its source spelling. -/
def publicationPayload : Pattern → Option Pattern
  | .apply "At" [body, _] => some body
  | .apply "Done" [_, _, body] => some body
  | _ => none

def publicationEquations : List Pattern → List (Option Pattern) → Option (EquationStore Pattern)
  | [], [] => some []
  | p :: ps, text :: rest =>
    match publicationPayload p, text with
    | none, none => publicationEquations ps rest
    | some body, some source =>
      (publicationEquations ps rest).map ((body, ReflUniform.predotU source) :: ·)
    | _, _ => none
  | _, _ => none

def Candidate.authoredPlan {s : Store O} (f : Candidate s) :
    Option (Vector (Option Pattern) f.raw.selection.made.length × EquationStore Pattern) := do
  let texts ← authoredOutputs s.authored f.op f.raw.selection.taken f.raw.selection.read f.raw.selection.made
  let equations ← publicationEquations (f.raw.opened QN).produce texts.toList
  pure (texts, equations)

/-- The state-retaining written policy. The payload and the defining equations
come from one planned publication of the existing step. A missing authored
origin prevents this firing; it does not synthesize one from the quotient. -/
def withAuthored (policy : GuardPolicy) : Interface.Step QN O (Store O) (fun s => Candidate s) :=
  Spaces.restrict
    (step policy (fun f => f.authoredPlan.map Prod.snd) (fun f => f.authoredPlan.map Prod.fst)).toStep
    (fun f => f.authoredPlan.isSome)

theorem authored_admits_iff (policy : GuardPolicy) {s : Store O} (f : Candidate s) :
    (withAuthored policy).Admits f ↔
      (step policy (fun g => g.authoredPlan.map Prod.snd) (fun g => g.authoredPlan.map Prod.fst)).Admits f ∧
      f.authoredPlan.isSome := Iff.rfl

theorem authored_admits_of_models (policy : GuardPolicy) {s : Store O} {f : Candidate s}
    (base : (step (O := O) policy).Admits f)
    {texts : Vector (Option Pattern) f.raw.selection.made.length} {equations : EquationStore Pattern}
    (plan : f.authoredPlan = some (texts, equations))
    {σ : PSubst} (compatible : nameAction.Models σ (f.raw.information QN s.raw))
    (publishes : nameAction.Models σ equations) :
    (withAuthored policy).Admits f := by
  refine (authored_admits_iff policy f).mpr ⟨?_, ?_⟩
  · change f.SymbolicAdmits policy (f.authoredPlan.map Prod.snd) ∧
      f.plan.isSome ∧ s.ledger.Fresh f.raw.selection
    exact admits_with_tells policy (fun g => g.authoredPlan.map Prod.snd) base
      ⟨PUnit.unit, σ, (f.models_information _).mpr ⟨compatible, by simpa [plan] using publishes⟩⟩
  · simp [plan]

/-- Read an authored publication without identifying its syntax with the
quotient of its label. The read is indexed by a solution of the knowledge. -/
def AuthoredRead (σ : PSubst) (label : Pattern) (text : Option Pattern) : Prop :=
  match publicationPayload label, text with
  | some payload, some source => NameLaws (psubst σ payload) (psubst σ (ReflUniform.predotU source))
  | none, none => True
  | _, _ => False

theorem publicationEquations_read {labels : List Pattern} {texts : List (Option Pattern)}
    {equations : EquationStore Pattern} (compiled : publicationEquations labels texts = some equations)
    {σ : PSubst} (solved : nameAction.Models σ equations) {p : Pattern} {text : Option Pattern}
    (entry : (p, text) ∈ labels.zip texts) : AuthoredRead σ p text := by
  induction labels generalizing texts equations with
  | nil => simp at entry
  | cons head tail ih =>
    cases texts with
    | nil => simp at entry
    | cons origin rest =>
      cases payload : publicationPayload head with
      | none =>
        cases origin with
        | none =>
          simp only [publicationEquations, payload] at compiled
          rcases List.mem_cons.mp entry with equality | later
          · cases equality
            simp [AuthoredRead, payload]
          · exact ih compiled solved later
        | some _ => simp [publicationEquations, payload] at compiled
      | some body =>
        cases origin with
        | none => simp [publicationEquations, payload] at compiled
        | some source =>
          simp only [publicationEquations, payload] at compiled
          obtain ⟨restEq, compiledRest, rfl⟩ := Option.map_eq_some_iff.mp compiled
          obtain ⟨headRead, tailRead⟩ := (nameAction.models_cons σ _ _).mp solved
          rcases List.mem_cons.mp entry with equality | later
          · cases equality
            have read : NameLaws (psubst σ body) (psubst σ (ReflUniform.predotU source)) := headRead
            simpa only [AuthoredRead, payload] using read
          · exact ih compiledRest tailRead later

/-- All nonlive slots have no text. Every live slot reads as its stored
text (or as a payload-free control) at every solution of the frame. -/
structure AuthoredReads (s : Store O) : Prop where
  dead : ∀ o ∉ s.raw.present, s.authored o = none
  live : ∀ o ∈ s.raw.present, ∀ σ : PSubst, nameAction.Models σ s.raw.knowledge →
    AuthoredRead σ (s.raw.label o) (s.authored o)

theorem startAuthored_reads (s : State Tm O) (syntaxAt : O → Pattern)
    (encoded : ∀ o ∈ s.present, s.label o = atLoc (ReflUniform.predotU (syntaxAt o)) rootLoc) :
    AuthoredReads (startAuthored s syntaxAt) := by
  constructor
  · intro o dead
    exact if_neg dead
  · intro o live σ _
    change o ∈ s.present at live
    change AuthoredRead σ (s.label o) (if o ∈ s.present then some (syntaxAt o) else none)
    rw [if_pos live, encoded o live]
    exact NameLaws.refl _

/-- The authoritative source lookup cannot turn a ticket or a row in
another region into a row of this region. -/
def Store.authoredRow (s : Store O) (place : Option O) (o : O) : Option Pattern :=
  if o ∈ s.raw.present ∧ s.route o = some (.cell place) then s.authored o else none

theorem Store.authoredRow_eq_some_iff (s : Store O) (place : Option O) (o : O) (text : Pattern) :
    s.authoredRow place o = some text ↔
      o ∈ s.raw.present ∧ s.route o = some (.cell place) ∧ s.authored o = some text := by
  by_cases there : o ∈ s.raw.present ∧ s.route o = some (.cell place)
  · simp [Store.authoredRow, there]
  · simp only [Store.authoredRow, if_neg there, reduceCtorEq]
    exact ⟨False.elim, fun ready => there ⟨ready.1, ready.2.1⟩⟩

theorem Store.authoredRow_readback {s : Store O} {place : Option O} {o : O} {source : Pattern}
    (read : s.authoredRow place o = some source) (authored : AuthoredReads s)
    (forms : LabelForms s) :
    ∃ loc : Pattern, (place = none → loc = rootLoc) ∧
      ∀ σ : PSubst, nameAction.Models σ s.raw.knowledge →
        NameLaws (psubst σ (s.raw.label o))
          (psubst σ (atLoc (ReflUniform.predotU source) loc)) := by
  obtain ⟨live, routed, text⟩ := (s.authoredRow_eq_some_iff place o source).mp read
  have stable {body loc : Pattern} (label : s.raw.label o = atLoc body loc) :
      ∀ σ : PSubst, nameAction.Models σ s.raw.knowledge →
        NameLaws (psubst σ (s.raw.label o)) (psubst σ (atLoc (ReflUniform.predotU source) loc)) := by
    intro σ solved
    have atValue := authored.live o live σ solved
    rw [label, text] at atValue
    change NameLaws (psubst σ body) (psubst σ (ReflUniform.predotU source)) at atValue
    rw [label, psubst_atLoc_any, psubst_atLoc_any]
    exact (ReflLocated.locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨atValue, NameLaws.refl _⟩
  cases place with
  | none =>
    obtain ⟨_, label⟩ := forms routed
    exact ⟨rootLoc, fun _ => rfl, stable label⟩
  | some _ =>
    obtain ⟨_, loc, label⟩ := forms routed
    refine ⟨loc, ?_, stable label⟩
    intro impossible
    cases impossible

theorem authored_routed_result (policy : GuardPolicy)
    {s : Store O} {f : Candidate s} (admitted : (withAuthored policy).Admits f)
    {marks : Vector (Mark O) f.raw.selection.made.length}
    {texts : Vector (Option Pattern) f.raw.selection.made.length} {equations : EquationStore Pattern}
    (route : f.plan = some marks) (source : f.authoredPlan = some (texts, equations)) :
    (withAuthored policy).result f admitted = update f marks (some equations) (some texts) := by
  change update f (f.plan.get _) (f.authoredPlan.map Prod.snd) (f.authoredPlan.map Prod.fst) = _
  simp [source, route]

theorem result_authoredReads (policy : GuardPolicy)
    {s : Store O} {f : Candidate s} (a : (withAuthored policy).Admits f) (prior : AuthoredReads s) :
    AuthoredReads ((withAuthored policy).result f a) := by
  obtain ⟨prepared, recorded⟩ := (authored_admits_iff policy f).mp a
  obtain ⟨route, plan⟩ := Option.isSome_iff_exists.mp prepared.2.1
  obtain ⟨⟨texts, equations⟩, source⟩ := Option.isSome_iff_exists.mp recorded
  have compiled : publicationEquations (f.raw.opened QN).produce texts.toList = some equations := by
    have built := source
    change (authoredOutputs s.authored f.op f.raw.selection.taken f.raw.selection.read
      f.raw.selection.made).bind (fun ts =>
        (publicationEquations (f.raw.opened QN).produce ts.toList).bind (fun es => some (ts, es))) =
      some (texts, equations) at built
    obtain ⟨other, _, store⟩ := Option.bind_eq_some_iff.mp built
    obtain ⟨extra, matched, equal⟩ := Option.bind_eq_some_iff.mp store
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj equal)
    exact matched
  rw [authored_routed_result policy a plan source]
  constructor
  · intro slot absent
    change slot ∉ (f.raw.result QN s.raw).present at absent
    simp [update, absent]
  · intro slot live σ solved
    change nameAction.Models σ (f.information (some equations)) at solved
    change slot ∈ (f.raw.result QN s.raw).present at live
    obtain ⟨symbolic, told⟩ := (f.models_information (some equations)).mp solved
    let outputs := (f.raw.opened QN).produce
    have width : outputs.length = f.raw.selection.made.length := by
      simpa only [outputs, Firing.opened, RuleInstance.map, List.length_map] using prepared.1.1.2.2.2.2.2.1
    have keys : ((f.raw.selection.made.zip texts.toList).map Prod.fst) = f.raw.selection.made :=
      List.map_fst_zip (by simp)
    change AuthoredRead σ ((f.raw.result QN s.raw).label slot)
      (if slot ∈ (f.raw.result QN s.raw).present then
        ((f.raw.selection.made.zip texts.toList).lookup slot).getD (s.authored slot) else none)
    rw [if_pos live]
    by_cases made : slot ∈ f.raw.selection.made
    · obtain ⟨i, index, selected⟩ := List.getElem_of_mem made
      have textIndex : i < texts.toList.length := by simpa using index
      have bodyIndex : i < outputs.length := width ▸ index
      let text := texts.toList[i]'textIndex
      let body := outputs[i]'bodyIndex
      have pairText : (slot, text) ∈ f.raw.selection.made.zip texts.toList := by
        apply List.mem_iff_getElem.mpr
        exact ⟨i, by rw [List.length_zip]; omega, by simp only [List.getElem_zip, selected, text]⟩
      have pairBody : (slot, body) ∈ f.raw.selection.made.zip outputs := by
        apply List.mem_iff_getElem.mpr
        exact ⟨i, by rw [List.length_zip]; omega, by simp only [List.getElem_zip, selected, body]⟩
      have pairBoth : (body, text) ∈ outputs.zip texts.toList := by
        apply List.mem_iff_getElem.mpr
        exact ⟨i, by rw [List.length_zip]; omega, by simp only [List.getElem_zip, body, text]⟩
      have distinct : ((f.raw.selection.made.zip texts.toList).map Prod.fst).Nodup := by
        rw [keys]
        exact prepared.1.1.2.2.1
      have written := LocatedSubstitution.Authority.lookup_write _ distinct pairText
      rw [written, Option.getD_some, Firing.result_label_made (X := QN) (s := s.raw) f.raw prepared.1.1 pairBody]
      exact publicationEquations_read compiled told pairBoth
    · have noWrite : (f.raw.selection.made.zip texts.toList).lookup slot = none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry member
        have appears := (List.of_mem_zip member).1
        simpa using fun equal : slot = entry.1 => made (equal.symm ▸ appears)
      have before : slot ∈ s.raw.present := by
        rcases MeTTaCalculus.OccurrenceCommits.mem_fire.mp live with kept | new
        · exact kept.1
        · exact (made (by simpa [Selection.commit] using new)).elim
      have keptLabel : (f.raw.result QN s.raw).label slot = psubst (fun _ => none) (s.raw.label slot) :=
        Firing.result_label_other (X := QN) (s := s.raw) f.raw made
      have known : nameAction.Models σ s.raw.knowledge := by
        intro e member
        have transported := (RuleSyntax.step QN O QNE located).transported (s := s.raw) f.raw e member
        change (psubst (fun _ => none) e.1, psubst (fun _ => none) e.2) ∈
          f.raw.information QN s.raw at transported
        simp only [psubst_none] at transported
        exact symbolic _ transported
      rw [noWrite, keptLabel, psubst_none]
      exact prior.live slot before σ known

theorem run_authoredReads (policy : GuardPolicy) {s : Store O}
    (run : (withAuthored policy).Run s) (prior : AuthoredReads s) : AuthoredReads run.last := by
  induction run with
  | nil => exact prior
  | cons _ admitted later ih =>
    exact ih (result_authoredReads policy admitted prior)

theorem authored_retained (policy : GuardPolicy)
    {s : Store O} {f : Candidate s} (a : (withAuthored policy).Admits f)
    (covered : s.ledger.Covers s.raw.present) {slot : O}
    (live : slot ∈ s.raw.present) (untouched : slot ∉ f.raw.selection.taken) :
    let after := (withAuthored policy).result f a
    slot ∈ after.raw.present ∧ after.authored slot = s.authored slot ∧ after.route slot = s.route slot := by
  obtain ⟨prepared, recorded⟩ := (authored_admits_iff policy f).mp a
  obtain ⟨route, plan⟩ := Option.isSome_iff_exists.mp prepared.2.1
  obtain ⟨⟨texts, equations⟩, source⟩ := Option.isSome_iff_exists.mp recorded
  rw [authored_routed_result policy a plan source]
  have survives : slot ∈ (f.raw.result QN s.raw).present :=
    MeTTaCalculus.OccurrenceCommits.mem_fire.mpr (.inl ⟨live, by simpa [Selection.commit] using untouched⟩)
  have notMade : slot ∉ f.raw.selection.made :=
    fun made => Ledger.fresh_not_issued prepared.2.2 made (covered.1 live)
  have unwritten : (f.raw.selection.made.zip texts.toList).lookup slot = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry member
    have appears := (List.of_mem_zip member).1
    simpa using fun equal : slot = entry.1 => notMade (equal.symm ▸ appears)
  exact ⟨survives, by simp [update, survives, unwritten],
    Ledger.mark_retained s.ledger route survives notMade⟩

theorem close_root_plan_iff (s : Store O) (owner token result : O) :
    (routes s .closeRoot [owner, token] [] [result]).isSome ↔
      ∃ t, s.route token = some (.control t .done) ∧ t.owner = owner ∧ t.parent = none ∧
        s.route owner = some (.cell none) ∧ s.reserved owner = {token} ∧
        s.childRows t.key = ∅ ∧ s.nested t.key = ∅ := by
  cases current : s.route token with
  | none => simp [routes, controlAt, current]
  | some mark =>
    cases mark with
    | cell place => simp [routes, controlAt, current]
    | control t phase => cases phase <;> simp [routes, controlAt, checked, current]

theorem child_comm_plan_iff (s : Store O) (first second token m₁ m₂ done : O)
    (out : Vector (Mark O) 3) :
    routes s .childComm [first, second, token] [] [m₁, m₂, done] = some out ↔
      ∃ t, s.route token = some (.control t .pending) ∧
        (s.available (some t.key) first ∧ s.available (some t.key) second ∧ s.nested t.key = ∅) ∧
        out = #v[.cell (some t.key), .cell (some t.key), .control t .done] := by
  simp only [routes, Option.bind_eq_some_iff, control_at_some, checked_some]
  exact exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ => eq_comm

/-- The concrete nested return plan, including the parent stamp it
moves to the new done occurrence. -/
theorem close_child_plan_eq_iff (s : Store O) (owner token parent made next : O)
    (out : Vector (Mark O) 2) :
    routes s .closeChild [owner, token, parent] [] [made, next] = some out ↔
      ∃ t p, s.route token = some (.control t .done) ∧ s.route parent = some (.control p .pending) ∧
        t.owner = owner ∧ t.parent = some p.key ∧ s.route owner = some (.cell (some p.key)) ∧
        s.reserved owner = {token} ∧ s.childRows t.key = ∅ ∧ s.nested t.key = ∅ ∧
        s.nested p.key = {token} ∧ out = #v[.cell (some p.key), .control p .done] := by
  simp only [routes, Option.bind_eq_some_iff, control_at_some, checked_some]
  constructor
  · rintro ⟨t, here, p, up, ⟨owns, home, cell, reserved, rows, nested, only⟩, rfl⟩
    exact ⟨t, p, here, up, owns, home, cell, reserved, rows, nested, only, rfl⟩
  · rintro ⟨t, p, here, up, owns, home, cell, reserved, rows, nested, only, rfl⟩
    exact ⟨t, here, p, up, ⟨owns, home, cell, reserved, rows, nested, only⟩, rfl⟩

theorem open_root_plan (s : Store O) (owner pr token : O)
    (present : s.route owner = some (.cell none)) (unreserved : s.reserved owner = ∅) :
    routes s .openRoot [] [owner] [pr, token] =
      some #v[.cell (some token), .control ⟨token, owner, none⟩ .pending] := by
  simp [routes, checked, Store.available, present, unreserved]

theorem open_child_plan (s : Store O) (owner parent pr token : O) (p : Ticket O)
    (pending : s.route parent = some (.control p .pending))
    (available : s.available (some p.key) owner) (noChild : s.nested p.key = ∅) :
    routes s .openChild [] [owner, parent] [pr, token] =
      some #v[.cell (some token), .control ⟨token, owner, some p.key⟩ .pending] := by
  have address : controlAt s parent .pending = some p := control_at_some.mpr pending
  simp [routes, Option.bind, address, checked, available, noChild]

theorem start_unreserved (s : State Tm O) (owner : O) : (start s).reserved owner = ∅ := by
  ext o
  by_cases live : o ∈ s.present <;>
    simp [Store.reserved, Store.route, start, Ledger.root, live, LocatedSubstitution.Authority.Mark.ticket]

/-- A live ticket has an issued key, an exact owner and, when nested, a
pending parent. Keys, owners and outstanding children of a given parent
are unique. Private rows have a live home. These claims concern physical
occurrences, not equality classes of their payloads. -/
structure ScopeLinks (s : Store O) : Prop where
  owner : ∀ ⦃token ticket phase⦄, s.route token = some (.control ticket phase) →
    s.route ticket.owner = some (.cell ticket.parent)
  parent : ∀ ⦃token ticket phase key⦄, s.route token = some (.control ticket phase) →
    ticket.parent = some key → ∃ slot p, s.route slot = some (.control p .pending) ∧ p.key = key
  home : ∀ ⦃row key⦄, s.route row = some (.cell (some key)) →
    ∃ slot t phase, s.route slot = some (.control t phase) ∧ t.key = key
  keyIssued : ∀ ⦃slot t phase⦄, s.route slot = some (.control t phase) → t.key ∈ s.issued
  keyUnique : ∀ ⦃a b t u phase phase'⦄, s.route a = some (.control t phase) →
    s.route b = some (.control u phase') → t.key = u.key → a = b
  ownerUnique : ∀ ⦃a b t u phase phase'⦄, s.route a = some (.control t phase) →
    s.route b = some (.control u phase') → t.owner = u.owner → a = b
  childUnique : ∀ ⦃a b t u phase phase' key⦄, s.route a = some (.control t phase) →
    s.route b = some (.control u phase') → t.parent = some key → u.parent = some key → a = b

omit [DecidableEq O] in
theorem ScopeLinks.of_ledger {s t : Store O} (linked : ScopeLinks s) (same : t.ledger = s.ledger) :
    ScopeLinks t := by
  constructor <;> simp only [Store.route, Store.issued, same]
  · exact linked.owner
  · exact linked.parent
  · exact linked.home
  · exact linked.keyIssued
  · exact linked.keyUnique
  · exact linked.ownerUnique
  · exact linked.childUnique

theorem start_scopeLinks (s : State Tm O) : ScopeLinks (start s) := by
  have noTicket {slot : O} {t : Ticket O} {phase : Phase}
      (marked : (start s).route slot = some (.control t phase)) : False := by
    by_cases live : slot ∈ s.present <;> simp [Store.route, start, Ledger.root, live] at marked
  constructor
  · intro _ _ _ marked
    exact (noTicket marked).elim
  · intro _ _ _ _ marked _
    exact (noTicket marked).elim
  · intro row key marked
    by_cases live : row ∈ s.present <;> simp [Store.route, start, Ledger.root, live] at marked
  · intro _ _ _ marked
    exact (noTicket marked).elim
  · intro _ _ _ _ _ _ marked _ _
    exact (noTicket marked).elim
  · intro _ _ _ _ _ _ marked _ _
    exact (noTicket marked).elim
  · intro _ _ _ _ _ _ _ marked _ _ _
    exact (noTicket marked).elim

theorem region_empty_of_unissued {s : Store O} (linked : ScopeLinks s) {key : O} (fresh : key ∉ s.issued) :
    s.region key = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro slot member
  obtain ⟨_, mark, atSlot, region⟩ := mem_region_iff.mp member
  cases mark with
  | cell place =>
    change place = some key at region
    subst place
    obtain ⟨_, t, _, ticket, rfl⟩ := linked.home atSlot
    exact fresh (linked.keyIssued ticket)
  | control t phase =>
    rcases (show t.key = key ∨ t.parent = some key from region) with rfl | parent
    · exact fresh (linked.keyIssued atSlot)
    · obtain ⟨_, p, up, rfl⟩ := linked.parent atSlot parent
      exact fresh (linked.keyIssued up)

private theorem physical_checks_vacant_or_no_checks {s : Store O} (linked : ScopeLinks s)
    {op : Operation} {taken read made : List O}
    (planned : (routes s op taken read made).isSome) (fresh : Disjoint made.toFinset s.issued) :
    childCheckRows s op taken read made = ∅ ∨ op.rule.body.checks = [] := by
  obtain ⟨out, accepted⟩ := Option.isSome_iff_exists.mp planned
  unfold routes at accepted
  split at accepted <;> simp only [checked_some, Option.bind_eq_some_iff, control_at_some, reduceCtorEq] at accepted
  case h_1 => exact .inr rfl
  case h_2 => exact .inr rfl
  case h_3 => exact .inr rfl
  case h_4 =>
    rename_i owner row key
    exact .inl (region_empty_of_unissued linked (Finset.disjoint_left.mp fresh (by simp)))
  case h_5 =>
    rename_i owner parent row key
    exact .inl (region_empty_of_unissued linked (Finset.disjoint_left.mp fresh (by simp)))
  case h_6 => exact .inr rfl
  case h_7 => exact .inr rfl
  case h_8 => exact .inr rfl
  case h_9 =>
    obtain ⟨t, done, ⟨_, _, _, _, empty, _⟩, _⟩ := accepted
    exact .inl (by simp [childCheckRows, control_at_some.mpr done, empty])
  case h_10 =>
    obtain ⟨t, done, _, _, ⟨_, _, _, _, empty, _, _⟩, _⟩ := accepted
    exact .inl (by simp [childCheckRows, control_at_some.mpr done, empty])

/-- On the proved scope invariant, the route checks settle absence on
the physical domain. Birth examines a never-issued region, while
closing checks the actual child rows and nested tickets. The remaining
symbolic admission still requires solvable matched information. -/
theorem physical_admits_iff {s : Store O} (linked : ScopeLinks s) (f : Candidate s) :
    (step (O := O) .physical).Admits f ↔
      f.raw.Shapes QN s.raw ∧ Enabled (fun _ : O => ()) s.raw.present (f.raw.selection.commit (T := Unit)) ∧
        QN.Solvable (f.raw.information QN s.raw) ∧ f.plan.isSome ∧ s.ledger.Fresh f.raw.selection := by
  constructor
  · rintro ⟨⟨shape, enabled, solves, _⟩, plan, fresh⟩
    exact ⟨shape, enabled, solves, plan, fresh⟩
  · rintro ⟨shape, enabled, solves, plan, fresh⟩
    refine ⟨⟨shape, enabled, solves, fun _ _ _ => ?_⟩, plan, fresh⟩
    constructor
    · intro c member
      rcases physical_checks_vacant_or_no_checks linked plan fresh with vacant | none
      · obtain ⟨p, rfl⟩ := f.opened_absence_checks member
        intro slot seen
        change slot ∈ f.guardRows .physical at seen
        have noRows : f.guardRows .physical = ∅ := vacant
        rw [noRows] at seen
        exact (Finset.notMem_empty _ seen).elim
      · have checks : f.raw.rule.body.checks = [] := by
          rw [f.describes]
          exact none
        simp [Firing.opened, RuleInstance.map, checks] at member
    · simp [Firing.collectOpened, f.collect_empty]

theorem mem_reserved_iff {s : Store O} {owner slot : O} :
    slot ∈ s.reserved owner ↔
      slot ∈ s.raw.present ∧ ∃ t phase, s.route slot = some (.control t phase) ∧ t.owner = owner := by
  simp only [Store.reserved, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  cases s.route slot with
  | none => simp
  | some tag => cases tag <;> simp [LocatedSubstitution.Authority.Mark.ticket]

theorem mem_nested_iff {s : Store O} {key slot : O} :
    slot ∈ s.nested key ↔
      slot ∈ s.raw.present ∧ ∃ t phase, s.route slot = some (.control t phase) ∧ t.parent = some key := by
  simp only [Store.nested, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  cases s.route slot with
  | none => simp
  | some tag => cases tag <;> simp [LocatedSubstitution.Authority.Mark.ticket]

theorem mem_reserved_of_mark {s : Store O} {token : O} {t : Ticket O} {phase : Phase}
    (live : token ∈ s.raw.present) (marked : s.route token = some (.control t phase)) :
    token ∈ s.reserved t.owner :=
  mem_reserved_iff.mpr ⟨live, t, phase, marked, rfl⟩

theorem mem_nested_of_mark {s : Store O} {token key : O} {t : Ticket O} {phase : Phase}
    (live : token ∈ s.raw.present) (marked : s.route token = some (.control t phase))
    (parent : t.parent = some key) : token ∈ s.nested key :=
  mem_nested_iff.mpr ⟨live, t, phase, marked, parent⟩

theorem reserved_eq_singleton {s : Store O} (covered : s.ledger.Covers s.raw.present)
    (linked : ScopeLinks s) {slot : O} {t : Ticket O} {phase : Phase}
    (actual : s.route slot = some (.control t phase)) : s.reserved t.owner = {slot} := by
  ext other
  simp only [Finset.mem_singleton]
  constructor
  · intro member
    obtain ⟨_, u, _, marked, same⟩ := mem_reserved_iff.mp member
    exact linked.ownerUnique marked actual same
  · intro same
    subst other
    have live := (covered.2 slot).mpr (Option.isSome_iff_exists.mpr ⟨_, actual⟩)
    exact mem_reserved_of_mark live actual

theorem nested_eq_singleton {s : Store O} (covered : s.ledger.Covers s.raw.present)
    (linked : ScopeLinks s) {slot key : O} {t : Ticket O} {phase : Phase}
    (actual : s.route slot = some (.control t phase)) (parent : t.parent = some key) :
    s.nested key = {slot} := by
  ext other
  simp only [Finset.mem_singleton]
  constructor
  · intro member
    obtain ⟨_, u, _, marked, same⟩ := mem_nested_iff.mp member
    exact linked.childUnique marked actual same parent
  · intro same
    subst other
    have live := (covered.2 slot).mpr (Option.isSome_iff_exists.mpr ⟨_, actual⟩)
    exact mem_nested_of_mark live actual parent

/-- On an invariant store the selected done stamp already determines
its unique reservation and the owner's place. Child emptiness is
still a separate check. -/
theorem close_root_plan_on_scope_iff (s : Store O) (covered : s.ledger.Covers s.raw.present)
    (linked : ScopeLinks s) (owner token made : O) :
    (routes s .closeRoot [owner, token] [] [made]).isSome ↔
      ∃ t, s.route token = some (.control t .done) ∧ t.owner = owner ∧ t.parent = none ∧
        s.childRows t.key = ∅ ∧ s.nested t.key = ∅ := by
  rw [close_root_plan_iff]
  constructor
  · rintro ⟨t, here, owns, root, _, _, rows, children⟩
    exact ⟨t, here, owns, root, rows, children⟩
  · rintro ⟨t, here, owns, root, rows, children⟩
    refine ⟨t, here, owns, root, ?_, ?_, rows, children⟩
    · simpa only [owns, root] using linked.owner here
    · simpa only [owns] using reserved_eq_singleton covered linked here

/-- For nested return, the two exact stamps also identify the parent's
one outstanding child. No scan is needed to re-prove exclusivity on
a store satisfying the invariant. -/
theorem close_child_plan_on_scope_iff (s : Store O) (covered : s.ledger.Covers s.raw.present)
    (linked : ScopeLinks s) (owner token parent made next : O) :
    (routes s .closeChild [owner, token, parent] [] [made, next]).isSome ↔
      ∃ t p, s.route token = some (.control t .done) ∧ s.route parent = some (.control p .pending) ∧
        t.owner = owner ∧ t.parent = some p.key ∧ s.childRows t.key = ∅ ∧ s.nested t.key = ∅ := by
  constructor
  · intro checked
    obtain ⟨out, plan⟩ := Option.isSome_iff_exists.mp checked
    obtain ⟨t, p, here, up, owns, home, _, _, rows, children, _, _⟩ :=
      (close_child_plan_eq_iff s owner token parent made next out).mp plan
    exact ⟨t, p, here, up, owns, home, rows, children⟩
  · rintro ⟨t, p, here, up, owns, home, rows, children⟩
    refine Option.isSome_iff_exists.mpr ⟨_, (close_child_plan_eq_iff s owner token parent made next _).mpr
      ⟨t, p, here, up, owns, home, ?_, ?_, rows, children,
       nested_eq_singleton covered linked here home, rfl⟩⟩
    · simpa only [owns, home] using linked.owner here
    · simpa only [owns] using reserved_eq_singleton covered linked here

private theorem reserved_control_empty {s : Store O} (linked : ScopeLinks s)
    {slot : O} {t : Ticket O} {phase : Phase} (marked : s.route slot = some (.control t phase)) :
    s.reserved slot = ∅ := by
  ext other
  constructor
  · intro member
    obtain ⟨_, u, _, actual, owner⟩ := mem_reserved_iff.mp member
    have proper := linked.owner actual
    rw [show u.owner = slot from owner, marked] at proper
    cases proper
  · simp

/-- Every taken owner gives up all of its outstanding reservations in
that same cut. A pending parent token can only be taken if every
nested ticket is also taken. These are checks on the actual selection,
not on a reconstructed symbolic location. -/
private theorem routes_spend {s : Store O} (linked : ScopeLinks s)
    {op : Operation} {taken read made : List O} {out : Vector (Mark O) made.length}
    (plan : routes s op taken read made = some out) :
    (∀ owner ∈ taken, ∀ obligation ∈ s.reserved owner, obligation ∈ taken) ∧
      (∀ slot ∈ taken, ∀ p, s.route slot = some (.control p .pending) →
        ∀ child ∈ s.nested p.key, child ∈ taken) := by
  unfold routes at plan
  split at plan <;> simp only [checked_some, Option.bind_eq_some_iff, control_at_some, reduceCtorEq] at plan
  all_goals grind [Store.available, reserved_control_empty]

private def CutLinks (s : Store O) (taken : List O) (t : Ticket O) : Prop :=
  s.route t.owner = some (.cell t.parent) ∧ t.owner ∉ taken ∧
    ∀ key, t.parent = some key → ∃ slot p, s.route slot = some (.control p .pending) ∧
      p.key = key ∧ slot ∉ taken

omit [DecidableEq O] in
private theorem live_of_route {s : Store O} (covered : s.ledger.Covers s.raw.present)
    {slot : O} {mark : Mark O} (known : s.route slot = some mark) : slot ∈ s.raw.present :=
  (covered.2 slot).mpr (by rw [show s.ledger.mark slot = some mark from known]; rfl)

/-- A plan can publish at most one ticket. A birth claims the fresh
output slot as key and takes an unoccupied reservation. A move carries
the exact stamp from a taken token. -/
private theorem routes_ticket_write {s : Store O}
    {op : Operation} {taken read made : List O} {out : Vector (Mark O) made.length}
    (plan : routes s op taken read made = some out) {slot : O} {t : Ticket O} {phase : Phase}
    (written : (slot, .control t phase) ∈ made.zip out.toList) :
    (∀ other u phase', (other, .control u phase') ∈ made.zip out.toList → other = slot) ∧
      ((t.key = slot ∧ s.reserved t.owner = ∅ ∧ ∀ key, t.parent = some key → s.nested key = ∅) ∨
        phase = .done ∧ ∃ source phase', source ∈ taken ∧ s.route source = some (.control t phase')) := by
  unfold routes at plan
  split at plan <;> simp only [checked_some, Option.bind_eq_some_iff, control_at_some, reduceCtorEq] at plan
  case h_1 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_2 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_3 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_4 =>
    obtain ⟨available, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl, rfl⟩ := written
    refine ⟨fun other u phase' member => ?_, .inl ⟨rfl, available.2, by simp⟩⟩
    simp at member
    exact member.1
  case h_5 =>
    obtain ⟨p, _, ⟨available, clear⟩, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl, rfl⟩ := written
    refine ⟨fun other u phase' member => ?_, .inl ⟨rfl, available.2, ?_⟩⟩
    · simp at member
      exact member.1
    · intro key same
      cases same
      exact clear
  case h_6 =>
    obtain ⟨prior, stamp, _, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl, rfl⟩ := written
    refine ⟨fun other u phase' member => ?_, .inr ⟨rfl, _, .pending, by simp, stamp⟩⟩
    simp at member
    exact member.1
  case h_7 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    simp at written
  case h_8 =>
    obtain ⟨prior, stamp, _, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl, rfl⟩ := written
    refine ⟨fun other u phase' member => ?_, .inr ⟨rfl, _, .done, by simp, stamp⟩⟩
    simp at member
    exact member.1
  case h_9 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    simp at written
  case h_10 =>
    obtain ⟨_, _, p, stamp, _, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl, rfl⟩ := written
    refine ⟨fun other u phase' member => ?_, .inr ⟨rfl, _, .pending, by simp, stamp⟩⟩
    simp at member
    exact member.1

/-- Making a new token or moving an existing ticket to a fresh token
has the same predecessor obligations: its owner and any pending
parent both survive this cut. -/
private theorem routes_written_links {s : Store O} (covered : s.ledger.Covers s.raw.present)
    (linked : ScopeLinks s) {op : Operation} {taken read made : List O} {out : Vector (Mark O) made.length}
    (plan : routes s op taken read made = some out) {t : Ticket O} {phase : Phase}
    (written : LocatedSubstitution.Authority.Mark.control t phase ∈ out.toList) :
    CutLinks s taken t := by
  unfold routes at plan
  split at plan <;> simp only [checked_some, Option.bind_eq_some_iff, control_at_some, reduceCtorEq] at plan
  case h_1 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_2 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_3 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_4 =>
    obtain ⟨available, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl⟩ := written
    exact ⟨available.1, by simp, by simp⟩
  case h_5 =>
    obtain ⟨p, pending, ⟨available, _⟩, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl⟩ := written
    refine ⟨available.1, by simp, fun key parent => ⟨_, p, pending, ?_, by simp⟩⟩
    exact Option.some.inj parent
  case h_6 =>
    obtain ⟨source, stamp, enabled, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl⟩ := written
    have owns := linked.owner stamp
    have held := mem_reserved_of_mark (live_of_route covered stamp) stamp
    refine ⟨owns, by grind [Store.available], ?_⟩
    intro key parent
    have inside := mem_nested_of_mark (live_of_route covered stamp) stamp parent
    obtain ⟨slot, anchor, pending, identifies⟩ := linked.parent stamp parent
    exact ⟨slot, anchor, pending, identifies, by grind [Store.available]⟩
  case h_7 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    simp at written
  case h_8 =>
    obtain ⟨source, stamp, enabled, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl⟩ := written
    have owns := linked.owner stamp
    have held := mem_reserved_of_mark (live_of_route covered stamp) stamp
    refine ⟨owns, by grind [Store.available], ?_⟩
    intro key parent
    obtain ⟨slot, anchor, pending, identifies⟩ := linked.parent stamp parent
    exact ⟨slot, anchor, pending, identifies, by grind [Store.available]⟩
  case h_9 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    simp at written
  case h_10 =>
    obtain ⟨inner, childStamp, source, stamp, enabled, rfl⟩ := plan
    simp at written
    obtain ⟨rfl, rfl⟩ := written
    have owns := linked.owner stamp
    have held := mem_reserved_of_mark (live_of_route covered stamp) stamp
    refine ⟨owns, by grind, ?_⟩
    intro key parent
    have inside := mem_nested_of_mark (live_of_route covered stamp) stamp parent
    obtain ⟨slot, anchor, pending, identifies⟩ := linked.parent stamp parent
    exact ⟨slot, anchor, pending, identifies, by grind⟩

/-- Moving a token retains the same logical region. Discarding its
region altogether is allowed only when there are no private rows. -/
private theorem routes_taken_home {s : Store O}
    {op : Operation} {taken read made : List O} {out : Vector (Mark O) made.length}
    (plan : routes s op taken read made = some out) {slot : O} {t : Ticket O} {phase : Phase}
    (selected : slot ∈ taken) (marked : s.route slot = some (.control t phase)) :
    s.childRows t.key = ∅ ∨ ∃ phase', LocatedSubstitution.Authority.Mark.control t phase' ∈ out.toList := by
  unfold routes at plan
  split at plan <;> simp only [checked_some, Option.bind_eq_some_iff, control_at_some, reduceCtorEq] at plan
  case h_1 => grind [Store.available]
  case h_2 => grind [Store.available]
  case h_3 => grind [Store.available]
  case h_4 => simp at selected
  case h_5 => simp at selected
  case h_6 =>
    obtain ⟨prior, stamp, enabled, rfl⟩ := plan
    have same : t = prior := by grind [Store.available]
    subst t
    exact .inr ⟨.done, by simp⟩
  case h_7 => grind [Store.available]
  case h_8 =>
    obtain ⟨prior, stamp, enabled, rfl⟩ := plan
    have same : t = prior := by grind [Store.available]
    subst t
    exact .inr ⟨.done, by simp⟩
  case h_9 =>
    obtain ⟨prior, stamp, ⟨_, _, owner, _, empty, _⟩, _⟩ := plan
    have same : t = prior := by grind
    exact .inl (same.symm ▸ empty)
  case h_10 =>
    obtain ⟨inner, stamp, parent, pending, ⟨_, _, owner, _, empty, _⟩, rfl⟩ := plan
    by_cases same : t = inner
    · exact .inl (same.symm ▸ empty)
    · have equal : t = parent := by grind
      subst t
      exact .inr ⟨.done, by simp⟩

/-- A made private row gets its region from either a made or a
retained token in the very same cut. -/
private theorem routes_written_home {s : Store O}
    {op : Operation} {taken read made : List O} {out : Vector (Mark O) made.length}
    (plan : routes s op taken read made = some out) {key : O}
    (written : LocatedSubstitution.Authority.Mark.cell (some key) ∈ out.toList) :
    (∃ t phase, LocatedSubstitution.Authority.Mark.control t phase ∈ out.toList ∧ t.key = key) ∨
      (∃ slot t phase, s.route slot = some (.control t phase) ∧ t.key = key ∧ slot ∉ taken) := by
  unfold routes at plan
  split at plan <;> simp only [checked_some, Option.bind_eq_some_iff, control_at_some, reduceCtorEq] at plan
  case h_1 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_2 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_3 =>
    obtain ⟨_, rfl⟩ := plan
    simp at written
  case h_4 =>
    rename_i owner row child
    obtain ⟨_, rfl⟩ := plan
    simp at written
    subst key
    exact .inl ⟨⟨child, owner, none⟩, .pending, by simp, rfl⟩
  case h_5 =>
    rename_i owner parent row child
    obtain ⟨p, _, _, rfl⟩ := plan
    simp at written
    subst key
    exact .inl ⟨⟨child, owner, some p.key⟩, .pending, by simp, rfl⟩
  case h_6 =>
    obtain ⟨t, _, _, rfl⟩ := plan
    simp at written
    exact .inl ⟨t, .done, by simp, written.symm⟩
  case h_7 =>
    obtain ⟨t, pending, available, rfl⟩ := plan
    simp at written
    exact .inr ⟨_, t, .pending, pending, written.symm, by grind [Store.available]⟩
  case h_8 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    simp at written
  case h_9 =>
    obtain ⟨_, _, _, rfl⟩ := plan
    simp at written
  case h_10 =>
    obtain ⟨_, _, t, _, _, rfl⟩ := plan
    simp at written
    exact .inl ⟨t, .done, by simp, written.symm⟩

private theorem update_scopeLinks {s : Store O} {f : Candidate s}
    {out : Vector (Mark O) f.raw.selection.made.length}
    (covered : s.ledger.Covers s.raw.present) (linked : ScopeLinks s)
    (unused : s.ledger.Fresh f.raw.selection) (distinct : f.raw.selection.made.Nodup)
    (planned : f.plan = some out) :
    ScopeLinks (update f out) := by
  have origin {slot : O} {tag : Mark O} :
      (update f out).route slot = some tag ↔
        (slot, tag) ∈ f.raw.selection.made.zip out.toList ∨
          (slot ∈ s.raw.present ∧ slot ∉ f.raw.selection.taken ∧ s.route slot = some tag) :=
    Ledger.mark_advance_iff out covered unused distinct
  have writes {tag : Mark O} (member : tag ∈ out.toList) :
      ∃ slot, (update f out).route slot = some tag := by
    have columns : (f.raw.selection.made.zip out.toList).map Prod.snd = out.toList :=
      List.map_snd_zip (by simp)
    rw [← columns] at member
    obtain ⟨⟨slot, mark⟩, paired, same⟩ := List.mem_map.mp member
    change mark = tag at same
    subst mark
    exact ⟨slot, origin.mpr (.inl paired)⟩
  have guards := routes_spend linked planned
  have supports {slot : O} {t : Ticket O} {phase : Phase}
      (current : (update f out).route slot = some (.control t phase)) :
      CutLinks s f.raw.selection.taken t := by
    rcases origin.mp current with wrote | ⟨live, retained, old⟩
    · exact routes_written_links covered linked planned (List.of_mem_zip wrote).2
    · have reserved := mem_reserved_of_mark live old
      refine ⟨linked.owner old, fun took => retained (guards.1 _ took _ reserved), ?_⟩
      intro key parent
      obtain ⟨a, p, pending, home⟩ := linked.parent old parent
      refine ⟨a, p, pending, home, ?_⟩
      intro took
      apply retained (guards.2 a took p pending slot ?_)
      rw [home]
      exact mem_nested_of_mark live old parent
  have uniqueClaim (claim : Ticket O → Prop)
      (oldUnique : ∀ ⦃a b t u phase phase'⦄, s.route a = some (.control t phase) →
        s.route b = some (.control u phase') → claim t → claim u → a = b)
      (newDisjoint : ∀ ⦃a b t u phase⦄, a ∈ f.raw.selection.made → t.key = a → s.reserved t.owner = ∅ →
        (∀ key, t.parent = some key → s.nested key = ∅) →
        s.route b = some (.control u phase) → claim t → claim u → False) :
      ∀ ⦃a b t u phase phase'⦄, (update f out).route a = some (.control t phase) →
        (update f out).route b = some (.control u phase') → claim t → claim u → a = b := by
    have mixed {a b t u phase phase'}
        (written : (a, LocatedSubstitution.Authority.Mark.control t phase) ∈
          f.raw.selection.made.zip out.toList)
        (kept : b ∉ f.raw.selection.taken) (old : s.route b = some (.control u phase'))
        (left : claim t) (right : claim u) : False := by
      rcases (routes_ticket_write planned written).2 with ⟨isKey, clear, notNested⟩ |
        ⟨_, source, _, took, carries⟩
      · exact newDisjoint (List.of_mem_zip written).1 isKey clear notNested old left right
      · exact kept ((oldUnique carries old left right) ▸ took)
    intro a b t u phase phase' left right claimsLeft claimsRight
    rcases origin.mp left with writtenLeft | ⟨_, keptLeft, oldLeft⟩
    · rcases origin.mp right with writtenRight | ⟨_, keptRight, oldRight⟩
      · exact ((routes_ticket_write planned writtenLeft).1 _ _ _ writtenRight).symm
      · exact (mixed writtenLeft keptRight oldRight claimsLeft claimsRight).elim
    · rcases origin.mp right with writtenRight | ⟨_, keptRight, oldRight⟩
      · exact (mixed writtenRight keptLeft oldLeft claimsRight claimsLeft).elim
      · exact oldUnique oldLeft oldRight claimsLeft claimsRight
  constructor
  · intro slot t phase current
    obtain ⟨mark, retained, _⟩ := supports current
    exact origin.mpr (.inr ⟨live_of_route covered mark, retained, mark⟩)
  · intro slot t phase key current parent
    obtain ⟨a, p, mark, identifies, retained⟩ := (supports current).2.2 key parent
    exact ⟨a, p, origin.mpr (.inr ⟨live_of_route covered mark, retained, mark⟩), identifies⟩
  · intro row key current
    rcases origin.mp current with written | ⟨live, _, old⟩
    · rcases routes_written_home planned (List.of_mem_zip written).2 with
        ⟨t, phase, published, equal⟩ | ⟨slot, t, phase, retained, equal, notTaken⟩
      · obtain ⟨slot, reads⟩ := writes published
        exact ⟨slot, t, phase, reads, equal⟩
      · exact ⟨slot, t, phase, origin.mpr (.inr ⟨live_of_route covered retained, notTaken, retained⟩), equal⟩
    · obtain ⟨slot, t, phase, previous, home⟩ := linked.home old
      by_cases taken : slot ∈ f.raw.selection.taken
      · rcases routes_taken_home planned taken previous with empty | ⟨phase', produced⟩
        · have resident : row ∈ s.childRows t.key := by simp [Store.childRows, live, home, old]
          rw [empty] at resident
          exact (Finset.notMem_empty _ resident).elim
        · obtain ⟨new, stamp⟩ := writes produced
          exact ⟨new, t, phase', stamp, home⟩
      · exact ⟨slot, t, phase, origin.mpr (.inr ⟨live_of_route covered previous, taken, previous⟩), home⟩
  · intro slot t phase current
    change t.key ∈ s.issued ∪ f.raw.selection.made.toFinset
    rcases origin.mp current with written | ⟨_, _, old⟩
    · rcases (routes_ticket_write planned written).2 with ⟨isKey, _, _⟩ | ⟨_, _, _, _, old⟩
      · exact Finset.mem_union_right _ (isKey.symm ▸ List.mem_toFinset.mpr (List.of_mem_zip written).1)
      · exact Finset.mem_union_left _ (linked.keyIssued old)
    · exact Finset.mem_union_left _ (linked.keyIssued old)
  · intro a b t u phase phase' left right same
    apply uniqueClaim (fun v => v.key = u.key) ?_ ?_ left right same rfl
    · intro _ _ _ _ _ _ x y k₁ k₂
      exact linked.keyUnique x y (k₁.trans k₂.symm)
    · intro slot _ _ _ _ made atKey _ _ old k₁ k₂
      apply Ledger.fresh_not_issued unused made
      rw [← atKey, k₁, ← k₂]
      exact linked.keyIssued old
  · intro a b t u phase phase' left right same
    apply uniqueClaim (fun v => v.owner = u.owner) ?_ ?_ left right same rfl
    · intro _ _ _ _ _ _ x y owner₁ owner₂
      exact linked.ownerUnique x y (owner₁.trans owner₂.symm)
    · intro _ _ _ _ _ _ _ clear _ old owner₁ owner₂
      have held := mem_reserved_of_mark (live_of_route covered old) old
      rw [owner₂.trans owner₁.symm, clear] at held
      exact Finset.notMem_empty _ held
  · intro a b t u phase phase' key left right parent₁ parent₂
    apply uniqueClaim (fun v => v.parent = some key) ?_ ?_ left right parent₁ parent₂
    · intro _ _ _ _ _ _ x y p₁ p₂
      exact linked.childUnique x y p₁ p₂
    · intro _ _ _ _ _ _ _ _ clear old p₁ p₂
      have nested := mem_nested_of_mark (live_of_route covered old) old p₂
      rw [clear key p₁] at nested
      exact Finset.notMem_empty _ nested

section RoutingResults

variable {policy : GuardPolicy}

theorem raw_result {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) :
    ((step (O := O) policy).toStep.result f a).raw = f.raw.result QN s.raw := rfl

theorem routed_result_with {tells : {s : Store O} → Candidate s → Option (EquationStore Pattern)}
    {s : Store O} {f : Candidate s} (a : (step (O := O) policy tells).Admits (s := s) f)
    {out : Vector (Mark O) f.raw.selection.made.length} (planned : f.plan = some out) :
    (step (O := O) policy tells).toStep.result f a = update f out (tells f) := by
  change update f (f.plan.get _) (tells f) = update f out (tells f)
  congr 1
  simp [planned]

theorem routed_result {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f)
    {out : Vector (Mark O) f.raw.selection.made.length} (planned : f.plan = some out) :
    (step (O := O) policy).toStep.result f a = update f out :=
  routed_result_with a planned

/-- A written commit alters only the information, not the route installed
for the selected occurrences. -/
theorem written_routed_result (rows : Store O → Option O → List (O × Pattern))
    {s : Store O} {f : Candidate s} (a : (withWrittenComm policy rows).Admits f)
    {out : Vector (Mark O) f.raw.selection.made.length} (planned : f.plan = some out) :
    (withWrittenComm policy rows).result f a = update f out (writtenTells (rows s) f) :=
  routed_result_with (written_comm_admits_iff policy rows f |>.mp a |>.1) planned

private theorem labelForms_update {s : Store O} {f : Candidate s}
    {out : Vector (Mark O) f.raw.selection.made.length} {equations : Option (EquationStore Pattern)}
    {origins : Option (Vector (Option Pattern) f.raw.selection.made.length)}
    (plan : f.plan = some out) (shapes : f.raw.Shapes QN s.raw)
    (unused : s.ledger.Fresh f.raw.selection)
    (covered : s.ledger.Covers s.raw.present) (formed : LabelForms s) :
    LabelForms (update f out equations origins) := by
  intro slot mark tagged
  change MarkForm mark ((f.raw.result QN s.raw).label slot)
  rcases (Ledger.mark_advance_iff out covered unused shapes.2.2.1).mp tagged with
    written | ⟨live, _, old⟩
  · obtain ⟨body, position, form⟩ := paired_mark_form (routes_output_forms plan) written
    have selected : (slot, body) ∈ f.raw.selection.made.zip f.raw.rule.body.produce := by
      rw [f.describes]
      exact position
    have opened : (slot, psubst f.raw.opening body) ∈ f.raw.selection.made.zip (f.raw.opened QN).produce := by
      show _ ∈ f.raw.selection.made.zip (f.raw.rule.body.produce.map _)
      rw [List.zip_map_right]
      exact List.mem_map.mpr ⟨_, selected, rfl⟩
    rw [Firing.result_label_made (X := QN) (s := s.raw) f.raw shapes opened]
    exact form.instantiate f.raw.opening
  · have notMade : slot ∉ f.raw.selection.made :=
      fun made => Ledger.fresh_not_issued unused made (covered.1 live)
    have same : (f.raw.result QN s.raw).label slot = psubst (fun _ => none) (s.raw.label slot) :=
      Firing.result_label_other (X := QN) (s := s.raw) f.raw notMade
    rw [same, psubst_none]
    exact formed old

theorem result_labelForms {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits f) (covered : s.ledger.Covers s.raw.present) (formed : LabelForms s) :
    LabelForms ((step (O := O) policy).toStep.result f a) := by
  obtain ⟨out, plan⟩ := Option.isSome_iff_exists.mp a.2.1
  rw [routed_result a plan]
  exact labelForms_update plan a.1.1 a.2.2 covered formed

/-- Extend a run by a raw firing once its physical route and fresh occurrence
selection are checked. The endpoint is the concrete tagged update. -/
theorem append_update {start current : Store O}
    (earlier : (step (O := O) policy).toStep.Run start) (endpoint : earlier.last = current)
    {f : Candidate current} {out : Vector (Mark O) f.raw.selection.made.length}
    (raw : f.SymbolicAdmits policy)
    (planned : f.plan = some out) (fresh : current.ledger.Fresh f.raw.selection) :
    ∃ run : (step (O := O) policy).toStep.Run start, run.last = update f out := by
  subst current
  have admitted : (step (O := O) policy).Admits (s := earlier.last) f :=
    ⟨raw, by simp [planned], fresh⟩
  let edge : (step (O := O) policy).toStep.Run earlier.last := .cons f admitted (.nil _)
  exact ⟨earlier.append edge, (earlier.last_append edge).trans (routed_result admitted planned)⟩

/-- A routed run cannot forget that an identity was issued, and its
tagged domain agrees with the actual occurrence store at every prefix. -/
theorem covers_result {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) (covered : s.ledger.Covers s.raw.present) :
    ((step (O := O) policy).toStep.result f a).ledger.Covers ((step (O := O) policy).toStep.result f a).raw.present :=
  Ledger.covers_advance _ covered

/-- A take retires the selected slot even when its ticket is moved to a
new occurrence. Made identities cannot overlap live taken identities. -/
theorem result_taken_unmarked {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits f) (covered : s.ledger.Covers s.raw.present)
    {slot : O} (spent : slot ∈ f.raw.selection.taken) :
    ((step (O := O) policy).toStep.result f a).route slot = none := by
  have disjoint := MeTTaCalculus.OccurrenceCommits.disjoint_taken_fire a.1.2.1
  have taken : slot ∈ (f.raw.selection.commit (T := Unit)).taken := by
    simpa only [Selection.commit, List.mem_toFinset] using spent
  by_contra marked
  exact Finset.disjoint_left.mp disjoint taken
    ((covers_result a covered).2 slot |>.mpr (Option.isSome_iff_ne_none.mpr marked))

/-- A routed cut frames any class of marks it neither takes nor writes.
This is a statement about actual occurrences, independent of whether a
term substitution can identify the labels on two different rows. -/
theorem result_marks_frame {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) (covered : s.ledger.Covers s.raw.present)
    {out : Vector (Mark O) f.raw.selection.made.length} (planned : f.plan = some out)
    (holds : Mark O → Prop)
    (retains : ∀ ⦃slot tag⦄, s.route slot = some tag → holds tag → slot ∉ f.raw.selection.taken)
    (outside : ∀ tag ∈ out.toList, ¬ holds tag) ⦃slot : O⦄ ⦃tag : Mark O⦄ (view : holds tag) :
    ((step (O := O) policy).toStep.result f a).route slot = some tag ↔ s.route slot = some tag := by
  rw [routed_result a planned]
  change (s.ledger.advance s.raw.present f.raw.selection out).mark slot = some tag ↔ _
  rw [Ledger.mark_advance_iff out covered a.2.2 a.1.1.2.2.1]
  refine ⟨?_, fun old => .inr ⟨live_of_route covered old, retains old view, old⟩⟩
  rintro (put | ⟨_, _, old⟩)
  · exact (outside _ (List.of_mem_zip put).2 view).elim
  · exact old

private theorem childRows_eq_of_marks {s t : Store O} {key : O}
    (pre : s.ledger.Covers s.raw.present) (post : t.ledger.Covers t.raw.present)
    (same : ∀ o, t.route o = some (.cell (some key)) ↔ s.route o = some (.cell (some key))) :
    t.childRows key = s.childRows key := by
  ext o
  have readback (u : Store O) (valid : u.ledger.Covers u.raw.present) :
      o ∈ u.childRows key ↔ u.route o = some (.cell (some key)) :=
    ⟨fun member => (Finset.mem_filter.mp member).2, fun mark =>
      Finset.mem_filter.mpr ⟨live_of_route valid mark, mark⟩⟩
  exact (readback t post).trans ((same o).trans (readback s pre).symm)

private theorem nested_eq_of_marks {s t : Store O} {key : O}
    (pre : s.ledger.Covers s.raw.present) (post : t.ledger.Covers t.raw.present)
    (same : ∀ o child phase, child.parent = some key →
      (t.route o = some (.control child phase) ↔ s.route o = some (.control child phase))) :
    t.nested key = s.nested key := by
  ext o
  have readback (u : Store O) (valid : u.ledger.Covers u.raw.present) :
      o ∈ u.nested key ↔ ∃ child phase, u.route o = some (.control child phase) ∧ child.parent = some key :=
    ⟨fun member => (mem_nested_iff.mp member).2, fun ⟨child, phase, mark, parent⟩ =>
      mem_nested_of_mark (live_of_route valid mark) mark parent⟩
  rw [readback t post, readback s pre]
  exact exists_congr fun child => exists_congr fun phase =>
    ⟨fun ⟨mark, parent⟩ => ⟨(same o child phase parent).mp mark, parent⟩,
     fun ⟨mark, parent⟩ => ⟨(same o child phase parent).mpr mark, parent⟩⟩

/-- The row and nested-ticket indexes of an untouched region are
unchanged by the real commit; even the token slot and phase are the
same when observed at that region. -/
theorem result_region_frame {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) (covered : s.ledger.Covers s.raw.present)
    {out : Vector (Mark O) f.raw.selection.made.length} (planned : f.plan = some out) (key : O)
    (retains : ∀ ⦃slot tag⦄, s.route slot = some tag → AtRegion key tag → slot ∉ f.raw.selection.taken)
    (outside : ∀ tag ∈ out.toList, ¬ AtRegion key tag) :
    let after := (step (O := O) policy).toStep.result f a
    after.childRows key = s.childRows key ∧ after.nested key = s.nested key ∧
    ∀ slot t phase, t.key = key →
      (after.route slot = some (.control t phase) ↔ s.route slot = some (.control t phase)) := by
  intro after
  have frame := result_marks_frame a covered planned (AtRegion key) retains outside
  have posts := covers_result a covered
  exact ⟨childRows_eq_of_marks covered posts (fun _ => frame rfl),
    nested_eq_of_marks covered posts (fun _ _ _ parent => frame (.inr parent)),
    fun _ _ _ same => frame (.inl same)⟩

/-- An existing owner reservation is a finite mark query as well. Its
entire answer set is retained when the cut neither spends nor creates
a ticket for that owner. -/
theorem result_owner_frame {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) (covered : s.ledger.Covers s.raw.present)
    {out : Vector (Mark O) f.raw.selection.made.length} (planned : f.plan = some out) (owner : O)
    (retains : ∀ ⦃slot t phase⦄, s.route slot = some (.control t phase) → t.owner = owner →
        slot ∉ f.raw.selection.taken)
    (outside : ∀ t phase, LocatedSubstitution.Authority.Mark.control t phase ∈ out.toList → t.owner ≠ owner) :
    ((step (O := O) policy).toStep.result f a).reserved owner = s.reserved owner := by
  let after := (step (O := O) policy).toStep.result f a
  let observation : Mark O → Prop := fun tag => (tag.ticket.map Ticket.owner) = some owner
  have keep ⦃slot tag⦄ (old : s.route slot = some tag) (relevant : observation tag) :
      slot ∉ f.raw.selection.taken := by
    cases tag with
    | cell place => cases relevant
    | control t phase => exact retains old (Option.some.inj relevant)
  have remote (tag : Mark O) (written : tag ∈ out.toList) : ¬ observation tag := by
    cases tag with
    | cell place => intro impossible; cases impossible
    | control t phase => exact fun relevant => outside t phase written (Option.some.inj relevant)
  have frame := result_marks_frame a covered planned observation keep remote
  have member (u : Store O) (valid : u.ledger.Covers u.raw.present) (slot : O) :
      slot ∈ u.reserved owner ↔ ∃ t phase, u.route slot = some (.control t phase) ∧ t.owner = owner :=
    ⟨fun known => (mem_reserved_iff.mp known).2, fun ⟨t, phase, marked, own⟩ =>
      mem_reserved_iff.mpr ⟨live_of_route valid marked, t, phase, marked, own⟩⟩
  ext slot
  change slot ∈ after.reserved owner ↔ slot ∈ s.reserved owner
  rw [member after (covers_result a covered), member s covered]
  exact exists_congr fun t => exists_congr fun phase =>
    ⟨fun ⟨marks, own⟩ => ⟨(frame (slot := slot) (tag := .control t phase) (congrArg some own)).mp marks, own⟩,
     fun ⟨marks, own⟩ => ⟨(frame (slot := slot) (tag := .control t phase) (congrArg some own)).mpr marks, own⟩⟩

/-- Opening under one physical parent leaves the routing and allocation
checks for a different parent's opening intact. This is the physical
part of the swap: a second symbolic firing must still establish its
equations and absence checks. -/
theorem separate_parent_open_plan {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) (covered : s.ledger.Covers s.raw.present)
    (linked : ScopeLinks s)
    {firstOwner firstSlot firstRow firstKey otherOwner otherSlot otherRow otherKey : O}
    {firstParent otherParent : Ticket O}
    (op : f.op = .openChild) (chosen : f.raw.selection = ⟨[], [firstOwner, firstSlot], [firstRow, firstKey]⟩)
    (first : s.route firstSlot = some (.control firstParent .pending))
    (other : s.route otherSlot = some (.control otherParent .pending))
    (different : firstParent.key ≠ otherParent.key)
    (available : s.available (some otherParent.key) otherOwner)
    (noChild : s.nested otherParent.key = ∅)
    (otherFresh : Disjoint ({otherRow, otherKey} : Finset O) s.issued)
    (disjointMade : Disjoint ({otherRow, otherKey} : Finset O) {firstRow, firstKey}) :
    let after := (step (O := O) policy).toStep.result f a
    routes after .openChild [] [otherOwner, otherSlot] [otherRow, otherKey] =
      some #v[.cell (some otherKey), .control ⟨otherKey, otherOwner, some otherParent.key⟩ .pending] ∧
    Disjoint ({otherRow, otherKey} : Finset O) after.issued := by
  intro after
  let visible (sel : Selection O) : Option (List (Mark O)) :=
    (routes s .openChild sel.taken sel.read sel.made).map Vector.toList
  have shape := congrArg visible chosen
  have accepted : (routes s .openChild [] [firstOwner, firstSlot] [firstRow, firstKey]).isSome := by
    have check : (visible f.raw.selection).isSome := by
      simpa only [visible, Option.isSome_map, Candidate.plan, op] using a.2.1
    rw [shape] at check
    simpa only [visible, Option.isSome_map] using check
  have atFirst := control_at_some.mpr first
  have opened : s.available (some firstParent.key) firstOwner ∧ s.nested firstParent.key = ∅ := by
    by_contra notEnabled
    simp [routes, atFirst, checked, notEnabled] at accepted
  obtain ⟨out, planned⟩ := Option.isSome_iff_exists.mp a.2.1
  have selectedTags :
      (routes s .openChild [] [firstOwner, firstSlot] [firstRow, firstKey]).map Vector.toList =
        some out.toList := by
    have tags : visible f.raw.selection = some out.toList := by
      simpa only [visible, Candidate.plan, op, Option.map_some] using congrArg (Option.map Vector.toList) planned
    exact shape.symm.trans tags
  rw [open_child_plan s firstOwner firstSlot firstRow firstKey firstParent first opened.1 opened.2]
    at selectedTags
  have written : out.toList = [.cell (some firstKey),
      .control ⟨firstKey, firstOwner, some firstParent.key⟩ .pending] :=
    (Option.some.inj selectedTags).symm
  have ownsDifferent : firstOwner ≠ otherOwner := by
    intro same
    have left : s.route otherOwner = some (.cell (some firstParent.key)) := same ▸ opened.1.1
    have homes := LocatedSubstitution.Authority.Mark.cell.inj (Option.some.inj (left.symm.trans available.1))
    exact different (Option.some.inj homes)
  have keyDifferent : firstKey ≠ otherParent.key := by
    intro same
    have fresh : firstKey ∉ s.issued := Ledger.fresh_not_issued a.2.2 (by simp [chosen])
    exact fresh (same.symm ▸ linked.keyIssued other)
  have framed := result_region_frame a covered planned otherParent.key (by simp [chosen]) (by
    intro mark made
    rw [written] at made
    simp only [List.mem_cons, List.not_mem_nil, or_false] at made
    rcases made with rfl | rfl <;> simp [AtRegion, different, keyDifferent])
  have reserved := result_owner_frame a covered planned otherOwner (by simp [chosen]) (by
    intro t phase member
    simp [written] at member
    obtain ⟨rfl, rfl⟩ := member
    exact ownsDifferent)
  have keptParent : after.route otherSlot = some (.control otherParent .pending) :=
    (framed.2.2 otherSlot otherParent .pending rfl).mpr other
  have keptOwner : after.route otherOwner = some (.cell (some otherParent.key)) := by
    have resides : otherOwner ∈ s.childRows otherParent.key :=
      Finset.mem_filter.mpr ⟨live_of_route covered available.1, available.1⟩
    have retained : otherOwner ∈ after.childRows otherParent.key := framed.1.symm ▸ resides
    exact (Finset.mem_filter.mp retained).2
  refine ⟨open_child_plan after otherOwner otherSlot otherRow otherKey otherParent keptParent
    ⟨keptOwner, reserved.trans available.2⟩ (framed.2.1.trans noChild), ?_⟩
  change Disjoint _ ((step (O := O) policy).toStep.result f a).issued
  rw [routed_result a planned]
  change Disjoint _ (s.issued ∪ f.raw.selection.made.toFinset)
  exact Finset.disjoint_union_right.mpr ⟨otherFresh, by simpa [chosen] using disjointMade⟩

theorem run_covers {s : Store O} (run : (step (O := O) policy).toStep.Run s)
    (covered : s.ledger.Covers s.raw.present) : run.last.ledger.Covers run.last.raw.present := by
  induction run with
  | nil => exact covered
  | cons _ admitted _ ih => exact ih (covers_result admitted covered)

theorem run_labelForms {s : Store O} (run : (step (O := O) policy).toStep.Run s)
    (covered : s.ledger.Covers s.raw.present) (formed : LabelForms s) : LabelForms run.last := by
  induction run with
  | nil => exact formed
  | cons _ a _ ih => exact ih (covers_result a covered) (result_labelForms a covered formed)

theorem result_scopeLinks {s : Store O} {f : Candidate s}
    (admitted : (step (O := O) policy).Admits (s := s) f)
    (covered : s.ledger.Covers s.raw.present) (linked : ScopeLinks s) :
    ScopeLinks ((step (O := O) policy).toStep.result f admitted) := by
  cases checkedPlan : f.plan with
  | none =>
    have impossible := admitted.2.1
    simp [checkedPlan] at impossible
  | some out =>
    rw [routed_result admitted checkedPlan]
    exact update_scopeLinks covered linked admitted.2.2 admitted.1.1.2.2.1 checkedPlan

theorem run_scopeLinks {s : Store O} (run : (step (O := O) policy).toStep.Run s)
    (covered : s.ledger.Covers s.raw.present) (linked : ScopeLinks s) : ScopeLinks run.last := by
  induction run with
  | nil => exact linked
  | cons _ admitted _ ih => exact ih (covers_result admitted covered) (result_scopeLinks admitted covered linked)

/-- Owners and pending parent links are available at every reachable
cut from the actual root encoding. No readiness condition about term
equality or isolation is assumed on the run. -/
theorem reachable_scopeLinks (s : State Tm O) (run : (step (O := O) policy).toStep.Run (start s)) :
    ScopeLinks run.last :=
  run_scopeLinks run (Ledger.root_covers s.present) (start_scopeLinks s)

theorem run_authored_custody {s : Store O}
    (run : (withAuthored policy).Run s)
    (covered : s.ledger.Covers s.raw.present) (linked : ScopeLinks s) (formed : LabelForms s) :
    run.last.ledger.Covers run.last.raw.present ∧ ScopeLinks run.last ∧ LabelForms run.last := by
  induction run with
  | nil => exact ⟨covered, linked, formed⟩
  | cons f admitted _ ih =>
    obtain ⟨prepared, recorded⟩ := (authored_admits_iff policy f).mp admitted
    obtain ⟨tags, plan⟩ := Option.isSome_iff_exists.mp prepared.2.1
    obtain ⟨⟨texts, equations⟩, source⟩ := Option.isSome_iff_exists.mp recorded
    have next := authored_routed_result policy admitted plan source
    apply ih
    · rw [next]
      exact Ledger.covers_advance tags covered
    · rw [next]
      exact (update_scopeLinks covered linked prepared.2.2 prepared.1.1.2.2.1 plan).of_ledger rfl
    · rw [next]
      exact labelForms_update plan prepared.1.1 prepared.2.2 covered formed

/-- The actual initialized root carries a complete authored view and
the physical custody invariant at every reached prefix. -/
theorem reachable_authored (s : State Tm O) (syntaxAt : O → Pattern)
    (encoded : ∀ o ∈ s.present, s.label o = atLoc (ReflUniform.predotU (syntaxAt o)) rootLoc)
    (run : (withAuthored policy).Run (startAuthored s syntaxAt)) :
    AuthoredReads run.last ∧ run.last.ledger.Covers run.last.raw.present ∧
      ScopeLinks run.last ∧ LabelForms run.last := by
  have forms : LabelForms (startAuthored s syntaxAt) := by
    intro slot mark marked
    exact start_labelForms s (fun o live => ⟨_, encoded o live⟩) (slot := slot) (mark := mark) marked
  exact ⟨run_authoredReads policy run (startAuthored_reads s syntaxAt encoded),
    run_authored_custody run (Ledger.root_covers s.present) ((start_scopeLinks s).of_ledger rfl) forms⟩

theorem run_issued_mono {s : Store O} (run : (step (O := O) policy).toStep.Run s) :
    s.issued ⊆ run.last.issued := by
  induction run with
  | nil => exact fun _ h => h
  | cons _ _ _ ih => exact Finset.Subset.trans Finset.subset_union_left ih

private theorem result_old_pending {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) (covered : s.ledger.Covers s.raw.present)
    {slot : O} {t : Ticket O} (issued : t.key ∈ s.issued)
    (pending : ((step (O := O) policy).toStep.result f a).route slot = some (.control t .pending)) :
    s.route slot = some (.control t .pending) := by
  obtain ⟨out, plan⟩ := Option.isSome_iff_exists.mp a.2.1
  rw [routed_result a plan] at pending
  rcases (Ledger.mark_advance_iff out covered a.2.2 a.1.1.2.2.1).mp pending with written | ⟨_, _, kept⟩
  · rcases (routes_ticket_write plan written).2 with ⟨newKey, _, _⟩ | ⟨phase, _⟩
    · exact (Ledger.fresh_not_issued a.2.2 (List.of_mem_zip written).1 (newKey ▸ issued)).elim
    · cases phase
  · exact kept

/-- A pending stamp at an already issued key is a retained ticket, not
a replay of its birth or a phase rollback. This reads back the exact
pending occurrence through any later admitted path. -/
theorem run_old_pending {s : Store O} (run : (step (O := O) policy).toStep.Run s)
    (covered : s.ledger.Covers s.raw.present) {slot : O} {t : Ticket O} (issued : t.key ∈ s.issued)
    (pending : run.last.route slot = some (.control t .pending)) :
    s.route slot = some (.control t .pending) := by
  induction run with
  | nil => exact pending
  | cons _ a _ ih =>
    exact result_old_pending a covered issued
      (ih (covers_result a covered) (Finset.mem_union_left _ issued) pending)

theorem run_done_never_pending {s : Store O} (run : (step (O := O) policy).toStep.Run s)
    (covered : s.ledger.Covers s.raw.present) (linked : ScopeLinks s)
    {slot other : O} {t u : Ticket O} (done : s.route slot = some (.control t .done))
    (same : u.key = t.key) : run.last.route other ≠ some (.control u .pending) := by
  intro future
  have issued : u.key ∈ s.issued := same.symm ▸ linked.keyIssued done
  have prior := run_old_pending run covered issued future
  have slotEq := linked.keyUnique prior done same
  rw [slotEq, done] at prior
  cases prior

private theorem result_retired_key {s : Store O} {f : Candidate s}
    (a : (step (O := O) policy).Admits (s := s) f) (covered : s.ledger.Covers s.raw.present)
    {key : O} (issued : key ∈ s.issued)
    (retired : ∀ ⦃slot t phase⦄, s.route slot = some (.control t phase) → t.key ≠ key) :
    ∀ ⦃slot t phase⦄, ((step (O := O) policy).toStep.result f a).route slot = some (.control t phase) →
      t.key ≠ key := by
  obtain ⟨out, plan⟩ := Option.isSome_iff_exists.mp a.2.1
  rw [routed_result a plan]
  intro slot t phase marked
  rcases (Ledger.mark_advance_iff out covered a.2.2 a.1.1.2.2.1).mp marked with
    written | ⟨_, _, kept⟩
  · rcases (routes_ticket_write plan written).2 with ⟨freshKey, _, _⟩ | ⟨_, _, _, _, prior⟩
    · intro same
      have unused := Ledger.fresh_not_issued a.2.2 (List.of_mem_zip written).1
      exact unused ((same.symm.trans freshKey) ▸ issued)
    · exact retired prior
  · exact retired kept

/-- A key cannot come back once it is issued and no live ticket holds it.
The lifetime is tied to the stamp, not the replaceable token slot. -/
theorem run_retired_key {s : Store O} (run : (step (O := O) policy).toStep.Run s)
    (covered : s.ledger.Covers s.raw.present) {key : O} (issued : key ∈ s.issued)
    (retired : ∀ ⦃slot t phase⦄, s.route slot = some (.control t phase) → t.key ≠ key) :
    ∀ ⦃slot t phase⦄, run.last.route slot = some (.control t phase) → t.key ≠ key := by
  induction run with
  | nil => exact retired
  | cons _ admitted _ ih =>
    exact ih (covers_result admitted covered) (Finset.mem_union_left _ issued)
      (result_retired_key admitted covered issued retired)

end RoutingResults

/-- Forget only the extra custody information. Every actual routed
firing, not just its output bag, is a firing of the unchanged base
program at the same frame. The converse fails at the cross-close. -/
def forgetRun {s : Store O} : (step (O := O)).toStep.Run s →
    (RuleSyntax.step QN O QNE located).toStep.Run s.raw
  | .nil _ => .nil _
  | .cons candidate admitted rest => .cons candidate.raw admitted.1 (forgetRun rest)

theorem forgetRun_last {s : Store O} (run : (step (O := O)).toStep.Run s) :
    (forgetRun run).last = run.last.raw := by
  induction run with
  | nil => rfl
  | cons _ _ _ ih => exact ih

end Ownership

#print axioms check_fails_pending
#print axioms check_fails_done
#print axioms made_not_pending_first
#print axioms made_not_pending_second
#print axioms made_not_done_first
#print axioms token_kept_first
#print axioms step_reads_token
#print axioms pending_phase_step
#print axioms done_phase_step
#print axioms close_refused_before_step
#print axioms done_run
#print axioms pending_run
#print axioms at_most_one_step
#print axioms exactly_one_before_close
#print axioms child_comm_admitted
#print axioms child_steps_once
#print axioms nameLaws_pReflect_iff
#print axioms child_close_admitted
#print axioms child_closes_once
#print axioms pendingOnly_phase
#print axioms doneOnly_phase
#print axioms located_cases
#print axioms produce_shapes
#print axioms take_shapes
#print axioms read_shapes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflLocatedStep
