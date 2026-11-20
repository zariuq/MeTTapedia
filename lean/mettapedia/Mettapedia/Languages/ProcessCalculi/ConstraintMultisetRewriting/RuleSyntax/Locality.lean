import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Permissions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.CheckAccepts

/-!
# What the step of a program excludes: locality, determined knowledge, finite selections

The interface admits every transition system with refining knowledge (`realizable_iff`). The step of
a program does not. Its admission reads the store only through its regions.

## Locality

The **regions** of a firing are its taken, read and made identities and, at each solution of its
information, the rows that a solution equates with one of its query patterns (the none query and count
patterns of its checks and its collect patterns, `Firing.queryPatterns`). A change of the present rows
**outside the regions** (`OutsideRegions`) keeps the taken, read and made identities as they were and
touches only rows that no solution of the information equates with a query pattern.

* **`admits_of_outsideRegions`**: a firing admitted at a state is admitted after any change outside
  its regions that keeps its opening fresh; with freshness at both states, `admits_iff_of_outsideRegions`.
* Control (query regions count, `Controls.row_in_region_refused`, `Controls.row_outside_admitted`): the
  none queries of `9` is admitted with a row `x` bound to `5`; adding a row labelled `9` (inside the region)
  refuses it, while adding a second row labelled `x` (outside the region at every solution, though its
  label is an unknown) keeps it admitted.
* Control (an instance of the interface whose admission is not local, `Controls.nonlocal_restriction`):
  restricting the step to states without row `7` gives an instance of the interface whose admission
  changes when row `7`, outside every region, is added. By locality no step of a program does this.
* **Rights are local** (`permitted_admits_of_outsideRegions`): permissions restrict the step by a
  predicate on the selected identities and their handles, so the permitted step of a program is local
  too. They do not see predicate queries (`Controls.none_without_rights_permitted`): with no right
  at all, a none query is permitted, since the permission checks the selection's commit, which carries
  no query.

## The knowledge of a result, by definition

`result_knowledge` (proved by `rfl`): the result's knowledge is the state's knowledge carried along
the extension, the take and
read equations of the opened rule with the labels of the selected rows, and the opened tells. It does
not depend on the present rows (`result_knowledge_present`). Control
(`Controls.knowledge_reads_selected_labels`): it depends on the labels of the selected rows.

## Finitely many selections

`selections_finite`: at a finite store, for one rule, one extension, one opening and one choice of
made identities, the admitted firings are finitely many (their taken and read lists range over the
present rows and each collect query sees a subset of them). The remaining freedom of a firing is the choice
of fresh made identities and of a fresh opening, which no admission can observe beyond freshness.
Control (`Controls.made_choices_infinite`): without fixing the made identities, the token firing is
admitted with every identity other than the taken one, so infinitely many firings are admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc

/-- The pattern whose region a check reads, if it is a query. -/
def checkRegion {T : Type uT} : Check T → Option T
  | .equal _ _ => none
  | .predicate _ pattern => some pattern
  | .count pattern _ => some pattern

/-- Each element of the right list is paired in the zip of lists of one length. -/
theorem exists_mem_zip_right {α : Type uT} {β : Type uOcc} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length → ∀ b ∈ l₂, ∃ a, (a, b) ∈ l₁.zip l₂
  | [], [], _, _, inside => by cases inside
  | [], _ :: _, lengths, _, _ => by simp at lengths
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | a :: as, b' :: bs, lengths, b, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨a, List.mem_cons_self⟩
      · obtain ⟨a', paired⟩ := exists_mem_zip_right as bs (Nat.succ.inj lengths) b later
        exact ⟨a', List.mem_cons_of_mem _ paired⟩

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

section Locality

variable {X : Frames Tm Hom} {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **The query patterns of a firing**: the opened none queries and count patterns and collect patterns. -/
def Firing.queryPatterns (X : Frames Tm Hom) {a : Obj} (f : Firing O E P a) :
    List (Tm (E.target f.ext)) :=
  (f.opened X).checks.filterMap checkRegion ++ f.collectOpened X

/-- The state with other present rows. -/
def State.withPresent (s : State Tm O) (W : Finset O) : State Tm O :=
  ⟨s.frame, s.knowledge, W, s.label⟩

/-- **A change of the present rows outside a firing's regions**: its taken, read and made identities
are present exactly as before, and no solution of its information equates a changed row with one of
its query patterns. -/
structure OutsideRegions (X : Frames Tm Hom) (s : State Tm O) (W : Finset O)
    (f : Firing O E P s.frame) : Prop where
  touched : ∀ o, (o ∈ f.selection.taken ∨ o ∈ f.selection.read ∨ o ∈ f.selection.made) →
    (o ∈ s.present ↔ o ∈ W)
  queries : ∀ (b : Obj) (σ : Hom (E.target f.ext) b), X.Models σ (f.information X s) →
    ∀ p ∈ f.queryPatterns X, ∀ o, ¬ (o ∈ s.present ↔ o ∈ W) →
      ¬ X.E (X.act σ p) (X.act σ (f.row X s o))

theorem matchesAt_congr (X : Frames Tm Hom) {a b : Obj} (σ : Hom a b) (row : O → Tm a)
    {W W' : Finset O} (p : Tm a)
    (apart : ∀ o, ¬ (o ∈ W ↔ o ∈ W') → ¬ X.E (X.act σ p) (X.act σ (row o))) :
    matchesAt X σ row W p = matchesAt X σ row W' p := by
  ext o
  rw [mem_matchesAt, mem_matchesAt]
  by_cases same : o ∈ W ↔ o ∈ W'
  · rw [same]
  · constructor
    · rintro ⟨-, equated⟩
      exact absurd equated (apart o same)
    · rintro ⟨-, equated⟩
      exact absurd equated (apart o same)

theorem checkHolds_congr (X : Frames Tm Hom) {a b : Obj} (σ : Hom a b) (row : O → Tm a)
    {W W' : Finset O} (c : Check (Tm a))
    (apart : ∀ p, checkRegion c = some p → ∀ o, ¬ (o ∈ W ↔ o ∈ W') →
      ¬ X.E (X.act σ p) (X.act σ (row o))) :
    checkHolds X σ row W c ↔ checkHolds X σ row W' c := by
  cases c with
  | equal left right => exact Iff.rfl
  | predicate quantifier pattern =>
      rw [checkHolds_predicate_iff, checkHolds_predicate_iff,
        matchesAt_congr X σ row pattern (apart pattern rfl)]
  | count pattern number =>
      show (matchesAt X σ row W pattern).card = number ↔ (matchesAt X σ row W' pattern).card = number
      rw [matchesAt_congr X σ row pattern (apart pattern rfl)]

variable [DecidableEq O]

omit [DecidableEq O] in
/-- The guard predicate agrees at every solution of the information, after a change outside the
regions. -/
theorem holds_iff_of_outsideRegions {s : State Tm O} {W : Finset O} {f : Firing O E P s.frame}
    (outside : OutsideRegions X s W f) {b : Obj} {σ : Hom (E.target f.ext) b}
    (solved : X.Models σ (f.information X s)) :
    f.Holds X s σ ↔ f.Holds X (s.withPresent W) σ := by
  unfold Firing.Holds
  apply and_congr
  · apply forall₂_congr
    intro c member
    apply checkHolds_congr X σ (f.row X s) c
    intro p region o changed
    exact outside.queries b σ solved p
      (List.mem_append_left _ (List.mem_filterMap.mpr ⟨c, member, region⟩)) o changed
  · apply forall₂_congr
    intro q member
    have inside : q.1 ∈ f.collectOpened X := (List.of_mem_zip member).1
    show matchesAt X σ (f.row X s) s.present q.1 = q.2 ↔ matchesAt X σ (f.row X s) W q.1 = q.2
    rw [matchesAt_congr X σ (f.row X s) q.1
      (fun o changed => outside.queries b σ solved q.1 (List.mem_append_right _ inside) o changed)]

theorem enabled_iff_of_outsideRegions {s : State Tm O} {W : Finset O} {f : Firing O E P s.frame}
    (outside : OutsideRegions X s W f) :
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ↔
      Enabled (fun _ : O => ()) W (f.selection.commit (T := Unit)) := by
  have taken : ∀ o ∈ f.selection.taken, (o ∈ s.present ↔ o ∈ W) :=
    fun o member => outside.touched o (Or.inl member)
  have read : ∀ o ∈ f.selection.read, (o ∈ s.present ↔ o ∈ W) :=
    fun o member => outside.touched o (Or.inr (Or.inl member))
  have made : ∀ o ∈ f.selection.made, (o ∈ s.present ↔ o ∈ W) :=
    fun o member => outside.touched o (Or.inr (Or.inr member))
  constructor
  · intro enabled
    refine ⟨fun o member => ?_, fun o member => ?_, enabled.apart, ?_, fun q member => ?_⟩
    · have list : o ∈ f.selection.taken := by simpa [Selection.commit] using member
      exact (taken o list).mp (enabled.taken_subset member)
    · have list : o ∈ f.selection.read := by simpa [Selection.commit] using member
      exact (read o list).mp (enabled.kept_subset member)
    · rw [Finset.disjoint_left]
      intro o member present
      have list : o ∈ f.selection.made := by simpa [Selection.commit] using member
      exact Finset.disjoint_left.mp enabled.fresh member ((made o list).mpr present)
    · simp [Selection.commit] at member
  · intro enabled
    refine ⟨fun o member => ?_, fun o member => ?_, enabled.apart, ?_, fun q member => ?_⟩
    · have list : o ∈ f.selection.taken := by simpa [Selection.commit] using member
      exact (taken o list).mpr (enabled.taken_subset member)
    · have list : o ∈ f.selection.read := by simpa [Selection.commit] using member
      exact (read o list).mpr (enabled.kept_subset member)
    · rw [Finset.disjoint_left]
      intro o member present
      have list : o ∈ f.selection.made := by simpa [Selection.commit] using member
      exact Finset.disjoint_left.mp enabled.fresh member ((made o list).mp present)
    · simp [Selection.commit] at member

/-- **Locality.** A firing admitted at a state is admitted after any change of the present rows
outside its regions that keeps its opening fresh. -/
theorem admits_of_outsideRegions {s : State Tm O} {W : Finset O} {f : Firing O E P s.frame}
    (admitted : (step X O E P).Admits (s := s) f) (outside : OutsideRegions X s W f)
    (fresh : f.Fresh X (s.withPresent W)) :
    (step X O E P).Admits (s := s.withPresent W) f := by
  obtain ⟨⟨-, shapes⟩, enabled, solvable, asks⟩ := admitted
  refine ⟨⟨fresh, shapes⟩, (enabled_iff_of_outsideRegions outside).mp enabled, solvable, ?_⟩
  intro b σ solved
  exact (holds_iff_of_outsideRegions outside solved).mp (asks b σ solved)

/-- **Locality, both ways**, when the opening is fresh at both states. -/
theorem admits_iff_of_outsideRegions {s : State Tm O} {W : Finset O} {f : Firing O E P s.frame}
    (outside : OutsideRegions X s W f) (fresh : f.Fresh X s) (fresh' : f.Fresh X (s.withPresent W)) :
    (step X O E P).Admits (s := s) f ↔ (step X O E P).Admits (s := s.withPresent W) f := by
  constructor
  · exact fun admitted => admits_of_outsideRegions admitted outside fresh'
  · rintro ⟨⟨-, shapes⟩, enabled, solvable, asks⟩
    refine ⟨⟨fresh, shapes⟩, (enabled_iff_of_outsideRegions outside).mpr enabled, solvable, ?_⟩
    intro b σ solved
    exact (holds_iff_of_outsideRegions outside solved).mpr (asks b σ solved)

/-- **Rights are local**: the permitted step of a program is local as well. -/
theorem permitted_admits_of_outsideRegions {H : Type*} (space : O → H)
    (Γ : MeTTaCalculus.InteractionTypes.Rights H) {s : State Tm O} {W : Finset O}
    {f : Firing O E P s.frame}
    (admitted : (Permissions.permitted (step X O E P).toStep space Γ).Admits (s := s) f)
    (outside : OutsideRegions X s W f) (fresh : f.Fresh X (s.withPresent W)) :
    (Permissions.permitted (step X O E P).toStep space Γ).Admits (s := s.withPresent W) f :=
  ⟨admits_of_outsideRegions admitted.1 outside fresh, admitted.2⟩

/-! ## The knowledge of a result -/

omit [DecidableEq O] in
/-- **The knowledge of a result, by definition**: the state's knowledge along the extension, the
opened take and read equations with the labels of the selected rows, and the opened tells. -/
theorem result_knowledge (s : State Tm O) (f : Firing O E P s.frame) [DecidableEq O] :
    (f.result X s).knowledge =
      X.applyStore (E.weaken f.ext) s.knowledge ++
        (f.opened X).take.zipWith (fun p o => (p, X.act (E.weaken f.ext) (s.label o)))
          f.selection.taken ++
        (f.opened X).read.zipWith (fun p o => (p, X.act (E.weaken f.ext) (s.label o)))
          f.selection.read ++
        (f.opened X).tell := rfl

/-- **It does not depend on the present rows.** -/
theorem result_knowledge_present (s : State Tm O) (W : Finset O) (f : Firing O E P s.frame) :
    (f.result X (s.withPresent W)).knowledge = (f.result X s).knowledge := rfl

end Locality

/-! ## Finitely many selections -/

section Finite

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- The firings of one rule, extension, opening and choice of made identities. -/
def sameChoice {a : Obj} (f : Firing O E P a) (g : Firing O E P a) : Prop :=
  g.rule = f.rule ∧ HEq g.ext f.ext ∧ HEq g.opening f.opening ∧ g.selection.made = f.selection.made

/-- **Finitely many selections**: at a finite store, the admitted firings with one rule, extension,
opening and choice of made identities form a finite set. -/
theorem selections_finite (s : State Tm O) (f : Firing O E P s.frame) :
    {g : Firing O E P s.frame | sameChoice f g ∧ (step X O E P).Admits (s := s) g}.Finite := by
  classical
  let lists : Set (List O) := {l | ∀ o ∈ l, o ∈ s.present}
  have bounded : ∀ n, {l : List O | l.length = n ∧ ∀ o ∈ l, o ∈ s.present}.Finite := fun n =>
    LogicOverTheStep.ProgramAdequacy.listsOver_finite s.present n
  let seenSets : Set (List (Finset O)) :=
    {l | l.length = f.rule.collect.length ∧ ∀ x ∈ l, x ∈ s.present.powerset}
  have seenFinite : seenSets.Finite := by
    have := (List.finite_length_eq (s.present.powerset) f.rule.collect.length)
    refine (this.image (List.map Subtype.val)).subset ?_
    rintro l ⟨length, inside⟩
    refine ⟨l.attach.map fun x => ⟨x.1, inside x.1 x.2⟩, by simp [length], ?_⟩
    simp
  let key : Firing O E P s.frame → List O × List O × List (Finset O) :=
    fun g => (g.selection.taken, g.selection.read, g.seen)
  have injective : Set.InjOn key {g | sameChoice f g ∧ (step X O E P).Admits (s := s) g} := by
    rintro ⟨r, member, x, ι, ⟨taken, read, made⟩, seen⟩ ⟨⟨rfl, hx, hι, hmade⟩, -⟩
      ⟨r', member', x', ι', ⟨taken', read', made'⟩, seen'⟩ ⟨⟨rfl, hx', hι', hmade'⟩, -⟩ same
    simp only [key, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    simp only at hmade hmade' hx hx' hι hι'
    subst hmade hmade'
    have : x = x' := eq_of_heq (hx.trans hx'.symm)
    subst this
    have : ι = ι' := eq_of_heq (hι.trans hι'.symm)
    subst this
    rfl
  refine Set.Finite.of_finite_image ?_ injective
  refine (((bounded f.rule.body.take.length).prod
    ((bounded f.rule.body.read.length).prod seenFinite))).subset ?_
  rintro ⟨taken, read, seen⟩ ⟨g, ⟨⟨rule, -, -, -⟩, admitted⟩, image⟩
  simp only [key, Prod.mk.injEq] at image
  obtain ⟨rfl, rfl, rfl⟩ := image
  obtain ⟨-, ⟨-, -, take, readLength, -, collect⟩, enabled, ⟨b, σ, solved⟩, -, asks⟩ :=
    (admits_iff g).mp admitted
  have takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (List.mem_toFinset.mpr member)
  have readPresent : ∀ o ∈ g.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (List.mem_toFinset.mpr member)
  have seenPresent : ∀ seenSet ∈ g.seen, seenSet ∈ s.present.powerset := by
    intro seenSet member
    have lengths : (g.collectOpened X).length = g.seen.length := by
      rw [← collect]
      exact List.length_map _
    obtain ⟨p, paired⟩ := exists_mem_zip_right _ _ lengths seenSet member
    have sees : matchesAt X σ (g.row X s) s.present p = seenSet := asks _ paired b σ solved
    rw [Finset.mem_powerset, ← sees]
    intro o inside
    exact ((mem_matchesAt X σ (g.row X s) s.present p o).mp inside).1
  have takeLength : g.selection.taken.length = f.rule.body.take.length := by rw [← take, rule]
  have readLength' : g.selection.read.length = f.rule.body.read.length := by rw [← readLength, rule]
  have seenLength : g.seen.length = f.rule.collect.length := by rw [← collect, rule]
  exact ⟨⟨takeLength, takenPresent⟩, ⟨readLength', readPresent⟩, seenLength, seenPresent⟩

end Finite

end Generic

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.LP
open Examples (Tm X E x c demo noNineFiring guardAt everywhere fresh_of_ground noNine)
open OneFrame (frames ext)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- Row `1` is labelled `9`; every other row is labelled by the unknown `x`. -/
def nineAtOne (o : ℕ) : Term atoms := if o = 1 then c 9 else x

/-- The request row `0` with `x` bound to `5`. -/
def base : State Tm ℕ := ⟨PUnit.unit, [(x, c 5)], {0}, nineAtOne⟩

theorem base_fresh (W : Finset ℕ) : Firing.Fresh X (base.withPresent W) noNineFiring := by
  apply fresh_of_ground action _ noNineFiring
  intro t member σ
  simp only [noNineFiring, noNine, Rule.terms, checkTerms, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append, List.append_nil, List.mem_singleton] at member
  subst member
  rfl

theorem base_information (W : Finset ℕ) :
    noNineFiring.information X (base.withPresent W) = [(x, c 5)] := rfl

/-- The none query of `9` at the given rows, with `x` bound to `5`. -/
theorem none_admitted_iff (W : Finset ℕ) :
    (step X ℕ E demo).Admits (s := base.withPresent W) noNineFiring ↔ 1 ∉ W := by
  rw [admits_iff]
  constructor
  · rintro ⟨-, -, -, -, checks, -⟩ present
    have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (everywhere 5)
        (noNineFiring.information X (base.withPresent W)) := by
      rw [base_information]
      intro e inside
      rw [List.mem_singleton] at inside
      subst inside
      rfl
    exact checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit _ solved 1 present rfl
  · intro missing
    refine ⟨base_fresh W, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_,
      ⟨PUnit.unit, everywhere 5, ?_⟩, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [noNineFiring, Selection.commit]
    · rw [base_information]
      intro e inside
      rw [List.mem_singleton] at inside
      subst inside
      rfl
    · intro check inside b σ solved
      rw [base_information] at solved
      have bound : σ 0 = c 5 := solved (x, c 5) List.mem_cons_self
      simp only [noNineFiring, noNine, Firing.opened, RuleInstance.map, List.map_cons,
        List.map_nil, Check.map, List.mem_singleton] at inside
      subst inside
      intro o present equated
      have other : o ≠ 1 := fun same => missing (same ▸ present)
      have nine : (c 9 : Term atoms) = σ 0 := by
        have h : (c 9 : Term atoms) =
            Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (nineAtOne o)) := equated
        rw [nineAtOne, if_neg other] at h
        exact h
      rw [bound] at nine
      exact absurd (Term.const.inj nine) (by decide)
    · intro q inside
      simp [noNineFiring, noNine, Firing.collectOpened] at inside

/-- **A row inside the region refuses the none query.** -/
theorem row_in_region_refused :
    (step X ℕ E demo).Admits (s := base.withPresent {0}) noNineFiring ∧
      ¬ (step X ℕ E demo).Admits (s := base.withPresent {0, 1}) noNineFiring :=
  ⟨(none_admitted_iff {0}).mpr (by decide), fun admitted =>
    (none_admitted_iff {0, 1}).mp admitted (by decide)⟩

/-- **A row outside the region at every solution keeps it admitted**, though its label is an unknown;
this is locality applied to row `2`. -/
theorem row_outside_admitted :
    OutsideRegions X (base.withPresent {0}) {0, 2} noNineFiring ∧
      (step X ℕ E demo).Admits (s := (base.withPresent {0}).withPresent {0, 2}) noNineFiring := by
  have outside : OutsideRegions X (base.withPresent {0}) {0, 2} noNineFiring := by
    refine ⟨fun o member => ?_, fun b σ solved p inside o changed => ?_⟩
    · simp [noNineFiring] at member
    · rw [base_information] at solved
      have bound : σ 0 = c 5 := solved (x, c 5) List.mem_cons_self
      have two : o = 2 := by
        by_contra other
        apply changed
        simp only [State.withPresent, Finset.mem_insert, Finset.mem_singleton]
        omega
      subst two
      simp only [Firing.queryPatterns, noNineFiring, noNine, Firing.opened, RuleInstance.map,
        List.map_cons, List.map_nil, Check.map, List.filterMap_cons, checkRegion,
        List.filterMap_nil, Firing.collectOpened, List.append_nil, List.mem_singleton] at inside
      subst inside
      intro equated
      have nine : (c 9 : Term atoms) = σ 0 := equated
      rw [bound] at nine
      exact absurd (Term.const.inj nine) (by decide)
  exact ⟨outside, admits_of_outsideRegions ((none_admitted_iff {0}).mpr (by decide)) outside
    (base_fresh {0, 2})⟩

/-- **An instance of the interface whose admission is not local**: the step restricted to states
without row `7`. Adding row `7`, outside every region of the none firing, refuses it. -/
theorem nonlocal_restriction :
    let nonlocal := Spaces.restrict (step X ℕ E demo).toStep (fun {s} _ => 7 ∉ s.present)
    OutsideRegions X (base.withPresent {0}) {0, 7} noNineFiring ∧
      nonlocal.Admits (s := base.withPresent {0}) noNineFiring ∧
      ¬ nonlocal.Admits (s := (base.withPresent {0}).withPresent {0, 7}) noNineFiring := by
  intro nonlocal
  refine ⟨⟨fun o member => ?_, fun b σ solved p inside o changed => ?_⟩,
    ⟨(none_admitted_iff {0}).mpr (by decide), by decide⟩, fun admitted => admitted.2 (by decide)⟩
  · simp [noNineFiring] at member
  · rw [base_information] at solved
    have bound : σ 0 = c 5 := solved (x, c 5) List.mem_cons_self
    have seven : o = 7 := by
      by_contra other
      apply changed
      simp only [State.withPresent, Finset.mem_insert, Finset.mem_singleton]
      omega
    subst seven
    simp only [Firing.queryPatterns, noNineFiring, noNine, Firing.opened, RuleInstance.map,
      List.map_cons, List.map_nil, Check.map, List.filterMap_cons, checkRegion,
      List.filterMap_nil, Firing.collectOpened, List.append_nil, List.mem_singleton] at inside
    subst inside
    intro equated
    have nine : (c 9 : Term atoms) = σ 0 := equated
    rw [bound] at nine
    exact absurd (Term.const.inj nine) (by decide)

/-- **Rights do not see predicate queries**: with no right at all, the none query of `9` is still
permitted and admitted, because the permission of the tree checks the selection's commit, which
carries no query, so its `observe` clause is never asked. -/
theorem none_without_rights_permitted :
    (Permissions.permitted (step X ℕ E demo).toStep (fun _ : ℕ => (0 : ℕ))
      (fun _ _ => false)).Admits (s := Examples.boundRequest) noNineFiring := by
  refine ⟨Examples.noNine_admitted_when_bound, ⟨fun o member => ?_, fun o member => ?_,
    fun o member => ?_, fun q member => ?_⟩⟩
  · change o ∈ ([] : List ℕ).toFinset at member
    simp at member
  · change o ∈ ([] : List ℕ).toFinset at member
    simp at member
  · change o ∈ ([] : List ℕ).toFinset at member
    simp at member
  · simp [noNineFiring, Selection.commit] at member

/-- The token firing, making identity `n`. -/
def consumeAt (n : ℕ) : Firing ℕ E demo PUnit.unit :=
  ⟨Examples.consume, Or.inl rfl, PUnit.unit, Subst.id atoms, ⟨[0], [], [n]⟩, []⟩

theorem consumeAt_admitted (n : ℕ) (fresh : n ≠ 0) :
    (step X ℕ E demo).Admits (s := Examples.tokenState) (consumeAt n) := by
  refine (admits_iff (consumeAt n)).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_singleton n, rfl,
    rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply fresh_of_ground action Examples.tokenState (consumeAt n)
    intro t member σ
    simp only [consumeAt, Examples.consume, Rule.terms, List.map_nil, List.flatMap_nil,
      List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [consumeAt, Examples.tokenState, Selection.commit, fresh]
  · have known : (consumeAt n).information X Examples.tokenState = [(c 1, c 1)] := rfl
    rw [known]
    exact ⟨PUnit.unit, Subst.id atoms, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · intro check member
    simp [consumeAt, Examples.consume, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [consumeAt, Examples.consume, Firing.collectOpened] at member

/-- **Without fixing the made identities, the admitted firings are infinitely many**: every
identity other than the taken one can be made. So `selections_finite` needs its hypotheses. -/
theorem made_choices_infinite :
    {g : Firing ℕ E demo PUnit.unit | (step X ℕ E demo).Admits (s := Examples.tokenState) g}.Infinite := by
  have injective : Function.Injective fun n : ℕ => consumeAt (n + 1) := by
    intro n m same
    have made := congrArg (fun g : Firing ℕ E demo PUnit.unit => g.selection.made) same
    simp only [consumeAt, List.cons.injEq, and_true] at made
    omega
  exact Set.infinite_of_injective_forall_mem injective fun n =>
    consumeAt_admitted (n + 1) (Nat.succ_ne_zero n)

/-- **The knowledge reads the labels of the selected rows**: the same read firing on a row labelled
`x` and on a row labelled `7` leaves different knowledge. -/
theorem knowledge_reads_selected_labels :
    (Examples.answerFiring.result X Examples.openRequest).knowledge ≠
      (Examples.answerFiring.result X (⟨PUnit.unit, [], {0}, fun _ => c 7⟩ : State Tm ℕ)).knowledge := by
  intro same
  have left : (Examples.answerFiring.result X Examples.openRequest).knowledge =
      [(.var 1, x), (.var 1, c 5)] := rfl
  have right : (Examples.answerFiring.result X (⟨PUnit.unit, [], {0}, fun _ => c 7⟩ : State Tm ℕ)).knowledge =
      [(.var 1, c 7), (.var 1, c 5)] := rfl
  rw [left, right] at same
  simp [x, c] at same

end Controls

#print axioms admits_of_outsideRegions
#print axioms admits_iff_of_outsideRegions
#print axioms permitted_admits_of_outsideRegions
#print axioms result_knowledge
#print axioms result_knowledge_present
#print axioms selections_finite
#print axioms Controls.row_in_region_refused
#print axioms Controls.row_outside_admitted
#print axioms Controls.nonlocal_restriction
#print axioms Controls.knowledge_reads_selected_labels
#print axioms Controls.made_choices_infinite
#print axioms Controls.none_without_rights_permitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
