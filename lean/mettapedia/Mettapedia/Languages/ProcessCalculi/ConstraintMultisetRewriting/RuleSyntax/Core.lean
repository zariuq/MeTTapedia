import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Universality

/-!
# A one-match step of constraint multiset rewriting, as rule syntax

Over a frame action (`Interface.Frames`) with its extensions, this module defines one step of
constraint multiset rewriting whose admission is computed from syntax. Its choices:

* the store is a bag of occurrences;
* a firing is one match: one rule, one opening, one selection;
* a firing's guards are asked at every solution of its information, which includes its own tells;
* the program is a fixed set of rules beside the store;
* there is one store of knowledge.

Each choice is one option among others studied beside it: bags of matches in `JointFirings`,
rules held by the state in `RuleOccurrences`, knowledge located at worlds in `Worlds`, guards asked
before the tells in `TellDependentGuards`. Nothing here says which options are right.

## Syntax

* **Extensions** (`Extensions`): how a firing may extend a frame by fresh unknowns. Each extension
  of a frame `a` reaches a frame and comes with the weakening from `a`. At one frame the only
  extension is the identity (`Extensions.identity`); at declaration families it adds names; at
  dependent telescopes it adds helpers.
* **A rule** (`Rule`) has its own frame of schematic unknowns and, at that frame, take patterns,
  read patterns, told equations, checks (equation guards, predicate queries and count aggregates:
  the tree's `Check`), made rows, and collect patterns. The body is the tree's `RuleInstance` at the rule's own
  frame. A **program** is a set of rules.
* **A state** (`State`) is a frame, its knowledge, the present occurrences, and their labels, terms at
  the frame.
* **A firing** of a program at a frame (`Firing`) is a rule of the program, an extension of the frame,
  an **opening** of the rule's unknowns into the extended frame, a selection of occurrences (taken,
  read, made), and for each collect pattern the set of rows it claims to see.

## What is derived

From these alone (`Firing.opened`, `Firing.information`, `Firing.Fresh`, `Firing.Shapes`,
`Firing.Holds`, `Firing.Admits`, `Firing.result`):

* the **opened rule**: the rule's body along the opening;
* the **information**: the knowledge carried along the extension, the equations of each opened take
  and read pattern with the label of its selected row read at the extended frame, and the opened tells;
* **freshness** of the opening: any instantiation of the state's frame and any instantiation of the
  rule's unknowns are realized together, on the terms the state mentions and the terms of the rule.
  At one frame, on first-order terms, an opening that renames the rule's unknown apart from the
  state's is fresh (`Examples.answer_fresh`) and one that captures the state's unknown is not
  (`Examples.capture_not_fresh`); at declaration frames the canonical opening is fresh at every state,
  by the coproduct property (`Contextual.canonical_fresh`);
* the **shapes**: freshness, distinct takes and made identities, one row per pattern, one made row per
  made identity, one seen set per collect pattern;
* the **guard predicate** at a solution: every opened check holds there, predicate queries and counts read
  through the solution, and each collect pattern sees exactly its claimed rows;
* **admission**: the shapes, the enabling of the selection, solvability of the information, and the
  guard predicate at every solution of the information;
* the **result**: the extended frame, the information as knowledge, the fired occurrences, and made
  identities labelled by the opened made rows.

`step X O E P` is then an `Interface.Step.Standard` whose admission is this derived predicate
(`admits_iff`); it is supplied by no field. Takes and reads constrain (`take_solved`, `read_solved`),
and the result carries the opened made rows (`result_label_made`, `result_label_other`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Syntax -/

/-- **How a firing may extend a frame**: the extensions of each frame, each with the frame it reaches
and the weakening into it. -/
structure Extensions (Hom : Obj → Obj → Type uH) where
  Ext : Obj → Type uE
  target : {a : Obj} → Ext a → Obj
  weaken : {a : Obj} → (x : Ext a) → Hom a (target x)

/-- The extensions that add nothing: a firing moves along the identity. -/
def Extensions.identity (X : Frames Tm Hom) : Extensions.{uO, uH, uE} Hom where
  Ext _ := PUnit
  target {a} _ := a
  weaken {a} _ := X.id a

/-- **A rule**: its own frame of schematic unknowns, and at that frame its take and read patterns,
told equations, checks (guards, predicate queries and count aggregates), made rows (the tree's
`RuleInstance`),
and its collect patterns. -/
structure Rule (Tm : Obj → Type uT) where
  locals : Obj
  body : RuleInstance (Tm locals)
  collect : List (Tm locals)

/-- **A program** is a set of rules. -/
abbrev Program (Tm : Obj → Type uT) := Set (Rule Tm)

/-- **A state**: a frame, its knowledge, the present occurrences, and their labels at the frame. -/
structure State (Tm : Obj → Type uT) (O : Type uOcc) where
  frame : Obj
  knowledge : EquationStore (Tm frame)
  present : Finset O
  label : O → Tm frame

/-- **A firing of a program at a frame**: a rule of the program, an extension of the frame, an opening
of the rule's unknowns into the extended frame, a selection of occurrences, and the set of rows each
collect pattern claims to see. -/
structure Firing (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom) (P : Program Tm) (a : Obj) where
  rule : Rule Tm
  member : rule ∈ P
  ext : E.Ext a
  opening : Hom rule.locals (E.target ext)
  selection : Selection O
  seen : List (Finset O)

/-- The terms a check mentions. -/
def checkTerms {T : Type uT} : Check T → List T
  | .equal left right => [left, right]
  | .predicate _ pattern => [pattern]
  | .count pattern _ => [pattern]

/-- Every term of a rule. -/
def Rule.terms (r : Rule Tm) : List (Tm r.locals) :=
  r.body.take ++ r.body.read ++ r.body.tell.map Prod.fst ++ r.body.tell.map Prod.snd ++
    r.body.checks.flatMap checkTerms ++ r.body.produce ++ r.collect

/-- The terms a state mentions: its knowledge and the labels of its present rows. -/
def State.Mentions {O : Type uOcc} (s : State Tm O) (t : Tm s.frame) : Prop :=
  t ∈ s.knowledge.map Prod.fst ∨ t ∈ s.knowledge.map Prod.snd ∨ ∃ o ∈ s.present, s.label o = t

/-! ## Checks at a solution -/

section Checks

variable (X : Frames Tm Hom) {O : Type uOcc}

/-- The present rows a solution equates with a pattern. -/
noncomputable def matchesAt {a b : Obj} (σ : Hom a b) (row : O → Tm a) (present : Finset O)
    (pattern : Tm a) : Finset O := by
  classical
  exact present.filter fun o => X.E (X.act σ pattern) (X.act σ (row o))

theorem mem_matchesAt {a b : Obj} (σ : Hom a b) (row : O → Tm a) (present : Finset O)
    (pattern : Tm a) (o : O) :
    o ∈ matchesAt X σ row present pattern ↔ o ∈ present ∧ X.E (X.act σ pattern) (X.act σ (row o)) := by
  classical
  unfold matchesAt
  convert Finset.mem_filter

/-- **A check at a solution**: an equation guard holds, the predicate query's quantifier holds of the
present rows matching its pattern, or exactly the counted number of present rows match. Rows are read
through the solution. -/
def checkHolds {a b : Obj} (σ : Hom a b) (row : O → Tm a) (present : Finset O) : Check (Tm a) → Prop
  | .equal left right => X.E (X.act σ left) (X.act σ right)
  | .predicate q pattern => q.Holds present fun o => X.E (X.act σ pattern) (X.act σ (row o))
  | .count pattern number => (matchesAt X σ row present pattern).card = number

/-- The predicate query `none` is the count zero. -/
theorem none_iff_count_zero {a b : Obj} (σ : Hom a b) (row : O → Tm a) (present : Finset O)
    (pattern : Tm a) :
    checkHolds X σ row present (.predicate .none pattern) ↔
      checkHolds X σ row present (.count pattern 0) := by
  simp only [checkHolds, Quantifier.holds_none, Finset.card_eq_zero]
  constructor
  · intro none
    ext o
    simp only [mem_matchesAt, Finset.notMem_empty, iff_false, not_and]
    exact none o
  · intro empty o present' equated
    have inside : o ∈ matchesAt X σ row present pattern := (mem_matchesAt X σ row present pattern o).mpr
      ⟨present', equated⟩
    rw [empty] at inside
    exact Finset.notMem_empty o inside

end Checks

/-! ## What a firing determines -/

/-- Relabel the made identities by the made rows, in order; every other identity keeps its label. -/
def relabel {O : Type uOcc} [DecidableEq O] {a : Obj} (old : O → Tm a) :
    List O → List (Tm a) → O → Tm a
  | o' :: rest, t :: ts, o => if o = o' then t else relabel old rest ts o
  | _, _, o => old o

namespace Firing

section Opening

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  {a : Obj} (f : Firing O E P a)

/-- The rule's body along the opening, at the extended frame. -/
def opened : RuleInstance (Tm (E.target f.ext)) := f.rule.body.map (X.act f.opening)

/-- The collect patterns along the opening. -/
def collectOpened : List (Tm (E.target f.ext)) := f.rule.collect.map (X.act f.opening)

end Opening

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  (s : State Tm O) (f : Firing O E P s.frame)

/-- A row of the state, read at the extended frame. -/
def row (o : O) : Tm (E.target f.ext) := X.act (E.weaken f.ext) (s.label o)

/-- The equations of patterns with the rows selected for them. -/
def matching (patterns : List (Tm (E.target f.ext))) (selected : List O) :
    EquationStore (Tm (E.target f.ext)) :=
  patterns.zipWith (fun pattern o => (pattern, f.row X s o)) selected

/-- **The information**: the knowledge along the extension, the take and read equations, and the
opened tells. -/
def information : EquationStore (Tm (E.target f.ext)) :=
  X.applyStore (E.weaken f.ext) s.knowledge ++ f.matching X s (f.opened X).take f.selection.taken ++
    f.matching X s (f.opened X).read f.selection.read ++ (f.opened X).tell

/-- **Freshness of the opening**: every instantiation of the state's frame and every instantiation of
the rule's unknowns are realized by one instantiation of the extended frame, on what the state
mentions and on the rule's terms. -/
def Fresh : Prop :=
  ∀ (b : Obj) (g : Hom s.frame b) (h : Hom f.rule.locals b), ∃ u : Hom (E.target f.ext) b,
    (∀ t, s.Mentions t → X.E (X.act u (X.act (E.weaken f.ext) t)) (X.act g t)) ∧
      ∀ t ∈ f.rule.terms, X.E (X.act u (X.act f.opening t)) (X.act h t)

/-- **The shapes**: a fresh opening, distinct takes and made identities, one row per pattern, one made
row per made identity, one seen set per collect pattern. -/
def Shapes : Prop :=
  f.Fresh X s ∧ f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
    f.rule.body.take.length = f.selection.taken.length ∧
    f.rule.body.read.length = f.selection.read.length ∧
    f.rule.body.produce.length = f.selection.made.length ∧
    f.rule.collect.length = f.seen.length

/-- **The guard predicate at a solution**: every opened check holds, and each collect pattern sees
exactly its claimed rows. -/
def Holds {b : Obj} (σ : Hom (E.target f.ext) b) : Prop :=
  (∀ c ∈ (f.opened X).checks, checkHolds X σ (f.row X s) s.present c) ∧
    ∀ q ∈ (f.collectOpened X).zip f.seen, matchesAt X σ (f.row X s) s.present q.1 = q.2

variable [DecidableEq O]

/-- **Admission, derived**: the shapes, the enabling of the selection, solvable information, and the
guard predicate at every solution of the information. -/
def Admits : Prop :=
  f.Shapes X s ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X s) ∧ X.Entails (f.information X s) (fun _ σ => f.Holds X s σ)

/-- **The result**: the extended frame, the information as knowledge, the fired occurrences, and the
made identities labelled by the opened made rows. -/
def result : State Tm O :=
  ⟨E.target f.ext, f.information X s, fire s.present (f.selection.commit (T := Unit)),
    relabel (f.row X s) f.selection.made (f.opened X).produce⟩

end Firing

/-! ## The step -/

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  (P : Program Tm)

/-- **The step of a program.** Its admission is `Firing.Admits`, computed from the rule, the opening
and the selection. -/
def step : Interface.Step.Standard X O (State Tm O) (fun s => Firing O E P s.frame) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := E.target f.ext
  extension f := E.weaken f.ext
  information {s} f := f.information X s
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨e, member, rfl⟩)))
  Shapes {s} f := f.Shapes X s
  Holds {s} f _ σ := f.Holds X s σ
  Admits {s} f := f.Admits X s
  admits_iff _ := Iff.rfl
  preparedResult {s} f _ := f.result X s
  present_preparedResult _ _ := rfl
  preparedSettle f _ := X.id (E.target f.ext)
  knowledge_preparedResult {s} f _ := (Frames.applyStore_id (X := X) (f.information X s)).symm

variable {X O E P}

/-- **Admission of the step of a program, spelled out**: a fresh opening, the shapes, the occurrences
(takes and reads present, takes not read, made identities fresh), solvable information, every opened
check at every solution, and every collect query at every solution. -/
theorem admits_iff {s : State Tm O} (f : Firing O E P s.frame) :
    (step X O E P).Admits f ↔ f.Fresh X s ∧
      (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        f.rule.body.take.length = f.selection.taken.length ∧
        f.rule.body.read.length = f.selection.read.length ∧
        f.rule.body.produce.length = f.selection.made.length ∧
        f.rule.collect.length = f.seen.length) ∧
      Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
      X.Solvable (f.information X s) ∧
      (∀ c ∈ (f.opened X).checks,
        X.Entails (f.information X s) (fun _ σ => checkHolds X σ (f.row X s) s.present c)) ∧
      ∀ q ∈ (f.collectOpened X).zip f.seen,
        X.Entails (f.information X s) (fun _ σ => matchesAt X σ (f.row X s) s.present q.1 = q.2) := by
  show f.Admits X s ↔ _
  unfold Firing.Admits Firing.Shapes Firing.Holds
  constructor
  · rintro ⟨⟨fresh, shapes⟩, enabled, solvable, asks⟩
    exact ⟨fresh, shapes, enabled, solvable, fun c member b σ solved => (asks b σ solved).1 c member,
      fun q member b σ solved => (asks b σ solved).2 q member⟩
  · rintro ⟨fresh, shapes, enabled, solvable, checks, collected⟩
    exact ⟨⟨fresh, shapes⟩, enabled, solvable, fun b σ solved =>
      ⟨fun c member => checks c member b σ solved, fun q member => collected q member b σ solved⟩⟩

theorem result_eq {s : State Tm O} (f : Firing O E P s.frame) (admitted : (step X O E P).Admits f) :
    (step X O E P).result f admitted = f.result X s := rfl

/-! ## Takes and reads constrain; results carry the made rows -/

namespace Firing

variable {s : State Tm O} (f : Firing O E P s.frame)

omit [DecidableEq O] in
theorem matching_mem {patterns : List (Tm (E.target f.ext))} {selected : List O}
    {p : Tm (E.target f.ext)} {o : O} (inside : (p, o) ∈ patterns.zip selected) :
    (p, f.row X s o) ∈ f.matching X s patterns selected := by
  unfold matching
  rw [← List.map_uncurry_zip_eq_zipWith]
  exact List.mem_map.mpr ⟨(p, o), inside, rfl⟩

omit [DecidableEq O] in
/-- **A take constrains**: every solution of the information equates each opened take pattern with the
label of its taken row, read at the extended frame. -/
theorem take_solved {b : Obj} {σ : Hom (E.target f.ext) b} (solved : X.Models σ (f.information X s))
    {p : Tm (E.target f.ext)} {o : O} (inside : (p, o) ∈ (f.opened X).take.zip f.selection.taken) :
    X.E (X.act σ p) (X.act σ (f.row X s o)) :=
  solved _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (f.matching_mem inside))))

omit [DecidableEq O] in
/-- **A read constrains** in the same way. -/
theorem read_solved {b : Obj} {σ : Hom (E.target f.ext) b} (solved : X.Models σ (f.information X s))
    {p : Tm (E.target f.ext)} {o : O} (inside : (p, o) ∈ (f.opened X).read.zip f.selection.read) :
    X.E (X.act σ p) (X.act σ (f.row X s o)) :=
  solved _ (List.mem_append_left _ (List.mem_append_right _ (f.matching_mem inside)))

omit [DecidableEq O] in
/-- **A tell constrains**: every solution of the information solves each opened tell. -/
theorem tell_solved {b : Obj} {σ : Hom (E.target f.ext) b} (solved : X.Models σ (f.information X s))
    {e : Equation (Tm (E.target f.ext))} (inside : e ∈ (f.opened X).tell) : X.Solves σ e :=
  solved _ (List.mem_append_right _ inside)

omit [DecidableEq O] in
/-- **The information refines the knowledge along the extension.** -/
theorem knowledge_solved {b : Obj} {σ : Hom (E.target f.ext) b}
    (solved : X.Models σ (f.information X s)) :
    X.Models (X.comp σ (E.weaken f.ext)) s.knowledge :=
  (Frames.models_applyStore (E.weaken f.ext) σ s.knowledge).mp
    (Frames.models_of_subset (fun _ member => List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ member))) solved)

theorem relabel_of_not_mem {a : Obj} (old : O → Tm a) :
    ∀ (made : List O) (rows : List (Tm a)) {o : O}, o ∉ made → relabel old made rows o = old o
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | o' :: rest, t :: ts, o, missing => by
      have other : o ≠ o' := fun same => missing (List.mem_cons.mpr (Or.inl same))
      have later : o ∉ rest := fun inside => missing (List.mem_cons.mpr (Or.inr inside))
      simp only [relabel, if_neg other]
      exact relabel_of_not_mem old rest ts later

theorem relabel_zip {a : Obj} (old : O → Tm a) :
    ∀ (made : List O) (rows : List (Tm a)), made.Nodup → made.length = rows.length →
      ∀ x ∈ made.zip rows, relabel old made rows x.1 = x.2
  | [], _, _, _, _, inside => by simp at inside
  | _ :: _, [], _, lengths, _, _ => by simp at lengths
  | o' :: rest, t :: ts, nodup, lengths, x, inside => by
      rcases List.mem_cons.mp inside with first | later
      · subst first
        simp [relabel]
      · have notHead : x.1 ≠ o' := by
          intro same
          have inRest : x.1 ∈ rest := (List.of_mem_zip later).1
          exact (List.nodup_cons.mp nodup).1 (same ▸ inRest)
        simp only [relabel, if_neg notHead]
        exact relabel_zip old rest ts (List.nodup_cons.mp nodup).2 (Nat.succ.inj lengths) x later

/-- **A made identity carries its opened made row.** -/
theorem result_label_made (shapes : f.Shapes X s) {o : O} {t : Tm (E.target f.ext)}
    (inside : (o, t) ∈ f.selection.made.zip (f.opened X).produce) :
    (f.result X s).label o = t := by
  have lengths : f.selection.made.length = (f.opened X).produce.length := by
    simp only [opened, RuleInstance.map, List.length_map]
    exact shapes.2.2.2.2.2.1.symm
  exact relabel_zip (f.row X s) f.selection.made (f.opened X).produce shapes.2.2.1 lengths (o, t) inside

/-- **Every other identity keeps its label, read at the extended frame.** -/
theorem result_label_other {o : O} (missing : o ∉ f.selection.made) :
    (f.result X s).label o = f.row X s o :=
  relabel_of_not_mem (f.row X s) f.selection.made (f.opened X).produce missing

end Firing

#print axioms step
#print axioms admits_iff
#print axioms none_iff_count_zero
#print axioms Firing.take_solved
#print axioms Firing.read_solved
#print axioms Firing.tell_solved
#print axioms Firing.knowledge_solved
#print axioms Firing.result_label_made
#print axioms Firing.result_label_other

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
