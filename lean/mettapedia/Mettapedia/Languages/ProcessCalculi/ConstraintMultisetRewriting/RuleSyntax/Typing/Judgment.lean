import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.DependentEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopes

/-!
# Typing as a property of programs at dependent frames

At the typed βη frames with telescopes of fresh helpers (`Dependent.helperExtensions`), every term
of a rule, of a state and of an opening is a typed term (`TotalTerm`): a rule is formed syntax over
its own frame, a row is a term at its type, an opening is a typed substitution, and an equation of
the knowledge relates two typed terms, possibly of different types, holding where a solution
equates their types and then their terms. So the typing of rows, of made rows and of equations
holds by construction, and the check of the dependent full step that made rows are typed is
satisfied by every firing of every program (`made_rows_typed`).

What construction does not give is that **an answer has the type of the call it answers**. The rule
`append zero k nil ys = ys` makes `ys : vec k` for a call of type `vec (add zero k)`; the two types
are equal only where addition computes.

## The judgment

* **Answers** of a rule: for each made row, the take pattern it answers, if any.
* **`WellTypedRule levels r answers`**: at every solution of the rule's own tells, every answer has the
  type of the take pattern it answers (`HasType`). With no tells this is type equality in the rule's
  frame (`wellTypedRule_iff_of_tell_nil`), a judgment of the framework.
* **`WellTypedProgram levels P answers`**: every rule of the program is well typed; the union of two
  well-typed programs is well typed (`WellTypedProgram.union`).
* **A typing of a state** gives each occurrence an expected type at the state's frame, and
  **`WellTypedState levels s Δ`** says that every present row has its expected type at every solution
  of the knowledge. Every state is well typed at the rows' own types (`wellTypedState_own`).
* **Retyping along a firing** (`retype`): an answer inherits the expected type of the row it answers,
  read at the extended frame; any other made row expects its own type; every other occurrence keeps
  its expected type, read at the extended frame.

## The check a firing can make, and the judgment that makes it redundant

* **`AnswerCheck levels f answers`**: at every solution of the firing's information, each answer has
  the type of the row it answers. This is the per-firing typing premise for answers.
* `answerCheck_of_wellTyped`: every admitted firing of a well-typed rule passes it.
* `result_wellTyped_of_check`: for every rule, an admitted firing that passes the check, from a
  well-typed state, reaches a state that is well typed at the retyping.

## Subject reduction over whole runs

* `result_wellTyped`: an admitted firing of a well-typed rule from a well-typed state reaches a state
  that is well typed at the retyping.
* `TypedReach`: runs that carry the typing along their firings. Every run of the step lifts to one
  for every initial typing (`typedReach_of_reach`), and along it every state is well typed
  (`TypedReach.wellTyped`).
* `reach_wellTyped`: from a well-typed state, every state that a well-typed program reaches is well
  typed at the typing carried along the run. `dependent_reach_wellTyped` says the same for the
  dependent full step restricted to the program, through `dependent_eq`.

## Canonical openings

A rule whose unknowns are a closed telescope `T` (`telescopeRule`) opens at any frame `Γ` along the
telescope copied over `Γ`, by the lift of the unique map to the empty frame (`canonicalFiring`). The
copy is a pullback, so this opening is fresh at every state (`canonical_fresh`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open Interface.DependentFull (Helpers Make)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Dependent (Terms helperExtensions toState dependentOn dependent_eq toDependent)

variable {Head : Type} {rules : Rules Head}

/-! ## Positions in lists -/

section Lists

theorem exists_getElem?_of_length {α β : Type*} {l₁ : List α} {l₂ : List β} {j : ℕ} {a : α}
    (lengths : l₁.length = l₂.length) (inside : l₁[j]? = some a) : ∃ b, l₂[j]? = some b := by
  obtain ⟨bound, -⟩ := List.getElem?_eq_some_iff.mp inside
  exact ⟨l₂[j]'(lengths ▸ bound), List.getElem?_eq_getElem _⟩

/-- **Relabelling at a position**: the `j`-th made identity gets the `j`-th row. -/
theorem relabel_getElem? {Obj : Type*} {Tm : Obj → Type*} {O : Type*} [DecidableEq O] {a : Obj}
    (old : O → Tm a) :
    ∀ (made : List O) (rows : List (Tm a)) (j : ℕ) {o : O} {t : Tm a}, made.Nodup →
      made[j]? = some o → rows[j]? = some t → relabel old made rows o = t
  | [], _, _, _, _, _, inside, _ => by simp at inside
  | _ :: _, [], _, _, _, _, _, row => by simp at row
  | o' :: rest, t' :: ts, 0, o, t, _, inside, row => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at inside row
      subst inside row
      simp [relabel]
  | o' :: rest, t' :: ts, j + 1, o, t, nodup, inside, row => by
      simp only [List.getElem?_cons_succ] at inside row
      have other : o ≠ o' := fun same =>
        (List.nodup_cons.mp nodup).1 (same ▸ List.mem_of_getElem? inside)
      simp only [relabel, if_neg other]
      exact relabel_getElem? old rest ts j (List.nodup_cons.mp nodup).2 inside row

theorem getElem?_mapIdx_of {α β : Type*} {l : List α} {g : ℕ → α → β} {j : ℕ} {a : α}
    (inside : l[j]? = some a) : (l.mapIdx g)[j]? = some (g j a) := by
  rw [List.getElem?_mapIdx, inside]
  rfl

end Lists

/-! ## Reindexing typed terms and types -/

section Reindexing

theorem reindex_factor {Γ Δ Θ : Context rules} (t : TotalTerm Γ) (w : Δ ⟶ Γ) (u : Θ ⟶ Δ)
    (g : Θ ⟶ Γ) (same : u ≫ w = g) : (t.reindex w).reindex u = t.reindex g := by
  rw [← reindex_comp, same]

theorem equivalent_of_eq {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)
    {Γ : Context rules} {a b : TotalTerm Γ} (same : a = b) : (frames levels).E a b := by
  rw [same]
  exact ((frames levels).equivalence Γ).refl b

/-- **The copy of a closed telescope over a frame is a pullback**: a substitution of the frame and
one of the telescope factor together through it. -/
theorem copy_factors (T : Helpers (empty rules)) {Γ b : Context rules} (g : b ⟶ Γ)
    (h : b ⟶ T.frame) :
    ∃ u : b ⟶ (T.reindex (toEmpty Γ)).frame,
      u ≫ (T.reindex (toEmpty Γ)).weaken = g ∧ u ≫ Helpers.lift (toEmpty Γ) T = h :=
  ⟨Helpers.into (toEmpty Γ) T g h ((toEmpty_unique _ _).trans (toEmpty_unique _ _).symm),
    Helpers.into_weaken _ _ _ _ _, Helpers.into_lift _ _ _ _ _⟩

theorem typeEq_along {Γ Δ Θ : Context rules} (w : Δ ⟶ Γ) (σ : Θ ⟶ Δ) {A B : TypeOver Γ}
    (same : TypeEq rules Θ.raw (A.reindex (σ ≫ w)).code (B.reindex (σ ≫ w)).code) :
    TypeEq rules Θ.raw ((A.reindex w).reindex σ).code ((B.reindex w).reindex σ).code := by
  rw [← TypeOver.reindex_comp, ← TypeOver.reindex_comp]
  exact same

/-- **The answer's step**: the rule types the answer like its call pattern, and the take equation types
the call pattern like the taken row. -/
theorem typeEq_answer {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)
    {Δ ρ Θ : Context rules} (ι : Δ ⟶ ρ) (σ : Θ ⟶ Δ) {A C : TypeOver ρ} {B : TypeOver Δ}
    (rule : TypeEq rules Θ.raw (A.reindex (σ ≫ ι)).code (C.reindex (σ ≫ ι)).code)
    (matched : TypeEq rules Θ.raw ((C.reindex ι).reindex σ).code (B.reindex σ).code) :
    TypeEq rules Θ.raw ((A.reindex ι).reindex σ).code (B.reindex σ).code := by
  rw [← TypeOver.reindex_comp] at matched
  rw [← TypeOver.reindex_comp]
  exact rule.trans levels matched

/-- **The state's step**: the taken row has its expected type, read along the extension. -/
theorem typeEq_expected {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)
    {Γ Δ Θ : Context rules} (w : Δ ⟶ Γ) (σ : Θ ⟶ Δ) {X : Tm Head Θ.arity} {B D : TypeOver Γ}
    (answer : TypeEq rules Θ.raw X ((B.reindex w).reindex σ).code)
    (before : TypeEq rules Θ.raw (B.reindex (σ ≫ w)).code (D.reindex (σ ≫ w)).code) :
    TypeEq rules Θ.raw X ((D.reindex w).reindex σ).code := by
  rw [← TypeOver.reindex_comp] at answer
  rw [← TypeOver.reindex_comp]
  exact answer.trans levels before

end Reindexing

/-! ## Rules over closed telescopes, and their canonical openings -/

section Canonical

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L) {O : Type}

/-- **A rule whose unknowns are a closed telescope.** -/
def telescopeRule (T : Helpers (empty rules)) (body : RuleInstance (TotalTerm T.frame))
    (collect : List (TotalTerm T.frame)) : Rule (Terms rules) :=
  ⟨T.frame, body, collect⟩

/-- **The canonical opening of such a rule at a frame**: the telescope copied over the frame, opened
by the lift of the unique map to the empty frame. -/
def canonicalFiring {P : Program (Terms rules)} (T : Helpers (empty rules))
    (body : RuleInstance (TotalTerm T.frame)) (collect : List (TotalTerm T.frame))
    (member : telescopeRule T body collect ∈ P) (Γ : Context rules) (selection : Selection O)
    (seen : List (Finset O)) : Firing O (helperExtensions (rules := rules)) P Γ :=
  ⟨telescopeRule T body collect, member, T.reindex (toEmpty Γ), Helpers.lift (toEmpty Γ) T,
    selection, seen⟩

/-- **Canonical openings are fresh**: a substitution of the state's frame and one of the rule's
telescope agree on the empty frame, so they factor together through the copy, which is a pullback. -/
theorem canonical_fresh {P : Program (Terms rules)} (T : Helpers (empty rules))
    (body : RuleInstance (TotalTerm T.frame)) (collect : List (TotalTerm T.frame))
    (member : telescopeRule T body collect ∈ P) (s : State (Terms rules) O) (selection : Selection O)
    (seen : List (Finset O)) :
    (canonicalFiring T body collect member s.frame selection seen).Fresh (frames levels) s := by
  intro b g h
  obtain ⟨u, weakened, lifted⟩ := copy_factors T g h
  exact ⟨u, fun t _ => equivalent_of_eq levels (reindex_factor t _ u g weakened),
    fun t _ => equivalent_of_eq levels (reindex_factor t _ u h lifted)⟩

end Canonical

/-! ## The judgment -/

section Judgment

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- **A typed term has a type at a substitution**: their types are equal once substituted. -/
def HasType {Γ Θ : Context rules} (σ : Θ ⟶ Γ) (t : TotalTerm Γ) (A : TypeOver Γ) : Prop :=
  TypeEq rules Θ.raw (t.1.reindex σ).code (A.reindex σ).code

/-- **A well-typed rule**, for a choice of answers (for each made row, the take pattern it answers,
if any): at every solution of the rule's own tells, every answer has the type of the take pattern
it answers. -/
def WellTypedRule (r : Rule (Terms rules)) (answers : List (Option ℕ)) : Prop :=
  ∀ (j i : ℕ) (made call : TotalTerm r.locals), answers[j]? = some (some i) →
    r.body.produce[j]? = some made → r.body.take[i]? = some call →
    ∀ (Θ : Context rules) (σ : Θ ⟶ r.locals), (frames levels).Models σ r.body.tell →
      HasType σ made call.1

/-- **A well-typed program**: each of its rules is well typed for its answers. -/
def WellTypedProgram (P : Program (Terms rules)) (answers : Rule (Terms rules) → List (Option ℕ)) :
    Prop :=
  ∀ r ∈ P, WellTypedRule levels r (answers r)

/-- **Typing composes**: the union of two well-typed programs is well typed. -/
theorem WellTypedProgram.union {P Q : Program (Terms rules)}
    {answers : Rule (Terms rules) → List (Option ℕ)} (left : WellTypedProgram levels P answers)
    (right : WellTypedProgram levels Q answers) : WellTypedProgram levels (P ∪ Q) answers :=
  fun r member => member.elim (left r) (right r)

/-- **Without tells, the judgment is type equality in the rule's frame.** -/
theorem wellTypedRule_iff_of_tell_nil (r : Rule (Terms rules)) (answers : List (Option ℕ))
    (noTells : r.body.tell = []) :
    WellTypedRule levels r answers ↔
      ∀ (j i : ℕ) (made call : TotalTerm r.locals), answers[j]? = some (some i) →
        r.body.produce[j]? = some made → r.body.take[i]? = some call →
          TypeEq rules r.locals.raw made.1.code call.1.code := by
  constructor
  · intro typed j i made call hj hm hc
    have atIdentity := typed j i made call hj hm hc r.locals (𝟙 _)
      (by rw [noTells]; exact Frames.models_nil _)
    simpa only [HasType, TypeOver.reindex_id] using atIdentity
  · intro typed j i made call hj hm hc Θ σ _
    exact reindex_typeEquality (typed j i made call hj hm hc) σ

variable {O : Type}

/-- **A well-typed state** for a typing of its occurrences: every present row has its expected type
at every solution of the knowledge. -/
def WellTypedState (s : State (Terms rules) O) (Δ : O → TypeOver s.frame) : Prop :=
  ∀ o ∈ s.present, ∀ (Θ : Context rules) (σ : Θ ⟶ s.frame), (frames levels).Models σ s.knowledge →
    HasType σ (s.label o) (Δ o)

/-- Every state is well typed at the typing by its rows' own types. -/
theorem wellTypedState_own (s : State (Terms rules) O) :
    WellTypedState levels s (fun o => (s.label o).1) := by
  intro o _ Θ σ _
  exact (TypeOver.isType _).refl

/-! ## Answers and retyping -/

/-- The taken row that the `j`-th made row answers, if any. -/
def answerOf (answers : List (Option ℕ)) (taken : List O) (j : ℕ) : Option O :=
  (answers[j]?.bind id).bind fun i => taken[i]?

theorem answerOf_eq_some {answers : List (Option ℕ)} {taken : List O} {j : ℕ} {o : O} :
    answerOf answers taken j = some o ↔ ∃ i, answers[j]? = some (some i) ∧ taken[i]? = some o := by
  unfold answerOf
  cases h : answers[j]? with
  | none => simp
  | some a =>
      cases a with
      | none => simp
      | some i => simp

variable {P : Program (Terms rules)}

/-- **The expected type of the `j`-th made row**: the expected type of the row it answers, read at
the extended frame, or else its own type. -/
def expectedType {s : State (Terms rules) O}
    (f : Firing O (helperExtensions (rules := rules)) P s.frame) (answers : List (Option ℕ))
    (Δ : O → TypeOver s.frame) (j : ℕ) (t : TotalTerm f.ext.frame) : TypeOver f.ext.frame :=
  (answerOf answers f.selection.taken j).elim t.1 fun o => (Δ o).reindex f.ext.weaken

/-- The expected types of a firing's made rows. -/
def expected {s : State (Terms rules) O} (f : Firing O (helperExtensions (rules := rules)) P s.frame)
    (answers : List (Option ℕ)) (Δ : O → TypeOver s.frame) : List (TypeOver f.ext.frame) :=
  (f.opened (frames levels)).produce.mapIdx (expectedType f answers Δ)

variable [DecidableEq O]

/-- **Retyping along a firing**: every answer expects the type of the row it answers, every other made
row its own type, and every other occurrence keeps its expected type, read at the extended frame. -/
def retype {s : State (Terms rules) O} (f : Firing O (helperExtensions (rules := rules)) P s.frame)
    (answers : List (Option ℕ)) (Δ : O → TypeOver s.frame) : O → TypeOver f.ext.frame :=
  relabel (Tm := fun Γ : Context rules => TypeOver Γ) (fun o => (Δ o).reindex f.ext.weaken)
    f.selection.made (expected levels f answers Δ)

theorem retype_of_not_mem {s : State (Terms rules) O}
    (f : Firing O (helperExtensions (rules := rules)) P s.frame) (answers : List (Option ℕ))
    (Δ : O → TypeOver s.frame) {o : O} (missing : o ∉ f.selection.made) :
    retype levels f answers Δ o = (Δ o).reindex f.ext.weaken :=
  Firing.relabel_of_not_mem (Tm := fun Γ : Context rules => TypeOver Γ) _ _ _ missing

theorem retype_made {s : State (Terms rules) O}
    (f : Firing O (helperExtensions (rules := rules)) P s.frame) (answers : List (Option ℕ))
    (Δ : O → TypeOver s.frame) {j : ℕ} {o : O} {t : TotalTerm f.ext.frame}
    (nodup : f.selection.made.Nodup) (made : f.selection.made[j]? = some o)
    (row : (f.opened (frames levels)).produce[j]? = some t) :
    retype levels f answers Δ o = expectedType f answers Δ j t := by
  apply relabel_getElem? _ _ _ j nodup made
  exact getElem?_mapIdx_of row

/-- **An answer inherits the expected type of the row it answers.** -/
theorem retype_answer {s : State (Terms rules) O}
    (f : Firing O (helperExtensions (rules := rules)) P s.frame) (answers : List (Option ℕ))
    (Δ : O → TypeOver s.frame) {j : ℕ} {o oi : O} {t : TotalTerm f.ext.frame}
    (nodup : f.selection.made.Nodup) (made : f.selection.made[j]? = some o)
    (row : (f.opened (frames levels)).produce[j]? = some t)
    (answer : answerOf answers f.selection.taken j = some oi) :
    retype levels f answers Δ o = (Δ oi).reindex f.ext.weaken := by
  rw [retype_made levels f answers Δ nodup made row, expectedType, answer]
  rfl

/-! ## The answer check of a firing -/

/-- **The answer check of a firing**, the per-firing typing premise generalized from made rows to
answers: at every solution of the firing's information, each answer has the type of the row it
answers. -/
def AnswerCheck {s : State (Terms rules) O}
    (f : Firing O (helperExtensions (rules := rules)) P s.frame) (answers : List (Option ℕ)) : Prop :=
  ∀ (j : ℕ) (oi : O) (t : TotalTerm f.ext.frame), answerOf answers f.selection.taken j = some oi →
    (f.opened (frames levels)).produce[j]? = some t →
    ∀ (Θ : Context rules) (σ : Θ ⟶ f.ext.frame),
      (frames levels).Models σ (f.information (frames levels) s) →
      HasType σ t (f.row (frames levels) s oi).1

/-- **A well-typed rule passes the answer check at every admitted firing**: the rule types the
answer like its call pattern, and the take equation types the call pattern like the taken row. -/
theorem answerCheck_of_wellTyped {s : State (Terms rules) O}
    {f : Firing O (helperExtensions (rules := rules)) P s.frame} {answers : List (Option ℕ)}
    (typed : WellTypedRule levels f.rule answers)
    (admitted : (step (frames levels) O helperExtensions P).Admits (s := s) f) :
    AnswerCheck levels f answers := by
  obtain ⟨⟨-, -, -, takeLength, -, -, -⟩, -, -, -⟩ := admitted
  intro j oi t' hAnswer rowJ Θ σ solved
  obtain ⟨i, hi, takenI⟩ := answerOf_eq_some.mp hAnswer
  have rowJ' : (f.rule.body.produce.map ((frames levels).act f.opening))[j]? = some t' := rowJ
  rw [List.getElem?_map] at rowJ'
  obtain ⟨t, produceJ, rfl⟩ := Option.map_eq_some_iff.mp rowJ'
  obtain ⟨p, takeI⟩ := exists_getElem?_of_length takeLength.symm takenI
  have tells : (frames levels).Models (σ ≫ f.opening) f.rule.body.tell := by
    have opened : (frames levels).Models σ ((frames levels).applyStore f.opening f.rule.body.tell) :=
      fun e member => f.tell_solved solved member
    exact (Frames.models_applyStore (X := frames levels) f.opening σ f.rule.body.tell).mp opened
  have e1 : TypeEq rules Θ.raw (t.1.reindex (σ ≫ f.opening)).code (p.1.reindex (σ ≫ f.opening)).code :=
    typed j i t p hi produceJ takeI Θ (σ ≫ f.opening) tells
  have openedTake : (f.opened (frames levels)).take[i]? = some (p.reindex f.opening) := by
    simp only [Firing.opened, RuleInstance.map, List.getElem?_map, takeI]
    rfl
  have zipped : (p.reindex f.opening, oi) ∈ (f.opened (frames levels)).take.zip f.selection.taken :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨openedTake, takenI⟩)
  have e2 : TypeEq rules Θ.raw ((p.1.reindex f.opening).reindex σ).code
      ((f.row (frames levels) s oi).1.reindex σ).code := (f.take_solved solved zipped).1
  exact typeEq_answer levels f.opening σ (A := t.1) (C := p.1) (B := (f.row (frames levels) s oi).1)
    e1 e2

/-! ## Subject reduction -/

/-- **Subject reduction for one firing, from the check**: an admitted firing that passes the answer
check, from a well-typed state, reaches a state that is well typed at the retyping. This holds for
every rule, well typed or not. -/
theorem result_wellTyped_of_check {s : State (Terms rules) O} {Δ : O → TypeOver s.frame}
    {f : Firing O (helperExtensions (rules := rules)) P s.frame} {answers : List (Option ℕ)}
    (admitted : (step (frames levels) O helperExtensions P).Admits (s := s) f)
    (check : AnswerCheck levels f answers) (state : WellTypedState levels s Δ) :
    WellTypedState levels (f.result (frames levels) s) (retype levels f answers Δ) := by
  obtain ⟨⟨-, -, madeNodup, -, -, produceLength, -⟩, enabled, -, -⟩ := admitted
  intro o present Θ σ solved
  have old : (frames levels).Models (σ ≫ f.ext.weaken) s.knowledge := f.knowledge_solved solved
  rcases mem_fire.mp present with ⟨wasPresent, -⟩ | made
  · have notMade : o ∉ f.selection.made := fun inside =>
      Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr inside) wasPresent
    have label : (f.result (frames levels) s).label o = (s.label o).reindex f.ext.weaken :=
      Firing.result_label_other f notMade
    show HasType σ ((f.result (frames levels) s).label o) (retype levels f answers Δ o)
    rw [label, retype_of_not_mem levels f answers Δ notMade]
    exact typeEq_along f.ext.weaken σ (A := (s.label o).1) (B := Δ o)
      (state o wasPresent Θ (σ ≫ f.ext.weaken) old)
  · have inMade : o ∈ f.selection.made := List.mem_toFinset.mp made
    obtain ⟨j, atJ⟩ := List.mem_iff_getElem?.mp inMade
    have lengths : f.selection.made.length = (f.opened (frames levels)).produce.length := by
      simp only [Firing.opened, RuleInstance.map, List.length_map]
      exact produceLength.symm
    obtain ⟨t', rowJ⟩ := exists_getElem?_of_length lengths atJ
    have label : (f.result (frames levels) s).label o = t' :=
      relabel_getElem? _ _ _ j madeNodup atJ rowJ
    show HasType σ ((f.result (frames levels) s).label o) (retype levels f answers Δ o)
    rw [label, retype_made levels f answers Δ madeNodup atJ rowJ]
    unfold expectedType
    cases hAnswer : answerOf answers f.selection.taken j with
    | none =>
        show HasType σ t' t'.1
        exact (TypeOver.isType _).refl
    | some oi =>
        show HasType σ t' ((Δ oi).reindex f.ext.weaken)
        obtain ⟨i, -, takenI⟩ := answerOf_eq_some.mp hAnswer
        have answer : TypeEq rules Θ.raw (t'.1.reindex σ).code
            (((s.label oi).1.reindex f.ext.weaken).reindex σ).code :=
          check j oi t' hAnswer rowJ Θ σ solved
        have takenPresent : oi ∈ s.present :=
          enabled.taken_subset (List.mem_toFinset.mpr (List.mem_of_getElem? takenI))
        have before : TypeEq rules Θ.raw ((s.label oi).1.reindex (σ ≫ f.ext.weaken)).code
            ((Δ oi).reindex (σ ≫ f.ext.weaken)).code :=
          state oi takenPresent Θ (σ ≫ f.ext.weaken) old
        exact typeEq_expected levels f.ext.weaken σ (B := (s.label oi).1) (D := Δ oi) answer before

/-- **Subject reduction for one firing**: an admitted firing of a well-typed rule from a well-typed
state reaches a state that is well typed at the retyping. -/
theorem result_wellTyped {s : State (Terms rules) O} {Δ : O → TypeOver s.frame}
    {f : Firing O (helperExtensions (rules := rules)) P s.frame} {answers : List (Option ℕ)}
    (typed : WellTypedRule levels f.rule answers)
    (admitted : (step (frames levels) O helperExtensions P).Admits (s := s) f)
    (state : WellTypedState levels s Δ) :
    WellTypedState levels (f.result (frames levels) s) (retype levels f answers Δ) :=
  result_wellTyped_of_check levels admitted (answerCheck_of_wellTyped levels typed admitted) state

/-! ## Runs that carry the typing -/

variable (P) in
/-- **Runs that carry a typing**: each firing of the run retypes the state. -/
inductive TypedReach (answers : Rule (Terms rules) → List (Option ℕ)) :
    (s : State (Terms rules) O) → (O → TypeOver s.frame) → (t : State (Terms rules) O) →
      (O → TypeOver t.frame) → Prop
  | refl (s : State (Terms rules) O) (Δ : O → TypeOver s.frame) : TypedReach answers s Δ s Δ
  | head {s : State (Terms rules) O} {Δ : O → TypeOver s.frame} {t : State (Terms rules) O}
      {Δt : O → TypeOver t.frame} (f : Firing O (helperExtensions (rules := rules)) P s.frame)
      (admitted : (step (frames levels) O helperExtensions P).Admits (s := s) f) :
      TypedReach answers (f.result (frames levels) s) (retype levels f (answers f.rule) Δ) t Δt →
      TypedReach answers s Δ t Δt

/-- **Along a typed run of a well-typed program, every state is well typed.** -/
theorem TypedReach.wellTyped {answers : Rule (Terms rules) → List (Option ℕ)}
    (typed : WellTypedProgram levels P answers) {s t : State (Terms rules) O}
    {Δ : O → TypeOver s.frame} {Δt : O → TypeOver t.frame}
    (reach : TypedReach levels P answers s Δ t Δt) (state : WellTypedState levels s Δ) :
    WellTypedState levels t Δt := by
  induction reach with
  | refl => exact state
  | head f admitted _ rest => exact rest (result_wellTyped levels (typed f.rule f.member) admitted state)

/-- **Every run of the step carries every initial typing.** -/
theorem typedReach_of_reach {answers : Rule (Terms rules) → List (Option ℕ)}
    {s t : State (Terms rules) O}
    (reach : Relation.ReflTransGen (Succ (step (frames levels) O helperExtensions P).toStep) s t) :
    ∀ Δ : O → TypeOver s.frame, ∃ Δt : O → TypeOver t.frame, TypedReach levels P answers s Δ t Δt := by
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun Δ => ⟨Δ, .refl _ _⟩
  | head first _ rest =>
      obtain ⟨f, admitted, rfl⟩ := first
      intro Δ
      obtain ⟨Δt, typedRest⟩ := rest (retype levels f (answers f.rule) Δ)
      exact ⟨Δt, .head f admitted typedRest⟩

/-- **Subject reduction over whole runs**: from a well-typed state, every state that a well-typed
program reaches is well typed at the typing carried along the run. -/
theorem reach_wellTyped {answers : Rule (Terms rules) → List (Option ℕ)}
    (typed : WellTypedProgram levels P answers) {s t : State (Terms rules) O}
    {Δ : O → TypeOver s.frame} (state : WellTypedState levels s Δ)
    (reach : Relation.ReflTransGen (Succ (step (frames levels) O helperExtensions P).toStep) s t) :
    ∃ Δt : O → TypeOver t.frame, TypedReach levels P answers s Δ t Δt ∧ WellTypedState levels t Δt := by
  obtain ⟨Δt, carried⟩ := typedReach_of_reach levels (answers := answers) reach Δ
  exact ⟨Δt, carried, carried.wellTyped levels typed state⟩

/-- **The same for the dependent full step restricted to the program**, through `dependent_eq`. -/
theorem dependent_reach_wellTyped {answers : Rule (Terms rules) → List (Option ℕ)}
    (typed : WellTypedProgram levels P answers) {s t : Interface.DependentFull.State rules O}
    {Δ : O → TypeOver s.frame} (state : WellTypedState levels (toState s) Δ)
    (reach : Relation.ReflTransGen (Succ (dependentOn levels P)) s t) :
    ∃ Δt : O → TypeOver t.frame, TypedReach levels P answers (toState s) Δ (toState t) Δt ∧
      WellTypedState levels (toState t) Δt := by
  have lifted : Relation.ReflTransGen (Succ (step (frames levels) O helperExtensions P).toStep)
      (toState s) (toState t) :=
    Relation.ReflTransGen.lift toState (fun a b succ => (dependent_eq a b).mp succ) _ _ reach
  exact reach_wellTyped levels typed state lifted

/-! ## The check the construction makes redundant -/

omit [DecidableEq O] in
/-- **The dependent full step's check that made rows are typed holds for every firing of every
program**, because a rule's made rows are typed terms. -/
theorem made_rows_typed {s : Interface.DependentFull.State rules O}
    (g : Firing O (helperExtensions (rules := rules)) P s.frame) :
    ∀ m ∈ (toDependent levels g).makes, m.2.WellTyped := by
  intro m member
  obtain ⟨-, inside⟩ := List.of_mem_zip member
  obtain ⟨t, -, same⟩ := List.mem_map.mp inside
  rw [← same]
  exact Make.ofRow_wellTyped t

end Judgment

#print axioms canonical_fresh
#print axioms WellTypedProgram.union
#print axioms wellTypedRule_iff_of_tell_nil
#print axioms wellTypedState_own
#print axioms answerOf_eq_some
#print axioms retype_answer
#print axioms answerCheck_of_wellTyped
#print axioms result_wellTyped_of_check
#print axioms result_wellTyped
#print axioms TypedReach.wellTyped
#print axioms typedReach_of_reach
#print axioms reach_wellTyped
#print axioms dependent_reach_wellTyped
#print axioms made_rows_typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing
