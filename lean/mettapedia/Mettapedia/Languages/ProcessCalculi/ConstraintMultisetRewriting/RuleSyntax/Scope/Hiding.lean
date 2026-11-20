import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Renaming

/-!
# Hiding knowledge that no row mentions

A firing reads the knowledge only through its solutions, and a solution only through what it does to
the rows and to the rule's own terms. So knowledge about unknowns that no row mentions can be
replaced by any store with the same solutions **as seen from the rows**, without changing a run.

## Seen alike from the rows

* `Rows s`: the labels of the present rows.
* `SeenAlike A K K' F`: every solution of either store is matched by a solution of the other that
  agrees with it on the terms of `F`.
* `Hides A s s'`: the same present rows with the same labels, and knowledge seen alike from the rows.
  It is symmetric (`Hides.symm`).

## The theorem

* `transfer`: a solution of a firing's information at `s` is matched by a solution of its information
  at `s'` agreeing with it on the rows and on the rule's opened terms, when the opening is fresh at
  `s'`.
* **`admits_iff_of_hides`**: for an opening fresh at both states, the firing is admitted at one
  exactly when at the other, for every program.
* **`hides_result`**: and the two results again hide each other.

So `Hides` is a bisimulation of the step of every program on openings fresh at both states. Which
openings are fresh depends on what the state mentions, knowledge included; at first-order terms it
depends only on the unknowns mentioned (`HidingFirstOrder.fresh_iff_of_unknowns`), and there the
relation with equal knowledge unknowns is a bisimulation outright (`HidingFirstOrder`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO}

/-- The labels of the present rows. -/
def Rows (s : State (Terms T) O) (t : T) : Prop := ∃ o ∈ s.present, s.label o = t

/-- Two substitutions agree on a family of terms. -/
def AgreeOn (ρ σ : S) (F : T → Prop) : Prop := ∀ t, F t → A.E (A.apply ρ t) (A.apply σ t)

/-- **Two stores seen alike from a family of terms**: every solution of either is matched by a
solution of the other that agrees with it on the family. -/
def SeenAlike (K K' : EquationStore T) (F : T → Prop) : Prop :=
  (∀ σ, A.Models σ K → ∃ σ', A.Models σ' K' ∧ AgreeOn A σ' σ F) ∧
    ∀ σ', A.Models σ' K' → ∃ σ, A.Models σ K ∧ AgreeOn A σ σ' F

/-- **A hiding**: the same present rows with the same labels, and knowledge seen alike from the
rows. -/
structure Hides (s s' : State (Terms T) O) : Prop where
  present : s.present = s'.present
  label : s.label = s'.label
  seen : SeenAlike A s.knowledge s'.knowledge (Rows s)

/-- The rows and the terms of the rule along the opening. -/
def RowsOrOpened {P : Program (Terms T)} (s : State (Terms T) O)
    (f : Firing O (ext A) P PUnit.unit) (t : T) : Prop :=
  Rows s t ∨ t ∈ f.rule.terms.map (A.apply f.opening)

variable {A}

theorem rows_eq {s s' : State (Terms T) O} (present : s.present = s'.present)
    (label : s.label = s'.label) : Rows s = Rows s' := by
  funext t
  unfold Rows
  rw [present, label]

theorem Hides.symm {s s' : State (Terms T) O} (hides : Hides A s s') : Hides A s' s :=
  ⟨hides.present.symm, hides.label.symm, by
    rw [← rows_eq hides.present hides.label]
    exact ⟨hides.seen.2, hides.seen.1⟩⟩

theorem e_congr {a a' b b' : T} (left : A.E a a') (right : A.E b b') : A.E a b ↔ A.E a' b' :=
  ⟨fun same => A.equivalence.trans (A.equivalence.symm left) (A.equivalence.trans same right),
    fun same => A.equivalence.trans left (A.equivalence.trans same (A.equivalence.symm right))⟩

variable [DecidableEq O]

section OwnInformation

variable {P : Program (Terms T)}

/-- The firing's own equations: its take and read equations and its opened tells. -/
def ownInformation (f : Firing O (ext A) P PUnit.unit) (s : State (Terms T) O) : EquationStore T :=
  f.matching (frames A) s (f.opened (frames A)).take f.selection.taken ++
    f.matching (frames A) s (f.opened (frames A)).read f.selection.read ++ (f.opened (frames A)).tell

omit [DecidableEq O] in
theorem information_eq_append (f : Firing O (ext A) P PUnit.unit) (s : State (Terms T) O) :
    f.information (frames A) s = s.knowledge ++ ownInformation f s := by
  unfold Firing.information ownInformation
  rw [applyStore_weaken]
  simp only [List.append_assoc]

omit [DecidableEq O] in
theorem ownInformation_congr (f : Firing O (ext A) P PUnit.unit) {s s' : State (Terms T) O}
    (label : s.label = s'.label) : ownInformation f s = ownInformation f s' := by
  have rows : f.row (frames A) s = f.row (frames A) s' := by
    funext o
    unfold Firing.row
    rw [label]
  unfold ownInformation Firing.matching
  rw [rows]

omit [DecidableEq O] in
theorem rowsOrOpened_row (f : Firing O (ext A) P PUnit.unit) {s : State (Terms T) O} {o : O}
    (present : o ∈ s.present) : RowsOrOpened A s f (f.row (frames A) s o) := by
  refine Or.inl ⟨o, present, ?_⟩
  show s.label o = A.apply A.identity (s.label o)
  rw [A.apply_identity]

omit [DecidableEq O] in
theorem rowsOrOpened_opened (f : Firing O (ext A) P PUnit.unit) {s : State (Terms T) O} {t : T}
    (member : t ∈ f.rule.terms) : RowsOrOpened A s f (A.apply f.opening t) :=
  Or.inr (List.mem_map.mpr ⟨t, member, rfl⟩)

/-- **The firing's own equations mention only rows and opened terms.** -/
theorem own_terms {f : Firing O (ext A) P PUnit.unit} {s : State (Terms T) O}
    (enabled : Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit))) {t : T}
    (mentioned : StoreTerms (ownInformation f s) t) : RowsOrOpened A s f t := by
  have sides : ∀ e ∈ ownInformation f s, RowsOrOpened A s f e.1 ∧ RowsOrOpened A s f e.2 := by
    intro e member
    unfold ownInformation at member
    simp only [List.mem_append] at member
    rcases member with (taken | read) | told
    · unfold Firing.matching at taken
      rw [← List.map_uncurry_zip_eq_zipWith] at taken
      obtain ⟨⟨p, o⟩, inside, rfl⟩ := List.mem_map.mp taken
      obtain ⟨p₀, member₀, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).1
      exact ⟨rowsOrOpened_opened f (take_mem_terms member₀), rowsOrOpened_row f
        (selected_of_enabled enabled o (Or.inl (List.of_mem_zip inside).2))⟩
    · unfold Firing.matching at read
      rw [← List.map_uncurry_zip_eq_zipWith] at read
      obtain ⟨⟨p, o⟩, inside, rfl⟩ := List.mem_map.mp read
      obtain ⟨p₀, member₀, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).1
      exact ⟨rowsOrOpened_opened f (read_mem_terms member₀), rowsOrOpened_row f
        (selected_of_enabled enabled o (Or.inr (List.of_mem_zip inside).2))⟩
    · obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp told
      exact ⟨rowsOrOpened_opened f (tell_mem_terms inside).1,
        rowsOrOpened_opened f (tell_mem_terms inside).2⟩
  rcases mentioned with first | second
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp first
    exact (sides e member).1
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp second
    exact (sides e member).2

end OwnInformation

section Transfer

variable {P : Program (Terms T)}

/-- **The transfer**: a solution of the information at `s` is matched by a solution of the
information at `s'` that agrees with it on the rows and on the opened terms, when `s` and `s'` hide
each other and the opening is fresh at `s'`. -/
theorem transfer {s s' : State (Terms T) O} (hides : Hides A s s') {f : Firing O (ext A) P PUnit.unit}
    (enabled : Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)))
    (fresh' : f.Fresh (frames A) s') {σ : S} (solved : A.Models σ (f.information (frames A) s)) :
    ∃ u, A.Models u (f.information (frames A) s') ∧ AgreeOn A u σ (RowsOrOpened A s f) := by
  rw [information_eq_append] at solved
  obtain ⟨onK, onOwn⟩ := (A.models_append σ _ _).mp solved
  obtain ⟨σ', onK', near⟩ := hides.seen.1 σ onK
  obtain ⟨u, onState, onRule⟩ := fresh' PUnit.unit σ' (A.compose σ f.opening)
  have onMentions : ∀ t, s'.Mentions t → A.E (A.apply u t) (A.apply σ' t) := by
    intro t mentioned
    have h : A.E (A.apply u (A.apply A.identity t)) (A.apply σ' t) := onState t mentioned
    rwa [A.apply_identity] at h
  have agree : AgreeOn A u σ (RowsOrOpened A s f) := by
    rintro t (⟨o, present, rfl⟩ | opened)
    · have mentioned : s'.Mentions (s.label o) := by
        refine Or.inr (Or.inr ⟨o, hides.present ▸ present, ?_⟩)
        rw [hides.label]
      exact A.equivalence.trans (onMentions _ mentioned) (near _ ⟨o, present, rfl⟩)
    · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
      have h : A.E (A.apply u (A.apply f.opening t₀)) (A.apply (A.compose σ f.opening) t₀) :=
        onRule t₀ member
      rwa [A.apply_compose] at h
  refine ⟨u, ?_, agree⟩
  rw [information_eq_append]
  refine (A.models_append u _ _).mpr ⟨models_of_agree (fun t member => onMentions t ?_) onK', ?_⟩
  · rcases member with first | second
    · exact Or.inl first
    · exact Or.inr (Or.inl second)
  · rw [← ownInformation_congr f hides.label]
    exact models_of_agree (fun t member => agree t (own_terms enabled member)) onOwn

theorem pattern_mem_terms {r : Rule (Terms T)} {c : Check (Terms T r.locals)} (member : c ∈ r.body.checks)
    {p : Terms T r.locals} (pattern : p ∈ checkTerms c) : p ∈ r.terms := by
  have inChecks : p ∈ r.body.checks.flatMap checkTerms := List.mem_flatMap.mpr ⟨c, member, pattern⟩
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

theorem collect_mem_terms {r : Rule (Terms T)} {p : Terms T r.locals} (member : p ∈ r.collect) :
    p ∈ r.terms := by
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

omit [DecidableEq O] in
theorem matchesAt_congr_agree {s : State (Terms T) O} {f : Firing O (ext A) P PUnit.unit} {ρ σ : S}
    (agree : AgreeOn A ρ σ (RowsOrOpened A s f)) {p : T} (opened : RowsOrOpened A s f p) :
    matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) ρ (f.row (frames A) s) s.present p =
      matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ (f.row (frames A) s) s.present p := by
  ext o
  rw [mem_matchesAt, mem_matchesAt]
  constructor
  · rintro ⟨present, equated⟩
    exact ⟨present, (e_congr (agree p opened) (agree _ (rowsOrOpened_row f present))).mp equated⟩
  · rintro ⟨present, equated⟩
    exact ⟨present, (e_congr (agree p opened) (agree _ (rowsOrOpened_row f present))).mpr equated⟩

omit [DecidableEq O] in
/-- **The guard reads a solution only on the rows and the opened terms.** -/
theorem holds_iff_of_agree {s : State (Terms T) O} {f : Firing O (ext A) P PUnit.unit} {ρ σ : S}
    (agree : AgreeOn A ρ σ (RowsOrOpened A s f)) :
    f.Holds (frames A) s (b := PUnit.unit) ρ ↔ f.Holds (frames A) s (b := PUnit.unit) σ := by
  unfold Firing.Holds
  apply and_congr
  · refine forall₂_congr fun c member => ?_
    obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp member
    cases c₀ with
    | equal l r =>
        have left := agree _ (rowsOrOpened_opened (s := s) f (pattern_mem_terms inRule
          (by simp [checkTerms] : l ∈ checkTerms (Check.equal l r))))
        have right := agree _ (rowsOrOpened_opened (s := s) f (pattern_mem_terms inRule
          (by simp [checkTerms] : r ∈ checkTerms (Check.equal l r))))
        exact e_congr left right
    | predicate quantifier p =>
        have opened := rowsOrOpened_opened (s := s) f (pattern_mem_terms inRule
          (by simp [checkTerms] : p ∈ checkTerms (Check.predicate quantifier p)))
        show quantifier.Holds s.present
            (fun o => A.E (A.apply ρ (A.apply f.opening p)) (A.apply ρ (f.row (frames A) s o))) ↔
          quantifier.Holds s.present
            (fun o => A.E (A.apply σ (A.apply f.opening p)) (A.apply σ (f.row (frames A) s o)))
        exact quantifier.holds_congr fun o present =>
          e_congr (agree _ opened) (agree _ (rowsOrOpened_row f present))
    | count p n =>
        have opened := rowsOrOpened_opened (s := s) f (pattern_mem_terms inRule
          (by simp [checkTerms] : p ∈ checkTerms (Check.count p n)))
        show (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) ρ _ _ (A.apply f.opening p)).card = n ↔
          (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ _ _ (A.apply f.opening p)).card = n
        rw [matchesAt_congr_agree agree opened]
  · refine forall₂_congr fun q member => ?_
    obtain ⟨p₀, inCollect, isFirst⟩ := List.mem_map.mp (List.of_mem_zip member).1
    have opened : RowsOrOpened A s f q.1 := by
      rw [← isFirst]
      exact rowsOrOpened_opened f (collect_mem_terms inCollect)
    show matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) ρ _ _ q.1 = q.2 ↔
      matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ _ _ q.1 = q.2
    rw [matchesAt_congr_agree agree opened]

omit [DecidableEq O] in
theorem holds_congr_rows {s s' : State (Terms T) O} (present : s.present = s'.present)
    (label : s.label = s'.label) (f : Firing O (ext A) P PUnit.unit) (σ : S) :
    f.Holds (frames A) s (b := PUnit.unit) σ ↔ f.Holds (frames A) s' (b := PUnit.unit) σ := by
  have rows : f.row (frames A) s = f.row (frames A) s' := by
    funext o
    unfold Firing.row
    rw [label]
  unfold Firing.Holds
  rw [rows, present]

/-- **For an opening fresh at both states, admission is the same.** -/
theorem admits_of_hides {s s' : State (Terms T) O} (hides : Hides A s s') {f : Firing O (ext A) P PUnit.unit}
    (fresh : f.Fresh (frames A) s) (fresh' : f.Fresh (frames A) s')
    (admitted : (step (frames A) O (ext A) P).Admits (s := s) f) :
    (step (frames A) O (ext A) P).Admits (s := s') f := by
  obtain ⟨⟨-, rest⟩, enabled, ⟨_, σ, solved⟩, asked⟩ := admitted
  have enabled' : Enabled (fun _ : O => ()) s'.present (f.selection.commit (T := Unit)) := by
    rw [← hides.present]
    exact enabled
  obtain ⟨u, solved', -⟩ := transfer hides enabled fresh' solved
  refine ⟨⟨fresh', rest⟩, enabled', ⟨PUnit.unit, u, solved'⟩, fun b ρ onInfo => ?_⟩
  obtain ⟨v, onInfoS, near⟩ := transfer hides.symm enabled' fresh onInfo
  have atS : f.Holds (frames A) s (b := PUnit.unit) v := asked PUnit.unit v onInfoS
  have atS' : f.Holds (frames A) s' (b := PUnit.unit) v :=
    (holds_congr_rows hides.present hides.label f v).mp atS
  exact (holds_iff_of_agree near).mp atS'

theorem admits_iff_of_hides {s s' : State (Terms T) O} (hides : Hides A s s')
    {f : Firing O (ext A) P PUnit.unit} (fresh : f.Fresh (frames A) s) (fresh' : f.Fresh (frames A) s') :
    (step (frames A) O (ext A) P).Admits (s := s) f ↔ (step (frames A) O (ext A) P).Admits (s := s') f :=
  ⟨admits_of_hides hides fresh fresh', admits_of_hides hides.symm fresh' fresh⟩

/-- What the result's rows are: kept rows of the state, and made rows of the opened rule. -/
theorem rows_result {s : State (Terms T) O} {f : Firing O (ext A) P PUnit.unit}
    (shapes : f.Shapes (frames A) s) {t : T} (row : Rows (f.result (frames A) s) t) :
    RowsOrOpened A s f t := by
  obtain ⟨o, present, rfl⟩ := row
  by_cases isMade : o ∈ f.selection.made
  · have lengths : f.selection.made.length = (f.opened (frames A)).produce.length := by
      simp only [Firing.opened, RuleInstance.map, List.length_map]
      exact shapes.2.2.2.2.2.1.symm
    obtain ⟨t', inside⟩ := exists_mem_zip_left _ _ lengths o isMade
    rw [Firing.result_label_made f shapes inside]
    obtain ⟨t₀, member₀, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).2
    exact rowsOrOpened_opened f (produce_mem_terms member₀)
  · rw [Firing.result_label_other (s := s) f isMade]
    have inS : o ∈ s.present := by
      rcases mem_fire.mp present with ⟨inS, -⟩ | made
      · exact inS
      · exact absurd (List.mem_toFinset.mp made) isMade
    exact rowsOrOpened_row f inS

/-- **The results hide each other.** -/
theorem hides_result {s s' : State (Terms T) O} (hides : Hides A s s') {f : Firing O (ext A) P PUnit.unit}
    (fresh : f.Fresh (frames A) s) (fresh' : f.Fresh (frames A) s')
    (admitted : (step (frames A) O (ext A) P).Admits (s := s) f) :
    Hides A (f.result (frames A) s) (f.result (frames A) s') := by
  obtain ⟨⟨-, rest⟩, enabled, -, -⟩ := admitted
  have shapes : f.Shapes (frames A) s := ⟨fresh, rest⟩
  have shapes' : f.Shapes (frames A) s' := ⟨fresh', rest⟩
  have enabled' : Enabled (fun _ : O => ()) s'.present (f.selection.commit (T := Unit)) := by
    rw [← hides.present]
    exact enabled
  have rows : f.row (frames A) s = f.row (frames A) s' := by
    funext o
    unfold Firing.row
    rw [hides.label]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show fire s.present _ = fire s'.present _
    rw [hides.present]
  · show relabel (f.row (frames A) s) f.selection.made (f.opened (frames A)).produce =
      relabel (f.row (frames A) s') f.selection.made (f.opened (frames A)).produce
    rw [rows]
  · intro σ solved
    obtain ⟨u, solved', near⟩ := transfer hides enabled fresh' solved
    exact ⟨u, solved', fun t row => near t (rows_result shapes row)⟩
  · intro σ' solved'
    obtain ⟨u, solved, near⟩ := transfer hides.symm enabled' fresh solved'
    refine ⟨u, solved, fun t row => near t ?_⟩
    have row' : Rows (f.result (frames A) s') t := by
      obtain ⟨o, present, labelled⟩ := row
      refine ⟨o, ?_, ?_⟩
      · show o ∈ fire s'.present _
        rw [← hides.present]
        exact present
      · rw [← labelled]
        show relabel (f.row (frames A) s') f.selection.made (f.opened (frames A)).produce o =
          relabel (f.row (frames A) s) f.selection.made (f.opened (frames A)).produce o
        rw [rows]
    exact rows_result shapes' row'

end Transfer

#print axioms transfer
#print axioms holds_iff_of_agree
#print axioms admits_iff_of_hides
#print axioms hides_result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
