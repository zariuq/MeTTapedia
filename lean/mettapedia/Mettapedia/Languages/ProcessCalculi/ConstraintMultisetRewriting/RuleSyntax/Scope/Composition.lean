import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Independence

/-!
# Composition restored: systems side by side whose unknowns are private

At the one-frame action of a substitution action, with the identity extension, two states are put
side by side (`beside D C`): the neighbour's knowledge, then the system's; the union of the present
rows; each row labelled as at the side where it is present.

## The footprint of a firing, and privacy

The **footprint** of a firing at a state (`Footprint`) is what the state mentions (its knowledge and
the labels of its present rows) together with the terms of the rule along the opening. Everything
the firing's information and its result mention lies in its footprint (`footprint_of_information`,
`footprint_of_result`). A system is **private from** a neighbour (`PrivateFrom`) when the neighbour's
terms are independent of what the system mentions (`Independent`): at first-order terms, when they
share no unknown (`independent_iff_disjoint`).

A rule is **positive** (`Positive`) when its checks are equations and it has no collect query.

## Admission beside a private neighbour

* **`admits_beside_iff`, what sharing costs, exactly**: a positive firing admitted at `C`, whose made
  identities are new to `D` and whose opening is fresh beside `D`, is admitted beside `D` exactly when
  one solution solves both its information at `C` and the knowledge of `D`.
* **`admits_beside`**: such a joint solution exists, and the opening stays fresh, whenever `D`'s
  knowledge is solvable and `D` is independent of the firing's footprint. So positive admission is
  monotone under composition with a neighbour that shares no unknown with the firing.
* **`admits_of_beside`**: conversely, a positive firing whose takes and reads are rows of `C`, admitted
  beside such a neighbour, is admitted at `C` alone; `admits_beside_iff_alone` states both.
* **`result_beside`**: the result of the firing beside `D` is `D` beside its result at `C`.

## Runs and success

A **private step** (`PrivateStep`) of a system beside a neighbour is a positive admitted firing whose
footprint is independent of the neighbour and whose made identities are new to it.

* `privateFrom_of_step`, `privateFrom_along`: **privacy is a property of reachable states**: along
  private steps the system stays private from the neighbour.
* `runs_beside`: every run of private steps from `C` is a run of the step from `D` beside `C`, to `D`
  beside the end of the run.
* **`success_persists`**: reachable success (a present row whose label satisfies a barb, `Succeeds`)
  persists beside a solvable neighbour, along private runs.

Each hypothesis has its control in `CompositionControls`: a shared unknown (the knowledge of a
neighbour without rows contradicting a tell on an unknown the system's row carries) refuses the
firing and switches success off; absence over ground rows, independent of everything, is refused
beside a ground row; an unsolvable neighbour refuses; a neighbour mentioning the firing's own opened
unknown makes the opening not fresh.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

universe uT uS uO uA uB uC

/-! ## List and label helpers -/

section Helpers

theorem exists_mem_zip_left {α : Type uA} {β : Type uB} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length → ∀ a ∈ l₁, ∃ b, (a, b) ∈ l₁.zip l₂
  | [], _, _, _, inside => by cases inside
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | a' :: as, b :: bs, lengths, a, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨b, List.mem_cons_self⟩
      · obtain ⟨b', paired⟩ := exists_mem_zip_left as bs (Nat.succ.inj lengths) a later
        exact ⟨b', List.mem_cons_of_mem _ paired⟩

theorem zipWith_congr_right {α : Type uA} {β : Type uB} {γ : Type uC} (g h : α → β → γ) :
    ∀ (l : List α) (m : List β), (∀ b ∈ m, ∀ a, g a b = h a b) → l.zipWith g m = l.zipWith h m
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: as, b :: bs, same => by
      simp only [List.zipWith_cons_cons]
      rw [same b List.mem_cons_self a,
        zipWith_congr_right g h as bs fun b' member a' => same b' (List.mem_cons_of_mem _ member) a']

theorem relabel_congr {Obj : Type uA} {Tm : Obj → Type uB} {O : Type uO} [DecidableEq O] {a : Obj}
    {old old' : O → Tm a} {o : O} (same : old o = old' o) :
    ∀ (made : List O) (rows : List (Tm a)), relabel old made rows o = relabel old' made rows o
  | [], _ => same
  | _ :: _, [] => same
  | o' :: rest, t :: ts => by
      simp only [relabel]
      split_ifs
      · rfl
      · exact relabel_congr same rest ts

end Helpers

/-! ## Rule terms -/

section RuleTerms

variable {Obj : Type uA} {Tm : Obj → Type uB}

theorem take_mem_terms {r : Rule Tm} {t : Tm r.locals} (member : t ∈ r.body.take) :
    t ∈ r.terms := by
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

theorem read_mem_terms {r : Rule Tm} {t : Tm r.locals} (member : t ∈ r.body.read) :
    t ∈ r.terms := by
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

theorem tell_mem_terms {r : Rule Tm} {e : Equation (Tm r.locals)} (member : e ∈ r.body.tell) :
    e.1 ∈ r.terms ∧ e.2 ∈ r.terms := by
  have first : e.1 ∈ r.body.tell.map Prod.fst := List.mem_map.mpr ⟨e, member, rfl⟩
  have second : e.2 ∈ r.body.tell.map Prod.snd := List.mem_map.mpr ⟨e, member, rfl⟩
  unfold Rule.terms
  simp only [List.mem_append]
  exact ⟨by tauto, by tauto⟩

theorem produce_mem_terms {r : Rule Tm} {t : Tm r.locals} (member : t ∈ r.body.produce) :
    t ∈ r.terms := by
  unfold Rule.terms
  simp only [List.mem_append]
  tauto

theorem equal_mem_terms {r : Rule Tm} {l l' : Tm r.locals} (member : Check.equal l l' ∈ r.body.checks) :
    l ∈ r.terms ∧ l' ∈ r.terms := by
  have first : l ∈ r.body.checks.flatMap checkTerms :=
    List.mem_flatMap.mpr ⟨_, member, by simp [checkTerms]⟩
  have second : l' ∈ r.body.checks.flatMap checkTerms :=
    List.mem_flatMap.mpr ⟨_, member, by simp [checkTerms]⟩
  unfold Rule.terms
  simp only [List.mem_append]
  exact ⟨by tauto, by tauto⟩

/-- **A positive rule**: its checks are equations, and it has no collect query. -/
def Positive (r : Rule Tm) : Prop :=
  (∀ c ∈ r.body.checks, ∃ l l', c = Check.equal l l') ∧ r.collect = []

end RuleTerms

/-! ## Two systems side by side -/

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]

/-- **Two systems side by side** at the one frame: the neighbour's knowledge, then the system's; the
union of the present rows; each row labelled as at the side where it is present. -/
def beside (D C : State (Terms T) O) : State (Terms T) O :=
  ⟨PUnit.unit, D.knowledge ++ C.knowledge, D.present ∪ C.present,
    fun o => if o ∈ D.present then D.label o else C.label o⟩

/-- **The footprint of a firing at a state**: what the state mentions, and the terms of the rule
along its opening. -/
def Footprint {P : Program (Terms T)} (s : State (Terms T) O) (f : Firing O (ext A) P PUnit.unit)
    (t : T) : Prop :=
  s.Mentions t ∨ t ∈ f.rule.terms.map (A.apply f.opening)

/-- **A system is private from a neighbour** when the neighbour's terms are independent of what the
system mentions. -/
def PrivateFrom (D C : State (Terms T) O) : Prop := Independent A D.Mentions C.Mentions

omit [DecidableEq O] in
/-- A state with knowledge, present rows and labels as given is determined by them. -/
theorem state_ext {s t : State (Terms T) O} (knowledge : s.knowledge = t.knowledge)
    (present : s.present = t.present) (label : s.label = t.label) : s = t := by
  obtain ⟨⟨⟩, k, p, l⟩ := s
  obtain ⟨⟨⟩, k', p', l'⟩ := t
  dsimp only at knowledge present label
  subst knowledge present label
  rfl

section Beside

variable {D C : State (Terms T) O}

theorem beside_label_left {o : O} (inD : o ∈ D.present) : (beside D C).label o = D.label o :=
  if_pos inD

theorem beside_label_right (apart : Disjoint D.present C.present) {o : O} (inC : o ∈ C.present) :
    (beside D C).label o = C.label o :=
  if_neg (Finset.disjoint_right.mp apart inC)

/-- **What two systems side by side mention is what each mentions.** -/
theorem mentions_beside (apart : Disjoint D.present C.present) (t : T) :
    (beside D C).Mentions t ↔ D.Mentions t ∨ C.Mentions t := by
  have first : t ∈ (beside D C).knowledge.map Prod.fst ↔
      t ∈ D.knowledge.map Prod.fst ∨ t ∈ C.knowledge.map Prod.fst := by
    show t ∈ (D.knowledge ++ C.knowledge).map Prod.fst ↔ _
    rw [List.map_append, List.mem_append]
  have second : t ∈ (beside D C).knowledge.map Prod.snd ↔
      t ∈ D.knowledge.map Prod.snd ∨ t ∈ C.knowledge.map Prod.snd := by
    show t ∈ (D.knowledge ++ C.knowledge).map Prod.snd ↔ _
    rw [List.map_append, List.mem_append]
  have rows : (∃ o ∈ (beside D C).present, (beside D C).label o = t) ↔
      (∃ o ∈ D.present, D.label o = t) ∨ ∃ o ∈ C.present, C.label o = t := by
    constructor
    · rintro ⟨o, present, labelled⟩
      rcases Finset.mem_union.mp present with inD | inC
      · exact Or.inl ⟨o, inD, (beside_label_left inD).symm.trans labelled⟩
      · exact Or.inr ⟨o, inC, (beside_label_right apart inC).symm.trans labelled⟩
    · rintro (⟨o, inD, labelled⟩ | ⟨o, inC, labelled⟩)
      · exact ⟨o, Finset.mem_union_left _ inD, (beside_label_left inD).trans labelled⟩
      · exact ⟨o, Finset.mem_union_right _ inC, (beside_label_right apart inC).trans labelled⟩
  unfold State.Mentions
  rw [first, second, rows]
  constructor
  · rintro ((h | h) | (h | h) | (h | h))
    exacts [Or.inl (Or.inl h), Or.inr (Or.inl h), Or.inl (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inl h)), Or.inl (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inr h))]
  · rintro ((h | h | h) | (h | h | h))
    exacts [Or.inl (Or.inl h), Or.inr (Or.inl (Or.inl h)), Or.inr (Or.inr (Or.inl h)),
      Or.inl (Or.inr h), Or.inr (Or.inl (Or.inr h)), Or.inr (Or.inr (Or.inr h))]

theorem selected_of_enabled {selection : Selection O}
    (enabled : Enabled (fun _ : O => ()) C.present (selection.commit (T := Unit))) :
    ∀ o, o ∈ selection.taken ∨ o ∈ selection.read → o ∈ C.present := by
  rintro o (taken | read)
  · exact enabled.taken_subset (List.mem_toFinset.mpr taken)
  · exact enabled.kept_subset (List.mem_toFinset.mpr read)

theorem enabled_beside {selection : Selection O}
    (enabled : Enabled (fun _ : O => ()) C.present (selection.commit (T := Unit)))
    (madeNew : ∀ o ∈ selection.made, o ∉ D.present) :
    Enabled (fun _ : O => ()) (beside D C).present (selection.commit (T := Unit)) := by
  refine ⟨fun o member => Finset.mem_union_right _ (enabled.taken_subset member),
    fun o member => Finset.mem_union_right _ (enabled.kept_subset member), enabled.apart, ?_,
    fun q member => by simp [Selection.commit] at member⟩
  show Disjoint _ (D.present ∪ C.present)
  rw [Finset.disjoint_union_right]
  exact ⟨Finset.disjoint_left.mpr fun {o} made inD => madeNew o (List.mem_toFinset.mp made) inD,
    enabled.fresh⟩

variable {P : Program (Terms T)}

theorem row_beside (f : Firing O (ext A) P PUnit.unit) (apart : Disjoint D.present C.present)
    {o : O} (inC : o ∈ C.present) :
    f.row (frames A) (beside D C) o = f.row (frames A) C o := by
  unfold Firing.row
  rw [beside_label_right apart inC]

theorem matching_beside (f : Firing O (ext A) P PUnit.unit) (apart : Disjoint D.present C.present)
    (patterns : List T) {selected : List O} (inC : ∀ o ∈ selected, o ∈ C.present) :
    f.matching (frames A) (beside D C) patterns selected = f.matching (frames A) C patterns selected := by
  unfold Firing.matching
  exact zipWith_congr_right _ _ patterns selected fun o member _ => by
    rw [row_beside A f apart (inC o member)]

/-- **The information beside a neighbour** is the neighbour's knowledge, then the information at the
system, when the firing takes and reads rows of the system. -/
theorem information_beside (f : Firing O (ext A) P PUnit.unit) (apart : Disjoint D.present C.present)
    (selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ C.present) :
    f.information (frames A) (beside D C) = D.knowledge ++ f.information (frames A) C := by
  unfold Firing.information
  have known : (frames A).applyStore ((ext A).weaken f.ext) (beside D C).knowledge =
      D.knowledge ++ (frames A).applyStore ((ext A).weaken f.ext) C.knowledge := by
    show (frames A).applyStore ((frames A).id PUnit.unit) (D.knowledge ++ C.knowledge) =
      D.knowledge ++ (frames A).applyStore ((frames A).id PUnit.unit) C.knowledge
    rw [Frames.applyStore_id, Frames.applyStore_id]
  rw [known, matching_beside A f apart _ fun o member => selected o (Or.inl member),
    matching_beside A f apart _ fun o member => selected o (Or.inr member)]
  simp only [List.append_assoc]

/-- **Everything the information mentions lies in the footprint.** -/
theorem footprint_of_information {f : Firing O (ext A) P PUnit.unit}
    (enabled : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit))) {t : T}
    (mentioned : StoreTerms (f.information (frames A) C) t) : Footprint A C f t := by
  have rowFoot : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read →
      Footprint A C f (f.row (frames A) C o) := by
    intro o selected
    refine Or.inl ?_
    show C.Mentions (A.apply A.identity (C.label o))
    rw [A.apply_identity]
    exact Or.inr (Or.inr ⟨o, selected_of_enabled enabled o selected, rfl⟩)
  have openedFoot : ∀ t₀ ∈ f.rule.terms, Footprint A C f (A.apply f.opening t₀) :=
    fun t₀ member => Or.inr (List.mem_map.mpr ⟨t₀, member, rfl⟩)
  have sides : ∀ e ∈ f.information (frames A) C, Footprint A C f e.1 ∧ Footprint A C f e.2 := by
    intro e member
    unfold Firing.information at member
    simp only [List.mem_append] at member
    rcases member with ((known | taken) | read) | told
    · obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp known
      have left : C.Mentions e₀.1 := Or.inl (List.mem_map.mpr ⟨e₀, inside, rfl⟩)
      have right : C.Mentions e₀.2 := Or.inr (Or.inl (List.mem_map.mpr ⟨e₀, inside, rfl⟩))
      refine ⟨Or.inl ?_, Or.inl ?_⟩
      · show C.Mentions (A.apply A.identity e₀.1)
        rw [A.apply_identity]
        exact left
      · show C.Mentions (A.apply A.identity e₀.2)
        rw [A.apply_identity]
        exact right
    · unfold Firing.matching at taken
      rw [← List.map_uncurry_zip_eq_zipWith] at taken
      obtain ⟨⟨p, o⟩, inside, rfl⟩ := List.mem_map.mp taken
      obtain ⟨p₀, member₀, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).1
      exact ⟨openedFoot p₀ (take_mem_terms member₀), rowFoot o (Or.inl (List.of_mem_zip inside).2)⟩
    · unfold Firing.matching at read
      rw [← List.map_uncurry_zip_eq_zipWith] at read
      obtain ⟨⟨p, o⟩, inside, rfl⟩ := List.mem_map.mp read
      obtain ⟨p₀, member₀, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).1
      exact ⟨openedFoot p₀ (read_mem_terms member₀), rowFoot o (Or.inr (List.of_mem_zip inside).2)⟩
    · obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp told
      exact ⟨openedFoot e₀.1 (tell_mem_terms inside).1, openedFoot e₀.2 (tell_mem_terms inside).2⟩
  rcases mentioned with first | second
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp first
    exact (sides e member).1
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp second
    exact (sides e member).2

/-- A substitution agreeing with a solution of the information on the footprint solves it. -/
theorem models_information_of_agree {f : Firing O (ext A) P PUnit.unit} {ρ σ : S}
    (enabled : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)))
    (agree : ∀ t, Footprint A C f t → A.E (A.apply ρ t) (A.apply σ t))
    (solved : A.Models σ (f.information (frames A) C)) : A.Models ρ (f.information (frames A) C) :=
  models_of_agree (fun t member => agree t (footprint_of_information A enabled member)) solved

/-- **Everything the result mentions lies in the footprint.** -/
theorem footprint_of_result {f : Firing O (ext A) P PUnit.unit} (shapes : f.Shapes (frames A) C)
    (enabled : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit))) {t : T}
    (mentioned : (f.result (frames A) C).Mentions t) : Footprint A C f t := by
  rcases mentioned with first | second | ⟨o, present, rfl⟩
  · exact footprint_of_information A enabled (Or.inl first)
  · exact footprint_of_information A enabled (Or.inr second)
  · by_cases isMade : o ∈ f.selection.made
    · have lengths : f.selection.made.length = (f.opened (frames A)).produce.length := by
        simp only [Firing.opened, RuleInstance.map, List.length_map]
        exact shapes.2.2.2.2.2.1.symm
      obtain ⟨t', inside⟩ := exists_mem_zip_left _ _ lengths o isMade
      rw [Firing.result_label_made f shapes inside]
      obtain ⟨t₀, member₀, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).2
      exact Or.inr (List.mem_map.mpr ⟨t₀, produce_mem_terms member₀, rfl⟩)
    · rw [Firing.result_label_other (s := C) f isMade]
      have inC : o ∈ C.present := by
        rcases mem_fire.mp present with ⟨inC, -⟩ | made
        · exact inC
        · exact absurd (List.mem_toFinset.mp made) isMade
      refine Or.inl ?_
      show C.Mentions (A.apply A.identity (C.label o))
      rw [A.apply_identity]
      exact Or.inr (Or.inr ⟨o, inC, rfl⟩)

omit [DecidableEq O] in
theorem opened_check_equal {f : Firing O (ext A) P PUnit.unit} (positive : Positive f.rule)
    {c : Check T} (member : c ∈ (f.opened (frames A)).checks) :
    ∃ c₀ ∈ f.rule.body.checks, ∃ l l', c₀ = Check.equal l l' ∧
      c = Check.equal (A.apply f.opening l) (A.apply f.opening l') := by
  obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp member
  obtain ⟨l, l', rfl⟩ := positive.1 c₀ inRule
  exact ⟨_, inRule, l, l', rfl, rfl⟩

omit [DecidableEq O] in
/-- **A positive firing's guard does not read the rows.** -/
theorem holds_of_positive {f : Firing O (ext A) P PUnit.unit} (positive : Positive f.rule)
    {s s' : State (Terms T) O} {σ : S} (holds : f.Holds (frames A) s (b := PUnit.unit) σ) :
    f.Holds (frames A) s' (b := PUnit.unit) σ := by
  refine ⟨fun c member => ?_, fun q member => ?_⟩
  · obtain ⟨_, _, l, l', -, rfl⟩ := opened_check_equal A positive member
    exact holds.1 _ member
  · simp [Firing.collectOpened, positive.2] at member

/-- **Freshness beside a neighbour**: an opening fresh at the system stays fresh beside a neighbour
independent of the firing's footprint. -/
theorem fresh_beside {f : Firing O (ext A) P PUnit.unit} (fresh : f.Fresh (frames A) C)
    (apart : Disjoint D.present C.present) (independent : Independent A D.Mentions (Footprint A C f)) :
    f.Fresh (frames A) (beside D C) := by
  intro b g h
  obtain ⟨u, onC, onRule⟩ := fresh b g h
  obtain ⟨ρ, onD, onFoot⟩ := independent g u
  refine ⟨ρ, fun t mentioned => ?_, fun t member => ?_⟩
  · show A.E (A.apply ρ (A.apply A.identity t)) (A.apply g t)
    rw [A.apply_identity]
    rcases (mentions_beside apart t).mp mentioned with inD | inC
    · exact onD t inD
    · have viaU : A.E (A.apply u (A.apply A.identity t)) (A.apply g t) := onC t inC
      rw [A.apply_identity] at viaU
      exact A.equivalence.trans (onFoot t (Or.inl inC)) viaU
  · show A.E (A.apply ρ (A.apply f.opening t)) (A.apply h t)
    exact A.equivalence.trans (onFoot _ (Or.inr (List.mem_map.mpr ⟨t, member, rfl⟩))) (onRule t member)

/-- **Freshness is antitone in what the state mentions**: fresh beside a neighbour is fresh alone. -/
theorem fresh_of_beside {f : Firing O (ext A) P PUnit.unit} (fresh : f.Fresh (frames A) (beside D C))
    (apart : Disjoint D.present C.present) : f.Fresh (frames A) C := by
  intro b g h
  obtain ⟨u, onBeside, onRule⟩ := fresh b g h
  exact ⟨u, fun t mentioned => onBeside t ((mentions_beside apart t).mpr (Or.inr mentioned)), onRule⟩

/-- **The joint solution exists** when the neighbour is solvable and independent of the footprint. -/
theorem joint_of_independent {f : Firing O (ext A) P PUnit.unit}
    (enabled : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)))
    (solvable : (frames A).Solvable (f.information (frames A) C))
    (solvableD : A.Consistent D.knowledge) (independent : Independent A D.Mentions (Footprint A C f)) :
    ∃ σ : S, A.Models σ (f.information (frames A) C) ∧ A.Models σ D.knowledge := by
  obtain ⟨_, σ, solved⟩ := solvable
  obtain ⟨τ, onD⟩ := solvableD
  obtain ⟨ρ, nearD, nearFoot⟩ := independent τ σ
  refine ⟨ρ, models_information_of_agree A enabled nearFoot solved, models_of_agree ?_ onD⟩
  intro t member
  rcases member with first | second
  · exact nearD t (Or.inl first)
  · exact nearD t (Or.inr (Or.inl second))

/-- **What sharing costs, exactly.** A positive firing admitted at `C`, whose made identities are new
to `D` and whose opening is fresh beside `D`, is admitted beside `D` exactly when one solution solves
both its information at `C` and the knowledge of `D`. -/
theorem admits_beside_iff {f : Firing O (ext A) P PUnit.unit} (positive : Positive f.rule)
    (admitted : (step (frames A) O (ext A) P).Admits (s := C) f)
    (apart : Disjoint D.present C.present) (madeNew : ∀ o ∈ f.selection.made, o ∉ D.present)
    (fresh : f.Fresh (frames A) (beside D C)) :
    (step (frames A) O (ext A) P).Admits (s := beside D C) f ↔
      ∃ σ : S, A.Models σ (f.information (frames A) C) ∧ A.Models σ D.knowledge := by
  obtain ⟨-, shapes, enabled, -, checks, -⟩ := (admits_iff (s := C) f).mp admitted
  have known := information_beside A f apart (selected_of_enabled enabled)
  constructor
  · intro admittedBeside
    obtain ⟨-, -, -, ⟨_, σ, solved⟩, -, -⟩ := (admits_iff (s := beside D C) f).mp admittedBeside
    rw [known] at solved
    obtain ⟨onD, onC⟩ := (Frames.models_append _ _ _).mp solved
    exact ⟨σ, onC, onD⟩
  · rintro ⟨σ, onC, onD⟩
    refine (admits_iff (s := beside D C) f).mpr ⟨fresh, shapes, enabled_beside enabled madeNew, ?_, ?_,
      ?_⟩
    · rw [known]
      exact ⟨PUnit.unit, σ, (Frames.models_append _ _ _).mpr ⟨onD, onC⟩⟩
    · intro c member b ρ solved
      rw [known] at solved
      have onC' := ((Frames.models_append _ _ _).mp solved).2
      obtain ⟨_, _, l, l', -, rfl⟩ := opened_check_equal A positive member
      exact checks _ member b ρ onC'
    · intro q member
      simp [Firing.collectOpened, positive.2] at member

/-- **Positive admission is monotone under composition with a private neighbour**: a positive firing
admitted at `C` is admitted beside any neighbour whose knowledge is solvable and whose terms are
independent of the firing's footprint, when its made identities are new to the neighbour. -/
theorem admits_beside {f : Firing O (ext A) P PUnit.unit} (positive : Positive f.rule)
    (admitted : (step (frames A) O (ext A) P).Admits (s := C) f)
    (apart : Disjoint D.present C.present) (madeNew : ∀ o ∈ f.selection.made, o ∉ D.present)
    (solvableD : A.Consistent D.knowledge) (independent : Independent A D.Mentions (Footprint A C f)) :
    (step (frames A) O (ext A) P).Admits (s := beside D C) f := by
  obtain ⟨fresh, -, enabled, solvable, -, -⟩ := (admits_iff (s := C) f).mp admitted
  exact (admits_beside_iff A positive admitted apart madeNew (fresh_beside A fresh apart independent)).mpr
    (joint_of_independent A enabled solvable solvableD independent)

/-- **Conversely, beside a private neighbour a positive firing of the system is admitted only if it
is admitted alone**, when it takes and reads rows of the system. -/
theorem admits_of_beside {f : Firing O (ext A) P PUnit.unit} (positive : Positive f.rule)
    (admittedBeside : (step (frames A) O (ext A) P).Admits (s := beside D C) f)
    (apart : Disjoint D.present C.present)
    (selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ C.present)
    (solvableD : A.Consistent D.knowledge) (independent : Independent A D.Mentions (Footprint A C f)) :
    (step (frames A) O (ext A) P).Admits (s := C) f := by
  obtain ⟨fresh, shapes, enabledBeside, solvable, checks, -⟩ :=
    (admits_iff (s := beside D C) f).mp admittedBeside
  have known := information_beside A f apart selected
  have enabled : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) := by
    refine ⟨fun o member => selected o (Or.inl (List.mem_toFinset.mp member)),
      fun o member => selected o (Or.inr (List.mem_toFinset.mp member)), enabledBeside.apart, ?_,
      fun q member => by simp [Selection.commit] at member⟩
    have beside' : Disjoint _ (D.present ∪ C.present) := enabledBeside.fresh
    exact (Finset.disjoint_union_right.mp beside').2
  refine (admits_iff (s := C) f).mpr ⟨fresh_of_beside A fresh apart, shapes, enabled, ?_, ?_, ?_⟩
  · rw [known] at solvable
    obtain ⟨b, σ, solved⟩ := solvable
    exact ⟨b, σ, ((Frames.models_append _ _ _).mp solved).2⟩
  · intro c member b σ solved
    obtain ⟨τ, onD⟩ := solvableD
    obtain ⟨ρ, nearD, nearFoot⟩ := independent τ σ
    have onC : A.Models ρ (f.information (frames A) C) :=
      models_information_of_agree A enabled nearFoot solved
    have onDρ : A.Models ρ D.knowledge := by
      refine models_of_agree (fun t member => ?_) onD
      rcases member with first | second
      · exact nearD t (Or.inl first)
      · exact nearD t (Or.inr (Or.inl second))
    have solvedBeside : (frames A).Models (a := PUnit.unit) (b := PUnit.unit) ρ
        (f.information (frames A) (beside D C)) := by
      rw [known]
      exact (Frames.models_append _ _ _).mpr ⟨onDρ, onC⟩
    obtain ⟨c₀, inRule, l, l', rfl, rfl⟩ := opened_check_equal A positive member
    have atρ : A.E (A.apply ρ (A.apply f.opening l)) (A.apply ρ (A.apply f.opening l')) :=
      checks _ member PUnit.unit ρ solvedBeside
    have terms := equal_mem_terms inRule
    have nearL : A.E (A.apply ρ (A.apply f.opening l)) (A.apply σ (A.apply f.opening l)) :=
      nearFoot _ (Or.inr (List.mem_map.mpr ⟨l, terms.1, rfl⟩))
    have nearL' : A.E (A.apply ρ (A.apply f.opening l')) (A.apply σ (A.apply f.opening l')) :=
      nearFoot _ (Or.inr (List.mem_map.mpr ⟨l', terms.2, rfl⟩))
    show A.E (A.apply σ (A.apply f.opening l)) (A.apply σ (A.apply f.opening l'))
    exact A.equivalence.trans (A.equivalence.symm nearL) (A.equivalence.trans atρ nearL')
  · intro q member
    simp [Firing.collectOpened, positive.2] at member

/-- **Beside a solvable neighbour that shares no unknown with its footprint, a positive firing of the
system is admitted exactly when it is admitted alone**, when it takes and reads rows of the system
and makes identities new to the neighbour. -/
theorem admits_beside_iff_alone {f : Firing O (ext A) P PUnit.unit} (positive : Positive f.rule)
    (apart : Disjoint D.present C.present)
    (selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ C.present)
    (madeNew : ∀ o ∈ f.selection.made, o ∉ D.present)
    (solvableD : A.Consistent D.knowledge) (independent : Independent A D.Mentions (Footprint A C f)) :
    (step (frames A) O (ext A) P).Admits (s := beside D C) f ↔
      (step (frames A) O (ext A) P).Admits (s := C) f :=
  ⟨fun beside' => admits_of_beside A positive beside' apart selected solvableD independent,
    fun alone => admits_beside A positive alone apart madeNew solvableD independent⟩

/-- **The result beside a neighbour is the neighbour beside the result.** -/
theorem result_beside (f : Firing O (ext A) P PUnit.unit) (apart : Disjoint D.present C.present)
    (enabled : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)))
    (madeNew : ∀ o ∈ f.selection.made, o ∉ D.present) :
    f.result (frames A) (beside D C) = beside D (f.result (frames A) C) := by
  apply state_ext
  · exact information_beside A f apart (selected_of_enabled enabled)
  · show fire (D.present ∪ C.present) (f.selection.commit (T := Unit)) =
      D.present ∪ fire C.present (f.selection.commit (T := Unit))
    have takenC : ∀ o, o ∈ (f.selection.commit (T := Unit)).taken → o ∉ D.present :=
      fun _ taken inD => Finset.disjoint_left.mp apart inD (enabled.taken_subset taken)
    ext o
    constructor
    · intro inside
      rcases mem_fire.mp inside with ⟨inUnion, notTaken⟩ | made
      · rcases Finset.mem_union.mp inUnion with inD | inC
        · exact Finset.mem_union_left _ inD
        · exact Finset.mem_union_right _ (mem_fire.mpr (Or.inl ⟨inC, notTaken⟩))
      · exact Finset.mem_union_right _ (mem_fire.mpr (Or.inr made))
    · intro inside
      rcases Finset.mem_union.mp inside with inD | inFire
      · exact mem_fire.mpr (Or.inl ⟨Finset.mem_union_left _ inD, fun taken => takenC o taken inD⟩)
      · rcases mem_fire.mp inFire with ⟨inC, notTaken⟩ | made
        · exact mem_fire.mpr (Or.inl ⟨Finset.mem_union_right _ inC, notTaken⟩)
        · exact mem_fire.mpr (Or.inr made)
  · funext o
    show relabel (f.row (frames A) (beside D C)) f.selection.made (f.opened (frames A)).produce o =
      if o ∈ D.present then D.label o
      else relabel (f.row (frames A) C) f.selection.made (f.opened (frames A)).produce o
    by_cases inD : o ∈ D.present
    · have notMade : o ∉ f.selection.made := fun made => madeNew o made inD
      rw [if_pos inD, Firing.relabel_of_not_mem _ _ _ notMade]
      show A.apply A.identity (if o ∈ D.present then D.label o else C.label o) = D.label o
      rw [if_pos inD, A.apply_identity]
    · rw [if_neg inD]
      apply relabel_congr
      show A.apply A.identity (if o ∈ D.present then D.label o else C.label o) =
        A.apply A.identity (C.label o)
      rw [if_neg inD]

end Beside

/-! ## Private steps, runs and success -/

section Runs

variable (P : Program (Terms T))

/-- **A private step of a system beside a neighbour**: a positive admitted firing of the program at
the system, whose footprint shares no unknown with the neighbour and whose made identities are new
to it. -/
def PrivateStep (D C C' : State (Terms T) O) : Prop :=
  ∃ f : Firing O (ext A) P PUnit.unit, (step (frames A) O (ext A) P).Admits (s := C) f ∧
    Positive f.rule ∧ Independent A D.Mentions (Footprint A C f) ∧
      (∀ o ∈ f.selection.made, o ∉ D.present) ∧ f.result (frames A) C = C'

/-- **Success**: a present row whose label satisfies the barb. -/
def Succeeds (barb : T → Prop) (s : State (Terms T) O) : Prop := ∃ o ∈ s.present, barb (s.label o)

variable {A P}

theorem disjoint_of_privateStep {D C C' : State (Terms T) O} (step' : PrivateStep A P D C C')
    (apart : Disjoint D.present C.present) : Disjoint D.present C'.present := by
  obtain ⟨f, admitted, -, -, madeNew, rfl⟩ := step'
  rw [Finset.disjoint_right]
  intro o present inD
  rcases mem_fire.mp present with ⟨inC, -⟩ | made
  · exact Finset.disjoint_left.mp apart inD inC
  · exact madeNew o (List.mem_toFinset.mp made) inD

/-- **Privacy is a property of reachable states**: a private step keeps the system private from the
neighbour. -/
theorem privateFrom_of_step {D C C' : State (Terms T) O} (step' : PrivateStep A P D C C') :
    PrivateFrom A D C' := by
  obtain ⟨f, admitted, -, independent, -, rfl⟩ := step'
  obtain ⟨shapes, enabled, -⟩ := admitted
  exact independent.mono (fun _ inD => inD) fun _ mentioned => footprint_of_result A shapes enabled mentioned

theorem privateFrom_along {D C C' : State (Terms T) O} (privateStart : PrivateFrom A D C)
    (run : Relation.ReflTransGen (PrivateStep A P D) C C') : PrivateFrom A D C' := by
  induction run with
  | refl => exact privateStart
  | tail _ last _ => exact privateFrom_of_step last

/-- **A private step beside the neighbour is a step of the program.** -/
theorem succ_beside {D C C' : State (Terms T) O} (step' : PrivateStep A P D C C')
    (apart : Disjoint D.present C.present) (solvableD : A.Consistent D.knowledge) :
    Succ (step (frames A) O (ext A) P).toStep (beside D C) (beside D C') := by
  obtain ⟨f, admitted, positive, independent, madeNew, rfl⟩ := step'
  have enabled : Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) := admitted.2.1
  exact ⟨f, admits_beside A positive admitted apart madeNew solvableD independent,
    result_beside A f apart enabled madeNew⟩

/-- **Runs of private steps lift beside the neighbour.** -/
theorem runs_beside {D C C' : State (Terms T) O} (run : Relation.ReflTransGen (PrivateStep A P D) C C')
    (apart : Disjoint D.present C.present) (solvableD : A.Consistent D.knowledge) :
    Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (beside D C) (beside D C') ∧
      Disjoint D.present C'.present := by
  induction run with
  | refl => exact ⟨Relation.ReflTransGen.refl, apart⟩
  | tail _ last ih =>
      obtain ⟨lifted, apart'⟩ := ih
      exact ⟨lifted.tail (succ_beside last apart' solvableD), disjoint_of_privateStep last apart'⟩

theorem succeeds_beside {barb : T → Prop} {D C : State (Terms T) O}
    (apart : Disjoint D.present C.present) (succeeds : Succeeds barb C) :
    Succeeds barb (beside D C) := by
  obtain ⟨o, inC, holds⟩ := succeeds
  exact ⟨o, Finset.mem_union_right _ inC, by rw [beside_label_right apart inC]; exact holds⟩

/-- **Reachable success persists beside a private neighbour**: if a private run of the system
reaches success, the program's step reaches success from the neighbour beside the system. -/
theorem success_persists {barb : T → Prop} {D C C' : State (Terms T) O}
    (run : Relation.ReflTransGen (PrivateStep A P D) C C') (succeeds : Succeeds barb C')
    (apart : Disjoint D.present C.present) (solvableD : A.Consistent D.knowledge) :
    ∃ t, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (beside D C) t ∧
      Succeeds barb t := by
  obtain ⟨lifted, apart'⟩ := runs_beside run apart solvableD
  exact ⟨_, lifted, succeeds_beside apart' succeeds⟩

end Runs

#print axioms mentions_beside
#print axioms information_beside
#print axioms footprint_of_information
#print axioms footprint_of_result
#print axioms holds_of_positive
#print axioms fresh_beside
#print axioms fresh_of_beside
#print axioms joint_of_independent
#print axioms admits_beside_iff
#print axioms admits_beside
#print axioms admits_of_beside
#print axioms admits_beside_iff_alone
#print axioms result_beside
#print axioms privateFrom_of_step
#print axioms privateFrom_along
#print axioms succ_beside
#print axioms runs_beside
#print axioms success_persists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
