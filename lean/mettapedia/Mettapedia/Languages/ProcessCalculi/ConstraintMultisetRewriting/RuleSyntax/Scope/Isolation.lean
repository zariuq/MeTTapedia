import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Hiding

/-!
# Isolation of two spaces whose unknowns are private to each

Two systems side by side are two spaces of one store: the identities present at each. The step has
no notion of a space's own knowledge; the knowledge is one list, and a firing of the left space
appends its equations after the right space's knowledge. This module proves that this order does
not matter and that, with unknowns private to each space, a firing at one space does not change
what is admitted at the other.

## Structural congruence

`Congruent s t`: the same equations in the knowledge (in any order, with any repetition), the same
present rows, the same labels at the present rows.

* `admits_iff_of_congruent`, `result_congruent`: congruent states admit the same firings and reach
  congruent results; **`succ_congruent`**: so congruence is a bisimulation of the step of every
  program (with `Congruent.symm`).
* `beside_comm`: two systems side by side, in either order, are congruent.

## Isolation

**`isolation`**: let `f` be a positive firing of the left space `D` and `g` a positive firing of the
right space `C` (its takes and reads are rows of `C`). If `C` is independent of `f`'s footprint and
the two footprints are independent of each other (their unknowns are private to each), then `f` is
admitted beside `C`, and `g` is admitted beside `D` exactly when it is admitted after `f` has fired.

The control just outside (`IsolationControls.shared_unknown_crosses_spaces`) is the tree's
`Spaces.Controls.shared_variable_crosses_spaces` on the rule syntax: two rows at the two spaces
labelled by one unknown `x`; a read-and-tell at one binds `x` and refuses the read-and-tell at the
other. With the other row labelled by its own unknown, the theorem applies
(`IsolationControls.private_unknowns_isolated`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {A : SubstitutionAction T S} {O : Type uO} [DecidableEq O]

/-- **Structural congruence at the one frame**: the same equations in the knowledge, the same present
rows, the same labels at the present rows. -/
structure Congruent (s t : State (Terms T) O) : Prop where
  knowledge : ∀ e, e ∈ s.knowledge ↔ e ∈ t.knowledge
  present : s.present = t.present
  label : ∀ o ∈ s.present, s.label o = t.label o

omit [DecidableEq O] in
theorem Congruent.symm {s t : State (Terms T) O} (same : Congruent s t) : Congruent t s :=
  ⟨fun e => (same.knowledge e).symm, same.present.symm,
    fun o present => (same.label o (same.present ▸ present)).symm⟩

omit [DecidableEq O] in
theorem Congruent.trans {s t u : State (Terms T) O} (first : Congruent s t) (second : Congruent t u) :
    Congruent s u :=
  ⟨fun e => (first.knowledge e).trans (second.knowledge e), first.present.trans second.present,
    fun o present => (first.label o present).trans (second.label o (first.present ▸ present))⟩

omit [DecidableEq O] in
theorem models_of_mem_iff {K K' : EquationStore T} (same : ∀ e, e ∈ K ↔ e ∈ K') (σ : S) :
    A.Models σ K ↔ A.Models σ K' :=
  ⟨fun solved e member => solved e ((same e).mpr member),
    fun solved e member => solved e ((same e).mp member)⟩

omit [DecidableEq O] in
theorem mentions_congruent {s t : State (Terms T) O} (same : Congruent s t) (u : T) :
    s.Mentions u ↔ t.Mentions u := by
  have sides : ∀ (g : Equation T → T), u ∈ s.knowledge.map g ↔ u ∈ t.knowledge.map g := by
    intro g
    simp only [List.mem_map]
    exact ⟨fun ⟨e, member, labelled⟩ => ⟨e, (same.knowledge e).mp member, labelled⟩,
      fun ⟨e, member, labelled⟩ => ⟨e, (same.knowledge e).mpr member, labelled⟩⟩
  have rows : (∃ o ∈ s.present, s.label o = u) ↔ ∃ o ∈ t.present, t.label o = u :=
    ⟨fun ⟨o, present, labelled⟩ => ⟨o, same.present ▸ present, (same.label o present).symm.trans labelled⟩,
      fun ⟨o, present, labelled⟩ => ⟨o, same.present ▸ present,
        (same.label o (same.present ▸ present)).trans labelled⟩⟩
  unfold State.Mentions
  rw [sides, sides, rows]

section Firings

variable {P : Program (Terms T)}

omit [DecidableEq O] in
theorem fresh_congruent {s t : State (Terms T) O} (same : Congruent s t)
    (f : Firing O (ext A) P PUnit.unit) : f.Fresh (frames A) s ↔ f.Fresh (frames A) t := by
  constructor
  · intro fresh b g h
    obtain ⟨u, onS, onRule⟩ := fresh b g h
    exact ⟨u, fun v mentioned => onS v ((mentions_congruent same v).mpr mentioned), onRule⟩
  · intro fresh b g h
    obtain ⟨u, onT, onRule⟩ := fresh b g h
    exact ⟨u, fun v mentioned => onT v ((mentions_congruent same v).mp mentioned), onRule⟩

omit [DecidableEq O] in
theorem row_congruent {s t : State (Terms T) O} (same : Congruent s t) (f : Firing O (ext A) P PUnit.unit)
    {o : O} (present : o ∈ s.present) : f.row (frames A) s o = f.row (frames A) t o := by
  unfold Firing.row
  rw [same.label o present]

theorem information_congruent {s t : State (Terms T) O} (same : Congruent s t)
    {f : Firing O (ext A) P PUnit.unit}
    (enabled : Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit))) (e : Equation T) :
    e ∈ f.information (frames A) s ↔ e ∈ f.information (frames A) t := by
  have own : ownInformation f s = ownInformation f t := by
    unfold ownInformation Firing.matching
    rw [zipWith_congr_right _ _ _ f.selection.taken fun o member _ => by
        rw [row_congruent same f (selected_of_enabled enabled o (Or.inl member))],
      zipWith_congr_right _ _ _ f.selection.read fun o member _ => by
        rw [row_congruent same f (selected_of_enabled enabled o (Or.inr member))]]
  rw [information_eq_append, information_eq_append, own, List.mem_append, List.mem_append,
    same.knowledge e]

omit [DecidableEq O] in
theorem holds_congruent {s t : State (Terms T) O} (same : Congruent s t)
    (f : Firing O (ext A) P PUnit.unit) (σ : S) :
    f.Holds (frames A) s (b := PUnit.unit) σ ↔ f.Holds (frames A) t (b := PUnit.unit) σ := by
  have matches' : ∀ p, matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ (f.row (frames A) s)
      s.present p = matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ (f.row (frames A) t)
      t.present p := by
    intro p
    ext o
    rw [mem_matchesAt, mem_matchesAt]
    constructor
    · rintro ⟨present, equated⟩
      exact ⟨same.present ▸ present, by rw [← row_congruent same f present]; exact equated⟩
    · rintro ⟨present, equated⟩
      have present' : o ∈ s.present := same.present ▸ present
      exact ⟨present', by rw [row_congruent same f present']; exact equated⟩
  unfold Firing.Holds
  apply and_congr
  · refine forall₂_congr fun c _ => ?_
    cases c with
    | equal l r => exact Iff.rfl
    | predicate quantifier p =>
        cases quantifier with
        | any =>
            show (∃ o ∈ s.present, A.E (A.apply σ p) (A.apply σ (f.row (frames A) s o))) ↔
              ∃ o ∈ t.present, A.E (A.apply σ p) (A.apply σ (f.row (frames A) t o))
            constructor
            · rintro ⟨o, present, equated⟩
              refine ⟨o, same.present ▸ present, ?_⟩
              rw [← row_congruent same f present]
              exact equated
            · rintro ⟨o, present, equated⟩
              have present' : o ∈ s.present := same.present ▸ present
              refine ⟨o, present', ?_⟩
              rw [row_congruent same f present']
              exact equated
        | none =>
            show (∀ o ∈ s.present, ¬ A.E (A.apply σ p) (A.apply σ (f.row (frames A) s o))) ↔
              ∀ o ∈ t.present, ¬ A.E (A.apply σ p) (A.apply σ (f.row (frames A) t o))
            constructor
            · intro none o present
              have present' : o ∈ s.present := same.present ▸ present
              rw [← row_congruent same f present']
              exact none o present'
            · intro none o present
              rw [row_congruent same f present]
              exact none o (same.present ▸ present)
    | count p n =>
        show (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ _ _ p).card = n ↔
          (matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ _ _ p).card = n
        rw [matches' p]
  · refine forall₂_congr fun q _ => ?_
    show matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ _ _ q.1 = q.2 ↔
      matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit) σ _ _ q.1 = q.2
    rw [matches' q.1]

theorem admits_of_congruent {s t : State (Terms T) O} (same : Congruent s t)
    {f : Firing O (ext A) P PUnit.unit} (admitted : (step (frames A) O (ext A) P).Admits (s := s) f) :
    (step (frames A) O (ext A) P).Admits (s := t) f := by
  obtain ⟨⟨fresh, rest⟩, enabled, ⟨_, σ, solved⟩, asked⟩ := admitted
  have info := information_congruent same enabled
  refine ⟨⟨(fresh_congruent same f).mp fresh, rest⟩, same.present ▸ enabled,
    ⟨PUnit.unit, σ, (models_of_mem_iff info σ).mp solved⟩, fun b ρ onT => ?_⟩
  exact (holds_congruent same f ρ).mp (asked PUnit.unit ρ ((models_of_mem_iff info ρ).mpr onT))

theorem admits_iff_of_congruent {s t : State (Terms T) O} (same : Congruent s t)
    (f : Firing O (ext A) P PUnit.unit) :
    (step (frames A) O (ext A) P).Admits (s := s) f ↔ (step (frames A) O (ext A) P).Admits (s := t) f :=
  ⟨admits_of_congruent same, admits_of_congruent same.symm⟩

theorem relabel_congr_made {Obj : Type*} {Tm : Obj → Type*} {a : Obj} {old old' : O → Tm a} {o : O} :
    ∀ (made : List O) (rows : List (Tm a)), made.length ≤ rows.length →
      (o ∉ made → old o = old' o) → relabel old made rows o = relabel old' made rows o
  | [], _, _, same => same (List.not_mem_nil)
  | _ :: _, [], lengths, _ => by simp at lengths
  | o' :: rest, t :: ts, lengths, same => by
      simp only [relabel]
      split_ifs with here
      · rfl
      · exact relabel_congr_made rest ts (Nat.le_of_succ_le_succ lengths) fun notRest =>
          same fun inside => (List.mem_cons.mp inside).elim here notRest

/-- **Congruent states reach congruent results.** -/
theorem result_congruent {s t : State (Terms T) O} (same : Congruent s t)
    {f : Firing O (ext A) P PUnit.unit} (admitted : (step (frames A) O (ext A) P).Admits (s := s) f) :
    Congruent (f.result (frames A) s) (f.result (frames A) t) := by
  obtain ⟨shapes, enabled, -, -⟩ := admitted
  refine ⟨information_congruent same enabled, ?_, fun o present => ?_⟩
  · show fire s.present _ = fire t.present _
    rw [same.present]
  · show relabel (f.row (frames A) s) f.selection.made (f.opened (frames A)).produce o =
      relabel (f.row (frames A) t) f.selection.made (f.opened (frames A)).produce o
    have lengths : f.selection.made.length ≤ (f.opened (frames A)).produce.length := by
      simp only [Firing.opened, RuleInstance.map, List.length_map]
      exact shapes.2.2.2.2.2.1.symm.le
    apply relabel_congr_made _ _ lengths
    intro notMade
    have inS : o ∈ s.present := by
      rcases mem_fire.mp present with ⟨inS, -⟩ | made
      · exact inS
      · exact absurd (List.mem_toFinset.mp made) notMade
    exact row_congruent same f inS

/-- **Congruence is a bisimulation of the step of every program.** -/
theorem succ_congruent {s t s' : State (Terms T) O} (same : Congruent s t)
    (reached : Succ (step (frames A) O (ext A) P).toStep s s') :
    ∃ t', Succ (step (frames A) O (ext A) P).toStep t t' ∧ Congruent s' t' := by
  obtain ⟨f, admitted, rfl⟩ := reached
  exact ⟨_, ⟨f, admits_of_congruent same admitted, rfl⟩, result_congruent same admitted⟩

end Firings

/-- **Two systems side by side, in either order, are congruent.** -/
theorem beside_comm {D C : State (Terms T) O} (apart : Disjoint D.present C.present) :
    Congruent (beside D C) (beside C D) := by
  refine ⟨fun e => ?_, Finset.union_comm _ _, fun o present => ?_⟩
  · show e ∈ D.knowledge ++ C.knowledge ↔ e ∈ C.knowledge ++ D.knowledge
    rw [List.mem_append, List.mem_append, or_comm]
  · rcases Finset.mem_union.mp present with inD | inC
    · rw [beside_label_left inD, beside_label_right apart.symm inD]
    · rw [beside_label_right apart inC, beside_label_left inC]

/-! ## Isolation -/

section Isolation

variable {P : Program (Terms T)}

/-- **Isolation of two spaces.** A positive firing `f` of the left space and a positive firing `g` of
the right space, with the right space independent of `f`'s footprint and the two footprints
independent of each other: `f` is admitted beside the right space, and `g` is admitted beside the
left space exactly when it is admitted after `f` has fired. -/
theorem isolation {D C : State (Terms T) O} (apart : Disjoint D.present C.present)
    (solvableD : A.Consistent D.knowledge) (solvableC : A.Consistent C.knowledge)
    {f g : Firing O (ext A) P PUnit.unit} (positiveF : Positive f.rule) (positiveG : Positive g.rule)
    (admittedF : (step (frames A) O (ext A) P).Admits (s := D) f)
    (madeF : ∀ o ∈ f.selection.made, o ∉ C.present)
    (selectedG : ∀ o, o ∈ g.selection.taken ∨ o ∈ g.selection.read → o ∈ C.present)
    (madeG : ∀ o ∈ g.selection.made, o ∉ D.present ∧ o ∉ f.selection.made)
    (independentF : Independent A C.Mentions (Footprint A D f))
    (independentG : Independent A (Footprint A D f) (Footprint A C g)) :
    (step (frames A) O (ext A) P).Admits (s := beside D C) f ∧
      ((step (frames A) O (ext A) P).Admits (s := beside D C) g ↔
        (step (frames A) O (ext A) P).Admits (s := f.result (frames A) (beside D C)) g) := by
  have atCD : (step (frames A) O (ext A) P).Admits (s := beside C D) f :=
    admits_beside A positiveF admittedF apart.symm madeF solvableC independentF
  have atDC : (step (frames A) O (ext A) P).Admits (s := beside D C) f :=
    admits_of_congruent (beside_comm apart.symm) atCD
  refine ⟨atDC, ?_⟩
  obtain ⟨shapesF, enabledF, ⟨_, σ, solvedF⟩, -⟩ := admittedF
  -- after `f`, the left space is its result at `D`, beside the same right space
  set D' := f.result (frames A) D with hD'
  have apart' : Disjoint D'.present C.present := by
    rw [Finset.disjoint_left]
    intro o present inC
    rcases mem_fire.mp present with ⟨inD, -⟩ | made
    · exact Finset.disjoint_left.mp apart inD inC
    · exact madeF o (List.mem_toFinset.mp made) inC
  have after : Congruent (f.result (frames A) (beside D C)) (beside D' C) := by
    have toCD := result_congruent (beside_comm apart) atDC
    rw [result_beside A f apart.symm enabledF madeF] at toCD
    exact toCD.trans (beside_comm apart'.symm)
  have solvableD' : A.Consistent D'.knowledge := ⟨σ, solvedF⟩
  have independentD : Independent A D.Mentions (Footprint A C g) :=
    independentG.mono (fun t mentioned => Or.inl mentioned) (fun _ foot => foot)
  have independentD' : Independent A D'.Mentions (Footprint A C g) :=
    independentG.mono (fun t mentioned => footprint_of_result A shapesF enabledF mentioned)
      (fun _ foot => foot)
  have madeD : ∀ o ∈ g.selection.made, o ∉ D.present := fun o made => (madeG o made).1
  have madeD' : ∀ o ∈ g.selection.made, o ∉ D'.present := by
    intro o made present
    rcases mem_fire.mp present with ⟨inD, -⟩ | madeByF
    · exact (madeG o made).1 inD
    · exact (madeG o made).2 (List.mem_toFinset.mp madeByF)
  rw [admits_beside_iff_alone A positiveG apart selectedG madeD solvableD independentD,
    admits_iff_of_congruent after g,
    admits_beside_iff_alone A positiveG apart' selectedG madeD' solvableD' independentD']

end Isolation

#print axioms succ_congruent
#print axioms admits_iff_of_congruent
#print axioms result_congruent
#print axioms beside_comm
#print axioms isolation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
