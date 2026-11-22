import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition

/-!
# A state and some of its rows: what a firing asks of the rows it does not select

`restrict w H` is the state `w` with only the rows `H` present: the same frame, the same knowledge, the
same labels. A firing at `w` is a firing at `restrict w H`, with the same information
(`information_restrict`) and, row for row, the same result (`result_restrict`).

A rule is **absence-only** (`AbsenceOnly`) when its checks are equations and absences and it has no
collect pattern; a positive rule (`RuleSyntax.Scope.Positive`) is one (`absenceOnly_of_positive`). For
a firing of such a rule that selects rows of `H`:

* `admits_restrict`: **admitted with more rows, admitted with fewer**. Rows it does not select can
  only refuse it: by an absence check, or by being mentioned by the state where its opening must be
  fresh.
* `admits_extend`: **admitted with fewer rows, admitted with more**, when its opening is fresh at the
  larger state, the identities it makes are new there, and no row outside `H` matches one of its
  absence patterns at a solution of its information.
* `admits_iff_restrict`: the two together: admission at the larger state is exactly admission at the
  smaller one with those three clauses.

For a positive rule the last clause is empty: only freshness and new identities are asked
(`admits_extend_positive`). A rule with a count check or a collect pattern is outside these statements:
its guard reads how many present rows match.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open RuleSyntax (Rule Program State Firing Extensions checkHolds)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A rule whose guard only asks rows to be absent**: its checks are equations and absences, and it
has no collect pattern. -/
def AbsenceOnly (r : Rule Tm) : Prop :=
  (∀ c ∈ r.body.checks, (∃ l l', c = Check.equal l l') ∨ ∃ p, c = Check.predicate .none p) ∧ r.collect = []

/-- A positive rule is absence-only: it has no absence check at all. -/
theorem absenceOnly_of_positive {r : Rule Tm} (positive : RuleSyntax.Scope.Positive r) : AbsenceOnly r :=
  ⟨fun c member => .inl (positive.1 c member), positive.2⟩

variable {O : Type uOcc}

/-- **The state with only the rows `H` present**: the same frame, knowledge and labels. -/
@[reducible] def restrict (w : State Tm O) (H : Finset O) : State Tm O :=
  ⟨w.frame, w.knowledge, H, w.label⟩

variable (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **The information of a firing does not depend on the rows present.** -/
theorem information_restrict (w : State Tm O) (H : Finset O) (f : Firing O E P w.frame) :
    Firing.information X (restrict w H) f = Firing.information X w f :=
  rfl

/-- **Freshness is antitone in the rows present**: an opening fresh at a state is fresh at the state
with fewer rows, which mentions less. -/
theorem fresh_restrict {w : State Tm O} {H : Finset O} (sub : H ⊆ w.present) {f : Firing O E P w.frame}
    (fresh : Firing.Fresh X w f) : Firing.Fresh X (restrict w H) f := by
  intro b g h
  obtain ⟨u, onState, onRule⟩ := fresh b g h
  refine ⟨u, fun t mentioned => onState t ?_, onRule⟩
  rcases mentioned with first | second | ⟨o, present, labelled⟩
  · exact .inl first
  · exact .inr (.inl second)
  · exact .inr (.inr ⟨o, sub present, labelled⟩)

variable [DecidableEq O]

/-- **The result of a firing, row for row**: with fewer rows present the firing makes the same frame,
knowledge and labels, and fires the rows that were present. -/
theorem result_restrict (w : State Tm O) (H : Finset O) (f : Firing O E P w.frame) :
    Firing.result X (restrict w H) f =
      restrict (Firing.result X w f) (fire H (f.selection.commit (T := Unit))) :=
  rfl

/-- The result at the larger state, restricted to the rows the firing leaves at the smaller one. -/
theorem restrict_result {w : State Tm O} {H H' : Finset O} {f : Firing O E P w.frame}
    (same : (Firing.result X (restrict w H) f).present = H') :
    restrict (Firing.result X w f) H' = Firing.result X (restrict w H) f := by
  subst same
  rfl

/-- **Admitted with more rows, admitted with fewer**, for a firing of an absence-only rule that
selects rows of `H`. -/
theorem admits_restrict {w : State Tm O} {H : Finset O} (sub : H ⊆ w.present) {f : Firing O E P w.frame}
    (absenceOnly : AbsenceOnly f.rule)
    (selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ H)
    (admitted : Firing.Admits X w f) : Firing.Admits X (restrict w H) f := by
  obtain ⟨⟨fresh, shapes⟩, enabled, solvable, holds⟩ := admitted
  refine ⟨⟨fresh_restrict X sub fresh, shapes⟩, ?_, solvable, ?_⟩
  · exact ⟨fun o member => selected o (.inl (List.mem_toFinset.mp member)),
      fun o member => selected o (.inr (List.mem_toFinset.mp member)), enabled.apart,
      Finset.disjoint_of_subset_right sub enabled.fresh, fun q member => by simp [Selection.commit] at member⟩
  · intro b σ solved
    obtain ⟨checks, _⟩ := holds b σ solved
    refine ⟨fun c member => ?_, fun q member => ?_⟩
    · have atW := checks c member
      obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp member
      rcases absenceOnly.1 c₀ inRule with ⟨l, l', rfl⟩ | ⟨p, rfl⟩
      · exact atW
      · exact fun o present => atW o (sub present)
    · simp [Firing.collectOpened, absenceOnly.2] at member

/-- **Admitted with fewer rows, admitted with more**, for a firing of an absence-only rule: when its
opening is fresh at the larger state, the identities it makes are new there, and no row outside `H`
matches one of its absence patterns at a solution of its information. -/
theorem admits_extend {w : State Tm O} {H : Finset O} (sub : H ⊆ w.present) {f : Firing O E P w.frame}
    (absenceOnly : AbsenceOnly f.rule) (fresh : Firing.Fresh X w f)
    (madeNew : ∀ o ∈ f.selection.made, o ∉ w.present)
    (others : ∀ p, Check.predicate .none p ∈ f.rule.body.checks → ∀ (b : Obj) (σ : Hom (E.target f.ext) b),
      X.Models σ (Firing.information X w f) → ∀ o ∈ w.present, o ∉ H →
        ¬ X.E (X.act σ (X.act f.opening p)) (X.act σ (Firing.row X w f o)))
    (admitted : Firing.Admits X (restrict w H) f) : Firing.Admits X w f := by
  obtain ⟨⟨_, shapes⟩, enabled, solvable, holds⟩ := admitted
  refine ⟨⟨fresh, shapes⟩, ?_, solvable, ?_⟩
  · exact ⟨fun o member => sub (enabled.taken_subset member), fun o member => sub (enabled.kept_subset member),
      enabled.apart,
      Finset.disjoint_left.mpr fun {o} made present => madeNew o (List.mem_toFinset.mp made) present,
      fun q member => by simp [Selection.commit] at member⟩
  · intro b σ solved
    obtain ⟨checks, _⟩ := holds b σ solved
    refine ⟨fun c member => ?_, fun q member => ?_⟩
    · have atH := checks c member
      obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp member
      rcases absenceOnly.1 c₀ inRule with ⟨l, l', rfl⟩ | ⟨p, rfl⟩
      · exact atH
      · intro o present
        by_cases inH : o ∈ H
        · exact atH o inH
        · exact others p inRule b σ solved o present inH
    · simp [Firing.collectOpened, absenceOnly.2] at member

/-- **Admission with more rows, exactly**: for a firing of an absence-only rule that selects rows of
`H`, admission at the larger state is admission at the smaller one, a fresh opening at the larger
state, identities new there, and no row outside `H` matching an absence pattern at a solution of the
information. -/
theorem admits_iff_restrict {w : State Tm O} {H : Finset O} (sub : H ⊆ w.present) {f : Firing O E P w.frame}
    (absenceOnly : AbsenceOnly f.rule)
    (selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ H) :
    Firing.Admits X w f ↔ Firing.Admits X (restrict w H) f ∧ Firing.Fresh X w f ∧
      (∀ o ∈ f.selection.made, o ∉ w.present) ∧
      ∀ p, Check.predicate .none p ∈ f.rule.body.checks → ∀ (b : Obj) (σ : Hom (E.target f.ext) b),
        X.Models σ (Firing.information X w f) → ∀ o ∈ w.present, o ∉ H →
          ¬ X.E (X.act σ (X.act f.opening p)) (X.act σ (Firing.row X w f o)) := by
  constructor
  · intro admitted
    refine ⟨admits_restrict X sub absenceOnly selected admitted, admitted.1.1, ?_, ?_⟩
    · intro o made present
      exact Finset.disjoint_left.mp admitted.2.1.fresh (List.mem_toFinset.mpr made) present
    · intro p inRule b σ solved o present _
      exact (admitted.2.2.2 b σ solved).1 _ (List.mem_map.mpr ⟨_, inRule, rfl⟩) o present
  · rintro ⟨admitted, fresh, madeNew, others⟩
    exact admits_extend X sub absenceOnly fresh madeNew others admitted

/-- **A positive firing asks nothing of the rows it does not select**: admitted with fewer rows, it is
admitted with more when its opening is fresh there and the identities it makes are new there. -/
theorem admits_extend_positive {w : State Tm O} {H : Finset O} (sub : H ⊆ w.present)
    {f : Firing O E P w.frame} (positive : RuleSyntax.Scope.Positive f.rule) (fresh : Firing.Fresh X w f)
    (madeNew : ∀ o ∈ f.selection.made, o ∉ w.present) (admitted : Firing.Admits X (restrict w H) f) :
    Firing.Admits X w f := by
  refine admits_extend X sub (absenceOnly_of_positive positive) fresh madeNew ?_ admitted
  intro p inRule
  obtain ⟨l, l', same⟩ := positive.1 _ inRule
  cases same

#print axioms information_restrict
#print axioms fresh_restrict
#print axioms result_restrict
#print axioms admits_restrict
#print axioms admits_extend
#print axioms admits_iff_restrict
#print axioms admits_extend_positive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
