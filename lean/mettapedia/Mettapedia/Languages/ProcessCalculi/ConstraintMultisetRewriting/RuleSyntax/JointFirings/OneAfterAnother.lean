import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Members

/-!
# A bag whose members are admitted on their own is a run of its members

At the one-frame action of a substitution action, with the identity extension, a firing of a program can
be fired at any state, so "one after another" has a meaning: fire the first member, then the bag of the
rest at the result.

Under the reading of joint admission that asks the guards of each member at its **own** information
(`Bag.AdmitsOwn`):

* **`peel`**: if the bag `m :: rest` is admitted at `s` and the rules of `rest` are positive, then `m` is
  admitted at `s` by the step of the program, the bag `rest` is admitted at the result of `m`, and the
  result of `rest` there is the result of the whole bag at `s`, as a state. The first member may have
  any rule.
* **`run_of_admitsOwn`**: so an admitted bag of positive rules is a run of the step of the program
  through its members in their order, ending at the result of the bag.
* **`result_nil`**, **`admits_nil_iff_consistent`**: the bag without members is jointly admissible exactly
  when the knowledge is solvable, and its result is the state itself. It would be a step that changes
  nothing at every such state, which is why `bagStep` asks for a member.

So under that reading a bag adds to the step of the program only that nothing comes between its members.

The other reading (`Bag.Admits`: guards at the joint information) is the same reading on states that
mention only fixed terms:

* **`admitsOwn_of_fixed`**: at a state all of whose mentioned terms are fixed by every substitution, a bag
  of positive rules that is admitted with its guards at the joint information is admitted with the
  guards of each member at its own. The solution of one member's information and a joint solution are
  realized together by joint freshness (`Realized.pick`).
* **`run_of_admits_of_fixed`**: so there every admitted bag of positive rules is a run of its members.

Outside that fragment the two readings part: `Knowledge` exhibits rows sharing an unknown and a bag that
is admitted at the joint information while no firing of the program is admitted.

The statement `peel` is the counterpart, for the step of a program with fresh openings and relabelled
made identities, of `AnnotatedRuns.Round.cons` for the first-order step with labels fixed once and for
all.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)
open Scope (Positive Footprint)

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- **A member at the one frame.** -/
abbrev OneMember (O : Type uO) (P : Program (Terms T)) :=
  Member O (ext A) P (a := PUnit.unit) PUnit.unit

/-- **The bag of a list of members at the one frame.** -/
abbrev bagOf {O : Type uO} {P : Program (Terms T)} (l : List (OneMember A O P)) :
    Bag O (ext A) P PUnit.unit := ⟨PUnit.unit, l⟩

variable {O : Type uO} {P : Program (Terms T)}

/-! ## Rows and own equations after a firing -/

/-- A row read at the one frame is its label. -/
theorem row_one (s : State (Terms T) O) (g : Firing O (ext A) P PUnit.unit) (o : O) :
    g.row (frames A) s o = s.label o := A.apply_identity (s.label o)

variable [DecidableEq O]

/-- A row that a firing does not make reads after it as before. -/
theorem row_after (s : State (Terms T) O) (g r : Firing O (ext A) P PUnit.unit) {o : O}
    (absent : o ∉ g.selection.made) :
    r.row (frames A) (g.result (frames A) s) o = r.row (frames A) s o := by
  rw [row_one A, row_one A, Firing.result_label_other (s := s) g absent, row_one A]

/-- **The own equations of a member after a firing that makes none of its rows are its own equations
before.** -/
theorem own_after (s : State (Terms T) O) (g : Firing O (ext A) P PUnit.unit) (r : OneMember A O P)
    (apartTaken : ∀ o ∈ r.selection.taken, o ∉ g.selection.made)
    (apartRead : ∀ o ∈ r.selection.read, o ∉ g.selection.made) :
    Member.own (frames A) (g.result (frames A) s) r = Member.own (frames A) s r := by
  have taken : r.firing.matching (frames A) (g.result (frames A) s) (r.firing.opened (frames A)).take
      r.firing.selection.taken =
      r.firing.matching (frames A) s (r.firing.opened (frames A)).take r.firing.selection.taken := by
    unfold Firing.matching
    exact Scope.zipWith_congr_right _ _ _ _ fun o member _ => by
      rw [row_after A s g r.firing (apartTaken o member)]
  have read : r.firing.matching (frames A) (g.result (frames A) s) (r.firing.opened (frames A)).read
      r.firing.selection.read =
      r.firing.matching (frames A) s (r.firing.opened (frames A)).read r.firing.selection.read := by
    unfold Firing.matching
    exact Scope.zipWith_congr_right _ _ _ _ fun o member _ => by
      rw [row_after A s g r.firing (apartRead o member)]
  unfold Member.own
  rw [taken, read]

/-- **The information of a member after a firing that makes none of its rows** is the information of
that firing and the member's own equations. -/
theorem information_after_member (s : State (Terms T) O) (g : Firing O (ext A) P PUnit.unit)
    (r : OneMember A O P) (apartTaken : ∀ o ∈ r.selection.taken, o ∉ g.selection.made)
    (apartRead : ∀ o ∈ r.selection.read, o ∉ g.selection.made) :
    r.firing.information (frames A) (g.result (frames A) s) =
      g.information (frames A) s ++ Member.own (frames A) s r :=
  (Member.information_eq (frames A) (g.result (frames A) s) r).trans
    (congrArg₂ (fun known own => known ++ own)
      (Frames.applyStore_id (X := frames A) (a := PUnit.unit) (g.information (frames A) s))
      (own_after A s g r apartTaken apartRead))

/-! ## The bag without members -/

/-- **The result of the bag without members is the state itself.** -/
theorem result_nil (s : State (Terms T) O) :
    Bag.result (frames A) s (bagOf A ([] : List (OneMember A O P))) = s := by
  apply Scope.state_ext
  · show (frames A).applyStore ((frames A).id PUnit.unit) s.knowledge ++ [] = s.knowledge
    rw [List.append_nil, Frames.applyStore_id]
  · show fire s.present ((⟨[], [], []⟩ : Selection O).commit (T := Unit)) = s.present
    ext o
    simp [mem_fire, Selection.commit]
  · funext o
    exact A.apply_identity (s.label o)

/-- **The bag without members is jointly admissible exactly when the knowledge is solvable.** -/
theorem admits_nil_iff_consistent (s : State (Terms T) O) :
    Bag.Admits (frames A) s (bagOf A ([] : List (OneMember A O P))) ↔ A.Consistent s.knowledge := by
  refine (Bag.admits_nil_iff (frames A) (s := s) (E := ext A) (P := P) PUnit.unit).trans ?_
  constructor
  · rintro ⟨-, solvable⟩
    have solvable' : (frames A).Solvable (a := PUnit.unit)
        ((frames A).applyStore ((frames A).id PUnit.unit) s.knowledge) := solvable
    rw [Frames.applyStore_id] at solvable'
    exact (Frames.ofSubstitution_solvable_iff A s.knowledge).mp solvable'
  · intro consistent
    refine ⟨fun b g => ⟨g, fun t _ => ?_⟩, ?_⟩
    · show A.E (A.apply g (A.apply A.identity t)) (A.apply g t)
      rw [A.apply_identity]
      exact A.equivalence.refl _
    · show (frames A).Solvable (a := PUnit.unit)
        ((frames A).applyStore ((frames A).id PUnit.unit) s.knowledge)
      rw [Frames.applyStore_id]
      exact (Frames.ofSubstitution_solvable_iff A s.knowledge).mpr consistent

/-! ## Peeling the first member -/

section Peel

variable {s : State (Terms T) O} {m : OneMember A O P} {rest : List (OneMember A O P)}

/-- The rows the members of the rest select are present, hence not made by the first member. -/
theorem selected_apart
    (enabled : Enabled (fun _ : O => ()) s.present ((bagOf A (m :: rest)).selection.commit (T := Unit)))
    {r : OneMember A O P} (inside : r ∈ rest) :
    (∀ o ∈ r.selection.taken, o ∉ m.selection.made) ∧ ∀ o ∈ r.selection.read, o ∉ m.selection.made := by
  have fresh : ∀ o, o ∈ s.present → o ∉ m.selection.made := fun o present made =>
    Finset.disjoint_left.mp enabled.fresh
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, List.mem_cons_self, made⟩)) present
  constructor
  · intro o taken
    exact fresh o (enabled.taken_subset
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨r, List.mem_cons_of_mem _ inside, taken⟩)))
  · intro o read
    exact fresh o (enabled.kept_subset
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨r, List.mem_cons_of_mem _ inside, read⟩)))

/-- **The joint information of the rest after the first member is the joint information of the whole
bag.** -/
theorem information_after
    (apart : ∀ r ∈ rest, (∀ o ∈ r.selection.taken, o ∉ m.selection.made) ∧
      ∀ o ∈ r.selection.read, o ∉ m.selection.made) :
    Bag.information (frames A) (m.firing.result (frames A) s) (bagOf A rest) =
      Bag.information (frames A) s (bagOf A (m :: rest)) := by
  have owns : rest.flatMap (fun r => Member.own (frames A) (m.firing.result (frames A) s) r) =
      rest.flatMap (fun r => Member.own (frames A) s r) :=
    List.flatMap_congr fun r inside => own_after A s m.firing r (apart r inside).1 (apart r inside).2
  have known : (frames A).applyStore ((frames A).id PUnit.unit) (m.firing.information (frames A) s) =
      (frames A).applyStore ((frames A).id PUnit.unit) s.knowledge ++ Member.own (frames A) s m :=
    (Frames.applyStore_id (X := frames A) (a := PUnit.unit) (m.firing.information (frames A) s)).trans
      (Member.information_eq (frames A) s m)
  show (frames A).applyStore ((frames A).id PUnit.unit) (m.firing.information (frames A) s) ++
      rest.flatMap (fun r => Member.own (frames A) (m.firing.result (frames A) s) r) =
    (frames A).applyStore ((frames A).id PUnit.unit) s.knowledge ++
      (Member.own (frames A) s m ++ rest.flatMap (fun r => Member.own (frames A) s r))
  rw [owns, known]
  exact List.append_assoc _ _ _

/-- **The joint selection of the rest is enabled after the first member.** -/
theorem enabled_after
    (taken : (bagOf A (m :: rest)).selection.taken.Nodup)
    (made : (bagOf A (m :: rest)).selection.made.Nodup)
    (enabled : Enabled (fun _ : O => ()) s.present ((bagOf A (m :: rest)).selection.commit (T := Unit))) :
    Enabled (fun _ : O => ()) (fire s.present (m.selection.commit (T := Unit)))
      ((bagOf A rest).selection.commit (T := Unit)) := by
  have taken' : (m.selection.taken ++ (bagOf A rest).selection.taken).Nodup := taken
  have made' : (m.selection.made ++ (bagOf A rest).selection.made).Nodup := made
  have inTaken : ∀ o, o ∈ (bagOf A rest).selection.taken →
      o ∈ ((bagOf A (m :: rest)).selection.commit (T := Unit)).taken := fun o inside =>
    List.mem_toFinset.mpr (show o ∈ m.selection.taken ++ (bagOf A rest).selection.taken from
      List.mem_append_right _ inside)
  have inRead : ∀ o, o ∈ (bagOf A rest).selection.read →
      o ∈ ((bagOf A (m :: rest)).selection.commit (T := Unit)).kept := fun o inside =>
    List.mem_toFinset.mpr (show o ∈ m.selection.read ++ (bagOf A rest).selection.read from
      List.mem_append_right _ inside)
  have inMade : ∀ o, o ∈ (bagOf A rest).selection.made →
      o ∈ ((bagOf A (m :: rest)).selection.commit (T := Unit)).made := fun o inside =>
    List.mem_toFinset.mpr (show o ∈ m.selection.made ++ (bagOf A rest).selection.made from
      List.mem_append_right _ inside)
  have headTaken : ∀ o, o ∈ m.selection.taken →
      o ∈ ((bagOf A (m :: rest)).selection.commit (T := Unit)).taken := fun o inside =>
    List.mem_toFinset.mpr (show o ∈ m.selection.taken ++ (bagOf A rest).selection.taken from
      List.mem_append_left _ inside)
  refine ⟨fun o member => ?_, fun o member => ?_, ?_, ?_, fun q member => ?_⟩
  · have inside : o ∈ (bagOf A rest).selection.taken := List.mem_toFinset.mp member
    refine mem_fire.mpr (Or.inl ⟨enabled.taken_subset (inTaken o inside), fun gone => ?_⟩)
    exact (List.nodup_append.mp taken').2.2 o (List.mem_toFinset.mp gone) o inside rfl
  · have inside : o ∈ (bagOf A rest).selection.read := List.mem_toFinset.mp member
    refine mem_fire.mpr (Or.inl ⟨enabled.kept_subset (inRead o inside), fun gone => ?_⟩)
    exact Finset.disjoint_left.mp enabled.apart (headTaken o (List.mem_toFinset.mp gone))
      (inRead o inside)
  · exact Finset.disjoint_left.mpr fun o isTaken isKept =>
      Finset.disjoint_left.mp enabled.apart (inTaken o (List.mem_toFinset.mp isTaken))
        (inRead o (List.mem_toFinset.mp isKept))
  · refine Finset.disjoint_left.mpr fun o isMade after => ?_
    have inside : o ∈ (bagOf A rest).selection.made := List.mem_toFinset.mp isMade
    rcases mem_fire.mp after with ⟨present, -⟩ | madeFirst
    · exact Finset.disjoint_left.mp enabled.fresh (inMade o inside) present
    · exact (List.nodup_append.mp made').2.2 o (List.mem_toFinset.mp madeFirst) o inside rfl
  · simp [Selection.commit] at member

/-- **The rest is jointly fresh after the first member.** -/
theorem fresh_after (shapes : m.firing.Shapes (frames A) s)
    (enabledM : Enabled (fun _ : O => ()) s.present (m.selection.commit (T := Unit)))
    (fresh : (bagOf A (m :: rest)).Fresh (frames A) s) :
    (bagOf A rest).Fresh (frames A) (m.firing.result (frames A) s) := by
  intro b g
  have joint := (realized_cons (frames A) m rest _).mp (fresh b g) (A.compose g m.opening)
  refine Realized.mono (frames A) rest (fun u both t mentioned => ?_) joint
  rcases Scope.footprint_of_result A shapes enabledM mentioned with old | opened
  · exact both.1 t old
  · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
    have key : A.E (A.apply u (A.apply m.opening t₀)) (A.apply (A.compose g m.opening) t₀) :=
      both.2 t₀ member
    rw [A.apply_compose] at key
    show A.E (A.apply u (A.apply A.identity (A.apply m.opening t₀))) (A.apply g (A.apply m.opening t₀))
    rw [A.apply_identity]
    exact key

/-- **The result of the rest after the first member is the result of the whole bag.** -/
theorem result_after (fits : (bagOf A (m :: rest)).Fits (frames A) s)
    (enabled : Enabled (fun _ : O => ()) s.present ((bagOf A (m :: rest)).selection.commit (T := Unit))) :
    Bag.result (frames A) (m.firing.result (frames A) s) (bagOf A rest) =
      Bag.result (frames A) s (bagOf A (m :: rest)) := by
  obtain ⟨-, -, made, lengths⟩ := fits
  have made' : (m.selection.made ++ (bagOf A rest).selection.made).Nodup := made
  have apartMade : ∀ o ∈ m.selection.made, o ∉ (bagOf A rest).selection.made := fun o first later =>
    (List.nodup_append.mp made').2.2 o first o later rfl
  have rowsMade : m.selection.made.length = (m.firing.opened (frames A)).produce.length := by
    show m.selection.made.length = (m.rule.body.produce.map (A.apply m.opening)).length
    rw [List.length_map]
    exact (lengths m List.mem_cons_self).2.2.1.symm
  apply Scope.state_ext
  · exact information_after A fun r inside => selected_apart A enabled inside
  · show fire (fire s.present (m.selection.commit (T := Unit)))
        ((bagOf A rest).selection.commit (T := Unit)) =
      fire s.present ((bagOf A (m :: rest)).selection.commit (T := Unit))
    have takenEq : (bagOf A (m :: rest)).selection.taken =
        m.selection.taken ++ (bagOf A rest).selection.taken := rfl
    have madeEq : (bagOf A (m :: rest)).selection.made =
        m.selection.made ++ (bagOf A rest).selection.made := rfl
    ext o
    have side : o ∈ m.selection.made → o ∉ (bagOf A rest).selection.taken := fun first later =>
      Finset.disjoint_left.mp enabled.fresh
        (List.mem_toFinset.mpr (show o ∈ m.selection.made ++ (bagOf A rest).selection.made from
          List.mem_append_left _ first))
        (enabled.taken_subset (List.mem_toFinset.mpr
          (show o ∈ m.selection.taken ++ (bagOf A rest).selection.taken from
            List.mem_append_right _ later)))
    simp only [mem_fire, Selection.commit, List.mem_toFinset, takenEq, madeEq, List.mem_append]
    tauto
  · funext o
    show relabel (fun o' => A.apply A.identity
          (relabel (fun o'' => A.apply A.identity (s.label o'') : O → Terms T PUnit.unit)
            m.selection.made (m.firing.opened (frames A)).produce o'))
        (bagOf A rest).selection.made (Bag.produce (frames A) (bagOf A rest)) o =
      relabel (fun o'' => A.apply A.identity (s.label o'') : O → Terms T PUnit.unit)
        (m.selection.made ++ (bagOf A rest).selection.made)
        ((m.firing.opened (frames A)).produce ++ Bag.produce (frames A) (bagOf A rest)) o
    rw [relabel_append _ _ _ _ _ rowsMade apartMade o]
    exact Scope.relabel_congr (A.apply_identity _) _ _

/-- **Peeling the first member.** If a bag is admitted with the guards of each member at its own
information, and the rules of all members but the first are positive, then the first member is admitted
by the step of the program, the rest is admitted at its result, and the result of the rest there is the
result of the whole bag. -/
theorem peel (positive : ∀ r ∈ rest, Positive r.rule)
    (own : Bag.AdmitsOwn (frames A) s (bagOf A (m :: rest))) :
    m.firing.Admits (frames A) s ∧
      Bag.AdmitsOwn (frames A) (m.firing.result (frames A) s) (bagOf A rest) ∧
      Bag.result (frames A) (m.firing.result (frames A) s) (bagOf A rest) =
        Bag.result (frames A) s (bagOf A (m :: rest)) := by
  have head : m.firing.Admits (frames A) s :=
    Bag.admits_member (frames A) (fun _ _ => ⟨A.identity⟩) own List.mem_cons_self
  obtain ⟨fits, enabled, solvable, asks⟩ := own
  have same := information_after (s := s) A fun r inside => selected_apart A enabled inside
  refine ⟨head, ⟨⟨fresh_after A head.1 head.2.1 fits.1, ?_, ?_, fun r inside =>
      fits.2.2.2 r (List.mem_cons_of_mem _ inside)⟩, enabled_after A fits.2.1 fits.2.2.1 enabled, ?_,
      fun r inside b σ solved => ?_⟩, result_after A fits enabled⟩
  · exact (List.nodup_append.mp (show (m.selection.taken ++ (bagOf A rest).selection.taken).Nodup from
      fits.2.1)).2.1
  · exact (List.nodup_append.mp (show (m.selection.made ++ (bagOf A rest).selection.made).Nodup from
      fits.2.2.1)).2.1
  · exact Eq.mpr (congrArg ((frames A).Solvable (a := PUnit.unit)) same) solvable
  · have apartR := selected_apart A enabled inside
    have split : A.Models σ (m.firing.information (frames A) s ++ Member.own (frames A) s r) :=
      Eq.mp (congrArg (A.Models σ) (information_after_member A s m.firing r apartR.1 apartR.2)) solved
    have parts := (A.models_append σ _ _).mp split
    have first : A.Models σ ((frames A).applyStore ((ext A).weaken m.firing.ext) s.knowledge ++
        Member.own (frames A) s m) :=
      Eq.mp (congrArg (A.Models σ) (Member.information_eq (frames A) s m)) parts.1
    have known := ((A.models_append σ _ _).mp first).1
    have before : A.Models σ (r.firing.information (frames A) s) :=
      Eq.mpr (congrArg (A.Models σ) (Member.information_eq (frames A) s r))
        ((A.models_append σ _ _).mpr ⟨known, parts.2⟩)
    exact Scope.holds_of_positive A (positive r inside)
      (asks r (List.mem_cons_of_mem _ inside) b σ before)

end Peel

/-! ## Runs -/

/-- **An admitted bag of positive rules is a run of its members**, in their order, ending at the result
of the bag. -/
theorem run_of_admitsOwn : ∀ (l : List (OneMember A O P)) (s : State (Terms T) O),
    (∀ r ∈ l, Positive r.rule) → Bag.AdmitsOwn (frames A) s (bagOf A l) →
    Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s
      (Bag.result (frames A) s (bagOf A l))
  | [], s, _, _ => by
      rw [result_nil A s]
  | m :: rest, s, positive, own => by
      obtain ⟨head, later, same⟩ :=
        peel A (fun r inside => positive r (List.mem_cons_of_mem _ inside)) own
      rw [← same]
      exact Relation.ReflTransGen.head ⟨m.firing, head, rfl⟩
        (run_of_admitsOwn rest _ (fun r inside => positive r (List.mem_cons_of_mem _ inside)) later)

/-! ## States that mention only fixed terms -/

/-- **At a state that mentions only fixed terms, guards at the joint information are guards at each
member's own**, for positive rules. -/
theorem admitsOwn_of_fixed {s : State (Terms T) O} {l : List (OneMember A O P)}
    (fixed : ∀ t, s.Mentions t → ∀ σ : S, A.E (A.apply σ t) t)
    (positive : ∀ r ∈ l, Positive r.rule)
    (admitted : Bag.Admits (frames A) s (bagOf A l)) : Bag.AdmitsOwn (frames A) s (bagOf A l) := by
  classical
  obtain ⟨fits, enabled, solvable, asks⟩ := admitted
  refine ⟨fits, enabled, solvable, fun m inside b σ solved => ?_⟩
  obtain ⟨_, τ, joint⟩ := solvable
  obtain ⟨u, -, rules⟩ := Realized.pick (frames A)
    (fun r : OneMember A O P => if r = m then A.compose σ r.opening else A.compose τ r.opening) l
    (fits.1 PUnit.unit σ)
  have near : ∀ t₀ ∈ m.rule.terms,
      A.E (A.apply u (A.apply m.opening t₀)) (A.apply σ (A.apply m.opening t₀)) := by
    intro t₀ member
    have key : A.E (A.apply u (A.apply m.opening t₀))
        (A.apply (if m = m then A.compose σ m.opening else A.compose τ m.opening) t₀) :=
      rules m inside t₀ member
    rw [if_pos rfl, A.apply_compose] at key
    exact key
  have each : ∀ r ∈ l, A.Models u (r.firing.information (frames A) s) := by
    intro r inR
    have enabledR := Bag.enabled_member enabled inR
    by_cases same : r = m
    · refine Scope.models_information_of_agree A enabledR (fun t foot => ?_)
        (show A.Models σ (r.firing.information (frames A) s) from same ▸ solved)
      rcases foot with mentioned | opened
      · exact A.equivalence.trans (fixed t mentioned u) (A.equivalence.symm (fixed t mentioned σ))
      · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
        have key : A.E (A.apply u (A.apply r.opening t₀))
            (A.apply (if r = m then A.compose σ r.opening else A.compose τ r.opening) t₀) :=
          rules r inR t₀ member
        rw [if_pos same, A.apply_compose] at key
        exact key
    · refine Scope.models_information_of_agree A enabledR (fun t foot => ?_)
        (show A.Models τ (r.firing.information (frames A) s) from Bag.models_member (frames A) inR joint)
      rcases foot with mentioned | opened
      · exact A.equivalence.trans (fixed t mentioned u) (A.equivalence.symm (fixed t mentioned τ))
      · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
        have key : A.E (A.apply u (A.apply r.opening t₀))
            (A.apply (if r = m then A.compose σ r.opening else A.compose τ r.opening) t₀) :=
          rules r inR t₀ member
        rw [if_neg same, A.apply_compose] at key
        exact key
  have whole : A.Models u (Bag.information (frames A) s (bagOf A l)) := by
    have mine : A.Models u ((frames A).applyStore ((ext A).weaken m.firing.ext) s.knowledge ++
        Member.own (frames A) s m) :=
      Eq.mp (congrArg (A.Models u) (Member.information_eq (frames A) s m)) (each m inside)
    refine (A.models_append u _ _).mpr ⟨((A.models_append u _ _).mp mine).1, fun e inOwn => ?_⟩
    obtain ⟨r, inR, inside'⟩ := List.mem_flatMap.mp inOwn
    have theirs : A.Models u ((frames A).applyStore ((ext A).weaken r.firing.ext) s.knowledge ++
        Member.own (frames A) s r) :=
      Eq.mp (congrArg (A.Models u) (Member.information_eq (frames A) s r)) (each r inR)
    exact ((A.models_append u _ _).mp theirs).2 e inside'
  have held : m.firing.Holds (frames A) s (b := PUnit.unit) u := asks PUnit.unit u whole m inside
  refine ⟨fun c member => ?_, fun q member => ?_⟩
  · obtain ⟨c₀, inRule, lhs, rhs, rfl, rfl⟩ := Scope.opened_check_equal A (positive m inside) member
    have atU : A.E (A.apply u (A.apply m.opening lhs)) (A.apply u (A.apply m.opening rhs)) :=
      held.1 _ member
    have terms := Scope.equal_mem_terms inRule
    show A.E (A.apply σ (A.apply m.opening lhs)) (A.apply σ (A.apply m.opening rhs))
    exact A.equivalence.trans (A.equivalence.symm (near lhs terms.1))
      (A.equivalence.trans atU (near rhs terms.2))
  · simp [Firing.collectOpened, (positive m inside).2] at member

/-- **At a state that mentions only fixed terms, every admitted bag of positive rules is a run of its
members.** -/
theorem run_of_admits_of_fixed {s : State (Terms T) O} {l : List (OneMember A O P)}
    (fixed : ∀ t, s.Mentions t → ∀ σ : S, A.E (A.apply σ t) t)
    (positive : ∀ r ∈ l, Positive r.rule)
    (admitted : Bag.Admits (frames A) s (bagOf A l)) :
    Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s
      (Bag.result (frames A) s (bagOf A l)) :=
  run_of_admitsOwn A l s positive (admitsOwn_of_fixed A fixed positive admitted)

#print axioms row_after
#print axioms own_after
#print axioms information_after_member
#print axioms result_nil
#print axioms admits_nil_iff_consistent
#print axioms information_after
#print axioms enabled_after
#print axioms fresh_after
#print axioms result_after
#print axioms peel
#print axioms run_of_admitsOwn
#print axioms admitsOwn_of_fixed
#print axioms run_of_admits_of_fixed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
