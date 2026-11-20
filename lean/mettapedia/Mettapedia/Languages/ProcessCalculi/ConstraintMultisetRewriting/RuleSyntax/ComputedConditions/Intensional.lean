import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Tables

/-!
# A table that is not stored: the program holds the graph

The store is a finite set of identities (`State.present`); the graph of a function is in general
infinite. The program at a graph (`specialized`) holds the graph instead: it has one rule per choice of
points, and a firing chooses the points it uses. No row of the store is read for them, and no change of
`RuleSyntax.Core` is needed: a read that needs no identity is a rule of the program indexed by the row.

This module relates two restricted relations, relative to ONE finite set of table identities chosen before
the run (`tables`): the firings of the program at a graph whose points label identities of that set in the
state's own label function and whose made identities avoid the set (`PointStep`), and the firings of the
program of table reads, at the same state with those identities present, whose conditions read rows at
identities of the set (`StoredStep`). The proof is by locality (`admits_iff_of_outsideRegions`) and the
exchange of stored rows and points (`points_to_table`, `table_to_points`).

Hypotheses of the run theorems: every point of the graph is fixed by every substitution (`fixedGraph`),
every rule is blind to the graph (`Blind`), and the state labels the identities of `tables`, which it does
not have, by fixed points of the graph (`StoresGraph`).

What the run theorems do not relate: `PointStep` is not the step of the program at the graph. A firing of
that program whose points label no identity of the chosen set is no `PointStep`, and there are such firings
(`StoredRuns.graph_fires`, `StoredRuns.no_pointStep`). The hypotheses and a run have an instance
(`StoredRuns.addStep_blind`, `StoredRuns.stores`, `StoredRuns.stored_run_exists`). Without identities chosen
before the run, on states that read as bags: `StoredRuns.stored_run_to_evaluated` and
`StoredRuns.evaluated_run_to_stored`.

* **Stored tables** (`withTables s tables`): the state `s` with the identities `tables` present as well,
  labelled by `s.label`; the stored rows are fixed points of the graph at identities `s` does not have
  (`StoresGraph`).
* **Blind rules** (`Blind`): no substitution equates a take, read, none queries, count or collect pattern of the
  rule with a point of the graph. The table rows are then seen only by the conditions.
* `points_to_stored`: **a firing of the program at the graph at `s`**, whose points are stored and
  whose made identities avoid the stored ones, **is a firing of the program of table reads at the state
  with the tables stored**, and its result is the result at `s` with the same tables stored.
* `stored_to_points`: conversely, **a firing of the program of table reads at the state with the tables
  stored, whose conditions read stored rows, is a firing of the program at the graph at `s`**, and its
  result is that firing's result at `s` with the same tables stored.
* `withTables_result`, `storesGraph_result`: the results keep the stored rows.
* **The runs of the two restricted relations are the same** (`runs_stored_to_points`,
  `runs_points_to_stored`): a run of the table reads from the state with the tables stored, whose
  conditions read stored rows (`StoredStep`), is a run of `PointStep` from the state without them (points
  labelling stored identities, made identities apart from them), to the same state with the tables stored,
  and conversely.

So the function is evaluated, in the first program, by the membership of a rule (`mem_specialized`);
in the second, by the rows the store holds. The step is `RuleSyntax.step` in both, restricted as above.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (Terms frames ext)

universe uF uT uS uO

variable {F : Type uF} {T : Type uT} {S : Type uS} {A : SubstitutionAction T S} {O : Type uO}
  [DecidableEq O] {R : Tabulation F T}

/-- **The state with stored tables**: the identities `tables` present beside those of `s`, labelled by
`s.label`. -/
def withTables (s : State (Terms T) O) (tables : Finset O) : State (Terms T) O :=
  s.withPresent (s.present ∪ tables)

/-- **The stored rows are fixed points of the graph, at identities `s` does not have.** -/
def StoresGraph (A : SubstitutionAction T S) (G : Set T) (s : State (Terms T) O) (tables : Finset O) :
    Prop :=
  Disjoint tables s.present ∧ ∀ o ∈ tables, s.label o ∈ G ∧ Fixed A (s.label o)

/-- **A rule blind to the graph**: no substitution equates one of its take, read, none queries, count or
collect patterns with a point of the graph. -/
def Blind (A : SubstitutionAction T S) (G : Set T) (r : Rule (Terms T)) : Prop :=
  ∀ σ : S, ∀ g ∈ G, ∀ p ∈ r.body.take ++ r.body.read ++ r.body.checks.filterMap checkRegion ++ r.collect,
    ¬ A.E (A.apply σ p) g

theorem blind_at {G : Set T} {ρ : RuleWithCondition F T} (blind : Blind A G ρ.rule) (points : List T) :
    Blind A G (ρ.at R points) := blind

section Locality

variable {P : Program (Terms T)} {G : Set T}

/-- **Stored fixed rows do not change freshness.** -/
theorem fresh_withTables_iff {s : State (Terms T) O} {tables : Finset O}
    (fixed : ∀ o ∈ tables, Fixed A (s.label o)) (f : Firing O (ext A) P PUnit.unit) :
    f.Fresh (frames A) s ↔ f.Fresh (frames A) (withTables s tables) := by
  constructor
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b g h
    refine ⟨u, fun t mentioned => ?_, onRule⟩
    rcases mentioned with inKnowledge | inKnowledge | ⟨o, present, rfl⟩
    · exact onState t (.inl inKnowledge)
    · exact onState t (.inr (.inl inKnowledge))
    · rcases Finset.mem_union.mp present with old | stored
      · exact onState _ (.inr (.inr ⟨o, old, rfl⟩))
      · show A.E (A.apply u (A.apply A.identity (s.label o))) (A.apply g (s.label o))
        rw [fixed o stored, fixed o stored, fixed o stored]
        exact A.equivalence.refl _
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b g h
    refine ⟨u, fun t mentioned => onState t ?_, onRule⟩
    rcases mentioned with inKnowledge | inKnowledge | ⟨o, present, rfl⟩
    · exact .inl inKnowledge
    · exact .inr (.inl inKnowledge)
    · exact .inr (.inr ⟨o, Finset.mem_union_left _ present, rfl⟩)

omit [DecidableEq O] in
/-- A blind rule's opened pattern is equated with no stored row by any substitution. -/
theorem blind_row {s : State (Terms T) O} {tables : Finset O} (stores : StoresGraph A G s tables)
    (f : Firing O (ext A) P PUnit.unit) (blind : Blind A G f.rule) (σ : S) {p : T}
    (inside : p ∈ f.rule.body.take ++ f.rule.body.read ++ f.rule.body.checks.filterMap checkRegion ++
      f.rule.collect) {o : O} (stored : o ∈ tables) :
    ¬ A.E (A.apply σ (A.apply f.opening p)) (A.apply σ (A.apply A.identity (s.label o))) := by
  rw [(stores.2 o stored).2 A.identity, (stores.2 o stored).2 σ, ← A.apply_compose]
  exact blind _ _ (stores.2 o stored).1 p inside

omit [DecidableEq O] in
theorem queryPatterns_of_mem (f : Firing O (ext A) P PUnit.unit) {q : T}
    (inside : q ∈ f.queryPatterns (frames A)) :
    ∃ p ∈ f.rule.body.take ++ f.rule.body.read ++ f.rule.body.checks.filterMap checkRegion ++
      f.rule.collect, q = A.apply f.opening p := by
  rcases List.mem_append.mp inside with query | collect
  · obtain ⟨c, inChecks, region⟩ := List.mem_filterMap.mp query
    obtain ⟨c₀, inRule, rfl⟩ := List.mem_map.mp inChecks
    cases c₀ with
    | equal _ _ => cases region
    | predicate quantifier pattern =>
        cases region
        exact ⟨pattern, List.mem_append_left _ (List.mem_append_right _
          (List.mem_filterMap.mpr ⟨_, inRule, rfl⟩)), rfl⟩
    | count pattern number =>
        cases region
        exact ⟨pattern, List.mem_append_left _ (List.mem_append_right _
          (List.mem_filterMap.mpr ⟨_, inRule, rfl⟩)), rfl⟩
  · obtain ⟨p, inCollect, rfl⟩ := List.mem_map.mp collect
    exact ⟨p, List.mem_append_right _ inCollect, rfl⟩

/-- **Storing the tables is a change outside the regions of a blind firing** whose selected rows are the
state's and whose made identities are neither present nor stored. -/
theorem outside_withTables {s : State (Terms T) O} {tables : Finset O} (stores : StoresGraph A G s tables)
    (f : Firing O (ext A) P PUnit.unit) (blind : Blind A G f.rule)
    (selected : ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∈ s.present)
    (madeApart : ∀ o ∈ f.selection.made, o ∉ s.present ∧ o ∉ tables) :
    OutsideRegions (frames A) s (s.present ∪ tables) f := by
  refine ⟨fun o touched => ?_, fun b σ _ q inside o changed => ?_⟩
  · rcases touched with taken | read | made
    · exact ⟨fun present => Finset.mem_union_left _ present, fun _ => selected o (.inl taken)⟩
    · exact ⟨fun present => Finset.mem_union_left _ present, fun _ => selected o (.inr read)⟩
    · refine ⟨fun present => absurd present (madeApart o made).1, fun present => ?_⟩
      rcases Finset.mem_union.mp present with old | stored
      · exact absurd old (madeApart o made).1
      · exact absurd stored (madeApart o made).2
  · have stored : o ∈ tables := by
      by_contra notStored
      exact changed ⟨fun present => Finset.mem_union_left _ present, fun present =>
        (Finset.mem_union.mp present).resolve_right notStored⟩
    obtain ⟨p, inRule, rfl⟩ := queryPatterns_of_mem f inside
    exact blind_row stores f blind σ inRule stored

/-- **A blind firing whose information is solvable selects no stored row** by a take or a read. -/
theorem selected_not_stored {s : State (Terms T) O} {tables : Finset O} (stores : StoresGraph A G s tables)
    (f : Firing O (ext A) P PUnit.unit) (blind : Blind A G f.rule)
    (takeLength : f.rule.body.take.length = f.selection.taken.length)
    (readLength : f.rule.body.read.length = f.selection.read.length)
    (solvable : (frames A).Solvable (f.information (frames A) (withTables s tables))) :
    ∀ o, o ∈ f.selection.taken ∨ o ∈ f.selection.read → o ∉ tables := by
  obtain ⟨_, σ, solved⟩ := solvable
  rintro o (taken | read) stored
  · obtain ⟨p, paired⟩ := exists_mem_zip_right (f.opened (frames A)).take f.selection.taken
      (by simp only [Firing.opened, RuleInstance.map, List.length_map]; exact takeLength) o taken
    have equated := f.take_solved (b := PUnit.unit) solved paired
    obtain ⟨p₀, inRule, rfl⟩ := List.mem_map.mp (List.of_mem_zip paired).1
    exact blind_row stores f blind σ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ inRule))) stored equated
  · obtain ⟨p, paired⟩ := exists_mem_zip_right (f.opened (frames A)).read f.selection.read
      (by simp only [Firing.opened, RuleInstance.map, List.length_map]; exact readLength) o read
    have equated := f.read_solved (b := PUnit.unit) solved paired
    obtain ⟨p₀, inRule, rfl⟩ := List.mem_map.mp (List.of_mem_zip paired).1
    exact blind_row stores f blind σ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ inRule))) stored equated

/-- **The result at the state with stored tables is the result at `s` with the same tables stored**,
for a firing that takes no stored row. -/
theorem withTables_result {s : State (Terms T) O} {tables : Finset O} (f : Firing O (ext A) P PUnit.unit)
    (apart : ∀ o ∈ f.selection.taken, o ∉ tables) :
    f.result (frames A) (withTables s tables) = withTables (f.result (frames A) s) tables := by
  have present : fire (s.present ∪ tables) (f.selection.commit (T := Unit)) =
      fire s.present (f.selection.commit (T := Unit)) ∪ tables := by
    ext o
    simp only [fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
    constructor
    · rintro (⟨old | stored, notTaken⟩ | made)
      · exact .inl (.inl ⟨old, notTaken⟩)
      · exact .inr stored
      · exact .inl (.inr made)
    · rintro ((⟨old, notTaken⟩ | made) | stored)
      · exact .inl ⟨.inl old, notTaken⟩
      · exact .inr made
      · exact .inl ⟨.inr stored, fun taken => apart o taken stored⟩
  simp only [Firing.result, withTables, State.withPresent]
  rw [present]
  rfl

/-- **The stored rows stay stored** in the result of a firing that makes no stored identity. -/
theorem storesGraph_result {s : State (Terms T) O} {tables : Finset O} (stores : StoresGraph A G s tables)
    (f : Firing O (ext A) P PUnit.unit) (madeApart : ∀ o ∈ f.selection.made, o ∉ tables) :
    StoresGraph A G (f.result (frames A) s) tables := by
  have label : ∀ o ∈ tables, (f.result (frames A) s).label o = s.label o := by
    intro o stored
    rw [Firing.result_label_other f (fun made => madeApart o made stored)]
    show A.apply A.identity (s.label o) = s.label o
    exact (stores.2 o stored).2 A.identity
  refine ⟨Finset.disjoint_left.mpr fun o stored present => ?_, fun o stored => ?_⟩
  · simp only [Firing.result, fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff,
      List.mem_toFinset] at present
    rcases present with ⟨old, -⟩ | made
    · exact Finset.disjoint_left.mp stores.1 stored old
    · exact madeApart o made stored
  · rw [label o stored]
    exact stores.2 o stored

end Locality

/-! ## The two programs have the same steps -/

section Steps

variable {G : Set T} {P : Set (RuleWithCondition F T)}

/-- **From the graph to the stored tables.** A firing of the program at the graph at `s`, whose rule is
blind, whose points are the labels of stored rows and whose made identities avoid the stored ones, is
the point firing of choices whose table firing is admitted at the state with the tables stored, and the
results agree: the result there is the result at `s` with the tables stored. -/
theorem points_to_stored (fixedGraph : ∀ g ∈ G, Fixed A g) {s : State (Terms T) O} {tables : Finset O}
    (stores : StoresGraph A G s tables) (h : Firing O (ext A) (specialized R G P) PUnit.unit)
    (admitted : (step (frames A) O (ext A) (specialized R G P)).Admits (s := s) h)
    {ρ : RuleWithCondition F T} (inP : ρ ∈ P) {points : List T} (isRule : h.rule = ρ.at R points)
    (length : points.length = ρ.conditions.length) (blind : Blind A G ρ.rule)
    (stored : List O) (storedIn : ∀ o ∈ stored, o ∈ tables) (labels : stored.map s.label = points)
    (madeApart : ∀ o ∈ h.selection.made, o ∉ tables) :
    ∃ (c : Choice O S) (member : ρ.at R points ∈ specialized R G P),
      c.tables = stored ∧ h = pointFiring (A := A) ρ points member c ∧
      (step (frames A) O (ext A) (tabled R P)).Admits (s := withTables s tables)
        (tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c) ∧
      (tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c).result (frames A) (withTables s tables) =
        withTables (h.result (frames A) s) tables := by
  obtain ⟨fresh, ⟨_, _, _, _, _, _⟩, enabled, _, _⟩ := (admits_iff h).mp admitted
  have blindH : Blind A G h.rule := isRule ▸ blind_at blind points
  have selected : ∀ o, o ∈ h.selection.taken ∨ o ∈ h.selection.read → o ∈ s.present := by
    rintro o (taken | read)
    · exact enabled.taken_subset (by simp [Selection.commit, taken])
    · exact enabled.kept_subset (by simp [Selection.commit, read])
  have made : ∀ o ∈ h.selection.made, o ∉ s.present ∧ o ∉ tables := fun o inside =>
    ⟨fun present => Finset.disjoint_left.mp enabled.fresh (by simp [Selection.commit, inside]) present,
      madeApart o inside⟩
  have outside := outside_withTables stores h blindH selected made
  have fixed : ∀ o ∈ tables, Fixed A (s.label o) := fun o inside => (stores.2 o inside).2
  have atStored : (step (frames A) O (ext A) (specialized R G P)).Admits (s := withTables s tables) h :=
    (admits_iff_of_outsideRegions outside fresh ((fresh_withTables_iff fixed h).mp fresh)).mp admitted
  have onGraph : ∀ g ∈ points, g ∈ G := by
    intro g inside
    rw [← labels] at inside
    obtain ⟨o, member, rfl⟩ := List.mem_map.mp inside
    exact (stores.2 o (storedIn o member)).1
  have notTaken : ∀ o ∈ h.selection.taken, o ∉ tables := fun o taken stored' =>
    Finset.disjoint_left.mp stores.1 stored' (selected o (.inl taken))
  obtain ⟨c, member, tablesEq, same, admittedT, resultT⟩ := points_to_table fixedGraph (withTables s tables) h
    atStored inP isRule length onGraph stored labels (fun o inside =>
      ⟨Finset.mem_union_right _ (storedIn o inside), fun taken => notTaken o taken (storedIn o inside)⟩)
  exact ⟨c, member, tablesEq, same, admittedT, resultT.trans (withTables_result h notTaken)⟩

/-- **From the stored tables to the graph.** A firing of the program of table reads at the state with the
tables stored, whose rule is blind and whose conditions read stored rows, is the table firing of choices
whose point firing is admitted at `s`, with the result at the stored state equal to the point firing's
result at `s` with the tables stored. -/
theorem stored_to_points (fixedGraph : ∀ g ∈ G, Fixed A g) {s : State (Terms T) O} {tables : Finset O}
    (stores : StoresGraph A G s tables) (g : Firing O (ext A) (tabled R P) PUnit.unit)
    (admitted : (step (frames A) O (ext A) (tabled R P)).Admits (s := withTables s tables) g)
    {ρ : RuleWithCondition F T} (inP : ρ ∈ P) (isRule : g.rule = ρ.tableRule R) (blind : Blind A G ρ.rule)
    (readsStored : ∀ o ∈ g.selection.read.drop ρ.rule.body.read.length, o ∈ tables) :
    ∃ (c : Choice O S) (member : ρ.at R (c.tables.map s.label) ∈ specialized R G P),
      g = tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c ∧
      (c.tables.map s.label).length = ρ.conditions.length ∧ (∀ o ∈ c.tables, o ∈ tables) ∧
      (∀ o ∈ c.made, o ∉ tables) ∧
      (step (frames A) O (ext A) (specialized R G P)).Admits (s := s)
        (pointFiring (A := A) ρ (c.tables.map s.label) member c) ∧
      g.result (frames A) (withTables s tables) =
        withTables ((pointFiring (A := A) ρ (c.tables.map s.label) member c).result (frames A) s) tables := by
  obtain ⟨c, member, same, lengths, admittedP, resultP⟩ := table_to_points fixedGraph (withTables s tables) g
    admitted inP isRule (fun o inside => (stores.2 o (readsStored o inside)).1)
  let h := pointFiring (A := A) (P := specialized R G P) ρ (c.tables.map s.label) member c
  obtain ⟨freshW, ⟨_, _, takeLength, readLength, _, _⟩, enabledW, solvableW, _⟩ := (admits_iff h).mp admittedP
  have blindH : Blind A G h.rule := blind_at blind _
  have notStored := selected_not_stored stores h blindH takeLength readLength solvableW
  have selected : ∀ o, o ∈ h.selection.taken ∨ o ∈ h.selection.read → o ∈ s.present := by
    intro o chosen
    have inW : o ∈ (withTables s tables).present := by
      rcases chosen with taken | read
      · exact enabledW.taken_subset (by simp [Selection.commit, taken])
      · exact enabledW.kept_subset (by simp [Selection.commit, read])
    exact (Finset.mem_union.mp inW).resolve_right (notStored o chosen)
  have made : ∀ o ∈ h.selection.made, o ∉ s.present ∧ o ∉ tables := by
    intro o inside
    have apart : o ∉ (withTables s tables).present := fun present =>
      Finset.disjoint_left.mp enabledW.fresh (by simp [Selection.commit, inside]) present
    exact ⟨fun present => apart (Finset.mem_union_left _ present),
      fun stored => apart (Finset.mem_union_right _ stored)⟩
  have outside := outside_withTables stores h blindH selected made
  have fixed : ∀ o ∈ tables, Fixed A (s.label o) := fun o inside => (stores.2 o inside).2
  have atS : (step (frames A) O (ext A) (specialized R G P)).Admits (s := s) h :=
    (admits_iff_of_outsideRegions outside ((fresh_withTables_iff fixed h).mpr freshW) freshW).mpr admittedP
  have tablesStored : ∀ o ∈ c.tables, o ∈ tables := by
    intro o inside
    apply readsStored o
    rw [same]
    show o ∈ (c.read ++ c.tables).drop ρ.rule.body.read.length
    rw [show ρ.rule.body.read.length = c.read.length from readLength, List.drop_left]
    exact inside
  exact ⟨c, member, same, lengths, tablesStored, fun o inside => (made o inside).2, atS,
    resultP.trans (withTables_result h fun o taken => notStored o (.inl taken))⟩

end Steps

/-! ## The two programs have the same runs -/

section Runs

variable (A) (R) (G : Set T) (P : Set (RuleWithCondition F T)) (tables : Finset O)

/-- **A step of the table reads whose conditions read stored rows.** -/
def StoredStep (s' t' : State (Terms T) O) : Prop :=
  ∃ (g : Firing O (ext A) (tabled R P) PUnit.unit)
    (admitted : (step (frames A) O (ext A) (tabled R P)).Admits (s := s') g),
    (∃ ρ ∈ P, g.rule = ρ.tableRule R ∧ ∀ o ∈ g.selection.read.drop ρ.rule.body.read.length, o ∈ tables) ∧
    t' = (step (frames A) O (ext A) (tabled R P)).result g admitted

/-- **A step of the program at the graph whose points are labels of stored identities and whose made
identities avoid them.** -/
def PointStep (s t : State (Terms T) O) : Prop :=
  ∃ (h : Firing O (ext A) (specialized R G P) PUnit.unit)
    (admitted : (step (frames A) O (ext A) (specialized R G P)).Admits (s := s) h),
    (∃ ρ ∈ P, ∃ points : List T, h.rule = ρ.at R points ∧ points.length = ρ.conditions.length ∧
      ∃ stored : List O, (∀ o ∈ stored, o ∈ tables) ∧ stored.map s.label = points) ∧
    (∀ o ∈ h.selection.made, o ∉ tables) ∧ t = (step (frames A) O (ext A) (specialized R G P)).result h admitted

variable {A R G P tables}

/-- **Every run of the table reads from the state with the tables stored, reading stored rows, is a run of
`PointStep` from the state without them** (firings of the program at the graph whose points label stored
identities), ending at the same state with the tables stored. The set `tables` is one set for the whole run;
the graph's points are fixed by every substitution. -/
theorem runs_stored_to_points (fixedGraph : ∀ g ∈ G, Fixed A g) (blind : ∀ ρ ∈ P, Blind A G ρ.rule)
    {s : State (Terms T) O} (stores : StoresGraph A G s tables) {t' : State (Terms T) O}
    (run : Relation.ReflTransGen (StoredStep A R P tables) (withTables s tables) t') :
    ∃ t, Relation.ReflTransGen (PointStep A R G P tables) s t ∧ t' = withTables t tables ∧
      StoresGraph A G t tables := by
  induction run with
  | refl => exact ⟨s, .refl, rfl, stores⟩
  | tail _ moved ih =>
      obtain ⟨t, points, rfl, storesT⟩ := ih
      obtain ⟨g, admitted, ⟨ρ, inP, isRule, readsStored⟩, rfl⟩ := moved
      obtain ⟨c, member, -, lengths, tablesStored, madeApart, admittedP, resultEq⟩ :=
        stored_to_points fixedGraph storesT g admitted inP isRule (blind ρ inP) readsStored
      refine ⟨_, .tail points ⟨_, admittedP, ⟨ρ, inP, c.tables.map t.label, rfl, lengths, c.tables,
        tablesStored, rfl⟩, madeApart, rfl⟩, resultEq, storesGraph_result storesT _ madeApart⟩

/-- **Every run of the program at the graph from the state without the tables, whose points are stored
and whose made identities avoid them, is a run of the table reads from the state with the tables
stored**, ending at the same state with the tables stored. -/
theorem runs_points_to_stored (fixedGraph : ∀ g ∈ G, Fixed A g) (blind : ∀ ρ ∈ P, Blind A G ρ.rule)
    {s : State (Terms T) O} (stores : StoresGraph A G s tables) {t : State (Terms T) O}
    (run : Relation.ReflTransGen (PointStep A R G P tables) s t) :
    Relation.ReflTransGen (StoredStep A R P tables) (withTables s tables) (withTables t tables) ∧
      StoresGraph A G t tables := by
  induction run with
  | refl => exact ⟨.refl, stores⟩
  | tail _ moved ih =>
      obtain ⟨stored', storesT⟩ := ih
      obtain ⟨h, admitted, ⟨ρ, inP, points, isRule, length, stored, storedIn, labels⟩, madeApart, rfl⟩ := moved
      obtain ⟨c, member, tablesEq, same, admittedT, resultEq⟩ :=
        points_to_stored fixedGraph storesT h admitted inP isRule length (blind ρ inP) stored storedIn labels
          madeApart
      have readLength : ρ.rule.body.read.length = c.read.length := by
        have shapes := (admits_iff h).mp admitted
        rw [same] at shapes
        exact shapes.2.1.2.2.2.1
      refine ⟨.tail stored' ⟨_, admittedT, ⟨ρ, inP, rfl, fun o inside => ?_⟩, ?_⟩,
        storesGraph_result storesT _ madeApart⟩
      · have inTables : o ∈ c.tables := by
          have dropped : (c.read ++ c.tables).drop ρ.rule.body.read.length = c.tables := by
            rw [readLength, List.drop_left]
          rw [← dropped]
          exact inside
        rw [tablesEq] at inTables
        exact storedIn o inTables
      · exact resultEq.symm

end Runs

#print axioms fresh_withTables_iff
#print axioms outside_withTables
#print axioms selected_not_stored
#print axioms withTables_result
#print axioms storesGraph_result
#print axioms points_to_stored
#print axioms stored_to_points
#print axioms runs_stored_to_points
#print axioms runs_points_to_stored

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
