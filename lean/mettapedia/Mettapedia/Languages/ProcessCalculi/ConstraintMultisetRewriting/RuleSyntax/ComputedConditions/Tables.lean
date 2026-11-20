import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Syntax

/-!
# Reading a stored row of a table is telling a point of the table

At the one frame of a substitution action, a firing of a rule with conditions is given by its
**choices** (`Choice`): an opening, the taken rows, the rows its own read patterns read, the rows of
the tables its conditions read, the made identities and the seen sets. The same choices give a
firing of the table read (`tableFiring`) and, at any points, a firing of the rule at those points
(`pointFiring`), which reads no table row.

A **point is fixed** (`Fixed`) when every substitution fixes it: a ground row. At a stored row that holds
an unknown the theorem below fails: the table read is admitted and the rule at that point is refused
(`OpenRow.box_not_fixed`, `OpenRow.nullary_table_admitted`, `OpenRow.nullary_point_refused`).

## The theorem

At one state, with the table rows read labelled by fixed points:

* `information_eq`: the two firings have **the same information**, equation for equation: reading the
  stored row `g` with the call row `q` contributes the equation `q ≐ g`, which is exactly what the rule
  at the point `g` tells;
* `tableFiring_admits_iff`: **the table firing is admitted exactly when the point firing is admitted
  and the table rows it reads are present and not taken**;
* `tableFiring_result`: **the two results are equal.**

So a stored row of a table and a rule specialized at that row are interchangeable: every table firing
gives a point firing with the same result (`table_to_points`), and every point firing whose points are
stored gives a table firing (`points_to_table`). The two are one firing for one firing only at a state
that stores each point at most once (`tables_unique`: there the table rows are determined by the
points); where a point is stored twice, one point firing has two table firings. Over a graph of fixed
points, the program of table reads and the program at the graph (`specialized`) have the same
admitted firings and results at every state whose table rows read are points of the graph. The theorems
are about one firing at one state; along runs see `Intensional` and `StoredRuns`.

The function is evaluated in one of two places: by the rows the store holds, or by the membership of
the specialization in the program. The step is the same.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (Terms frames ext)

universe uF uT uS uO

variable {F : Type uF} {T : Type uT} {S : Type uS}

/-- **A fixed term**: every substitution fixes it. -/
def Fixed (A : SubstitutionAction T S) (t : T) : Prop := ∀ σ : S, A.apply σ t = t

/-- **The choices of a firing of a rule with conditions**: an opening, the taken rows, the rows its own
read patterns read, the rows of the tables its conditions read, the made identities, and the rows each
collect pattern claims to see. -/
structure Choice (O : Type uO) (S : Type uS) where
  opening : S
  taken : List O
  read : List O
  tables : List O
  made : List O
  seen : List (Finset O)

variable {A : SubstitutionAction T S} {O : Type uO} [DecidableEq O] {R : Tabulation F T}

/-- **The firing of the table read** with the given choices. -/
def tableFiring {P : Program (Terms T)} (ρ : RuleWithCondition F T) (member : ρ.tableRule R ∈ P)
    (c : Choice O S) : Firing O (ext A) P PUnit.unit :=
  ⟨ρ.tableRule R, member, PUnit.unit, c.opening, ⟨c.taken, c.read ++ c.tables, c.made⟩, c.seen⟩

/-- **The firing of the rule at points** with the given choices; it reads no table row. -/
def pointFiring {P : Program (Terms T)} (ρ : RuleWithCondition F T) (points : List T)
    (member : ρ.at R points ∈ P) (c : Choice O S) : Firing O (ext A) P PUnit.unit :=
  ⟨ρ.at R points, member, PUnit.unit, c.opening, ⟨c.taken, c.read, c.made⟩, c.seen⟩

/-! ## The information is the same -/

section Information

omit [DecidableEq O]

/-- Reading rows labelled by fixed points is telling the patterns equal to the points. -/
theorem matching_points (s : State (Terms T) O) (θ : S) :
    ∀ (qs : List T) (os : List O), (∀ o ∈ os, Fixed A (s.label o)) →
      (qs.map (A.apply θ)).zipWith (fun p o => (p, A.apply A.identity (s.label o))) os =
        (qs.zip (os.map s.label)).map fun pair => (A.apply θ pair.1, A.apply θ pair.2)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | q :: qs, o :: os, fixed => by
      have head : A.apply A.identity (s.label o) = A.apply θ (s.label o) := by
        rw [fixed o List.mem_cons_self A.identity, fixed o List.mem_cons_self θ]
      simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, head]
      rw [matching_points s θ qs os fun o' inside => fixed o' (List.mem_cons_of_mem _ inside)]

variable {P Q : Program (Terms T)} (s : State (Terms T) O) (ρ : RuleWithCondition F T)
  (mT : ρ.tableRule R ∈ P) (points : List T) (mP : ρ.at R points ∈ Q) (c : Choice O S)

/-- **The two firings have the same information**: the read of each stored row is the tell of its
point. -/
theorem information_eq (lengthRead : ρ.rule.body.read.length = c.read.length)
    (labels : c.tables.map s.label = points) (fixed : ∀ g ∈ points, Fixed A g) :
    (tableFiring (A := A) ρ mT c).information (frames A) s =
      (pointFiring (A := A) ρ points mP c).information (frames A) s := by
  have fixedRows : ∀ o ∈ c.tables, Fixed A (s.label o) := fun o inside =>
    fixed _ (labels ▸ List.mem_map_of_mem inside)
  show (s.knowledge.map fun e => (A.apply A.identity e.1, A.apply A.identity e.2)) ++
      (ρ.rule.body.take.map (A.apply c.opening)).zipWith
        (fun p o => (p, A.apply A.identity (s.label o))) c.taken ++
      ((ρ.rule.body.read ++ ρ.calls R).map (A.apply c.opening)).zipWith
        (fun p o => (p, A.apply A.identity (s.label o))) (c.read ++ c.tables) ++
      ρ.rule.body.tell.map (fun pair => (A.apply c.opening pair.1, A.apply c.opening pair.2)) =
    (s.knowledge.map fun e => (A.apply A.identity e.1, A.apply A.identity e.2)) ++
      (ρ.rule.body.take.map (A.apply c.opening)).zipWith
        (fun p o => (p, A.apply A.identity (s.label o))) c.taken ++
      (ρ.rule.body.read.map (A.apply c.opening)).zipWith
        (fun p o => (p, A.apply A.identity (s.label o))) c.read ++
      (((ρ.calls R).zip points) ++ ρ.rule.body.tell).map
        (fun pair => (A.apply c.opening pair.1, A.apply c.opening pair.2))
  rw [List.map_append, List.zipWith_append (by rw [List.length_map, lengthRead]), ← labels,
    matching_points s c.opening (ρ.calls R) c.tables fixedRows, List.map_append]
  simp only [List.append_assoc]

end Information

/-! ## Freshness, shapes and enabling -/

section Pieces

omit [DecidableEq O]

variable (ρ : RuleWithCondition F T) (points : List T)

theorem terms_table_sub (length : points.length = ρ.conditions.length) {t : T}
    (inside : t ∈ (ρ.tableRule R).terms) : t ∈ (ρ.at R points).terms := by
  have fsts : ((ρ.calls R).zip points).map Prod.fst = ρ.calls R :=
    List.map_fst_zip (le_of_eq (by rw [RuleWithCondition.calls_length, length]))
  simp only [Rule.terms, RuleWithCondition.tableRule_take, RuleWithCondition.tableRule_read,
    RuleWithCondition.tableRule_tell, RuleWithCondition.tableRule_checks,
    RuleWithCondition.tableRule_produce, RuleWithCondition.tableRule_collect, List.mem_append] at inside
  simp only [Rule.terms, RuleWithCondition.at_take, RuleWithCondition.at_read, RuleWithCondition.at_tell,
    RuleWithCondition.at_checks, RuleWithCondition.at_produce, RuleWithCondition.at_collect, List.map_append,
    fsts, List.mem_append]
  tauto

theorem terms_at_sub {t : T} (inside : t ∈ (ρ.at R points).terms) :
    t ∈ (ρ.tableRule R).terms ∨ t ∈ points := by
  have snds : t ∈ ((ρ.calls R).zip points).map Prod.snd → t ∈ points := fun member => by
    obtain ⟨pair, inZip, rfl⟩ := List.mem_map.mp member
    exact (List.of_mem_zip inZip).2
  have fsts : t ∈ ((ρ.calls R).zip points).map Prod.fst → t ∈ ρ.calls R := fun member => by
    obtain ⟨pair, inZip, rfl⟩ := List.mem_map.mp member
    exact (List.of_mem_zip inZip).1
  simp only [Rule.terms, RuleWithCondition.at_take, RuleWithCondition.at_read, RuleWithCondition.at_tell,
    RuleWithCondition.at_checks, RuleWithCondition.at_produce, RuleWithCondition.at_collect, List.map_append,
    List.mem_append] at inside
  simp only [Rule.terms, RuleWithCondition.tableRule_take, RuleWithCondition.tableRule_read,
    RuleWithCondition.tableRule_tell, RuleWithCondition.tableRule_checks,
    RuleWithCondition.tableRule_produce, RuleWithCondition.tableRule_collect, List.mem_append]
  tauto

variable {P Q : Program (Terms T)} (s : State (Terms T) O)
  (mT : ρ.tableRule R ∈ P) (mP : ρ.at R points ∈ Q) (c : Choice O S)

/-- **Freshness is the same**: the rule at points has the table read's terms and the points, and the
points are fixed. -/
theorem fresh_iff (length : points.length = ρ.conditions.length) (fixed : ∀ g ∈ points, Fixed A g) :
    (tableFiring (A := A) ρ mT c).Fresh (frames A) s ↔ (pointFiring (A := A) ρ points mP c).Fresh (frames A) s := by
  constructor
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b g h
    refine ⟨u, onState, fun t inside => ?_⟩
    rcases terms_at_sub ρ points inside with table | point
    · exact onRule t table
    · show A.E (A.apply u (A.apply c.opening t)) (A.apply h t)
      rw [fixed t point c.opening, fixed t point u, fixed t point h]
      exact A.equivalence.refl t
  · intro fresh b g h
    obtain ⟨u, onState, onRule⟩ := fresh b g h
    exact ⟨u, onState, fun t inside => onRule t (terms_table_sub ρ points length inside)⟩

variable [DecidableEq O]

/-- **Enabling**: the table firing is enabled exactly when the point firing is and the table rows are
present and not taken. -/
theorem enabled_iff :
    Enabled (fun _ : O => ()) s.present ((tableFiring (A := A) ρ mT c).selection.commit (T := Unit)) ↔
      Enabled (fun _ : O => ()) s.present ((pointFiring (A := A) ρ points mP c).selection.commit (T := Unit)) ∧
        ∀ o ∈ c.tables, o ∈ s.present ∧ o ∉ c.taken := by
  simp only [tableFiring, pointFiring, Selection.commit]
  constructor
  · intro enabled
    refine ⟨⟨enabled.taken_subset, fun o inside => enabled.kept_subset ?_, ?_, enabled.fresh,
      fun q inside => by cases inside⟩, fun o inside => ⟨enabled.kept_subset ?_, fun taken => ?_⟩⟩
    · simp only [List.mem_toFinset, List.mem_append] at inside ⊢
      exact .inl inside
    · exact Finset.disjoint_of_subset_right (fun o inside => by
        simp only [List.mem_toFinset, List.mem_append] at inside ⊢
        exact .inl inside) enabled.apart
    · simp only [List.mem_toFinset, List.mem_append]
      exact .inr inside
    · exact Finset.disjoint_left.mp enabled.apart (List.mem_toFinset.mpr taken)
        (by simp only [List.mem_toFinset, List.mem_append]; exact .inr inside)
  · rintro ⟨enabled, tables⟩
    refine ⟨enabled.taken_subset, fun o inside => ?_, ?_, enabled.fresh, fun q inside => by cases inside⟩
    · simp only [List.mem_toFinset, List.mem_append] at inside
      rcases inside with read | table
      · exact enabled.kept_subset (List.mem_toFinset.mpr read)
      · exact (tables o table).1
    · rw [Finset.disjoint_left]
      intro o taken kept
      simp only [List.mem_toFinset, List.mem_append] at kept
      rcases kept with read | table
      · exact Finset.disjoint_left.mp enabled.apart taken (List.mem_toFinset.mpr read)
      · exact (tables o table).2 (List.mem_toFinset.mp taken)

end Pieces

/-! ## Admission and results -/

section Admission

variable {P Q : Program (Terms T)} (s : State (Terms T) O) (ρ : RuleWithCondition F T)
  (mT : ρ.tableRule R ∈ P) (points : List T) (mP : ρ.at R points ∈ Q) (c : Choice O S)

omit [DecidableEq O] in
theorem holds_iff {σ : S} :
    (tableFiring (A := A) ρ mT c).Holds (frames A) s (b := PUnit.unit) σ ↔
      (pointFiring (A := A) ρ points mP c).Holds (frames A) s (b := PUnit.unit) σ := Iff.rfl

/-- **Reading a stored point is telling it.** The table firing is admitted exactly when the firing of the
rule at the points is admitted and the table rows it reads are present and not taken. -/
theorem tableFiring_admits_iff (labels : c.tables.map s.label = points)
    (length : points.length = ρ.conditions.length) (fixed : ∀ g ∈ points, Fixed A g) :
    (step (frames A) O (ext A) P).Admits (s := s) (tableFiring (A := A) ρ mT c) ↔
      (step (frames A) O (ext A) Q).Admits (s := s) (pointFiring (A := A) ρ points mP c) ∧
        ∀ o ∈ c.tables, o ∈ s.present ∧ o ∉ c.taken := by
  have tablesLength : c.tables.length = (ρ.calls R).length := by
    rw [← List.length_map (f := s.label), labels, RuleWithCondition.calls_length, length]
  have reads : (ρ.tableRule R).body.read.length = (c.read ++ c.tables).length ↔
      ρ.rule.body.read.length = c.read.length := by
    simp only [RuleWithCondition.tableRule_read, List.length_append, tablesLength]
    omega
  show (tableFiring (A := A) ρ mT c).Admits (frames A) s ↔
    (pointFiring (A := A) ρ points mP c).Admits (frames A) s ∧ _
  unfold Firing.Admits Firing.Shapes
  rw [fresh_iff ρ points s mT mP c length fixed, enabled_iff ρ points s mT mP c]
  constructor
  · rintro ⟨⟨fresh, takenNodup, madeNodup, take, read, produce, collect⟩, ⟨enabled, tables⟩, solvable, asks⟩
    have readSplit : ρ.rule.body.read.length = c.read.length := reads.mp read
    rw [information_eq s ρ mT points mP c readSplit labels fixed] at solvable asks
    exact ⟨⟨⟨fresh, takenNodup, madeNodup, take, readSplit, produce, collect⟩, enabled, solvable, asks⟩, tables⟩
  · rintro ⟨⟨⟨fresh, takenNodup, madeNodup, take, read, produce, collect⟩, enabled, solvable, asks⟩, tables⟩
    rw [← information_eq s ρ mT points mP c read labels fixed] at solvable asks
    exact ⟨⟨fresh, takenNodup, madeNodup, take, reads.mpr read, produce, collect⟩, ⟨enabled, tables⟩, solvable,
      asks⟩

/-- **The results are equal.** -/
theorem tableFiring_result (lengthRead : ρ.rule.body.read.length = c.read.length)
    (labels : c.tables.map s.label = points) (fixed : ∀ g ∈ points, Fixed A g) :
    (tableFiring (A := A) ρ mT c).result (frames A) s = (pointFiring (A := A) ρ points mP c).result (frames A) s := by
  unfold Firing.result
  rw [information_eq s ρ mT points mP c lengthRead labels fixed]
  rfl

end Admission

/-! ## One firing for one firing, over a graph -/

section Programs

variable {G : Set T} {P : Set (RuleWithCondition F T)}

omit [DecidableEq O] in
/-- Every firing of the program of table reads whose rule is the table read of `ρ` is the table firing
of its choices. -/
theorem eq_tableFiring (g : Firing O (ext A) (tabled R P) PUnit.unit) {ρ : RuleWithCondition F T}
    (member : ρ.tableRule R ∈ tabled R P) (isRule : g.rule = ρ.tableRule R) :
    g = tableFiring (A := A) ρ member ⟨g.opening, g.selection.taken,
      g.selection.read.take ρ.rule.body.read.length, g.selection.read.drop ρ.rule.body.read.length,
      g.selection.made, g.seen⟩ := by
  obtain ⟨rule, inP, ⟨⟩, opening, ⟨taken, read, made⟩, seen⟩ := g
  obtain rfl : rule = ρ.tableRule R := isRule
  simp only [tableFiring, List.take_append_drop]

omit [DecidableEq O] in
/-- Every firing of the program at a graph whose rule is `ρ` at `points` is the point firing of its
choices, with no table rows. -/
theorem eq_pointFiring (h : Firing O (ext A) (specialized R G P) PUnit.unit) {ρ : RuleWithCondition F T}
    {points : List T} (member : ρ.at R points ∈ specialized R G P) (isRule : h.rule = ρ.at R points)
    (tables : List O) :
    h = pointFiring (A := A) ρ points member ⟨h.opening, h.selection.taken, h.selection.read, tables,
      h.selection.made, h.seen⟩ := by
  obtain ⟨rule, inP, ⟨⟩, opening, ⟨taken, read, made⟩, seen⟩ := h
  obtain rfl : rule = ρ.at R points := isRule
  rfl

/-- **From the table to the graph.** An admitted firing of the program of table reads, whose table rows
read are labelled by points of a graph of fixed points, is the table firing of choices whose point
firing is an admitted firing of the program at the graph, with the same result. -/
theorem table_to_points (fixedGraph : ∀ g ∈ G, Fixed A g) (s : State (Terms T) O)
    (g : Firing O (ext A) (tabled R P) PUnit.unit)
    (admitted : (step (frames A) O (ext A) (tabled R P)).Admits (s := s) g)
    {ρ : RuleWithCondition F T} (inP : ρ ∈ P) (isRule : g.rule = ρ.tableRule R)
    (onGraph : ∀ o ∈ g.selection.read.drop ρ.rule.body.read.length, s.label o ∈ G) :
    ∃ (c : Choice O S) (member : ρ.at R (c.tables.map s.label) ∈ specialized R G P),
      g = tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c ∧
      (c.tables.map s.label).length = ρ.conditions.length ∧
      (step (frames A) O (ext A) (specialized R G P)).Admits (s := s)
        (pointFiring (A := A) ρ (c.tables.map s.label) member c) ∧
      g.result (frames A) s = (pointFiring (A := A) ρ (c.tables.map s.label) member c).result (frames A) s := by
  obtain ⟨c, hc⟩ : ∃ c : Choice O S, c = ⟨g.opening, g.selection.taken,
      g.selection.read.take ρ.rule.body.read.length, g.selection.read.drop ρ.rule.body.read.length,
      g.selection.made, g.seen⟩ := ⟨_, rfl⟩
  have same : g = tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c := by
    rw [hc]
    exact eq_tableFiring g _ isRule
  have shapes := (admits_iff g).mp admitted
  have readLength : (ρ.tableRule R).body.read.length = g.selection.read.length := by
    rw [← isRule]
    exact shapes.2.1.2.2.2.1
  have tablesEq : c.tables = g.selection.read.drop ρ.rule.body.read.length := by rw [hc]
  have readEq : c.read = g.selection.read.take ρ.rule.body.read.length := by rw [hc]
  have bigEnough : ρ.rule.body.read.length ≤ g.selection.read.length := by
    rw [← readLength, RuleWithCondition.tableRule_read, List.length_append]
    omega
  have lengths : (c.tables.map s.label).length = ρ.conditions.length := by
    rw [List.length_map, tablesEq, List.length_drop, ← readLength, RuleWithCondition.tableRule_read,
      List.length_append, RuleWithCondition.calls_length]
    omega
  have onGraph' : ∀ x ∈ c.tables.map s.label, x ∈ G := by
    intro x inside
    obtain ⟨o, member, rfl⟩ := List.mem_map.mp inside
    exact onGraph o (tablesEq ▸ member)
  have fixed : ∀ x ∈ c.tables.map s.label, Fixed A x := fun x inside => fixedGraph x (onGraph' x inside)
  have member : ρ.at R (c.tables.map s.label) ∈ specialized R G P := at_mem_specialized inP lengths onGraph'
  have readSplit : ρ.rule.body.read.length = c.read.length := by
    rw [readEq, List.length_take]
    omega
  have admitted' : (step (frames A) O (ext A) (tabled R P)).Admits (s := s)
      (tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c) := same ▸ admitted
  refine ⟨c, member, same, lengths, ((tableFiring_admits_iff s ρ _ _ member c rfl lengths fixed).mp admitted').1,
    ?_⟩
  rw [same]
  exact tableFiring_result s ρ _ _ member c readSplit rfl fixed

/-- **From the graph to the table.** An admitted firing of the program at a graph, at points read from
rows present at the state and not taken, is the point firing of choices whose table firing is an
admitted firing of the program of table reads, with the same result. -/
theorem points_to_table (fixedGraph : ∀ g ∈ G, Fixed A g) (s : State (Terms T) O)
    (h : Firing O (ext A) (specialized R G P) PUnit.unit)
    (admitted : (step (frames A) O (ext A) (specialized R G P)).Admits (s := s) h)
    {ρ : RuleWithCondition F T} (inP : ρ ∈ P) {points : List T} (isRule : h.rule = ρ.at R points)
    (length : points.length = ρ.conditions.length) (onGraph : ∀ g ∈ points, g ∈ G)
    (tables : List O) (labels : tables.map s.label = points)
    (stored : ∀ o ∈ tables, o ∈ s.present ∧ o ∉ h.selection.taken) :
    ∃ (c : Choice O S) (member : ρ.at R points ∈ specialized R G P),
      c.tables = tables ∧ h = pointFiring (A := A) ρ points member c ∧
      (step (frames A) O (ext A) (tabled R P)).Admits (s := s)
        (tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c) ∧
      (tableFiring (A := A) ρ (tableRule_mem_tabled (R := R) inP) c).result (frames A) s =
        h.result (frames A) s := by
  have member : ρ.at R points ∈ specialized R G P := at_mem_specialized inP length onGraph
  obtain ⟨c, hc⟩ : ∃ c : Choice O S,
      c = ⟨h.opening, h.selection.taken, h.selection.read, tables, h.selection.made, h.seen⟩ := ⟨_, rfl⟩
  have same : h = pointFiring (A := A) ρ points member c := by
    rw [hc]
    exact eq_pointFiring h member isRule tables
  have tablesEq : c.tables = tables := by rw [hc]
  have takenEq : c.taken = h.selection.taken := by rw [hc]
  have fixed : ∀ x ∈ points, Fixed A x := fun x inside => fixedGraph x (onGraph x inside)
  have admitted' : (step (frames A) O (ext A) (specialized R G P)).Admits (s := s)
      (pointFiring (A := A) ρ points member c) := same ▸ admitted
  have readLength : ρ.rule.body.read.length = c.read.length :=
    ((admits_iff (pointFiring (A := A) ρ points member c)).mp admitted').2.1.2.2.2.1
  have labels' : c.tables.map s.label = points := by rw [tablesEq, labels]
  have stored' : ∀ o ∈ c.tables, o ∈ s.present ∧ o ∉ c.taken := by
    rw [tablesEq, takenEq]
    exact stored
  refine ⟨c, member, tablesEq, same,
    (tableFiring_admits_iff s ρ _ points member c labels' length fixed).mpr ⟨admitted', stored'⟩, ?_⟩
  rw [same]
  exact tableFiring_result s ρ _ points member c readLength labels' fixed

omit [DecidableEq O] in
/-- **The table rows are determined by the points** at a state that stores each point at most once: two
lists of present identities with the same labels, all points of the graph, are equal. -/
theorem tables_unique (s : State (Terms T) O)
    (once : ∀ o ∈ s.present, ∀ o' ∈ s.present, s.label o ∈ G → s.label o = s.label o' → o = o') :
    ∀ (tables tables' : List O), (∀ o ∈ tables, o ∈ s.present ∧ s.label o ∈ G) →
      (∀ o ∈ tables', o ∈ s.present) → tables.map s.label = tables'.map s.label → tables = tables'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, same => by simp at same
  | _ :: _, [], _, _, same => by simp at same
  | o :: os, o' :: os', each, each', same => by
      simp only [List.map_cons, List.cons.injEq] at same
      have head : o = o' := once o (each o List.mem_cons_self).1 o' (each' o' List.mem_cons_self)
        (each o List.mem_cons_self).2 same.1
      rw [head, tables_unique s once os os' (fun x inside => each x (List.mem_cons_of_mem _ inside))
        (fun x inside => each' x (List.mem_cons_of_mem _ inside)) same.2]

end Programs

#print axioms matching_points
#print axioms information_eq
#print axioms fresh_iff
#print axioms enabled_iff
#print axioms tableFiring_admits_iff
#print axioms tableFiring_result
#print axioms eq_tableFiring
#print axioms table_to_points
#print axioms points_to_table
#print axioms tables_unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
