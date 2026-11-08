import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison

/-!
# `match` as single-read firings of the transform candidate

`(match space pattern template)` returns one answer for every occurrence of
the space whose atom is an instance of `pattern`, together with the binding
of the pattern's variables. The reference below states this on a bag of
ground atoms. It does not mention the occurrence calculus.

The encoding uses one ordinary rule instance per answer: it reads one
occurrence through `pattern` and produces `template`. The produced label is
the unresolved template; an answer is read by the client in a solution of the
result store. The encoding has no answer port.

* `valid_iff`: a single-read selection is valid exactly when the read
  occurrence is present, the output occurrence is fresh and labelled by the
  template, and the store remains consistent with the read equation.
* `consistent_iff_matches`: when the pattern's variables are fresh for the
  store and the label is ground, that consistency is exactly matching.
* `resolved_answer`: every solution of the result store gives the reference
  answer and the reference binding of every pattern variable.
* `encodedAnswers_eq_reference`: the answers of all valid single-read
  selections at one store, indexed by the read occurrence, are the reference
  bag, with multiplicity. Two occurrences with equal labels give two answers.
* `probe_answers`: on the space `(p 1) (p 1) (p 2)` with `(p $x)` and
  `(r $x)` the encoded bag is `(r 1) (r 1) (r 2)`.

The bag is an observation over the set of valid selections at one store. It
is not itself a firing: `MeTTaOperationsCollapse` proves that validity of one
firing cannot certify that a set of reads is complete.

Stored atoms with variables need per-use opening. `shared_variable_conflates_queries`
shows that reading a stored `(q $z)` whose variable is live binds that
variable for every later reader: a second query `(q 7)` is refused after
`(q 5)`. Hyperon Experimental answers both, as does a fresh copy per use.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsMatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)

/-! ## The reference semantics -/

/-- A pattern matches a value when one substitution instantiates it to the value. -/
def Matches (pattern value : Atom) : Prop := ∃ σ : Subst, subst σ pattern = value

/-- Every variable of the template occurs in the pattern. -/
def Covered (pattern template : Atom) : Prop := ∀ v ∈ vars template, v ∈ vars pattern

/-- A chosen matching substitution, restricted to the pattern's variables.
Any other matching substitution agrees with it on those variables; template
variables outside the pattern stay open, as in Hyperon Experimental. -/
noncomputable def matcher (pattern value : Atom) : Subst := by
  classical
  exact if h : Matches pattern value then restrict (Classical.choose h) (vars pattern) else empty

theorem matcher_spec {pattern value : Atom} (h : Matches pattern value) :
    subst (matcher pattern value) pattern = value := by
  classical
  unfold matcher
  rw [dif_pos h, subst_restrict_vars]
  exact Classical.choose_spec h

theorem matcher_outside {pattern value : Atom} {v : Var} (outside : v ∉ vars pattern) :
    matcher pattern value v = none := by
  classical
  unfold matcher
  split_ifs <;> simp [restrict, outside, empty]

/-- The answer contributed by one matching value. -/
noncomputable def answer (pattern template value : Atom) : Atom :=
  subst (matcher pattern value) template

/-- The returned binding: the value of every pattern variable, and nothing else. -/
noncomputable def binding (pattern value : Atom) (v : Var) : Option Atom := by
  classical
  exact if v ∈ vars pattern then some (subst (matcher pattern value) (.var v)) else none

/-- The reference answer bag of `(match space pattern template)`. -/
noncomputable def referenceAnswers (space : Multiset Atom) (pattern template : Atom) : Multiset Atom := by
  classical
  exact (space.filter (Matches pattern)).map (answer pattern template)

/-- The reference bag of returned bindings, aligned with the answers. -/
noncomputable def referenceBindings (space : Multiset Atom) (pattern : Atom) :
    Multiset (Var → Option Atom) := by
  classical
  exact (space.filter (Matches pattern)).map (binding pattern)

/-- Two substitutions instantiating a pattern to one value agree on its variables. -/
theorem agree_on_pattern {pattern value : Atom} {σ τ : Subst}
    (first : subst σ pattern = value) (second : subst τ pattern = value) :
    ∀ v ∈ vars pattern, subst σ (.var v) = subst τ (.var v) :=
  (subst_eq_iff_on_vars σ τ pattern).mp (first.trans second.symm)

/-- Any matching substitution computes the reference answer. -/
theorem answer_eq_of_solution {pattern template value : Atom} (covered : Covered pattern template)
    {τ : Subst} (solves : subst τ pattern = value) :
    answer pattern template value = subst τ template :=
  subst_template_eq_of_pattern_eq _ _ pattern template covered
    ((matcher_spec ⟨τ, solves⟩).trans solves.symm)

/-! ## The encoding -/

/-- One answer: read one occurrence through the pattern and produce the template. -/
def rule (pattern template : Atom) : RuleInstance Atom := ⟨[], [pattern], [], [], [template]⟩

/-- The selection that reads `read` and allocates `made` for the answer. -/
def selection {O : Type*} (read made : O) : Selection O := ⟨[], [read], [made]⟩

variable {O : Type*} [DecidableEq O]

omit [DecidableEq O] in
theorem problem_eq (label : O → Atom) (pattern template : Atom) (before : Configuration Atom O)
    (o m : O) :
    (selection o m).problem label (rule pattern template) before =
      before.equations ++ [(pattern, label o)] := by
  simp [Selection.problem, Selection.equations, selection, rule]

theorem valid_iff (label : O → Atom) (pattern template : Atom) (before : Configuration Atom O)
    (o m : O) :
    (selection o m).Valid atomAction label (rule pattern template) before ↔
      o ∈ before.present ∧ m ∉ before.present ∧ label m = template ∧
        atomAction.Consistent (before.equations ++ [(pattern, label o)]) := by
  constructor
  · intro valid
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact valid.occurrences.kept_subset (by simp [Selection.commit, selection])
    · intro member
      exact Finset.disjoint_left.mp valid.occurrences.fresh
        (by simp [Selection.commit, selection]) member
    · simpa [selection, rule] using valid.outputs
    · simpa [problem_eq] using valid.consistent
  · rintro ⟨present, fresh, labelled, consistent⟩
    refine ⟨by simp [selection], by simp [selection], rfl, rfl,
      by simp [selection, rule, labelled], ?_, ?_, ?_⟩
    · refine ⟨by simp [Selection.commit, selection], by simp [Selection.commit, selection, present],
        by simp [Selection.commit, selection], by simp [Selection.commit, selection, fresh], ?_⟩
      intro query member
      simp [Selection.commit] at member
    · rw [problem_eq]
      exact consistent
    · intro check member
      simp [rule] at member

/-- The variables of an equation store. -/
def storeVars (store : EquationStore Atom) : List Var :=
  store.flatMap fun e => vars e.1 ++ vars e.2

theorem mem_storeVars {store : EquationStore Atom} {v : Var} :
    v ∈ storeVars store ↔ ∃ e ∈ store, v ∈ vars e.1 ∨ v ∈ vars e.2 := by
  simp [storeVars]

/-- Solutions glue across disjoint variables: a solution of a store and a
matching substitution of a fresh pattern give one solution of both. -/
theorem consistent_iff_matches (store : EquationStore Atom) (pattern value : Atom)
    (fresh : ∀ v ∈ vars pattern, v ∉ storeVars store) (ground : vars value = [])
    (base : atomAction.Consistent store) :
    atomAction.Consistent (store ++ [(pattern, value)]) ↔ Matches pattern value := by
  classical
  constructor
  · rintro ⟨σ, solved⟩
    have equation := solved (pattern, value) (by simp)
    change subst σ pattern = subst σ value at equation
    exact ⟨σ, equation.trans (subst_of_vars_eq_nil σ value ground)⟩
  · rintro ⟨τ, matched⟩
    obtain ⟨σ, solved⟩ := base
    let glued : Subst := fun v => if v ∈ vars pattern then τ v else σ v
    refine ⟨glued, ?_⟩
    intro e member
    rcases List.mem_append.mp member with old | new
    · have equation := solved e old
      change subst σ e.1 = subst σ e.2 at equation
      change subst glued e.1 = subst glued e.2
      have outside : ∀ term, (∀ v ∈ vars term, v ∈ storeVars store) →
          subst glued term = subst σ term := by
        intro term inside
        apply subst_congr_on_vars
        intro v member
        have notPattern : v ∉ vars pattern := fun inPattern =>
          fresh v inPattern (inside v member)
        simp [glued, notPattern]
      rw [outside e.1 (fun v member => mem_storeVars.mpr ⟨e, old, .inl member⟩),
        outside e.2 (fun v member => mem_storeVars.mpr ⟨e, old, .inr member⟩)]
      exact equation
    · obtain rfl := List.mem_singleton.mp new
      change subst glued pattern = subst glued value
      rw [subst_of_vars_eq_nil glued value ground, ← matched]
      apply subst_congr_on_vars
      intro v member
      simp [glued, member]

/-- Every solution of a valid answer's store gives the reference answer and
the reference binding of each pattern variable. -/
theorem resolved_answer {store : EquationStore Atom} {pattern template value : Atom}
    (ground : vars value = []) (covered : Covered pattern template) {σ : Subst}
    (solved : atomAction.Models σ (store ++ [(pattern, value)])) :
    subst σ template = answer pattern template value ∧
      ∀ v ∈ vars pattern, subst σ (.var v) = subst (matcher pattern value) (.var v) := by
  have equation := solved (pattern, value) (by simp)
  change subst σ pattern = subst σ value at equation
  have matched : subst σ pattern = value := equation.trans (subst_of_vars_eq_nil σ value ground)
  exact ⟨(answer_eq_of_solution covered matched).symm,
    agree_on_pattern matched (matcher_spec ⟨σ, matched⟩)⟩

/-- The occurrences whose single-read answer firing is valid at `before`. -/
noncomputable def answerOccurrences (label : O → Atom) (pattern template : Atom)
    (before : Configuration Atom O) : Finset O := by
  classical
  exact before.present.filter fun o =>
    ∃ m, (selection o m).Valid atomAction label (rule pattern template) before

/-- The encoded answer bag: one answer per valid read, indexed by the occurrence read. -/
noncomputable def encodedAnswers (label : O → Atom) (pattern template : Atom)
    (before : Configuration Atom O) : Multiset Atom :=
  (answerOccurrences label pattern template before).val.map fun o => answer pattern template (label o)

/-- The encoded binding bag, aligned with the answers. -/
noncomputable def encodedBindings (label : O → Atom) (pattern template : Atom)
    (before : Configuration Atom O) : Multiset (Var → Option Atom) :=
  (answerOccurrences label pattern template before).val.map fun o => binding pattern (label o)

/-- The hypotheses of the reference comparison: ground stored labels, a pattern
private to this use, a consistent store, and an available output occurrence. -/
structure Prepared (label : O → Atom) (pattern template : Atom) (before : Configuration Atom O) : Prop where
  supply : ∃ m, m ∉ before.present ∧ label m = template
  fresh : ∀ v ∈ vars pattern, v ∉ storeVars before.equations
  ground : ∀ o ∈ before.present, vars (label o) = []
  base : atomAction.Consistent before.equations

theorem mem_answerOccurrences_iff {label : O → Atom} {pattern template : Atom}
    {before : Configuration Atom O} (prepared : Prepared label pattern template before) (o : O) :
    o ∈ answerOccurrences label pattern template before ↔
      o ∈ before.present ∧ Matches pattern (label o) := by
  classical
  unfold answerOccurrences
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨present, m, valid⟩
    obtain ⟨_, _, _, consistent⟩ := (valid_iff label pattern template before o m).mp valid
    exact ⟨present, (consistent_iff_matches _ _ _ prepared.fresh (prepared.ground o present)
      prepared.base).mp consistent⟩
  · rintro ⟨present, matched⟩
    obtain ⟨m, notPresent, labelled⟩ := prepared.supply
    exact ⟨present, m, (valid_iff label pattern template before o m).mpr ⟨present, notPresent, labelled,
      (consistent_iff_matches _ _ _ prepared.fresh (prepared.ground o present) prepared.base).mpr matched⟩⟩

theorem answerOccurrences_eq {label : O → Atom} {pattern template : Atom}
    {before : Configuration Atom O} (prepared : Prepared label pattern template before) :
    answerOccurrences label pattern template before =
      by classical exact before.present.filter fun o => Matches pattern (label o) := by
  classical
  ext o
  rw [mem_answerOccurrences_iff prepared, Finset.mem_filter]

/-- **Adequacy of `match`.** The answers of all valid single-read firings are
the reference answer bag of the stored labels, with multiplicity. -/
theorem encodedAnswers_eq_reference {label : O → Atom} {pattern template : Atom}
    {before : Configuration Atom O} (prepared : Prepared label pattern template before) :
    encodedAnswers label pattern template before =
      referenceAnswers (before.present.val.map label) pattern template := by
  classical
  unfold encodedAnswers referenceAnswers
  rw [answerOccurrences_eq prepared, Finset.filter_val, Multiset.filter_map, Multiset.map_map]
  rfl

/-- The returned bindings agree with the reference bindings, with multiplicity. -/
theorem encodedBindings_eq_reference {label : O → Atom} {pattern template : Atom}
    {before : Configuration Atom O} (prepared : Prepared label pattern template before) :
    encodedBindings label pattern template before =
      referenceBindings (before.present.val.map label) pattern := by
  classical
  unfold encodedBindings referenceBindings
  rw [answerOccurrences_eq prepared, Finset.filter_val, Multiset.filter_map, Multiset.map_map]
  rfl

/-- Every solution of a valid answer firing's result reads the reference
answer from the produced occurrence. -/
theorem valid_answer_resolves {label : O → Atom} {pattern template : Atom}
    {before : Configuration Atom O} (covered : Covered pattern template)
    (ground : ∀ o ∈ before.present, vars (label o) = []) {o m : O}
    (valid : (selection o m).Valid atomAction label (rule pattern template) before) {σ : Subst}
    (solved : atomAction.Models σ ((selection o m).result label (rule pattern template) before).equations) :
    subst σ (label m) = answer pattern template (label o) := by
  obtain ⟨present, _, labelled, _⟩ := (valid_iff label pattern template before o m).mp valid
  have models : atomAction.Models σ (before.equations ++ [(pattern, label o)]) := by
    simpa [Selection.result, problem_eq] using solved
  rw [labelled]
  exact (resolved_answer (ground o present) covered models).1

/-! ## The probe space `(p 1) (p 1) (p 2)` -/

namespace Probe

def one : Atom := .symbol "1"
def two : Atom := .symbol "2"
def p (value : Atom) : Atom := .expression [.symbol "p", value]
def r (value : Atom) : Atom := .expression [.symbol "r", value]
def pattern : Atom := p (.var "x")
def template : Atom := r (.var "x")

def label (n : Nat) : Atom :=
  if n = 0 then p one else if n = 1 then p one else if n = 2 then p two else template

def before : Configuration Atom Nat := ⟨[], {0, 1, 2}⟩

theorem prepared : Prepared label pattern template before where
  supply := ⟨3, by decide, rfl⟩
  fresh := by intro v _; simp [before, storeVars]
  ground := by
    intro o member
    simp only [before, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> rfl
  base := ⟨empty, by intro e member; simp [before] at member⟩

theorem covered : Covered pattern template := by
  intro v member
  simpa [pattern, template, p, r, vars, vars.varsList] using member

theorem answer_value (value : Atom) :
    answer pattern template (p value) = r value := by
  have solves : subst (Insertion.single "x" value) pattern = p value := by
    simp [pattern, p, subst, subst.substList, Insertion.single]
  rw [answer_eq_of_solution covered solves]
  simp [template, r, subst, subst.substList, Insertion.single]

theorem matches_value (value : Atom) : Matches pattern (p value) :=
  ⟨Insertion.single "x" value, by simp [pattern, p, subst, subst.substList, Insertion.single]⟩

theorem stored_labels : before.present.val.map label = {p one, p one, p two} := by
  decide

/-- Hyperon Experimental, PeTTa and the CeTTa draft print `(r 1) (r 1) (r 2)`
for this space; the encoded bag is the same. -/
theorem probe_answers : encodedAnswers label pattern template before = {r one, r one, r two} := by
  rw [encodedAnswers_eq_reference prepared, stored_labels]
  classical
  unfold referenceAnswers
  rw [Multiset.filter_eq_self.mpr]
  · simp [answer_value one, answer_value two]
  · intro value member
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> exact matches_value _

/-- Equal labels at distinct occurrences are distinct answers. -/
theorem probe_multiplicity : Multiset.count (r one) (encodedAnswers label pattern template before) = 2 := by
  rw [probe_answers]
  decide

def seen (value : Atom) : Atom := .expression [.symbol "seen", value, .var "z"]

/-- A template variable outside the pattern stays open in the answer:
Hyperon Experimental prints `(seen 1 $z)` for `(match &self (p $x) (seen $x $z))`. -/
theorem open_template_variable_stays_open :
    answer pattern (seen (.var "x")) (p one) = seen one := by
  have spec := matcher_spec (matches_value one)
  have outside : matcher pattern (p one) "z" = none :=
    matcher_outside (by simp [pattern, p, vars, vars.varsList])
  unfold answer
  generalize matcher pattern (p one) = m at spec outside ⊢
  simp only [pattern, p, subst, subst.substList, Atom.expression.injEq, List.cons.injEq,
    true_and, and_true] at spec
  simp [seen, subst, subst.substList, outside, spec]

end Probe

/-! ## A stored variable must be opened per use -/

namespace SharedStorage

def q (value : Atom) : Atom := .expression [.symbol "q", value]
def five : Atom := .symbol "5"
def seven : Atom := .symbol "7"
def yes : Atom := .symbol "yes"

/-- Occurrence 0 stores `(q $z)` with a shared `z`; outputs are labelled `yes`. -/
def label (n : Nat) : Atom := if n = 0 then q (.var "z") else yes

def before : Configuration Atom Nat := ⟨[], {0}⟩

theorem first_query_valid :
    (selection 0 1).Valid atomAction label (rule (q five) yes) before := by
  refine (valid_iff label (q five) yes before 0 1).mpr ⟨by decide, by decide, rfl, ?_⟩
  refine ⟨Insertion.single "z" five, ?_⟩
  intro e member
  simp only [before, List.nil_append, List.mem_singleton] at member
  subst member
  change subst _ (q five) = subst _ (q (.var "z"))
  simp [q, five, subst, subst.substList, Insertion.single]

/-- After the first query, the shared variable is bound for every reader. -/
theorem shared_variable_conflates_queries :
    ¬ (selection 0 2).Valid atomAction label (rule (q seven) yes)
      ((selection 0 1).result label (rule (q five) yes) before) := by
  intro valid
  obtain ⟨_, _, _, ⟨σ, solved⟩⟩ := (valid_iff label (q seven) yes _ 0 2).mp valid
  have first := solved (q five, q (.var "z")) (by simp [Selection.result, problem_eq, before, label])
  have second := solved (q seven, q (.var "z")) (by simp [Selection.result, problem_eq, before, label])
  change subst σ (q five) = subst σ (q (.var "z")) at first
  change subst σ (q seven) = subst σ (q (.var "z")) at second
  have same := first.trans second.symm
  simp [q, five, seven, subst, subst.substList] at same

/-- A fresh copy per use answers both queries, as Hyperon Experimental does. -/
def openedLabel (n : Nat) : Atom :=
  if n = 0 then q (.var "z") else if n = 1 then q (.var "z'") else yes

def openedBefore : Configuration Atom Nat := ⟨[], {0, 1}⟩

theorem opened_copies_answer_both :
    (selection 0 2).Valid atomAction openedLabel (rule (q five) yes) openedBefore ∧
      (selection 1 3).Valid atomAction openedLabel (rule (q seven) yes)
        ((selection 0 2).result openedLabel (rule (q five) yes) openedBefore) := by
  constructor
  · refine (valid_iff openedLabel (q five) yes openedBefore 0 2).mpr ⟨by decide, by decide, rfl, ?_⟩
    refine ⟨Insertion.single "z" five, ?_⟩
    intro e member
    simp only [openedBefore, List.nil_append, List.mem_singleton] at member
    subst member
    change subst _ (q five) = subst _ (q (.var "z"))
    simp [q, five, subst, subst.substList, Insertion.single]
  · refine (valid_iff openedLabel (q seven) yes _ 1 3).mpr ⟨?_, ?_, rfl, ?_⟩
    · simp [Selection.result, fire, Selection.commit, selection, openedBefore]
    · simp [Selection.result, fire, Selection.commit, selection, openedBefore]
    · refine ⟨fun v => if v = "z" then some five else if v = "z'" then some seven else none, ?_⟩
      intro e member
      simp [Selection.result, problem_eq, openedBefore] at member
      rcases member with rfl | rfl
      · change subst _ (q five) = subst _ (openedLabel 0)
        simp [q, five, seven, subst, subst.substList, openedLabel]
      · change subst _ (q seven) = subst _ (openedLabel 1)
        simp [q, five, seven, subst, subst.substList, openedLabel]

end SharedStorage

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsMatch
