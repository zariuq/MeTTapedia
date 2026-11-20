import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Singletons
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations

/-!
# Query-only unknowns need freshness on their scope

The caller's unknown is bound to five. A query-only rule has no raw terms, so the raw freshness
test permits both capturing that unknown and opening the query's private unknown apart from it.
An added count-one observation passes under capture and fails under the separate opening.

Putting the count pattern in the actual raw rule restores the missing freshness obligation:
the captured opening is refused, while the separate opening is fresh but its count is not entailed.
This control concerns arbitrary openings; it makes no claim against a compiler's fixed opening.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.QueryScopeControls

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled regionOf)
open PredicateQueryAdmission (RegionQuery)
open RuleSyntax
open RuleSyntax.Controls (atoms action)

abbrev Tm : PUnit.{1} → Type := fun _ => Term atoms
abbrev X := Frames.ofSubstitution action
abbrev E : Extensions.{0, 0, 0} (fun _ _ : PUnit.{1} => Subst atoms) :=
  Extensions.identity X

def x : Term atoms := .var 0
def c (number : Nat) : Term atoms := .const number

def before : State Tm Nat := ⟨PUnit.unit, [(x, c 5)], {0}, fun _ => c 5⟩

def queryOnly : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [], []⟩, []⟩
def program : Program Tm := {queryOnly}

def raw (opening : Subst atoms) : Firing Nat E program PUnit.unit :=
  ⟨queryOnly, Set.mem_singleton _, PUnit.unit, opening, ⟨[], [], []⟩, []⟩

def captured : Subst atoms := Subst.id atoms
def separate : Subst atoms := fun name => .var (name + 1)
def countermodel : Subst atoms := fun name => if name = 0 then c 5 else c 6

theorem no_raw_query_terms : queryOnly.terms = [] := rfl

theorem actual_old_unknown : before.Mentions x := by
  left
  simp [before]

theorem information (opening : Subst atoms) :
    (raw opening).information X before = [(x, c 5)] := rfl

theorem row (opening : Subst atoms) (occurrence : Nat) :
    (raw opening).row X before occurrence = c 5 := rfl

theorem countermodel_models (opening : Subst atoms) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) countermodel
      ((raw opening).information X before) := by
  rw [information]
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- Neither opening is constrained on the query-only private unknown by raw freshness. -/
theorem raw_fresh (opening : Subst atoms) : (raw opening).Fresh X before := by
  intro target old _
  refine ⟨old, ?_, ?_⟩
  · intro term _
    change action.apply old (action.apply action.identity term) = action.apply old term
    rw [action.apply_identity]
  · intro term member
    change term ∈ queryOnly.terms at member
    rw [no_raw_query_terms] at member
    cases member

theorem raw_admitted (opening : Subst atoms) :
    (step X Nat E program).Admits (s := before) (raw opening) := by
  refine (admits_iff _).mpr ⟨raw_fresh opening,
    ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨PUnit.unit, countermodel, countermodel_models opening⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [raw, Selection.commit]
  · intro check member
    simp [raw, queryOnly, Firing.opened, RuleInstance.map] at member
  · intro query member
    simp [raw, queryOnly, Firing.collectOpened] at member

/-- The actual semantic count uses the supplied opening on a query-only source variable. -/
noncomputable def addedQuery (opening : Subst atoms) :
    RegionQuery (Term atoms) (Σ _ : PUnit.{1}, Subst atoms) Nat :=
  RegionQuery.count (fun solution term =>
    @decide (action.E (action.apply solution.2 (action.apply opening x))
      (action.apply solution.2 term)) (Classical.propDecidable _)) 1

theorem query_holds_iff (opening candidate : Subst atoms) :
    (addedQuery opening).Holds ⟨PUnit.unit, candidate⟩
      ((raw opening).row X before) before.present ↔
        action.apply candidate (action.apply opening x) = c 5 := by
  classical
  change (regionOf ((raw opening).row X before) before.present
    ((addedQuery opening).region ⟨PUnit.unit, candidate⟩)).card = 1 ↔ _
  have labels : (raw opening).row X before = fun _ : Nat => c 5 := funext (row opening)
  rw [labels]
  change (regionOf (fun _ : Nat => c 5) {0}
    ((addedQuery opening).region ⟨PUnit.unit, candidate⟩)).card = 1 ↔ _
  simp only [regionOf, Finset.filter_singleton]
  have decoded : (addedQuery opening).region ⟨PUnit.unit, candidate⟩ (c 5) = true ↔
      action.apply candidate (action.apply opening x) = c 5 := by
    change decide (action.apply candidate (action.apply opening x) = c 5) = true ↔ _
    exact decide_eq_true_iff
  simp only [decoded]
  by_cases same : action.apply candidate (action.apply opening x) = c 5
  · simp [same]
  · simp [same]

theorem captured_count_asked :
    X.Entails (a := PUnit.unit) ((raw captured).information X before) fun target candidate =>
      (addedQuery captured).Holds ⟨target, candidate⟩
        ((raw captured).row X before) before.present := by
  intro target candidate models
  cases target
  apply (query_holds_iff captured candidate).mpr
  have bound := models (x, c 5) (by rw [information]; simp)
  change action.apply candidate (action.apply captured x) = c 5
  exact bound

theorem separate_count_refuted_at_actual_model :
    ¬ (addedQuery separate).Holds ⟨PUnit.unit, countermodel⟩
      ((raw separate).row X before) before.present := by
  rw [query_holds_iff]
  change c 6 ≠ c 5
  intro equal
  cases equal

theorem separate_count_not_asked :
    ¬ X.Entails (a := PUnit.unit) ((raw separate).information X before) (fun target candidate =>
      (addedQuery separate).Holds ⟨target, candidate⟩
        ((raw separate).row X before) before.present) := by
  intro asked
  exact separate_count_refuted_at_actual_model
    (asked PUnit.unit countermodel (countermodel_models separate))

/-! ## The ordinary raw count includes the private pattern in its freshness test -/

def counted : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.count x 1], []⟩, []⟩
def countedProgram : Program Tm := {counted}

def countedFiring (opening : Subst atoms) : Firing Nat E countedProgram PUnit.unit :=
  ⟨counted, Set.mem_singleton _, PUnit.unit, opening, ⟨[], [], []⟩, []⟩

theorem counted_terms : counted.terms = [x] := rfl

theorem captured_counted_not_fresh : ¬ (countedFiring captured).Fresh X before := by
  intro fresh
  obtain ⟨joint, old, rule⟩ := fresh PUnit.unit (fun _ => c 5) (fun _ => c 6)
  have keeps : joint 0 = c 5 := old x actual_old_unknown
  have aliases : joint 0 = c 6 := rule x (by change x ∈ counted.terms; rw [counted_terms]; simp)
  have impossible : c 5 = c 6 := keeps.symm.trans aliases
  cases impossible

theorem captured_counted_refused :
    ¬ (step X Nat E countedProgram).Admits (s := before) (countedFiring captured) :=
  fun admitted => captured_counted_not_fresh ((admits_iff _).mp admitted).1

theorem separate_counted_fresh : (countedFiring separate).Fresh X before := by
  intro target old rule
  refine ⟨fun name => if name = 1 then rule 0 else old name, ?_, ?_⟩
  · intro term member
    rcases member with left | right | ⟨occurrence, present, rfl⟩
    · have same : term = x := by simpa [before] using left
      subst term
      rfl
    · have same : term = c 5 := by simpa [before] using right
      subst term
      rfl
    · rfl
  · intro term member
    have same : term = x := by
      change term ∈ counted.terms at member
      rw [counted_terms] at member
      exact List.mem_singleton.mp member
    subst term
    rfl

theorem separate_counted_information :
    (countedFiring separate).information X before = [(x, c 5)] := rfl

theorem separate_counted_guard_refused :
    ¬ (step X Nat E countedProgram).Admits (s := before) (countedFiring separate) := by
  intro admitted
  have guards := ((admits_iff _).mp admitted).2.2.2.2.1
  have model : X.Models (a := PUnit.unit) (b := PUnit.unit) countermodel
      ((countedFiring separate).information X before) := by
    rw [separate_counted_information]
    exact countermodel_models separate
  have checked := guards (.count (.var 1) 1) (by
    change (Check.count (.var 1) 1 : Check (Term atoms)) ∈ [Check.count (.var 1) 1]
    exact List.mem_singleton_self _) PUnit.unit countermodel model
  change (matchesAt X countermodel ((countedFiring separate).row X before)
    before.present (.var 1)).card = 1 at checked
  have none : matchesAt X (a := PUnit.unit) (b := PUnit.unit)
      countermodel ((countedFiring separate).row X before)
      before.present (.var 1) = ∅ := by
    ext occurrence
    simp only [mem_matchesAt, Finset.notMem_empty, iff_false, not_and]
    intro _ matched
    change c 6 = c 5 at matched
    cases matched
  rw [none] at checked
  exact Nat.zero_ne_one checked

/-- The private query sees capture that the base rule's empty term list cannot detect. -/
theorem query_only_capture_boundary :
    (raw captured).Fresh X before ∧ (raw separate).Fresh X before ∧
      (step X Nat E program).Admits (s := before) (raw captured) ∧
      (step X Nat E program).Admits (s := before) (raw separate) ∧
      (X.Entails (a := PUnit.unit) ((raw captured).information X before) fun target candidate =>
        (addedQuery captured).Holds ⟨target, candidate⟩
          ((raw captured).row X before) before.present) ∧
      ¬ X.Entails (a := PUnit.unit) ((raw separate).information X before) (fun target candidate =>
        (addedQuery separate).Holds ⟨target, candidate⟩
          ((raw separate).row X before) before.present) :=
  ⟨raw_fresh captured, raw_fresh separate, raw_admitted captured, raw_admitted separate,
    captured_count_asked, separate_count_not_asked⟩

/-! ## The actual scoped profile refuses capture on its query-only unknown -/

open RuleSyntax.JointFirings
open RuleSyntax.StepWeb.ObservedBags

def queryBag (opening : Subst atoms) : Bag Nat E program PUnit.unit :=
  Bag.single (raw opening)

noncomputable def scopedQueries : ScopedQueries Tm Nat E program where
  scope _ _ := [x]
  build _ _ opened := opened.map fun pattern =>
    RegionQuery.count (fun solution term =>
      @decide (action.E (action.apply solution.2 pattern) (action.apply solution.2 term))
        (Classical.propDecidable _)) 1

theorem profile_at (opening : Subst atoms) :
    scopedQueries.profile X (P := program) (Member.ofFiring (raw opening)) =
      [addedQuery opening] := rfl

theorem singleton_own (opening : Subst atoms) :
    (queryBag opening).AdmitsOwn X before :=
  (Bag.admitsOwn_single X before (Member.ofFiring (raw opening))).mpr (raw_admitted opening)

theorem captured_not_freshOn : ¬ FreshOn X scopedQueries.scope before (queryBag captured) := by
  intro fresh
  obtain ⟨joint, old, opened⟩ := fresh PUnit.unit (fun _ => c 5) (fun _ => c 6)
  have keeps : joint 0 = c 5 := old x actual_old_unknown
  have aliases : joint 0 = c 6 := opened x (by
    change x ∈ queryOnly.terms ++ [x]
    rw [no_raw_query_terms]
    simp)
  have impossible : c 5 = c 6 := keeps.symm.trans aliases
  cases impossible

theorem separate_freshOn : FreshOn X scopedQueries.scope before (queryBag separate) := by
  intro target old rule
  obtain ⟨joint, keeps, opened⟩ := separate_counted_fresh target old rule
  refine ⟨joint, keeps, ?_⟩
  intro term member
  change term ∈ queryOnly.terms ++ [x] at member
  rw [no_raw_query_terms, List.nil_append] at member
  apply opened term
  change term ∈ counted.terms
  rw [counted_terms]
  exact member

theorem captured_observed_admitted :
    (observedOwnStep X (scopedQueries.profile X (P := program))).Admits
      (s := before) (queryBag captured) := by
  rw [observedOwnStep_admits_iff]
  refine ⟨List.cons_ne_nil _ _, singleton_own captured, ?_⟩
  intro member inside observed queried
  change member ∈ [Member.ofFiring (raw captured)] at inside
  have same := List.mem_singleton.mp inside
  subst member
  change observed ∈ [addedQuery captured] at queried
  have sameQuery := List.mem_singleton.mp queried
  subst observed
  exact captured_count_asked

theorem separate_observed_refused :
    ¬ (observedOwnStep X (scopedQueries.profile X (P := program))).Admits
      (s := before) (queryBag separate) := by
  intro admitted
  have asks := ((observedOwnStep_admits_iff X (scopedQueries.profile X) (queryBag separate)).mp
    admitted).2.2
  have actual := asks (Member.ofFiring (raw separate))
    (List.mem_singleton_self _) (addedQuery separate) (by
      change addedQuery separate ∈ [addedQuery separate]
      exact List.mem_singleton_self _)
  exact separate_count_not_asked actual

theorem captured_scoped_refused :
    ¬ (scopedStep X scopedQueries).Admits (s := before) (queryBag captured) := by
  intro admitted
  exact captured_not_freshOn ((scopedStep_admits_iff X scopedQueries (queryBag captured)).mp
    admitted).2.2.2

theorem scope_distinguishes_capture :
    (observedOwnStep X (scopedQueries.profile X (P := program))).Admits
        (s := before) (queryBag captured) ∧
      ¬ (scopedStep X scopedQueries).Admits (s := before) (queryBag captured) ∧
      FreshOn X scopedQueries.scope before (queryBag separate) ∧
      ¬ (observedOwnStep X (scopedQueries.profile X (P := program))).Admits
        (s := before) (queryBag separate) :=
  ⟨captured_observed_admitted, captured_scoped_refused, separate_freshOn,
    separate_observed_refused⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.QueryScopeControls
