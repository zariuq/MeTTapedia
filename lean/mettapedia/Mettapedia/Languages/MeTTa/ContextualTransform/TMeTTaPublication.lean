import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunInterchangeWitness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublication

/-!
# Atomic publication and independent payments

The ground program reads a witness, spends a coin and publishes a paid row.
Each selected space also consumes its current version and produces its next
version. These private version occurrences model validation at publication.
The public reading forgets version occurrences. This model covers one
logical commit, including a commit touching several physical regions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Publication
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open AnnotatedRuns

inductive Slot where
  | coin | witness | paid | version (n : Nat)
  deriving DecidableEq
abbrev Occ := Bool × Slot
abbrev A := RuleSyntax.RuleOccurrences.Closed.action Slot
abbrev label : Occ → Slot := Prod.snd
abbrev P := (firstOrder A label).toStep
abbrev T := firstOrderTransport A label

def payment (space : Bool) (epoch : Nat) : Firing Slot PUnit.{1} Occ :=
  ⟨⟨[.coin, .version epoch], [.witness], [], [], [.paid, .version (epoch+1)]⟩, [],
   ⟨[(space, .coin), (space, .version epoch)], [(space, .witness)],
     [(space, .paid), (space, .version (epoch+1))]⟩⟩

def initial : Configuration Slot Occ :=
  ⟨[], {(false, .coin), (false, .witness), (false, .version 0),
        (true, .coin), (true, .witness), (true, .version 0)}⟩

private theorem valid {s : Configuration Slot Occ} (space : Bool) (epoch : Nat)
    (consistent : A.Models PUnit.unit s.equations)
    (resources : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled
      label s.present (payment space epoch).selection.commit) :
    (payment space epoch).Valid A label s := by
  refine ⟨⟨by simp [payment], by simp [payment], rfl, rfl, rfl, resources, ⟨PUnit.unit, ?_⟩,
    fun _ member => by cases member⟩, fun _ member => by cases member⟩
  intro equation member
  simp [Selection.problem, Selection.equations, payment] at member
  rcases member with old | rfl | rfl | rfl
  · exact consistent _ old
  all_goals rfl

private theorem first (space : Bool) : P.Admits (s := initial) (payment space 0) := by
  apply valid
  · intro e he; cases he
  · cases space <;> decide

private theorem after (space : Bool) : P.Admits
    (s := P.result (payment (!space) 0) (first (!space))) (payment space 0) := by
  apply valid
  · exact (first (!space)).firing.consistent.choose_spec
  · cases space <;> decide

/-- Exchanging these two commits transports any remaining continuation. -/
noncomputable def interchange (rest : P.Run (P.result (payment true 0) (after true))) :
    T.InterchangeWitness
      (.cons (payment false 0) (first false) (.cons (payment true 0) (after true) rest))
      (.cons (payment true 0) (first true) (.cons (payment false 0) (after false)
        (T.moveRun ((firstOrder_closes A label) (first false) (first true) (after true) (after false)).some rest))) :=
  .here (T := T) (first false) (first true) (after true) (after false) _ rest

theorem stale_refused (space : Bool) :
    ¬ P.Admits (s := P.result (payment space 0) (first space)) (payment space 0) := by
  intro later
  have present := later.firing.occurrences.taken_subset
    (show (space, Slot.version 0) ∈ ((payment space 0).selection.commit (T := Slot)).taken by
      simp [payment, Selection.commit])
  cases space <;> revert present <;> decide

namespace RemoveAndCount
/-- Each selected template spends its own row and observes the number left
in the live space. The after-state of each admitted firing is the read cut. -/
abbrev action := RuleSyntax.RuleOccurrences.Closed.action Bool
abbrev start : Configuration Bool Bool := ⟨[], {false, true}⟩
def take (row : Bool) : Firing Bool PUnit.{1} Bool := ⟨⟨[row], [], [], [], []⟩, [], ⟨[row], [], []⟩⟩

private theorem allowed {c : Configuration Bool Bool} (row : Bool) (present : row ∈ c.present)
    (known : action.Models PUnit.unit c.equations) : (take row).Valid action id c := by
  refine ⟨⟨by simp [take], by simp [take], rfl, rfl, rfl, ?_, ⟨PUnit.unit, ?_⟩,
    fun _ member => by cases member⟩, fun _ member => by cases member⟩
  · constructor <;> simp_all [take, Selection.commit]
  · intro e mem
    simp [Selection.problem, Selection.equations, take] at mem
    rcases mem with old | rfl
    · exact known _ old
    · rfl

def afterOne (row : Bool) := (take row).result id start
def afterBoth (first : Bool) := (take (!first)).result id (afterOne first)

theorem both_admitted (i : Bool) :
    (take i).Valid action id start ∧ (take (!i)).Valid action id (afterOne i) := by
  have first : (take i).Valid action id start := allowed i (by cases i <;> decide) (fun _ e => nomatch e)
  exact ⟨first, allowed (!i) (by cases i <;> decide) first.firing.consistent.choose_spec⟩

def observed (first : Bool) : Multiset (Bool × Nat) :=
  {(first, (afterOne first).present.card), (!first, (afterBoth first).present.card)}

theorem effect_order_changes_bag :
    (afterBoth false).present = ∅ ∧ (afterBoth true).present = ∅ ∧ observed false ≠ observed true := by
  decide
end RemoveAndCount

section Batch
open ResourcePublication
variable {O R Term Sub : Type} [DecidableEq O] [DecidableEq R]

/-- Stage the complete replacement in private, validate every participating
region (including guard-only reads), and return one successor. Callers
retain their current root on `none`. The model's publication is indivisible. -/
def publish? {action : SubstitutionAction Term Sub} (location : O → R) (labels : O → Term) (pick : Selection O) (rule : RuleInstance Term)
    (snapshot : Configuration Term O) (live : Finset O) (guardReads : List R)
    (atPrepare atCommit : R → Nat) (prepared : R → Bool) (_admitted : pick.Valid action labels rule snapshot) : Option (Configuration Term O) :=
  let writes := destinations location (pick.taken ++ pick.made)
  let observed := writes ++ destinations location pick.read ++ guardReads
  if observed.all (fun r => atPrepare r == atCommit r) && writes.all prepared then
    some ⟨pick.problem labels rule snapshot,
      publish location (replacement (T := Term) location pick snapshot.present) writes live⟩
  else none

theorem publish_stale {action : SubstitutionAction Term Sub} {location : O → R} (labels : O → Term) (pick : Selection O) (rule : RuleInstance Term)
    (snapshot : Configuration Term O) (live : Finset O) (guards : List R) (old current : R → Nat) (prepared : R → Bool)
    {r : R} (observed : r ∈ destinations location (pick.taken ++ pick.made) ++
      destinations location pick.read ++ guards) (stale : old r ≠ current r)
    (admitted : pick.Valid action labels rule snapshot) :
    publish? location labels pick rule snapshot live guards old current prepared admitted = none := by
  simp only [publish?, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  exact if_neg (fun valid => stale (valid.1 r observed))

theorem publish_prepare_failure {action : SubstitutionAction Term Sub} {location : O → R} (labels : O → Term) (pick : Selection O)
    (rule : RuleInstance Term) (snapshot : Configuration Term O) (live : Finset O) (guards : List R)
    (old current : R → Nat) (prepared : R → Bool) {r : R}
    (written : r ∈ destinations location (pick.taken ++ pick.made)) (failed : prepared r = false)
    (admitted : pick.Valid action labels rule snapshot) :
    publish? location labels pick rule snapshot live guards old current prepared admitted = none := by
  simp only [publish?, Bool.and_eq_true, List.all_eq_true]
  exact if_neg (fun valid => Bool.noConfusion (failed.symm.trans (valid.2 r written)))

/-- On an admitted frozen snapshot successful installation computes exactly
the selected logical successor, including its residual equations. -/
theorem publication_exact (action : SubstitutionAction Term Sub) (labels : O → Term)
    (location : O → R) (pick : Selection O) (rule : RuleInstance Term) (snapshot : Configuration Term O)
    (v : R → Nat) (guards : List R) (admitted : pick.Valid action labels rule snapshot) :
    publish? location labels pick rule snapshot snapshot.present guards v v (fun _ => true) admitted =
      some (pick.result labels rule snapshot) := by
  simp [publish?, List.all_eq_true]
  rw [(valid_publication_result action labels location pick rule snapshot admitted).2]
  rfl

/-- A successful commit retains changes in unrelated physical destinations
that arrived after private preparation. -/
theorem outside_preserved {action : SubstitutionAction Term Sub} (location : O → R) (labels : O → Term) (pick : Selection O) (rule : RuleInstance Term)
    (snapshot next : Configuration Term O) (live : Finset O) (guards : List R) (old current : R → Nat)
    (prepared : R → Bool) {o : O} (outside : location o ∉ destinations location (pick.taken ++ pick.made))
    (admitted : pick.Valid action labels rule snapshot)
    (committed : publish? location labels pick rule snapshot live guards old current prepared admitted = some next) :
    o ∈ next.present ↔ o ∈ live := by
  simp only [publish?] at committed
  split at committed
  · cases committed
    exact (publication_membership location _ _ _ live
      (fun r _ => replacement_eq_source_slice (T := Term) location r pick snapshot.present) o).trans
        (by rw [if_neg outside])
  · contradiction

/-- Once validation has established that written fibres still match the
snapshot, a successful batch also agrees with firing against the live
resource store. The branch's own equations remain those of its snapshot. -/
theorem live_successor {action : SubstitutionAction Term Sub} (location : O → R) (labels : O → Term)
    (pick : Selection O) (rule : RuleInstance Term) (snapshot next : Configuration Term O) (live : Finset O)
    (guards : List R) (old current : R → Nat) (prepared : R → Bool)
    (admitted : pick.Valid action labels rule snapshot)
    (unchanged : ∀ r ∈ destinations location (pick.taken ++ pick.made),
      slice location r snapshot.present = slice location r live)
    (committed : publish? location labels pick rule snapshot live guards old current prepared admitted = some next) :
    next = pick.result labels rule {snapshot with present := live} := by
  simp only [publish?] at committed
  split at committed
  · cases committed
    congr 1
    ext o
    rw [publication_membership location _ _ _ live
      (fun r _ => replacement_eq_source_slice (T := Term) location r pick snapshot.present)]
    by_cases covered : location o ∈ destinations location (pick.taken ++ pick.made)
    · rw [if_pos covered]
      have agree := Finset.ext_iff.mp (unchanged (location o) covered) o
      simp only [mem_slice, and_true, eq_self] at agree
      simp [Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire, agree]
    · rw [if_neg covered]
      have untouched : o ∉ pick.taken ∧ o ∉ pick.made := by
        constructor <;> intro h <;> apply covered <;> apply (mem_destinations _ _ _).mpr
        · exact ⟨o, List.mem_append_left _ h, rfl⟩
        · exact ⟨o, List.mem_append_right _ h, rfl⟩
      simp [Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire,
        Selection.commit, untouched.1, untouched.2]
  · contradiction

/-- Successful version validation is a firing at the live cut. The guard
support covers possible new matches as well as the rows present at staging. -/
theorem committed_firing_is_live (action : SubstitutionAction Term Sub) (labels : O → Term)
    (location : O → R) (firing : Firing Term Sub O)
    (snapshot next : Configuration Term O) (live : Finset O) (guards : List R)
    (old current : R → Nat) (prepared : R → Bool)
    (valid : firing.Valid action labels snapshot)
    (versionSound : ∀ region, old region = current region →
      slice location region snapshot.present = slice location region live)
    (checks : ∀ pattern, (∃ quantifier, Check.predicate quantifier pattern ∈ firing.rule.checks) ∨
        (∃ number, Check.count pattern number ∈ firing.rule.checks) →
      ∀ σ o, action.E (action.apply σ pattern) (action.apply σ (labels o)) → location o ∈ guards)
    (queries : ∀ query ∈ firing.queries, ∀ σ o, query.region σ (labels o) = true → location o ∈ guards)
    (success : publish? location labels firing.selection firing.rule snapshot live guards
      old current prepared valid.firing = some next) :
    firing.Valid action labels {snapshot with present := live} ∧
      next = firing.result labels {snapshot with present := live} := by
  classical
  let picked := firing.selection
  let written := destinations location (picked.taken ++ picked.made)
  let borrowed := destinations location picked.read
  have now : ∀ r ∈ written ++ borrowed ++ guards, old r = current r := by
    simp only [publish?] at success
    split at success
    · rename_i validated
      exact fun r hr => beq_iff_eq.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp validated).1 r hr)
    · contradiction
  have agrees {o : O} (covered : location o ∈ written ++ borrowed ++ guards) :
      o ∈ snapshot.present ↔ o ∈ live := by
    have same := Finset.ext_iff.mp (versionSound _ (now _ covered)) o
    simpa only [mem_slice, and_true, eq_self] using same
  have fromWrite {o : O} (member : o ∈ picked.taken ++ picked.made) :
      o ∈ snapshot.present ↔ o ∈ live :=
    agrees (List.mem_append_left _ (List.mem_append_left _ ((mem_destinations _ _ _).mpr ⟨o, member, rfl⟩)))
  have fromRead {o : O} (member : o ∈ picked.read) :
      o ∈ snapshot.present ↔ o ∈ live :=
    agrees (List.mem_append_left _ (List.mem_append_right _ ((mem_destinations _ _ _).mpr ⟨o, member, rfl⟩)))
  have fromGuard {o : O} (member : location o ∈ guards) : o ∈ snapshot.present ↔ o ∈ live :=
    agrees (List.mem_append_right _ member)
  obtain ⟨takeDistinct, madeDistinct, takeLength, readLength, outputs, enabled, consistent, checksBefore⟩ := valid.firing
  have actual : picked.Valid action labels firing.rule {snapshot with present := live} := by
    refine ⟨takeDistinct, madeDistinct, takeLength, readLength, outputs, ?_, consistent, ?_⟩
    · refine ⟨?_, ?_, enabled.apart, Finset.disjoint_left.mpr ?_, ?_⟩
      · intro o taken
        exact (fromWrite (List.mem_append_left _ (List.mem_toFinset.mp taken))).mp
          (enabled.taken_subset taken)
      · intro o read
        exact (fromRead (List.mem_toFinset.mp read)).mp (enabled.kept_subset read)
      · intro o made present
        exact Finset.disjoint_left.mp enabled.fresh made
          ((fromWrite (List.mem_append_right _ (List.mem_toFinset.mp made))).mpr present)
      · intro query member
        simp [Selection.commit] at member
    · intro check member σ solves
      have before := checksBefore check member σ solves
      cases check with
      | equal => exact before
      | predicate quantifier pattern =>
        cases quantifier with
        | any =>
          obtain ⟨o, present, fits⟩ := before
          exact ⟨o, (fromGuard (checks pattern (Or.inl ⟨_, member⟩) σ o fits)).mp present, fits⟩
        | none =>
          intro o present fits
          exact before o ((fromGuard (checks pattern (Or.inl ⟨_, member⟩) σ o fits)).mpr present) fits
      | count pattern number =>
        have same : Check.«matches» action σ labels live pattern = Check.«matches» action σ labels snapshot.present pattern := by
          ext o
          simp only [Check.«matches», Finset.mem_filter]
          exact ⟨fun ⟨present, fits⟩ =>
            ⟨(fromGuard (checks pattern (Or.inr ⟨number, member⟩) σ o fits)).mpr present, fits⟩,
            fun ⟨present, fits⟩ =>
              ⟨(fromGuard (checks pattern (Or.inr ⟨number, member⟩) σ o fits)).mp present, fits⟩⟩
        change (Check.«matches» action σ labels live pattern).card = number
        rw [same]
        exact before
  refine ⟨⟨actual, ?_⟩, live_successor (location := location) labels _ _ snapshot next live guards old current
    prepared valid.firing (fun r hr => versionSound r (now r (List.mem_append_left _ (List.mem_append_left _ hr)))) success⟩
  intro query member σ solved
  have same : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.regionOf labels live (query.region σ) =
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.regionOf labels snapshot.present (query.region σ) := by
    ext o
    simp only [Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.regionOf, Finset.mem_filter]
    exact ⟨fun ⟨present, fits⟩ => ⟨(fromGuard (queries query member σ o fits)).mpr present, fits⟩,
      fun ⟨present, fits⟩ => ⟨(fromGuard (queries query member σ o fits)).mp present, fits⟩⟩
  change query.accepts σ (Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.regionOf labels live (query.region σ))
  rw [same]
  exact valid.observations query member σ solved

end Batch
end Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Publication
