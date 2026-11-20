import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimedOutcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingControls

/-!
# The two ask-timing policies differ on actual set-store steps

The self-telling rule takes row 0, tells and checks its local unknown is 5,
then makes row 10. The idle rule takes row 1 and makes row 11. Asking before
tells excludes the self-telling rule. Quantifying over that smaller match
set permits the idle step; restricting the after-tells every, maximal or
unique commit permits no step. Both readings have explicit definitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimingControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings
open MeTTaCalculus.OccurrenceCommits (Enabled)
open SetStoreSyntax (GroundRows Discipline DisciplinedStep QuantifiedAllowed QuantifiedStep QuantifiedTerminal)
open JointFirings.AskTimingControls (Tm X E v c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms action)

def selfRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[c 0], [], [(v 0, c 5)], [.equal (v 0) (c 5)], [c 10]⟩, []⟩
def idleRule : Rule Tm := ⟨PUnit.unit, ⟨[c 1], [], [], [], [c 11]⟩, []⟩
def program : Program Tm := {selfRule, idleRule}
def rows (numbers : Finset ℕ) : Finset (Term atoms) := numbers.image c
def seed : Finset (Term atoms) := rows {0, 1}
def afterIdle : Finset (Term atoms) := rows {0, 11}

def selfMember : OneMember action (Term atoms × ℕ) program :=
  ⟨selfRule, Or.inl rfl, Subst.id atoms, ⟨[(c 0, 0)], [], [(c 10, 1)]⟩, []⟩
def idleMember : OneMember action (Term atoms × ℕ) program :=
  ⟨idleRule, Or.inr rfl, Subst.id atoms, ⟨[(c 1, 0)], [], [(c 11, 1)]⟩, []⟩
def both : SetStore.Candidate program := bagOf action [selfMember, idleMember]
def idle : SetStore.Candidate program := bagOf action [idleMember]

theorem rule_cases {r : Rule Tm} (member : r ∈ program) : r = selfRule ∨ r = idleRule := member

theorem rows_ground (numbers : Finset ℕ) : GroundRows (rows numbers) := by
  intro term inside
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp inside
  trivial

/-- Ground matching determines the selected source row, independently of the local opening. -/
theorem firing_key (numbers : Finset ℕ)
    (g : Firing (Term atoms × ℕ) E program PUnit.unit)
    (lengths : g.rule.body.take.length = g.selection.taken.length ∧
      g.rule.body.read.length = g.selection.read.length)
    (enabled : Enabled (fun _ : Term atoms × ℕ => ()) (SetStore.represent (rows numbers)).present
      (g.selection.commit (T := Unit)))
    (consistent : X.Solvable (g.information X (SetStore.represent (rows numbers)))) :
    firingKey g = (selfRule, [(c 0, 0)], []) ∨
      firingKey g = (idleRule, [(c 1, 0)], []) := by
  have one : g.selection.taken.length = 1 := by
    rcases rule_cases g.member with isSelf | isIdle
    · rw [isSelf] at lengths
      exact lengths.1.symm
    · rw [isIdle] at lengths
      exact lengths.1.symm
  have noRead : g.selection.read = [] := by
    apply List.eq_nil_of_length_eq_zero
    rcases rule_cases g.member with isSelf | isIdle
    · rw [isSelf] at lengths
      exact lengths.2.symm
    · rw [isIdle] at lengths
      exact lengths.2.symm
  obtain ⟨o, selected⟩ := List.length_eq_one_iff.mp one
  have inside := enabled.taken_subset (List.mem_toFinset.mpr
    (show o ∈ g.selection.taken from by rw [selected]; exact List.mem_cons_self))
  obtain ⟨value, present, rfl⟩ := Finset.mem_image.mp inside
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp present
  obtain ⟨b, assignment, solves⟩ := consistent
  cases b
  rcases rule_cases g.member with isSelf | isIdle
  · have matched := solves (c 0, c n) (by
      unfold Firing.information Firing.opened
      rw [isSelf, selected, noRead]
      exact List.mem_cons_self)
    have equal : 0 = n := Term.const.inj matched
    exact Or.inl (by simp [firingKey, isSelf, selected, noRead, ← equal])
  · have matched := solves (c 1, c n) (by
      unfold Firing.information Firing.opened
      rw [isIdle, selected, noRead]
      exact List.mem_cons_self)
    have equal : 1 = n := Term.const.inj matched
    exact Or.inr (by simp [firingKey, isIdle, selected, noRead, ← equal])

theorem firing_ask_free (numbers : Finset ℕ)
    (g : Firing (Term atoms × ℕ) E program PUnit.unit)
    (lengths : g.rule.body.take.length = g.selection.taken.length ∧
      g.rule.body.read.length = g.selection.read.length)
    (enabled : Enabled (fun _ : Term atoms × ℕ => ()) (SetStore.represent (rows numbers)).present
      (g.selection.commit (T := Unit)))
    (consistent : X.Solvable (g.information X (SetStore.represent (rows numbers))))
    (assignment : Subst atoms) :
    X.Models (b := PUnit.unit) assignment (g.askInformation X (SetStore.represent (rows numbers))) := by
  rcases firing_key numbers g lengths enabled consistent with key | key
  · have rule : g.rule = selfRule := congrArg Prod.fst key
    have taken : g.selection.taken = [(c 0, 0)] := congrArg
      (fun k : Rule Tm × List (Term atoms × ℕ) × List (Term atoms × ℕ) => k.2.1) key
    have read : g.selection.read = [] := congrArg
      (fun k : Rule Tm × List (Term atoms × ℕ) × List (Term atoms × ℕ) => k.2.2) key
    have info : g.askInformation X (SetStore.represent (rows numbers)) = [(c 0, c 0)] := by
      unfold Firing.askInformation Firing.opened
      rw [rule, taken, read]
      rfl
    rw [info]
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · have rule : g.rule = idleRule := congrArg Prod.fst key
    have taken : g.selection.taken = [(c 1, 0)] := congrArg
      (fun k : Rule Tm × List (Term atoms × ℕ) × List (Term atoms × ℕ) => k.2.1) key
    have read : g.selection.read = [] := congrArg
      (fun k : Rule Tm × List (Term atoms × ℕ) × List (Term atoms × ℕ) => k.2.2) key
    have info : g.askInformation X (SetStore.represent (rows numbers)) = [(c 1, c 1)] := by
      unfold Firing.askInformation Firing.opened
      rw [rule, taken, read]
      rfl
    rw [info]
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl

theorem bag_ask_free (numbers : Finset ℕ) (bag : SetStore.Candidate program)
    (admitted : bag.Admits X (SetStore.represent (rows numbers))) (assignment : Subst atoms) :
    X.Models (b := PUnit.unit) assignment (bag.askInformation X (SetStore.represent (rows numbers))) := by
  intro equation inside
  rcases List.mem_append.mp inside with known | matched
  · cases known
  · obtain ⟨m, member, matched⟩ := List.mem_flatMap.mp matched
    have lengths := admitted.1.2.2.2 m member
    have free := firing_ask_free numbers m.firing ⟨lengths.1, lengths.2.1⟩
      (Bag.enabled_member admitted.2.1 member) (Bag.solvable_member X member admitted.2.2.1) assignment
    apply free equation
    change equation ∈ [] ++ m.firing.matching X _ (m.firing.opened X).take m.selection.taken ++
      m.firing.matching X _ (m.firing.opened X).read m.selection.read
    exact matched

theorem before_members_idle (numbers : Finset ℕ) (bag : SetStore.Candidate program)
    (before : bag.AdmitsBeforeTells X (SetStore.represent (rows numbers)))
    {m : Member (Term atoms × ℕ) E program bag.ext} (inside : m ∈ bag.members) : m.rule = idleRule := by
  rcases rule_cases m.member with isSelf | isIdle
  · exact False.elim (StepWeb.AskTimingControls.bag_refused bag inside (n := 5) (by decide)
      (by rw [isSelf]; exact List.mem_cons_self)
      (bag_ask_free numbers bag (Bag.admits_of_beforeTells X _ bag before)) before)
  · exact isIdle

theorem self_firing_refused (numbers : Finset ℕ)
    (g : Firing (Term atoms × ℕ) E program PUnit.unit) (isSelf : g.rule = selfRule) :
    ¬ g.AdmitsBeforeTells X (SetStore.represent (rows numbers)) := by
  intro before
  exact StepWeb.AskTimingControls.firing_refused g (n := 5) (by decide)
    (by rw [isSelf]; exact List.mem_cons_self)
    (firing_ask_free numbers g ⟨before.1.2.2.2.1, before.1.2.2.2.2.1⟩ before.2.1 before.2.2.1) before

theorem both_fresh : both.Fresh X (SetStore.represent seed) := by
  intro b g first second
  cases b
  refine ⟨first, ⟨?_, ?_⟩, ?_⟩
  · intro term mentioned
    rcases mentioned with known | known | ⟨o, present, rfl⟩
    · cases known
    · cases known
    · obtain ⟨value, inside, rfl⟩ := Finset.mem_image.mp present
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp inside
      rfl
  · intro term _
    change first.applyTerm ((Subst.id atoms).applyTerm term) = first.applyTerm term
    rw [Subst.applyTerm_id]
  · intro term inside
    change term ∈ [c 1, c 11] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · rfl
    · obtain rfl := List.mem_singleton.mp inside
      rfl

theorem both_own : both.AdmitsOwn X (SetStore.represent seed) := by
  refine ⟨⟨both_fresh, by decide +kernel, by decide +kernel, ?_⟩, ?_, ?_, ?_⟩
  · intro m inside
    change m ∈ [selfMember, idleMember] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp inside
      exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      fun query member => by cases member⟩
  · refine ⟨PUnit.unit, (fun _ => c 5), fun equation inside => ?_⟩
    change equation ∈ [(c 0, c 0), (v 0, c 5), (c 1, c 1)] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · rfl
    · rcases List.mem_cons.mp inside with rfl | inside
      · rfl
      · obtain rfl := List.mem_singleton.mp inside
        rfl
  · intro m inside b assignment solved
    change m ∈ [selfMember, idleMember] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · refine ⟨?_, fun query member => by cases member⟩
      intro check member
      obtain rfl := List.mem_singleton.mp member
      exact solved (v 0, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)
    · obtain rfl := List.mem_singleton.mp inside
      refine ⟨?_, ?_⟩
      · intro check member
        cases member
      · intro query member
        cases member

theorem both_admitted : both.Admits X (SetStore.represent seed) :=
  Bag.admits_of_admitsOwn X both_own

theorem self_admitted : selfMember.firing.Admits X (SetStore.represent seed) :=
  Bag.admits_member X (fun _ _ => ⟨Subst.id atoms⟩) both_own List.mem_cons_self

theorem idle_admitted : idleMember.firing.Admits X (SetStore.represent seed) :=
  Bag.admits_member X (fun _ _ => ⟨Subst.id atoms⟩) both_own (List.mem_cons_of_mem _ List.mem_cons_self)

theorem self_ne_idle : selfRule ≠ idleRule := by
  intro same
  have lengths := congrArg (fun r : Rule Tm => r.body.tell.length) same
  exact Nat.noConfusion lengths

theorem before_member_key (numbers : Finset ℕ) (bag : SetStore.Candidate program)
    (before : bag.AdmitsBeforeTells X (SetStore.represent (rows numbers)))
    {m : Member (Term atoms × ℕ) E program bag.ext} (inside : m ∈ bag.members) :
    m.key = idleMember.key := by
  have lengths := before.1.2.2.2 m inside
  rcases firing_key numbers m.firing ⟨lengths.1, lengths.2.1⟩
      (Bag.enabled_member before.2.1 inside) (Bag.solvable_member X inside before.2.2.1) with key | key
  · exact False.elim (self_ne_idle ((congrArg Prod.fst key).symm.trans
      (before_members_idle numbers bag before inside)))
  · exact key

/-- Equality of existing ordered presentations implies equality of existing symmetric classes. -/
theorem symmetric_of_ordered {first second : Firing (Term atoms × ℕ) E program PUnit.unit}
    (same : firingKey first = firingKey second) :
    SymmetricMatches.identity.key first = SymmetricMatches.identity.key second := by
  have rule : first.rule = second.rule := congrArg Prod.fst same
  have taken : first.selection.taken = second.selection.taken := congrArg
    (fun k : Rule Tm × List (Term atoms × ℕ) × List (Term atoms × ℕ) => k.2.1) same
  have read : first.selection.read = second.selection.read := congrArg
    (fun k : Rule Tm × List (Term atoms × ℕ) × List (Term atoms × ℕ) => k.2.2) same
  exact SymmetricMatches.key_eq_of_pair_perms first second rule
    (by rw [rule, taken]) (by rw [rule, read])

theorem idle_own_before : StepWeb.AdmitsOwnBeforeTells X (SetStore.represent seed) idle := by
  have yes : idle.Admits X (SetStore.represent seed) :=
    (Bag.admits_single X _ idleMember).mpr idle_admitted
  refine ⟨yes.1, yes.2.1, yes.2.2.1, ?_⟩
  intro m inside b assignment _
  obtain rfl := List.mem_singleton.mp inside
  refine ⟨?_, ?_⟩
  · intro check member
    cases member
  · intro query member
    cases member

theorem idle_before : idle.AdmitsBeforeTells X (SetStore.represent seed) :=
  StepWeb.beforeTells_of_ownBeforeTells idle_own_before

theorem idle_every_before :
    idle.AdmitsEveryBeforeTellsBy X (SetStore.represent seed) SymmetricMatches.identity Set.univ := by
  refine ⟨idle_own_before, fun key _ => Set.mem_univ key, List.nodup_singleton _, ?_⟩
  intro g _ before
  have lengths := before.1.2.2.2
  rcases firing_key {0, 1} g ⟨lengths.1, lengths.2.1⟩ before.2.1 before.2.2.1 with key | key
  · exact False.elim (self_firing_refused {0, 1} g (congrArg Prod.fst key) before)
  · rw [symmetric_of_ordered (show firingKey g = firingKey idleMember.firing from key)]
    exact List.mem_cons_self

theorem idle_maximal_before : StepWeb.AdmitsMaximalBeforeTells X (SetStore.represent seed) idle := by
  refine ⟨idle_before, List.nodup_singleton _, fun bag before _ _ key inside => ?_⟩
  obtain ⟨m, member, rfl⟩ := List.mem_map.mp inside
  rw [before_member_key {0, 1} bag before member]
  exact List.mem_cons_self

theorem both_distinct : both.Distinct := by
  refine List.nodup_cons.mpr ⟨fun inside => ?_, List.nodup_singleton _⟩
  exact self_ne_idle (congrArg Prod.fst (List.mem_singleton.mp inside))

theorem self_symmetric_key_differs :
    SymmetricMatches.identity.key selfMember.firing ≠ SymmetricMatches.identity.key idleMember.firing := by
  intro equal
  have taken := congrArg SymmetricMatches.taken equal
  have impossible : ([(c 0, 0)] : Multiset (Term atoms × ℕ)) = [(c 1, 0)] := taken
  exact (by decide +kernel : ([(c 0, 0)] : Multiset (Term atoms × ℕ)) ≠ [(c 1, 0)]) impossible

theorem every_restriction_refused (bag : SetStore.Candidate program)
    (before : bag.AdmitsBeforeTells X (SetStore.represent seed)) :
    ¬ bag.AdmitsEveryBy X (SetStore.represent seed) SymmetricMatches.identity Set.univ := by
  intro every
  have listed := every.2.2.2 selfMember.firing
    (Set.mem_univ (SymmetricMatches.identity.key selfMember.firing)) self_admitted
  obtain ⟨m, member, same⟩ := List.mem_map.mp listed
  exact self_symmetric_key_differs (same.symm.trans
    (symmetric_of_ordered (before_member_key {0, 1} bag before member)))

theorem maximal_restriction_refused (bag : SetStore.Candidate program)
    (before : bag.AdmitsBeforeTells X (SetStore.represent seed)) :
    ¬ bag.AdmitsMaximal X (SetStore.represent seed) := by
  intro maximal
  have listed := maximal.2.2 both both_admitted both_distinct
    (fun key inside => by
      obtain ⟨m, member, rfl⟩ := List.mem_map.mp inside
      rw [before_member_key {0, 1} bag before member]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    selfMember.key List.mem_cons_self
  obtain ⟨m, member, same⟩ := List.mem_map.mp listed
  exact self_ne_idle (congrArg Prod.fst (same.symm.trans (before_member_key {0, 1} bag before member)))

theorem restriction_has_no_step (discipline : Discipline)
    (which : discipline = .every ∨ discipline = .maximal ∨ discipline = .unique) :
    ∀ after, ¬ DisciplinedStep discipline .beforeTells program seed after := by
  rintro after ⟨bag, _, before, allowed, _⟩
  rcases which with rfl | rfl | rfl
  · exact every_restriction_refused bag before allowed
  · exact maximal_restriction_refused bag before allowed
  · exact every_restriction_refused bag before allowed.1

theorem idle_allowed (discipline : Discipline)
    (which : discipline = .every ∨ discipline = .maximal ∨ discipline = .unique) :
    QuantifiedAllowed discipline .beforeTells seed idle := by
  rcases which with rfl | rfl | rfl
  · exact idle_every_before
  · exact idle_maximal_before
  · exact ⟨idle_every_before, rfl⟩

theorem idle_result (answer : Subst atoms) : SetStore.setResult seed idle answer = afterIdle := by
  change ((rows {0, 1} \ {c 1}).image answer.applyTerm ∪ {c 11}) = rows {0, 11}
  have removed : rows {0, 1} \ {c 1} = {c 0} := by decide +kernel
  rw [removed]
  simp only [Finset.image_singleton]
  change {c 0} ∪ {c 11} = rows {0, 11}
  decide +kernel

theorem idle_changes : ¬ SetStore.SameRows seed afterIdle := by
  intro same
  have equal := SetStoreSyntax.sameRows_ground_eq (rows_ground {0, 1}) same
  have made : c 11 ∈ afterIdle := by decide +kernel
  rw [equal] at made
  exact (by decide +kernel : c 11 ∉ seed) made

/-- A changing set step under every, maximal and unique with quantifiers before tells. -/
theorem quantified_idle_step (discipline : Discipline)
    (which : discipline = .every ∨ discipline = .maximal ∨ discipline = .unique) :
    QuantifiedStep discipline .beforeTells program seed afterIdle := by
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent [(c 1, c 1)]).mpr
    ⟨Subst.id atoms, fun equation member => by obtain rfl := List.mem_singleton.mp member; rfl⟩
  exact ⟨idle, List.cons_ne_nil _ _, idle_before, idle_allowed discipline which,
    answer, accepted, (idle_result answer).symm, idle_changes⟩

/-- The new outcome is terminal because the remaining self-telling rule is refused. -/
theorem after_idle_terminal (discipline : Discipline) :
    QuantifiedTerminal discipline .beforeTells program afterIdle := by
  rintro after ⟨bag, nonempty, before, _, _⟩
  obtain ⟨m, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have key := before_member_key {0, 11} bag before member
  have selected : m.selection.taken = [(c 1, 0)] := congrArg
    (fun k : Rule Tm × List (Term atoms × ℕ) × List (Term atoms × ℕ) => k.2.1) key
  have enabled := Bag.enabled_member before.2.1 member
  have present := enabled.taken_subset (List.mem_toFinset.mpr
    (show (c 1, 0) ∈ m.selection.taken from by rw [selected]; exact List.mem_cons_self))
  exact (by decide +kernel : (c 1, 0) ∉ (SetStore.represent afterIdle).present) present

/-- The separation is about actual completed set observations, not only bag admission. -/
theorem distinct_before_tells_set_contracts (discipline : Discipline)
    (which : discipline = .every ∨ discipline = .maximal ∨ discipline = .unique) :
    (Relation.ReflTransGen (QuantifiedStep discipline .beforeTells program) seed afterIdle ∧
      QuantifiedTerminal discipline .beforeTells program afterIdle) ∧
      SetStoreSyntax.TerminalWith discipline .beforeTells program seed ∧ seed ≠ afterIdle := by
  exact ⟨⟨Relation.ReflTransGen.single (quantified_idle_step discipline which), after_idle_terminal discipline⟩,
    restriction_has_no_step discipline which, fun equal => idle_changes (equal ▸ SetStore.sameRows_refl seed)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimingControls
