import Mettapedia.Machines.TIsa.Derivation.SymbolicBatchAllocation
import Mettapedia.Machines.TIsa.Derivation.SymbolicComplete
import Mettapedia.Machines.TIsa.Derivation.SymbolicJointReopening
import Mettapedia.Machines.TIsa.Derivation.SerialReopening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Maximal
import Mathlib.Data.List.Sublists

/-!
# Finite symbolic population search

Search proposes rule and port geometry before checking any guard.
In particular it does not discard a member merely because the rest
of its batch is needed to establish one of its guards. Each fixed
batch width is a finite search. Maximality only needs distinct
match keys, which also gives a finite bound on the width.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicScheduleSearch

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open RuleSyntax (Program)
open RuleSyntax.OneFrame (Terms ext)
open RuleSyntax.JointFirings (Bag OneMember bagOf firingKey)
open RuleSyntax.JointFirings.SymmetricMatches (WordResultModel)
open SymbolicFiring (act LiveWorld Rules portChoices portChoices_iff tuples mem_tuples)
open SymbolicBatch (Request requestBatch)

variable {signature : LPSignature} [DecidableEq signature.vars]

private abbrev A := FirstOrder.action signature
abbrev Member (signature : LPSignature) (program : Program (Terms (Term signature))) :=
  OneMember (A (signature := signature)) ℕ program

private abbrev Ready {program : Program (Terms (Term signature))} (m : Member signature program) :=
  m.rule.body.take.length = m.selection.taken.length ∧
  m.rule.body.read.length = m.selection.read.length ∧
  m.rule.body.produce.length = m.selection.made.length ∧
  m.rule.collect.length = m.seen.length

private def requestOf {program : Program (Terms (Term signature))} (m : Member signature program)
    (ready : Ready m) : Request program :=
  ⟨m.rule, m.member, m.selection.taken, m.selection.read, m.seen, ready.1, ready.2.1, ready.2.2.2⟩

private def requestsOf {program : Program (Terms (Term signature))} :
    (members : List (Member signature program)) → (∀ m ∈ members, Ready m) → List (Request program)
  | [], _ => []
  | first :: tail, ready =>
    requestOf first (ready first List.mem_cons_self) ::
      requestsOf tail (fun m mem => ready m (List.mem_cons_of_mem _ mem))

variable (before : LiveWorld signature) (slots : signature.vars ≃ ℕ)

private theorem requests_align {program : Program (Terms (Term signature))}
    (members : List (Member signature program)) (ready : ∀ m ∈ members, Ready m) (index offset : ℕ) :
    List.Forall₂ (SymbolicJointReopening.Same before.state) members
      ((SymbolicBatch.allocate before slots (requestsOf members ready) index offset).map Prod.snd) := by
  induction members generalizing index offset with
  | nil => exact .nil
  | cons first rest ih => exact .cons ⟨rfl, rfl, rfl, rfl⟩ (ih _ _ _)

omit [DecidableEq signature.vars] in
private theorem same_inputs {program : Program (Terms (Term signature))}
    {left right : List (Member signature program)}
    (paired : List.Forall₂ (SymbolicJointReopening.Same before.state) left right) :
    (bagOf A left).selection.taken = (bagOf A right).selection.taken ∧
    (bagOf A left).selection.read = (bagOf A right).selection.read ∧
    ((bagOf A left).members.map RuleSyntax.JointFirings.Member.key) =
      ((bagOf A right).members.map RuleSyntax.JointFirings.Member.key) := by
  induction paired with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | @cons l r ls rs aligned _ ih =>
    have takes : l.selection.taken = r.selection.taken := aligned.taken
    have reads : l.selection.read = r.selection.read := aligned.read
    have rule : l.rule = r.rule := aligned.rule
    obtain ⟨tailTakes, tailReads, tailKeys⟩ := ih
    have keys : l.key = r.key := by
      simp only [RuleSyntax.JointFirings.Member.key, rule, takes, reads]
    exact ⟨congrArg₂ List.append takes tailTakes, congrArg₂ List.append reads tailReads,
      congrArg₂ List.cons keys tailKeys⟩

omit [DecidableEq signature.vars] in
private theorem enabled_after_reservation {program : Program (Terms (Term signature))}
    {left right : List (Member signature program)}
    (takes : (bagOf A left).selection.taken = (bagOf A right).selection.taken)
    (reads : (bagOf A left).selection.read = (bagOf A right).selection.read)
    (enabled : Enabled (fun _ : ℕ => ()) before.state.present ((bagOf A left).selection.commit (T := Unit)))
    (fresh : Disjoint (bagOf A right).selection.made.toFinset before.state.present) :
    Enabled (fun _ : ℕ => ()) before.state.present ((bagOf A right).selection.commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, fresh, ?_⟩
  · simpa only [Selection.commit, takes] using enabled.taken_subset
  · simpa only [Selection.commit, reads] using enabled.kept_subset
  · simpa only [Selection.commit, takes, reads] using enabled.apart
  · intro query absent
    cases absent

variable (rules : Rules signature)

private def seenChoices : List (Finset ℕ) := before.live.sublists.map List.toFinset

omit [DecidableEq signature.vars] in
private theorem listed_seen {seen : Finset ℕ} (contained : seen ⊆ before.state.present) :
    seen ∈ seenChoices before := by
  let kept := before.live.filter fun id => decide (id ∈ seen)
  have same : kept.toFinset = seen := by
    ext i
    simp only [kept, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨And.right, fun found => ⟨?_, found⟩⟩
    exact List.mem_toFinset.mp (before.visible.symm ▸ contained found)
  exact List.mem_map.mpr ⟨kept, List.mem_sublists.mpr List.filter_sublist, same⟩

private def seenWords : ℕ → List (List (Finset ℕ))
  | 0 => [[]]
  | n + 1 => tuples (seenChoices before) (n + 1)

omit [DecidableEq signature.vars] in
private theorem mem_seenWords (count : ℕ) (seen : List (Finset ℕ)) :
    seen ∈ seenWords before count ↔ seen.length = count ∧ ∀ set ∈ seen, set ∈ seenChoices before := by
  cases count with
  | zero => cases seen <;> simp [seenWords]
  | succ count => exact mem_tuples _ _ _

/-- Exhaustive reference search for collect claims. An optimized search
can propose only the claim determined by the principal solution. -/
def inventory : List (Request rules.program) :=
  rules.attach.flatMap fun entry =>
    (portChoices before.live entry.val.body.take.length entry.val.body.read.length).attach.flatMap fun ports =>
      (seenWords before entry.val.collect.length).attach.map fun seen =>
        let shape := (portChoices_iff before.live _ _ _ _).mp ports.property
        let width := ((mem_seenWords before _ _).mp seen.property).1
        ⟨entry.val, entry.property, ports.val.1, ports.val.2, seen.val, shape.1.symm, shape.2.1.symm, width.symm⟩

omit [DecidableEq signature.vars] in
private theorem ports_listed (m : Member signature rules.program) (ready : Ready m)
    (distinct : m.selection.taken.Nodup)
    (usable : Enabled (fun _ : ℕ => ()) before.state.present (m.selection.commit (T := Unit))) :
    (m.selection.taken, m.selection.read) ∈
      portChoices before.live m.rule.body.take.length m.rule.body.read.length := by
  apply (portChoices_iff before.live _ _ _ _).mpr
  refine ⟨ready.1.symm, ready.2.1.symm, distinct, ?_, ?_⟩
  · intro id found
    exact List.mem_toFinset.mp (before.visible.symm ▸ usable.taken_subset (List.mem_toFinset.mpr found))
  · intro id found
    have read := List.mem_toFinset.mpr found
    exact ⟨List.mem_toFinset.mp (before.visible.symm ▸ usable.kept_subset read),
      fun take => Finset.disjoint_left.mp usable.apart (List.mem_toFinset.mpr take) read⟩

omit [DecidableEq signature.vars] in
private theorem request_listed (m : Member signature rules.program) (ready : Ready m)
    (distinct : m.selection.taken.Nodup)
    (usable : Enabled (fun _ : ℕ => ()) before.state.present (m.selection.commit (T := Unit)))
    (collects : ∀ seen ∈ m.seen, seen ⊆ before.state.present) :
    requestOf m ready ∈ inventory before rules := by
  apply List.mem_flatMap.mpr
  refine ⟨⟨m.rule, m.member⟩, List.mem_attach _ _, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨_, ports_listed before rules m ready distinct usable⟩, List.mem_attach _ _, ?_⟩
  have seen : m.seen ∈ seenWords before m.rule.collect.length :=
    (mem_seenWords before _ _).mpr ⟨ready.2.2.2.symm, fun seen inside => listed_seen before (collects seen inside)⟩
  exact List.mem_map.mpr ⟨⟨_, seen⟩, List.mem_attach _ _, rfl⟩

private theorem zip_right {L R : Type*} {left : List L} {right : List R} (width : left.length = right.length)
    {e : R} (member : e ∈ right) : ∃ k, (k, e) ∈ left.zip right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons first tail ih =>
    cases right with
    | nil => cases width
    | cons firstR tailR =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self⟩
      · obtain ⟨k, present⟩ := ih (Nat.succ.inj width) later
        exact ⟨k, List.mem_cons_of_mem _ present⟩

omit [DecidableEq signature.vars] in
private theorem claims_subset (m : Member signature rules.program) (ready : Ready m) (σ : Subst signature)
    (holds : m.firing.Holds (act signature) before.state (b := PUnit.unit) σ) :
    ∀ seen ∈ m.seen, seen ⊆ before.state.present := by
  intro seen inside
  have width : (m.firing.collectOpened (act signature)).length = m.seen.length := by
    simpa [RuleSyntax.Firing.collectOpened] using ready.2.2.2
  obtain ⟨pattern, claimed⟩ := zip_right width inside
  have justified : RuleSyntax.matchesAt (act signature) (b := PUnit.unit) σ
      (m.firing.row (act signature) before.state) before.state.present pattern = seen :=
    holds.2 (pattern, seen) claimed
  intro i present
  rw [← justified] at present
  exact (RuleSyntax.mem_matchesAt (act signature) σ _ _ _ _).mp present |>.1

/-! The shape proof for each member is independent of checking its guards. -/
omit [DecidableEq signature.vars] in
private theorem requestsOf_listed (members : List (Member signature rules.program))
    (ready : ∀ m ∈ members, Ready m)
    (each : ∀ m ∈ members, m.selection.taken.Nodup ∧
      Enabled (fun _ : ℕ => ()) before.state.present (m.selection.commit (T := Unit)) ∧
      ∀ seen ∈ m.seen, seen ⊆ before.state.present) :
    ∀ request ∈ requestsOf members ready, request ∈ inventory before rules := by
  induction members with
  | nil => intro request inside; cases inside
  | cons first tail ih =>
    intro request inside
    rcases List.mem_cons.mp inside with rfl | rest
    · obtain ⟨nodup, enabled, claims⟩ := each first List.mem_cons_self
      exact request_listed before rules first _ nodup enabled claims
    · exact ih (fun m hm => ready m (List.mem_cons_of_mem _ hm))
        (fun m hm => each m (List.mem_cons_of_mem _ hm)) _ rest

omit [DecidableEq signature.vars] in
private theorem requestsOf_length (members : List (Member signature rules.program)) (ready : ∀ m ∈ members, Ready m) :
    (requestsOf members ready).length = members.length := by
  induction members with
  | nil => rfl
  | cons first tail ih => simp only [requestsOf, List.length_cons, ih]

/-- A bounded family of candidate batches. A refusal at one width is
not a global quiescence certificate for a repeated-match discipline. -/
def atWidth (width : ℕ) : List (List (Request rules.program)) :=
  tuples (inventory before rules) width

omit [DecidableEq signature.vars] in
private theorem source_requests_listed (members : List (Member signature rules.program))
    (fits : (bagOf A members).Fits (act signature) before.state)
    (usable : ∀ m ∈ members, Enabled (fun _ : ℕ => ()) before.state.present (m.selection.commit (T := Unit)))
    (ρ : Subst signature) (holds : (bagOf A members).Holds (act signature) before.state (b := PUnit.unit) ρ) :
    requestsOf members fits.2.2.2 ∈ atWidth before rules members.length := by
  refine (mem_tuples _ _ _).mpr ⟨requestsOf_length rules _ _, ?_⟩
  apply requestsOf_listed before rules
  intro m inside
  exact ⟨(List.nodup_flatMap.mp fits.2.1).1 m inside, usable m inside,
    claims_subset before rules m (fits.2.2.2 m inside) ρ (holds m inside)⟩

private theorem fresh_outputs (requests : List (Request rules.program)) :
    Disjoint (requestBatch before slots requests).selection.made.toFinset before.state.present := by
  rw [SymbolicBatch.requestBatch_made]
  exact before.reserve_fresh _ _

omit [DecidableEq signature.vars] in
private theorem member_enabled {left right : List (Member signature rules.program)}
    (paired : List.Forall₂ (SymbolicJointReopening.Same before.state) left right)
    (available : ∀ m ∈ left, Enabled (fun _ : ℕ => ()) before.state.present (m.selection.commit (T := Unit)))
    (fresh : Disjoint (bagOf A right).selection.made.toFinset before.state.present) :
    ∀ m ∈ right, Enabled (fun _ : ℕ => ()) before.state.present (m.selection.commit (T := Unit)) := by
  intro member included
  obtain ⟨source, belongs, related⟩ := SymbolicJointReopening.pair_of_right paired member included
  have take : source.selection.taken = member.selection.taken := related.taken
  have read : source.selection.read = member.selection.read := related.read
  have enabled := available source belongs
  refine ⟨?_, ?_, ?_, ?_, fun _ no => by cases no⟩
  · simpa only [Selection.commit, take] using enabled.taken_subset
  · simpa only [Selection.commit, read] using enabled.kept_subset
  · simpa only [Selection.commit, take, read] using enabled.apart
  · apply Finset.disjoint_left.mpr
    intro id new live
    have all : id ∈ (bagOf A right).selection.made.toFinset := List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨member, included, List.mem_toFinset.mp new⟩)
    exact Finset.disjoint_left.mp fresh all live

private theorem canonical_joint_candidate (members : List (Member signature rules.program))
    (admitted : (bagOf A members).Admits (act signature) before.state) :
    ∃ reqs ∈ atWidth before rules members.length,
      List.Forall₂ (SymbolicJointReopening.Same before.state) members (requestBatch before slots reqs).members ∧
      (requestBatch before slots reqs).Fits (act signature) before.state ∧
      Enabled (fun _ : ℕ => ()) before.state.present ((requestBatch before slots reqs).selection.commit (T := Unit)) ∧
      ∀ m ∈ members, ∀ seen ∈ m.seen, seen ⊆ before.state.present := by
  let reqs := requestsOf members admitted.1.2.2.2
  have paired := requests_align before slots members admitted.1.2.2.2 0 0
  have ⟨takes, reads, _⟩ := same_inputs before paired
  have fits : (requestBatch before slots reqs).Fits (act signature) before.state :=
    SymbolicBatch.requestBatch_fits before slots reqs (takes ▸ admitted.1.2.1)
  have enabled := enabled_after_reservation before takes reads admitted.2.1 (fresh_outputs before slots rules reqs)
  obtain ⟨point, ρ, model⟩ := admitted.2.2.1
  cases point
  have tests := admitted.2.2.2 PUnit.unit ρ model
  have listed := source_requests_listed before rules members admitted.1
    (fun _ inside => Bag.enabled_member admitted.2.1 inside) ρ tests
  exact ⟨reqs, listed, paired, fits, enabled,
    fun m inside => claims_subset before rules m (admitted.1.2.2.2 m inside) ρ (tests m inside)⟩

theorem atWidth_covers_joint_models (members : List (Member signature rules.program))
    (admitted : (bagOf A members).Admits (act signature) before.state) :
    ∃ reqs ∈ atWidth before rules members.length,
      (requestBatch before slots reqs).Admits (act signature) before.state ∧
      (requestBatch before slots reqs).members.map RuleSyntax.JointFirings.Member.key =
        members.map RuleSyntax.JointFirings.Member.key ∧
      ∀ incoming output, WordResultModel before.state (bagOf A members) incoming output ↔
        WordResultModel before.state (requestBatch before slots reqs) incoming output := by
  obtain ⟨reqs, listed, paired, fits, enabled, _⟩ := canonical_joint_candidate before slots rules members admitted
  have ⟨_, _, keys⟩ := same_inputs before paired
  exact ⟨reqs, listed, SymbolicJointReopening.admits_joint paired admitted fits enabled, keys.symm,
    SymbolicJointReopening.result_models paired admitted.1.1 fits.1
      (fun _ inside => Bag.enabled_member admitted.2.1 inside) (fun _ inside => Bag.enabled_member enabled inside)⟩

theorem atWidth_covers_round_models (members : List (Member signature rules.program))
    (admitted : RuleSyntax.StepWeb.Rounds.RuntimeRound A before.state members) :
    ∃ reqs ∈ atWidth before rules members.length,
      RuleSyntax.StepWeb.Rounds.RuntimeRound A before.state (requestBatch before slots reqs).members ∧
      ∀ incoming output, WordResultModel before.state (bagOf A members) incoming output ↔
        WordResultModel before.state (requestBatch before slots reqs) incoming output := by
  obtain ⟨reqs, listed, paired, fits, enabled, collects⟩ := canonical_joint_candidate before slots rules members admitted.1
  exact ⟨reqs, listed, SerialReopening.round before paired admitted fits enabled collects,
    SymbolicJointReopening.result_models paired admitted.1.1.1 fits.1
      (fun _ inside => Bag.enabled_member admitted.1.2.1 inside) (fun _ inside => Bag.enabled_member enabled inside)⟩

theorem atWidth_covers_joint (members : List (Member signature rules.program))
    (admitted : (bagOf A members).Admits (act signature) before.state) :
    ∃ reqs ∈ atWidth before rules members.length,
      (requestBatch before slots reqs).Admits (act signature) before.state ∧
      (requestBatch before slots reqs).members.map RuleSyntax.JointFirings.Member.key =
        members.map RuleSyntax.JointFirings.Member.key := by
  obtain ⟨reqs, listed, legal, keys, _⟩ := atWidth_covers_joint_models before slots rules members admitted
  exact ⟨reqs, listed, legal, keys⟩

/-- The same proposals cover synchronous firings. In contrast with a
joint firing, a member may read an occurrence that another member is
taking; the read is from the entry snapshot. -/
theorem atWidth_covers_snapshot_models (members : List (Member signature rules.program))
    (admitted : (bagOf A members).AdmitsSnapshot (act signature) before.state) :
    ∃ reqs ∈ atWidth before rules members.length,
      (requestBatch before slots reqs).AdmitsSnapshot (act signature) before.state ∧
      (requestBatch before slots reqs).members.map RuleSyntax.JointFirings.Member.key =
        members.map RuleSyntax.JointFirings.Member.key ∧
      ∀ incoming output, WordResultModel before.state (bagOf A members) incoming output ↔
        WordResultModel before.state (requestBatch before slots reqs) incoming output := by
  let reqs := requestsOf members admitted.1.2.2.2
  have paired := requests_align before slots members admitted.1.2.2.2 0 0
  have ⟨takes, _, keys⟩ := same_inputs before paired
  have fits : (requestBatch before slots reqs).Fits (act signature) before.state :=
    SymbolicBatch.requestBatch_fits before slots reqs (takes ▸ admitted.1.2.1)
  have enabled := member_enabled before rules paired admitted.2.1 (fresh_outputs before slots rules reqs)
  have snapshot := SymbolicJointReopening.admits_snapshot paired admitted fits enabled
  obtain ⟨point, ρ, model⟩ := admitted.2.2.1
  cases point
  have listed := source_requests_listed before rules members admitted.1 admitted.2.1 ρ (admitted.2.2.2 PUnit.unit ρ model)
  exact ⟨reqs, listed, snapshot, keys.symm, SymbolicJointReopening.result_models paired admitted.1.1 fits.1 admitted.2.1 enabled⟩

omit [DecidableEq signature.vars] in
private theorem keys_agree (keying : SymbolicComplete.Keying rules)
    {left right : List (Member signature rules.program)}
    (paired : List.Forall₂ (SymbolicJointReopening.Same before.state) left right) :
    (bagOf A left).keysBy keying.identity = (bagOf A right).keysBy keying.identity := by
  induction paired with
  | nil => rfl
  | @cons l r restL restR aligned _ ih =>
    exact congrArg₂ List.cons (keying.stable aligned) ih

theorem atWidth_covers_own_models (keying : SymbolicComplete.Keying rules)
    (members : List (Member signature rules.program))
    (admitted : (bagOf A members).AdmitsOwn (act signature) before.state) :
    ∃ reqs ∈ atWidth before rules members.length,
      (requestBatch before slots reqs).AdmitsOwn (act signature) before.state ∧
      (requestBatch before slots reqs).keysBy keying.identity = (bagOf A members).keysBy keying.identity ∧
      ∀ incoming output, WordResultModel before.state (bagOf A members) incoming output ↔
        WordResultModel before.state (requestBatch before slots reqs) incoming output := by
  let reqs := requestsOf members admitted.1.2.2.2
  have paired := requests_align before slots members admitted.1.2.2.2 0 0
  have ⟨takes, reads, _⟩ := same_inputs before paired
  have keys := keys_agree before rules keying paired
  have fits : (requestBatch before slots reqs).Fits (act signature) before.state :=
    SymbolicBatch.requestBatch_fits before slots reqs (takes ▸ admitted.1.2.1)
  have enabled := enabled_after_reservation before takes reads admitted.2.1 (fresh_outputs before slots rules reqs)
  have check := SymbolicJointReopening.admits_own paired admitted fits enabled
  have joint := Bag.admits_of_admitsOwn (act signature) admitted
  obtain ⟨point, ρ, model⟩ := joint.2.2.1
  cases point
  have each (m : Member signature rules.program) (inside : m ∈ members) :
      Enabled (fun _ : ℕ => ()) before.state.present (m.selection.commit (T := Unit)) :=
    Bag.enabled_member (m := m) admitted.2.1 inside
  have listed := source_requests_listed before rules members admitted.1 each ρ (joint.2.2.2 PUnit.unit ρ model)
  exact ⟨reqs, listed, check, keys.symm,
    SymbolicJointReopening.result_models paired admitted.1.1 fits.1 each (fun _ inside => Bag.enabled_member enabled inside)⟩

theorem atWidth_covers_every_models (keying : SymbolicComplete.Keying rules) (region : keying.identity.Key → Prop)
    (members : List (Member signature rules.program))
    (admitted : (bagOf A members).AdmitsEveryBy (act signature) before.state keying.identity region) :
    ∃ reqs ∈ atWidth before rules members.length,
      (requestBatch before slots reqs).AdmitsEveryBy (act signature) before.state keying.identity region ∧
      ∀ incoming output, WordResultModel before.state (bagOf A members) incoming output ↔
        WordResultModel before.state (requestBatch before slots reqs) incoming output := by
  obtain ⟨reqs, listed, own, keys, model⟩ := atWidth_covers_own_models before slots rules keying members admitted.1
  refine ⟨reqs, listed, ⟨own, ?_, ?_, ?_⟩, model⟩
  · rw [keys]
    exact admitted.2.1
  · change ((requestBatch before slots reqs).keysBy keying.identity).Nodup
    rw [keys]
    exact admitted.2.2.1
  · intro source hasRegion admittedSource
    rw [keys]
    exact admitted.2.2.2 source hasRegion admittedSource

theorem atWidth_covers_unique_models (keying : SymbolicComplete.Keying rules) (region : keying.identity.Key → Prop)
    (members : List (Member signature rules.program))
    (admitted : (bagOf A members).AdmitsUniqueBy (act signature) before.state keying.identity region) :
    ∃ reqs ∈ atWidth before rules members.length,
      (requestBatch before slots reqs).AdmitsUniqueBy (act signature) before.state keying.identity region ∧
      ∀ incoming output, WordResultModel before.state (bagOf A members) incoming output ↔
        WordResultModel before.state (requestBatch before slots reqs) incoming output := by
  obtain ⟨reqs, listed, entire, model⟩ := atWidth_covers_every_models before slots rules keying region members admitted.1
  have length : reqs.length = members.length := ((mem_tuples _ _ _).mp listed).1
  refine ⟨reqs, listed, ⟨entire, ?_⟩, model⟩
  rw [SymbolicBatch.requestBatch_width, length]
  exact admitted.2

theorem atWidth_covers_maximal_models (members : List (Member signature rules.program))
    (admitted : (bagOf A members).AdmitsMaximal (act signature) before.state) :
    ∃ reqs ∈ atWidth before rules members.length,
      (requestBatch before slots reqs).AdmitsMaximal (act signature) before.state ∧
      ∀ incoming output, WordResultModel before.state (bagOf A members) incoming output ↔
        WordResultModel before.state (requestBatch before slots reqs) incoming output := by
  obtain ⟨reqs, listed, joint, keys, model⟩ := atWidth_covers_joint_models before slots rules members admitted.1
  refine ⟨reqs, listed, ⟨joint, ?_, ?_⟩, model⟩
  · change ((requestBatch before slots reqs).members.map RuleSyntax.JointFirings.Member.key).Nodup
    rw [keys]
    exact admitted.2.1
  · intro other allowed distinct contains key inside
    rw [keys]
    exact admitted.2.2 other allowed distinct (fun k tagged => contains k (keys ▸ tagged)) key inside

abbrev Key (signature : LPSignature) := RuleSyntax.Rule (Terms (Term signature)) × List ℕ × List ℕ

def requestKey {program : Program (Terms (Term signature))} (request : Request program) : Key signature :=
  (request.rule, request.taken, request.read)

def keyInventory : List (Key signature) :=
  rules.flatMap fun rule =>
    (portChoices before.live rule.body.take.length rule.body.read.length).map
      fun ports => (rule, ports.1, ports.2)

theorem requestBatch_keys (requests : List (Request rules.program)) :
    (requestBatch before slots requests).members.map RuleSyntax.JointFirings.Member.key =
      requests.map requestKey := by
  change ((SymbolicBatch.allocate before slots requests 0 0).map Prod.snd).map _ = _
  suffices ∀ index offset,
      ((SymbolicBatch.allocate before slots requests index offset).map Prod.snd).map
        RuleSyntax.JointFirings.Member.key = requests.map requestKey by
    exact this 0 0
  induction requests with
  | nil => intros; rfl
  | cons first tail ih =>
    intro index offset
    exact congrArg (List.cons (requestKey first)) (ih (index + 1) (offset + first.rule.body.produce.length))

omit [DecidableEq signature.vars] in
/-- Collection claims and fresh identities cannot raise the width of a
distinct batch. Its keys lie in the finite geometry inventory, whether
or not any of those keys passes its guard in isolation. -/
theorem distinct_joint_width
    (members : List (Member signature rules.program))
    (admitted : (bagOf A members).Admits (act signature) before.state)
    (distinct : (bagOf A members).Distinct) :
    members.length ≤ (keyInventory before rules).length := by
  have subset : members.map RuleSyntax.JointFirings.Member.key ⊆ keyInventory before rules := by
    intro key here
    obtain ⟨m, inside, rfl⟩ := List.mem_map.mp here
    have geometry := ports_listed before rules m (admitted.1.2.2.2 m inside)
      ((List.nodup_flatMap.mp admitted.1.2.1).1 m inside) (Bag.enabled_member admitted.2.1 inside)
    exact List.mem_flatMap.mpr ⟨m.rule, m.member,
      List.mem_map.mpr ⟨(m.selection.taken, m.selection.read), geometry, rfl⟩⟩
  simpa only [List.length_map] using distinct.length_le_of_subset subset

omit [DecidableEq signature.vars] in
/-- A distinct jointly admitted batch that fills the geometry bound has
no larger extension. No further guard or batch needs to be tried. -/
theorem maximal_of_full (batch : Bag ℕ (ext A) rules.program before.state.frame)
    (allowed : batch.Admits (act signature) before.state) (unique : batch.Distinct)
    (full : (keyInventory before rules).length ≤ batch.members.length) :
    batch.AdmitsMaximal (act signature) before.state := by
  refine ⟨allowed, unique, ?_⟩
  intro rival admitted distinct contains extra inside
  by_contra absent
  have enlarged : (extra :: batch.members.map RuleSyntax.JointFirings.Member.key).Nodup :=
    List.nodup_cons.mpr ⟨absent, unique⟩
  have bound := enlarged.length_le_of_subset (l₂ := rival.members.map RuleSyntax.JointFirings.Member.key)
    (fun _ found => (List.mem_cons.mp found).elim (fun eq => eq.symm ▸ inside) (contains _))
  cases rival with
  | mk extension others =>
    cases extension
    have size := distinct_joint_width before rules others admitted distinct
    simp only [List.length_cons, List.length_map] at bound
    change (keyInventory before rules).length ≤ batch.members.length at full
    change batch.members.length + 1 ≤ others.length at bound
    omega

variable [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

private theorem joint_test_accepts (requests : List (Request rules.program)) :
    (SymbolicBatch.advanceRequests before slots .joint requests).isSome = true ↔
      requests ≠ [] ∧ (requestBatch before slots requests).Admits (act signature) before.state := by
  constructor
  · intro found
    obtain ⟨⟨answer, after⟩, note⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨ready, prepared, licensed, _, _⟩ :=
      (SymbolicBatch.advanceRequests_exact before slots .joint requests answer after).mp note
    have readySome : (SymbolicBatch.prepareRequests before slots requests).isSome = true := by rw [prepared]; rfl
    refine ⟨((SymbolicBatch.prepareRequests_some_iff before slots requests).mp readySome).1, ?_⟩
    have batch := SymbolicBatch.prepared_batch before slots requests prepared
    change ready.batch.Admits (act signature) before.state at licensed
    exact batch ▸ licensed
  · rintro ⟨nonempty, joint⟩
    have readySome := (SymbolicBatch.prepareRequests_some_iff before slots requests).mpr ⟨nonempty, joint.1.2.1⟩
    obtain ⟨ready, prepared⟩ := Option.isSome_iff_exists.mp readySome
    have batch := SymbolicBatch.prepared_batch before slots requests prepared
    have licensed : SymbolicBatch.Admits .joint ready := by
      change ready.batch.Admits (act signature) before.state
      exact batch ▸ joint
    obtain ⟨answer, executed⟩ := SymbolicBatch.admitted_has_result .joint ready licensed
    have solved := ((SymbolicBatch.evaluate_exact .joint ready answer _).mp executed).1
    exact Option.isSome_iff_exists.mpr ⟨(answer, _),
      (SymbolicBatch.advanceRequests_exact before slots .joint requests answer _).mpr
        ⟨ready, prepared, licensed, solved, rfl⟩⟩

private def strictSuperset (base trial : List (Key signature)) : Bool :=
  letI : DecidableEq (Key signature) := (SymbolicComplete.ordered rules).equality
  base.all (fun k => decide (k ∈ trial)) && trial.any (fun k => decide (k ∉ base))

private theorem strictSuperset_exact (base trial : List (Key signature)) :
    strictSuperset rules base trial = true ↔ base ⊆ trial ∧ ∃ k ∈ trial, k ∉ base := by
  simp only [strictSuperset, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
  exact Iff.rfl

def extensionSeen (base : List (Key signature)) : Bool :=
  letI : DecidableEq (Key signature) := (SymbolicComplete.ordered rules).equality
  (List.range ((keyInventory before rules).length + 1)).any fun width =>
    (atWidth before rules width).any fun reqs =>
      let keys := reqs.map requestKey
      (decide keys.Nodup && strictSuperset rules base keys) &&
        (SymbolicBatch.advanceRequests before slots .joint reqs).isSome

theorem extensionSeen_exact (base : List (Key signature)) :
    extensionSeen before slots rules base = true ↔
      ∃ trial : Bag ℕ (ext A) rules.program before.state.frame,
        trial.Admits (act signature) before.state ∧ trial.Distinct ∧
        base ⊆ trial.members.map RuleSyntax.JointFirings.Member.key ∧
        ∃ k ∈ trial.members.map RuleSyntax.JointFirings.Member.key, k ∉ base := by
  simp only [extensionSeen, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    strictSuperset_exact, joint_test_accepts]
  constructor
  · rintro ⟨_, _, reqs, _, ⟨distinct, cover, extra⟩, _, licensed⟩
    let batch := requestBatch before slots reqs
    have keys := requestBatch_keys before slots rules reqs
    refine ⟨batch, licensed, ?_, ?_, ?_⟩
    · change (batch.members.map RuleSyntax.JointFirings.Member.key).Nodup
      exact keys ▸ distinct
    · exact keys ▸ cover
    · exact keys ▸ extra
  · rintro ⟨⟨extension, members⟩, licensed, unique, covered, ⟨key, extra, absent⟩⟩
    cases extension
    have width := distinct_joint_width before rules members licensed unique
    obtain ⟨reqs, listed, admitted, sameKeys⟩ := atWidth_covers_joint before slots rules members licensed
    have keys : reqs.map requestKey = members.map RuleSyntax.JointFirings.Member.key :=
      (requestBatch_keys before slots rules reqs).symm.trans sameKeys
    have nonempty : reqs ≠ [] := by
      intro no
      rw [← keys, no] at extra
      cases extra
    refine ⟨members.length, List.mem_range.mpr (Nat.lt_succ_of_le width), reqs, listed,
      ⟨?_, ?_, ⟨key, ?_, absent⟩⟩, nonempty, admitted⟩
    · exact keys ▸ unique
    · exact keys ▸ covered
    · exact keys ▸ extra

def maximalOK (batch : Bag ℕ (ext (FirstOrder.action signature)) rules.program before.state.frame) : Bool :=
  letI : DecidableEq (Key signature) := (SymbolicComplete.ordered rules).equality
  let keys := batch.members.map RuleSyntax.JointFirings.Member.key
  decide keys.Nodup &&
    (decide ((keyInventory before rules).length ≤ keys.length) || !(extensionSeen before slots rules keys))

theorem maximalOK_exact (batch : Bag ℕ (ext (FirstOrder.action signature)) rules.program before.state.frame)
    (joint : batch.Admits (act signature) before.state) :
    maximalOK before slots rules batch = true ↔ batch.AdmitsMaximal (act signature) before.state := by
  have absent : extensionSeen before slots rules (batch.members.map RuleSyntax.JointFirings.Member.key) =
      false ↔ ¬ ∃ rival : Bag ℕ (ext A) rules.program before.state.frame,
        rival.Admits (act signature) before.state ∧ rival.Distinct ∧
        (∀ k ∈ batch.members.map RuleSyntax.JointFirings.Member.key,
          k ∈ rival.members.map RuleSyntax.JointFirings.Member.key) ∧
        ∃ k ∈ rival.members.map RuleSyntax.JointFirings.Member.key,
          k ∉ batch.members.map RuleSyntax.JointFirings.Member.key := by
    exact Bool.eq_false_iff.trans (not_congr (extensionSeen_exact before slots rules _))
  simp only [maximalOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.length_map]
  constructor
  · rintro ⟨distinct, full | none⟩
    · exact maximal_of_full before rules batch joint distinct full
    · exact (Bag.admitsMaximal_iff batch).mpr ⟨joint, distinct, absent.mp none⟩
  · intro maximal
    exact ⟨maximal.2.1, Or.inr (absent.mpr ((Bag.admitsMaximal_iff batch).mp maximal).2.2)⟩

def evaluateMaximal (selection : SymbolicBatch.Prepared (program := rules.program) before.state) :
    Option (Subst signature × SymbolicFiring.World signature ℕ) :=
  if maximalOK before slots rules selection.batch then SymbolicBatch.evaluate .joint selection else none

theorem evaluateMaximal_exact (selection : SymbolicBatch.Prepared (program := rules.program) before.state)
    (answer : Subst signature) (after : SymbolicFiring.World signature ℕ) :
    evaluateMaximal before slots rules selection = some (answer, after) ↔
      selection.batch.AdmitsMaximal (act signature) before.state ∧
      unifyTotal (selection.batch.information (act signature) before.state) = some answer ∧
      after = selection.batch.result (act signature) before.state := by
  constructor
  · intro found
    unfold evaluateMaximal at found
    split at found
    · rename_i checked
      obtain ⟨solved, joint, equal⟩ := (SymbolicBatch.evaluate_exact .joint selection answer after).mp found
      exact ⟨(maximalOK_exact before slots rules _ joint).mp checked, solved, equal⟩
    · cases found
  · rintro ⟨maximal, solved, equal⟩
    have allowed := (maximalOK_exact before slots rules _ maximal.1).mpr maximal
    have found := (SymbolicBatch.evaluate_exact .joint selection answer after).mpr ⟨solved, maximal.1, equal⟩
    simp [evaluateMaximal, allowed, found]

end Mettapedia.Machines.TIsa.Derivation.SymbolicScheduleSearch
