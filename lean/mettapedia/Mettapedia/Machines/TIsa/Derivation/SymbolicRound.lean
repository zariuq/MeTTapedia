import Mettapedia.Machines.TIsa.Derivation.SymbolicBatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundEveryOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MaximalOneExtension
import Mathlib.Data.List.Permutation

/-!
# One snapshot is not a round

A round must also be legal as a sequence of single firings in every
order. The reference checker evaluates each order with the same
symbolic firing evaluator, inspecting the state produced by preceding
firings. Admission at the entry snapshot alone cannot justify this:
one member can make a value another member required to be absent.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicRound

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open RuleSyntax.JointFirings (Bag OneMember bagOf fresh_after enabled_after)
open RuleSyntax.OneFrame (Terms)
open RuleSyntax.StepWeb.Rounds (FiresInOrder RuntimeRound stateAfter stateAfter_eq_result result_perm_congruent)
open SymbolicFiring (World act)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {program : RuleSyntax.Program (Terms (Term signature))}

private abbrev Action (signature : LPSignature) := FirstOrder.action signature
abbrev Member (signature : LPSignature) (O : Type) (program : RuleSyntax.Program (Terms (Term signature))) :=
  OneMember (Action signature) O program

private abbrev bag (members : List (Member signature O program)) := bagOf (Action signature) members

private def selectedAt {before : World signature O} {member : Member signature O program}
    {available : List (Member signature O program)} (inside : member ∈ available)
    (fits : (bag available).Fits (act signature) before)
    (enabled : Enabled (fun _ : O => ()) before.present ((bag available).selection.commit (T := Unit))) :
    SymbolicFiring.Selection (program := program) before :=
  ⟨member.firing,
    ⟨Bag.fresh_member (act signature) (fun _ _ => ⟨Subst.id signature⟩) fits.1 inside,
      (List.nodup_flatMap.mp fits.2.1).1 member inside,
      (List.nodup_flatMap.mp fits.2.2.1).1 member inside,
      fits.2.2.2 member inside⟩,
    Bag.enabled_member (m := member) enabled inside⟩

private abbrev selected {before : World signature O} {member : Member signature O program}
    {rest : List (Member signature O program)}
    (fits : (bag (member :: rest)).Fits (act signature) before)
    (enabled : Enabled (fun _ : O => ()) before.present ((bag (member :: rest)).selection.commit (T := Unit))) :
    SymbolicFiring.Selection (program := program) before :=
  selectedAt List.mem_cons_self fits enabled

private theorem tail_fits {before : World signature O} {member : Member signature O program}
    {rest : List (Member signature O program)}
    (fits : (bag (member :: rest)).Fits (act signature) before)
    (enabled : Enabled (fun _ : O => ()) before.present ((bag (member :: rest)).selection.commit (T := Unit))) :
    (bag rest).Fits (act signature) (member.firing.result (act signature) before) :=
  ⟨fresh_after (Action signature) (selected fits enabled).shaped (selected fits enabled).enabled fits.1,
    (List.nodup_append.mp
      (show (member.selection.taken ++ (bag rest).selection.taken).Nodup from fits.2.1)).2.1,
    (List.nodup_append.mp
      (show (member.selection.made ++ (bag rest).selection.made).Nodup from fits.2.2.1)).2.1,
    fun later inside => fits.2.2.2 later (List.mem_cons_of_mem _ inside)⟩

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

private theorem selected_exact {before : World signature O}
    (selection : SymbolicFiring.Selection (program := program) before) :
    (SymbolicFiring.evaluate selection).isSome = true ↔ SymbolicFiring.Admitted selection :=
  ⟨fun successful => by
    obtain ⟨⟨answer, world⟩, run⟩ := Option.isSome_iff_exists.mp successful
    exact ((SymbolicFiring.evaluate_exact selection answer world).mp run).2.1,
    fun allowed => by
      obtain ⟨answer, run⟩ := SymbolicFiring.admitted_has_computed_result selection allowed
      simp [run]⟩

/-- Check a concrete order at each successive prefix. The fit and commit
evidence only justify carrying the remaining resource selection forward;
they do not assert that any of its guards continue to hold. -/
def orderOK : (before : World signature O) → (members : List (Member signature O program)) →
    (bag members).Fits (act signature) before →
    Enabled (fun _ : O => ()) before.present ((bag members).selection.commit (T := Unit)) → Bool
  | _, [], _, _ => true
  | before, member :: rest, fits, enabled =>
    (SymbolicFiring.evaluate (selected fits enabled)).isSome &&
      orderOK (member.firing.result (act signature) before) rest (tail_fits fits enabled)
        (enabled_after (Action signature) fits.2.1 fits.2.2.1 enabled)

theorem orderOK_exact : ∀ (before : World signature O) (members : List (Member signature O program))
    (fits : (bag members).Fits (act signature) before)
    (enabled : Enabled (fun _ : O => ()) before.present ((bag members).selection.commit (T := Unit))),
    orderOK before members fits enabled = true ↔ FiresInOrder (Action signature) before members
  | _, [], _, _ => by simp [orderOK, FiresInOrder]
  | before, member :: rest, fits, enabled => by
    rw [orderOK, Bool.and_eq_true]
    change (_ = true ∧ _) ↔ SymbolicFiring.Admitted (selected fits enabled) ∧ _
    exact and_congr (selected_exact _) (orderOK_exact _ _ _ _)

def ordersOK (before : World signature O) (members : List (Member signature O program))
    (own : (bag members).AdmitsOwn (act signature) before) : Bool :=
  members.permutations.attach.all fun order =>
    have atOrder := Bag.admitsOwn_perm (act signature) (List.mem_permutations.mp order.property).symm own
    orderOK before order.val atOrder.1 atOrder.2.1

theorem ordersOK_exact (before : World signature O) (members : List (Member signature O program))
    (own : (bag members).AdmitsOwn (act signature) before) :
    ordersOK before members own = true ↔ RuntimeRound (Action signature) before members := by
  simp only [ordersOK, List.all_eq_true]
  constructor
  · intro checks
    apply RuleSyntax.StepWeb.Rounds.runtimeRound_of_fires (Action signature) own
    intro order permutation
    let index : { order // order ∈ members.permutations } :=
      ⟨order, List.mem_permutations.mpr permutation⟩
    exact (orderOK_exact _ _ _ _).mp (checks index (List.mem_attach _ _))
  · intro round order _
    exact (orderOK_exact _ _ _ _).mpr (round.2 order.val (List.mem_permutations.mp order.property)).1

section Partitions

variable {α : Type*}

/-- Each input position independently belongs to the executed prefix or
the remainder. Neither branch identifies equal members. Both lists keep
their original relative order. -/
def prefixParts : List α → List (List α × List α)
  | [] => [([], [])]
  | head :: tail =>
    let rest := prefixParts tail
    (rest.map fun (done, remaining) => (head :: done, remaining)) ++
      rest.map fun (done, remaining) => (done, head :: remaining)

theorem prefixParts_length (members : List α) : (prefixParts members).length = 2 ^ members.length := by
  induction members with
  | nil => rfl
  | cons head tail ih =>
    simp only [prefixParts, List.length_append, List.length_map, List.length_cons, ih, pow_succ]
    omega

/-- Number of guard probes if none of the tests short-circuit. -/
def prefixProbeCount (members : List α) : ℕ :=
  ((prefixParts members).map fun p => p.2.length).sum

private theorem sum_increments (lengths : List ℕ) :
    (lengths.map (· + 1)).sum = lengths.sum + lengths.length := by
  induction lengths with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem prefixProbeCount_cons (a : α) (members : List α) :
    prefixProbeCount (a :: members) = 2 * prefixProbeCount members + 2 ^ members.length := by
  unfold prefixProbeCount
  simp only [prefixParts, List.map_append, List.sum_append, List.map_map, Function.comp_def, List.length_cons]
  let lengths := (prefixParts members).map fun p => p.2.length
  change lengths.sum + ((prefixParts members).map (fun p => p.2.length + 1)).sum = _
  rw [show (prefixParts members).map (fun p => p.2.length + 1) = lengths.map (· + 1) from
    (List.map_map ..).symm, sum_increments, List.length_map, prefixParts_length]
  change lengths.sum + (lengths.sum + 2 ^ members.length) = 2 * lengths.sum + 2 ^ members.length
  omega

/-- Exactly one half of the subsets omit each input position. The factor
of two also gives a uniform statement for the empty batch. -/
theorem prefixProbeCount_exact (members : List α) :
    2 * prefixProbeCount members = members.length * 2 ^ members.length := by
  induction members with
  | nil => rfl
  | cons first rest ih =>
    rw [prefixProbeCount_cons, List.length_cons, pow_succ]
    conv_rhs => rw [Nat.succ_mul]
    calc
      2 * (2 * prefixProbeCount rest + 2 ^ rest.length) =
          (2 * prefixProbeCount rest) * 2 + 2 ^ rest.length * 2 := by omega
      _ = rest.length * (2 ^ rest.length * 2) + 2 ^ rest.length * 2 := by rw [ih, Nat.mul_assoc]

theorem prefixParts_sound {members done remaining : List α} (parts : (done, remaining) ∈ prefixParts members) :
    (done ++ remaining).Perm members := by
  induction members generalizing done remaining with
  | nil => simpa [prefixParts] using (show (done, remaining) ∈ [([], [])] from parts)
  | cons head tail ih =>
    simp only [prefixParts, List.mem_append, List.mem_map] at parts
    rcases parts with ⟨⟨p, r⟩, valid, eq⟩ | ⟨⟨p, r⟩, valid, eq⟩
    · cases eq
      exact (ih valid).cons _
    · cases eq
      exact List.perm_middle.trans ((ih valid).cons _)

theorem prefixParts_cover {members before after : List α} (split : (before ++ after).Perm members) :
    ∃ p ∈ prefixParts members, p.1.Perm before ∧ p.2.Perm after := by
  induction members generalizing before after with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp (List.perm_nil.mp split)
    exact ⟨([], []), List.mem_cons_self, .nil, .nil⟩
  | cons head tail ih =>
    have present : head ∈ before ++ after := split.mem_iff.mpr List.mem_cons_self
    rcases List.mem_append.mp present with inBefore | inAfter
    · obtain ⟨l, r, rfl⟩ := List.append_of_mem inBefore
      have reorder : (head :: ((l ++ r) ++ after)).Perm ((l ++ head :: r) ++ after) :=
        List.perm_middle.symm.append_right _
      obtain ⟨⟨p, q⟩, available, beforeEq, afterEq⟩ := ih (List.Perm.cons_inv (reorder.trans split))
      refine ⟨(head :: p, q), List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, available, rfl⟩)), ?_, afterEq⟩
      exact (beforeEq.cons head).trans List.perm_middle.symm
    · obtain ⟨l, r, rfl⟩ := List.append_of_mem inAfter
      have reorder : (head :: (before ++ (l ++ r))).Perm (before ++ (l ++ head :: r)) := by
        simpa only [List.append_assoc] using (List.perm_middle.symm :
          (head :: ((before ++ l) ++ r)).Perm ((before ++ l) ++ head :: r))
      obtain ⟨⟨p, q⟩, available, beforeEq, afterEq⟩ := ih (List.Perm.cons_inv (reorder.trans split))
      refine ⟨(p, head :: q), List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, available, rfl⟩)), beforeEq, ?_⟩
      exact (afterEq.cons head).trans List.perm_middle.symm

namespace Examples

theorem equal_members_still_give_two_singleton_prefixes :
    ((prefixParts ([5, 5] : List ℕ)).filter fun p => p.1.length == 1).length = 2 := rfl

theorem eight_members_need_1024_guard_probes :
    prefixProbeCount (List.range 8) = 1024 := by
  have exactCount := prefixProbeCount_exact (List.range 8)
  rw [List.length_range] at exactCount
  norm_num only [Nat.reducePow, Nat.reduceMul] at exactCount
  omega

end Examples

end Partitions

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem fits_after (source : World signature O) (done remaining : List (Member signature O program))
    (fits : (bag (done ++ remaining)).Fits (act signature) source)
    (enabled : Enabled (fun _ : O => ()) source.present ((bag (done ++ remaining)).selection.commit (T := Unit))) :
    (bag remaining).Fits (act signature) (stateAfter (Action signature) source done) ∧
      Enabled (fun _ : O => ()) (stateAfter (Action signature) source done).present
        ((bag remaining).selection.commit (T := Unit)) := by
  induction done generalizing source with
  | nil => exact ⟨fits, enabled⟩
  | cons first tail ih =>
    exact ih _ (tail_fits fits enabled) (enabled_after (Action signature) fits.2.1 fits.2.2.1 enabled)

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem prefix_own (source : World signature O) {members done remaining : List (Member signature O program)}
    (own : (bag members).AdmitsOwn (act signature) source) (order : (done ++ remaining).Perm members) :
    (bag done).AdmitsOwn (act signature) source :=
  Bag.admitsOwn_sublist (X := act signature) (fun _ _ => ⟨Subst.id signature⟩)
    (Bag.admitsOwn_perm (act signature) order.symm own) (List.sublist_append_left _ _)

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem prefix_equiv (source : World signature O) {first second : List (Member signature O program)}
    (own : (bag first).AdmitsOwn (act signature) source) (reorder : first.Perm second) :
    RuleSyntax.Scope.Congruent (stateAfter (Action signature) source second) (stateAfter (Action signature) source first) := by
  have other := Bag.admitsOwn_perm (act signature) reorder own
  rw [stateAfter_eq_result _ _ _ own.1 own.2.1, stateAfter_eq_result _ _ _ other.1 other.2.1]
  exact result_perm_congruent _ reorder own.1

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem suffix_of_fires (source : World signature O) (done rest : List (Member signature O program))
    (legal : FiresInOrder (Action signature) source (done ++ rest)) :
    FiresInOrder (Action signature) (stateAfter (Action signature) source done) rest := by
  induction done generalizing source with
  | nil => exact legal
  | cons first tail ih => exact ih (first.firing.result (act signature) source) legal.2

private def prefixOK (source : World signature O) {members : List (Member signature O program)}
    (own : (bag members).AdmitsOwn (act signature) source)
    (p : { part // part ∈ prefixParts members }) : Bool :=
  let current := stateAfter (Action signature) source p.val.1
  let atOrder := Bag.admitsOwn_perm (act signature) (prefixParts_sound p.property).symm own
  let available := fits_after source p.val.1 p.val.2 atOrder.1 atOrder.2.1
  p.val.2.attach.all fun member =>
    (SymbolicFiring.evaluate (before := current) (selectedAt member.property available.1 available.2)).isSome

set_option maxHeartbeats 1200000 in
private theorem prefixOK_exact (source : World signature O) {members : List (Member signature O program)}
    (own : (bag members).AdmitsOwn (act signature) source) (p : { part // part ∈ prefixParts members }) :
    prefixOK source own p = true ↔
      ∀ m ∈ p.val.2, m.firing.Admits (act signature) (stateAfter (Action signature) source p.val.1) := by
  let atOrder := Bag.admitsOwn_perm (act signature) (prefixParts_sound p.property).symm own
  let available := fits_after source p.val.1 p.val.2 atOrder.1 atOrder.2.1
  let test := fun (member : { m // m ∈ p.val.2 }) => selectedAt member.property available.1 available.2
  change (p.val.2.attach.all fun m => (SymbolicFiring.evaluate (test m)).isSome) = true ↔ _
  rw [List.all_eq_true]
  constructor
  · intro verified m member
    exact (selected_exact (test ⟨m, member⟩)).mp (verified ⟨m, member⟩ (List.mem_attach _ _))
  · intro verified m _
    exact (selected_exact (test m)).mpr (verified m.val m.property)

/-- Check each prefix population once and each possible next member at
that population. A changed guard is still checked, even if it passed
at the entry snapshot. -/
def prefixesOK (source : World signature O) (members : List (Member signature O program))
    (own : (bag members).AdmitsOwn (act signature) source) : Bool :=
  (prefixParts members).attach.all (prefixOK source own)

theorem prefixesOK_exact (source : World signature O) (members : List (Member signature O program))
    (own : (bag members).AdmitsOwn (act signature) source) :
    prefixesOK source members own = true ↔ RuntimeRound (Action signature) source members := by
  simp only [prefixesOK, List.all_eq_true]
  constructor
  · intro checked
    apply RuleSyntax.StepWeb.Rounds.runtimeRound_of_fires (Action signature) own
    intro order allowed
    suffices ∀ (rest done : List (Member signature O program)), (done ++ rest).Perm members →
        FiresInOrder (Action signature) (stateAfter (Action signature) source done) rest from
      this order [] allowed
    intro rest
    induction rest with
    | nil => intros; trivial
    | cons first tail ih =>
      intro done possible
      obtain ⟨⟨left, right⟩, part, orderLeft, orderRight⟩ := prefixParts_cover possible
      have stillThere : first ∈ right := orderRight.mem_iff.mpr List.mem_cons_self
      let choice : { part // part ∈ prefixParts members } := ⟨(left, right), part⟩
      have choiceOK := (prefixOK_exact source own choice).mp (checked choice (List.mem_attach _ _)) first stillThere
      have initial := prefix_own source own (prefixParts_sound part)
      have equiv := prefix_equiv source initial orderLeft
      have firstOK := RuleSyntax.Scope.admits_of_congruent equiv.symm choiceOK
      have restOrder : ( (done ++ [first]) ++ tail).Perm members := by
        simpa only [List.append_assoc, List.singleton_append] using possible
      have continued := ih (done ++ [first]) restOrder
      have appendOne : ∀ (s : World signature O) (l : List (Member signature O program)),
          stateAfter (Action signature) s (l ++ [first]) =
            first.firing.result (act signature) (stateAfter (Action signature) s l) := by
        intro s l
        induction l generalizing s with
        | nil => rfl
        | cons _ _ ih => exact ih _
      rw [appendOne] at continued
      exact ⟨firstOK, continued⟩
  · intro round p _
    apply (prefixOK_exact source own p).mpr
    intro m present
    obtain ⟨l, r, eq⟩ := List.append_of_mem present
    have order : (p.val.1 ++ m :: (l ++ r)).Perm members := by
      apply (List.perm_middle.symm.append_left p.val.1).trans
      rw [← eq]
      exact prefixParts_sound p.property
    exact (suffix_of_fires source p.val.1 _ (round.2 _ order).1).1

private def equationCheck : Check (Term signature) → Bool
  | .equal .. => true
  | _ => false

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem equationCheck_exact (c : Check (Term signature)) :
    equationCheck c = true ↔ ∃ l r, c = Check.equal l r := by
  cases c <;> simp [equationCheck]

private def positiveRule (rule : RuleSyntax.Rule (Terms (Term signature))) : Bool :=
  rule.body.checks.all equationCheck && rule.collect.isEmpty

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem positiveRule_exact (rule : RuleSyntax.Rule (Terms (Term signature))) :
    positiveRule rule = true ↔ RuleSyntax.Scope.Positive rule := by
  simp only [positiveRule, Bool.and_eq_true, List.all_eq_true, equationCheck_exact,
    List.isEmpty_iff, RuleSyntax.Scope.Positive]

/-- Equation-only guards and no collects certify every order at once.
Other rounds share checks at prefixes with the same committed
population, without dropping a count or absence guard. -/
def roundOK (before : World signature O) (members : List (Member signature O program))
    (own : (bag members).AdmitsOwn (act signature) before) : Bool :=
  if members.all (fun member => positiveRule member.rule) then true else prefixesOK before members own

theorem roundOK_exact (before : World signature O) (members : List (Member signature O program))
    (own : (bag members).AdmitsOwn (act signature) before) :
    roundOK before members own = true ↔ RuntimeRound (Action signature) before members := by
  unfold roundOK
  by_cases monotone : members.all (fun member => positiveRule member.rule) = true
  · have positive : ∀ m ∈ members, RuleSyntax.Scope.Positive m.rule := fun m member =>
      (positiveRule_exact m.rule).mp (List.all_eq_true.mp monotone m member)
    rw [if_pos monotone]
    exact ⟨fun _ => RuleSyntax.StepWeb.Rounds.runtimeRound_of_admitsOwn (Action signature) positive own,
      fun _ => rfl⟩
  · rw [if_neg monotone, prefixesOK_exact]

/-- Executable reference for a proposed nonempty round. Own-admission
establishes the initial certificate. Failed intermediate guards cause a
refusal even if the simultaneous firing would succeed. -/
def evaluate (before : World signature O) (members : List (Member signature O program))
    (nonempty : members ≠ []) (fits : (bag members).Fits (act signature) before) :
    Option (Subst signature × World signature O) :=
  let trial : SymbolicBatch.Prepared (program := program) before := ⟨bag members, nonempty, fits⟩
  match checked : SymbolicBatch.evaluate .memberOwn trial with
  | none => none
  | some (answer, after) =>
    have own := ((SymbolicBatch.evaluate_exact .memberOwn trial answer after).mp checked).2.1
    if roundOK before members own then some (answer, after) else none

theorem evaluate_exact (before : World signature O) (members : List (Member signature O program))
    (nonempty : members ≠ []) (fits : (bag members).Fits (act signature) before)
    (answer : Subst signature) (after : World signature O) :
    evaluate before members nonempty fits = some (answer, after) ↔
      RuntimeRound (Action signature) before members ∧
      unifyTotal ((bag members).information (act signature) before) = some answer ∧
      after = (bag members).result (act signature) before := by
  unfold evaluate
  dsimp only
  split
  · rename_i noOwn
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨round, _, _⟩
      have own := RuleSyntax.StepWeb.Rounds.admitsOwn_of_runtimeRound (Action signature) round
      exact ((SymbolicBatch.refuses_exactly_when_not_admitted .memberOwn _).mp noOwn own).elim
  · rename_i found result checked
    have exactResult := (SymbolicBatch.evaluate_exact .memberOwn _ found result).mp checked
    by_cases orders : roundOK before members exactResult.2.1 = true
    · have round := (roundOK_exact _ _ exactResult.2.1).mp orders
      simp only [if_pos orders, Option.some.injEq, Prod.mk.injEq, round, true_and]
      rw [exactResult.1, ← exactResult.2.2, Option.some.injEq]
      exact and_congr Iff.rfl eq_comm
    · have refused : ¬RuntimeRound (Action signature) before members :=
        fun round => orders ((roundOK_exact _ _ exactResult.2.1).mpr round)
      simp [orders, refused]

end Mettapedia.Machines.TIsa.Derivation.SymbolicRound
