import Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsSteps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationStore

/-!
# The store plan of the π-calculus with sums

The π-calculus with sums is stored as its canonical blocks, its steps read off by a plan (`plan`):

- **Keys** (`keys`): a sum reacts on the channels of its inputs and outputs, and on the silent key when it has a
  silent summand.
- **Firing** (`fire`): two sums leave, for each input among the summands of the first and output on its channel among
  those of the second, the reception beside the output's continuation; one sum leaves the continuation of each of its
  silent summands.

A redex's parts share its channel, or the silent key (`keys_complete`), and what parts leave is exactly what the
redexes they make leave (`fire_sound`, `fire_complete`), so the generic store theorems apply.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsStore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (StorePlan)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsSteps (piSumReactions Redex sum recv send tau)

/-! ## Picking a member of a list -/

/-- The ways to pick one member of a list, with the members before and after it. -/
def picks {α : Type} : List α → List (List α × α × List α)
  | [] => []
  | first :: rest => ([], first, rest) :: (picks rest).map fun pick => (first :: pick.1, pick.2.1, pick.2.2)

theorem mem_picks {α : Type} : ∀ {list before after : List α} {chosen : α},
    (before, chosen, after) ∈ picks list ↔ list = before ++ chosen :: after
  | [], before, after, chosen => by simp [picks]
  | first :: rest, [], after, chosen => by
      simp only [picks, List.mem_cons, List.mem_map, Prod.mk.injEq, List.nil_append, List.cons.injEq]
      constructor
      · rintro (⟨-, rfl, rfl⟩ | ⟨pick, -, nonempty, -⟩)
        · exact ⟨rfl, rfl⟩
        · exact absurd nonempty (List.cons_ne_nil _ _)
      · rintro ⟨rfl, rfl⟩
        exact .inl ⟨trivial, rfl, rfl⟩
  | first :: rest, head :: tail, after, chosen => by
      simp only [picks, List.mem_cons, List.mem_map, Prod.mk.injEq, List.cons_append, List.cons.injEq]
      constructor
      · rintro (⟨empty, -, -⟩ | ⟨⟨before, picked, later⟩, member, ⟨rfl, rfl⟩, rfl, rfl⟩)
        · simp at empty
        · exact ⟨rfl, mem_picks.mp member⟩
      · rintro ⟨rfl, rfl⟩
        exact .inr ⟨⟨tail, chosen, after⟩, mem_picks.mpr rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

/-! ## Reading sums and guards -/

/-- The summands of a sum. -/
def summands? : Pattern → Option (List Pattern)
  | .apply label [.collection .hashBag guards none] => if label = "PiSum" then some guards else none
  | _ => none

theorem summands?_sum (guards : List Pattern) : summands? (sum guards) = some guards := by
  simp [summands?, sum]

theorem eq_sum_of_summands? {part : Pattern} {guards : List Pattern} (found : summands? part = some guards) :
    part = sum guards := by
  unfold summands? at found
  split at found
  · split_ifs at found with isSum
    cases found
    subst isSum
    rfl
  · cases found

/-- An input's channel and body. -/
def received? : Pattern → Option (Pattern × Pattern)
  | .apply label [channel, .lambda none body] => if label = "PiRecv" then some (channel, body) else none
  | _ => none

theorem eq_recv_of_received? {guard channel body : Pattern} (found : received? guard = some (channel, body)) :
    guard = recv channel body := by
  unfold received? at found
  split at found
  · split_ifs at found with isRecv
    cases found
    subst isRecv
    rfl
  · cases found

/-- An output's channel, datum and continuation. -/
def sent? : Pattern → Option (Pattern × Pattern × Pattern)
  | .apply label [channel, datum, continuation] => if label = "PiSend" then some (channel, datum, continuation) else none
  | _ => none

theorem eq_send_of_sent? {guard channel datum continuation : Pattern}
    (found : sent? guard = some (channel, datum, continuation)) : guard = send channel datum continuation := by
  unfold sent? at found
  split at found
  · split_ifs at found with isSend
    cases found
    subst isSend
    rfl
  · cases found

/-- A silent summand's continuation. -/
def silent? : Pattern → Option Pattern
  | .apply label [continuation] => if label = "PiTau" then some continuation else none
  | _ => none

theorem eq_tau_of_silent? {guard continuation : Pattern} (found : silent? guard = some continuation) :
    guard = tau continuation := by
  unfold silent? at found
  split at found
  · split_ifs at found with isTau
    cases found
    subst isTau
    rfl
  · cases found

/-- The key of a summand: an input's or an output's channel, or the silent key. -/
def guardKey? : Pattern → Option (Option Pattern)
  | .apply label [channel, _] => if label = "PiRecv" then some (some channel) else none
  | .apply label [channel, _, _] => if label = "PiSend" then some (some channel) else none
  | .apply label [_] => if label = "PiTau" then some none else none
  | _ => none

/-! ## The plan -/

/-- **The keys of a component**: the channels of a sum's inputs and outputs, and the silent key for its silent
summands. -/
def keys (component : Pattern) : List (Option Pattern) :=
  match summands? component with
  | some guards => guards.filterMap guardKey?
  | none => []

/-- **What parts leave**: two sums, each input of the first with each output on its channel in the second; one sum,
each of its silent summands. -/
def fire : List Pattern → List (List Pattern)
  | [part] =>
      match summands? part with
      | some guards => (picks guards).filterMap fun pick => (silent? pick.2.1).map fun continuation => [continuation]
      | none => []
  | [first, second] =>
      match summands? first, summands? second with
      | some receivers, some senders =>
          (picks receivers).flatMap fun receiver => (picks senders).filterMap fun sender =>
            match received? receiver.2.1, sent? sender.2.1 with
            | some (channel, body), some (channel', datum, continuation) =>
                if channel = channel' then some [instantiateBVar datum body, continuation] else none
            | _, _ => none
      | _, _ => []
  | _ => []

theorem fire_sound {parts result : List Pattern} (fired : result ∈ fire parts) :
    ∃ redex, piSumReactions.parts redex = parts ∧ piSumReactions.result redex = result := by
  match parts, fired with
  | [], fired => simp [fire] at fired
  | [part], fired =>
      simp only [fire] at fired
      split at fired
      · rename_i guards found
        obtain ⟨⟨before, chosen, after⟩, inPicks, picked⟩ := List.mem_filterMap.mp fired
        obtain ⟨continuation, isSilent, rfl⟩ := Option.map_eq_some_iff.mp picked
        simp only at isSilent
        refine ⟨.silent continuation before after, ?_, rfl⟩
        show [sum (before ++ tau continuation :: after)] = [part]
        rw [eq_sum_of_summands? found, mem_picks.mp inPicks, eq_tau_of_silent? isSilent]
      · simp at fired
  | [first, second], fired =>
      simp only [fire] at fired
      split at fired
      · rename_i receivers senders firstFound secondFound
        obtain ⟨⟨before, receiver, after⟩, receiverIn, inner⟩ := List.mem_flatMap.mp fired
        obtain ⟨⟨before', sender, after'⟩, senderIn, matched⟩ := List.mem_filterMap.mp inner
        simp only at matched
        split at matched
        · rename_i channel body channel' datum continuation isReceived isSent
          split_ifs at matched with sameChannel
          cases matched
          subst sameChannel
          refine ⟨.comm channel body datum continuation before after before' after', ?_, rfl⟩
          show [sum (before ++ recv channel body :: after), sum (before' ++ send channel datum continuation :: after')] =
            [first, second]
          rw [eq_sum_of_summands? firstFound, eq_sum_of_summands? secondFound, mem_picks.mp receiverIn,
            mem_picks.mp senderIn, eq_recv_of_received? isReceived, eq_send_of_sent? isSent]
        · cases matched
      · simp at fired
  | _ :: _ :: _ :: _, fired => simp [fire] at fired

theorem fire_complete (redex : Redex) : piSumReactions.result redex ∈ fire (piSumReactions.parts redex) := by
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      show [instantiateBVar datum body, continuation] ∈
        fire [sum (before ++ recv channel body :: after), sum (before' ++ send channel datum continuation :: after')]
      simp only [fire, summands?_sum]
      refine List.mem_flatMap.mpr ⟨(before, recv channel body, after), mem_picks.mpr rfl, ?_⟩
      refine List.mem_filterMap.mpr ⟨(before', send channel datum continuation, after'), mem_picks.mpr rfl, ?_⟩
      simp [received?, sent?, recv, send]
  | silent continuation before after =>
      show [continuation] ∈ fire [sum (before ++ tau continuation :: after)]
      simp only [fire, summands?_sum]
      refine List.mem_filterMap.mpr ⟨(before, tau continuation, after), mem_picks.mpr rfl, ?_⟩
      simp [silent?, tau]

theorem keys_complete (redex : Redex) (_ : piSumReactions.parts redex ≠ []) :
    ∃ key, ∀ part ∈ piSumReactions.parts redex, key ∈ keys part := by
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      refine ⟨some channel, fun part member => ?_⟩
      change part ∈ [sum (before ++ recv channel body :: after),
        sum (before' ++ send channel datum continuation :: after')] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp only [keys, summands?_sum]
        exact List.mem_filterMap.mpr ⟨recv channel body, by simp, by simp [guardKey?, recv]⟩
      · simp only [keys, summands?_sum]
        exact List.mem_filterMap.mpr ⟨send channel datum continuation, by simp, by simp [guardKey?, send]⟩
  | silent continuation before after =>
      refine ⟨none, fun part member => ?_⟩
      change part ∈ [sum (before ++ tau continuation :: after)] at member
      rw [List.mem_singleton] at member
      subst member
      simp only [keys, summands?_sum]
      exact List.mem_filterMap.mpr ⟨tau continuation, by simp, by simp [guardKey?, tau]⟩

/-- **The store plan of the π-calculus with sums.** -/
def plan : StorePlan piSumReactions (Option Pattern) where
  keys := keys
  fire := fire
  fire_sound := fire_sound
  fire_complete := fire_complete
  keys_complete := keys_complete

end Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsStore
