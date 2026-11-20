import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms

/-!
# A rule that arrives as data fires directly: the relay

Over first-order atoms at one frame. The code system (`codes`) has the **relay** as code `0` and, for
every `n`, the rule `bump n` (take a token `n`, make a token `n + 1`) as code `n + 1`; the constant
`100 + k` denotes the code `k`.

**The relay** (`relay`) takes a message, a row labelled by its own unknown, and installs the rule
that the unknown denotes. Its spec names no code.

* `relay_admitted`, `relayed_holds`: for **every** code `k`, at the state that holds the relay and a
  message carrying `k`, the relay fires and the result holds an occurrence of the code `k`.
* `bump_admitted`, `bump_result_label`: the occurrence installed from the message carrying the code
  of `bump 1` then fires on the token `1` and makes the token `2`. Its firing is a firing of the
  present step of the rule `bump 1` (`RFiring.admits_plain`): no interpreter rule and no coded row
  takes part.
* `relay_runs`: the two firings, as two transitions of the candidate with no ambient program.

**Control** (`open_refused`): a message whose content nothing determines installs nothing. With the
message row labelled by an unknown that the knowledge does not bind, the relay is refused whatever
code the firing claims, since a solution may send the unknown elsewhere.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Relay

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Mettapedia.Logic.LP
open Examples (Tm X E x c shift)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## The code system -/

/-- Take a token `n`, make a token `n + 1`. -/
def bump (n : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[c n], [], [], [], [c (n + 1)]⟩, []⟩

/-- **The relay**: take a message `x` and install the rule that `x` denotes, persistently. -/
def relay : Spec Tm ℕ Unit :=
  ⟨PUnit.unit, ⟨[x], [], [], [], []⟩, [], [], [], [], [⟨x, [], .persistent, ()⟩], [], []⟩

/-- The code system: code `0` is the relay, code `n + 1` is `bump n`; the constant `100 + k`
denotes the code `k`. -/
def codes : Codes Tm ℕ Unit where
  unfold
    | 0 => relay
    | n + 1 => Spec.ofRule (bump n)
  denotes _ t k := t = c (100 + k)
  close _ _ _ := none

/-! ## The relay installs the code a message carries -/

/-- A message carrying the code `k` at row `0`, a token `1` at row `1`, and the relay held at
identity `0`. -/
def start (k : ℕ) : RState Tm ℕ ℕ ℕ Unit :=
  ⟨⟨PUnit.unit, [], {0, 1}, fun o => c (if o = 0 then 100 + k else 1)⟩, {0},
    fun _ => ⟨0, [], .persistent, ()⟩⟩

/-- The relay takes the message and installs the code `k` at identity `5`. -/
def relayFiring (k : ℕ) : RFiring ℕ ℕ E codes (start k) :=
  ⟨.held 0, PUnit.unit, shift, ⟨[0], [], []⟩, [], [5], [k], [], []⟩

theorem relay_information (k : ℕ) :
    (relayFiring k).information X = [(.var 1, c (100 + k))] := rfl

theorem relay_fresh (k : ℕ) : (relayFiring k).Fresh X := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t ((member | member | ⟨o, -, rfl⟩) | ⟨ρ, -, member⟩)
    · simp [start] at member
    · simp [start] at member
    · rfl
    · exact absurd member List.not_mem_nil
  · intro t member
    have inside : t ∈ relay.terms := member
    simp [relay, Spec.terms, Rule.terms] at inside
    subst inside
    rfl

/-- **The relay fires, for every code**: at the state holding the relay and a message carrying the
code `k`, the firing that installs `k` is admitted. -/
theorem relay_admitted (k : ℕ) : (relayFiring k).Admits X (∅ : Set ℕ) := by
  refine ⟨⟨relay_fresh k, ⟨List.nodup_singleton 0, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ⟨Finset.mem_singleton_self 0, rfl, rfl, List.nodup_singleton 5, rfl, ?_, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩⟩, ?_, ?_, ?_⟩
  · intro ρ inside held
    obtain rfl := List.mem_singleton.mp inside
    exact absurd (Finset.mem_singleton.mp held) (by decide)
  · apply enabled_of <;> simp [relayFiring, start]
  · rw [relay_information]
    exact ⟨PUnit.unit, fun _ => c (100 + k), fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · rw [relay_information]
    intro b σ solved
    have value : σ 1 = c (100 + k) := solved (.var 1, c (100 + k)) List.mem_cons_self
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro y member
      have inside : y ∈ [((⟨x, [], .persistent, ()⟩ : Install Tm Unit PUnit.unit), k)] := member
      obtain rfl := List.mem_singleton.mp inside
      exact value
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil

/-- **The result holds the code the message carried.** -/
theorem relayed_holds (k : ℕ) :
    ((relayFiring k).result X).held 5 = ⟨k, [], .persistent, ()⟩ := rfl

theorem relayed_mem_rules (k : ℕ) : 5 ∈ ((relayFiring k).result X).rules :=
  (RFiring.mem_result_rules _).mpr (Or.inr (List.mem_singleton_self 5))

/-! ## The installed rule fires as a rule -/

/-- The state after the relay received the code of `bump 1`. -/
def relayed : RState Tm ℕ ℕ ℕ Unit := (relayFiring 2).result X

theorem relayed_closed : relayed.Closed := by
  intro ρ inside
  rcases (RFiring.mem_result_rules _).mp inside with kept | made
  · rw [RFiring.kept_persistent (relayFiring 2) rfl rfl rfl] at kept
    obtain rfl := Finset.mem_singleton.mp kept
    rfl
  · obtain rfl := List.mem_singleton.mp made
    rfl

/-- The installed occurrence takes the token `1` at row `1` and makes row `7`. -/
def bumpFiring : RFiring ℕ ℕ E codes relayed :=
  ⟨.held 5, PUnit.unit, Subst.id atoms, ⟨[1], [], [7]⟩, [], [], [], [], []⟩

theorem bump_plain : bumpFiring.spec.Plain := Spec.plain_ofRule (bump 1)

theorem bump_information :
    bumpFiring.base.information X relayed.toState = [(.var 1, c 102), (c 1, c 1)] := rfl

/-- Its firing of the present step of `bump 1` is admitted. -/
theorem bump_base_admitted : bumpFiring.base.Admits X relayed.toState := by
  refine ⟨⟨?_, List.nodup_singleton 1, List.nodup_singleton 7, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · apply Examples.fresh_of_ground action relayed.toState bumpFiring.base
    intro t member σ
    have inside : t ∈ (bump 1).terms := member
    simp [bump, Rule.terms] at inside
    rcases inside with rfl | rfl <;> rfl
  · apply enabled_of <;> simp [bumpFiring, relayed, RFiring.result, relayFiring, start, fire,
      Selection.commit]
  · rw [bump_information]
    refine ⟨PUnit.unit, fun _ => c 102, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro b σ _
    refine ⟨?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil

/-- **The installed rule fires**: the occurrence made from the message is used like any held rule. -/
theorem bump_admitted : bumpFiring.Admits X (∅ : Set ℕ) :=
  (bumpFiring.admits_plain X relayed_closed bump_plain ∅).mpr
    ⟨bump_base_admitted, relayed_mem_rules 2, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- **It makes the token `2`.** -/
theorem bump_result_label : (bumpFiring.result X).label 7 = c 2 := rfl

/-- **Received, installed, fired**: two transitions of the candidate with no ambient program. -/
theorem relay_runs :
    Succ (rstep X ℕ ℕ E codes (∅ : Set ℕ)).toStep (start 2) relayed ∧
      Succ (rstep X ℕ ℕ E codes (∅ : Set ℕ)).toStep relayed (bumpFiring.result X) :=
  ⟨⟨relayFiring 2, relay_admitted 2, rfl⟩, ⟨bumpFiring, bump_admitted, rfl⟩⟩

/-- **The relay names no code**: it makes no rule from a code, and the one rule it installs is read
from its own unknown. -/
theorem relay_names_none : relay.makes = [] ∧ relay.installs.map Install.term = [x] :=
  ⟨rfl, rfl⟩

/-! ## Control: a message whose content nothing determines -/

/-- A message row labelled by an unknown that nothing binds, and the relay held. -/
def openStart : RState Tm ℕ ℕ ℕ Unit :=
  ⟨⟨PUnit.unit, [], {0}, fun _ => x⟩, {0}, fun _ => ⟨0, [], .persistent, ()⟩⟩

/-- The relay on the open message, claiming the code `k`. -/
def openFiring (k : ℕ) : RFiring ℕ ℕ E codes openStart :=
  ⟨.held 0, PUnit.unit, shift, ⟨[0], [], []⟩, [], [5], [k], [], []⟩

theorem open_information (k : ℕ) : (openFiring k).information X = [(.var 1, x)] := rfl

/-- **An undetermined message installs nothing**: whatever code is claimed, the firing is refused. -/
theorem open_refused (k : ℕ) : ¬ (openFiring k).Admits X (∅ : Set ℕ) := by
  intro admitted
  have asks := admitted.2.2.2
  rw [open_information] at asks
  have holds := asks PUnit.unit (fun _ => c (100 + k + 1)) (fun e member => by
    obtain rfl := List.mem_singleton.mp member
    rfl)
  have inside : ((⟨x, [], .persistent, ()⟩ : Install Tm Unit PUnit.unit), k) ∈
      (openFiring k).spec.installs.zip (openFiring k).installed := List.mem_singleton_self _
  have denoted : c (100 + k + 1) = c (100 + k) := holds.2.2.1 _ inside
  have same : 100 + k + 1 = 100 + k := Term.const.inj denoted
  omega

#print axioms relay_admitted
#print axioms relayed_holds
#print axioms relayed_closed
#print axioms bump_base_admitted
#print axioms bump_admitted
#print axioms bump_result_label
#print axioms relay_runs
#print axioms relay_names_none
#print axioms open_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Relay
