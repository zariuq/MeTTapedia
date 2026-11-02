import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingRuleLibrary

/-!
# Composing actual guarded rewriting runs with supplied request packets

A block records a finite batch of ordinary requests and a proof of the
existing process-step closure. Appending blocks uses the proved frame law for
these data-guarded rules. It does not add a proof execution relation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

abbrev RequestPacket := String × List Tm

def requestBag (requests : List RequestPacket) : Multiset Tm :=
  requests.map fun packet => requestValue packet.1 packet.2

theorem requestBag_append (first second : List RequestPacket) :
    requestBag (first ++ second) = requestBag first + requestBag second := by
  simp [requestBag]

structure Block (theory : Theory) (target : Context) (keys : List RuleKey) (initial : Multiset Tm) where
  requests : List RequestPacket
  produced : Multiset Tm
  execution : Relation.ReflTransGen (process theory target keys).Step
    (requestBag requests + initial) (initial + produced)

namespace Block

variable {theory : Theory} {target : Context} {keys : List RuleKey} {initial : Multiset Tm}

def empty (initial : Multiset Tm) : Block theory target keys initial :=
  ⟨[], 0, by simpa [requestBag] using
    (Relation.ReflTransGen.refl : Relation.ReflTransGen (process theory target keys).Step initial initial)⟩

def single (packet : RequestPacket) (result : Tm)
    (step : (process theory target keys).Step ({requestValue packet.1 packet.2} + initial) (initial + {result})) :
    Block theory target keys initial :=
  ⟨[packet], {result}, by simpa [requestBag] using Relation.ReflTransGen.single step⟩

def append (first : Block theory target keys initial)
    (second : Block theory target keys (initial + first.produced)) : Block theory target keys initial where
  requests := first.requests ++ second.requests
  produced := first.produced + second.produced
  execution := by
    have framed := process_run_frame first.execution (requestBag second.requests)
    have firstRun : Relation.ReflTransGen (process theory target keys).Step
        (requestBag (first.requests ++ second.requests) + initial)
        (requestBag second.requests + (initial + first.produced)) := by
      simpa [requestBag_append, add_assoc, add_left_comm, add_comm] using framed
    simpa [add_assoc] using firstRun.trans second.execution

theorem retains (block : Block theory target keys initial) {value : Tm} (member : value ∈ initial) :
    value ∈ initial + block.produced := Multiset.mem_add.mpr (Or.inl member)

theorem append_retains_first (first : Block theory target keys initial)
    (second : Block theory target keys (initial + first.produced)) {value : Tm}
    (member : value ∈ initial + first.produced) : value ∈ initial + (first.append second).produced := by
  simpa [append, add_assoc] using second.retains member

theorem append_contains_second (first : Block theory target keys initial)
    (second : Block theory target keys (initial + first.produced)) {value : Tm}
    (member : value ∈ initial + first.produced + second.produced) :
    value ∈ initial + (first.append second).produced := by
  simpa [append, add_assoc] using member

end Block

def hypothesisBag (target : Context) (hypotheses : List Preterm) : Multiset Tm :=
  hypotheses.map (proofValue target)

theorem requestBag_valid (theory : Theory) (target : Context) (hypotheses : List Preterm) (requests : List RequestPacket) :
    ∀ value ∈ requestBag requests,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
  intro value member
  obtain ⟨packet, _, rfl⟩ := List.mem_map.mp (show value ∈ requests.map (fun packet => requestValue packet.1 packet.2) from member)
  exact valid_request _ _ _ _ _ _ _

theorem hypothesisBag_valid (theory : Theory) (target : Context) (hypotheses : List Preterm) :
    ∀ value ∈ hypothesisBag target hypotheses,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
  intro value member
  obtain ⟨expression, assumed, rfl⟩ := List.mem_map.mp (show value ∈ hypotheses.map (proofValue target) from member)
  exact valid_proof (.hypothesis assumed)

/-- The acceptance-to-derivability direction is about reachability in the
actual finite guarded rewriting process. Requests initially carry no logical authority. -/
theorem reachable_proof_sound {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm)
    (keys : List RuleKey) (requests : List RequestPacket) {after : Multiset Tm} {expression : Preterm}
    (run : Relation.ReflTransGen (process theory target keys).Step
      (requestBag requests + hypothesisBag target hypotheses) after)
    (published : proofValue target expression ∈ after) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression := by
  have initial : ∀ value ∈ requestBag requests + hypothesisBag target hypotheses,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value := by
    intro value member
    rcases Multiset.mem_add.mp member with request | hypothesis
    · exact requestBag_valid theory target hypotheses requests value request
    · exact hypothesisBag_valid theory target hypotheses value hypothesis
  exact (process_run_preserves wellFormed formed hypotheses keys initial run _ published).1 expression rfl

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
