import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolPhaseReflection
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolScopeReflection
import Mettapedia.OSLF.Syntax.VariableArgumentRecognition
import Mettapedia.OSLF.Syntax.VariablePosition

/-!
# Computed private capabilities of a committed tuple protocol

A public rendezvous chooses its sender and receiver before these capabilities
are created. Each committed occurrence has two distinct intrinsic private name
positions, session and callback. Reindexing ordinary source terms into this
world cannot mention any of these positions. The placement has a computed
partial inverse, so actual directed firings retain their supplied endpoints.

The construction is bookkeeping over the existing scoped syntax, communication
rules and strengthening operation. It is not another transition relation.
Transporting the selected occurrences through arbitrary structural equations
requires the separate occurrence-provenance comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Capabilities

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

inductive Port where
  | callback
  | session
  deriving DecidableEq

def Port.offset : Port → Nat
  | .callback => 0
  | .session => 1

/-- A pair is allocated only for an already committed public rendezvous. -/
def privatePrefix : Nat → Ctx sig
  | 0 => []
  | n + 1 => .nm :: .nm :: privatePrefix n

/-- Occurrence positions retain duplicate calls and equal tuple fields. -/
def privateVar : (n : Nat) → Fin n → Port → Var (privatePrefix n) .nm
  | _n + 1, ⟨0, _⟩, .callback => .zero
  | _n + 1, ⟨0, _⟩, .session => .succ .zero
  | n + 1, ⟨i + 1, bound⟩, port =>
      .succ (.succ (privateVar n ⟨i, Nat.lt_of_succ_lt_succ bound⟩ port))

theorem privateVar_position : ∀ (n : Nat) (i : Fin n) (port : Port),
    (varIdx (privateVar n i port)).val = 2 * i.val + port.offset
  | n + 1, ⟨0, _⟩, .callback => rfl
  | n + 1, ⟨0, _⟩, .session => rfl
  | n + 1, ⟨i + 1, bound⟩, port => by
      change (varIdx (privateVar n ⟨i, Nat.lt_of_succ_lt_succ bound⟩ port)).val + 1 + 1 = _
      rw [privateVar_position]
      dsimp only
      omega

theorem privateVar_injective (n : Nat) (first second : Fin n)
    (firstPort secondPort : Port)
    (same : privateVar n first firstPort = privateVar n second secondPort) :
    first = second ∧ firstPort = secondPort := by
  have positions := congrArg (fun name => (varIdx name).val) same
  rw [privateVar_position, privateVar_position] at positions
  cases firstPort <;> cases secondPort <;> simp only [Port.offset] at positions
  all_goals try omega
  all_goals exact ⟨Fin.ext (by omega), rfl⟩

abbrev World (n : Nat) (Γ : Ctx sig) := privatePrefix n ++ Γ

def ambient {Γ : Ctx sig} (n : Nat) : Ren sig Γ (World n Γ) :=
  fun _ name => weakenVar (privatePrefix n) name

def key {Γ : Ctx sig} (n : Nat) (i : Fin n) (port : Port) :
    Var (World n Γ) .nm := injPrefix (privatePrefix n) (privateVar n i port)

def keyName {Γ : Ctx sig} (n : Nat) (i : Fin n) (port : Port) : Name (World n Γ) :=
  .var (key n i port)

@[simp] theorem key_new_callback {Γ : Ctx sig} (n : Nat) :
    key (Γ := Γ) (n + 1) ⟨0, Nat.succ_pos n⟩ .callback = .zero := rfl

@[simp] theorem key_new_session {Γ : Ctx sig} (n : Nat) :
    key (Γ := Γ) (n + 1) ⟨0, Nat.succ_pos n⟩ .session = .succ .zero := rfl

/-- Allocating one committed pair weakens every previously allocated name;
its owner position changes, but its identity and payload do not. -/
@[simp] theorem key_existing {Γ : Ctx sig} (n : Nat) (i : Fin n) (port : Port) :
    key (Γ := Γ) (n + 1) i.succ port = .succ (.succ (key n i port)) := rfl

theorem ambient_extend {Γ : Ctx sig} (n : Nat) (sort : Srt) (name : Var Γ sort) :
    ambient (Γ := Γ) (n + 1) sort name = .succ (.succ (ambient n sort name)) := rfl

/-- Channel equality determines both the committed occurrence and its port. -/
theorem key_injective {Γ : Ctx sig} (n : Nat) (first second : Fin n)
    (firstPort secondPort : Port)
    (same : key (Γ := Γ) n first firstPort = key n second secondPort) :
    first = second ∧ firstPort = secondPort := by
  have split := congrArg (splitVar (privatePrefix n)) same
  simp only [key, splitVar_injPrefix] at split
  exact privateVar_injective n first second firstPort secondPort (Sum.inl.inj split)

theorem keyName_iff {Γ : Ctx sig} (n : Nat) (first second : Fin n)
    (firstPort secondPort : Port) :
    keyName (Γ := Γ) n first firstPort = keyName n second secondPort ↔
      first = second ∧ firstPort = secondPort := by
  constructor
  · intro same
    exact key_injective n first second firstPort secondPort (Term.var.inj same)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem key_ne_ambient {Γ : Ctx sig} (n : Nat) (i : Fin n) (port : Port)
    (name : Var Γ .nm) : key n i port ≠ ambient n .nm name :=
  injPrefix_ne_weakenVar (privatePrefix n) (privateVar n i port) name

theorem sameVar_prefix_ambient : ∀ (bs Γ : Ctx sig)
    {firstSort secondSort : Srt} (first : Var bs firstSort) (second : Var Γ secondSort),
    sameVar (injPrefix bs first) (weakenVar bs second) = false
  | _ :: _, _, _, _, .zero, _ => rfl
  | _ :: rest, Γ, _, _, .succ first, second =>
      sameVar_prefix_ambient rest Γ first second

/-- Ordinary source code has no occurrence of any allocated protocol name,
even in the bodies below its own binders. -/
theorem ambient_has_no_private {Γ : Ctx sig} {sort : Srt} (n : Nat)
    (i : Fin n) (port : Port) (term : Term sig Γ sort) :
    countVar (key n i port) (rename (ambient n) term) = 0 :=
  countVar_rename_of_miss (ambient n) (key n i port)
    (fun _ name => sameVar_prefix_ambient (privatePrefix n) Γ
      (privateVar n i port) name) term

private theorem prefix_inverse_private : ∀ (bs Γ : Ctx sig)
    {sort : Srt} (name : Var bs sort),
    (Strengthener.ofWeakenPrefix sig (Γ := Γ) bs).un sort
      (injPrefix bs name) = none
  | _ :: _, _, _, .zero => rfl
  | _ :: rest, Γ, _, .succ name => prefix_inverse_private rest Γ name

/-- Place the two canonical private binders at one computed occurrence. -/
def placement {Γ : Ctx sig} (n : Nat) (i : Fin n) :
    Ren sig (.nm :: .nm :: Γ) (World n Γ) :=
  prependRen (key n i .callback) (prependRen (key n i .session) (ambient n))

theorem placement_new {Γ : Ctx sig} (n : Nat) :
    placement (Γ := Γ) (n + 1) ⟨0, Nat.succ_pos n⟩ =
      liftRen (ambient n) [.nm, .nm] := by
  funext sort name
  cases name with
  | zero => rfl
  | succ name => cases name <;> rfl

theorem placement_extend {Γ : Ctx sig} (n : Nat) (i : Fin n)
    (sort : Srt) (name : Var (.nm :: .nm :: Γ) sort) :
    placement (Γ := Γ) (n + 1) i.succ sort name =
      .succ (.succ (placement n i sort name)) := by
  cases name with
  | zero => exact key_existing n i .callback
  | succ name => cases name with
    | zero => exact key_existing n i .session
    | succ name => exact ambient_extend n sort name

/-- The actual syntax of all older actors is carried unchanged below the
new pair of private binders. -/
theorem placement_term_extend {Γ : Ctx sig} {sort : Srt} (n : Nat) (i : Fin n)
    (term : Term sig (.nm :: .nm :: Γ) sort) :
    rename (placement (n + 1) i.succ) term =
      weaken (t := Srt.nm) (weaken (t := Srt.nm) (rename (placement n i) term)) := by
  simp only [weaken, rename_comp]
  congr 1
  funext s name
  exact placement_extend n i s name

private def sessionInverse {Γ : Ctx sig} (n : Nat) (i : Fin n) :
    Strengthener (prependRen (key n i .session) (ambient (Γ := Γ) n)) :=
  (Strengthener.ofWeakenPrefix sig (privatePrefix n)).prepend (key n i .session)
    (prefix_inverse_private (privatePrefix n) Γ (privateVar n i .session))

/-- The inverse is computed by the existing strengthening operation. It
rejects every other occurrence's private names. -/
def placementInverse {Γ : Ctx sig} (n : Nat) (i : Fin n) :
    Strengthener (placement (Γ := Γ) n i) :=
  (sessionInverse n i).prepend (key n i .callback) (by
    have different : key (Γ := Γ) n i .callback ≠ key n i .session := by
      intro same
      have ports := (key_injective n i i .callback .session same).2
      cases ports
    simp only [sessionInverse, Strengthener.prepend, prependInverse,
      ↓reduceDIte, different, ↓reduceIte]
    rw [key, prefix_inverse_private]
    rfl)

/-- Every actual firing of the reindexed private phase has an actual
canonical preimage and exactly the supplied target endpoint. -/
theorem placement_actual_step {Γ : Ctx sig} (n : Nat) (i : Fin n)
    (source : Proc (.nm :: .nm :: Γ)) {endpoint : Proc (World n Γ)}
    (step : Step (rename (placement n i) source) endpoint) :
    ∃ canonical, Step source canonical ∧ rename (placement n i) canonical = endpoint :=
  ScopeReflection.reindexed_actual_step (placement n i) (placementInverse n i) source step

private theorem unary_step_channels {Γ : Ctx sig} (channel other datum : Name Γ)
    (body : Proc (.nm :: Γ)) {endpoint : Proc Γ}
    (step : Step (par (out1 channel datum) (inp1 other body)) endpoint) :
    channel = other := by
  cases step with
  | comm1 => rfl
  | parL _ impossible => cases impossible
  | parR _ impossible => cases impossible

/-- A selected private communication cannot cross committed occurrences or
cross the session/callback ports. -/
theorem private_communication_iff {Γ : Ctx sig} (n : Nat)
    (sender receiver : Fin n) (sendPort receivePort : Port)
    (datum : Name (World n Γ)) (body : Proc (.nm :: World n Γ))
    (endpoint : Proc (World n Γ)) :
    Step (par (out1 (keyName n sender sendPort) datum)
      (inp1 (keyName n receiver receivePort) body)) endpoint ↔
      sender = receiver ∧ sendPort = receivePort ∧ endpoint = inst body datum := by
  constructor
  · intro step
    have same := unary_step_channels _ _ _ _ step
    obtain ⟨rfl, rfl⟩ := (keyName_iff n sender receiver sendPort receivePort).1 same
    exact ⟨rfl, rfl, (unary_communication_iff _ datum body endpoint).1 step⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact .comm1 _ _ _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Capabilities
