import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# One native frontier controller for finite named rule catalogues

The catalogue supplies a lookup, its finite support and rule membership.
No source-step or correspondence field occurs. Every expansion carries actual
admitted firings and exact name coverage. Pending probes cannot certify an
empty expansion. Different names may select the same concrete rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNativeCore

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Name : Type} {Prog : CProgram S}

structure Catalogue (Prog : CProgram S) (Name : Type) where
  lookup : Name → Option (CRule S)
  support : Finset Name
  member : ∀ {name rule}, lookup name = some rule → rule ∈ Prog
  bounded : ∀ {name rule}, lookup name = some rule → name ∈ support

structure Leaf (S : Signature) where
  state : HostState S
  active : Nat

def Valid (leaf : Leaf S) : Prop :=
  leaf.active ∈ leaf.state.present ∧ (Interface.Frames.contextual S).Solvable leaf.state.knowledge

variable (catalogue : Catalogue Prog Name)

/-- The selected rule and physical effect are actual fields of the invocation. -/
structure Invocation (before : Leaf S) (name : Name) where
  firing : RuleSyntax.Firing Nat (RuleSyntax.Contextual.declarations S) Prog before.state.frame
  named : catalogue.lookup name = some firing.rule
  afterActive : Nat
  taken : firing.selection.taken = [before.active]
  made : firing.selection.made = [afterActive]
  admitted : firing.Admits (Interface.Frames.contextual S) before.state

def Invocation.after {before : Leaf S} {name : Name} (invocation : Invocation catalogue before name) : Leaf S :=
  ⟨invocation.firing.result (Interface.Frames.contextual S) before.state, invocation.afterActive⟩

def Fires (name : Name) (before after : Leaf S) : Prop :=
  ∃ rule, catalogue.lookup name = some rule ∧
    FiresAt Prog rule before.state before.active after.state after.active

theorem Invocation.fires {before : Leaf S} {name : Name} (invocation : Invocation catalogue before name) :
    Fires catalogue name before invocation.after :=
  ⟨invocation.firing.rule, invocation.named, invocation.firing, rfl, invocation.admitted,
    invocation.taken, invocation.made, rfl⟩

theorem invocation_of_fires {before after : Leaf S} {name : Name}
    (fired : Fires catalogue name before after) :
    ∃ invocation : Invocation catalogue before name, invocation.after = after := by
  obtain ⟨rule, named, firing, sameRule, admitted, taken, made, result⟩ := fired
  let invocation : Invocation catalogue before name :=
    ⟨firing, by rw [sameRule]; exact named, after.active, taken, made, admitted⟩
  refine ⟨invocation, ?_⟩
  rcases after with ⟨state, active⟩
  exact congrArg (fun state => Leaf.mk state active) result

def Enabled (before : Leaf S) (name : Name) : Prop := Nonempty (Invocation catalogue before name)

theorem enabled_iff_fires (before : Leaf S) (name : Name) :
    Enabled catalogue before name ↔ ∃ after : Leaf S,
      Fires catalogue name before after := by
  constructor
  · rintro ⟨invocation⟩
    exact ⟨invocation.after, invocation.fires⟩
  · rintro ⟨after, fired⟩
    obtain ⟨invocation, _⟩ := invocation_of_fires catalogue fired
    exact ⟨invocation⟩

theorem enabled_name_mem {before : Leaf S} {name : Name} (enabled : Enabled catalogue before name) :
    name ∈ catalogue.support := by
  obtain ⟨invocation⟩ := enabled
  exact catalogue.bounded invocation.named

/-- Coverage is a local condition on the native representative and its fixed indexed program. -/
structure Expansion (before : Leaf S) where
  names : Finset Name
  complete : ∀ name, name ∈ names ↔ Enabled catalogue before name
  invocation : (name : Name) → name ∈ names → Invocation catalogue before name

def Expansion.children {before : Leaf S} (expansion : Expansion catalogue before) : Multiset (Leaf S) :=
  expansion.names.attach.val.map fun name => (expansion.invocation name.1 name.2).after

def Expansion.retire {before : Leaf S} (expansion : Expansion catalogue before) (old : Multiset (Leaf S)) :
    Multiset (Leaf S) := if expansion.names.card = 0 then before ::ₘ old else old

theorem Expansion.children_card {before : Leaf S} (expansion : Expansion catalogue before) :
    expansion.children.card = expansion.names.card := by
  rw [Expansion.children, Multiset.card_map]
  exact Multiset.card_attach

theorem Expansion.names_bounded {before : Leaf S} (expansion : Expansion catalogue before) :
    expansion.names ⊆ catalogue.support :=
  fun name inside => enabled_name_mem catalogue ((expansion.complete name).mp inside)

/-- A complete semantic expansion exists because the indexed name set is finite.
This existence proof does not supply a computable negative-admission procedure. -/
noncomputable def expansion (before : Leaf S) : Expansion catalogue before := by
  classical
  let names := (catalogue.support).filter (Enabled catalogue before)
  have complete : ∀ name, name ∈ names ↔ Enabled catalogue before name := by
    intro name
    exact ⟨fun inside => (Finset.mem_filter.mp inside).2,
      fun enabled => Finset.mem_filter.mpr ⟨enabled_name_mem catalogue enabled, enabled⟩⟩
  exact ⟨names, complete, fun name inside => Classical.choice ((complete name).mp inside)⟩

abbrev State (S : Signature) := Frontier.State (Leaf S)

inductive Step (finished : Leaf S → Prop) : State S → State S → Prop
  | expand (before : Leaf S) (rest retired : Multiset (Leaf S))
      (valid : Valid before) (unfinished : ¬ finished before)
      (chosen : Expansion catalogue before) :
      Step finished ⟨before ::ₘ rest, retired⟩ ⟨chosen.children + rest, Expansion.retire catalogue chosen retired⟩

def theory (finished : Leaf S → Prop) : Mettapedia.GSLT.GSLT :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT (State S) (Step catalogue finished)

theorem Step.frame {finished : Leaf S → Prop} {before after : State S}
    (moved : Step catalogue finished before after) (context : Multiset (Leaf S)) :
    Step catalogue finished ⟨before.leaves + context, before.retired⟩
      ⟨after.leaves + context, after.retired⟩ := by
  cases moved with
  | expand leaf rest retired valid unfinished chosen =>
      simpa only [Multiset.cons_add, add_assoc] using
        (Step.expand leaf (rest + context) retired valid unfinished chosen)

universe uPending

variable {catalogue} {Pending : Type uPending} {before : Leaf S} {name : Name}

abbrev ProbeResult (Pending : Type uPending) (catalogue : Catalogue Prog Name) (before : Leaf S) (name : Name) :=
  Except Pending (Sum (Invocation catalogue before name) (PLift (¬ Enabled catalogue before name)))

def ProbeResult.accepted : ProbeResult Pending catalogue before name → Bool
  | .ok (.inl _) => true
  | _ => false

def ProbeResult.settled : ProbeResult Pending catalogue before name → Bool
  | .ok _ => true
  | .error _ => false

def ProbeResult.verdict : ProbeResult Pending catalogue before name → Search.Outcome.Verdict
  | .ok (.inl _) => .commit
  | .ok (.inr _) => .refuted
  | .error _ => .suspended

def ProbeResult.invocation (reply : ProbeResult Pending catalogue before name)
    (accepted : reply.accepted = true) : Invocation catalogue before name := by
  cases reply with
  | error reason => cases accepted
  | ok result =>
      cases result with
      | inl invocation => exact invocation
      | inr refuted => cases accepted

theorem ProbeResult.accepted_sound (reply : ProbeResult Pending catalogue before name)
    (accepted : reply.accepted = true) : Enabled catalogue before name :=
  ⟨reply.invocation accepted⟩

theorem ProbeResult.enabled_accepted (reply : ProbeResult Pending catalogue before name)
    (ready : reply.settled = true) (enabled : Enabled catalogue before name) : reply.accepted = true := by
  cases reply with
  | error reason => cases ready
  | ok result =>
      cases result with
      | inl invocation => rfl
      | inr refuted => exact False.elim (refuted.down enabled)

theorem ProbeResult.refuted_sound (reply : ProbeResult Pending catalogue before name)
    (refused : reply.verdict = .refuted) : ¬ Enabled catalogue before name := by
  cases reply with
  | error reason => cases refused
  | ok result =>
      cases result with
      | inl invocation => cases refused
      | inr refuted => exact refuted.down

variable (catalogue)

def Ready (probe : (name : Name) → ProbeResult Pending catalogue before name) : Prop :=
  ∀ name ∈ catalogue.support, (probe name).settled = true

def acceptedNames (probe : (name : Name) → ProbeResult Pending catalogue before name) : Finset Name :=
  (catalogue.support).filter fun name => (probe name).accepted = true

/-- A finite builder from actual supplied decisions. Positive entries carry their native data;
negative entries carry refutations. The ready condition rejects every pending entry. -/
def fromProbes (probe : (name : Name) → ProbeResult Pending catalogue before name)
    (ready : Ready catalogue probe) : Expansion catalogue before where
  names := acceptedNames catalogue probe
  complete name := by
    constructor
    · intro member
      exact (probe name).accepted_sound (Finset.mem_filter.mp member).2
    · intro enabled
      have supported := enabled_name_mem catalogue enabled
      exact Finset.mem_filter.mpr ⟨supported, (probe name).enabled_accepted (ready name supported) enabled⟩
  invocation name member := (probe name).invocation (Finset.mem_filter.mp member).2

theorem fromProbes_names (probe : (name : Name) → ProbeResult Pending catalogue before name)
    (ready : Ready catalogue probe) : (fromProbes catalogue probe ready).names = acceptedNames catalogue probe := rfl

/-- A pending supported query prevents this probe family from certifying coverage.
It says nothing about whether another procedure could complete the expansion. -/
theorem pending_not_ready (probe : (name : Name) → ProbeResult Pending catalogue before name)
    {name : Name} {reason : Pending} (supported : name ∈ catalogue.support)
    (pending : probe name = .error reason) : ¬ Ready catalogue probe := by
  intro ready
  have settled := ready name supported
  rw [pending] at settled
  cases settled

theorem pending_status (reason : Pending) :
    (ProbeResult.verdict (.error reason : ProbeResult Pending catalogue before name)) = .suspended := rfl

theorem pending_is_not_refuted (reason : Pending) :
    (ProbeResult.verdict (.error reason : ProbeResult Pending catalogue before name)) ≠ .refuted := by
  intro impossible
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNativeCore
