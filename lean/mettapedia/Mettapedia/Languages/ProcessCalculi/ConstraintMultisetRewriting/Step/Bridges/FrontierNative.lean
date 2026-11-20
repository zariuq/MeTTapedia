import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeCore

/-!
# A frontier controller storing native representatives

Leaves contain actual hosted states and active occurrence identities. Each
expansion certificate contains one admitted native invocation per enabled
compiler name and exact name coverage. Different names retain separate
children even when their native results agree. History words are not fields
of this runtime state or its expansion certificates.

This is the plain catalogue instance of FrontierNativeCore, whose controller
and proof-producing probe builder are shared with sequencing profiles.

Coverage is semantic evidence. A finite name bound does not decide negative
admission, and an incomplete search cannot construct a completed expansion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star}

abbrev Leaf := FrontierNativeCore.Leaf
abbrev Leaf.mk (state : HostState S) (active : Nat) : Leaf S := FrontierNativeCore.Leaf.mk state active
abbrev Leaf.state (leaf : Leaf S) := FrontierNativeCore.Leaf.state leaf
abbrev Leaf.active (leaf : Leaf S) := FrontierNativeCore.Leaf.active leaf
abbrev Valid := @FrontierNativeCore.Valid

variable (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)

/-- The plain profile of the common native catalogue. -/
def catalogue : FrontierNativeCore.Catalogue (translate N P) RuleName where
  lookup := ruleNamed N P
  support := FrontierNames.names P
  bounded := FrontierNames.rule_name_mem P N
  member := by
    intro name rule found
    cases name with
    | ret => cases found; exact retRule_mem N P
    | unmatched => cases found; exact unmatchedRule_mem N P
    | left => cases found; exact choiceLeftRule_mem N P
    | right => cases found; exact choiceRightRule_mem N P
    | eqn index =>
        obtain ⟨equation, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        exact schema_mem N P (List.mem_of_getElem? selected)

/-- The selected rule and physical effect are actual fields of the invocation. -/
abbrev Invocation (before : Leaf S) (name : RuleName) :=
  FrontierNativeCore.Invocation (catalogue N P) before name

def Invocation.after {before : Leaf S} {name : RuleName} (invocation : Invocation N P before name) : Leaf S :=
  ⟨invocation.firing.result (Interface.Frames.contextual S) before.state, invocation.afterActive⟩

theorem Invocation.fires {before : Leaf S} {name : RuleName} (invocation : Invocation N P before name) :
    FiresNamed N P name before.state before.active invocation.after.state invocation.after.active :=
  ⟨invocation.firing.rule, invocation.named, invocation.firing, rfl, invocation.admitted,
    invocation.taken, invocation.made, rfl⟩

theorem invocation_of_fires {before after : Leaf S} {name : RuleName}
    (fired : FiresNamed N P name before.state before.active after.state after.active) :
    ∃ invocation : Invocation N P before name, invocation.after = after := by
  obtain ⟨rule, named, firing, sameRule, admitted, taken, made, result⟩ := fired
  let invocation : Invocation N P before name :=
    ⟨firing, by rw [sameRule]; exact named, after.active, taken, made, admitted⟩
  refine ⟨invocation, ?_⟩
  rcases after with ⟨state, active⟩
  exact congrArg (fun state => Leaf.mk state active) result

def Enabled (before : Leaf S) (name : RuleName) : Prop := Nonempty (Invocation N P before name)

theorem enabled_iff_fires (before : Leaf S) (name : RuleName) :
    Enabled N P before name ↔ ∃ after : Leaf S,
      FiresNamed N P name before.state before.active after.state after.active := by
  constructor
  · rintro ⟨invocation⟩
    exact ⟨invocation.after, invocation.fires⟩
  · rintro ⟨after, fired⟩
    obtain ⟨invocation, _⟩ := invocation_of_fires N P fired
    exact ⟨invocation⟩

theorem enabled_name_mem {before : Leaf S} {name : RuleName} (enabled : Enabled N P before name) :
    name ∈ FrontierNames.names P := by
  obtain ⟨invocation⟩ := enabled
  exact FrontierNames.rule_name_mem P N invocation.named

/-- Coverage is a local condition on the native representative and its fixed indexed program. -/
abbrev Expansion (before : Leaf S) := FrontierNativeCore.Expansion (catalogue N P) before

def Expansion.children {before : Leaf S} (expansion : Expansion N P before) : Multiset (Leaf S) :=
  expansion.names.attach.val.map fun name => (expansion.invocation name.1 name.2).after

def Expansion.retire {before : Leaf S} (expansion : Expansion N P before) (old : Multiset (Leaf S)) :
    Multiset (Leaf S) := if expansion.names.card = 0 then before ::ₘ old else old

theorem Expansion.children_card {before : Leaf S} (expansion : Expansion N P before) :
    expansion.children.card = expansion.names.card := by
  rw [Expansion.children, Multiset.card_map]
  exact Multiset.card_attach

theorem Expansion.names_bounded {before : Leaf S} (expansion : Expansion N P before) :
    expansion.names ⊆ FrontierNames.names P :=
  fun name inside => enabled_name_mem N P ((expansion.complete name).mp inside)

/-- A complete semantic expansion exists because the indexed name set is finite.
This existence proof does not supply a computable negative-admission procedure. -/
noncomputable def expansion (before : Leaf S) : Expansion N P before :=
  FrontierNativeCore.expansion (catalogue N P) before

abbrev State (S : Signature) := Frontier.State (Leaf S)

abbrev Step : State S → State S → Prop :=
  FrontierNativeCore.Step (catalogue N P) (fun leaf => StateFinished N leaf.state leaf.active)

variable {N P} in
theorem Step.expand (before : Leaf S) (rest retired : Multiset (Leaf S))
    (valid : Valid before) (unfinished : ¬ StateFinished N before.state before.active)
    (chosen : Expansion N P before) :
    Step N P ⟨before ::ₘ rest, retired⟩ ⟨chosen.children + rest, Expansion.retire N P chosen retired⟩ :=
  FrontierNativeCore.Step.expand before rest retired valid unfinished chosen

def theory : Mettapedia.GSLT.GSLT :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT (State S) (Step N P)

noncomputable def answers (state : State S) : Multiset (Set (Term S Γ star)) :=
  Frontier.answers (fun leaf => StateFinished N leaf.state leaf.active)
    (fun leaf => stateAnswer N leaf.state leaf.active) state

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Invocation.fires
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.invocation_of_fires
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Expansion.children_card
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.expansion
