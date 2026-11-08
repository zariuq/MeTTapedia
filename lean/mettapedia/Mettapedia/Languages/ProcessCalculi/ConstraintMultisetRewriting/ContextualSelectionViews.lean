import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivationScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshening

/-!
# Contextual views of selected occurrence uses

The rule and each selected take/read port are freshened with their reserved
scopes. One whole row uses one assignment, preserving repeated-variable
aliases. Explicit captures keep their existing identities. A row consisting
only of captured/shared variables therefore has the same view at every port.

The physical selection is the input index of the prepared views: no read is
turned into a new physical occurrence. This prepares terms and a scope
ledger; step admission, guards and theorem provenance are not defined here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViews

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

abbrev source := ContextualFreshening.declarations locals captures
abbrev target := ContextualFreshening.scopedDeclarations locals captures

structure Prepared (selection : Selection O) (context : Ctx S) (sort : S.Srt) where
  rule : RuleInstance (Term (signature S (target locals captures)) context sort)
  taken : Fin selection.taken.length → Term (signature S (target locals captures)) context sort
  read : Fin selection.read.length → Term (signature S (target locals captures)) context sort
  occupied : Finset Nat

def termAtPort (occupied : Finset Nat) {size : Nat}
    (port : Fin size) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (source locals captures)) Γ sort) :
    Term (signature S (target locals captures)) Γ sort :=
  ContextualFreshening.termAt locals captures (ContextualActivationScopes.scopeAt occupied port) term

def prepare (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (label : O → Term (signature S (source locals captures)) Γ sort) :
    Prepared locals captures selection Γ sort where
  rule := ContextualFreshening.ruleAt locals captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)) rule
  taken position := termAtPort locals captures occupied
    (ContextualActivationScopes.takePort selection position) (label (selection.taken.get position))
  read position := termAtPort locals captures occupied
    (ContextualActivationScopes.readPort selection position) (label (selection.read.get position))
  occupied := ContextualActivationScopes.after occupied selection

theorem termAtPort_injective (occupied : Finset Nat) {size : Nat}
    (port : Fin size) {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (termAtPort locals captures occupied port (Γ := Γ) (sort := sort)) :=
  ContextualFreshening.termAt_injective locals captures _

theorem local_scope (occupied : Finset Nat) {size : Nat}
    (port : Fin size) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (source locals captures)) Γ sort) (name : ScopedVar Local)
    (member : Sum.inl name ∈ support (termAtPort locals captures occupied port term)) :
    name.scope = ContextualActivationScopes.scopeAt occupied port :=
  ContextualFreshening.local_scope locals captures _ term name member

theorem captured_iff (occupied : Finset Nat) {size : Nat}
    (port : Fin size) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S (source locals captures)) Γ sort) (name : Shared) :
    Sum.inr name ∈ support (termAtPort locals captures occupied port term) ↔
      Sum.inr name ∈ support term :=
  ContextualFreshening.captured_iff locals captures _ term name

theorem different_ports_only_share_captures (occupied : Finset Nat) {size : Nat}
    {first second : Fin size} (different : first ≠ second)
    {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S (source locals captures)) Γ sort)
    (name : ScopedVar Local ⊕ Shared)
    (inLeft : name ∈ support (termAtPort locals captures occupied first left))
    (inRight : name ∈ support (termAtPort locals captures occupied second right)) :
    ∃ sharedName : Shared, name = .inr sharedName :=
  ContextualFreshening.different_activations_only_share_captures locals captures
    (ContextualActivationScopes.different_ports_have_different_scopes occupied different)
    left right name inLeft inRight

def capturedSource : Assignment captures (source locals captures) :=
  fun name => generator (source locals captures) (.inr name)

def capturedTarget : Assignment captures (target locals captures) :=
  fun name => generator (target locals captures) (.inr name)

theorem shared_value_at_port (occupied : Finset Nat) {size : Nat}
    (port : Fin size) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) :
    termAtPort locals captures occupied port (instantiate (capturedSource locals captures) value) =
      instantiate (capturedTarget locals captures) value := by
  rw [termAtPort, ContextualFreshening.termAt, instantiate_comp]
  have same : (fun name => instantiate
      (ContextualFreshening.assignment locals captures (ContextualActivationScopes.scopeAt occupied port))
      (capturedSource locals captures name)) = capturedTarget locals captures := by
    funext name
    exact instantiate_generator
      (ContextualFreshening.assignment locals captures (ContextualActivationScopes.scopeAt occupied port))
      (Sum.inr name)
  rw [same]

theorem shared_value_does_not_change_between_ports (occupied : Finset Nat) {size : Nat}
    (first second : Fin size) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) :
    termAtPort locals captures occupied first (instantiate (capturedSource locals captures) value) =
      termAtPort locals captures occupied second (instantiate (capturedSource locals captures) value) := by
  rw [shared_value_at_port, shared_value_at_port]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViews
