import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger
import Mathlib.Algebra.BigOperators.Fin

/-!
# A finite common inventory of fresh contextual event-use scopes

The finite port family contains one rule port and every take/read port of
each indexed event. Its computed enumeration gives globally distinct scopes
above the complete incoming ledger. This allocates views in the existing
contextual term family; it does not declare any firing or execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewScopes

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualActivationScopes

variable {S : Signature} {Local Shared O : Type} {n : Nat}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  (selections : Fin n → Selection O)

abbrev UsePort := (event : Fin n) × ContextualActivationScopes.Port (selections event)

def total : Nat := ∑ event : Fin n, count (selections event)

def index : UsePort selections ≃ Fin (total selections) := finSigmaFinEquiv

def scope (occupied : Finset Nat) (port : UsePort selections) : Nat :=
  scopeAt occupied (index selections port)

def reserved (occupied : Finset Nat) : Finset Nat :=
  Finset.Ico (start occupied) (start occupied + total selections)

def after (occupied : Finset Nat) : Finset Nat := occupied ∪ reserved selections occupied

theorem scope_injective (occupied : Finset Nat) : Function.Injective (scope selections occupied) := by
  intro first second same
  exact (index selections).injective (at_injective occupied _ same)

theorem scope_fresh (occupied : Finset Nat) (port : UsePort selections) :
    scope selections occupied port ∉ occupied := at_fresh occupied (index selections port)

theorem scope_mem_reserved (occupied : Finset Nat) (port : UsePort selections) :
    scope selections occupied port ∈ reserved selections occupied := by
  rw [reserved, Finset.mem_Ico]
  have bounded := (index selections port).isLt
  dsimp [scope, scopeAt]
  omega

theorem reserved_disjoint (occupied : Finset Nat) : Disjoint (reserved selections occupied) occupied := by
  apply Finset.disjoint_left.mpr
  intro value member old
  have lower := (Finset.mem_Ico.mp member).1
  have upper := occupied_lt_start occupied old
  omega

theorem reserved_card (occupied : Finset Nat) : (reserved selections occupied).card = total selections := by
  simp [reserved]

theorem old_scopes_retained (occupied : Finset Nat) : occupied ⊆ after selections occupied :=
  Finset.subset_union_left

theorem every_port_is_retained (occupied : Finset Nat) (port : UsePort selections) :
    scope selections occupied port ∈ after selections occupied :=
  Finset.mem_union_right _ (scope_mem_reserved selections occupied port)

def ruleUse (event : Fin n) : UsePort selections := ⟨event, rulePort (selections event)⟩
def takeUse (event : Fin n) (port : Fin (selections event).taken.length) : UsePort selections :=
  ⟨event, takePort (selections event) port⟩
def readUse (event : Fin n) (port : Fin (selections event).read.length) : UsePort selections :=
  ⟨event, readPort (selections event) port⟩

theorem different_events_have_different_scopes (occupied : Finset Nat)
    {first second : Fin n} (different : first ≠ second)
    (left : ContextualActivationScopes.Port (selections first))
    (right : ContextualActivationScopes.Port (selections second)) :
    scope selections occupied ⟨first, left⟩ ≠ scope selections occupied ⟨second, right⟩ := by
  intro same
  exact different (congrArg Sigma.fst (scope_injective selections occupied same))

theorem distinct_read_ports_have_different_scopes (occupied : Finset Nat) (event : Fin n)
    {first second : Fin (selections event).read.length} (different : first ≠ second) :
    scope selections occupied (readUse selections event first) ≠
      scope selections occupied (readUse selections event second) := by
  intro same
  have sameUse := scope_injective selections occupied same
  have samePort : readPort (selections event) first = readPort (selections event) second := by
    exact eq_of_heq (Sigma.mk.inj sameUse).2
  exact different (readPort_injective (selections event) samePort)

def openTerm (occupied : Finset Nat) (port : UsePort selections) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :
    Term (signature S (ContextualSelectionViews.target locals captures)) Γ sort :=
  ContextualFreshening.termAt locals captures (scope selections occupied port) value

theorem openTerm_injective (occupied : Finset Nat) (port : UsePort selections)
    {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (openTerm locals captures selections occupied port (Γ := Γ) (sort := sort)) :=
  ContextualFreshening.termAt_injective locals captures _

theorem different_ports_only_share_captures (occupied : Finset Nat)
    {first second : UsePort selections} (different : first ≠ second)
    {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort)
    (name : ScopedVar Local ⊕ Shared)
    (inLeft : name ∈ support (openTerm locals captures selections occupied first left))
    (inRight : name ∈ support (openTerm locals captures selections occupied second right)) :
    ∃ sharedName : Shared, name = .inr sharedName :=
  ContextualFreshening.different_activations_only_share_captures locals captures
    (fun same => different (scope_injective selections occupied same)) left right name inLeft inRight

theorem captures_unchanged (occupied : Finset Nat) (port : UsePort selections)
    {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) (name : Shared) :
    Sum.inr name ∈ support (openTerm locals captures selections occupied port value) ↔
      Sum.inr name ∈ support value :=
  ContextualFreshening.captured_iff locals captures _ value name

def prepared (occupied : Finset Nat) (event : Fin n) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    ContextualSelectionViews.Prepared locals captures (selections event) Γ sort where
  rule := rule.map (openTerm locals captures selections occupied (ruleUse selections event))
  taken port := openTerm locals captures selections occupied (takeUse selections event port)
    (ContextualStoredRows.asTemplate locals captures (rows ((selections event).taken.get port)))
  read port := openTerm locals captures selections occupied (readUse selections event port)
    (ContextualStoredRows.asTemplate locals captures (rows ((selections event).read.get port)))
  occupied := after selections occupied

theorem prepared_read_is_the_original_schema_view (occupied : Finset Nat) (event : Fin n)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (port : Fin (selections event).read.length) :
    (prepared locals captures selections occupied event rule rows).read port =
      ContextualStoredRows.viewAt locals captures
        (scope selections occupied (readUse selections event port))
        (rows ((selections event).read.get port)) :=
  (ContextualStoredRows.viewAt_eq_freshening locals captures _ _).symm

theorem shared_read_keeps_its_shared_identity (occupied : Finset Nat) (event : Fin n)
    {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) (port : Fin (selections event).read.length) :
    ContextualStoredRows.viewAt locals captures
      (scope selections occupied (readUse selections event port)) (.shared value) =
        instantiate (ContextualSelectionViews.capturedTarget locals captures) value := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewScopes
