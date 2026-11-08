import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationPlan

/-!
# Source clause variables enter the actual activation frame

The source has separate query variables, per-use stored-row variables and
captures. The native private bank adds query declarations to the existing
row bank. Its activation scopes are allocated from the current endpoint.
The maps below preserve the source terms, their object binders and exact
capture identities; unused native declarations stay genuinely unused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseFrames

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualConjunctiveQueries ContextualGuardMatching

variable {S : Signature} {Query Local Shared O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

abbrev bank : Local ⊕ Query → MetaArity S := Sum.elim locals queries
abbrev nativeRaw := ContextualSelectionViews.source (bank queries locals) captures
abbrev nativeActive := ContextualSelectionViews.target (bank queries locals) captures

def actor : Assignment (queryFamily queries captures) (nativeRaw queries locals captures)
  | .inl name => generator (nativeRaw queries locals captures) (.inl (.inr name))
  | .inr name => generator (nativeRaw queries locals captures) (.inr name)

def frameName (occupied : Finset Nat) : Query ⊕ (ScopedVar Local ⊕ Shared) → ScopedVar (Local ⊕ Query) ⊕ Shared
  | .inl name => .inl ⟨ContextualActivationScopes.start occupied, .inr name⟩
  | .inr (.inl name) => .inl ⟨occupied.sup id + name.scope, .inl name.name⟩
  | .inr (.inr name) => .inr name

theorem frameName_injective (occupied : Finset Nat) : Function.Injective (frameName (Query := Query) (Local := Local)
    (Shared := Shared) occupied) := by
  intro first second same
  rcases first with first | first | first <;> rcases second with second | second | second
  · exact congrArg Sum.inl (Sum.inr.inj (congrArg ScopedVar.name (Sum.inl.inj same)))
  · have impossible := congrArg ScopedVar.name (Sum.inl.inj same); cases impossible
  · cases same
  · have impossible := congrArg ScopedVar.name (Sum.inl.inj same); cases impossible
  · have scopes := congrArg ScopedVar.scope (Sum.inl.inj same)
    have names := Sum.inl.inj (congrArg ScopedVar.name (Sum.inl.inj same))
    have sameScope : first.scope = second.scope := Nat.add_left_cancel scopes
    have equal : first = second := by cases first; cases second; cases sameScope; cases names; rfl
    exact congrArg (fun name => Sum.inr (Sum.inl name)) equal
  · cases same
  · cases same
  · cases same
  · exact congrArg (fun name => Sum.inr (Sum.inr name)) (Sum.inr.inj same)

abbrev frame (occupied : Finset Nat) : Extension (family queries locals captures) where
  Names := ScopedVar (Local ⊕ Query) ⊕ Shared
  declarations := nativeActive queries locals captures
  name := frameName occupied
  injective := frameName_injective occupied
  preserves name := by rcases name with name | name | name <;> rfl

theorem frame_query (occupied : Finset Nat) (name : Query) :
    (frame queries locals captures occupied).assignment (.inl name) =
      generator (nativeActive queries locals captures)
        (.inl ⟨ContextualActivationScopes.start occupied, .inr name⟩) := rfl

theorem frame_row (occupied : Finset Nat) (name : ScopedVar Local) :
    (frame queries locals captures occupied).assignment (.inr (.inl name)) =
      generator (nativeActive queries locals captures)
        (.inl ⟨occupied.sup id + name.scope, .inl name.name⟩) := rfl

theorem frame_capture (occupied : Finset Nat) (name : Shared) :
    (frame queries locals captures occupied).assignment (.inr (.inr name)) =
      generator (nativeActive queries locals captures) (.inr name) := rfl

theorem captures_square (occupied : Finset Nat) :
    Assignment.compose (frame queries locals captures occupied).assignment (captureEmbedding queries locals captures) =
      ContextualSelectionViews.capturedTarget (bank queries locals) captures := by
  funext name
  change instantiate (frame queries locals captures occupied).assignment
    (instantiate (rowEmbedding queries locals captures)
      (generator (rowFamily locals captures) (.inr name))) = _
  rw [instantiate_generator]
  change instantiate (frame queries locals captures occupied).assignment
    (generator (family queries locals captures) (.inr (.inr name))) = _
  exact instantiate_generator _ _

theorem query_square (occupied : Finset Nat) :
    Assignment.compose (frame queries locals captures occupied).assignment (queryEmbedding queries locals captures) =
      Assignment.compose (ContextualFreshening.assignment (bank queries locals) captures
        (ContextualActivationScopes.start occupied)) (actor queries locals captures) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (frame queries locals captures occupied).assignment (generator _ (.inl name)) =
        instantiate (ContextualFreshening.assignment (bank queries locals) captures
          (ContextualActivationScopes.start occupied)) (generator _ (.inl (.inr name)))
      rw [instantiate_generator, instantiate_generator]
      rfl
  | inr name =>
      change instantiate (frame queries locals captures occupied).assignment (generator _ (.inr (.inr name))) =
        instantiate (ContextualFreshening.assignment (bank queries locals) captures
          (ContextualActivationScopes.start occupied)) (generator _ (.inr name))
      rw [instantiate_generator, instantiate_generator]
      rfl

theorem query_term (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S (queryFamily queries captures)) Γ sort) :
    instantiate (frame queries locals captures occupied).assignment (queryView queries locals captures value) =
      ContextualFreshening.termAt (bank queries locals) captures (ContextualActivationScopes.start occupied)
        (instantiate (actor queries locals captures) value) := by
  unfold queryView ContextualFreshening.termAt
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, query_square]

theorem row_square (occupied : Finset Nat) (scope : Nat) :
    Assignment.compose (frame queries locals captures occupied).assignment
      (Assignment.compose (rowEmbedding queries locals captures) (ContextualFreshening.assignment locals captures scope)) =
      Assignment.compose (ContextualFreshening.assignment (bank queries locals) captures (occupied.sup id + scope))
        (ContextualPublication.includePrivate locals queries) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (frame queries locals captures occupied).assignment
        (instantiate (rowEmbedding queries locals captures) (generator _ (.inl (ScopedVar.at scope name)))) =
        instantiate (ContextualFreshening.assignment (bank queries locals) captures (occupied.sup id + scope))
          (generator _ (.inl (.inl name)))
      rw [instantiate_generator]
      change instantiate (frame queries locals captures occupied).assignment
        (generator (family queries locals captures) (.inr (.inl (ScopedVar.at scope name)))) =
        instantiate (ContextualFreshening.assignment (bank queries locals) captures (occupied.sup id + scope))
          (generator (nativeRaw queries locals captures) (.inl (.inl name)))
      rw [instantiate_generator, instantiate_generator]
      rfl
  | inr name =>
      change instantiate (frame queries locals captures occupied).assignment
        (instantiate (rowEmbedding queries locals captures) (generator _ (.inr name))) =
        instantiate (ContextualFreshening.assignment (bank queries locals) captures (occupied.sup id + scope))
          (generator _ (.inr name))
      rw [instantiate_generator]
      change instantiate (frame queries locals captures occupied).assignment
        (generator (family queries locals captures) (.inr (.inr name))) =
        instantiate (ContextualFreshening.assignment (bank queries locals) captures (occupied.sup id + scope))
          (generator (nativeRaw queries locals captures) (.inr name))
      rw [instantiate_generator, instantiate_generator]
      rfl

theorem row_term (occupied : Finset Nat) (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    instantiate (frame queries locals captures occupied).assignment
      (instantiate (rowEmbedding queries locals captures) (ContextualStoredRows.viewAt locals captures scope row)) =
      ContextualStoredRows.viewAt (bank queries locals) captures (occupied.sup id + scope)
        (ContextualPublication.extendPrivate locals queries row) := by
  rw [ContextualStoredRows.viewAt_eq_freshening]
  cases row with
  | schema body =>
      change instantiate (frame queries locals captures occupied).assignment
        (instantiate (rowEmbedding queries locals captures)
          (instantiate (ContextualFreshening.assignment locals captures scope) body)) =
        instantiate (ContextualFreshening.assignment (bank queries locals) captures (occupied.sup id + scope))
          (instantiate (ContextualPublication.includePrivate locals queries) body)
      rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
        ← Assignment.instantiate_compose, ← Assignment.compose_associative, row_square]
  | shared value =>
      rw [← ContextualStoredRows.viewAt_eq_freshening]
      change instantiate (frame queries locals captures occupied).assignment
        (instantiate (rowEmbedding queries locals captures)
          (instantiate (ContextualSelectionViews.capturedTarget locals captures) value)) =
        instantiate (ContextualSelectionViews.capturedTarget (bank queries locals) captures) value
      rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, ← Assignment.compose_associative]
      exact congrArg (fun assignment => instantiate assignment value) (captures_square queries locals captures occupied)

def prepareEndpoint {Γ : Ctx S} {sort : S.Srt} (before : ContextualExecution.Endpoint locals O Γ sort) :
    ContextualExecution.Endpoint (bank queries locals) O Γ sort where
  Names := before.Names
  equality := before.equality
  declarations := before.declarations
  scopes := before.scopes
  occupied := before.occupied
  inventory := ContextualPublication.extendInventory locals queries before.declarations before.inventory
  covered := ContextualPublication.extendInventory_covered locals queries before.declarations before.scopes
    before.inventory before.covered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseFrames
