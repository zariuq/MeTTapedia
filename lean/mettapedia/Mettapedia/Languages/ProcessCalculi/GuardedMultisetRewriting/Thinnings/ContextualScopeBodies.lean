import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatcher
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ScopedApplication
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Scope

/-!
# Constructing contextual bodies in declared finite interfaces

An interface determines a variable spine independently of the value being
admitted. The existing common recovery operation builds a body over those
parameters, and the existing graft reconstructs the original value. This
construction succeeds exactly when every free occurrence is listed.

Only inverse recovery uses a distinct variable spine. Ordinary graft remains
available for reordered, repeated and compound authored arguments. The finite
interface is local metadata, not a global bound on names or contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualScopeBodies

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open Thin

variable {Head : Type}

def indices (allowed : Thin) : List Nat := (List.range (ones allowed)).map (sel allowed)

def arguments (allowed : Thin) : List (Term Head) := (indices allowed).map Term.idx

theorem indices_length (allowed : Thin) : (indices allowed).length = ones allowed := by simp [indices]

theorem indices_distinct (allowed : Thin) : (indices allowed).Nodup :=
  List.nodup_range.map (sel_injective allowed)

theorem graft_rename (allowed : Thin) (body : Term Head)
    (scopedBody : Term.supportedAt (ones allowed) body = true) :
    graft (ones allowed) (arguments allowed) body = some (rename allowed body) := by
  simp only [graft, arguments, List.length_map, indices_length, scopedBody, and_self, ↓reduceIte]
  congr 1
  calc
    Term.substituteMany (argumentAt ((indices allowed).map Term.idx)) body =
        Term.substituteMany (fun index => Term.idx (sel allowed index)) body := by
      apply Term.substituteMany_congr_scoped _ body scopedBody
      intro index inside
      simp [argumentAt, indices, inside]
    _ = rename allowed body := by rw [Term.substituteMany_renaming, ScopedApplication.renameMany_selection]

theorem support_of_graft {allowed : Thin} {body target : Term Head}
    (applied : graft (ones allowed) (arguments allowed) body = some target) :
    ∀ index, freeAt target index = true → bit allowed index = true := by
  have scopedBody : Term.supportedAt (ones allowed) body = true := by
    unfold graft at applied
    split at applied
    · exact (by assumption : (arguments (Head := Head) allowed).length = ones allowed ∧
        Term.supportedAt (ones allowed) body = true).2
    · cases applied
  have placed : rename allowed body = target := Option.some.inj ((graft_rename allowed body scopedBody).symm.trans applied)
  intro index used
  rw [← placed] at used
  obtain ⟨sourceIndex, sourceUsed, same⟩ := (freeAt_rename allowed body index).mp used
  have inside := (Scope.supportedAt_iff _ _).mp scopedBody sourceIndex sourceUsed
  exact same ▸ (bit_sel inside).1

variable [DecidableEq Head]

theorem exists_body_iff (allowed : Thin) (target : Term Head) :
    (∃ body, graft (ones allowed) (arguments allowed) body = some target) ↔
      ∀ index, freeAt target index = true → bit allowed index = true := by
  constructor
  · rintro ⟨body, applied⟩
    exact support_of_graft applied
  · intro permitted
    have encoded := encodeR_spec [] canonical_nil target
    have included : Sub (encodeR [] target).2.thin allowed := by
      intro index used
      apply permitted index
      rw [← encodeR_unfold canonical_nil target]
      rw [freeAt_unfold encoded.2.1 encoded.2.2.1]
      exact used
    have solution := ContextualMatching.projectRef_solution encoded.2.1 encoded.2.2.1 allowed included
    let body := unfold (encodeR [] target).1 (ContextualMatching.projectRef allowed (encodeR [] target).2)
    have scopedBody : Term.supportedAt (ones allowed) body = true := by
      rw [Scope.check_spec encoded.2.1 solution.1]
      exact decide_eq_true solution.2.1
    refine ⟨body, ?_⟩
    rw [graft_rename allowed body scopedBody, solution.2.2, encodeR_unfold canonical_nil target]

def recover (allowed : Thin) (target : Term Head) : Option (Term Head) :=
  ContextualPatterns.Recovery.recover (ones allowed) (arguments allowed) target

theorem recover_sound {allowed : Thin} {target body : Term Head}
    (recovered : recover allowed target = some body) :
    graft (ones allowed) (arguments allowed) body = some target :=
  ContextualPatterns.Recovery.recover_sound recovered

theorem recover_complete {allowed : Thin} {target body : Term Head}
    (applied : graft (ones allowed) (arguments allowed) body = some target) :
    recover allowed target = some body := by
  have exactRecovery := ContextualPatterns.Recovery.recover_complete (indices_distinct allowed)
    (by simpa only [indices_length, arguments] using applied)
  simpa only [recover, indices_length, arguments] using exactRecovery

theorem recover_isSome_iff (allowed : Thin) (target : Term Head) :
    (recover allowed target).isSome = true ↔
      ∀ index, freeAt target index = true → bit allowed index = true := by
  rw [Option.isSome_iff_exists, ← exists_body_iff]
  exact ⟨fun ⟨body, recovered⟩ => ⟨body, recover_sound recovered⟩,
    fun ⟨body, applied⟩ => ⟨body, recover_complete applied⟩⟩

theorem unlisted_occurrence_has_no_body (allowed : Thin) (target : Term Head) (index : Nat)
    (occurs : freeAt target index = true) (unlisted : bit allowed index = false) :
    recover allowed target = none := by
  cases computed : recover allowed target with
  | none => rfl
  | some body =>
      have permitted := (recover_isSome_iff allowed target).mp (by rw [computed]; rfl) index occurs
      rw [unlisted] at permitted
      cases permitted

namespace Controls

def lambda (body : Term Nat) : Term Nat := .node 0 (.cons 1 body .nil)

theorem local_binder_is_not_a_dependency :
    recover [] (lambda (.idx 0)) = some (lambda (.idx 0)) := by decide +kernel

theorem undeclared_outer_capture_has_no_body : recover [] (lambda (.idx 1)) = none := by decide +kernel

theorem sparse_interface_renumbers_the_body :
    recover [true, false, true] (.idx 2 : Term Nat) = some (.idx 1) := by decide +kernel

theorem reordered_application_remains_available :
    graft 2 [.idx 1, .idx 0] (.idx 0 : Term Nat) = some (.idx 1) := by decide +kernel

theorem repeated_application_remains_available :
    graft 2 [.idx 0, .idx 0] (.idx 1 : Term Nat) = some (.idx 0) := by decide +kernel

theorem compound_application_remains_available :
    graft 1 [lambda (.idx 1)] (.idx 0 : Term Nat) = some (lambda (.idx 1)) := by decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualScopeBodies
