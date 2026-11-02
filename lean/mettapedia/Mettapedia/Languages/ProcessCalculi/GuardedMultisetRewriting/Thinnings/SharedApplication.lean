import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.GraftSemantics
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Scope

/-!
# Capture-free partial application and grafting on shared references

The executable operation uses only reference weakening and the existing
shared-store opening. It does not decode the body to a tree. Each argument is
shifted past the still-open parameters; store extensions preserve every
remaining argument reference. The specification is the common ABT prefix
application, and full application is exactly the common graft.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication

variable {Head : Type} [DecidableEq Head]

def applyPrefixR : Nat → List Ref → Store Head → Ref → Store Head × Ref
  | _, [], store, body => (store, body)
  | arity, argument :: rest, store, body =>
      let opened := openRef store 0 (liftRef 0 (arity - 1) argument) body
      applyPrefixR (arity - 1) rest opened.1 opened.2

/-- The reference operation preserves the canonical store and computes the common prefix application. -/
theorem applyPrefixR_spec (arity : Nat) (arguments : List Ref) (store : Store Head) (body : Ref)
    (canonical : Canonical store) (validBody : CanonRef store body)
    (validArguments : ∀ argument ∈ arguments, CanonRef store argument)
    (count : arguments.length ≤ arity) :
    store <+: (applyPrefixR arity arguments store body).1 ∧
      Canonical (applyPrefixR arity arguments store body).1 ∧
      CanonRef (applyPrefixR arity arguments store body).1 (applyPrefixR arity arguments store body).2 ∧
      unfold (applyPrefixR arity arguments store body).1 (applyPrefixR arity arguments store body).2 =
        applyPrefix arity (arguments.map (unfold store)) (unfold store body) := by
  induction arguments generalizing arity store body with
  | nil =>
    exact ⟨List.prefix_refl _, canonical, validBody, (applyPrefix_empty arity _).symm⟩
  | cons argument rest ih =>
    have validArgument := validArguments argument (by simp)
    obtain ⟨liftedValid, liftedTree⟩ := liftRef_spec canonical validArgument.placed 0 (arity - 1)
    obtain ⟨grows, nextCanonical, nextBody, openedTree⟩ := openRef_spec canonical liftedValid validBody 0
    have remaining : rest.length ≤ arity - 1 := by simp only [List.length_cons] at count; omega
    obtain ⟨more, finalCanonical, finalBody, tailTree⟩ := ih (arity - 1) _ _ nextCanonical nextBody
      (fun r member => (validArguments r (by simp [member])).prefix grows) remaining
    refine ⟨grows.trans more, finalCanonical, finalBody, ?_⟩
    change unfold (applyPrefixR (arity - 1) rest _ _).1 (applyPrefixR (arity - 1) rest _ _).2 = _
    rw [tailTree]
    have retained : rest.map (unfold (openRef store 0 (liftRef 0 (arity - 1) argument) body).1) =
        rest.map (unfold store) := by
      apply List.map_congr_left
      intro r member
      exact unfold_prefix canonical.topo grows (validArguments r (by simp [member])).valid
    rw [retained, openedTree, liftedTree]
    simpa only [List.map_cons, List.length_map] using
      GraftSemantics.applyPrefix_cons_of_le arity (unfold store argument)
        (rest.map (unfold store)) (unfold store body) (by simpa using count)

/-- Checked partial application retains both the remaining parameters and the ambient scope. -/
def applyPrefixCheckedR (store : Store Head) (arity ambient : Nat) (arguments : List Ref) (body : Ref) :
    Option (Store Head × Ref) :=
  if arguments.length ≤ arity ∧ Scope.check body (arity + ambient) = true ∧
      arguments.all (fun argument => Scope.check argument ambient) = true then
    some (applyPrefixR arity arguments store body)
  else none

theorem applyPrefixCheckedR_supported {store : Store Head} (canonical : Canonical store)
    {arity ambient : Nat} {arguments : List Ref} {body : Ref} (validBody : CanonRef store body)
    (validArguments : ∀ argument ∈ arguments, CanonRef store argument)
    {result : Store Head × Ref}
    (applied : applyPrefixCheckedR store arity ambient arguments body = some result) :
    store <+: result.1 ∧ Canonical result.1 ∧ CanonRef result.1 result.2 ∧
      Scope.check result.2 (arity - arguments.length + ambient) = true := by
  unfold applyPrefixCheckedR at applied
  split at applied
  · rename_i admitted
    have same := Option.some.inj applied
    subst result
    obtain ⟨grows, finalCanonical, valid, tree⟩ :=
      applyPrefixR_spec arity arguments store body canonical validBody validArguments admitted.1
    refine ⟨grows, finalCanonical, valid, ?_⟩
    rw [← Scope.check_spec finalCanonical valid, tree]
    have scopedArguments : ∀ term ∈ arguments.map (unfold store), Term.supportedAt ambient term = true := by
      intro term member
      obtain ⟨r, sourceMember, same⟩ := List.mem_map.mp member
      subst term
      rw [Scope.check_spec canonical (validArguments r sourceMember)]
      exact (List.all_eq_true.mp admitted.2.2) r sourceMember
    have scopedBody : Term.supportedAt (arity + ambient) (unfold store body) = true := by
      rw [Scope.check_spec canonical validBody]
      exact admitted.2.1
    simpa only [List.length_map] using applyPrefix_supported (arguments.map (unfold store))
      (by simpa using admitted.1) scopedArguments (unfold store body) scopedBody
  · cases applied

/-- A full graft checks the declared arity and body support before any store extension. -/
def graftR (store : Store Head) (arity : Nat) (arguments : List Ref) (body : Ref) :
    Option (Store Head × Ref) :=
  if arguments.length = arity ∧ Scope.check body arity = true then
    some (applyPrefixR arity arguments store body)
  else none

/-- Exact agreement, including refusal, with the common simultaneous ABT graft. -/
theorem graftR_spec (store : Store Head) (canonical : Canonical store) (arity : Nat)
    (arguments : List Ref) (body : Ref) (validBody : CanonRef store body)
    (validArguments : ∀ argument ∈ arguments, CanonRef store argument) :
    (graftR store arity arguments body).map (fun result => unfold result.1 result.2) =
      graft arity (arguments.map (unfold store)) (unfold store body) := by
  by_cases count : arguments.length = arity
  · by_cases bodyScoped : Scope.check body arity = true
    · have scopedBody : Term.supportedAt arity (unfold store body) = true := by
        rwa [Scope.check_spec canonical validBody]
      have full := GraftSemantics.applyPrefix_full (arguments.map (unfold store)) (unfold store body)
        (by simpa using count) scopedBody
      rw [full]
      simp only [graftR, count, bodyScoped, and_self, ↓reduceIte, Option.map_some]
      exact congrArg some
        (applyPrefixR_spec arity arguments store body canonical validBody validArguments (Nat.le_of_eq count)).2.2.2
    · simp [graftR, graft, Scope.check_spec canonical validBody, bodyScoped, count]
  · simp [graftR, graft, count]

theorem graftR_canonical {store : Store Head} (canonical : Canonical store)
    {arity : Nat} {arguments : List Ref} {body : Ref} (validBody : CanonRef store body)
    (validArguments : ∀ argument ∈ arguments, CanonRef store argument)
    {result : Store Head × Ref} (applied : graftR store arity arguments body = some result) :
    store <+: result.1 ∧ Canonical result.1 ∧ CanonRef result.1 result.2 := by
  unfold graftR at applied
  split at applied
  · rename_i admitted
    have same := Option.some.inj applied
    subst result
    have correct := applyPrefixR_spec arity arguments store body canonical validBody validArguments
      (Nat.le_of_eq admitted.1)
    exact ⟨correct.1, correct.2.1, correct.2.2.1⟩
  · cases applied

/-- Closed bodies retain their exact reference and allocate no nodes, even with unused parameters. -/
theorem applyPrefixR_closed (arity : Nat) (arguments : List Ref) (store : Store Head)
    (body : Ref) (closed : body.thin = []) : applyPrefixR arity arguments store body = (store, body) := by
  induction arguments generalizing arity store body with
  | nil => rfl
  | cons argument rest ih =>
    have unused : Thin.bit body.thin 0 = false := by simp [closed]
    rw [applyPrefixR, openRef_unused store 0 (liftRef 0 (arity - 1) argument) body unused]
    have same : (⟨Thin.erase 0 body.thin, body.id⟩ : Ref) = body := by
      cases body
      simp_all
    rw [same]
    exact ih _ _ _ closed

namespace Controls

def pair (a b : Term Nat) : Term Nat := .node 2 (.cons 0 a (.cons 0 b .nil))
def eight : Term Nat := .node 8 .nil
def argumentStore : Store Nat := (encodeR (encodeR [] (.idx 0 : Term Nat)).1 eight).1
def firstArgument : Ref := (encodeR [] (.idx 0 : Term Nat)).2
def secondArgument : Ref := (encodeR (encodeR [] (.idx 0 : Term Nat)).1 eight).2
def template : Term Nat := pair (.idx 0) (.idx 1)
def stored : Store Nat × Ref := encodeR argumentStore template

theorem shared_graft_preserves_ambient_variable :
    (graftR stored.1 2 [firstArgument, secondArgument] stored.2).map
      (fun result => unfold result.1 result.2) = some (pair (.idx 0) eight) := by decide

theorem shared_partial_application_retains_remaining_parameter :
    (applyPrefixCheckedR stored.1 2 1 [firstArgument] stored.2).map
      (fun result => unfold result.1 result.2) = some (pair (.idx 1) (.idx 0)) := by decide

theorem shared_repeated_arguments_allowed :
    (graftR stored.1 2 [firstArgument, firstArgument] stored.2).map
      (fun result => unfold result.1 result.2) = some (pair (.idx 0) (.idx 0)) := by decide

theorem shared_missing_argument_refused : graftR stored.1 2 [firstArgument] stored.2 = none := by decide

theorem shared_wrong_body_scope_refused : graftR stored.1 1 [firstArgument] stored.2 = none := by decide

def nested : Store Nat × Ref := encodeR argumentStore
  (.node 1 (.cons 1 (pair (.idx 1) (.idx 2)) .nil))

theorem shared_graft_beneath_binder :
    (graftR nested.1 2 [firstArgument, secondArgument] nested.2).map
      (fun result => unfold result.1 result.2) =
        some (.node 1 (.cons 1 (pair (.idx 1) eight) .nil)) := by decide

end Controls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication
