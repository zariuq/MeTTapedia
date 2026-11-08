import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeMatcher
import Mettapedia.Logic.LP.UnificationPermutation

/-!
# Actual type substitutions under fresh variable coordinates

The existing atom codec and total unifier preserve the selected substitution,
not just existence of a solution. The ordered type matcher transports that
substitution through its top-level wildcard shortcuts and accumulated state.
Resource-free operands justify omitting external observations. This is a
source matching law; native allocator and representation proofs remain at
their own boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeRenaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Logic.LP (Term Subst)
open TypeDependencyAdmission TypeScopeMatcher
open RetainedTypePayloads (ExternalView)

theorem encode_decode (term : Term UnifyAtoms.sig) :
    UnifyAtoms.encode (UnifyAtoms.decode term) = term := by
  induction term with
  | var name => rw [UnifyAtoms.decode, UnifyAtoms.encode]
  | const value => cases value <;> rw [UnifyAtoms.decode, UnifyAtoms.encode]
  | app arity children ih =>
      simp only [UnifyAtoms.decode, UnifyAtoms.encode_expression]
      have appExt : ∀ (n m : Nat) (same : n = m)
          (left : Fin n → Term UnifyAtoms.sig) (right : Fin m → Term UnifyAtoms.sig),
          (∀ i, left i = right (i.cast same)) →
            Term.app (σ := UnifyAtoms.sig) n left = Term.app (σ := UnifyAtoms.sig) m right := by
        intro n m same left right pointwise
        subst m
        exact congrArg (Term.app (σ := UnifyAtoms.sig) n) (funext pointwise)
      apply appExt _ _ List.length_ofFn
      intro index
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact ih _

theorem decode_injective : Function.Injective UnifyAtoms.decode := by
  intro first second same
  have encoded := congrArg UnifyAtoms.encode same
  simpa only [encode_decode] using encoded

theorem decode_rename (rename : String → String) (term : Term UnifyAtoms.sig) :
    UnifyAtoms.decode (Mettapedia.Logic.LP.UnificationRenaming.rename rename term) =
      renameAtom rename (UnifyAtoms.decode term) := by
  induction term with
  | var name => rfl
  | const value => cases value <;> rfl
  | app arity children ih =>
      simp only [Mettapedia.Logic.LP.UnificationRenaming.rename_app, UnifyAtoms.decode,
        renameAtom, renameAtomList_eq_map, List.map_ofFn, ih, Function.comp_def]

theorem encode_rename (rename : String → String) (atom : Atom) :
    UnifyAtoms.encode (renameAtom rename atom) =
      Mettapedia.Logic.LP.UnificationRenaming.rename rename (UnifyAtoms.encode atom) := by
  apply decode_injective
  rw [UnifyAtoms.decode_encode, decode_rename, UnifyAtoms.decode_encode]

def renameState (permutation : Equiv.Perm String) (state : TypeScopeMatcher.State) : TypeScopeMatcher.State :=
  fun name => renameAtom permutation (state (permutation.symm name))

theorem readBack_transport (permutation : Equiv.Perm String) (theta : Subst UnifyAtoms.sig) :
    UnifyAtoms.readBack (Mettapedia.Logic.LP.UnificationPermutation.transport permutation theta) =
      renameState permutation (UnifyAtoms.readBack theta) := by
  funext name
  exact decode_rename permutation (theta (permutation.symm name))

theorem atom_unify_rename (permutation : Equiv.Perm String) (left right : Atom) :
    UnifyAtoms.unify (renameAtom permutation left) (renameAtom permutation right) =
      (UnifyAtoms.unify left right).map (Mettapedia.Logic.LP.UnificationPermutation.transport permutation) := by
  simp only [UnifyAtoms.unify, encode_rename]
  simpa only [Mettapedia.Logic.LP.UnificationRenaming.equations, List.map_cons, List.map_nil] using
    Mettapedia.Logic.LP.UnificationPermutation.unifyTotal_transport (σ := UnifyAtoms.sig) permutation
      [(UnifyAtoms.encode left, UnifyAtoms.encode right)]

mutual
theorem substitute (permutation : Equiv.Perm String) (state : TypeScopeMatcher.State) : ∀ atom,
    substA (renameState permutation state) (renameAtom permutation atom) =
      renameAtom permutation (substA state atom)
  | .var name => by simp [renameAtom, substA, renameState]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression children => congrArg Atom.expression (substituteList permutation state children)
theorem substituteList (permutation : Equiv.Perm String) (state : TypeScopeMatcher.State) : ∀ atoms,
    substL (renameState permutation state) (renameAtomList permutation atoms) =
      renameAtomList permutation (substL state atoms)
  | [] => rfl
  | atom :: atoms => by rw [renameAtomList, substL, substL, renameAtomList,
      substitute, substituteList]
end

theorem compose_transport (permutation : Equiv.Perm String) (after before : TypeScopeMatcher.State) :
    compose (renameState permutation after) (renameState permutation before) =
      renameState permutation (compose after before) := by
  funext name
  exact substitute permutation after (before (permutation.symm name))

theorem state_safe (permutation : Equiv.Perm String) (state : TypeScopeMatcher.State) (safe : SafeState state) :
    SafeState (renameState permutation state) := by
  intro name
  rw [renameState, rename_resourceFree]
  exact safe _

theorem wildcard_rename (rename : String → String) (type_ : Atom) :
    wildcard (renameAtom rename type_) = wildcard type_ := by
  cases type_ <;> rfl

theorem actualWildcard_rename (rename : String → String) (type_ : Atom) :
    actualWildcard (renameAtom rename type_) = actualWildcard type_ := by
  cases type_ <;> rfl

theorem symbol_test_rename (rename : String → String) (type_ : Atom) (name : String) :
    (renameAtom rename type_ == .symbol name) = (type_ == .symbol name) := by
  cases type_ <;> rfl

theorem spaceValueType_rename (rename : String → String) (type_ : Atom) :
    spaceValueType (renameAtom rename type_) = spaceValueType type_ := by
  cases type_ with
  | symbol _ | var _ | grounded _ => rfl
  | expression children =>
      cases children with
      | nil => rfl
      | cons head tail =>
          cases tail with
          | nil => cases head <;> rfl
          | cons discipline rest =>
              cases rest with
              | nil => cases head <;> simp [spaceValueType, renameAtom, renameAtomList]
              | cons _ _ => cases head <;> simp [spaceValueType, renameAtom, renameAtomList]

theorem spaceClassBridge_rename (rename : String → String) (actual expected : Atom) :
    spaceClassBridge (renameAtom rename actual) (renameAtom rename expected) =
      spaceClassBridge actual expected := by
  simp only [spaceClassBridge, symbol_test_rename, spaceValueType_rename]

theorem unify_rename (world : ExternalView) (permutation : Equiv.Perm String)
    (state : TypeScopeMatcher.State) (safe : SafeState state)
    (actual expected : Atom) (actualSafe : resourceFree actual = true) (expectedSafe : resourceFree expected = true) :
    unify world (renameState permutation state) (renameAtom permutation actual) (renameAtom permutation expected) =
      (unify world state actual expected).map (renameState permutation) := by
  have left := substitute_resourceFree state safe actual actualSafe
  have right := substitute_resourceFree state safe expected expectedSafe
  have leftRenamed : resourceFree (renameAtom permutation (substA state actual)) = true := by
    rw [rename_resourceFree]; exact left
  have rightRenamed : resourceFree (renameAtom permutation (substA state expected)) = true := by
    rw [rename_resourceFree]; exact right
  simp only [unify, substitute, observe_resourceFree world _ left,
    observe_resourceFree world _ right, observe_resourceFree world _ leftRenamed,
    observe_resourceFree world _ rightRenamed, wildcard_rename, actualWildcard_rename, spaceClassBridge_rename]
  split
  · rfl
  · rw [atom_unify_rename]
    simp only [Option.map_map, Function.comp_def, readBack_transport, compose_transport]

theorem firstChoice_rename (world : ExternalView) (permutation : Equiv.Perm String)
    (state : TypeScopeMatcher.State) (safe : SafeState state)
    (expected : Atom) (expectedSafe : resourceFree expected = true) : ∀ actuals,
    resourceFreeList actuals = true →
      StampInference.firstResult
          (fun actual => unify world (renameState permutation state) actual (renameAtom permutation expected))
          (actuals.map (renameAtom permutation)) =
        (StampInference.firstResult (fun actual => unify world state actual expected) actuals).map
          (renameState permutation)
  | [], _ => rfl
  | actual :: actuals, actualsSafe => by
      simp only [resourceFreeList, Bool.and_eq_true] at actualsSafe
      simp only [List.map_cons, StampInference.firstResult,
        unify_rename world permutation state safe actual expected actualsSafe.1 expectedSafe]
      cases selected : unify world state actual expected with
      | none => exact firstChoice_rename world permutation state safe expected expectedSafe actuals actualsSafe.2
      | some next => rfl

theorem firstChoice_range (world : ExternalView) (permutation : Equiv.Perm String)
    (state : TypeScopeMatcher.State) (safe : SafeState state)
    (expected : Atom) (expectedSafe : resourceFree expected = true)
    (actuals : List Atom) (actualsSafe : resourceFreeList actuals = true) (range : Atom) :
    (StampInference.firstResult
        (fun actual => unify world (renameState permutation state) actual (renameAtom permutation expected))
        (actuals.map (renameAtom permutation))).map (fun next => substA next (renameAtom permutation range)) =
      (StampInference.firstResult (fun actual => unify world state actual expected) actuals).map
        (fun next => renameAtom permutation (substA next range)) := by
  rw [firstChoice_rename world permutation state safe expected expectedSafe actuals actualsSafe]
  simp only [Option.map_map, Function.comp_def, substitute]

namespace Controls

def world : ExternalView := fun tag key => .grounded (.custom tag key)
def permutation : Equiv.Perm String := Equiv.swap "a" "b"

theorem shared_expected_variable_is_carried :
    (unify world Atom.var (.symbol "Number") (.var "a")).map (fun state => state "a") =
      some (.symbol "Number") ∧
    (unify world (renameState permutation Atom.var) (.symbol "Number") (.var "b")).map
        (fun state => state "b") = some (.symbol "Number") := by cbv

def paired (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]

theorem renaming_cannot_split_a_shared_variable :
    (unify world Atom.var (paired (.symbol "Number") (.symbol "String"))
      (renameAtom permutation (paired (.var "a") (.var "a")))).isNone = true := by cbv

theorem first_success_still_selects_the_first_instance :
    (StampInference.firstResult (fun actual => unify world Atom.var actual (.var "a"))
      [.symbol "Number", .symbol "String"]).map (fun state => state "a") = some (.symbol "Number") := by cbv

theorem actual_atom_is_not_a_universal_type :
    (unify world Atom.var Atom.atomType (.symbol "Number")).isNone = true ∧
    (unify world Atom.var (.symbol "Number") Atom.atomType).map (fun state => state "a") = some (.var "a") := by cbv

theorem space_class_bridge_does_not_bind_the_discipline :
    (unify world Atom.var (.symbol "SpaceType") (.expression [.symbol "Space", .var "discipline"])).map
      (fun state => state "discipline") = some (.var "discipline") ∧
    (unify world Atom.var (.expression [.symbol "Space", .symbol "linear"]) (.symbol "SpaceType")).isSome = true := by cbv

theorem space_bridge_requires_the_declared_shape :
    (unify world Atom.var (.symbol "SpaceType") (.expression [.symbol "NotSpace", .var "discipline"])).isNone = true ∧
    (unify world Atom.var (.symbol "SpaceType") (.expression [.symbol "Space"])).isNone = true := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeRenaming
