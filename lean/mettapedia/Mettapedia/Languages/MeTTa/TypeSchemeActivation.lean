import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Lemmas

/-!
# Hygienic activation of immutable type schemes

One renaming applies to the entire scheme, so repeated variable occurrences
in domains and codomain remain shared. Finite-support renaming is injective
on scheme variables and avoids the caller's occupied variables. The concrete
fresh-string construction proves that this requirement is satisfiable; it is
an existence witness, not a recommended native allocation strategy. Native
activation can use the existing fresh variable identities instead.

This module is shared atom-syntax mathematics, not a typing judgment for
either dialect. Substituting a variable with a type is deliberately separate
from fresh renaming. A renaming preserves the literal shape of a formal; a
substitution need not preserve argument demand.

Related representation principle: co-contextual typechecking retains type
unknowns and requirements to be combined later, rather than freezing the
caller context into each cached result. The laws here concern only syntax
activation, not equivalence with a co-contextual typing calculus.
See https://doi.org/10.4230/LIPIcs.ECOOP.2017.18.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeSchemeActivation

open OSLFCore (Atom)

def rename (names : String → String) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => .var (names name)
  | .grounded value => .grounded value
  | .expression items => .expression (items.map (rename names))

def freeVars : Atom → List String
  | .symbol _ | .grounded _ => []
  | .var name => [name]
  | .expression items => items.flatMap freeVars

theorem variables_rename (names : String → String) (scheme : Atom) :
    freeVars (rename names scheme) = (freeVars scheme).map names := by
  induction scheme using Atom.rec (motive_2 := fun items =>
    (items.map (rename names)).flatMap freeVars = (items.flatMap freeVars).map names) with
  | symbol _ => simp only [rename, freeVars, List.map_nil]
  | var _ => simp only [rename, freeVars, List.map_cons, List.map_nil]
  | grounded _ => simp only [rename, freeVars, List.map_nil]
  | expression items ih => simpa only [rename, freeVars] using ih
  | nil => rfl
  | cons head tail ihHead ihTail =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [ihHead, ihTail]

theorem rename_id (scheme : Atom) : rename id scheme = scheme := by
  induction scheme using Atom.rec (motive_2 := fun items => items.map (rename id) = items) with
  | symbol _ => simp only [rename]
  | var _ => simp only [rename, id_eq]
  | grounded _ => simp only [rename]
  | expression items ih => simpa only [rename] using congrArg Atom.expression ih
  | nil => rfl
  | cons head tail ihHead ihTail => simp only [List.map_cons, ihHead, ihTail]

theorem rename_comp (first second : String → String) (scheme : Atom) :
    rename second (rename first scheme) = rename (second ∘ first) scheme := by
  induction scheme using Atom.rec (motive_2 := fun items =>
    (items.map (rename first)).map (rename second) = items.map (rename (second ∘ first))) with
  | symbol _ => simp only [rename]
  | var _ => simp only [rename, Function.comp_apply]
  | grounded _ => simp only [rename]
  | expression items ih => simpa only [rename] using congrArg Atom.expression ih
  | nil => rfl
  | cons head tail ihHead ihTail => simp only [List.map_cons, ihHead, ihTail]

/-- The native allocator's contract on the scheme's finite support. A single
mapping serves all domains and the codomain, rather than freshening each
component independently. -/
structure Activation (scheme : Atom) (occupied : List String) where
  names : String → String
  injective : ∀ first ∈ freeVars scheme, ∀ second ∈ freeVars scheme,
    names first = names second → first = second
  fresh : ∀ name ∈ freeVars scheme, names name ∉ occupied

def Activation.value {scheme : Atom} {occupied : List String}
    (activation : Activation scheme occupied) : Atom := rename activation.names scheme

theorem Activation.no_capture {scheme : Atom} {occupied : List String}
    (activation : Activation scheme occupied) :
    ∀ name ∈ freeVars activation.value, name ∉ occupied := by
  intro name member
  rw [Activation.value, variables_rename] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact activation.fresh original present

theorem Activation.sharing_iff {scheme : Atom} {occupied : List String}
    (activation : Activation scheme occupied) (first second : String)
    (firstMember : first ∈ freeVars scheme) (secondMember : second ∈ freeVars scheme) :
    activation.names first = activation.names second ↔ first = second :=
  ⟨activation.injective first firstMember second secondMember,
    fun equal => congrArg activation.names equal⟩

def maxLength : List String → Nat
  | [] => 0
  | name :: names => max name.length (maxLength names)

theorem length_le_maxLength (names : List String) (name : String) (member : name ∈ names) :
    name.length ≤ maxLength names := by
  induction names with
  | nil => simp at member
  | cons head names ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact le_trans (ih member) (Nat.le_max_right _ _)

def freshName (bound slot : Nat) : String := String.ofList (List.replicate (bound + slot + 1) '#')

theorem freshName_length (bound slot : Nat) : (freshName bound slot).length = bound + slot + 1 := by
  simp [freshName, String.length_ofList]

theorem freshName_injective (bound : Nat) : Function.Injective (freshName bound) := by
  intro first second same
  have lengths := congrArg String.length same
  simp only [freshName_length] at lengths
  omega

theorem freshName_not_occupied (occupied : List String) (slot : Nat) :
    freshName (maxLength occupied) slot ∉ occupied := by
  intro member
  have bound := length_le_maxLength occupied _ member
  rw [freshName_length] at bound
  omega

/-- A concrete hygienic activation exists for every finite scheme and caller.
Both repeated variables and distinct variables are preserved exactly. -/
def freshActivation (scheme : Atom) (occupied : List String) : Activation scheme occupied where
  names name := freshName (maxLength occupied) ((freeVars scheme).idxOf name)
  injective _first firstMember _second _ same :=
    (List.idxOf_inj firstMember).mp (freshName_injective _ same)
  fresh _name _ := freshName_not_occupied occupied _

/-- Extending the occupied set by an earlier activation's variables ensures
that a later activation cannot alias any variable of the earlier one. -/
theorem activations_disjoint (scheme : Atom) (occupied : List String)
    (first : Activation scheme occupied)
    (second : Activation scheme (freeVars first.value ++ occupied)) :
    ∀ name ∈ freeVars second.value, name ∉ freeVars first.value := by
  intro name member earlier
  exact second.no_capture name member (List.mem_append_left _ earlier)

namespace Controls

def shared : Atom := .expression [.symbol "->", .var "a", .var "b", .var "a"]

theorem one_mapping_retains_domain_codomain_sharing :
    (freshActivation shared ["#"]).value =
      .expression [.symbol "->", .var "##", .var "###", .var "##"] := by
  simp [Activation.value, freshActivation, shared, freeVars, rename, maxLength, freshName]
  decide

theorem separately_freshening_repeated_occurrences_loses_sharing :
    .expression [.symbol "->", .var "a0", .var "a1"] ≠
      rename (fun _ => "a0") (.expression [.symbol "->", .var "a", .var "a"]) := by
  simp [rename]

theorem a_second_activation_has_disjoint_variables :
    let first := freshActivation shared []
    let second := freshActivation shared (freeVars first.value)
    ∀ name ∈ freeVars second.value, name ∉ freeVars first.value := by
  intro first second name member
  exact second.no_capture name member

end Controls

end Mettapedia.Languages.MeTTa.TypeSchemeActivation
