import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadWorlds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadSafety

/-!
# Coordinates of actual subtype-result extraction

The full-row unifier, its selected substitution and the unresolved-result
filter all commute with the same variable permutation. The fresh output
name is aligned while preserving the retained input interface. These laws
are for the existing subtype query, not an assumed completed closure oracle.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadCoordinates

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open TypeDependencyAdmission TypeScopeRenaming TypeReadWorlds
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply remember fresh)

theorem variable_variant (scope : List String) (name : String) (absent : name ∉ scope) :
    TypeCandidateAlphaVariantRel scope (.var "result") (.var name) := by
  refine ⟨Equiv.swap "result" name, (Equiv.swap "result" name).injective, ?_, ?_⟩
  · simp
  · intro original member
    have same : original = "result" := by simpa [TypeSubst.typeVars] using member
    simpa [same] using absent

theorem extend_fresh_name (previous : Equiv.Perm String) (live : List String)
    (firstName secondName : String) (firstFresh : firstName ∉ live)
    (secondFresh : secondName ∉ live.map previous) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live, next name = previous name) ∧ next firstName = secondName := by
  have first : ArgumentAlphaVariantsRel live [.var "result"] [.var firstName] :=
    .cons (variable_variant live firstName firstFresh) (.nil _)
  have second : ArgumentAlphaVariantsRel (live.map previous) [.var "result"] [.var secondName] :=
    .cons (variable_variant _ secondName secondFresh) (.nil _)
  obtain ⟨next, agrees, carried⟩ := extend_variant_family previous live _ _ _ first second
  refine ⟨next, agrees, ?_⟩
  have same : Atom.var secondName = Atom.var (next firstName) := by
    simpa only [List.map_cons, List.map_nil, renameAtom, List.cons.injEq, and_true] using carried
  exact (Atom.var.inj same).symm

theorem chosen_name_extension (previous : Equiv.Perm String) (live : List String)
    (first second : Supply) (firstProtected : live ⊆ first.used)
    (secondProtected : live.map previous ⊆ second.used) (base : String) :
    ∃ next : Equiv.Perm String,
      (∀ name ∈ live, next name = previous name) ∧
      next (chooseFreshName base first.used first.next).1 =
        (chooseFreshName base second.used second.next).1 :=
  extend_fresh_name previous live _ _
    (fun member => chooseFreshName_not_mem_avoid base first.used first.next (firstProtected member))
    (fun member => chooseFreshName_not_mem_avoid base second.used second.next (secondProtected member))

theorem pattern_rename (names : String → String) (input : Atom) (resultName : String) :
    TypeScopeClosure.subtypePattern (renameAtom names input) (names resultName) =
      renameAtom names (TypeScopeClosure.subtypePattern input resultName) := rfl

theorem readBack_at_renamed (names : Equiv.Perm String)
    (theta : Mettapedia.Logic.LP.Subst UnifyAtoms.sig) (resultName : String) :
    UnifyAtoms.readBack (Mettapedia.Logic.LP.UnificationPermutation.transport names theta) (names resultName) =
      renameAtom names (UnifyAtoms.readBack theta resultName) := by
  rw [readBack_transport]
  simp only [renameState, names.symm_apply_apply]

theorem subtypeRow_rename (world : ExternalView) (names : Equiv.Perm String)
    (input : Atom) (resultName : String) (row : Atom)
    (inputSafe : resourceFree input = true) (rowSafe : resourceFree row = true) :
    TypeScopeClosure.subtypeRow world (renameAtom names input) (names resultName) (renameAtom names row) =
      (TypeScopeClosure.subtypeRow world input resultName row).map (renameAtom names) := by
  have patternSafe : resourceFree (TypeScopeClosure.subtypePattern input resultName) = true := by
    simp [TypeScopeClosure.subtypePattern, resourceFree, resourceFreeList, inputSafe]
  have renamedPatternSafe : resourceFree (renameAtom names (TypeScopeClosure.subtypePattern input resultName)) = true := by
    rw [rename_resourceFree]
    exact patternSafe
  have renamedRowSafe : resourceFree (renameAtom names row) = true := by
    rw [rename_resourceFree]
    exact rowSafe
  simp only [TypeScopeClosure.subtypeRow, pattern_rename,
    observe_resourceFree world _ patternSafe, observe_resourceFree world _ renamedPatternSafe,
    observe_resourceFree world _ rowSafe, observe_resourceFree world _ renamedRowSafe,
    atom_unify_rename]
  cases matched : UnifyAtoms.unify (TypeScopeClosure.subtypePattern input resultName) row with
  | none => rfl
  | some theta =>
      simp only [Option.map_some]
      change (if UnifyAtoms.readBack (Mettapedia.Logic.LP.UnificationPermutation.transport names theta)
          (names resultName) == Atom.var (names resultName) then none
        else some (UnifyAtoms.readBack (Mettapedia.Logic.LP.UnificationPermutation.transport names theta)
          (names resultName))) =
        (if UnifyAtoms.readBack theta resultName == Atom.var resultName then none
          else some (UnifyAtoms.readBack theta resultName)).map (renameAtom names)
      rw [readBack_at_renamed]
      have sameTest :
          (renameAtom names (UnifyAtoms.readBack theta resultName) == Atom.var (names resultName)) =
            (UnifyAtoms.readBack theta resultName == Atom.var resultName) := by
        exact TypeNormalizationNames.equality_equivariant names _ (.var resultName)
      rw [sameTest]
      split <;> rfl

theorem possibleRow_rename (names : String → String) (row : Atom) :
    ScopedSubtypeReads.possibleRow (renameAtom names row) = ScopedSubtypeReads.possibleRow row := by
  cases row with
  | symbol _ | var _ | grounded _ => rfl
  | expression fields =>
      cases fields with
      | nil => rfl
      | cons head fields =>
          cases fields with
          | nil => cases head <;> rfl
          | cons left fields =>
              cases fields with
              | nil => cases head <;> simp [ScopedSubtypeReads.possibleRow, renameAtom, renameAtomList]
              | cons right rest =>
                  cases rest with
                  | nil =>
                      cases head with
                      | var _ | grounded _ | expression _ => rfl
                      | symbol name =>
                          by_cases subtype : name = ":<"
                          · subst name; rfl
                          · simp [ScopedSubtypeReads.possibleRow, renameAtom, renameAtomList, subtype]
                  | cons _ _ => cases head <;> simp [ScopedSubtypeReads.possibleRow, renameAtom, renameAtomList]

namespace Controls

def external : ExternalView := fun tag key => .grounded (.custom tag key)
def row : Atom := .expression [.symbol ":<", .expression [.symbol "F", .var "a"],
  .expression [.symbol "G", .var "a"]]
def input : Atom := .expression [.symbol "F", .var "public"]

theorem selected_unifier_retains_the_shared_rule_coordinate :
    TypeScopeClosure.subtypeRow external input "result" row =
      some (.expression [.symbol "G", .var "a"]) := by cbv

theorem unresolved_result_is_still_refused_after_renaming :
    TypeScopeClosure.subtypeRow external (.symbol "A") "result"
      (.expression [.symbol ":<", .symbol "A", .var "result"]) = none ∧
    TypeScopeClosure.subtypeRow external (.symbol "A") "new"
      (.expression [.symbol ":<", .symbol "A", .var "new"]) = none := by cbv

theorem reusing_the_output_name_can_capture_the_input :
    TypeScopeClosure.subtypeRow external (.var "x") "x"
      (.expression [.symbol ":<", .symbol "A", .symbol "B"]) = none ∧
    TypeScopeClosure.subtypeRow external (.var "x") "fresh"
      (.expression [.symbol ":<", .symbol "A", .symbol "B"]) = some (.symbol "B") := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadCoordinates
