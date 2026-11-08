import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryWorlds

/-!
# Actual type matching under a growing private-name relation

The selected substitution is the result of the existing total ordered
matcher. The proof retains its finite alias support; mere agreement on a
Boolean acceptance result is insufficient for a later formal or range.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMatcher

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open TypeDependencyAdmission TypeReadQueryWorlds
open RetainedTypePayloads (ExternalView)
open private atomVariables_eq_typeVars from Mettapedia.Languages.MeTTa.HE.EquationFreshening

theorem initial (world : Coordinates) : BindingRelated world Atom.var Atom.var :=
  ⟨fun _ => rfl, OpenFrameEffects.Local.identity _, (TypeFreshReadEquivalence.initial_state_fixed world.names).symm⟩

theorem apply_supported (world : Coordinates) (state : TypeScopeMatcher.State)
    (supported : TypeReadWorlds.Supported world.live state) (atom : Atom)
    (covered : atomVariables atom ⊆ world.live) : atomVariables (substA state atom) ⊆ world.live := by
  have source : TypeSubst.typeVars atom ⊆ world.live := by
    simpa only [atomVariables_eq_typeVars] using covered
  have result := OpenFrameEffects.subst_support_subset supported.closed (TypeReadWorlds.covered_support source)
  intro name member
  apply List.mem_toFinset.mp
  apply result
  apply (TypeReadWorlds.variables_support _ name).mp
  simpa only [atomVariables_eq_typeVars] using member

theorem apply_related {world : Coordinates} {firstState secondState : TypeScopeMatcher.State}
    (states : BindingRelated world firstState secondState) {first second : Atom}
    (atoms : AtomRelated world first second) :
    AtomRelated world (substA firstState first) (substA secondState second) := by
  refine ⟨substitute_resourceFree firstState states.1 first atoms.1,
    apply_supported world firstState states.2.1 first atoms.2.1, ?_⟩
  rw [states.2.2, atoms.2.2]
  exact TypeScopeRenaming.substitute world.names firstState first

theorem metaCheck_rename (names : String → String) (formal kind : Atom) :
    TypeScopeMatcher.metaCheckAtom (renameAtom names formal) kind = TypeScopeMatcher.metaCheckAtom formal kind := by
  cases formal <;> rfl

theorem metaCheck_related {world : Coordinates} {first second : Atom}
    (related : AtomRelated world first second) (kind : Atom) :
    TypeScopeMatcher.metaCheckAtom second kind = TypeScopeMatcher.metaCheckAtom first kind := by
  rw [related.2.2]
  exact metaCheck_rename world.names first kind

theorem firstChoice_related (external : ExternalView) (world : Coordinates)
    (firstState secondState : TypeScopeMatcher.State) (states : BindingRelated world firstState secondState)
    (firstExpected secondExpected : Atom) (expected : AtomRelated world firstExpected secondExpected)
    (firstTypes secondTypes : List Atom) (types : TypesRelated world firstTypes secondTypes) :
    Option.Rel (BindingRelated world)
      (StampInference.firstResult (fun actual => TypeScopeMatcher.unify external firstState actual firstExpected) firstTypes)
      (StampInference.firstResult (fun actual => TypeScopeMatcher.unify external secondState actual secondExpected) secondTypes) := by
  rw [states.2.2, expected.2.2, types.2.2,
    TypeScopeRenaming.firstChoice_rename external world.names firstState states.1 firstExpected expected.1
      firstTypes types.1]
  cases chosen : StampInference.firstResult
      (fun actual => TypeScopeMatcher.unify external firstState actual firstExpected) firstTypes with
  | none => exact .none
  | some after =>
      apply Option.Rel.some
      refine ⟨TypeScopeMatcher.firstResult_preserves external firstState states.1 firstExpected expected.1
        firstTypes types.1 after chosen, ?_, rfl⟩
      apply TypeReadWorlds.firstChoice_preserves_support external world.live firstState states.2.1 states.1
        firstExpected expected.1
      · simpa only [atomVariables_eq_typeVars] using expected.2.1
      · exact types.1
      · intro actual member
        simpa only [atomVariables_eq_typeVars] using (types_member types member).2.1
      · exact chosen

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMatcher
