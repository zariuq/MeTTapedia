import Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-!
# A selected equation cannot capture an unrelated live caller name

The source occurrence's freshening protects live names. Matching introduces
only names from the query and fresh pattern, and merge retains precisely
their support together with the incoming record. Thus a visible name absent
from both the incoming record and query remains absent after selection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.EquationProtectedNames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval.Steps Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Bindings.ScopeObservation.ModelTransport
open Spec.Match.SolutionTheory

def PreservesLive (live : List Atom) (before after : Bindings) : Prop :=
  ∀ name, (∃ atom ∈ live, Spec.Match.Merge.AtomOccurs atom name) → name ∉ specBindingVars before →
    name ∉ specBindingVars after

theorem selected {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (frontier : EquationFrontierRel space live query incoming works)
    {work : EquationWork} (present : work ∈ works) (name : String)
    (visible : QueryVisibleName live query incoming name)
    (unbound : name ∉ specBindingVars incoming) (unmentioned : name ∉ TypeSubst.typeVars query) :
    name ∉ specBindingVars work.bindings := by
  obtain ⟨matched, occurrence⟩ := frontier.occurrence present
  obtain ⟨rename, _injective, patternRenamed, _bodyRenamed, fresh⟩ := occurrence.selected.1
  have absentPattern : name ∉ TypeSubst.typeVars work.pattern := by
    rw [EquationFreshening.alphaRename_eq patternRenamed, Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
    intro member
    obtain ⟨old, occurs, same⟩ := List.mem_map.mp member
    have sourceOccurs : Spec.Match.Merge.AtomOccurs work.left old :=
      Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mpr (by
        rw [encodeModelAtom_vars_eq_typeVars]
        exact occurs)
    exact fresh old (Or.inl sourceOccurs) (same.symm ▸ visible)
  intro supported
  rcases (occurrence.result.1.support name).mp supported with fromMatch | fromIncoming
  · rcases (QueryBindingProjection.SourceSupport.match_support occurrence.selected.2 name).mp fromMatch with fromQuery | fromPattern
    · exact unmentioned fromQuery
    · exact absentPattern fromPattern
  · exact unbound fromIncoming

theorem closed_query {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (frontier : EquationFrontierRel space live query incoming works)
    {work : EquationWork} (present : work ∈ works) (name : String)
    (visible : QueryVisibleName live query incoming name) (unbound : name ∉ specBindingVars incoming)
    (closed : TypeSubst.typeVars query = []) : name ∉ specBindingVars work.bindings :=
  selected frontier present name visible unbound (by simp [closed])

end Mettapedia.Languages.MeTTa.HE.EquationProtectedNames
