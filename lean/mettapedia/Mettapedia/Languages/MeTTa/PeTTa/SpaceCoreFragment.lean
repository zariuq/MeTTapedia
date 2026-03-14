import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge

/-!
# PeTTa Space Core Fragment

Defines the first honest PeTTa space/query fragment that lands on the current
MORK/MM2-backed query seam.

This fragment is intentionally narrow but real:
- `(match &self $x tmpl)`
- `(get-atoms &self)`

It already exercises the atomspace/query side of PeTTa while staying inside the
existing theoremic MORK source-query machinery.

Positive example:
- querying any stored atom in `&self` with a single free variable pattern.

Negative example:
- this does not yet cover collection-pattern bag matching.
- this does not yet cover `new-space`, which is not formalized in the current
  Lean PeTTa stack.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment

open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.ProcessCalculi.MORK

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILBindings := Mettapedia.OSLF.MeTTaIL.Match.Bindings
private abbrev CSpace :=
  Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.CSpace

/-- The first explicit PeTTa space-query core fragment.

This packages the simplest non-sham atomspace/query fragment:
- the pattern is a single free variable
- a stored atom from the current space instantiates that variable
- the instantiated template is the reported answer
- or the current stored atom is returned directly via `(get-atoms &self)`
-/
inductive PeTTaSpaceCoreQuery (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) :
    ILPattern → ILPattern → Prop where
  | anyFactMatch (x : String) (tmpl atom q : ILPattern)
      (hatom : atom ∈ s.storedAtoms)
      (htrans_tmpl : morkTranslatable tmpl = true)
      (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings [(x, atom)] tmpl = q) :
      PeTTaSpaceCoreQuery s
        (.apply "match" [.apply "&self" [], .fvar x, tmpl]) q
  | getAtoms (atom : ILPattern)
      (hatom : atom ∈ s.storedAtoms) :
      PeTTaSpaceCoreQuery s (.apply "get-atoms" [.apply "&self" []]) atom

/-- Reflexive-transitive closure of the first PeTTa space-query core fragment. -/
abbrev PeTTaSpaceCoreQueryStar (s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) :=
  Relation.ReflTransGen (PeTTaSpaceCoreQuery s)

/-- This fragment is a genuine subset of `spaceMatch`: each answer arises from
matching a single stored atom against `.fvar x`. -/
theorem anyFactMatch_mem_spaceMatch
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {x : String} {tmpl atom q : ILPattern}
    (hatom : atom ∈ s.storedAtoms)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings [(x, atom)] tmpl = q) :
    q ∈ s.spaceMatch (.fvar x) tmpl := by
  exact hq ▸ Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.spaceMatch_complete
    s (.fvar x) tmpl atom [(x, atom)] hatom
      (by simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern])

/-- Forget the packaged fragment back to the raw `spaceMatch` semantics. -/
theorem toSpaceMatch
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {p q : ILPattern} (h : PeTTaSpaceCoreQuery s p q) :
    match p with
    | .apply "match" [.apply "&self" [], .fvar _, _] =>
        q ∈ s.spaceMatch (.fvar (match p with
      | .apply "match" [.apply "&self" [], .fvar x, _] => x
      | _ => "")) (match p with
      | .apply "match" [.apply "&self" [], .fvar _, tmpl] => tmpl
      | _ => .fvar "")
    | .apply "get-atoms" [.apply "&self" []] =>
        q ∈ s.storedAtoms
    | _ => False := by
  cases h with
  | anyFactMatch x tmpl atom q hatom _ hq =>
      simpa using anyFactMatch_mem_spaceMatch hatom hq
  | getAtoms atom hatom =>
      simpa using hatom

/-- A packaged `match &self $x tmpl` query lands on the current MORK source-query
seam. -/
theorem anyFactMatch_toMorkSourceQuery
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {x : String} {tmpl atom q : ILPattern}
    (_hatom : atom ∈ s.storedAtoms)
    (htrans_tmpl : morkTranslatable tmpl = true)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings [(x, atom)] tmpl = q)
    {workspace : Space}
    (hatom_in : morkPatternToAtom atom ∈ workspace) :
    let src := morkRuntimeQueryExec0.baseSourceFactor (.fvar x)
    ∃ σ a,
      (σ, a) ∈ morkRuntimeQueryExec0.sourceFactorMatch [] workspace src ∧
      applySubst σ (morkPatternToAtom tmpl) = morkPatternToAtom q := by
  dsimp [morkRuntimeQueryExec0]
  refine ⟨bindingsToSubst [(x, atom)], morkPatternToAtom atom, ?_, ?_⟩
  · change (bindingsToSubst [(x, atom)], morkPatternToAtom atom) ∈
      matchSourceFactor [] workspace (.btm (morkPatternToAtom (.fvar x)))
    simp only [matchSourceFactor]
    apply matchOneInSpace_mem
    · exact hatom_in
    · simpa [morkPatternToAtom, bindingsToSubst] using
        (matchAtom_var_bindingsToSubst_new ([] : ILBindings) x atom (by simp))
  · simpa [hq] using applySubst_commutes [(x, atom)] tmpl htrans_tmpl

/-- Computable version of the same MORK source-query witness on list spaces. -/
theorem anyFactMatch_toComputableSourceQuery
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {x : String} {tmpl atom q : ILPattern}
    (hatom : atom ∈ s.storedAtoms)
    (htrans_tmpl : morkTranslatable tmpl = true)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings [(x, atom)] tmpl = q)
    {workspace : CSpace}
    (hatom_in : morkPatternToAtom atom ∈ workspace) :
    let src := morkRuntimeQueryExec0.baseSourceFactor (.fvar x)
    ∃ σ a,
      (σ, a) ∈ morkRuntimeQueryExec0.computableSourceFactorMatch [] workspace src ∧
      applySubst σ (morkPatternToAtom tmpl) = morkPatternToAtom q := by
  obtain ⟨σ, a, hsrc, htmpl⟩ :=
    anyFactMatch_toMorkSourceQuery hatom htrans_tmpl hq
      (workspace := workspace.toFinset) (by exact List.mem_toFinset.mpr hatom_in)
  refine ⟨σ, a, ?_, htmpl⟩
  exact morkRuntimeQueryExec0.sourceFactorComplete [] workspace _ σ a hsrc

/-- A `(get-atoms &self)` core query also lands on the current MORK source-query
seam: any fact can be witnessed by a single free-variable source factor. -/
theorem getAtoms_toComputableSourceQuery
    {s : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace}
    {atom : ILPattern}
    (_hatom : atom ∈ s.storedAtoms)
    {workspace : CSpace}
    (hatom_in : morkPatternToAtom atom ∈ workspace) :
    let src := morkRuntimeQueryExec0.baseSourceFactor (.fvar "__fact")
    ∃ σ a,
      (σ, a) ∈ morkRuntimeQueryExec0.computableSourceFactorMatch [] workspace src ∧
      applySubst σ (morkPatternToAtom (.fvar "__fact")) = morkPatternToAtom atom := by
  refine ⟨bindingsToSubst [("__fact", atom)], morkPatternToAtom atom, ?_, ?_⟩
  · exact
      morkRuntimeQueryExec0.sourceFactorComplete [] workspace _ _ _
        (by
          change (bindingsToSubst [("__fact", atom)], morkPatternToAtom atom) ∈
            matchSourceFactor [] workspace.toFinset (.btm (morkPatternToAtom (.fvar "__fact")))
          simp only [matchSourceFactor]
          apply matchOneInSpace_mem
          · exact List.mem_toFinset.mpr hatom_in
          · simpa [morkPatternToAtom, bindingsToSubst] using
              (matchAtom_var_bindingsToSubst_new ([] : ILBindings) "__fact" atom (by simp)))
  · show (([("__fact", morkPatternToAtom atom)] : Subst).lookup "__fact").getD (.var "__fact") =
      morkPatternToAtom atom
    simp

end Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
