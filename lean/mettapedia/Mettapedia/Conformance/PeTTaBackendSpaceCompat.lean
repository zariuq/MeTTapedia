import Mettapedia.Languages.MeTTa.RuntimeResource
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# PeTTa Backend-Space Compatibility

This file states the current **backend compatibility normalization** for the
real PeTTa-on-MORK/MM2 runtime:

- `&self` is the proved default atomspace surface.
- `&mork` is treated as a compatibility alias for that same default backend
  atomspace.
- arbitrary named spaces are **not** included in this theorem.

This is intentionally a conformance-layer fact about the current backend, not a
new core semantic law of PeTTa and not a change to the MORK model.

Positive example:
- `(match &mork pat tmpl)` normalizes to the already-proved `(match &self pat tmpl)`
  backend surface.

Negative example:
- `(match &foo pat tmpl)` does not normalize through this theorem and remains
  outside the current proved backend seam.
-/

namespace Mettapedia.Conformance.PeTTaBackendSpaceCompat

open Mettapedia.Languages.MeTTa.RuntimeKernel
open Mettapedia.Languages.MeTTa.RuntimeResource
open Mettapedia.Languages.ProcessCalculi.MORK

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- Backend-space references that normalize to the one currently proved default
atomspace on the MORK/MM2 backend. This is intentionally narrower than generic
named-space support. -/
inductive DefaultBackendSpaceRef : ILPattern → Prop where
  | self : DefaultBackendSpaceRef (.apply "&self" [])
  | mork : DefaultBackendSpaceRef (.apply "&mork" [])

/-- Normalize the current backend's default-space compatibility aliases onto the
single proved default atomspace surface, `&self`. -/
def normalizeDefaultBackendSpaceRef : ILPattern → ILPattern
  | .apply "&mork" [] => .apply "&self" []
  | p => p

/-- Normalize the currently supported default-space surface forms. This is a
backend compatibility translation, not a general PeTTa evaluator. -/
def normalizeDefaultBackendSpaceExpr : ILPattern → ILPattern
  | .apply "match" [spaceRef, pat, tmpl] =>
      .apply "match" [normalizeDefaultBackendSpaceRef spaceRef, pat, tmpl]
  | .apply "get-atoms" [spaceRef] =>
      .apply "get-atoms" [normalizeDefaultBackendSpaceRef spaceRef]
  | .apply "add-atom" [spaceRef, p] =>
      .apply "add-atom" [normalizeDefaultBackendSpaceRef spaceRef, p]
  | .apply "add-atom!" [spaceRef, p] =>
      .apply "add-atom!" [normalizeDefaultBackendSpaceRef spaceRef, p]
  | .apply "remove-atom" [spaceRef, p] =>
      .apply "remove-atom" [normalizeDefaultBackendSpaceRef spaceRef, p]
  | .apply "remove-atom!" [spaceRef, p] =>
      .apply "remove-atom!" [normalizeDefaultBackendSpaceRef spaceRef, p]
  | .apply "let" [varP, valP, bodyP] =>
      .apply "let"
        [ varP
        , normalizeDefaultBackendSpaceExpr valP
        , normalizeDefaultBackendSpaceExpr bodyP ]
  | .apply "chain" [valP, varP, bodyP] =>
      .apply "chain"
        [ normalizeDefaultBackendSpaceExpr valP
        , varP
        , normalizeDefaultBackendSpaceExpr bodyP ]
  | .apply "let*" [bindings, bodyP] =>
      .apply "let*"
        [ normalizeDefaultBackendSpaceExpr bindings
        , normalizeDefaultBackendSpaceExpr bodyP ]
  | .apply "progn" [e₁, e₂] =>
      .apply "progn"
        [ normalizeDefaultBackendSpaceExpr e₁
        , normalizeDefaultBackendSpaceExpr e₂ ]
  | .apply "prog1" [e₁, e₂] =>
      .apply "prog1"
        [ normalizeDefaultBackendSpaceExpr e₁
        , normalizeDefaultBackendSpaceExpr e₂ ]
  | .apply "collapse" [inner] =>
      .apply "collapse" [normalizeDefaultBackendSpaceExpr inner]
  | .apply ctor args =>
      .apply ctor (args.map normalizeDefaultBackendSpaceExpr)
  | .collection kind elems rest =>
      .collection kind (elems.map normalizeDefaultBackendSpaceExpr) rest
  | p => p

section ResourceFacts

theorem defaultBackendSpaceRef_on_proved_resource :
    queryFragment.resourceClass = defaultAtomSpaceDescriptor.resourceClass ∧
    spaceEffectFragment.resourceClass = defaultAtomSpaceDescriptor.resourceClass ∧
    defaultAtomSpaceDescriptor.hasProvedExecSeam = true ∧
    defaultAtomSpaceDescriptor.backendName = "MORK/MM2" := by
  exact ⟨query_resource, spaceEffect_resource, only_defaultAtomSpace_proved, rfl⟩

theorem defaultBackendSpaceRef_not_generic_namedSpace :
    namedAtomSpaceDescriptor.hasProvedExecSeam = false := namedAtomSpace_not_proved

end ResourceFacts

section NormalizationFacts

theorem normalizeDefaultBackendSpaceRef_eq_self
    {spaceRef : ILPattern} (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceRef spaceRef = .apply "&self" [] := by
  cases hspace <;> rfl

theorem normalizeDefaultBackendSpaceRef_other
    {spaceName : String}
    (hmork : spaceName ≠ "&mork") :
    normalizeDefaultBackendSpaceRef (.apply spaceName []) = .apply spaceName [] := by
  simp [normalizeDefaultBackendSpaceRef, hmork]

theorem not_defaultBackendSpaceRef_other
    {spaceName : String}
    (hself : spaceName ≠ "&self")
    (hmork : spaceName ≠ "&mork") :
    ¬ DefaultBackendSpaceRef (.apply spaceName []) := by
  intro hspace
  cases hspace with
  | self => exact hself rfl
  | mork => exact hmork rfl

theorem normalize_match_defaultBackendSpace
    {spaceRef pat tmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "match" [spaceRef, pat, tmpl]) =
      .apply "match" [.apply "&self" [], pat, tmpl] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_getAtoms_defaultBackendSpace
    {spaceRef : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "get-atoms" [spaceRef]) =
      .apply "get-atoms" [.apply "&self" []] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_addAtom_defaultBackendSpace
    {spaceRef p : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "add-atom" [spaceRef, p]) =
      .apply "add-atom" [.apply "&self" [], p] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_addAtomBang_defaultBackendSpace
    {spaceRef p : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "add-atom!" [spaceRef, p]) =
      .apply "add-atom!" [.apply "&self" [], p] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_removeAtom_defaultBackendSpace
    {spaceRef p : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "remove-atom" [spaceRef, p]) =
      .apply "remove-atom" [.apply "&self" [], p] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_removeAtomBang_defaultBackendSpace
    {spaceRef p : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "remove-atom!" [spaceRef, p]) =
      .apply "remove-atom!" [.apply "&self" [], p] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_collapse_match_defaultBackendSpace
    {spaceRef pat tmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "collapse" [.apply "match" [spaceRef, pat, tmpl]]) =
      .apply "collapse" [.apply "match" [.apply "&self" [], pat, tmpl]] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_match_removeAtomTemplate_defaultBackendSpace
    {spaceRef pat payload : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr
      (.apply "match"
        [spaceRef, pat, .apply "remove-atom" [spaceRef, payload]]) =
      .apply "match"
        [.apply "&self" [], pat, .apply "remove-atom" [spaceRef, payload]] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_collapse_match_removeAtomTemplate_defaultBackendSpace
    {spaceRef pat payload : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr
      (.apply "collapse"
        [.apply "match"
          [spaceRef, pat, .apply "remove-atom" [spaceRef, payload]]]) =
      .apply "collapse"
        [.apply "match"
          [.apply "&self" [], pat, .apply "remove-atom" [spaceRef, payload]]] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_collapse_getAtoms_defaultBackendSpace
    {spaceRef : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr (.apply "collapse" [.apply "get-atoms" [spaceRef]]) =
      .apply "collapse" [.apply "get-atoms" [.apply "&self" []]] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_let_collapse_match_defaultBackendSpace
    {varP bodyP spaceRef pat tmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr
      (.apply "let"
        [ varP
        , .apply "collapse" [.apply "match" [spaceRef, pat, tmpl]]
        , bodyP ]) =
      .apply "let"
        [ varP
        , .apply "collapse" [.apply "match" [.apply "&self" [], pat, tmpl]]
        , normalizeDefaultBackendSpaceExpr bodyP ] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_chain_match_defaultBackendSpace
    {spaceRef pat tmpl varP bodyP : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr
      (.apply "chain"
        [ .apply "match" [spaceRef, pat, tmpl]
        , varP
        , bodyP ]) =
      .apply "chain"
        [ .apply "match" [.apply "&self" [], pat, tmpl]
        , varP
        , normalizeDefaultBackendSpaceExpr bodyP ] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

theorem normalize_letStar_singleton_collapse_match_defaultBackendSpace
    {binder bodyP spaceRef pat tmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    normalizeDefaultBackendSpaceExpr
      (.apply "let*"
        [ .collection .vec
            [ .apply "pair"
                [ binder
                , .apply "collapse" [.apply "match" [spaceRef, pat, tmpl]] ] ]
            none
        , bodyP ]) =
      .apply "let*"
        [ .collection .vec
            [ .apply "pair"
                [ normalizeDefaultBackendSpaceExpr binder
                , .apply "collapse" [.apply "match" [.apply "&self" [], pat, tmpl]] ] ]
            none
        , normalizeDefaultBackendSpaceExpr bodyP ] := by
  simp [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef_eq_self hspace]

end NormalizationFacts

section QueryCompatibility

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment

theorem defaultBackendSpace_anyFactMatch_query
    {s : PeTTaSpace}
    {spaceRef : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef)
    {x : String} {tmpl fact q : ILPattern}
    (hfact : fact ∈ s.storedAtoms)
    (htrans_tmpl : morkTranslatable tmpl = true)
    (hq : Mettapedia.OSLF.MeTTaIL.Match.applyBindings [(x, fact)] tmpl = q) :
    PeTTaSpaceCoreQuery s
      (normalizeDefaultBackendSpaceExpr (.apply "match" [spaceRef, .fvar x, tmpl])) q := by
  simpa [normalize_match_defaultBackendSpace hspace] using
    (PeTTaSpaceCoreQuery.anyFactMatch
      (s := s) x tmpl fact q hfact htrans_tmpl hq)

theorem defaultBackendSpace_getAtoms_query
    {s : PeTTaSpace}
    {spaceRef : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef)
    {fact : ILPattern}
    (hfact : fact ∈ s.storedAtoms) :
    PeTTaSpaceCoreQuery s
      (normalizeDefaultBackendSpaceExpr (.apply "get-atoms" [spaceRef])) fact := by
  simpa [normalize_getAtoms_defaultBackendSpace hspace] using
    (PeTTaSpaceCoreQuery.getAtoms (s := s) fact hfact)

theorem defaultBackendSpace_match_eval
    (s : PeTTaSpace)
    {spaceRef pat tmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    PeTTaEval s
      (normalizeDefaultBackendSpaceExpr (.apply "match" [spaceRef, pat, tmpl]))
      (s.spaceMatch pat tmpl) := by
  simpa [normalize_match_defaultBackendSpace hspace] using
    petta_eval_spaceQuery_correct s pat tmpl

theorem defaultBackendSpace_collapse_match_eval
    (s : PeTTaSpace)
    {spaceRef pat tmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    PeTTaEval s
      (normalizeDefaultBackendSpaceExpr
        (.apply "collapse" [.apply "match" [spaceRef, pat, tmpl]]))
      [.collection .vec (s.spaceMatch pat tmpl) none] := by
  simpa [normalize_collapse_match_defaultBackendSpace hspace] using
    petta_eval_collapse_spaceQuery s pat tmpl

end QueryCompatibility

section NestedMatchBodyCompatibility

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Match

/-- If an outer match has already produced bindings `bs`, then an instantiated
default-backend-space nested `match` body evaluates through the already-proved
default backend query lane after backend-space normalization.

This is the core Lean-side protocol Rust should mirror: outer `spaceMatch`
instantiates the body, then the instantiated body itself re-enters the current
certified backend slice rather than being left as a shallow template result. -/
theorem defaultBackendSpace_instantiatedMatch_pettaEval
    (s : PeTTaSpace)
    {spaceRef innerPat innerTmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef)
    (bs : Bindings) :
    PeTTaEval s
      (normalizeDefaultBackendSpaceExpr
        (applyBindings bs (.apply "match" [spaceRef, innerPat, innerTmpl])))
      (s.spaceMatch (applyBindings bs innerPat) (applyBindings bs innerTmpl)) := by
  cases hspace with
  | self =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using petta_eval_spaceQuery_correct
          s
          (applyBindings bs innerPat)
          (applyBindings bs innerTmpl)
  | mork =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using petta_eval_spaceQuery_correct
          s
          (applyBindings bs innerPat)
          (applyBindings bs innerTmpl)

/-- Binding-threaded version of
`defaultBackendSpace_instantiatedMatch_pettaEval`: once outer bindings have
instantiated a nested `match` body, the resulting default-backend-space query is
still a certified `MeTTaEval` query lane. -/
theorem defaultBackendSpace_instantiatedMatch_meTTaEval
    (s : PeTTaSpace)
    {spaceRef innerPat innerTmpl ty : ILPattern}
    {bindings : Bindings}
    (hspace : DefaultBackendSpaceRef spaceRef)
    (bs : Bindings) :
    MeTTaEval s
      (normalizeDefaultBackendSpaceExpr
        (applyBindings bs (.apply "match" [spaceRef, innerPat, innerTmpl])))
      ty
      bindings
      ((s.spaceMatch (applyBindings bs innerPat) (applyBindings bs innerTmpl)).map (·, bindings)) := by
  cases hspace with
  | self =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using
          (MeTTaEval.spaceQuery
            (applyBindings bs innerPat)
            (applyBindings bs innerTmpl)
            ty
            bindings
            ((s.spaceMatch (applyBindings bs innerPat) (applyBindings bs innerTmpl)).map (·, bindings))
            rfl)
  | mork =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using
          (MeTTaEval.spaceQuery
            (applyBindings bs innerPat)
            (applyBindings bs innerTmpl)
            ty
            bindings
            ((s.spaceMatch (applyBindings bs innerPat) (applyBindings bs innerTmpl)).map (·, bindings))
            rfl)

/-- If an outer match has already produced bindings `bs`, then an instantiated
default-backend-space `collapse (match ...)` body evaluates through the current
certified aggregation-over-query slice after backend-space normalization. -/
theorem defaultBackendSpace_instantiatedCollapseMatch_pettaEval
    (s : PeTTaSpace)
    {spaceRef innerPat innerTmpl : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef)
    (bs : Bindings) :
    PeTTaEval s
      (normalizeDefaultBackendSpaceExpr
        (applyBindings bs
          (.apply "collapse" [.apply "match" [spaceRef, innerPat, innerTmpl]])))
      [.collection .vec
        (s.spaceMatch (applyBindings bs innerPat) (applyBindings bs innerTmpl))
        none] := by
  cases hspace with
  | self =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using petta_eval_collapse_spaceQuery
          s
          (applyBindings bs innerPat)
          (applyBindings bs innerTmpl)
  | mork =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using petta_eval_collapse_spaceQuery
          s
          (applyBindings bs innerPat)
          (applyBindings bs innerTmpl)

/-- Binding-threaded version of
`defaultBackendSpace_instantiatedCollapseMatch_pettaEval`: once outer bindings
have instantiated a nested `collapse (match ...)` body, the resulting default
backend expression stays inside the existing certified `MeTTaEval` aggregation
lane. -/
theorem defaultBackendSpace_instantiatedCollapseMatch_meTTaEval
    (s : PeTTaSpace)
    {spaceRef innerPat innerTmpl ty : ILPattern}
    {bindings : Bindings}
    (hspace : DefaultBackendSpaceRef spaceRef)
    (bs : Bindings) :
    MeTTaEval s
      (normalizeDefaultBackendSpaceExpr
        (applyBindings bs
          (.apply "collapse" [.apply "match" [spaceRef, innerPat, innerTmpl]])))
      ty
      bindings
      [(.collection .vec
          (s.spaceMatch (applyBindings bs innerPat) (applyBindings bs innerTmpl))
          none,
        bindings)] := by
  cases hspace with
  | self =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using
          (meTTaEval_collapse_spaceQuery
            (s := s)
            (pat := applyBindings bs innerPat)
            (tmpl := applyBindings bs innerTmpl)
            (ty := ty)
            (bindings := bindings))
  | mork =>
      simpa [normalizeDefaultBackendSpaceExpr, normalizeDefaultBackendSpaceRef]
        using
          (meTTaEval_collapse_spaceQuery
            (s := s)
            (pat := applyBindings bs innerPat)
            (tmpl := applyBindings bs innerTmpl)
            (ty := ty)
            (bindings := bindings))

end NestedMatchBodyCompatibility

section StatefulCompatibility

open Mettapedia.Languages.MeTTa.PeTTa

theorem defaultBackendSpace_getAtoms_coreDecl
    (s : EvalState)
    {spaceRef : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef) :
    CoreDecl s
      (normalizeDefaultBackendSpaceExpr (.apply "get-atoms" [spaceRef]))
      s
      s.space.storedAtoms := by
  simpa [normalize_getAtoms_defaultBackendSpace hspace] using
    (CoreDecl.getAtoms s)

end StatefulCompatibility

section SpaceEffectCompatibility

open Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment

theorem defaultBackendSpace_addAtom_fireSourceRule_mem
    {spaceRef p : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef)
    {workspace : Space}
    (hcmd_in :
      morkPatternToAtom
        (normalizeDefaultBackendSpaceExpr (.apply "add-atom" [spaceRef, p])) ∈ workspace) :
    applySinks workspace [("x", morkPatternToAtom p)] addAtomSourceExecRule.tmpl ∈
      fireSourceRule workspace addAtomSourceExecRule := by
  have hcmd_self :
      morkPatternToAtom (.apply "add-atom" [.apply "&self" [], p]) ∈ workspace := by
    simpa [normalize_addAtom_defaultBackendSpace hspace] using hcmd_in
  simpa using addAtom_fireSourceRule_mem (p := p) (workspace := workspace) hcmd_self

theorem defaultBackendSpace_removeAtom_fireSourceRule_mem
    {spaceRef p : ILPattern}
    (hspace : DefaultBackendSpaceRef spaceRef)
    {workspace : Space}
    (hcmd_in :
      morkPatternToAtom
        (normalizeDefaultBackendSpaceExpr (.apply "remove-atom" [spaceRef, p])) ∈ workspace) :
    applySinks workspace [("x", morkPatternToAtom p)] removeAtomSourceExecRule.tmpl ∈
      fireSourceRule workspace removeAtomSourceExecRule := by
  have hcmd_self :
      morkPatternToAtom (.apply "remove-atom" [.apply "&self" [], p]) ∈ workspace := by
    simpa [normalize_removeAtom_defaultBackendSpace hspace] using hcmd_in
  simpa using
    removeAtom_fireSourceRule_mem (p := p) (workspace := workspace) hcmd_self

end SpaceEffectCompatibility

section Canaries

#check @DefaultBackendSpaceRef
#check @normalizeDefaultBackendSpaceRef
#check @normalizeDefaultBackendSpaceExpr
#check @defaultBackendSpaceRef_on_proved_resource
#check @normalize_match_defaultBackendSpace
#check @normalize_match_removeAtomTemplate_defaultBackendSpace
#check @normalize_collapse_match_removeAtomTemplate_defaultBackendSpace
#check @defaultBackendSpace_match_eval
#check @defaultBackendSpace_collapse_match_eval
#check @defaultBackendSpace_getAtoms_coreDecl
#check @defaultBackendSpace_addAtom_fireSourceRule_mem
#check @defaultBackendSpace_removeAtom_fireSourceRule_mem

end Canaries

section AxiomAudit

#print axioms defaultBackendSpaceRef_on_proved_resource
#print axioms normalize_match_removeAtomTemplate_defaultBackendSpace
#print axioms normalize_collapse_match_removeAtomTemplate_defaultBackendSpace
#print axioms defaultBackendSpace_match_eval
#print axioms defaultBackendSpace_collapse_match_eval
#print axioms defaultBackendSpace_getAtoms_coreDecl
#print axioms defaultBackendSpace_addAtom_fireSourceRule_mem
#print axioms defaultBackendSpace_removeAtom_fireSourceRule_mem

end AxiomAudit

end Mettapedia.Conformance.PeTTaBackendSpaceCompat
