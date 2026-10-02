import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedEquationPresentation

/-!
# Generated collection units require generated constructor references

The generated rho language contains no constructor with the untagged source
zero label. A collection declaration referring to that label therefore cannot
license the derived algebra laws. This control concerns the unit reference;
it does not claim that the live generated parallel rows retain stale metadata.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionMetadataBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.EquationSemantics

abbrev language := GeneratedEquationPresentation.language

/-- Constructor generation changes both copies of the source zero label. -/
theorem untagged_zero_absent :
    "PZero" ∉ language.terms.map GrammarRule.label := by
  decide +kernel

/-- Merely copying the source unit reference cannot supply an actual algebra
declaration in the generated language, regardless of the flattening flag. -/
theorem untagged_unit_not_licensed (rule : GrammarRule) (kind : CollType)
    (flatten : Bool) :
    ¬ AlgebraRule language rule kind ⟨flatten, some "PZero"⟩ := by
  intro declaration
  obtain ⟨unitRule, member, label, _, _⟩ := declaration.unitAuthored "PZero" rfl
  apply untagged_zero_absent
  exact List.mem_map.mpr ⟨unitRule, member, label⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionMetadataBoundary
