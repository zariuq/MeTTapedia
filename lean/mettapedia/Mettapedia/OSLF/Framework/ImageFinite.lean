import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.KSUnificationSketch

/-!
# OSLF Image-Finiteness Instantiations

Concrete finite-branching lemmas for `LanguageDef`-induced one-step semantics,
plus direct HM-converse wrappers for those relations.
-/

namespace Mettapedia.OSLF.Framework.ImageFinite

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.KSUnificationSketch

/-- Executable one-step semantics from a `LanguageDef` is image-finite:
successors are exactly a finite list returned by the engine. -/
theorem imageFinite_langReducesExecUsing
    (relEnv : RelationEnv) (lang : LanguageDef) (p : Pattern) :
    Set.Finite { q : Pattern | langReducesExecUsing relEnv lang p q } := by
  change Set.Finite { q : Pattern | q ∈ rewriteWithContextWithPremisesUsing relEnv lang p }
  exact List.finite_toSet (rewriteWithContextWithPremisesUsing relEnv lang p)

/-- Declarative one-step semantics from a `LanguageDef` is image-finite, using
the executable/declarative equivalence. -/
theorem imageFinite_langReducesUsing
    (relEnv : RelationEnv) (lang : LanguageDef) (p : Pattern) :
    Set.Finite { q : Pattern | langReducesUsing relEnv lang p q } := by
  apply Set.Finite.subset (imageFinite_langReducesExecUsing relEnv lang p)
  intro q hq
  exact (langReducesUsing_iff_execUsing relEnv lang p q).1 hq

/-- Default-env one-step semantics is image-finite. -/
theorem imageFinite_langReduces
    (lang : LanguageDef) (p : Pattern) :
    Set.Finite { q : Pattern | langReduces lang p q } := by
  simpa [langReduces] using
    (imageFinite_langReducesUsing RelationEnv.empty lang p)

/-- HM converse instantiated for `langReducesUsing` (parametric in `RelationEnv`). -/
theorem hm_converse_langReducesUsing
    (relEnv : RelationEnv) (lang : LanguageDef) (I : AtomSem)
    {p q : Pattern}
    (hobs : OSLFObsEq (langReducesUsing relEnv lang) I p q) :
    Bisimilar (langReducesUsing relEnv lang) p q := by
  exact
    hm_converse_schema
      (R := langReducesUsing relEnv lang)
      (I := I)
      (hImageFinite := imageFinite_langReducesUsing relEnv lang)
      hobs

/-- HM converse instantiated for default-env `langReduces`. -/
theorem hm_converse_langReduces
    (lang : LanguageDef) (I : AtomSem)
    {p q : Pattern}
    (hobs : OSLFObsEq (langReduces lang) I p q) :
    Bisimilar (langReduces lang) p q := by
  exact
    hm_converse_schema
      (R := langReduces lang)
      (I := I)
      (hImageFinite := imageFinite_langReduces lang)
      hobs

end Mettapedia.OSLF.Framework.ImageFinite
