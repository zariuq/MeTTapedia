import Mettapedia.GSLT.Contexts.ConstantMap
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.Branching
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.Hosting
import Mettapedia.GSLT.LanguageDef.Contexts.Interacting
import Mettapedia.Languages.ProcessCalculi.CCS.Section

/-!
# The constant map into CCS

From every presented theory there is a static map of theories to CCS that
sends every term to the inactive process.  A context of the source is sent to
the parallel composition of its holes; filled with inactive processes it is a
parallel composition of inactive processes, which the unit law of parallel
composition identifies with the inactive process.

So the static definition by pairs admits the constant map, whenever the target has a
composition with a unit.  It is the first non-degeneracy condition that
excludes it: the constant map out of the contact theory is not hosting.

Preservation of bisimilarity alone need not reflect it: the constant map
out of the branching theory sends two terms that are not bisimilar to one
term.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.Languages.ProcessCalculi.CCS
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.PatternCode

variable {arity : Type}

/-! ## The holes of a context, side by side -/

/-- The bag of the listed holes. -/
def holesBag (indices : List arity) : MultiHoleContext arity :=
  .collection .hashBag (indices.map .hole) none

theorem holes_holesBag (indices : List arity) :
    MultiHoleContext.holes (holesBag indices) = indices := by
  simp only [holesBag, MultiHoleContext.holes, MultiHoleContext.holesList_eq_flatMap]
  induction indices with
  | nil => rfl
  | cons index indices recurse =>
      simp only [List.map_cons, List.flatMap_cons, recurse]
      rfl

theorem fill_holesBag (filling : arity → Pattern) (indices : List arity) :
    MultiHoleContext.fill filling (holesBag indices) =
      .collection .hashBag (indices.map filling) none := by
  simp only [holesBag, MultiHoleContext.fill, MultiHoleContext.fillList_eq_map, List.map_map]
  congr 1

theorem mapContextSymbols_holesBag (symbols : LanguageDefSymbolMap) (indices : List arity) :
    mapContextSymbols symbols (holesBag indices) = holesBag indices := by
  simp only [holesBag, mapContextSymbols, mapContextSymbolsList_eq_map, List.map_map]
  congr 1

/-! ## Bags of processes -/

/-- The interface of closed processes of CCS. -/
abbrev ccsProc : Interface := interactingInterface ccsInteractivePresentation

/-- The inactive process. -/
def inactive : Term ccsValidatedLanguageDef.language ccsProc :=
  ofInteracting (presentation := ccsInteractivePresentation)
    (ClosedTerm.ofCheck (sort := ccsInteractivePresentation.interactingLangSort) nil
      (by decide +kernel))

/-- A bag of processes is a process, in CCS and in every presentation it maps
into. -/
theorem bag_sorted {extension : ValidatedLanguageDef}
    (morphism : StructuralMorphism ccsValidatedLanguageDef extension) (elements : List Pattern)
    (sorted : ∀ element ∈ elements,
      OpenPatternWellSorted extension.language FreeTypeContext.empty
        (ccsProc.map morphism.symbols).stage (ccsProc.map morphism.symbols).type element) :
    OpenPatternWellSorted extension.language FreeTypeContext.empty
      (ccsProc.map morphism.symbols).stage (ccsProc.map morphism.symbols).type
      (.collection .hashBag elements none) := by
  have typed : HasType extension.language FreeTypeContext.empty
      (ccsProc.map morphism.symbols).stage (.collection .hashBag elements none)
      (ccsProc.map morphism.symbols).type :=
    HasType.collectionConstructor
      (rule := mapGrammarRule morphism.symbols ccsParallelConstructor.1) (parameterName := "ps")
      (morphism.mapsTerms _ ccsParallelConstructor.2) rfl
      (elementsHaveType_iff.mpr fun element membership => (sorted element membership).1)
  refine ⟨typed, ?_, ?_, ?_⟩
  · simp only [Pattern.hasCanonicalBinderMetadata]
    exact hasCanonicalBinderMetadataList_iff.mpr fun element membership =>
      (sorted element membership).2.1
  · simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
    exact isObjectPatternList_iff.mpr fun element membership => (sorted element membership).2.2.1
  · simpa [ScopeSafeAt] using typed.isWellScopedAt

/-- **The parallel composition of the holes of a context**, as a context of
CCS. -/
def parallelOfHoles {source : ValidatedLanguageDef} {holes : arity → Interface}
    {result : Interface} (context : Context source holes result) :
    Context ccsValidatedLanguageDef (fun _ : arity => ccsProc) ccsProc where
  shape := holesBag context.shape.holes
  linear := by
    rw [MultiHoleContext.Linear, holes_holesBag]
    exact context.linear
  sorted := fun morphism filling => by
    rw [mapContextSymbols_holesBag, fill_holesBag]
    apply bag_sorted morphism
    intro element membership
    obtain ⟨index, -, rfl⟩ := List.mem_map.mp membership
    exact (filling index).2

/-! ## Inactive processes side by side are inactive -/

theorem bagContents_inactive (indices : List arity) :
    bagContents "CNil" (indices.map fun _ => nil) = [] := by
  induction indices with
  | nil => rfl
  | cons index indices recurse =>
      rw [List.map_cons, bagContents_cons, recurse]
      rfl

/-- The normal form of a bag of inactive processes is the inactive
process. -/
theorem normalForm_inactive_bag (indices : List arity) :
    normalForm (some "CNil") (.collection .hashBag (indices.map fun _ => nil) none) = nil := by
  have fixed : (indices.map fun _ => nil).map (normalForm (some "CNil")) =
      indices.map fun _ => nil := by
    rw [List.map_map]
    apply List.map_congr_left
    intro index _
    simp [Function.comp, nil, normalForm]
  rw [normalForm_bag, fixed]
  change collapse "CNil" (sortPatterns (bagContents "CNil" (indices.map fun _ => nil))) = nil
  rw [bagContents_inactive]
  simp [sortPatterns, collapse, nil]

/-- **A parallel composition of inactive processes is the inactive process**,
up to the static equivalence of CCS. -/
theorem parallelOfHoles_absorbs {source : ValidatedLanguageDef} {holes : arity → Interface}
    {result : Interface} (context : Context source holes result) :
    (termSetoid defaultBasePremises ccsValidatedLanguageDef.language ccsProc).r
      ((parallelOfHoles context).fill fun _ => inactive) inactive := by
  apply (termSetoid_ofInteracting_iff (presentation := ccsInteractivePresentation)
    defaultBasePremises (toClosed ((parallelOfHoles context).fill fun _ => inactive))
    (toClosed inactive)).mpr
  apply (ccsCanonicalSection.equivalent_iff_normalize_eq _ _).mpr
  apply Subtype.ext
  change normalForm (some "CNil") ((parallelOfHoles context).fill fun _ => inactive).1 =
    normalForm (some "CNil") nil
  have shape : ((parallelOfHoles context).fill fun _ => inactive).1 =
      .collection .hashBag (context.shape.holes.map fun _ => nil) none :=
    fill_holesBag _ context.shape.holes
  rw [shape, normalForm_inactive_bag]
  simp [nil, normalForm]

/-- The constant static map to the inactive process,
from every presented theory to CCS. -/
def constantToCCS (source : ValidatedLanguageDef) :
    ContextMap (contextTheory defaultBasePremises source)
      (contextTheory defaultBasePremises ccsValidatedLanguageDef) :=
  ContextMap.constant (source := contextTheory defaultBasePremises source)
    (target := contextTheory defaultBasePremises ccsValidatedLanguageDef) ccsProc inactive
    (fun context => parallelOfHoles context) (fun context => parallelOfHoles_absorbs context)

/-- **The constant map out of the contact theory is not hosting.** -/
theorem constantToCCS_not_hosting : ¬ (constantToCCS bareValidated).Hosting := by
  refine ContextMap.constant_not_hosting (source := contextTheory defaultBasePremises
    bareValidated) (target := contextTheory defaultBasePremises ccsValidatedLanguageDef)
    ccsProc inactive (fun context => parallelOfHoles context)
    (fun context => parallelOfHoles_absorbs context) (first := constantA) (second := constantB) ?_
  intro equivalent
  have same := (bare_equivalent_iff constantA constantB).mp equivalent
  have patterns : Interaction.Controls.EquationalContact.termA =
      Interaction.Controls.EquationalContact.termB := congrArg Subtype.val same
  revert patterns
  decide

/-- A static map preserving bisimilarity need not reflect it.  The two branching terms
are not bisimilar over all contexts of their theory, and the constant map
sends them to one term. -/
theorem constant_does_not_reflect :
    ¬ Branching.theory.fullProbe.Bisimilar (index := Branching.proc) Branching.early
        Branching.late ∧
      ((constantToCCS Branching.branchingValidated).push
        (contextTheory defaultBasePremises Branching.branchingValidated).fullProbe).Bisimilar
        (index := Branching.proc)
        ((constantToCCS Branching.branchingValidated).term Branching.early)
        ((constantToCCS Branching.branchingValidated).term Branching.late) :=
  ⟨Branching.early_late_not_bisimilar_fullProbe, ContextTheory.Probe.bisimilar_refl _ _⟩

end Mettapedia.GSLT.LanguageDef.Contexts.Controls
