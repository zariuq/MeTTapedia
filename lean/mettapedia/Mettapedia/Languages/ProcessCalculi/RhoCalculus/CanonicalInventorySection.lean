import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventorySupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteWhole
import Mettapedia.GSLT.LanguageDef.CanonicalConstructorSupport
import Mettapedia.GSLT.LanguageDef.Cost.FiniteStaticTyping

/-!
# Executable contextual sections for the rho declaration inventory

Sorting and reflective support come from the concrete grammar inventory.
Equation invariance checks the authored quote/drop equation and the declared
parallel algebra. The normalizer is the existing executable rho function;
there is no representative choice or assumed normalization closure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventory
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open CanonicalMatch CanonicalSupport LanguageDefCanonicalSection LanguageDefSemanticAgreement

variable {language : LanguageDef}

/-- Every algebra row is the existing parallel declaration. -/
theorem algebra_shape (inventory : CanonicalInventory language)
    {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (declared : AlgebraRule language rule kind algebra) :
    kind = .hashBag ∧ algebra.flatten = true ∧ algebra.unit = some "PZero" := by
  obtain ⟨parameter, parameters⟩ := declared.selfSorted
  have row := inventory.collection_row declared.authored
    ⟨parameter, kind, .base rule.category, parameters⟩
  subst rule
  have algebraShape := declared.declared
  simp [rhoCalc, TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at parameters algebraShape
  obtain ⟨_, rfl⟩ := parameters
  subst algebra
  exact ⟨rfl, rfl, rfl⟩

/-- No set carrier can appear in this inventory. -/
theorem no_set_carrier (inventory : CanonicalInventory language) {rule : GrammarRule} :
    ¬ CollectionCarrierRule language rule .hashSet := by
  intro carrier
  obtain ⟨parameter, element, parameters⟩ := carrier.selfSorted
  have row := inventory.collection_row carrier.authored
    ⟨parameter, .hashSet, element, parameters⟩
  subst rule
  simp [rhoCalc, TypeExpr.bag] at parameters

/-- The sole authored equation has no language-dependent premise evaluation. -/
theorem equationInstance_canonicalize_eq
    (equations : ∀ equation ∈ language.equations, equation ∈ rhoCalc.equations)
    {fuel : Nat} {source target : Pattern}
    (witness : EquationInstanceAt defaultBasePremises language fuel source target) :
    Canonical.canonicalize source = Canonical.canonicalize target := by
  have sourceInstance : EquationInstanceAt defaultBasePremises rhoCalc fuel source target := by
    cases witness with
    | forward member matched premises same =>
      have oldMember := equations _ member
      have empty : _ := List.mem_singleton.mp oldMember
      have premiseShape : _ := congrArg Equation.premises empty
      change _ = [] at premiseShape
      rw [premiseShape] at premises
      cases premises
      exact .forward oldMember matched (by rw [premiseShape]; exact .nil _) same
    | reverse member matched premises same =>
      have oldMember := equations _ member
      have empty : _ := List.mem_singleton.mp oldMember
      have premiseShape : _ := congrArg Equation.premises empty
      change _ = [] at premiseShape
      rw [premiseShape] at premises
      cases premises
      exact .reverse oldMember matched (by rw [premiseShape]; exact .nil _) same
  exact rhoEquationContextStep_canonicalize_eq
    (.core (.inContext .hole (Or.inl ⟨fuel, sourceInstance⟩)))

/-- Permutation of a closed parallel bag preserves the canonical
representative. -/
private theorem canonicalize_bag_perm {elements elements' : List Pattern}
    (permutation : List.Perm elements elements') :
    Canonical.canonicalize (.collection .hashBag elements none) =
      Canonical.canonicalize (.collection .hashBag elements' none) := by
  change Canonical.collapseBag
      (Canonical.normalizeBagElements (Canonical.canonicalizeList elements)) =
    Canonical.collapseBag
      (Canonical.normalizeBagElements (Canonical.canonicalizeList elements'))
  rw [Canonical.normalizeBagElements_eq_of_perm
    (Canonical.canonicalizeList_perm permutation)]

/-- A leading unit element of a closed parallel bag is absorbed by the
canonical representative. -/
private theorem canonicalize_bag_zero_cons (rest : List Pattern) :
    Canonical.canonicalize
        (.collection .hashBag (.apply "PZero" [] :: rest) none) =
      Canonical.canonicalize (.collection .hashBag rest none) := by
  change Canonical.collapseBag
      (Canonical.normalizeBagElements
        (Canonical.canonicalizeList (.apply "PZero" [] :: rest))) =
    Canonical.collapseBag
      (Canonical.normalizeBagElements (Canonical.canonicalizeList rest))
  have head : Canonical.canonicalizeList (.apply "PZero" [] :: rest) =
      .apply "PZero" [] :: Canonical.canonicalizeList rest := by
    simp [Canonical.canonicalizeList, Canonical.canonicalize]
  rw [head, Canonical.normalizeBagElements_zero_cons]

/-- Each presentation-derived law of the generic rho equation relation
preserves the established canonical representative.  Rho declares no sets, so
the set laws cannot fire; the bag laws are the canonicalizer's own
normalization steps. -/
theorem derivedInstance_canonicalize_eq (inventory : CanonicalInventory language)
    {source target : Pattern}
    (derived : DerivedInstance language source target) :
    Canonical.canonicalize source = Canonical.canonicalize target := by
  cases derived with
  | bagPerm _ _ permutation =>
      exact canonicalize_bag_perm permutation
  | setPerm declaration _ _ =>
      exact False.elim (inventory.no_set_carrier declaration)
  | setDedup declaration _ =>
      exact False.elim (inventory.no_set_carrier declaration)
  | @flatten rule kind algebra pre inner post algebraRule _ _ =>
      obtain ⟨rfl, _, _⟩ := inventory.algebra_shape algebraRule
      have toEnd : List.Perm (pre ++ (.collection .hashBag inner none) :: post)
          ((pre ++ post) ++ [.collection .hashBag inner none]) :=
        List.perm_middle.trans (List.perm_append_singleton _ _).symm
      have fromEnd : List.Perm ((pre ++ post) ++ inner) (pre ++ inner ++ post) := by
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left pre List.perm_append_comm
      rw [canonicalize_bag_perm toEnd, Canonical.canonicalize_parallel_flatten,
        canonicalize_bag_perm fromEnd]
  | singleton algebraRule _ _ =>
      obtain ⟨rfl, _, _⟩ := inventory.algebra_shape algebraRule
      exact Canonical.canonicalize_parallel_singleton _
  | @unitElim rule kind algebra unit pre post algebraRule unitEq _ =>
      obtain ⟨rfl, _, unitShape⟩ := inventory.algebra_shape algebraRule
      rw [unitShape] at unitEq
      cases unitEq
      have toFront : List.Perm (pre ++ (.apply "PZero" []) :: post)
          (.apply "PZero" [] :: (pre ++ post)) := List.perm_middle
      rw [canonicalize_bag_perm toFront, canonicalize_bag_zero_cons]
  | @emptyUnit rule kind algebra unit algebraRule unitEq _ =>
      obtain ⟨rfl, _, unitShape⟩ := inventory.algebra_shape algebraRule
      rw [unitShape] at unitEq
      cases unitEq
      rw [Canonical.canonicalize_parallel_empty]
      simp [Canonical.canonicalize, Canonical.canonicalizeList]

/-- Every contextual generator preserves the established representative.
The section below uses this raw theorem in each exact typed open fibre. -/
theorem equationContextStep_canonicalize_eq (inventory : CanonicalInventory language)
    (equations : ∀ equation ∈ language.equations, equation ∈ rhoCalc.equations)
    {left right : Pattern}
    (generator : ReflectiveEquationContextStep rhoReflectionProfile
      defaultBasePremises language left right) :
    Canonical.canonicalize left = Canonical.canonicalize right := by
  cases generator with
  | core coreGenerator =>
    cases coreGenerator with
    | @inContext context redex contractum equationWitness =>
      have rootCanonical :
          Canonical.canonicalize redex = Canonical.canonicalize contractum := by
        rcases equationWitness with ⟨fuel, bounded⟩ | derived
        · exact equationInstance_canonicalize_eq equations bounded
        · exact inventory.derivedInstance_canonicalize_eq derived
      have rootReflective :
          canonicalize rhoReflectivePresentation redex =
            canonicalize rhoReflectivePresentation contractum := by
        simpa only [derivedCanonicalize_eq] using rootCanonical
      have contextual := canonicalize_fill_congr
        rhoReflectivePresentation context rootReflective
      simpa only [derivedCanonicalize_eq] using contextual
  | @reflectiveInContext context declaration reflectedLeft reflectedRight
      membership representatives =>
      have declarationEquality : declaration = rhoReflectivePresentation := by
        change List.Mem declaration [rhoReflectivePresentation] at membership
        cases membership with
        | head => rfl
        | tail _ impossible => cases impossible
      rw [declarationEquality] at representatives
      have contextual := canonicalize_fill_congr
        rhoReflectivePresentation context representatives
      simpa only [derivedCanonicalize_eq] using contextual

private theorem canonicalize_metadata {pattern : Pattern}
    (metadata : pattern.hasCanonicalBinderMetadata = true) :
    (Canonical.canonicalize pattern).hasCanonicalBinderMetadata = true := by
  simpa only [canonicalizeByAt_const, canonicalizeBy_patternCode, derivedCanonicalize_eq] using
    canonicalizeByAt_hasCanonicalBinderMetadata
      (fun _ pattern => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
      rhoReflectivePresentation 0 pattern metadata

/-- The computed representative stays in its exact open reflective fibre. -/
def normalizeOpen (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr} {sort : LangSort language}
    (term : ReflectiveWellSorted.OpenTerm rhoReflectionProfile language free bound sort) :
    ReflectiveWellSorted.OpenTerm rhoReflectionProfile language free bound sort := by
  let typed := inventory.canonicalize_hasType term.2.1.1 (by trivial) term.2.1.2.2.1
  exact ⟨Canonical.canonicalize term.1,
    ⟨typed, canonicalize_metadata term.2.1.2.1,
      canonicalize_isObjectPattern term.2.1.2.2.1, typed.isWellScopedAt⟩,
    canonicalize_reflectiveScopeSafeAt term.2.2⟩

@[simp] theorem normalizeOpen_pattern (inventory : CanonicalInventory language)
    {free : FreeTypeContext} {bound : List TypeExpr} {sort : LangSort language}
    (term : ReflectiveWellSorted.OpenTerm rhoReflectionProfile language free bound sort) :
    (inventory.normalizeOpen term).1 = Canonical.canonicalize term.1 := rfl

/-- Construct the actual contextual canonical section from declaration and
equation inventories. No section or normalizer law is supplied as a premise. -/
def contextualSection (theory : IGSLT)
    (inventory : CanonicalInventory theory.presentation.presentation.language)
    (admitted : ReflectionExtension.validate
      theory.presentation.presentation.language rhoReflectionProfile = [])
    (equations : ∀ equation ∈ theory.presentation.presentation.language.equations,
      equation ∈ rhoCalc.equations) :
    ComputableReflectiveFiberContextualSection theory ⟨rhoReflectionProfile, admitted⟩ where
  normalize := inventory.normalizeOpen
  equivalent := by
    intro free bound sort term
    apply Relation.EqvGen.rel
    apply ReflectiveEquationContextStep.reflectiveInContext .hole
      (show rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoReflectionProfile.presentations from by simp [rhoReflectionProfile])
    change canonicalize rhoReflectivePresentation (Canonical.canonicalize term.1) =
      canonicalize rhoReflectivePresentation term.1
    simpa only [derivedCanonicalize_eq] using Canonical.canonicalize_idempotent term.1
  complete := by
    intro free bound sort left right equivalent
    induction equivalent with
    | rel left right generator =>
      apply Subtype.ext
      exact inventory.equationContextStep_canonicalize_eq equations generator
    | refl term => rfl
    | symm left right relation ih => exact ih.symm
    | trans left middle right first second firstIH secondIH => exact firstIH.trans secondIH
  preservesFreeVariableSupport := by
    intro free bound sort term name member
    change name ∈ (Canonical.canonicalize term.1).freeFvarNames at member
    rw [← derivedCanonicalize_eq term.1] at member
    exact (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.mem_freeFvarNames_canonicalize_iff
      rhoReflectivePresentation name term.1).mp member
  normalizeRecontextualizeFree := by intros; rfl
  preservesReflectiveSupport := by
    intro free bound sort term support available binderImage safe
    obtain ⟨normalized, preserved⟩ := inventory.canonicalize_supportSafe term.2.1.1 safe
      (by trivial) term.2.1.2.2.1
    exact HasType.ReflectiveSupportSafeAt.castTyping
      (source := normalized) (target := (inventory.normalizeOpen term).2.1.1) preserved

/-- The actual three-payload synchronous source has an executable open
contextual section, with the already admitted source reflection profile. -/
def synchronousContextualSection :
    ComputableReflectiveFiberContextualSection Synchronous.rhoSyncIGSLT
      Synchronous.FiniteWhole.sourceReflection :=
  contextualSection Synchronous.rhoSyncIGSLT synchronous
    Synchronous.FiniteWhole.sourceReflection.2 (fun _ member => member)

@[simp] theorem synchronousContextualSection_pattern
    {free : FreeTypeContext} {bound : List TypeExpr} {sort : LangSort Synchronous.rhoSyncCalc}
    (term : ReflectiveWellSorted.OpenTerm rhoReflectionProfile Synchronous.rhoSyncCalc free bound sort) :
    (synchronousContextualSection.normalize term).1 = Canonical.canonicalize term.1 := rfl

/-- The same construction specializes to the exact asynchronous normalizer. -/
theorem asynchronous_normalizer_agreement
    {free : FreeTypeContext} {bound : List TypeExpr} {sort : LangSort rhoCalc}
    (term : ReflectiveWellSorted.OpenTerm rhoReflectionProfile rhoCalc free bound sort) :
    asynchronous.normalizeOpen term = rhoContextualOpenSection.normalize term := by
  apply Subtype.ext
  rfl

/-- The actual synchronous continuation fragment admits every distinguished
constructor used by reflection and parallel normalization. -/
theorem synchronous_reflectiveConstructorsAllowed :
    ReflectiveConstructorsAllowed (· ∈ Synchronous.communicationDecoration.wrappedLabels)
      rhoReflectivePresentation :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem synchronous_bareConstructorsAllowed (rule : GrammarRule)
    (member : rule ∈ Synchronous.rhoSyncCalc.terms) (bare : UsesBareCollection rule) :
    rule.label ∈ Synchronous.communicationDecoration.wrappedLabels := by
  have exactRule := synchronous.collection_row member bare
  subst rule
  decide +kernel

/-- Normalization preserves the actual declaration-aware static fragment,
including the declaration hidden by bare parallel syntax. -/
theorem synchronous_preservesTypedConstructors :
    synchronousContextualSection.PreservesTypedConstructors
      (· ∈ Synchronous.communicationDecoration.wrappedLabels) := by
  apply synchronousContextualSection.preservesTypedConstructors_reflective
    rhoReflectivePresentation
  · intro free bound sort term
    exact (derivedCanonicalize_eq term.1).symm
  · exact synchronous_reflectiveConstructorsAllowed
  · exact synchronous_bareConstructorsAllowed

/-- The normalized synchronous frame transports into either static colour
of its actual finite Cost language. Principal introductions remain outside
this frame theorem; the source normalizer itself handles the whole language. -/
theorem synchronous_normalized_static_transport (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr} {sort : LangSort Synchronous.rhoSyncCalc}
    (term : ReflectiveWellSorted.OpenTerm rhoReflectionProfile Synchronous.rhoSyncCalc free bound sort)
    (supported : HasTypeWithConstructors Synchronous.rhoSyncCalc
      (· ∈ Synchronous.communicationDecoration.wrappedLabels) free bound term.1 (.base sort.1)) :
    HasType Synchronous.communicationDecoration.costWholeLanguage
      (free.map (color.symbolsOf Synchronous.rhoSyncIGSLT))
      (bound.map (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT)))
      (mapPattern (color.symbolsOf Synchronous.rhoSyncIGSLT)
        (synchronousContextualSection.normalize term).1)
      (mapTypeExpr (color.symbolsOf Synchronous.rhoSyncIGSLT) (.base sort.1)) :=
  FiniteStaticTypingControls.synchronous_mapStatic_hasType color
    (synchronous_preservesTypedConstructors term supported)

namespace Controls

/-- The receiver body uses both its local name and the outer name. Its two
output continuations and nested closed quotation have nontrivial normal forms. -/
def openSynchronousInput : Pattern :=
  .apply "PInput" [.bvar 0, .lambda none
    (.apply "POutputK"
      [.apply "NQuote" [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]],
       .collection .hashBag [.apply "PZero" [], .apply "PDrop" [.bvar 0]] none,
       .collection .hashBag [.apply "PZero" [], .apply "PDrop" [.bvar 1]] none])]

def normalizedSynchronousInput : Pattern :=
  .apply "PInput" [.bvar 0, .lambda none
    (.apply "POutputK"
      [.apply "NQuote" [.apply "PZero" []],
       .apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 1]])]

def processSort : LangSort Synchronous.rhoSyncCalc := ⟨"Proc", by decide⟩

theorem openSynchronousInput_typed :
    HasSort Synchronous.rhoSyncCalc (fun _ => none) [.base "Name"] openSynchronousInput "Proc" :=
  checkHasType_sound (by decide +kernel)

/-- This is an inhabitant of the full reflective open carrier, including
quotation sealing, rather than only the ordinary typing judgment. -/
def openSynchronousTerm : ReflectiveWellSorted.OpenTerm rhoReflectionProfile
    Synchronous.rhoSyncCalc (fun _ => none) [.base "Name"] processSort :=
  ⟨openSynchronousInput,
    ⟨openSynchronousInput_typed, rfl, rfl, openSynchronousInput_typed.isWellScopedAt⟩,
    by
      intro declaration member
      have same : declaration = rhoReflectivePresentation := by
        simpa [rhoReflectionProfile] using member
      subst declaration
      decide +kernel⟩

theorem openSynchronousTerm_normalizes :
    (synchronousContextualSection.normalize openSynchronousTerm).1 =
      normalizedSynchronousInput := by
  rw [synchronousContextualSection_pattern]
  simp [openSynchronousTerm, openSynchronousInput, normalizedSynchronousInput,
    Canonical.canonicalize, Canonical.canonicalizeList, Canonical.normalizeQuote,
    Canonical.normalizeBagElements, Canonical.bagSplice, Canonical.sortPatterns,
    Canonical.collapseBag]

theorem openSynchronousTerm_changes :
    openSynchronousTerm.1 ≠ (synchronousContextualSection.normalize openSynchronousTerm).1 := by
  rw [openSynchronousTerm_normalizes]
  decide

/-- A raw collection result is excluded for a concrete reason: empty bag
normalization returns the authored process unit, not a collection value. -/
theorem raw_collection_type_boundary :
    HasType Synchronous.rhoSyncCalc (fun _ => none) [] (.collection .hashBag [] none)
      (.collection .hashBag (.base "Proc")) ∧
    ¬ HasType Synchronous.rhoSyncCalc (fun _ => none) []
      (Canonical.canonicalize (.collection .hashBag [] none))
      (.collection .hashBag (.base "Proc")) := by
  refine ⟨.collection (.nil _ _), ?_⟩
  intro typed
  rw [Canonical.canonicalize_parallel_empty] at typed
  obtain ⟨rule, _, _, impossible, _, _⟩ := typed.apply_inv
  cases impossible

end Controls
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventory
