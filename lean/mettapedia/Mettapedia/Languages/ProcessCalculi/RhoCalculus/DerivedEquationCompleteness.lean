import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Generic equals bespoke: the presentation-derived rho equations reach the
canonical structural congruence

The authored `rhoCalc` presentation generates, without any reflection
profile, the equation theory `EquationEquiv base rhoCalc`: the authored
quote/drop equation together with the laws derived from the bag tag and the
declared parallel algebra.  This module proves that on closed, well-sorted
processes this core theory is exactly the established canonical structural
congruence:

* every canonicalization step is an equation of the core theory, so a closed
  process is equivalent to its canonical form; and
* every core generator preserves the canonical form (already established in
  the agreement module), so equivalent processes have equal canonical forms.

Consequently the reflective canonical-equality generator that the agreement
module admits is conservative over the core theory for rho: it adds no
identification that the presentation-derived laws do not already supply.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement

set_option autoImplicit false

/-- The core generated equation theory of the authored rho presentation. -/
abbrev CoreEquiv (base : BasePremiseEvaluator) : Pattern → Pattern → Prop :=
  EquationEquiv base rhoCalc

/-! ## The declared parallel algebra and its laws -/

/-- The authored parallel rule, with its algebra declaration. -/
def pparRule : GrammarRule :=
  { label := "PPar", category := "Proc",
    params := [.simple "ps" (TypeExpr.bag TypeExpr.proc)],
    syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
    algebra? := some { flatten := true, unit := some "PZero" } }

/-- The authored nil rule. -/
def pzeroRule : GrammarRule :=
  { label := "PZero", category := "Proc", params := [],
    syntaxPattern := [.terminal "0"] }

theorem pparRule_mem : pparRule ∈ rhoCalc.terms := by
  simp [rhoCalc, pparRule]

theorem pzeroRule_mem : pzeroRule ∈ rhoCalc.terms := by
  simp [rhoCalc, pzeroRule]

/-- Rho's parallel bag is a declared collection algebra with unit `PZero`. -/
theorem rhoParallelAlgebra :
    AlgebraRule rhoCalc pparRule .hashBag { flatten := true, unit := some "PZero" } where
  authored := pparRule_mem
  declared := rfl
  selfSorted := ⟨"ps", rfl⟩
  unitAuthored := by
    intro unit unitEq
    obtain rfl := Option.some.inj unitEq
    exact ⟨pzeroRule, pzeroRule_mem, rfl, rfl, rfl⟩

theorem rhoCalc_usesBags : rhoCalc.usesCollection .hashBag = true := by
  decide

/-- The bare `PPar` rule is the declared bag carrier of rho processes. -/
theorem rhoParallelCarrier :
    CollectionCarrierRule rhoCalc pparRule .hashBag where
  authored := pparRule_mem
  selfSorted := ⟨"ps", TypeExpr.proc, rfl⟩

/-- A bag of sorted processes is sorted at the process sort. -/
theorem sortedAt_bag {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound elements TypeExpr.proc) :
    SortedAt rhoCalc (.collection .hashBag elements none) "Proc" :=
  ⟨free, bound, rho_parallel_hasSort typed⟩

section Laws

variable {base : BasePremiseEvaluator}

theorem coreEquiv_bagPerm {free : FreeTypeContext} {bound : List TypeExpr}
    {elements elements' : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound elements TypeExpr.proc)
    (permutation : List.Perm elements elements') :
    CoreEquiv base (.collection .hashBag elements none)
      (.collection .hashBag elements' none) :=
  equationEquiv_bag_perm rhoParallelCarrier (sortedAt_bag typed) permutation

theorem coreEquiv_flatten {free : FreeTypeContext} {bound : List TypeExpr}
    {pre inner post : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound
      (pre ++ (.collection .hashBag inner none) :: post) TypeExpr.proc) :
    CoreEquiv base
      (.collection .hashBag (pre ++ (.collection .hashBag inner none) :: post) none)
      (.collection .hashBag (pre ++ inner ++ post) none) :=
  derivedInstance_equivalent
    (DerivedInstance.flatten rhoParallelAlgebra rfl (sortedAt_bag typed))

theorem coreEquiv_singleton {free : FreeTypeContext} {bound : List TypeExpr}
    {element : Pattern}
    (typed : ElementsHaveType rhoCalc free bound [element] TypeExpr.proc) :
    CoreEquiv base (.collection .hashBag [element] none) element :=
  derivedInstance_equivalent
    (DerivedInstance.singleton rhoParallelAlgebra rfl (sortedAt_bag typed))

theorem coreEquiv_unitElim {free : FreeTypeContext} {bound : List TypeExpr}
    {pre post : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound
      (pre ++ (.apply "PZero" []) :: post) TypeExpr.proc) :
    CoreEquiv base
      (.collection .hashBag (pre ++ (.apply "PZero" []) :: post) none)
      (.collection .hashBag (pre ++ post) none) :=
  derivedInstance_equivalent
    (DerivedInstance.unitElim rhoParallelAlgebra rfl (sortedAt_bag typed))

theorem coreEquiv_empty :
    CoreEquiv base (.collection .hashBag [] none) (.apply "PZero" []) :=
  derivedInstance_equivalent
    (DerivedInstance.emptyUnit rhoParallelAlgebra rfl
      (sortedAt_bag (free := FreeTypeContext.empty) (.nil [] TypeExpr.proc)))

/-- The authored quote/drop equation, instantiated at any name. -/
def quoteDropEquation : Equation :=
  { name := "QuoteDrop",
    typeContext := [("N", TypeExpr.name)],
    premises := [],
    left := .apply "NQuote" [.apply "PDrop" [.fvar "N"]],
    right := .fvar "N" }

theorem quoteDropEquation_mem : List.Mem quoteDropEquation rhoCalc.equations :=
  List.Mem.head _

theorem coreEquiv_quoteDrop (name : Pattern) :
    CoreEquiv base (.apply "NQuote" [.apply "PDrop" [name]]) name := by
  apply EquationSemantics.equationInstance_equivalent
  refine ⟨0, EquationInstanceAt.forward (equation := quoteDropEquation)
    (initialBindings := [("N", name)]) (finalBindings := [("N", name)])
    quoteDropEquation_mem ?_ (PremisesAt.nil _) ?_⟩
  · rw [matchPattern_iff_matchRel]
    exact MatchRel.apply
      (MatchArgsRel.cons
        (MatchRel.apply (MatchArgsRel.cons MatchRel.fvar MatchArgsRel.nil rfl) rfl)
        MatchArgsRel.nil rfl)
      rfl
  · simp [quoteDropEquation, applyBindings]

/-- Quote normalization is an equation: either the quote of a drop collapses
to the name, or nothing changes. -/
theorem coreEquiv_normalizeQuote (argument : Pattern) :
    CoreEquiv base (.apply "NQuote" [argument]) (normalizeQuote argument) := by
  unfold normalizeQuote
  split
  · exact coreEquiv_quoteDrop _
  · exact Relation.EqvGen.refl _

end Laws

/-! ## Bag normalization is a chain of derived laws -/

section Bags

variable {base : BasePremiseEvaluator}

/-- Membership form of pointwise process typing. -/
theorem procTyped_of_mem {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound elements TypeExpr.proc)
    {element : Pattern} (membership : element ∈ elements) :
    HasType rhoCalc free bound element TypeExpr.proc :=
  (elementsHaveType_iff_forall_mem.mp typed) element membership

theorem procTyped_of_forall_mem {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : ∀ element ∈ elements, HasType rhoCalc free bound element TypeExpr.proc) :
    ElementsHaveType rhoCalc free bound elements TypeExpr.proc :=
  elementsHaveType_iff_forall_mem.mpr typed

/-- Elements other than a closed parallel bag splice to themselves. -/
theorem bagSplice_eq_singleton {element : Pattern}
    (notBag : ∀ inner, element ≠ .collection .hashBag inner none) :
    bagSplice element = [element] := by
  cases element with
  | collection collectionType elements rest =>
      cases collectionType with
      | hashBag =>
          cases rest with
          | none => exact absurd rfl (notBag elements)
          | some restName => rfl
      | vec => rfl
      | hashSet => rfl
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments => rfl
  | lambda binder body => rfl
  | multiLambda arity binders body => rfl
  | subst body replacement => rfl

/-- Splicing every nested parallel bag into the enclosing bag is a chain of
flattening laws. -/
theorem coreEquiv_flatMapSplice {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ (pre elements : List Pattern),
      ElementsHaveType rhoCalc free bound (pre ++ elements) TypeExpr.proc →
      CoreEquiv base (.collection .hashBag (pre ++ elements) none)
        (.collection .hashBag (pre ++ elements.flatMap bagSplice) none)
  | pre, [], _ => by
      simp only [List.flatMap_nil, List.append_nil]
      exact Relation.EqvGen.refl _
  | pre, element :: elements, typed => by
      by_cases isBag : ∃ inner, element = .collection .hashBag inner none
      · obtain ⟨inner, rfl⟩ := isBag
        have innerElements : ElementsHaveType rhoCalc free bound inner TypeExpr.proc :=
          rhoParallel_elementsHaveType (procTyped_of_mem typed (by simp))
        have flattened := coreEquiv_flatten (base := base) typed
        have spliced : ElementsHaveType rhoCalc free bound
            ((pre ++ inner) ++ elements) TypeExpr.proc := by
          apply procTyped_of_forall_mem
          intro x membership
          simp only [List.mem_append] at membership
          rcases membership with (h | h) | h
          · exact procTyped_of_mem typed (by simp [h])
          · exact procTyped_of_mem innerElements h
          · exact procTyped_of_mem typed (by simp [h])
        have tail := coreEquiv_flatMapSplice (pre ++ inner) elements spliced
        simp only [List.flatMap_cons, bagSplice, List.append_assoc] at tail flattened ⊢
        exact Relation.EqvGen.trans _ _ _ flattened tail
      · have notBag : ∀ inner, element ≠ .collection .hashBag inner none :=
          fun inner equal => isBag ⟨inner, equal⟩
        have tail := coreEquiv_flatMapSplice (pre ++ [element]) elements
          (by simpa [List.append_assoc] using typed)
        rw [List.flatMap_cons, bagSplice_eq_singleton notBag]
        simp only [List.append_assoc, List.singleton_append] at tail
        exact tail

/-- Removing every unit element is a chain of unit-absorption laws. -/
theorem coreEquiv_filterZero {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ (pre elements : List Pattern),
      ElementsHaveType rhoCalc free bound (pre ++ elements) TypeExpr.proc →
      CoreEquiv base (.collection .hashBag (pre ++ elements) none)
        (.collection .hashBag
          (pre ++ elements.filter (fun pattern => pattern ≠ .apply "PZero" [])) none)
  | pre, [], _ => by
      simp only [List.filter_nil, List.append_nil]
      exact Relation.EqvGen.refl _
  | pre, element :: elements, typed => by
      by_cases isZero : element = .apply "PZero" []
      · subst isZero
        have absorbed := coreEquiv_unitElim (base := base) typed
        have restTyped : ElementsHaveType rhoCalc free bound (pre ++ elements)
            TypeExpr.proc := by
          apply procTyped_of_forall_mem
          intro x membership
          apply procTyped_of_mem typed
          simp only [List.mem_append, List.mem_cons] at membership ⊢
          rcases membership with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        have tail := coreEquiv_filterZero pre elements restTyped
        simp only [List.filter_cons, ne_eq, not_true_eq_false,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        exact Relation.EqvGen.trans _ _ _ absorbed tail
      · have tail := coreEquiv_filterZero (pre ++ [element]) elements
          (by simpa [List.append_assoc] using typed)
        have keep : (element :: elements).filter
            (fun pattern => pattern ≠ .apply "PZero" []) =
              element :: elements.filter (fun pattern => pattern ≠ .apply "PZero" []) := by
          simp [isZero]
        rw [keep]
        simp only [List.append_assoc, List.singleton_append] at tail
        exact tail

/-- The complete parallel normalization of a bag of sorted processes is a
chain of derived laws. -/
theorem coreEquiv_normalizeBagElements {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound elements TypeExpr.proc) :
    CoreEquiv base (.collection .hashBag elements none)
      (.collection .hashBag (normalizeBagElements elements) none) := by
  have spliced := coreEquiv_flatMapSplice (base := base) [] elements (by simpa using typed)
  have splicedTyped : ElementsHaveType rhoCalc free bound
      (elements.flatMap bagSplice) TypeExpr.proc :=
    flatMap_bagSplice_elementsHaveType typed
  have filtered := coreEquiv_filterZero (base := base) [] (elements.flatMap bagSplice)
    (by simpa using splicedTyped)
  have sorted : CoreEquiv base
      (.collection .hashBag (bagContents elements) none)
      (.collection .hashBag (normalizeBagElements elements) none) := by
    have contentsTyped : ElementsHaveType rhoCalc free bound
        (bagContents elements) TypeExpr.proc := by
      unfold bagContents
      apply procTyped_of_forall_mem
      intro element membership
      apply procTyped_of_mem splicedTyped
      simp only [List.mem_filter] at membership
      exact membership.1
    rw [normalizeBagElements_eq_sort_bagContents]
    exact coreEquiv_bagPerm contentsTyped
      (sortPatterns_perm (bagContents elements))
  simp only [List.nil_append] at spliced filtered
  exact Relation.EqvGen.trans _ _ _ spliced (Relation.EqvGen.trans _ _ _ filtered sorted)

/-- Collapsing the empty or singleton wrapper is a derived law. -/
theorem coreEquiv_collapseBag {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern}
    (typed : ElementsHaveType rhoCalc free bound elements TypeExpr.proc) :
    CoreEquiv base (.collection .hashBag elements none) (collapseBag elements) := by
  match elements, typed with
  | [], _ => exact coreEquiv_empty
  | [element], typed => exact coreEquiv_singleton typed
  | first :: second :: rest, _ =>
      simp only [collapseBag]
      exact Relation.EqvGen.refl _

end Bags

/-! ## Every closed process is equivalent to its canonical form -/

section Canonical

variable {base : BasePremiseEvaluator}

mutual
  /-- Canonicalization of a sorted name is a chain of core equations. -/
  theorem coreEquiv_canonicalize_name
      {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
      (typed : HasSort rhoCalc free bound name "Name")
      (object : isObjectPattern name = true) :
      CoreEquiv base name (canonicalize name) := by
    change HasType rhoCalc free bound name TypeExpr.name at typed
    generalize resultTypeEquality : TypeExpr.name = resultType at typed
    cases typed with
    | @bvar bound index type lookup =>
        exact Relation.EqvGen.refl _
    | @fvar bound name type lookup =>
        exact Relation.EqvGen.refl _
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · cases argumentsTyped with
          | @cons _ argument arguments parameter parameters expected
              representation parameterType argumentTyped argumentsTyped =>
              cases argumentsTyped
              have expectedEquality : expected = TypeExpr.proc := by
                simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType] using
                  parameterType.symm
              subst expected
              simp [isObjectPattern, isObjectPatternList] at object
              have inner := coreEquiv_canonicalize_proc
                argumentTyped object
              have congruence : CoreEquiv base (.apply "NQuote" [argument])
                  (.apply "NQuote" [canonicalize argument]) :=
                equationEquiv_apply_of_forall₂ "NQuote" (.cons inner .nil)
              change CoreEquiv base (.apply "NQuote" [argument])
                (normalizeQuote (canonicalize argument))
              exact Relation.EqvGen.trans _ _ _ congruence
                (coreEquiv_normalizeQuote _)
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · simp at parameterShape
        · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.name, TypeExpr.baseType] at resultTypeEquality
        · simp at parameterShape
        · simp at parameterShape

  /-- Canonicalization of a sorted process is a chain of core equations. -/
  theorem coreEquiv_canonicalize_proc
      {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
      (typed : HasSort rhoCalc free bound process "Proc")
      (object : isObjectPattern process = true) :
      CoreEquiv base process (canonicalize process) := by
    change HasType rhoCalc free bound process TypeExpr.proc at typed
    generalize resultTypeEquality : TypeExpr.proc = resultType at typed
    cases typed with
    | @bvar bound index type lookup =>
        exact Relation.EqvGen.refl _
    | @fvar bound name type lookup =>
        exact Relation.EqvGen.refl _
    | @constructor bound rule arguments membership notBare argumentsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · cases argumentsTyped
          exact Relation.EqvGen.refl _
        · cases argumentsTyped with
          | @cons _ argument arguments parameter parameters expected
              representation parameterType argumentTyped argumentsTyped =>
              cases argumentsTyped
              have expectedEquality : expected = TypeExpr.name := by
                simpa [parameterType?, TypeExpr.name, TypeExpr.baseType] using
                  parameterType.symm
              subst expected
              simp [isObjectPattern, isObjectPatternList] at object
              have inner := coreEquiv_canonicalize_name
                argumentTyped object
              have congruence : CoreEquiv base (.apply "PDrop" [argument])
                  (.apply "PDrop" [canonicalize argument]) :=
                equationEquiv_apply_of_forall₂ "PDrop" (.cons inner .nil)
              exact congruence
        · simp [TypeExpr.proc, TypeExpr.baseType] at resultTypeEquality
        · simp [UsesBareCollection, TypeExpr.bag, TypeExpr.proc,
            TypeExpr.baseType] at notBare
        · cases argumentsTyped with
          | @cons _ channel arguments parameter parameters channelType
              channelRepresentation channelParameterType channelTyped
              argumentsTyped =>
              cases argumentsTyped with
              | @cons _ payload arguments parameter parameters payloadType
                  payloadRepresentation payloadParameterType payloadTyped
                  argumentsTyped =>
                  cases argumentsTyped
                  have channelTypeEquality : channelType = TypeExpr.name := by
                    simpa [parameterType?, TypeExpr.name, TypeExpr.baseType]
                      using channelParameterType.symm
                  have payloadTypeEquality : payloadType = TypeExpr.proc := by
                    simpa [parameterType?, TypeExpr.proc, TypeExpr.baseType]
                      using payloadParameterType.symm
                  subst channelType
                  subst payloadType
                  simp [isObjectPattern, isObjectPatternList] at object
                  have channelEquiv := coreEquiv_canonicalize_name
                    channelTyped object.1
                  have payloadEquiv := coreEquiv_canonicalize_proc
                    payloadTyped object.2
                  have congruence : CoreEquiv base (.apply "POutput" [channel, payload])
                      (.apply "POutput" [canonicalize channel, canonicalize payload]) :=
                    equationEquiv_apply_of_forall₂ "POutput"
                      (.cons channelEquiv (.cons payloadEquiv .nil))
                  exact congruence
        · cases argumentsTyped with
          | @cons _ channel arguments parameter parameters channelType
              channelRepresentation channelParameterType channelTyped
              argumentsTyped =>
              cases argumentsTyped with
              | @cons _ abstraction arguments parameter parameters bodyType
                  bodyRepresentation bodyParameterType abstractionTyped
                  argumentsTyped =>
                  cases argumentsTyped
                  have channelTypeEquality : channelType = TypeExpr.name := by
                    simpa [parameterType?, TypeExpr.name, TypeExpr.baseType]
                      using channelParameterType.symm
                  have bodyTypeEquality : bodyType =
                      TypeExpr.arrow TypeExpr.name TypeExpr.proc := by
                    simpa [parameterType?, TypeExpr.name, TypeExpr.proc,
                      TypeExpr.funType, TypeExpr.baseType] using
                        bodyParameterType.symm
                  subst channelType
                  subst bodyType
                  cases abstraction with
                  | lambda binder body =>
                      cases binder with
                      | none =>
                          cases abstractionTyped with
                          | lambda bodyTyped =>
                              simp [isObjectPattern, isObjectPatternList] at object
                              have channelEquiv := coreEquiv_canonicalize_name
                                channelTyped object.1
                              have bodyEquiv := coreEquiv_canonicalize_proc
                                bodyTyped object.2
                              have abstractionEquiv :
                                  CoreEquiv base (.lambda none body)
                                    (.lambda none (canonicalize body)) := by
                                have filled :=
                                  equationEquiv_fill (.lambda none .hole) bodyEquiv
                                simp only [OneHoleContext.fill] at filled
                                exact filled
                              have congruence : CoreEquiv base
                                  (.apply "PInput" [channel, .lambda none body])
                                  (.apply "PInput"
                                    [canonicalize channel,
                                      .lambda none (canonicalize body)]) :=
                                equationEquiv_apply_of_forall₂ "PInput"
                                  (.cons channelEquiv (.cons abstractionEquiv .nil))
                              exact congruence
                      | some binderName =>
                          simp [MatchesParameterRepresentation] at bodyRepresentation
                  | bvar index =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | fvar name =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | apply name arguments =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | multiLambda arity binders body =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | subst body replacement =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
                  | collection collectionType elements rest =>
                      simp [MatchesParameterRepresentation] at bodyRepresentation
    | lambda bodyTyped => cases resultTypeEquality
    | multiLambda bodyTyped => cases resultTypeEquality
    | subst bodyTyped replacementTyped => simp [isObjectPattern] at object
    | collection elementsTyped => cases resultTypeEquality
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped =>
        simp [rhoCalc] at membership
        rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
        · simp at parameterShape
        · simp [TypeExpr.name, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.proc, TypeExpr.baseType] at parameterShape
        · simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at parameterShape
          rcases parameterShape with ⟨rfl, rfl, rfl⟩
          cases rest with
          | none =>
              simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
                at object
              have pointwise := coreEquiv_canonicalizeList_procElements
                elementsTyped object
              have congruence : CoreEquiv base
                  (.collection .hashBag elements none)
                  (.collection .hashBag (canonicalizeList elements) none) :=
                equationEquiv_collection_of_forall₂ .hashBag none pointwise
              have canonicalTyped :=
                canonicalize_procElementsHaveType elementsTyped object
              have normalized := coreEquiv_normalizeBagElements (base := base)
                canonicalTyped
              have collapsed := coreEquiv_collapseBag (base := base)
                (normalizeBagElements_elementsHaveType canonicalTyped)
              change CoreEquiv base (.collection .hashBag elements none)
                (collapseBag (normalizeBagElements (canonicalizeList elements)))
              exact Relation.EqvGen.trans _ _ _ congruence
                (Relation.EqvGen.trans _ _ _ normalized collapsed)
          | some restName => simp [isObjectPattern] at object
        · simp at parameterShape
        · simp at parameterShape

  /-- Pointwise form for the elements of a parallel bag. -/
  theorem coreEquiv_canonicalizeList_procElements
      {free : FreeTypeContext} {bound : List TypeExpr} {processes : List Pattern}
      (typed : ElementsHaveType rhoCalc free bound processes TypeExpr.proc)
      (object : isObjectPatternList processes = true) :
      List.Forall₂ (CoreEquiv base) processes (canonicalizeList processes) := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        exact .cons (coreEquiv_canonicalize_proc processTyped object.1)
          (coreEquiv_canonicalizeList_procElements processesTyped
            object.2)
end

end Canonical

/-! ## Generic equals bespoke on closed processes -/

/-- The sort and object-pattern data of a closed process. -/
theorem closedProcess_typed {process : Pattern}
    (closed : RhoClosedTermWellSorted rhoProc process) :
    HasSort rhoCalc FreeTypeContext.empty [] process "Proc" ∧
      isObjectPattern process = true := by
  have generic := (closed_process_wellSorted_iff process).mpr closed
  obtain ⟨⟨typed, _, _, object, _⟩, _⟩ := generic
  exact ⟨typed, object⟩

/-- Every closed process is core-equivalent to its canonical form. -/
theorem coreEquiv_canonicalize_of_closed {base : BasePremiseEvaluator}
    {process : Pattern} (closed : RhoClosedTermWellSorted rhoProc process) :
    CoreEquiv base process (canonicalize process) := by
  obtain ⟨typed, object⟩ := closedProcess_typed closed
  exact coreEquiv_canonicalize_proc typed object

/-- Core generators preserve the canonical form (soundness direction). -/
theorem canonicalize_eq_of_coreEquiv {left right : Pattern}
    (equivalent : CoreEquiv defaultBasePremises left right) :
    canonicalize left = canonicalize right := by
  induction equivalent with
  | rel left right step =>
      exact rhoEquationContextStep_canonicalize_eq
        (ReflectiveEquationContextStep.core step)
  | refl pattern => rfl
  | symm left right relation inductionHypothesis => exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH => exact firstIH.trans secondIH

/-- On closed processes the core generated theory is canonical equality. -/
theorem coreEquiv_iff_canonicalize_eq {left right : Pattern}
    (leftClosed : RhoClosedTermWellSorted rhoProc left)
    (rightClosed : RhoClosedTermWellSorted rhoProc right) :
    CoreEquiv defaultBasePremises left right ↔
      canonicalize left = canonicalize right := by
  constructor
  · exact canonicalize_eq_of_coreEquiv
  · intro representatives
    have leftEquiv := coreEquiv_canonicalize_of_closed (base := defaultBasePremises)
      leftClosed
    have rightEquiv := coreEquiv_canonicalize_of_closed (base := defaultBasePremises)
      rightClosed
    rw [representatives] at leftEquiv
    exact Relation.EqvGen.trans _ _ _ leftEquiv (Relation.EqvGen.symm _ _ rightEquiv)

/-- Generic equals bespoke, equations: on closed processes the core generated
theory is exactly the established structural congruence. -/
theorem coreEquiv_iff_structuralCongruence {left right : Pattern}
    (leftClosed : RhoClosedTermWellSorted rhoProc left)
    (rightClosed : RhoClosedTermWellSorted rhoProc right) :
    CoreEquiv defaultBasePremises left right ↔ StructuralCongruence left right := by
  rw [coreEquiv_iff_canonicalize_eq leftClosed rightClosed]
  have leftTyped := ((rhoClosedTermWellSorted_process_iff left).mp leftClosed).1
  have rightTyped := ((rhoClosedTermWellSorted_process_iff right).mp rightClosed).1
  exact (structuralCongruence_iff_canonicalize_eq
    (PureBoundary.rhoProcWellSorted_hashSetFree leftTyped)
    (PureBoundary.rhoProcWellSorted_hashSetFree rightTyped)).symm

/-- The equation setoid of the language-generated rho GSLT agrees with the
bespoke canonical setoid on the closed process fiber. -/
theorem langGSLT_rhoCalc_equiv_iff (left right : RhoProcess) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT rhoCalc).Equiv left.1 right.1 ↔
      rhoProcessEquations.r left right := by
  change CoreEquiv defaultBasePremises left.1 right.1 ↔
    canonicalize left.1 = canonicalize right.1
  exact coreEquiv_iff_canonicalize_eq left.2 right.2

/-- Reflective generators preserve the canonical form. -/
theorem canonicalize_eq_of_reflectiveEquiv {left right : Pattern}
    (equivalent : ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises
      rhoCalc left right) :
    canonicalize left = canonicalize right := by
  induction equivalent with
  | rel left right step => exact rhoEquationContextStep_canonicalize_eq step
  | refl pattern => rfl
  | symm left right relation inductionHypothesis => exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH => exact firstIH.trans secondIH

/-- The core theory embeds into the reflective theory. -/
theorem reflectiveEquiv_of_coreEquiv {left right : Pattern}
    (equivalent : CoreEquiv defaultBasePremises left right) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc left right := by
  induction equivalent with
  | rel left right step =>
      exact Relation.EqvGen.rel _ _ (ReflectiveEquationContextStep.core step)
  | refl pattern => exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- The reflective canonical-equality generator is conservative over the core
theory on closed processes: it identifies nothing the presentation-derived
laws do not already identify. -/
theorem reflectiveEquiv_iff_coreEquiv {left right : Pattern}
    (leftClosed : RhoClosedTermWellSorted rhoProc left)
    (rightClosed : RhoClosedTermWellSorted rhoProc right) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc left right ↔
      CoreEquiv defaultBasePremises left right :=
  ⟨fun equivalent => (coreEquiv_iff_canonicalize_eq leftClosed rightClosed).mpr
      (canonicalize_eq_of_reflectiveEquiv equivalent),
    reflectiveEquiv_of_coreEquiv⟩


end Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
