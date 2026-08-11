import Mathlib.CategoryTheory.Presentable.Finite
import Mettapedia.GSLT.Core.UltrainfiniteTransport
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Indexed operational GSLTs

This module supplies the finite operational core needed before an internal
language for growing GSLT diagrams can be executable.  It keeps three facts
separate:

* equations must be respected by a term translation;
* source steps must map to target steps;
* every step leaving a translated state must have a source lift when the map
  is used as an exact behavioral transport.

The first two obligations form `OperationalTranslation`; the third upgrades
one to `CoveredTranslation` using the existing `Ultrainfinite.StepCover`.
This distinction matters for growing theories: an extension may preserve all
old reductions while adding new behavior, whereas an exact realization or
conservative operational embedding must also cover target steps at image
states.

An indexed diagram is a functor into this covered operational category.  Its
terms are equation classes in individual fibres.  The small command language
has only returned fibre states and explicit `via` requests.  A `via` request
may either reduce in its source fibre or cross the selected map.  The two
orders form a carried naturality square, so transport is visible control state
rather than an implicit scheduler action.
-/

namespace Mettapedia.GSLT.IndexedOperational

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uTerm uSourceTerm uMiddleTerm uTargetTerm
  uIndex vIndex uObservation uCell

/-! ## Forward and covered operational translations -/

/-- A term translation that respects equations and preserves one-step
reduction.  It may expose additional target behavior at translated states. -/
structure OperationalTranslation
    (source : GSLT.{uSourceTerm}) (target : GSLT.{uTargetTerm}) where
  mapTerm : source.Term → target.Term
  mapEquiv : ∀ {left right}, source.Equiv left right →
    target.Equiv (mapTerm left) (mapTerm right)
  mapStep : ∀ {sourceTerm targetTerm}, source.Step sourceTerm targetTerm →
    target.Step (mapTerm sourceTerm) (mapTerm targetTerm)

namespace OperationalTranslation

@[ext]
theorem ext {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    {first second : OperationalTranslation source target}
    (mapTerm : first.mapTerm = second.mapTerm) : first = second := by
  cases first
  cases second
  cases mapTerm
  rfl

/-- Identity preserves equations and steps. -/
def id (theory : GSLT.{uTerm}) : OperationalTranslation theory theory where
  mapTerm := _root_.id
  mapEquiv := fun equivalent => equivalent
  mapStep := fun step => step

/-- Forward operational translations compose in execution order. -/
def comp {first : GSLT.{uSourceTerm}} {middle : GSLT.{uMiddleTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last) :
    OperationalTranslation first last where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  mapStep := fun step => later.mapStep (earlier.mapStep step)

end OperationalTranslation

/-- A term translation that respects equations and has exact local coverage
of one-step behavior at translated states. -/
structure CoveredTranslation (source target : GSLT.{uTerm}) where
  mapTerm : source.Term → target.Term
  mapEquiv : ∀ {left right}, source.Equiv left right →
    target.Equiv (mapTerm left) (mapTerm right)
  cover : StepCover source target mapTerm

namespace CoveredTranslation

@[ext]
theorem ext {source target : GSLT.{uTerm}}
    {first second : CoveredTranslation source target}
    (mapTerm : first.mapTerm = second.mapTerm) : first = second := by
  cases first
  cases second
  cases mapTerm
  rfl

/-- Identity transport preserves equations and covers steps exactly. -/
def id (theory : GSLT.{uTerm}) : CoveredTranslation theory theory where
  mapTerm := _root_.id
  mapEquiv := fun equivalent => equivalent
  cover := StepCover.id theory

/-- Covered operational transports compose in execution order. -/
def comp {first middle last : GSLT.{uTerm}}
    (earlier : CoveredTranslation first middle)
    (later : CoveredTranslation middle last) :
    CoveredTranslation first last where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  cover := earlier.cover.comp later.cover

/-- Forgetting equation preservation yields the established behavioral GSLT
morphism, using local coverage rather than assuming preservation by fiat. -/
def toBehavioralMorphism {source target : GSLT.{uTerm}}
    (translation : CoveredTranslation source target) : source ⟶ target :=
  translation.cover.toMorphism

/-- Forget local reflection while retaining equation and step preservation. -/
def toOperational {source target : GSLT.{uTerm}}
    (translation : CoveredTranslation source target) :
    OperationalTranslation source target where
  mapTerm := translation.mapTerm
  mapEquiv := translation.mapEquiv
  mapStep := translation.cover.mapStep

end CoveredTranslation

/-- Objects of the forward operational category. -/
structure OperationalTheory where
  theory : GSLT.{uTerm}

instance : CategoryTheory.Category OperationalTheory where
  Hom source target := OperationalTranslation source.theory target.theory
  id source := OperationalTranslation.id source.theory
  comp earlier later := earlier.comp later
  id_comp morphism := by
    apply OperationalTranslation.ext
    rfl
  comp_id morphism := by
    apply OperationalTranslation.ext
    rfl
  assoc first second third := by
    apply OperationalTranslation.ext
    rfl

/-- Objects of the covered operational category.  The wrapper permits a
second, stronger morphism notion without replacing the established behavioral
category on `GSLT`. -/
structure CoveredTheory where
  theory : GSLT.{uTerm}

instance : CategoryTheory.Category CoveredTheory where
  Hom source target := CoveredTranslation source.theory target.theory
  id source := CoveredTranslation.id source.theory
  comp earlier later := earlier.comp later
  id_comp morphism := by
    apply CoveredTranslation.ext
    rfl
  comp_id morphism := by
    apply CoveredTranslation.ext
    rfl
  assoc first second third := by
    apply CoveredTranslation.ext
    rfl

/-- The covered operational category forgets coherently to the behavioral
category. -/
def forget : CategoryTheory.Functor CoveredTheory.{uTerm} GSLT.{uTerm} where
  obj object := object.theory
  map translation := translation.toBehavioralMorphism
  map_id object := by
    apply GSLT.Morphism.ext
    rfl
  map_comp earlier later := by
    apply GSLT.Morphism.ext
    rfl

/-- Exact covered transports form a wide subcategory of forward operational
transports. -/
def forgetCoverage :
    CategoryTheory.Functor CoveredTheory.{uTerm} OperationalTheory.{uTerm} where
  obj object := ⟨object.theory⟩
  map translation := translation.toOperational
  map_id object := by
    apply OperationalTranslation.ext
    rfl
  map_comp earlier later := by
    apply OperationalTranslation.ext
    rfl

/-! ## Equation classes and induced steps -/

/-- A semantic fibre term is an authored term modulo the fibre's equations. -/
abbrev SemanticTerm (theory : GSLT.{uTerm}) := Quotient theory.equations

/-- A fibre step on equation classes is witnessed by one pair of authored
representatives.  The GSLT response laws make this independent of the chosen
representatives. -/
def SemanticStep (theory : GSLT.{uTerm})
    (source target : SemanticTerm theory) : Prop :=
  ∃ redex contractum : theory.Term,
    Quotient.mk theory.equations redex = source ∧
      theory.Step redex contractum ∧
      Quotient.mk theory.equations contractum = target

/-- Every authored step gives a semantic step between its equation classes. -/
theorem semanticStep_mk {theory : GSLT.{uTerm}}
    {source target : theory.Term} (step : theory.Step source target) :
    SemanticStep theory (Quotient.mk theory.equations source)
      (Quotient.mk theory.equations target) :=
  ⟨source, target, rfl, step, rfl⟩

/-- Passing to equation classes neither invents nor removes a one-step
reduction between two chosen authored representatives. -/
theorem semanticStep_mk_iff_step (theory : GSLT.{uTerm})
    (source target : theory.Term) :
    SemanticStep theory (Quotient.mk theory.equations source)
        (Quotient.mk theory.equations target) ↔
      theory.Step source target := by
  constructor
  · rintro ⟨redex, contractum, sourceClass, reduction, targetClass⟩
    have redexEquivalent : theory.Equiv redex source :=
      Quotient.exact sourceClass
    have contractumEquivalent : theory.Equiv contractum target :=
      Quotient.exact targetClass
    obtain ⟨sourceContractum, sourceReduction, resultEquivalent⟩ :=
      theory.rewrites_resp_left redexEquivalent reduction
    apply theory.rewrites_resp_right sourceReduction
    exact theory.equations.iseqv.trans
      (theory.equations.iseqv.symm resultEquivalent)
      contractumEquivalent
  · exact semanticStep_mk

/-- Equation-respecting forward transport acts on semantic fibre terms. -/
def OperationalTranslation.mapSemantic
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    SemanticTerm source → SemanticTerm target :=
  Quotient.map translation.mapTerm fun _ _ equivalent =>
    translation.mapEquiv equivalent

/-- Forward operational transport maps semantic one-step reductions. -/
theorem OperationalTranslation.mapSemanticStep
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    {left right : SemanticTerm source}
    (step : SemanticStep source left right) :
    SemanticStep target (translation.mapSemantic left)
      (translation.mapSemantic right) := by
  obtain ⟨redex, contractum, rfl, reduction, rfl⟩ := step
  exact ⟨translation.mapTerm redex, translation.mapTerm contractum,
    rfl, translation.mapStep reduction, rfl⟩

@[simp]
theorem OperationalTranslation.mapSemantic_id (theory : GSLT.{uTerm})
    (term : SemanticTerm theory) :
    (OperationalTranslation.id theory).mapSemantic term = term := by
  refine Quotient.inductionOn term ?_
  intro representative
  rfl

@[simp]
theorem OperationalTranslation.mapSemantic_comp
    {first middle last : GSLT.{uTerm}}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (term : SemanticTerm first) :
    (earlier.comp later).mapSemantic term =
      later.mapSemantic (earlier.mapSemantic term) := by
  refine Quotient.inductionOn term ?_
  intro representative
  rfl

/-- The quotient of one GSLT by its equations is itself a GSLT with equality
as its remaining equation theory. -/
def semanticTheory (theory : GSLT.{uTerm}) : GSLT.{uTerm} where
  Term := SemanticTerm theory
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SemanticStep theory
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-! ## The explicit finite indexed command core -/

/-- A finite indexed GSLT diagram with equation- and step-preserving maps.
Exact local coverage is intentionally a stronger, separately named profile. -/
abbrev Diagram (Index : Type uIndex)
    [CategoryTheory.Category.{vIndex} Index] :=
  CategoryTheory.Functor Index OperationalTheory.{uTerm}

/-- A diagram whose every stage map additionally covers all target steps at
translated states. -/
abbrev CoveredDiagram (Index : Type uIndex)
    [CategoryTheory.Category.{vIndex} Index] :=
  CategoryTheory.Functor Index CoveredTheory.{uTerm}

/-- Forget exact local coverage from an indexed diagram. -/
def CoveredDiagram.toOperational
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : CoveredDiagram.{uTerm, uIndex, vIndex} Index) :
    Diagram.{uTerm, uIndex, vIndex} Index :=
  CategoryTheory.Functor.comp diagram forgetCoverage

/-- Apply one selected diagram map to a semantic fibre term. -/
def transportTerm {Index : Type uIndex}
    [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    {source target : Index} (route : source ⟶ target) :
    SemanticTerm (diagram.obj source).theory →
      SemanticTerm (diagram.obj target).theory :=
  (diagram.map route).mapSemantic

@[simp]
theorem transportTerm_id
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    (stage : Index) (term : SemanticTerm (diagram.obj stage).theory) :
    transportTerm diagram (CategoryTheory.CategoryStruct.id stage) term = term := by
  change (diagram.map (CategoryTheory.CategoryStruct.id stage)).mapSemantic term = term
  rw [diagram.map_id]
  exact OperationalTranslation.mapSemantic_id _ term

@[simp]
theorem transportTerm_comp
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    {first second third : Index}
    (earlier : first ⟶ second) (later : second ⟶ third)
    (term : SemanticTerm (diagram.obj first).theory) :
    transportTerm diagram (CategoryTheory.CategoryStruct.comp earlier later) term =
      transportTerm diagram later (transportTerm diagram earlier term) := by
  change (diagram.map (CategoryTheory.CategoryStruct.comp earlier later)).mapSemantic term =
    (diagram.map later).mapSemantic ((diagram.map earlier).mapSemantic term)
  rw [diagram.map_comp]
  exact OperationalTranslation.mapSemantic_comp _ _ term

/-- The initial GSLT-IL command waist: a returned fibre state or an explicit
request to transport one state along one authored diagram map. -/
inductive Command
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index) where
  | at (stage : Index) (state : SemanticTerm (diagram.obj stage).theory)
  | via {source target : Index} (route : source ⟶ target)
      (state : SemanticTerm (diagram.obj source).theory)

namespace Command

variable {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)

/-- One proof-relevant command edge either computes inside a returned fibre,
computes under an explicit transport request, or performs the selected
transport. -/
inductive Step : Command diagram → Command diagram → Type _ where
  | fibre {stage : Index}
      {source target : SemanticTerm (diagram.obj stage).theory} :
      SemanticStep (diagram.obj stage).theory source target →
      Step (.at stage source) (.at stage target)
  | underVia {first second : Index} (route : first ⟶ second)
      {source target : SemanticTerm (diagram.obj first).theory} :
      SemanticStep (diagram.obj first).theory source target →
      Step (.via route source) (.via route target)
  | applyVia {source target : Index} (route : source ⟶ target)
      (state : SemanticTerm (diagram.obj source).theory) :
      Step (.via route state) (.at target (transportTerm diagram route state))

/-- The explicit command machine is one GSLT.  Fibre equations were already
quotiented before commands were formed, so command equality is exact. -/
def commandGSLT : GSLT.{max uTerm uIndex vIndex} where
  Term := Command diagram
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => Nonempty (Step diagram source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Naturality maps every source-fibre step to a target-fibre step. -/
theorem transported_fibre_step
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    SemanticStep (diagram.obj target).theory
      (transportTerm diagram route left)
      (transportTerm diagram route right) :=
  (diagram.map route).mapSemanticStep step

/-- Reduce before crossing a stage map. -/
def reduceBeforeRoute
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    Route (Step diagram) (.via route left)
      (.at target (transportTerm diagram route right)) :=
  .cons (.underVia route step) (.cons (.applyVia route right) (.refl _))

/-- Cross a stage map before reducing the transported state. -/
def transportBeforeRoute
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    Route (Step diagram) (.via route left)
      (.at target (transportTerm diagram route right)) :=
  .cons (.applyVia route left)
    (.cons (.fibre (transported_fibre_step diagram route step)) (.refl _))

/-- The generating 2-cell says that fibre computation and covered transport
form the naturality square generated by the exact source step. -/
inductive TransportCell :
    {source target : Command diagram} →
      Route (Step diagram) source target →
      Route (Step diagram) source target → Type _ where
  | naturality {first second : Index} (route : first ⟶ second)
      {left right : SemanticTerm (diagram.obj first).theory}
      (step : SemanticStep (diagram.obj first).theory left right) :
      TransportCell (reduceBeforeRoute diagram route step)
        (transportBeforeRoute diagram route step)

/-- The naturality square as a chosen filled diamond, retaining both
execution orders and the source step that licenses the filler. -/
def naturalityDiamond
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    FilledDiamond (Step diagram) (TransportCell diagram)
      (.via route left) (.via route right)
      (.at target (transportTerm diagram route left)) where
  leftBranch := .cons (.underVia route step) (.refl _)
  rightBranch := .cons (.applyVia route left) (.refl _)
  join := .at target (transportTerm diagram route right)
  closeLeft := .cons (.applyVia route right) (.refl _)
  closeRight := .cons
    (.fibre (transported_fibre_step diagram route step)) (.refl _)
  filler := .naturality route step

/-! ## Named observations -/

/-- A named observation that is invariant under changing finite theory stage.
No claim is made yet that it is invariant under execution. -/
structure TransportObserver where
  Result : Type uObservation
  observe : ∀ stage : Index,
    SemanticTerm (diagram.obj stage).theory → Result
  natural : ∀ {source target : Index} (route : source ⟶ target) state,
    observe target (transportTerm diagram route state) = observe source state

namespace TransportObserver

variable (observer : TransportObserver diagram)

/-- Observe an outstanding `via` request at its source boundary. -/
def observeCommand : Command diagram → observer.Result
  | .at stage state => observer.observe stage state
  | .via (source := source) _ state => observer.observe source state

/-- A separate property says that the observer is invariant under actual
fibre computation. -/
def FibreInvariant : Prop :=
  ∀ (stage : Index) {source target},
    SemanticStep (diagram.obj stage).theory source target →
      observer.observe stage source = observer.observe stage target

/-- Stage naturality plus fibre invariance conserves the observation across
every command step. -/
theorem step_conserved (invariant : observer.FibreInvariant)
    {source target : Command diagram} (step : Step diagram source target) :
    observeCommand diagram observer source =
      observeCommand diagram observer target := by
  cases step with
  | fibre step => exact invariant _ step
  | underVia _ step => exact invariant _ step
  | applyVia route state => exact (observer.natural route state).symm

/-- Consequently the named observation is invariant along every carried
finite execution route. -/
theorem route_conserved (invariant : observer.FibreInvariant)
    {source target : Command diagram}
    (route : Route (Step diagram) source target) :
    observeCommand diagram observer source =
      observeCommand diagram observer target :=
  Route.observe_eq_of_route (observeCommand diagram observer)
    (step_conserved diagram observer invariant) route

end TransportObserver

/-! ## OSLF-generated native meaning -/

/-- OSLF supplies the full predicate-valued native type theory of the indexed
command GSLT without adding a second operational relation. -/
abbrev NativeType :=
  GSLTNativeType (commandGSLT.{uTerm, uIndex, vIndex} diagram)

/-- An explicit stage transport inhabits the exact OSLF target type generated
for its returned state. -/
theorem applyVia_satisfies_nativeType
    {source target : Index} (route : source ⟶ target)
    (state : SemanticTerm (diagram.obj source).theory) :
    (gsltOSLF (commandGSLT.{uTerm, uIndex, vIndex} diagram)).satisfies
      (.via route state)
      (exactTargetNativeType (commandGSLT.{uTerm, uIndex, vIndex} diagram)
        (.at target (transportTerm diagram route state))).pred := by
  apply (satisfies_exactTargetNativeType_iff_step
    (commandGSLT.{uTerm, uIndex, vIndex} diagram) _ _).2
  exact ⟨.applyVia route state⟩

/-- A fibre reduction inhabits the exact OSLF target type generated for its
returned state. -/
theorem fibre_satisfies_nativeType
    {stage : Index}
    {source target : SemanticTerm (diagram.obj stage).theory}
    (step : SemanticStep (diagram.obj stage).theory source target) :
    (gsltOSLF (commandGSLT.{uTerm, uIndex, vIndex} diagram)).satisfies
      (.at stage source)
      (exactTargetNativeType (commandGSLT.{uTerm, uIndex, vIndex} diagram)
        (.at stage target)).pred := by
  apply (satisfies_exactTargetNativeType_iff_step
    (commandGSLT.{uTerm, uIndex, vIndex} diagram) _ _).2
  exact ⟨.fibre step⟩

end Command

/-! ## Compact requests into filtered operational growth -/

/-- A filtered growth presentation in the forward operational category. -/
abbrev FilteredGrowth
    {J : Type uIndex} [CategoryTheory.SmallCategory J]
    [CategoryTheory.IsFiltered J]
    (stages : CategoryTheory.Functor J OperationalTheory.{uTerm}) :=
  Ultrainfinite.FilteredGrowth stages

/-- The stronger filtered presentation in which every stage map has exact
local step coverage. -/
abbrev CoveredFilteredGrowth
    {J : Type uIndex} [CategoryTheory.SmallCategory J]
    [CategoryTheory.IsFiltered J]
    (stages : CategoryTheory.Functor J CoveredTheory.{uTerm}) :=
  Ultrainfinite.FilteredGrowth stages

/-- Every finitely presentable request into a supplied filtered covered growth
factors through a finite stage. -/
theorem compact_request_factors
    {J : Type uIndex} [CategoryTheory.SmallCategory J]
    [CategoryTheory.IsFiltered J]
    {stages : CategoryTheory.Functor J OperationalTheory.{uTerm}}
    (growth : FilteredGrowth stages)
    {request : OperationalTheory.{uTerm}}
    [CategoryTheory.IsFinitelyPresentable.{uIndex} request]
    (run : request ⟶ growth.cocone.pt) :
    ∃ (stage : J) (through : request ⟶ stages.obj stage),
      CategoryTheory.CategoryStruct.comp through
        (growth.cocone.ι.app stage) = run :=
  growth.compact_factor run

/-- Compact factorization is also available in the stronger exact-covered
subcategory when a supplied colimit there exists. -/
theorem compact_request_factors_covered
    {J : Type uIndex} [CategoryTheory.SmallCategory J]
    [CategoryTheory.IsFiltered J]
    {stages : CategoryTheory.Functor J CoveredTheory.{uTerm}}
    (growth : CoveredFilteredGrowth stages)
    {request : CoveredTheory.{uTerm}}
    [CategoryTheory.IsFinitelyPresentable.{uIndex} request]
    (run : request ⟶ growth.cocone.pt) :
    ∃ (stage : J) (through : request ⟶ stages.obj stage),
      CategoryTheory.CategoryStruct.comp through
        (growth.cocone.ι.app stage) = run :=
  growth.compact_factor run

end Mettapedia.GSLT.IndexedOperational
