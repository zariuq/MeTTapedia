import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLSignatureDenotation
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Native HOL proof terms in Henkin dependent families

This module interprets the actual cumulative-tower variable, abstraction and
application terms in ordinary dependent type families.  Represented HOL
constants receive their meaning from an arbitrary Henkin model of the same
logical signature.  A semantic context may mix object variables with proof
variables, so one telescope supports both universal and implication binders.

The interpretation is independent of the proof compiler.  Displayed
renamings state explicitly how native variable positions and semantic
projections commute.  The Aczel trace construction is a more structured model
of the same lambda spine; the ordinary family model is needed for operational
Henkin instances whose carrier is not a chosen set code.

The conversion constructor permits semantic recoding through arbitrary
pointwise equivalences.  Consequently this relation supplies forward
realization through a specified codec, not uniqueness of an observable value
for a fixed native term and expected family.  Native checker conversion and
execution adequacy require their own, stronger comparison.  The counterexample
in `NativeHOLHenkinFamilyConversionBoundary` makes this distinction explicit.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
namespace HenkinFamilySemantics

open Presentation Mettapedia.Logic
open FormationSensitiveHOLInterface

universe u v w s

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- A dependent family and one of its sections. -/
abbrev Family (Environment : Type s) := Environment → Type s

abbrev Section {Environment : Type s} (family : Family Environment) :=
  (environment : Environment) → family environment

abbrev Extension {Environment : Type s} (family : Family Environment) :=
  Σ environment, family environment

/-- A semantic telescope for a native de Bruijn scope. -/
structure SemanticContext (n : Nat) where
  Environment : Type s
  family : Fin n → Family Environment
  projection : (index : Fin n) → Section (family index)

def SemanticContext.nil : SemanticContext.{s} 0 where
  Environment := PUnit
  family := fun index => Fin.elim0 index
  projection := fun index => Fin.elim0 index

/-- Telescope comprehension, with the newest variable at index zero. -/
def SemanticContext.snoc {n : Nat} (context : SemanticContext.{s} n)
    (family : Family context.Environment) : SemanticContext (n + 1) where
  Environment := Extension family
  family := Fin.cases (fun point => family point.1)
    (fun index point => context.family index point.1)
  projection := Fin.cases (fun point => point.2)
    (fun index point => context.projection index point.1)

@[simp] theorem SemanticContext.snoc_family_zero {n : Nat}
    (context : SemanticContext.{s} n) (family : Family context.Environment) :
    (context.snoc family).family 0 = fun point => family point.1 := rfl

@[simp] theorem SemanticContext.snoc_family_succ {n : Nat}
    (context : SemanticContext.{s} n) (family : Family context.Environment)
    (index : Fin n) :
    (context.snoc family).family index.succ =
      fun (point : Extension family) => context.family index point.1 := rfl

@[simp] theorem SemanticContext.snoc_projection_zero {n : Nat}
    (context : SemanticContext.{s} n) (family : Family context.Environment) :
    (context.snoc family).projection 0 = fun point => point.2 := rfl

@[simp] theorem SemanticContext.snoc_projection_succ {n : Nat}
    (context : SemanticContext.{s} n) (family : Family context.Environment)
    (index : Fin n) :
    (context.snoc family).projection index.succ =
      fun (point : Extension family) => context.projection index point.1 := rfl

/-- Constant object families and dependent function families. -/
def typeFamily (model : HOL.HenkinModel.{u, v, w} Base Const)
    {Environment : Type (max (u + 1) w)} (type : HOL.Ty Base) :
    Family Environment :=
  fun _ => HOL.Ty.denote model.Carrier type

def piFamily {Environment : Type s} (domain : Family Environment)
    (codomain : Family (Extension domain)) : Family Environment :=
  fun environment => (argument : domain environment) →
    codomain ⟨environment, argument⟩

/-- A proposition is represented by its lifted proof-witness family. -/
def truthFamily {Environment : Type s} (proposition : Environment → Prop) :
    Family Environment :=
  fun environment => ULift.{s, 0} (PLift (proposition environment))

def castSection {Environment : Type s} {first second : Family Environment}
    (equal : first = second) (value : Section first) : Section second :=
  equal ▸ value

/-- Pointwise equivalence transports a semantic section without changing its
native term.  This is semantic conversion, not native definitional equality. -/
def mapSection {Environment : Type s} {first second : Family Environment}
    (equivalence : (environment : Environment) →
      first environment ≃ second environment)
    (value : Section first) : Section second :=
  fun environment => equivalence environment (value environment)

/-- Typed denotation of the native lambda/application spine together with the
closed operations selected by a logical signature. -/
inductive Denotes (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const) :
    {n : Nat} → (context : SemanticContext.{max (u + 1) w} n) →
      (term : Tower.Tm n) → (family : Family context.Environment) →
        Section family → Prop where
  | var {n : Nat} (context : SemanticContext.{max (u + 1) w} n)
      (index : Fin n) :
      Denotes signature model context (.var index)
        (context.family index) (context.projection index)
  | abstraction {n : Nat}
      {context : SemanticContext.{max (u + 1) w} n}
      {domain : Family context.Environment}
      {codomain : Family (Extension domain)} {body : Tower.Tm (n + 1)}
      {bodyValue : Section codomain} :
      Denotes signature model (context.snoc domain) body codomain bodyValue →
      Denotes signature model context (.lam body) (piFamily domain codomain)
        (fun environment argument => bodyValue ⟨environment, argument⟩)
  | application {n : Nat}
      {context : SemanticContext.{max (u + 1) w} n}
      {domain : Family context.Environment}
      {codomain : Family (Extension domain)} {function argument : Tower.Tm n}
      {functionValue : Section (piFamily domain codomain)}
      {argumentValue : Section domain} :
      Denotes signature model context function (piFamily domain codomain)
          functionValue →
      Denotes signature model context argument domain argumentValue →
      Denotes signature model context (.app function argument)
        (fun environment => codomain ⟨environment, argumentValue environment⟩)
        (fun environment => functionValue environment (argumentValue environment))
  | constant {n : Nat}
      (context : SemanticContext.{max (u + 1) w} n)
      {type : HOL.Ty Base} (symbol : Const type) :
      Denotes signature model context
        (liftClosed (signature.constant symbol)) (typeFamily model type)
        (fun _ => model.constDen symbol)
  | implication {n : Nat}
      (context : SemanticContext.{max (u + 1) w} n) :
      Denotes signature model context (liftClosed signature.implication)
        (typeFamily model (.arr .prop (.arr .prop .prop)))
        (fun _ premise conclusion => ULift.up (premise.down → conclusion.down))
  | universal {n : Nat}
      (context : SemanticContext.{max (u + 1) w} n) (type : HOL.Ty Base) :
      Denotes signature model context (liftClosed (signature.universal type))
        (typeFamily model (.arr (.arr type .prop) .prop))
        (fun _ predicate => ULift.up
          (∀ value, model.adm type value → (predicate value).down))
  | equality {n : Nat}
      (context : SemanticContext.{max (u + 1) w} n) (type : HOL.Ty Base) :
      Denotes signature model context (liftClosed (signature.equality type))
        (typeFamily model (.arr type (.arr type .prop)))
        (fun _ left right => ULift.up (model.Eqv type left right))
  /-- Semantic recoding, not native definitional conversion.  An arbitrary
  equivalence may change an observable even if the family is unchanged. -/
  | convert {n : Nat}
      {context : SemanticContext.{max (u + 1) w} n} {term : Tower.Tm n}
      {first second : Family context.Environment} {value : Section first}
      (meaning : Denotes signature model context term first value)
      (equivalence : (environment : context.Environment) →
        first environment ≃ second environment) :
      Denotes signature model context term second
        (mapSection equivalence value)

/-- A native abstraction over one simple HOL object is the constant-family
special case of dependent abstraction. -/
theorem Denotes.abstractSimple
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {n : Nat} {context : SemanticContext.{max (u + 1) w} n}
    {domain codomain : HOL.Ty Base} {body : Tower.Tm (n + 1)}
    {bodyValue : Section (typeFamily model codomain)}
    (meaning : Denotes signature model
      (context.snoc (typeFamily model domain)) body
      (typeFamily model codomain) bodyValue) :
    Denotes signature model context (.lam body)
      (typeFamily model (.arr domain codomain))
      (fun environment argument => bodyValue ⟨environment, argument⟩) := by
  exact Denotes.abstraction
    (codomain := fun point => typeFamily model codomain point.1) meaning

/-- Native application at a simple HOL arrow is the constant-family special
case of dependent application. -/
theorem Denotes.applySimple
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {n : Nat} {context : SemanticContext.{max (u + 1) w} n}
    {domain codomain : HOL.Ty Base} {function argument : Tower.Tm n}
    {functionValue : Section (typeFamily model (.arr domain codomain))}
    {argumentValue : Section (typeFamily model domain)}
    (functionMeaning : Denotes signature model context function
      (typeFamily model (.arr domain codomain)) functionValue)
    (argumentMeaning : Denotes signature model context argument
      (typeFamily model domain) argumentValue) :
    Denotes signature model context (.app function argument)
      (typeFamily model codomain)
      (fun environment => functionValue environment (argumentValue environment)) := by
  exact Denotes.application
    (codomain := fun point => typeFamily model codomain point.1)
    functionMeaning argumentMeaning

/-! ## Displayed semantic renaming -/

/-- A semantic context morphism is oriented like a substitution: target
environments are mapped back to source environments. -/
structure Morphism {n m : Nat} (source : SemanticContext.{s} n)
    (target : SemanticContext.{s} m) where
  environment : target.Environment → source.Environment

def Morphism.identity {n : Nat} (context : SemanticContext.{s} n) :
    Morphism context context := ⟨id⟩

def Morphism.comp {n m k : Nat} {source : SemanticContext.{s} n}
    {middle : SemanticContext.{s} m} {target : SemanticContext.{s} k}
    (first : Morphism source middle) (second : Morphism middle target) :
    Morphism source target :=
  ⟨first.environment ∘ second.environment⟩

def Morphism.reindexFamily {n m : Nat} {source : SemanticContext.{s} n}
    {target : SemanticContext.{s} m} (morphism : Morphism source target)
    (family : Family source.Environment) : Family target.Environment :=
  family ∘ morphism.environment

def Morphism.reindexSection {n m : Nat} {source : SemanticContext.{s} n}
    {target : SemanticContext.{s} m} (morphism : Morphism source target)
    {family : Family source.Environment} (value : Section family) :
    Section (morphism.reindexFamily family) :=
  fun environment => value (morphism.environment environment)

@[simp] theorem Morphism.reindexFamily_typeFamily
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {n m : Nat} {source : SemanticContext.{max (u + 1) w} n}
    {target : SemanticContext.{max (u + 1) w} m}
    (morphism : Morphism source target) (type : HOL.Ty Base) :
    morphism.reindexFamily (typeFamily model type) = typeFamily model type :=
  rfl

@[simp] theorem Morphism.reindexSection_typeFamily_constant
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {n m : Nat} {source : SemanticContext.{max (u + 1) w} n}
    {target : SemanticContext.{max (u + 1) w} m}
    (morphism : Morphism source target) (type : HOL.Ty Base)
    (value : HOL.Ty.denote model.Carrier type) :
    morphism.reindexSection (family := typeFamily model type) (fun _ => value) =
      (fun _ => value) :=
  rfl

def Morphism.weaken {n : Nat} (context : SemanticContext.{s} n)
    (family : Family context.Environment) : Morphism context (context.snoc family) :=
  ⟨Sigma.fst⟩

def Morphism.lift {n m : Nat} {source : SemanticContext.{s} n}
    {target : SemanticContext.{s} m} (morphism : Morphism source target)
    (family : Family source.Environment) :
    Morphism (source.snoc family)
      (target.snoc (morphism.reindexFamily family)) :=
  ⟨fun point => ⟨morphism.environment point.1, point.2⟩⟩

/-- A native de Bruijn renaming displayed over its semantic environment map. -/
structure Renaming {n m : Nat} (source : SemanticContext.{s} n)
    (target : SemanticContext.{s} m) (rho : Ren n m)
    (morphism : Morphism source target) where
  familyEq : ∀ index, target.family (rho index) =
    morphism.reindexFamily (source.family index)
  projectionEq : ∀ index,
    castSection (familyEq index) (target.projection (rho index)) =
      morphism.reindexSection (source.projection index)

theorem Renaming.identity {n : Nat} (context : SemanticContext.{s} n) :
    Renaming context context id (Morphism.identity context) where
  familyEq _ := rfl
  projectionEq _ := rfl

theorem Renaming.weaken {n : Nat} (context : SemanticContext.{s} n)
    (family : Family context.Environment) :
    Renaming context (context.snoc family) wk (Morphism.weaken context family) where
  familyEq _ := rfl
  projectionEq _ := rfl

theorem castSection_precompose {Gamma Delta : Type s}
    {first second : Family Gamma} (equal : first = second)
    (value : Section first) (environment : Delta → Gamma) :
    castSection (congrArg (fun family => family ∘ environment) equal)
        (fun point => value (environment point)) =
      fun point => castSection equal value (environment point) := by
  cases equal
  rfl

theorem Renaming.lift {n m : Nat} {source : SemanticContext.{s} n}
    {target : SemanticContext.{s} m} {rho : Ren n m}
    {morphism : Morphism source target}
    (displayed : Renaming source target rho morphism)
    (family : Family source.Environment) :
    Renaming (source.snoc family)
      (target.snoc (morphism.reindexFamily family))
      (liftRen rho) (morphism.lift family) where
  familyEq index := by
    refine Fin.cases ?_ (fun prior => ?_) index
    · rfl
    · apply funext
      intro point
      exact congrFun (displayed.familyEq prior) point.1
  projectionEq index := by
    refine Fin.cases ?_ (fun prior => ?_) index
    · rfl
    · change castSection
          (congrArg (fun displayedFamily => displayedFamily ∘ Sigma.fst)
            (displayed.familyEq prior))
          (fun (point : Extension (morphism.reindexFamily family)) =>
            target.projection (rho prior) point.1) =
        fun (point : Extension (morphism.reindexFamily family)) =>
          source.projection prior (morphism.environment point.1)
      rw [castSection_precompose]
      exact congrArg
        (fun value : Section (morphism.reindexFamily (source.family prior)) =>
          fun point : Extension (morphism.reindexFamily family) => value point.1)
        (displayed.projectionEq prior)

theorem Denotes.change_value
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {n : Nat} {context : SemanticContext.{max (u + 1) w} n}
    {term : Tower.Tm n} {family : Family context.Environment}
    {first second : Section family}
    (meaning : Denotes signature model context term family first)
    (equal : first = second) :
    Denotes signature model context term family second := by
  cases equal
  exact meaning

theorem Denotes.cast_family
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {n : Nat} {context : SemanticContext.{max (u + 1) w} n}
    {term : Tower.Tm n} {first second : Family context.Environment}
    {value : Section first}
    (meaning : Denotes signature model context term first value)
    (equal : first = second) :
    Denotes signature model context term second (castSection equal value) := by
  cases equal
  exact meaning

/-- Native renaming is semantic reindexing. -/
theorem Denotes.rename
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {n m : Nat} {source : SemanticContext.{max (u + 1) w} n}
    {target : SemanticContext.{max (u + 1) w} m} {rho : Ren n m}
    {morphism : Morphism source target}
    (displayed : Renaming source target rho morphism)
    {term : Tower.Tm n} {family : Family source.Environment}
    {value : Section family}
    (meaning : Denotes signature model source term family value) :
    Denotes signature model target (Presentation.rename rho term)
      (morphism.reindexFamily family) (morphism.reindexSection value) := by
  induction meaning generalizing m with
  | var context index =>
      have selected := Denotes.var (signature := signature) (model := model)
        target (rho index)
      have transported := selected.cast_family (displayed.familyEq index)
      exact transported.change_value (displayed.projectionEq index)
  | @abstraction n context domain codomain body bodyValue bodyMeaning bodyInduction =>
      exact .abstraction (bodyInduction (displayed.lift domain))
  | @application n context domain codomain function argument functionValue
      argumentValue functionMeaning argumentMeaning functionInduction
      argumentInduction =>
      exact .application
        (domain := morphism.reindexFamily domain)
        (codomain := (morphism.lift domain).reindexFamily codomain)
        (functionInduction displayed) (argumentInduction displayed)
  | constant context symbol =>
      simpa only [Presentation.rename, rename_liftClosed,
        Morphism.reindexFamily_typeFamily,
        Morphism.reindexSection_typeFamily_constant]
        using (Denotes.constant (signature := signature) (model := model)
          target symbol)
  | implication context =>
      change Denotes signature model target
        (Presentation.rename rho (liftClosed signature.implication))
        (typeFamily model (.arr .prop (.arr .prop .prop)))
        (fun _ premise conclusion => ULift.up (premise.down → conclusion.down))
      simpa only [rename_liftClosed]
        using (Denotes.implication (signature := signature) (model := model) target)
  | universal context type =>
      change Denotes signature model target
        (Presentation.rename rho (liftClosed (signature.universal type)))
        (typeFamily model (.arr (.arr type .prop) .prop))
        (fun _ predicate => ULift.up
          (∀ value, model.adm type value → (predicate value).down))
      simpa only [rename_liftClosed]
        using (Denotes.universal (signature := signature) (model := model) target type)
  | equality context type =>
      change Denotes signature model target
        (Presentation.rename rho (liftClosed (signature.equality type)))
        (typeFamily model (.arr type (.arr type .prop)))
        (fun _ left right => ULift.up (model.Eqv type left right))
      simpa only [rename_liftClosed]
        using (Denotes.equality (signature := signature) (model := model) target type)
  | @convert n context term first second value prior equivalence priorInduction =>
      exact .convert (priorInduction displayed)
        (fun environment => equivalence (morphism.environment environment))

/-! ## Source objects in a mixed native telescope -/

/-- A state relates the compiler's exact native object substitution to one
source Henkin valuation.  Proof variables may occupy the other native
positions; only the selected object terms must realize source variables. -/
structure State (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const)
    {gamma : HOL.Ctx Base} {n : Nat}
    (objects : Sub Tower.Head gamma.length n) where
  context : SemanticContext.{max (u + 1) w} n
  valuation : context.Environment → model.Valuation gamma
  objectsDenote : ∀ {type : HOL.Ty Base} (index : HOL.Var gamma type),
    Denotes signature model context
      (objects (variableIndex index)) (typeFamily model type)
      (fun environment => valuation environment index)

/-- Formula meaning over the source valuation carried by a mixed state. -/
def formulaMeaning
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) (formula : HOL.Formula Const gamma) :
    state.context.Environment → Prop :=
  fun environment => (model.denote formula (state.valuation environment)).down

/-- Adding a proof premise changes the native telescope but not the source
object context or valuation. -/
def proofExtension
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) (premise : HOL.Formula Const gamma) :
    State signature model (fun index => Presentation.rename wk (objects index)) :=
  { context := state.context.snoc (truthFamily (formulaMeaning state premise))
    valuation := fun point => state.valuation point.1
    objectsDenote := fun index =>
      (state.objectsDenote index).rename
        (Renaming.weaken state.context
          (truthFamily (formulaMeaning state premise))) }

/-- Adding a quantified object extends both the source valuation and the
native semantic telescope. -/
def objectExtension
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) (type : HOL.Ty Base) :
    State signature model (gamma := type :: gamma) (liftSub objects) :=
  { context := state.context.snoc (typeFamily model type)
    valuation := fun point => model.extend (state.valuation point.1) point.2
    objectsDenote := by
      intro objectType index
      cases index with
      | vz =>
          exact Denotes.var (signature := signature) (model := model)
            (state.context.snoc (typeFamily model type)) 0
      | vs prior =>
          have priorMeaning := (state.objectsDenote prior).rename
            (Renaming.weaken state.context (typeFamily model type))
          change Denotes signature model
            (state.context.snoc (typeFamily model type))
            (Presentation.rename wk (objects (variableIndex prior)))
            (typeFamily model objectType)
            (fun point => state.valuation point.1 prior) at priorMeaning
          exact priorMeaning.change_value (by
            funext point
            rfl) }

private theorem application_result {n : Nat}
    {function argument : Option (Tower.Tm n)} {result : Tower.Tm n} :
    (do let f ← function; let a ← argument; pure (.app f a)) = some result ↔
      ∃ f a, function = some f ∧ argument = some a ∧ result = .app f a := by
  cases function <;> cases argument <;> simp [eq_comm]

/-- Every represented source object, after the compiler's actual object
substitution, denotes its source Henkin value in the mixed telescope. -/
theorem representation_denotes
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term Const gamma type) {raw : Tower.Tm gamma.length}
    (represented : represent signature term = some raw)
    {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) :
    Denotes signature model state.context (Presentation.subst objects raw)
      (typeFamily model type)
      (fun environment => model.denote term (state.valuation environment)) := by
  induction term generalizing n with
  | var index =>
      cases Option.some.inj represented
      simpa [Presentation.subst, HOL.HenkinModel.denote,
        HOL.PreModel.denote] using state.objectsDenote index
  | const symbol =>
      cases Option.some.inj represented
      simpa [Presentation.subst, subst_liftClosed, HOL.HenkinModel.denote,
        HOL.PreModel.denote] using
        (Denotes.constant (signature := signature) (model := model)
          state.context symbol)
  | app function argument functionInduction argumentInduction =>
      obtain ⟨functionCode, argumentCode, functionRepresented,
        argumentRepresented, rfl⟩ := application_result.mp represented
      simpa [Presentation.subst, HOL.HenkinModel.denote,
        HOL.PreModel.denote] using
        (Denotes.applySimple
          (functionInduction functionRepresented state)
          (argumentInduction argumentRepresented state))
  | @lam domain gamma codomain body inductionHypothesis =>
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ :=
        Option.map_eq_some_iff.mp represented
      simpa [Presentation.subst, objectExtension, HOL.HenkinModel.denote,
        HOL.PreModel.denote] using
        (Denotes.abstractSimple
          (inductionHypothesis bodyRepresented (objectExtension state domain)))
  | imp premise conclusion premiseInduction conclusionInduction =>
      obtain ⟨function, conclusionCode, functionRepresented,
        conclusionRepresented, rfl⟩ := application_result.mp represented
      obtain ⟨head, premiseCode, headRepresented, premiseRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      simpa [Presentation.subst, HOL.HenkinModel.denote,
        HOL.PreModel.denote] using
        (Denotes.applySimple
          (Denotes.applySimple
            (Denotes.implication (signature := signature) (model := model)
              state.context)
            (premiseInduction premiseRepresented state))
          (conclusionInduction conclusionRepresented state))
  | @all domain gamma body inductionHypothesis =>
      obtain ⟨head, argument, headRepresented, argumentRepresented, rfl⟩ :=
        application_result.mp represented
      cases Option.some.inj headRepresented
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ :=
        Option.map_eq_some_iff.mp argumentRepresented
      simpa [Presentation.subst, objectExtension, HOL.HenkinModel.denote,
        HOL.PreModel.denote] using
        (Denotes.applySimple
          (Denotes.universal (signature := signature) (model := model)
            state.context domain)
          (Denotes.abstractSimple
            (inductionHypothesis bodyRepresented (objectExtension state domain))))
  | @eq gamma type left right leftInduction rightInduction =>
      obtain ⟨function, rightCode, functionRepresented,
        rightRepresented, rfl⟩ := application_result.mp represented
      obtain ⟨head, leftCode, headRepresented, leftRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      simpa [Presentation.subst, HOL.HenkinModel.denote,
        HOL.PreModel.denote] using
        (Denotes.applySimple
          (Denotes.applySimple
            (Denotes.equality (signature := signature) (model := model)
              state.context type)
            (leftInduction leftRepresented state))
          (rightInduction rightRepresented state))
  | top | bot | and | or | not | ex => cases represented

/-! ## Proof families for the logical compiler fragment -/

/-- Implication between proof witnesses is equivalent to a proof witness for
the implication.  The equivalence is computational in both directions; proof
irrelevance discharges only its two inverse laws. -/
def implicationProofEquiv (premise conclusion : Prop) :
    (ULift.{s, 0} (PLift premise) → ULift.{s, 0} (PLift conclusion)) ≃
      ULift.{s, 0} (PLift (premise → conclusion)) where
  toFun function :=
    ULift.up ⟨fun proof => (function (ULift.up ⟨proof⟩)).down.down⟩
  invFun proof :=
    fun premiseProof => ULift.up ⟨proof.down.down premiseProof.down.down⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Logical equivalence transports proof witnesses in both directions. -/
def iffProofEquiv {first second : Prop} (equivalence : first ↔ second) :
    ULift.{s, 0} (PLift first) ≃ ULift.{s, 0} (PLift second) where
  toFun proof := ULift.up ⟨equivalence.mp proof.down.down⟩
  invFun proof := ULift.up ⟨equivalence.mpr proof.down.down⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Full Henkin domains identify an ambient dependent proof function with the
Henkin interpretation of universal quantification. -/
def universalProofEquiv
    (model : HOL.HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (type : HOL.Ty Base)
    (body : HOL.Ty.denote model.Carrier type → Prop) :
    ((value : HOL.Ty.denote model.Carrier type) →
        ULift.{max (u + 1) w, 0} (PLift (body value))) ≃
      ULift.{max (u + 1) w, 0}
        (PLift (∀ value, model.adm type value → body value)) where
  toFun function :=
    ULift.up ⟨fun value _ => (function value).down.down⟩
  invFun proof :=
    fun value => ULift.up ⟨proof.down.down value (full type value)⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A native term proves a source formula when the term denotes a section of
the formula's proof-witness family.  The native term remains an argument of
the relation: source truth alone supplies no compiled proof. -/
def Proves
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) (term : Tower.Tm n)
    (formula : HOL.Formula Const gamma) : Prop :=
  ∃ value : Section (truthFamily (formulaMeaning state formula)),
    Denotes signature model state.context term
      (truthFamily (formulaMeaning state formula)) value

/-- The proof variable introduced by a premise denotes that premise. -/
theorem Proves.variable
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects)
    (premise : HOL.Formula Const gamma) :
    Proves (proofExtension state premise) (.var 0) premise := by
  refine ⟨fun point => point.2, ?_⟩
  exact Denotes.var (signature := signature) (model := model)
    (state.context.snoc (truthFamily (formulaMeaning state premise))) 0

/-- Proof weakening is semantic reindexing along telescope projection. -/
theorem Proves.weakenProof
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {term : Tower.Tm n}
    {formula premise : HOL.Formula Const gamma}
    (state : State signature model objects)
    (meaning : Proves state term formula) :
    Proves (proofExtension state premise) (Presentation.rename wk term) formula := by
  obtain ⟨value, termMeaning⟩ := meaning
  refine ⟨fun point => value point.1, ?_⟩
  exact termMeaning.rename
    (Renaming.weaken state.context
      (truthFamily (formulaMeaning state premise)))

/-- Pointwise proof-witness equivalence induced by the HOL weakening law. -/
def objectWeakeningFamilyEquiv
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) (type : HOL.Ty Base)
    (formula : HOL.Formula Const gamma)
    (point : Extension (typeFamily model type : Family state.context.Environment)) :
    truthFamily (formulaMeaning state formula) point.1 ≃
      truthFamily
        (formulaMeaning (objectExtension state type) (HOL.weaken formula)) point := by
  apply iffProofEquiv
  have equal := congrArg ULift.down
    (HOL.Soundness.denote_weaken model formula
      (state.valuation point.1) point.2)
  exact Iff.of_eq equal.symm

/-- Object weakening changes the source formula and valuation together, while
the proof term is reindexed along the same telescope projection. -/
theorem Proves.weakenObject
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n} {term : Tower.Tm n}
    {formula : HOL.Formula Const gamma}
    (state : State signature model objects) (type : HOL.Ty Base)
    (meaning : Proves state term formula) :
    Proves (objectExtension state type) (Presentation.rename wk term)
      (HOL.weaken (σ := type) formula) := by
  obtain ⟨value, termMeaning⟩ := meaning
  have renamed := termMeaning.rename
    (Renaming.weaken state.context (typeFamily model type))
  let weakenedValue : Section
      (truthFamily
        (formulaMeaning (objectExtension state type) (HOL.weaken formula))) :=
    mapSection (objectWeakeningFamilyEquiv state type formula)
      (fun point => value point.1)
  refine ⟨weakenedValue, ?_⟩
  exact Denotes.convert renamed (objectWeakeningFamilyEquiv state type formula)

/-- Pointwise family equivalence implementing implication formation. -/
def implicationFamilyEquiv
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects)
    (premise conclusion : HOL.Formula Const gamma)
    (environment : state.context.Environment) :
    piFamily (truthFamily (formulaMeaning state premise))
        (truthFamily (formulaMeaning (proofExtension state premise) conclusion))
        environment ≃
      truthFamily (formulaMeaning state (.imp premise conclusion)) environment := by
  exact implicationProofEquiv
    ((model.denote premise (state.valuation environment)).down)
    ((model.denote conclusion (state.valuation environment)).down)

/-- Native lambda introduction denotes source implication introduction. -/
theorem Proves.implicationIntro
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {premise conclusion : HOL.Formula Const gamma} {body : Tower.Tm (n + 1)}
    (state : State signature model objects)
    (meaning : Proves (proofExtension state premise) body conclusion) :
    Proves state (.lam body) (.imp premise conclusion) := by
  obtain ⟨bodyValue, bodyMeaning⟩ := meaning
  let functionValue : Section
      (piFamily (truthFamily (formulaMeaning state premise))
        (truthFamily (formulaMeaning (proofExtension state premise) conclusion))) :=
    fun environment premiseProof => bodyValue ⟨environment, premiseProof⟩
  refine ⟨mapSection (implicationFamilyEquiv state premise conclusion) functionValue, ?_⟩
  exact Denotes.convert (Denotes.abstraction bodyMeaning)
    (implicationFamilyEquiv state premise conclusion)

/-- Native application denotes source implication elimination. -/
theorem Proves.implicationElim
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {premise conclusion : HOL.Formula Const gamma}
    {function argument : Tower.Tm n}
    (state : State signature model objects)
    (functionMeaning : Proves state function (.imp premise conclusion))
    (argumentMeaning : Proves state argument premise) :
    Proves state (.app function argument) conclusion := by
  obtain ⟨functionValue, functionDenotes⟩ := functionMeaning
  obtain ⟨argumentValue, argumentDenotes⟩ := argumentMeaning
  let implicationValue : Section
      (piFamily (truthFamily (formulaMeaning state premise))
        (truthFamily (formulaMeaning (proofExtension state premise) conclusion))) :=
    mapSection (fun environment =>
      (implicationFamilyEquiv state premise conclusion environment).symm)
      functionValue
  have implicationDenotes : Denotes signature model state.context function
      (piFamily (truthFamily (formulaMeaning state premise))
        (truthFamily (formulaMeaning (proofExtension state premise) conclusion)))
      implicationValue :=
    Denotes.convert functionDenotes (fun environment =>
      (implicationFamilyEquiv state premise conclusion environment).symm)
  refine ⟨fun environment =>
    implicationValue environment (argumentValue environment), ?_⟩
  change Denotes signature model state.context (.app function argument)
    (fun environment =>
      ULift.{max (u + 1) w, 0}
        (PLift ((model.denote conclusion (state.valuation environment)).down)))
    (fun environment => implicationValue environment (argumentValue environment))
  exact Denotes.application implicationDenotes argumentDenotes

/-- Pointwise family equivalence implementing universal formation.  Fullness
appears here, rather than in source-term interpretation, because a native
lambda accepts every ambient value while Henkin quantification ranges over
admissible values. -/
def universalFamilyEquiv
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    (full : model.FullDomains)
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) (type : HOL.Ty Base)
    (formula : HOL.Formula Const (type :: gamma))
    (environment : state.context.Environment) :
    piFamily (typeFamily model type)
        (truthFamily (formulaMeaning (objectExtension state type) formula))
        environment ≃
      truthFamily (formulaMeaning state (.all formula)) environment := by
  exact universalProofEquiv model full type
    (fun value =>
      (model.denote formula
        (model.extend (state.valuation environment) value)).down)

/-- Native lambda introduction denotes source universal introduction in a
full-domain Henkin model. -/
theorem Proves.universalIntro
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    (full : model.FullDomains)
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {type : HOL.Ty Base} {formula : HOL.Formula Const (type :: gamma)}
    {body : Tower.Tm (n + 1)}
    (state : State signature model objects)
    (meaning : Proves (objectExtension state type) body formula) :
    Proves state (.lam body) (.all formula) := by
  obtain ⟨bodyValue, bodyMeaning⟩ := meaning
  let functionValue : Section
      (piFamily (typeFamily model type)
        (truthFamily (formulaMeaning (objectExtension state type) formula))) :=
    fun environment value => bodyValue ⟨environment, value⟩
  refine ⟨mapSection (universalFamilyEquiv full state type formula) functionValue, ?_⟩
  exact Denotes.convert (Denotes.abstraction bodyMeaning)
    (universalFamilyEquiv full state type formula)

/-- Pointwise proof-witness equivalence induced by semantic instantiation. -/
def instantiationFamilyEquiv
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State signature model objects) {type : HOL.Ty Base}
    (formula : HOL.Formula Const (type :: gamma))
    (argument : HOL.Term Const gamma type)
    (environment : state.context.Environment) :
    truthFamily (formulaMeaning (objectExtension state type) formula)
        ⟨environment, model.denote argument (state.valuation environment)⟩ ≃
      truthFamily (formulaMeaning state (HOL.instantiate argument formula))
        environment := by
  apply iffProofEquiv
  exact (HOL.Soundness.denote_instantiate model argument formula
    (state.valuation environment)).symm

/-- Native application denotes source universal elimination; the argument is
the compiler's actual represented source term in the mixed telescope. -/
theorem Proves.universalElim
    {signature : LogicalSignature Base Const}
    {model : HOL.HenkinModel.{u, v, w} Base Const}
    (full : model.FullDomains)
    {gamma : HOL.Ctx Base} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {type : HOL.Ty Base} {formula : HOL.Formula Const (type :: gamma)}
    {argument : HOL.Term Const gamma type}
    {argumentCode : Tower.Tm gamma.length} {function : Tower.Tm n}
    (state : State signature model objects)
    (represented : represent signature argument = some argumentCode)
    (meaning : Proves state function (.all formula)) :
    Proves state (.app function (Presentation.subst objects argumentCode))
      (HOL.instantiate argument formula) := by
  obtain ⟨functionValue, functionMeaning⟩ := meaning
  let universalValue : Section
      (piFamily (typeFamily model type)
        (truthFamily (formulaMeaning (objectExtension state type) formula))) :=
    mapSection (fun environment =>
      (universalFamilyEquiv full state type formula environment).symm)
      functionValue
  have universalMeaning : Denotes signature model state.context function
      (piFamily (typeFamily model type)
        (truthFamily (formulaMeaning (objectExtension state type) formula)))
      universalValue :=
    Denotes.convert functionMeaning (fun environment =>
      (universalFamilyEquiv full state type formula environment).symm)
  have argumentMeaning := representation_denotes argument represented state
  let appliedValue : Section
      (fun environment =>
        truthFamily (formulaMeaning (objectExtension state type) formula)
          ⟨environment, model.denote argument (state.valuation environment)⟩) :=
    fun environment =>
      universalValue environment
        (model.denote argument (state.valuation environment))
  have appliedMeaning : Denotes signature model state.context
      (.app function (Presentation.subst objects argumentCode))
      (fun environment =>
        truthFamily (formulaMeaning (objectExtension state type) formula)
          ⟨environment, model.denote argument (state.valuation environment)⟩)
      appliedValue :=
    Denotes.application universalMeaning argumentMeaning
  refine ⟨mapSection (instantiationFamilyEquiv state formula argument) appliedValue, ?_⟩
  exact Denotes.convert appliedMeaning
    (instantiationFamilyEquiv state formula argument)

/-- Every full-domain Henkin model supplies a displayed semantic algebra for
the compiler's logical-only operations.  The four logical rules are realized
by dependent-family structure; all equality and extensional rules are
impossible because this operation algebra rejects them. -/
def logicalOnlyAlgebra
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (fresh : signature.rules.constantType proofName = none)
    (model : HOL.HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) :
    GenericSemantics.Algebra signature proofName
      (Operations.logicalOnly signature proofName fresh) where
  State := State signature model
  Denotes := Proves
  proofExtension := proofExtension
  objectExtension := objectExtension
  proofVariable := Proves.variable
  proofWeakening := fun state _ meaning => Proves.weakenProof state meaning
  objectWeakening := Proves.weakenObject
  implicationIntro := fun state _ meaning => Proves.implicationIntro state meaning
  implicationElim := Proves.implicationElim
  universalIntro := Proves.universalIntro full
  universalElim := Proves.universalElim full
  reflexivity := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  symmetry := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  transitivity := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  propositionExtensionality := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  propositionForward := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  functionCongruence := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  argumentCongruence := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  lambdaCongruence := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  functionExtensionality := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  beta := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]
  eta := by
    intros
    simp_all [Operations.logicalOnly, RawOperations.logicalOnly]

/-! ## Audit -/

#print axioms Renaming.lift
#print axioms Denotes.rename
#print axioms representation_denotes
#print axioms implicationProofEquiv
#print axioms universalProofEquiv
#print axioms logicalOnlyAlgebra

end HenkinFamilySemantics
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
