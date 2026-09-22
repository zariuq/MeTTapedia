import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLFragmentDenotation
import Mettapedia.Logic.HOL.Embedding.UniformListPredicateFamily

/-!
# HOL predicate witnesses consumed by native List computations

Native List spines receive a compositional observation from the independently
defined denotation of their native element terms. The actual native map
programs execute to those spines by beta and the declared List iota rules.
The existing object-HOL induction proof supplies the property witness consumed
by the generated finite-execution OSLF observation.

This is a concrete connection in the ordinary Boolean-list Henkin model.
It does not identify the abstract HOL sequence type with native List, supply
native dependent inhabitants, or interpret all native terms. The GSLT here
uses the native reduction relation, not the separate textual LanguageDef
interpreter. Observations assert finite reachability, not trace or cost
equivalence.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeListHOLPredicateObservation

open Presentation NativeIndexedFamilies
open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
open NativeHOLFragmentDenotation IntrinsicNativeListMapComputation
open Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

abbrev model := StandardListModel.model
abbrev ElementMeaning (gamma : HOL.Ctx BaseSort) :=
  model.Valuation gamma → StandardListModel.LiftedElement
abbrev FunctionMeaning (gamma : HOL.Ctx BaseSort) :=
  model.Valuation gamma → StandardListModel.LiftedElement → StandardListModel.LiftedElement

def elementCode (gamma : HOL.Ctx BaseSort) : Tower.Tm gamma.length :=
  typeAt types gamma.length element

/-- Unlike the abstract HOL sequence constant, this observation explicitly
inspects native nil/cons constructors and native element denotations. -/
inductive SpineDenotes {gamma : HOL.Ctx BaseSort} :
    Tower.Tm gamma.length → (model.Valuation gamma → List Bool) → Prop where
  | nil : SpineDenotes (Intrinsic.nilApp (elementCode gamma)) (fun _ => [])
  | cons {head tail : Tower.Tm gamma.length}
      {headValue : ElementMeaning gamma} {tailValue : model.Valuation gamma → List Bool} :
      Denotes model (type := element) head headValue → SpineDenotes tail tailValue →
        SpineDenotes (Intrinsic.consApp (elementCode gamma) head tail)
          (fun rho => (headValue rho).down :: tailValue rho)

abbrev Heads (gamma : HOL.Ctx BaseSort) :=
  List (Tower.Tm gamma.length × ElementMeaning gamma)

def headValues {gamma : HOL.Ctx BaseSort} (heads : Heads gamma)
    (rho : model.Valuation gamma) : List Bool :=
  heads.map (fun head => (head.2 rho).down)

def functionValue {gamma : HOL.Ctx BaseSort} (meaning : FunctionMeaning gamma)
    (rho : model.Valuation gamma) : Bool → Bool :=
  fun value => (meaning rho ⟨value⟩).down

theorem encode_denotes {gamma : HOL.Ctx BaseSort} (heads : Heads gamma)
    (interpreted : ∀ head ∈ heads, Denotes model (type := element) head.1 head.2) :
    SpineDenotes (encode (elementCode gamma) (heads.map Prod.fst)) (headValues heads) := by
  induction heads with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (interpreted head List.mem_cons_self)
        (ih (fun h member => interpreted h (List.mem_cons_of_mem _ member)))

theorem fusion_output_denotes {gamma : HOL.Ctx BaseSort}
    (f g : Tower.Tm gamma.length) (fMeaning gMeaning : FunctionMeaning gamma)
    (fDenotes : Denotes model (type := mapping) f fMeaning)
    (gDenotes : Denotes model (type := mapping) g gMeaning)
    (heads : Heads gamma)
    (interpreted : ∀ head ∈ heads, Denotes model (type := element) head.1 head.2) :
    SpineDenotes
      (encode (elementCode gamma) ((heads.map Prod.fst).map (fun x => .app f (.app g x))))
      (fun rho => (headValues heads rho).map
        (fun x => functionValue fMeaning rho (functionValue gMeaning rho x))) := by
  induction heads with
  | nil => exact .nil
  | cons head tail ih =>
      have step := SpineDenotes.cons
        (Denotes.application (a := element) (b := element) fDenotes
          (Denotes.application (a := element) (b := element) gDenotes
            (interpreted head List.mem_cons_self)))
        (ih (fun h member => interpreted h (List.mem_cons_of_mem _ member)))
      simpa only [encode, List.map_cons, headValues, functionValue, ULift.up_down] using step

/-- A public observation consumes the interpreted property of the native
constructor result. The property need not be decidable. -/
def observes {gamma : HOL.Ctx BaseSort} (rho : model.Valuation gamma)
    (property : List Bool → Prop) (output : Tower.Tm gamma.length) : Prop :=
  ∃ values, SpineDenotes output values ∧ property (values rho)

theorem SpineDenotes.coherent {gamma : HOL.Ctx BaseSort}
    {raw : Tower.Tm gamma.length} {left right : model.Valuation gamma → List Bool}
    (first : SpineDenotes raw left) (second : SpineDenotes raw right)
    (rho : model.Valuation gamma) : left rho = right rho := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
      cases second with
      | cons otherHead otherTail =>
          exact congrArg₂ List.cons (congrArg ULift.down (head.coherent otherHead rho))
            (ih otherTail)

theorem observes_iff {gamma : HOL.Ctx BaseSort} (rho : model.Valuation gamma)
    (property : List Bool → Prop) {raw : Tower.Tm gamma.length}
    {values : model.Valuation gamma → List Bool} (meaning : SpineDenotes raw values) :
    observes rho property raw ↔ property (values rho) := by
  constructor
  · rintro ⟨otherValues, otherMeaning, accepted⟩
    exact (meaning.coherent otherMeaning rho) ▸ accepted
  · intro accepted
    exact ⟨values, meaning, accepted⟩

/-- The same native substitution acts on code and on its observed semantic
environment. Only its actual variable components need interpretations. -/
theorem SpineDenotes.substitute {gamma delta : HOL.Ctx BaseSort}
    {raw : Tower.Tm gamma.length} {values : model.Valuation gamma → List Bool}
    (meaning : SpineDenotes raw values)
    (sigma : Sub Tower.Head gamma.length delta.length)
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {type} (index : HOL.Var gamma type),
      Denotes model (sigma (variableIndex index)) (fun rho => environment rho index)) :
    SpineDenotes (subst sigma raw) (fun rho => values (environment rho)) := by
  have elementSub : subst sigma (elementCode gamma) = elementCode delta :=
    typeAt_subst types sigma element
  induction meaning with
  | nil =>
      simpa only [Intrinsic.nilApp, subst, elementSub] using
        (SpineDenotes.nil (gamma := delta))
  | cons head tail ih =>
      have result := SpineDenotes.cons (head.substitute sigma environment components) ih
      simpa only [Intrinsic.consApp, subst, elementSub] using result

/-- Finite execution and observation both commute with an interpreted
context substitution. The path uses the existing substitution-closed native
reduction, not a replay or new evaluation policy. -/
theorem observed_execution_substitute {gamma delta : HOL.Ctx BaseSort}
    (level : LevelExpr) {source output : Tower.Tm gamma.length}
    {values : model.Valuation gamma → List Bool}
    (path : Reduces level source output) (meaning : SpineDenotes output values)
    (sigma : Sub Tower.Head gamma.length delta.length)
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {type} (index : HOL.Var gamma type),
      Denotes model (sigma (variableIndex index)) (fun rho => environment rho index))
    (rho : model.Valuation delta) (property : List Bool → Prop)
    (accepted : property (values (environment rho))) :
    gsltDiamond (reduction level delta.length).closure (observes rho property)
      (subst sigma source) := by
  exact (finite_observation_iff level _ _).2
    ⟨subst sigma output, path.substitute sigma,
      _, meaning.substitute sigma environment components, accepted⟩

/-- The premise is a user's existing refinement of the unfused value.
Its transport is obtained from the actual HOL induction/congruence proof;
native computation then makes that transported witness observable. -/
theorem fusion_consumes_hol_refinement {gamma : HOL.Ctx BaseSort}
    (level : LevelExpr) (f g : Tower.Tm gamma.length)
    (fMeaning gMeaning : FunctionMeaning gamma)
    (fDenotes : Denotes model (type := mapping) f fMeaning)
    (gDenotes : Denotes model (type := mapping) g gMeaning)
    (heads : Heads gamma)
    (interpreted : ∀ head ∈ heads, Denotes model (type := element) head.1 head.2)
    (rho : model.Valuation gamma) (property : List Bool → Prop)
    (accepted : property (((headValues heads rho).map (functionValue gMeaning rho)).map
      (functionValue fMeaning rho))) :
    gsltDiamond (reduction level gamma.length).closure (observes rho property)
        (applyMap (elementCode gamma) (elementCode gamma) f
          (applyMap (elementCode gamma) (elementCode gamma) g
            (encode (elementCode gamma) (heads.map Prod.fst)))) ∧
      gsltDiamond (reduction level gamma.length).closure (observes rho property)
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) (heads.map Prod.fst))) := by
  apply fusion_observed level (elementCode gamma) (elementCode gamma) (elementCode gamma)
    f g (heads.map Prod.fst) (observes rho property)
  refine ⟨_, fusion_output_denotes f g fMeaning gMeaning fDenotes gDenotes heads interpreted, ?_⟩
  exact HOL.Embedding.UniformListPredicateFamily.Standard.outputRefinement_property
    property (functionValue fMeaning rho) (functionValue gMeaning rho)
    (headValues heads rho) accepted

/-- Actual represented HOL expressions are inputs to the independent native
head interpretation, not extra semantic assumptions about map execution. -/
theorem represented_head {gamma : HOL.Ctx BaseSort} (term : Expr gamma element)
    {raw : Tower.Tm gamma.length} (represented : represent signature term = some raw) :
    Denotes model (type := element) raw (fun rho => model.denote term rho) :=
  representation_square term represented

theorem represented_function {gamma : HOL.Ctx BaseSort} (term : Expr gamma mapping)
    {raw : Tower.Tm gamma.length} (represented : represent signature term = some raw) :
    Denotes model (type := mapping) raw (fun rho => model.denote term rho) :=
  representation_square term represented

namespace Controls

abbrev gamma : HOL.Ctx BaseSort := [element, mapping, mapping]

def sourceF : Expr gamma mapping := .var (.vs (.vs .vz))
def sourceG : Expr gamma mapping := .var (.vs .vz)
def sourceX : Expr gamma element := .var .vz

def f : Tower.Tm gamma.length := .var 2
def g : Tower.Tm gamma.length := .var 1
def x : Tower.Tm gamma.length := .var 0

def fMeaning : FunctionMeaning gamma := fun rho => model.denote sourceF rho
def gMeaning : FunctionMeaning gamma := fun rho => model.denote sourceG rho
def xMeaning : ElementMeaning gamma := fun rho => model.denote sourceX rho

theorem f_denotes : Denotes model (type := mapping) f fMeaning :=
  represented_function sourceF rfl
theorem g_denotes : Denotes model (type := mapping) g gMeaning :=
  represented_function sourceG rfl
theorem x_denotes : Denotes model (type := element) x xMeaning :=
  represented_head sourceX rfl

def rho : model.Valuation gamma :=
  model.extend (σ := element)
    (HOL.Embedding.UniformListPredicateFamily.Standard.functionContext
      (fun _ => true) Bool.not).1.1 (⟨false⟩ : StandardListModel.LiftedElement)

def heads : Heads gamma := [(x, xMeaning)]

/-- The positive case instantiates the source expressions, native execution,
and the actual HOL proof at the same valuation. -/
theorem correct_composition_observed (level : LevelExpr) :
    gsltDiamond (reduction level gamma.length).closure
        (observes rho (fun output => output = [true]))
        (applyMap (elementCode gamma) (elementCode gamma) f
          (applyMap (elementCode gamma) (elementCode gamma) g
            (encode (elementCode gamma) [x]))) ∧
      gsltDiamond (reduction level gamma.length).closure
        (observes rho (fun output => output = [true]))
        (applyMap (elementCode gamma) (elementCode gamma) (compose f g)
          (encode (elementCode gamma) [x])) := by
  apply fusion_consumes_hol_refinement level f g fMeaning gMeaning
    f_denotes g_denotes heads
  · intro head member
    have same : head = (x, xMeaning) := List.mem_singleton.mp member
    subst head
    exact x_denotes
  · rfl

/-- The reversed-composition constructor output cannot masquerade as the
proved result. This is observation rejection, not a claim about all native
reduction paths or a refutation of a true proposition from a bad proof. -/
theorem wrong_composition_output_rejected :
    ¬ observes rho (fun output => output = [true])
      (encode (elementCode gamma) [.app g (.app f x)]) := by
  have meaning := SpineDenotes.cons
    (Denotes.application (a := element) (b := element) g_denotes
      (Denotes.application (a := element) (b := element) f_denotes x_denotes))
    SpineDenotes.nil
  intro accepted
  have wrong := (observes_iff rho _ meaning).mp accepted
  exact (by decide : ¬ ([false] : List Bool) = [true]) wrong

end Controls

#print axioms encode_denotes
#print axioms fusion_output_denotes
#print axioms SpineDenotes.coherent
#print axioms SpineDenotes.substitute
#print axioms observed_execution_substitute
#print axioms fusion_consumes_hol_refinement
#print axioms represented_head
#print axioms represented_function
#print axioms Controls.correct_composition_observed
#print axioms Controls.wrong_composition_output_rejected

end NativeListHOLPredicateObservation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
