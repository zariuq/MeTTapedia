import Mettapedia.Cybernetics.ObservedVariety
import Mettapedia.GSLT.Core.LooseRelationEquipment

/-!
# Relational coordination in a world of views

This module gives a small interface for heterogeneous, modular views that can
coordinate without first embedding their states into one universal
representation.  The default cross-view connection is a proof-relevant loose
relation.  A direct functional translator is available only after the relation
is proved total and proof-relevantly deterministic.

The distinction follows Viktoras Veitas and David Weinbaum's account of a
"world of views": views may remain distinct, modular, and open to interaction
without converging to one shared worldview.  The precise relational equipment,
representation criterion, and gluing formulations below are our formal
extensions of that account.

Reference:

- V. Veitas and D. Weinbaum, *A World of Views: A World of Interacting
  Post-human Intelligences* (2014), arXiv:1410.6915.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.WorldOfViews

open Mettapedia.Cybernetics
open Mettapedia.GSLT.LooseRelationEquipment

universe u

/-! ## Modular local presentations -/

/-- A view presented by a family of local modules.  Joint faithfulness says
that the family retains every distinction of the view, while each individual
module may expose only a projection. -/
structure ModularView (State : Type u) where
  Module : Type u
  module_nonempty : Nonempty Module
  LocalState : Module -> Type u
  observer : (module : Module) -> Observer State (LocalState module)
  jointlyFaithful : Function.Injective fun state module =>
    (observer module).observe state

namespace ModularView

variable {State : Type u}

/-- The joint observation assembled from all local module observations. -/
def jointObservation (view : ModularView State) (state : State) :
    (module : view.Module) -> view.LocalState module :=
  fun module => (view.observer module).observe state

theorem jointObservation_injective (view : ModularView State) :
    Function.Injective view.jointObservation :=
  view.jointlyFaithful

end ModularView

/-! ## Plural systems and relational coordination -/

/-- A family of heterogeneous views connected by proof-relevant relations.
No common carrier and no globally preferred representation are assumed. -/
structure System (View : Type u) where
  State : View -> Type u
  modular : (view : View) -> ModularView (State view)
  relation : (source target : View) -> Loose (State source) (State target)

namespace System

variable {View : Type u} (system : System View)

/-- A retained coordination witness between two local views. -/
abbrev Coordination (source target : View) : Type u :=
  Sigma fun input : system.State source =>
    Sigma fun output : system.State target =>
      system.relation source target input output

/-- Two views can interact when at least one witnessed coordination exists. -/
def CanCoordinate (source target : View) : Prop :=
  Nonempty (system.Coordination source target)

/-- Openness is relational availability between distinct views.  It does not
assert a common ontology, a global state, or a functional translator. -/
def IsOpen : Prop :=
  forall source target, source ≠ target -> system.CanCoordinate source target

/-- A functional translator is an earned representation of the underlying
loose relation, not an additional primitive connection. -/
abbrev FunctionalTransport (source target : View) :=
  Representation (system.relation source target)

/-- Functional transport is earned exactly by totality and proof-relevant
determinism of the relational coordination fibre. -/
theorem functionalTransport_iff_total_and_deterministic
    (source target : View) :
    Nonempty (system.FunctionalTransport source target) <->
      Total (system.relation source target) /\
        Deterministic (system.relation source target) :=
  Representation.nonempty_iff_total_and_deterministic

namespace FunctionalTransport

variable {system} {source target : View}

/-- The direct map licensed by a functional-transport certificate. -/
def translate (transport : system.FunctionalTransport source target) :
    system.State source -> system.State target :=
  transport.map

/-- Executing the licensed map retains a witness in the original relation. -/
def relationWitness (transport : system.FunctionalTransport source target)
    (input : system.State source) :
    system.relation source target input (transport.translate input) :=
  (transport.exact input (transport.map input)).symm
    ⟨⟨rfl⟩⟩

end FunctionalTransport

end System

/-! ## Objectives and optional global gluing -/

/-- A proof-relevant objective evaluated directly on a relational
coordination.  It requires no universal state representation. -/
structure CoordinationObjective {View : Type u} (system : System View)
    (source target : View) where
  Outcome : Type u
  certifies : forall input output,
    system.relation source target input output -> Outcome -> Type u

namespace CoordinationObjective

variable {View : Type u} {system : System View} {source target : View}

/-- Evidence that one relational coordination realizes an objective. -/
structure Success
    (objective : CoordinationObjective system source target) where
  input : system.State source
  output : system.State target
  relationWitness : system.relation source target input output
  outcome : objective.Outcome
  certificate : objective.certifies input output relationWitness outcome

end CoordinationObjective

/-- A proposed global realization for a plural system.  This structure is
optional: relational coordination does not presuppose that one exists. -/
structure GluingProblem {View : Type u} (system : System View) where
  Global : Type u
  restrict : Global -> (view : View) -> system.State view

namespace GluingProblem

variable {View : Type u} {system : System View}

/-- A local family is realized only when one global state restricts to every
local view in the family. -/
def Realizes (problem : GluingProblem system)
    (family : (view : View) -> system.State view) : Prop :=
  Exists fun global => forall view, problem.restrict global view = family view

end GluingProblem

/-! ## Positive and negative controls -/

namespace Canary

inductive View where
  | request
  | response
deriving DecidableEq, Repr

def State : View -> Type
  | .request => Unit
  | .response => Bool × Bool

inductive ResponseModule where
  | left
  | right
deriving DecidableEq, Repr

def requestModules : ModularView Unit where
  Module := Unit
  module_nonempty := ⟨()⟩
  LocalState _ := Unit
  observer _ := ⟨fun _ => ()⟩
  jointlyFaithful := by
    intro first second _
    cases first
    cases second
    rfl

def responseModules : ModularView (Bool × Bool) where
  Module := ResponseModule
  module_nonempty := ⟨.left⟩
  LocalState _ := Bool
  observer
    | .left => ⟨Prod.fst⟩
    | .right => ⟨Prod.snd⟩
  jointlyFaithful := by
    intro first second same
    apply Prod.ext
    · exact congrFun same .left
    · exact congrFun same .right

def modules : (view : View) -> ModularView (State view)
  | .request => requestModules
  | .response => responseModules

/-- The request view relates to every response. -/
def alternatives : Loose Unit (Bool × Bool) :=
  fun _ _ => Unit

/-- Returning from a response to the request view forgets the two response
coordinates through one exact companion. -/
def returnToRequest : Loose (Bool × Bool) Unit :=
  companion fun _ => ()

def relation : (source target : View) -> Loose (State source) (State target)
  | .request, .request => identity
  | .request, .response => alternatives
  | .response, .request => returnToRequest
  | .response, .response => identity

def plural : System View where
  State := State
  modular := modules
  relation := relation

theorem plural_isOpen : plural.IsOpen := by
  intro source target different
  cases source <;> cases target
  · exact (different rfl).elim
  · exact ⟨⟨(), (false, false), ()⟩⟩
  · exact ⟨⟨(false, false), (), ⟨⟨rfl⟩⟩⟩⟩
  · exact (different rfl).elim

/-- One request has two genuinely distinct related responses. -/
theorem request_coordinates_distinct_responses :
    Nonempty (plural.relation .request .response () (false, false)) /\
      Nonempty (plural.relation .request .response () (true, false)) :=
  ⟨⟨()⟩, ⟨()⟩⟩

/-- Relational openness does not manufacture a functional translator: the
request-to-response relation is nondeterministic. -/
theorem request_response_not_functional :
    Not (Nonempty (plural.FunctionalTransport .request .response)) := by
  rintro ⟨transport⟩
  have falseEqual :=
    (transport.exact () (false, false) ()).down.down
  have trueEqual :=
    (transport.exact () (true, false) ()).down.down
  have outputsEqual : (false, false) = (true, false) :=
    falseEqual.symm.trans trueEqual
  exact Bool.false_ne_true (congrArg Prod.fst outputsEqual)

def returnTransport : plural.FunctionalTransport .response .request :=
  Representation.companionSelf fun _ => ()

theorem response_request_functional :
    Nonempty (plural.FunctionalTransport .response .request) :=
  ⟨returnTransport⟩

@[simp] theorem returnTransport_translate (response : Bool × Bool) :
    returnTransport.translate response = () :=
  rfl

/-- A coordination objective reads the first response coordinate while
retaining the relational witness that produced the response. -/
def firstResponseObjective :
    CoordinationObjective plural .request .response where
  Outcome := Bool
  certifies _ output _ outcome := EqWitness output.1 outcome

def firstResponseSuccess : firstResponseObjective.Success where
  input := ()
  output := (true, false)
  relationWitness := ()
  outcome := true
  certificate := ⟨⟨rfl⟩⟩

end Canary

end Mettapedia.GSLT.WorldOfViews

#print axioms Mettapedia.GSLT.WorldOfViews.System.functionalTransport_iff_total_and_deterministic
#print axioms Mettapedia.GSLT.WorldOfViews.Canary.plural_isOpen
#print axioms Mettapedia.GSLT.WorldOfViews.Canary.request_response_not_functional
#print axioms Mettapedia.GSLT.WorldOfViews.Canary.response_request_functional
