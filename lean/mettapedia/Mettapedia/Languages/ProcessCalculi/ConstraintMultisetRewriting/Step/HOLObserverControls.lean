import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLObserverModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLObserverAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventFeedbackControls

/-! # Loaded recording controls on genuine store-changing events

The two labels perform the same store update, but two-event words retain
their different orders. Encoded records cannot change their state indices.
The raw sentinel does not supply a record in an empty native data fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverControls

open Presentation.Controls PublicationTransportControls EventFeedbackControls
open Mettapedia.Languages.OpenTheory.TypeFamilySemantics

def second_event (label : Bool) : P.effectCore.Event P.eventAdmission
    [(true, false)] [(true, false), (true, false)] :=
  P.event label ⟨prepares _ (), trivial⟩

def orderedPath (first second : Bool) :
    @Quiver.Path (EffectCore.EventObject P.effectCore P.eventAdmission) _ []
      [(true, false), (true, false)] :=
  ((Quiver.Path.nil).cons (base_event first)).cons (second_event second)

theorem native_records (first second : Bool) :
    observer.evaluate (orderedPath first second) [] = [first, second] := rfl

variable (input : HOLRunModel.Input) (other : OperatorFamilies.{0}) (prior : Assignment.{0})

theorem loaded_records (first second : Bool) :
    HOLObserverModel.record P.effectCore P.eventAdmission observer input other prior
      (HOLPreparedRunEncoding.word P.effectCore P.eventAdmission (orderedPath first second))
      (HOLObserverEncoding.encode P.effectCore P.eventAdmission observer (s := []) []) =
        HOLObserverEncoding.encode P.effectCore P.eventAdmission observer
          (s := [(true, false), (true, false)]) [first, second] :=
  HOLObserverModel.record_eq_native P.effectCore P.eventAdmission observer input other prior
    (orderedPath first second) []

theorem loaded_order_retained :
    HOLObserverModel.record P.effectCore P.eventAdmission observer input other prior
      (HOLPreparedRunEncoding.word P.effectCore P.eventAdmission (orderedPath false true))
      (HOLObserverEncoding.encode P.effectCore P.eventAdmission observer (s := []) []) ≠
    HOLObserverModel.record P.effectCore P.eventAdmission observer input other prior
      (HOLPreparedRunEncoding.word P.effectCore P.eventAdmission (orderedPath true false))
      (HOLObserverEncoding.encode P.effectCore P.eventAdmission observer (s := []) []) := by
  rw [loaded_records, loaded_records]
  intro same
  have labels := HOLObserverEncoding.encode_injective P.effectCore P.eventAdmission observer _ same
  exact Bool.false_ne_true (List.cons.inj labels).1

omit input other prior in
theorem state_index_retained :
    ¬HOLObserverEncoding.Valid P.effectCore P.eventAdmission observer [(true, false)]
      (HOLObserverEncoding.encode P.effectCore P.eventAdmission observer (s := []) []) :=
  HOLObserverEncoding.wrong_source P.effectCore P.eventAdmission observer (by decide) []

def emptyObserver : EventObserver (EffectCore.EventObject P.effectCore P.eventAdmission) where
  Data _ := Empty
  update _ impossible := nomatch impossible

omit input other prior in
theorem empty_fibre_not_inhabited (state : Store) :
    ¬∃ raw, HOLObserverEncoding.Valid P.effectCore P.eventAdmission emptyObserver state raw :=
  HOLObserverEncoding.no_valid_initial_record P.effectCore P.eventAdmission emptyObserver state
    (fun ⟨impossible⟩ => nomatch impossible)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLObserverControls
