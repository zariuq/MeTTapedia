import Mettapedia.Logic.HOL.ContinuationPayloadBoundary

/-!
# A decoder that is injective exactly where represented values require it

The Boolean reader recovers each represented bit. A raw constant-false
continuation collides with the encoded false bit, but is outside the admitted
image. This separates guarded data recovery from unrestricted raw-payload
injectivity without claiming a recursive constructor implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ContinuationPayloadBoundary.Controls

def readBoolean (payload : Payload Unit Bool Bool) : Bool := payload (fun _ value _ => value)
def invalid : Payload Unit Bool Bool := fun _ => false

theorem read_represented (value : Bool) : readBoolean (singletonPayload () value) = value := rfl

theorem represented_reader_injective :
    Set.InjOn readBoolean (Set.range (singletonPayload (Element := Bool) (Truth := Bool) ())) := by
  rintro _ ⟨first,rfl⟩ _ ⟨second,rfl⟩ same
  exact congrArg (singletonPayload ()) same

theorem invalid_not_represented : invalid ∉ Set.range (singletonPayload (Element := Bool) (Truth := Bool) ()) := by
  rintro ⟨value,same⟩
  have impossible : true = false := congrFun same (fun _ _ _ => true)
  exact Bool.noConfusion impossible

theorem raw_collision : readBoolean invalid = readBoolean (singletonPayload () false) := rfl

theorem raw_collision_distinct : invalid ≠ singletonPayload (Truth := Bool) () false := by
  intro same
  exact invalid_not_represented ⟨false,same.symm⟩

theorem raw_reader_not_injective : ¬ Function.Injective readBoolean := by
  intro injective
  exact raw_collision_distinct (injective raw_collision)

#print axioms represented_reader_injective
#print axioms raw_reader_not_injective
end Mettapedia.Logic.HOL.ContinuationPayloadBoundary.Controls
