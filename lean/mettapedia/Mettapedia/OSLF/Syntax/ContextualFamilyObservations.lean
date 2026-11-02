import Mettapedia.OSLF.Syntax.ContextualFamilyComposition

/-!
# Context and sort metadata on existing contextual terms

A solver queue may contain terms at different object contexts and sorts.
An observation packages precisely those indices with the existing binding
term. Instantiation preserves the metadata and uses the same contextual
operation. No additional term constructors are introduced.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W X : Type}
  {source : V → MetaArity S} {target : W → MetaArity S} {next : X → MetaArity S}

abbrev Observation (S : Signature) {V : Type} (declaration : V → MetaArity S) :=
  (context : Ctx S) × (sort : S.Srt) × Term (signature S declaration) context sort

def observe {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) : Observation S source :=
  ⟨Γ, sort, term⟩

theorem observe_injective {Γ : Ctx S} {sort : S.Srt} :
    Function.Injective (observe (source := source) (Γ := Γ) (sort := sort)) := by
  intro first second same
  have inner : (⟨sort, first⟩ : (result : S.Srt) × Term (signature S source) Γ result) = ⟨sort, second⟩ :=
    eq_of_heq (Sigma.mk.inj same).2
  exact eq_of_heq (Sigma.mk.inj inner).2

def instantiateObservation (assignment : Assignment source target) : Observation S source → Observation S target
  | ⟨context, sort, term⟩ => ⟨context, sort, instantiate assignment term⟩

theorem instantiateObservation_observe (assignment : Assignment source target)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    instantiateObservation assignment (observe term) = observe (instantiate assignment term) := rfl

theorem instantiateObservation_identity (observation : Observation S source) :
    instantiateObservation (generator source) observation = observation := by
  rcases observation with ⟨context, sort, term⟩
  exact congrArg observe (instantiate_identity term)

theorem instantiateObservation_comp (first : Assignment source target) (second : Assignment target next)
    (observation : Observation S source) :
    instantiateObservation second (instantiateObservation first observation) =
      instantiateObservation (Assignment.compose second first) observation := by
  rcases observation with ⟨context, sort, term⟩
  exact congrArg observe (instantiate_comp first second term)

theorem factor_observation (candidate : Assignment source next) (answer : Assignment source target)
    (residual : Assignment target next)
    (components : ∀ identity, candidate identity = instantiate residual (answer identity))
    (observation : Observation S source) :
    instantiateObservation candidate observation =
      instantiateObservation residual (instantiateObservation answer observation) := by
  rcases observation with ⟨context, sort, term⟩
  apply congrArg observe
  rw [instantiate_comp]
  exact congrArg (fun assignment => instantiate assignment term) (funext components)

end Mettapedia.OSLF.Binding.ContextualFamily
