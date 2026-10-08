import Mettapedia.SetTheory.Profiles.ProfileChoice

/-!
# Explicit host-Choice witness extraction

The witness-bearing product/sum rearrangement in `ProfileChoice` is
constructive. Extraction from merely inhabited witness types is a separate
operation here, implemented with Lean's named `Classical.choice`. It supplies
new witnesses and does not invert the loss of original occurrence evidence.
This host operation adopts no native extensional set-Choice law.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileChoiceHost

universe u v w
variable {A : Type u} {B : A → Type v} {Evidence : (a : A) → B a → Type w}

noncomputable def extractMerelyInhabited
    (known : (a : A) → Nonempty (Σ b : B a, Evidence a b)) :
    (a : A) → Σ b : B a, Evidence a b :=
  fun a => Classical.choice (known a)

noncomputable def chooseFromMerelyInhabited
    (known : (a : A) → Nonempty (Σ b : B a, Evidence a b)) :
    Σ chosen : (a : A) → B a, (a : A) → Evidence a (chosen a) :=
  ProfileChoice.piSigmaChoice (extractMerelyInhabited known)

theorem host_choice_assembles_merely_inhabited
    (known : (a : A) → Nonempty (Σ b : B a, Evidence a b)) :
    Nonempty (Σ chosen : (a : A) → B a, (a : A) → Evidence a (chosen a)) :=
  ⟨chooseFromMerelyInhabited known⟩

end Mettapedia.SetTheory.Profiles.ProfileChoiceHost
