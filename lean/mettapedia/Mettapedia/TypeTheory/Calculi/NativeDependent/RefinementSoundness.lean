import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementComputationSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAssumptionSubstitutionSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundnessAssumptions
import Mettapedia.TypeTheory.NativeLocalPiEta
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundness

/-!
# Soundness of all generated external dependent judgments

Every authored local rule is interpreted by actual native families, sections
and subobjects in the independently supplied presheaf world category. Data
binders and predicate assumptions retain their distinct context actions.
The primitive meanings are independent; only their local header realization
is required. The complete generated derivation
theorem is proved by induction on its retained premise trees.

No global model soundness, syntactic classifying property or internal
universe operation is assumed. The theorem concerns this presheaf model class; arbitrary logical CwF
models and the classifying property remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {D : Signature S}

namespace ModelData

theorem rule_sound (model : ModelData S C) (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (eta : PiEta model.products stable.1) (rule : RuleCode D)
    (premises : (position : Fin rule.premises.length) → Interprets model (rule.premises.get position)) :
    Interprets model rule.conclusion := by
  exact (model.interprets_toAbstract_iff _).mp
    (Abstract.ModelData.rule_sound model.toAbstract realization.toAbstract stable beta eta rule
      (fun position => (model.interprets_toAbstract_iff _).mpr (premises position)))

end ModelData

namespace Derivation

theorem sound (model : ModelData S C) (realization : SignatureRealization model D)
    (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (eta : PiEta model.products stable.1) {judgment : Judgment S}
    (derivation : Derivation D judgment) : Interprets model judgment := by
  let algebra : JudgmentDerivation.Algebra (judgmentSignature D) := {
    Carrier := fun judgment => PLift (Interprets model judgment)
    conclude := by
      intro judgment rule premises
      rcases rule with ⟨rule, conclusion⟩
      cases conclusion
      exact ⟨model.rule_sound realization stable beta eta rule
        (fun position => (premises ⟨position⟩).down)⟩ }
  exact (JudgmentDerivation.interpret algebra derivation).down

/-- The native presheaf operations discharge the local stability and
computational qualifications for every supplied primitive realization. -/
theorem native_sound (model : ModelData S C) (realization : SignatureRealization model D)
    {judgment : Judgment S} (derivation : Derivation D judgment) : Interprets model judgment :=
  derivation.sound model realization (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
