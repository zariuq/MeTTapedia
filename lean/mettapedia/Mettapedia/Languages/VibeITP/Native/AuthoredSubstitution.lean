import Mettapedia.GSLT.LanguageDef.AuthoredComputation
import Mettapedia.Languages.VibeITP.Native.ComputedSubstitution
import Mettapedia.Languages.VibeITP.Presentation.SubstitutionSignature

/-!
# Vibe substitution leaves computed by the authored program

The authored Vibe substitution program, run by the shared engine on a signature
snapshot of the theory, is an authored computation whose relation is the
specification's top-level substitution. Its queries are guarded by the shape
check of the theory's signature. The existing qualification of substitution
judgments against the Vibe rule package makes it a qualified computation of the
calculus: certificates may replace substitution replay by a leaf that runs the
authored program.

The authored program and the earlier Lean evaluator agree on every guarded
query, so the authored leaf can take the evaluator's place.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.AuthoredSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.Languages.VibeITP.Presentation
open Mettapedia.Languages.VibeITP.Presentation.ComputationalData
open Mettapedia.Languages.VibeITP.Presentation.ComputationalShift
open Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution
open Mettapedia.Languages.VibeITP.Native.ComputedSubstitution

/-- A top-level substitution query in the shape domain of a signature. -/
structure TopQuery (sig : Sig) where
  images : List Spec.Term
  body : Spec.Term
  shaped : guard sig (.top images body) = true

/-- The specification's top-level substitution. -/
def Substitutes (sig : Sig) (query : TopQuery sig) (result : Spec.Term) : Prop :=
  Spec.substBVars sig query.images.length query.images query.body 0 = some result

/-- **Vibe top-level substitution is an authored computation** of the shared
interface. -/
def authored (sig : Sig) : AuthoredComputation (TopQuery sig) Spec.Term where
  relation := Substitutes sig
  program := substitutionProgram
  host := computationalHost
  head := "vibe:subst"
  encodeQuery query :=
    [encodeTable (substitutionSnapshot sig query.body query.images), natural query.images.length,
      .list (encodeTerms query.images), encode query.body, natural 0]
  encodeAnswer := encodeResult
  accepts query result := by
    rw [substitution_signature_result_exact]
    exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩
  refuses query := by
    rw [substitution_signature_result_exact]
    constructor
    · rintro same ⟨result, related⟩
      have none := encodeResult_injective same
      rw [Substitutes] at related
      rw [related] at none
      cases none
    · intro never
      congr 1
      cases computed : Spec.substBVars sig query.images.length query.images query.body 0 with
      | none => rfl
      | some result => exact absurd ⟨result, computed⟩ never

/-- **The authored program and the Lean evaluator agree** on every guarded
query. -/
theorem authored_agrees_with_evaluator (sig : Sig) (query : TopQuery sig) (result : Spec.Term) :
    (authored sig).relation query result ↔ run sig (.top query.images query.body) = some result := by
  rw [run_of_domain sig _ ((guard_iff sig _).mp query.shaped)]
  rfl

/-- **The qualification of authored substitution in the Vibe calculus**: every
related pair is a derivable substitution judgment of the hosted theory. -/
def qualification {T : Theory} {allocation : Nat} (hosted : Hosted T allocation) :
    Qualification (authored T.sig) (kernelValidated T allocation) where
  judgment query result := judgment T.sig (.top query.images query.body) result
  derivable query result related := by
    have domain := (guard_iff T.sig _).mp query.shaped
    have computed := (authored_agrees_with_evaluator T.sig query result).mp related
    obtain ⟨raw, checked⟩ := (run_iff_replay hosted _ result domain).mp computed
    exact checkRaw_soundness checked

end Mettapedia.Languages.VibeITP.Native.AuthoredSubstitution
