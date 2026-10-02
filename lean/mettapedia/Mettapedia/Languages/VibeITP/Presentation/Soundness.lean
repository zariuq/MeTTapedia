import Mettapedia.Languages.VibeITP.Presentation.KernelSoundness
import Mettapedia.Languages.VibeITP.Presentation.SoundAdmissions
import Mettapedia.Languages.VibeITP.Presentation.Validation

/-!
# Vibe-ITP presentation: complete static package soundness

Every fixed rule and every fact admitted by a concrete hosted theory
preserves the independently specified judgment meaning. Induction over
actual first-order derivations yields specification derivability; the generic
checker bridge transfers this result to accepted raw articles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker

theorem kernelRules_meaningSound (T : Theory) {n : Nat} (h : Hosted T n)
    {r : FORule} (hr : r ∈ kernelRules) : RuleMeaningSound T r := by
  simp only [kernelRules, List.mem_append, or_assoc] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · exact arithmeticRules_meaningSound T hr
  · exact listRules_meaningSound T hr
  · exact termRules_meaningSound T hr
  · exact shiftRules_meaningSound T hr
  · exact substRules_meaningSound T hr
  · exact instRules_meaningSound T hr
  · exact literalRules_meaningSound T hr
  · exact theoremRules_meaningSound T h.builtin hr
  · exact definitionRules_meaningSound T h.builtin h.fvarBinders hr
  · exact ms_builtinRules T h.builtin hr

theorem hostedRules_meaningSound (T : Theory) (n : Nat) (h : Hosted T n)
    {r : FORule} (hr : r ∈ kernelRules ++ theoryRules T n) : RuleMeaningSound T r := by
  rcases List.mem_append.mp hr with hr | hr
  · exact kernelRules_meaningSound T h hr
  · exact ms_theoryRules T n h hr

theorem meaning_of_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    {goal : Pattern} (derivation : FODerivable (kernelRules ++ theoryRules T n) goal) :
    Meaning T goal :=
  derivation.meaning (fun _ hr => hostedRules_meaningSound T n h hr)

/-- The full presented static kernel derives only independently derivable
theorem statements, uniformly over the concretely admitted theory. -/
theorem derives_of_foDerivable {T : Theory} {n : Nat} (h : Hosted T n)
    {φ : Term} (derivation :
      FODerivable (kernelRules ++ theoryRules T n) (jThm (encTerm T.sig φ))) :
    Derives T φ := by
  obtain ⟨ψ, heq, hψ⟩ := meaning_of_foDerivable h derivation
  have hφψ : φ = ψ := encTerm_inj T.sig heq
  exact hφψ.symm ▸ hψ

/-- Acceptance by the generic checker implies independent derivability
whenever its concrete validated package presents the full hosted rule list. -/
theorem checkRaw_sound_presented {T : Theory} {n : Nat} (h : Hosted T n)
    {definition : ValidatedCalculusLanguageDef}
    (presents : Presents definition (kernelRules ++ theoryRules T n))
    {φ : Term} {article : RawProof}
    (accepted : checkRaw definition (jThm (encTerm T.sig φ)) article = true) :
    Derives T φ :=
  derives_of_foDerivable h
    ((checkRaw_exists_iff_foDerivable presents _).mp ⟨article, accepted⟩)

/-- The actual theory-extended, validated NIK kernel checker accepts only
statements derivable in the independently specified Vibe-ITP kernel. -/
theorem checkRaw_kernel_sound {T : Theory} {n : Nat} (h : Hosted T n)
    {φ : Term} {article : RawProof}
    (accepted : checkRaw (kernelValidated T n) (jThm (encTerm T.sig φ)) article = true) :
    Derives T φ :=
  checkRaw_sound_presented h (kernelValidated_presents T n) accepted

/-- Derivations remain valid when their real rule list is extended. -/
theorem FODerivable.mono {R S : List FORule} (hRS : R ⊆ S) {goal : Pattern}
    (derivation : FODerivable R goal) : FODerivable S goal := by
  induction derivation with
  | rule r hr args hlen hvalid _ ih => exact .rule r (hRS hr) args hlen hvalid ih

end Mettapedia.Languages.VibeITP.Presentation
