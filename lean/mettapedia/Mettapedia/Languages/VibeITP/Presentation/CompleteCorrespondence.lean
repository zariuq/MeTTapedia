import Mettapedia.Languages.VibeITP.Presentation.CompleteInstantiation
import Mettapedia.Languages.VibeITP.Presentation.CompleteLiterals
import Mettapedia.Languages.VibeITP.Presentation.CompleteDefinitions
import Mettapedia.Languages.VibeITP.Presentation.DerivedTermShape

/-!
# Complete static Vibe-ITP kernel correspondence

Every independent derivation has a presented derivation and an accepted raw
article for the actual validated NIK package. Together with the assembled
soundness theorem this yields equivalence, uniformly over concrete hosted
theories. A theory's declared axioms remain its premises.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.GSLT.LanguageDef.InferenceChecker

theorem complete_axiom {R : List FORule} {T : Theory} {n : Nat}
    (hT : theoryRules T n ⊆ R) (φ : Term) (hφ : φ ∈ T.axioms) :
    FODerivable R (jThm (encTerm T.sig φ)) := by
  obtain ⟨k, hk⟩ := axiomRule_mem (sig := T.sig) (k := 1) hφ
  apply intro_axiomRule T.sig k φ
  apply hT
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hk)))

theorem complete_definition {R : List FORule} {T : Theory} {n : Nat}
    (hT : theoryRules T n ⊆ R) (d : Definition) (hd : d ∈ T.definitions) :
    FODerivable R (jThm (encTerm T.sig (definitionStatement T.sig d.symbol d.fvars d.value))) := by
  obtain ⟨k, hk⟩ := definitionRule_mem (sig := T.sig) (k := 1) hd
  apply intro_definitionRule T.sig k d
  exact hT (List.mem_append.mpr (Or.inr hk))

theorem complete_modusPonens {R : List FORule} (hR : kernelRules ⊆ R)
    (sig : Sig) (hb : BuiltinsFixed sig) (a b : Term)
    (himpl : FODerivable R (jThm (encTerm sig (.impl a b))))
    (ha : FODerivable R (jThm (encTerm sig a))) :
    FODerivable R (jThm (encTerm sig b)) := by
  have himpl' := himpl
  simp only [Term.impl, encTerm_app, encSym_builtin hb .impl,
    encTermList_cons, encTermList_nil] at himpl'
  exact intro_rMp (hR (by simp [kernelRules, theoremRules]))
    (isData_encTerm sig a) (isData_encTerm sig b)
    (IsData.app2 _ (isData_encNat (depthArgs sig (.builtin .impl) 0 [a, b]))
      (isData_encBool (isFvarSym sig (.builtin .impl) || hasFvarList sig [a, b])))
    himpl' ha

/-- Constructive completeness for every static kernel inference constructor. -/
theorem complete_derives {R : List FORule} (hR : kernelRules ⊆ R)
    {T : Theory} {n : Nat} (hT : theoryRules T n ⊆ R) (h : Hosted T n)
    {φ : Term} (derivation : Derives T φ) : FODerivable R (jThm (encTerm T.sig φ)) := by
  induction derivation with
  | «axiom» hφ => exact complete_axiom hT _ hφ
  | definition hd => exact complete_definition hT _ hd
  | modusPonens _ _ ihimpl iha => exact complete_modusPonens hR T.sig h.builtin _ _ ihimpl iha
  | @instantiate φ ψ value F hφ hvalue hs ih =>
      exact complete_instantiateStatement hR hT h F value φ ψ hvalue
        (derives_termShape h hφ) hs ih
  | litIsNat hn => exact complete_litIsNat hR T h.builtin _ hn
  | litLt hab hbw => exact complete_litLt hR T h.builtin _ _ hab hbw
  | litAdd haw hbw => exact complete_litAdd hR T h.builtin _ _ haw hbw
  | litMul haw hbw => exact complete_litMul hR T h.builtin _ _ haw hbw
  | litDiv haw hbw hb0 => exact complete_litDiv hR T h.builtin _ _ haw hbw hb0
  | litLength hwf => exact complete_litLength hR T h.builtin _ hwf
  | litGet hwf hi => exact complete_litGet hR T h.builtin _ _ hwf hi

theorem derives_iff_foDerivable {T : Theory} {n : Nat} (h : Hosted T n) (φ : Term) :
    Derives T φ ↔ FODerivable (kernelRules ++ theoryRules T n) (jThm (encTerm T.sig φ)) :=
  ⟨complete_derives (fun _ hr => List.mem_append.mpr (Or.inl hr))
      (fun _ hr => List.mem_append.mpr (Or.inr hr)) h,
    derives_of_foDerivable h⟩

/-- The independent static kernel and the actual theory-extended NIK checker
accept exactly the same encoded theorem statements. -/
theorem derives_iff_checkRaw {T : Theory} {n : Nat} (h : Hosted T n) (φ : Term) :
    Derives T φ ↔ ∃ article : RawProof,
      checkRaw (kernelValidated T n) (jThm (encTerm T.sig φ)) article = true :=
  (derives_iff_foDerivable h φ).trans
    (checkRaw_exists_iff_foDerivable (kernelValidated_presents T n) _).symm

theorem complete_article {T : Theory} {n : Nat} (h : Hosted T n)
    {φ : Term} (derivation : Derives T φ) :
    ∃ article : RawProof, checkRaw (kernelValidated T n) (jThm (encTerm T.sig φ)) article = true :=
  (derives_iff_checkRaw h φ).mp derivation

end Mettapedia.Languages.VibeITP.Presentation
