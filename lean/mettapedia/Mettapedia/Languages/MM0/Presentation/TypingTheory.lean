import Mettapedia.Languages.MM0.Presentation.TypingCorrespondence
import Mettapedia.Languages.MM0.Kernel.TheoryInvariant
import Mettapedia.Languages.MM0.Kernel.SignatureExtension

/-! # Authored typing on the actual admitted MM0 theory store -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalTyping

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem signatureOf_eq_lookup (table : SignatureTable) (index : Nat) :
    signatureOf table index = table.lookup index := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, declaration⟩ := entry
    by_cases same : index = key
    · subst index
      simp [signatureOf, List.lookup]
    · have unequal : (index == key) = false := by simp [same]
      simp [signatureOf, List.lookup, same, unequal, ih]

theorem theory_signature (theory : Theory) : signatureOf theory.terms = theory.termSignature := by
  funext index
  exact signatureOf_eq_lookup theory.terms index

theorem theory_infer_computes (theory : Theory) (context : Context) (expression : Preterm) :
    Applies typingProgram computationalHost "mm0:infer"
      [encodeTable theory.terms, encodeContext context, encode expression]
      (encodeType (Preterm.infer theory.termSignature context expression)) := by
  simpa only [theory_signature] using infer_computes theory.terms context expression

theorem theory_infer_accepts_iff (theory : Theory) (context remaining : Context)
    (expression : Preterm) (sort : Nat) :
    Applies typingProgram computationalHost "mm0:infer"
      [encodeTable theory.terms, encodeContext context, encode expression]
      (encodeType (some (remaining, sort))) ↔
      Preterm.HasType theory.termSignature context expression remaining sort := by
  simpa only [theory_signature] using infer_accepts_iff theory.terms context remaining expression sort

theorem theory_extension_preserves_typing {before after : Theory}
    (extension : Theory.Extends before after) {context remaining : Context}
    {expression : Preterm} {sort : Nat}
    (accepted : Applies typingProgram computationalHost "mm0:infer"
      [encodeTable before.terms, encodeContext context, encode expression]
      (encodeType (some (remaining, sort)))) :
    Applies typingProgram computationalHost "mm0:infer"
      [encodeTable after.terms, encodeContext context, encode expression]
      (encodeType (some (remaining, sort))) := by
  apply (theory_infer_accepts_iff after context remaining expression sort).mpr
  exact ((theory_infer_accepts_iff before context remaining expression sort).mp accepted).extendSignature
    extension.terms

end Mettapedia.Languages.MM0.Presentation.ComputationalTyping
