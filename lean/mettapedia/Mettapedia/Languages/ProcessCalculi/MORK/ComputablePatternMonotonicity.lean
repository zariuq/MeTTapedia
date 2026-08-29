import Mettapedia.Languages.ProcessCalculi.MORK.Conformance

/-!
# Monotonicity of computable positive pattern matching

Adding atoms to a finite list presentation cannot destroy a positive
simultaneous match.  The theorem is intentionally scoped to `Pattern`, whose
factors are all positive; negative source factors require a different law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Every row produced over a smaller positive-pattern space is also produced
over a larger space containing all of its atoms. -/
theorem cmatchPattern_mono
    (σ₀ : Subst) (small large : CSpace) (p : Pattern)
    (included : ∀ atom ∈ small, atom ∈ large)
    (σ : Subst) (consumed : List Atom)
    (matched : (σ, consumed) ∈ cmatchPattern σ₀ small p) :
    (σ, consumed) ∈ cmatchPattern σ₀ large p := by
  simp only [cmatchPattern] at matched ⊢
  suffices h : ∀ (patterns : List Atom) (σIn : Subst)
      (consumedIn : List Atom) (σOut : Subst) (consumedOut : List Atom),
      (σOut, consumedOut) ∈
          cmatchPattern.go small patterns σIn consumedIn →
        (σOut, consumedOut) ∈
          cmatchPattern.go large patterns σIn consumedIn by
    exact h p.atoms σ₀ [] σ consumed matched
  intro patterns
  induction patterns with
  | nil =>
      intro σIn consumedIn σOut consumedOut member
      simpa only [cmatchPattern.go] using member
  | cons pattern rest induction =>
      intro σIn consumedIn σOut consumedOut member
      simp only [cmatchPattern.go] at member ⊢
      rw [List.mem_flatMap] at member ⊢
      obtain ⟨⟨σMid, atom⟩, foundSmall, continued⟩ := member
      refine ⟨(σMid, atom), ?_, induction σMid (atom :: consumedIn)
        σOut consumedOut continued⟩
      rw [List.mem_filterMap] at foundSmall ⊢
      obtain ⟨concrete, concreteSmall, matchedAtom⟩ := foundSmall
      exact ⟨concrete, included concrete concreteSmall, matchedAtom⟩

#print axioms cmatchPattern_mono

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
