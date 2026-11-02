import Mettapedia.Languages.MM0.Kernel.SubstitutionStability
import Mettapedia.Languages.MM0.Kernel.ProofSharing

/-!
# Conservative extension by independently derived MM0 theorem schemas

A new theorem schema is justified in its own formal context and under its
retained hypotheses. At each use, admissible substitution transports that
derivation and cut supplies the instantiated hypotheses. A successful closed
instance is not a substitute for this schematic justification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

/-- Eliminate added theorem schemas by admissible instantiation and cut. -/
theorem Derives.replaceTheorems {signature : TermSignature} {definitions : Definition.Signature}
    {base extended : TheoremSignature}
    (justified : ∀ index declaration, extended index = some declaration →
      base index = some declaration ∨
        Derives signature definitions base declaration.arguments declaration.hypotheses declaration.conclusion)
    {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    (derived : Derives signature definitions extended context hypotheses expression) :
    Derives signature definitions base context hypotheses expression := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ => DerivesList signature definitions base context hypotheses expressions) with
  | hypothesis member => exact .hypothesis member
  | @theoremApp index declaration arguments instance_ known instantiated children ih =>
      rcases justified index declaration known with primitive | derivedSchema
      · exact .theoremApp primitive instantiated ih
      · have moved := instantiated.admissible.derives instantiated.hypotheses derivedSchema instantiated.conclusion
        exact moved.replaceHypotheses ((derivesList_iff _ _ _ _ _ _).mp ih)
  | conversion converted child ih => exact .conversion converted ih
  | nil => exact .nil
  | cons head tail ihHead ihTail => exact .cons ihHead ihTail

namespace TheoremSignature

def extend (base : TheoremSignature) (index : Nat) (declaration : TheoremDecl) : TheoremSignature :=
  fun queried => if queried = index then some declaration else base queried

theorem extend_conservative {signature : TermSignature} {definitions : Definition.Signature}
    {base : TheoremSignature} {index : Nat} {declaration : TheoremDecl}
    (schema : Derives signature definitions base declaration.arguments declaration.hypotheses declaration.conclusion)
    {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    (derived : Derives signature definitions (extend base index declaration) context hypotheses expression) :
    Derives signature definitions base context hypotheses expression := by
  apply derived.replaceTheorems
  intro queried payload known
  by_cases same : queried = index
  · subst queried
    have equal : declaration = payload := by simpa [extend] using known
    subst payload
    exact Or.inr schema
  · exact Or.inl (by simpa [extend, same] using known)

theorem extend_preserves {signature : TermSignature} {definitions : Definition.Signature}
    {base : TheoremSignature} {index : Nat} (fresh : base index = none) (declaration : TheoremDecl)
    {context : Context} {hypotheses : List Preterm} {expression : Preterm}
    (derived : Derives signature definitions base context hypotheses expression) :
    Derives signature definitions (extend base index declaration) context hypotheses expression := by
  apply derived.extendSignatures (fun _ _ known => known) (fun _ _ known => known)
  intro queried payload known
  have different : queried ≠ index := by
    intro same
    subst queried
    rw [fresh] at known
    cases known
  simpa [extend, different] using known

theorem extend_iff {signature : TermSignature} {definitions : Definition.Signature}
    {base : TheoremSignature} {index : Nat} {declaration : TheoremDecl}
    (fresh : base index = none)
    (schema : Derives signature definitions base declaration.arguments declaration.hypotheses declaration.conclusion)
    (context : Context) (hypotheses : List Preterm) (expression : Preterm) :
    Derives signature definitions (extend base index declaration) context hypotheses expression ↔
      Derives signature definitions base context hypotheses expression :=
  ⟨extend_conservative schema, extend_preserves fresh declaration⟩

end TheoremSignature
end Mettapedia.Languages.MM0.Kernel
