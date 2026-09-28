import Mettapedia.Languages.Agda.Adequacy.StaticForward
import Mettapedia.Languages.Agda.StaticSpecification.TypedSubstitution
import Mettapedia.Languages.Agda.Structural.StaticAdmission

/-!
# Admitting independently derived contexts and substitutions

The forward static translation supplies native derivations for both context
boundaries and every variable image of a source typed substitution. This is a
translation into the actual admitted structural context category. It neither
selects evidence from a proposition nor presumes static reflection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy

open Mettapedia.OSLF.Binding
open Structural.Statics

def substitutionForward {n m : Nat} {Γ : StaticSpecification.RawContext n}
    {Δ : StaticSpecification.RawContext m} {σ : StaticSpecification.Substitution n m}
    (d : StaticSpecification.SubDeriv Γ Δ σ) :
    TypedSubstitution Derivation (embedContext Γ) (embedContext Δ) (embedSub σ) where
  source := contextForward d.source
  target := contextForward d.target
  image v := by
    have typed := typingForward (d.lookup (readVar v))
    rw [← embed_readVar v, embedSub_var]
    exact (congrArg (fun A => Derivation (Structural.Statics.typed
      (embedContext Δ) (embedTerm (σ (readVar v))) A))
      (embedContext_lookup_subst Γ (readVar v) σ)).mp typed

noncomputable def admittedContext {n : Nat} {Γ : StaticSpecification.RawContext n}
    (d : StaticSpecification.FormCtx Γ) : canonicalAdmission.Context :=
  ⟨⟨n, embedContext Γ⟩, ⟨contextForward d⟩⟩

noncomputable def admittedSubstitution {n m : Nat} {Γ : StaticSpecification.RawContext n}
    {Δ : StaticSpecification.RawContext m} {σ : StaticSpecification.Substitution n m}
    (d : StaticSpecification.SubDeriv Γ Δ σ) :
    canonicalAdmission.Substitution (admittedContext d.target) (admittedContext d.source) :=
  ⟨embedSub σ, ⟨substitutionForward d⟩⟩

/-- The translation retains exactly the source's raw substitution action. -/
theorem admittedSubstitution_val {n m : Nat} {Γ : StaticSpecification.RawContext n}
    {Δ : StaticSpecification.RawContext m} {σ : StaticSpecification.Substitution n m}
    (d : StaticSpecification.SubDeriv Γ Δ σ) : (admittedSubstitution d).val = embedSub σ := rfl

end Mettapedia.Languages.Agda.StaticAdequacy
