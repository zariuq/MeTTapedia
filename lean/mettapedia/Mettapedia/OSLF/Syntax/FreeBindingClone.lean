import Mettapedia.OSLF.Syntax.BindingCloneFoldSubstitution

/-!
# The free binding clone of a scoped signature

The actual terms are initial among substitution-compatible algebras of the
same binding signature. A model morphism preserves variables, operators and
simultaneous semantic substitution. The unique candidate is the structural
fold; its substitution law was proved separately, rather than inserted as a
field or assumed from raw initiality.

This is the free terms rung with substitution. Presented equations and
operational rules still require their own freely generated constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FreeBindingClone

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution

universe u v w

variable {S : Signature}

/-- A binding-clone homomorphism preserves raw constructors and semantic
substitution with its full context-indexed environment. -/
structure Hom (A : BindingCloneAlgebra.Algebra.{u} S)
    (B : BindingCloneAlgebra.Algebra.{v} S) where
  raw : FreeBindingTerms.Hom A.toRaw B.toRaw
  map_substitute : ∀ {Γ Δ : Ctx S} {sort : S.Srt}
    (env : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ Δ)
    (x : A.substitution.Carrier Γ sort),
    raw.map (A.substitution.substitute env x) =
      B.substitution.substitute (fun s v => raw.map (env s v)) (raw.map x)

namespace Hom

@[ext] theorem ext {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {f g : Hom A B} (agree : f.raw = g.raw) : f = g := by
  cases f
  cases g
  cases agree
  rfl

def id (A : BindingCloneAlgebra.Algebra.{u} S) : Hom A A where
  raw := FreeBindingTerms.Hom.id A.toRaw
  map_substitute := by intro Γ Δ sort env x; rfl

def comp {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {C : BindingCloneAlgebra.Algebra.{w} S}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  raw := FreeBindingTerms.Hom.comp f.raw g.raw
  map_substitute := by
    intro Γ Δ sort env x
    change g.raw.map (f.raw.map (A.substitution.substitute env x)) =
      C.substitution.substitute
        (fun s v => g.raw.map (f.raw.map (env s v)))
        (g.raw.map (f.raw.map x))
    have first := congrArg (fun y => g.raw.map y) (f.map_substitute env x)
    have second :=
      g.map_substitute (fun s v => f.raw.map (env s v)) (f.raw.map x)
    exact first.trans second

end Hom

instance algebraCategory : CategoryTheory.Category (BindingCloneAlgebra.Algebra.{u} S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro A B f
    apply Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)
  comp_id := by
    intro A B f
    apply Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)
  assoc := by
    intro A B C D f g h
    apply Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl)

/-- The fold is a full binding-clone morphism because it was separately
proved natural for simultaneous substitution. -/
def interpretHom (A : BindingCloneAlgebra.Algebra.{u} S) :
    Hom (BindingCloneAlgebra.terms S) A where
  raw := FreeBindingTerms.foldHom A.toRaw
  map_substitute := by
    intro Γ Δ sort env term
    exact interpret_bind A env term

/-- A full binding-clone map from syntax is determined already by its raw
constructor action, so the proved fold is its only possible value. -/
theorem hom_unique (A : BindingCloneAlgebra.Algebra.{u} S)
    (h : Hom (BindingCloneAlgebra.terms S) A) : h = interpretHom A := by
  apply Hom.ext
  exact FreeBindingTerms.hom_unique A.toRaw h.raw

/-- Terms are initial in the category of small semantic binding clones.
The higher-universe fold remains available through `interpretHom`. -/
def termsIsInitial (S : Signature) :
    IsInitial (BindingCloneAlgebra.terms S) :=
  IsInitial.ofUniqueHom interpretHom (fun A h => hom_unique A h)

end Mettapedia.OSLF.Binding.FreeBindingClone
