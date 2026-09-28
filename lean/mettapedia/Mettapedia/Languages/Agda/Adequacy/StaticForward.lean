import Mettapedia.Languages.Agda.Adequacy.StaticParameters
import Mettapedia.Languages.Agda.StaticSpecification.Judgments
import Mettapedia.Languages.Agda.Structural.StaticConstructors

/-!
# Source derivations generate structural static rule trees

This translation reads each constructor of the independently authored static
reference and supplies the corresponding authored structural rule and all of
its ordered premises. Raw substitution and abstraction opening commute by the
separately proved syntax correspondence.

This is the forward direction for the canonical application fragment. It is
not static reflection, subject reduction for administrative computation nodes,
normalization, or correctness of an executable checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy

open Structural.Statics

@[simp] theorem embedPi_code {n : Nat} (A : StaticSpecification.Ty n)
    (B : StaticSpecification.TyAbs n) :
    (piType (embedTypeParameter A) (embedTypeBody B)).code = embedTy (StaticSpecification.Ty.pi A B) :=
  (congrArg TypeParameter.code (embedTypeParameter_pi A B)).symm.trans
    (embedTypeParameter_code (StaticSpecification.Ty.pi A B))

@[simp] theorem universeType_code (n k : Nat) :
    (universeType n k).code = embedTy (StaticSpecification.Ty.universe k) := rfl

@[simp] theorem embedTerm_zero (n : Nat) :
    embedTerm (StaticSpecification.Term.var (0 : Fin (n + 1))) =
      (Mettapedia.OSLF.Binding.Term.var .zero : RawTm (n + 1)) := rfl

mutual
  def contextForward {n : Nat} {Γ : StaticSpecification.RawContext n}
      (d : StaticSpecification.FormCtx Γ) : Derivation (context (embedContext Γ)) :=
    match d with
    | .nil => Derivation.empty
    | .snoc prior type => Derivation.extend (contextForward prior) (formationForward type)
  termination_by structural d

  def formationForward {n : Nat} {Γ : StaticSpecification.RawContext n} {A : StaticSpecification.Ty n}
      (d : StaticSpecification.FormTy Γ A) : Derivation (formed (embedContext Γ) (embedTy A)) :=
    match d with
    | .ofTyping term => Derivation.formation (typingForward term)
  termination_by structural d

  def typingForward {n : Nat} {Γ : StaticSpecification.RawContext n}
      {t : StaticSpecification.Term n} {A : StaticSpecification.Ty n}
      (d : StaticSpecification.Typing Γ t A) :
      Derivation (typed (embedContext Γ) (embedTerm t) (embedTy A)) :=
    match d with
    | .sort k formed => Derivation.sort k (contextForward formed)
    | .var i formed => by
        exact (congrArg (fun A => Derivation
          (typed (embedContext Γ) (embedTerm (.var i)) A)) (embedContext_lookup Γ i)).mpr
          (Derivation.variableTerm (Γ := embedContext Γ) (embedVar i) (contextForward formed))
    | .pi (a := A) (b := B) da db => by
        simpa only [embedTypeParameter_code, embedTypeBody_open, embedTypeBody_pi,
          embedTypeParameter_level, embedTypeBody_level, universeType_code] using
          Derivation.pi (A := embedTypeParameter A) (B := embedTypeBody B)
            (by simpa only [embedTypeParameter_code] using formationForward da)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open] using formationForward db)
    | .lam (a := A) (b := B) (body := body) da db dt => by
        simpa only [embedTermBody_lambda, embedPi_code] using
          Derivation.lambda (A := embedTypeParameter A) (B := embedTypeBody B) (body := embedTermBody body)
            (by simpa only [embedTypeParameter_code] using formationForward da)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open] using formationForward db)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open, embedTermBody_open] using typingForward dt)
    | .app (a := A) (b := B) (f := f) (u := u) df du => by
        simpa only [embedTerm_app, embedTypeBody_instantiate, embedTypeParameter_code] using
          Derivation.application (A := embedTypeParameter A) (B := embedTypeBody B)
            (f := embedTerm f) (a := embedTerm u)
            (by simpa only [embedPi_code] using typingForward df)
            (by simpa only [embedTypeParameter_code] using typingForward du)
    | .conv term equal => Derivation.conversion (typingForward term) (typeEqualityForward equal)
  termination_by structural d

  def typeEqualityForward {n : Nat} {Γ : StaticSpecification.RawContext n} {A B : StaticSpecification.Ty n}
      (d : StaticSpecification.TypeEq Γ A B) :
      Derivation (typeEqual (embedContext Γ) (embedTy A) (embedTy B)) :=
    match d with
    | .atSort equal => Derivation.typeEquality (termEqualityForward equal)
  termination_by structural d

  def termEqualityForward {n : Nat} {Γ : StaticSpecification.RawContext n}
      {t u : StaticSpecification.Term n} {A : StaticSpecification.Ty n}
      (d : StaticSpecification.TermEq Γ t u A) :
      Derivation (termEqual (embedContext Γ) (embedTerm t) (embedTerm u) (embedTy A)) :=
    match d with
    | .refl term => Derivation.reflexivity (typingForward term)
    | .symm equal => Derivation.symmetry (termEqualityForward equal)
    | .trans first second => Derivation.transitivity (termEqualityForward first) (termEqualityForward second)
    | .conv terms types => Derivation.equalityConversion (termEqualityForward terms) (typeEqualityForward types)
    | .piCong (a := A) (a' := A') (b := B) (b' := B') da de db => by
        simpa only [embedTypeBody_pi, embedTypeParameter_level, embedTypeBody_level, universeType_code] using
          Derivation.piCongruence (A := embedTypeParameter A) (A' := embedTypeParameter A')
            (B := embedTypeBody B) (B' := embedTypeBody B')
            (by simpa only [embedTypeParameter_code] using formationForward da)
            (by simpa only [embedTypeParameter_code] using typeEqualityForward de)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open] using typeEqualityForward db)
    | .appCong (a := A) (b := B) (f := f) (g := g) (u := u) (v := v) df du => by
        simpa only [embedTerm_app, embedTypeBody_instantiate, embedTypeParameter_code] using
          Derivation.applicationCongruence (A := embedTypeParameter A) (B := embedTypeBody B)
            (f := embedTerm f) (g := embedTerm g) (a := embedTerm u) (b := embedTerm v)
            (by simpa only [embedPi_code] using termEqualityForward df)
            (by simpa only [embedTypeParameter_code] using termEqualityForward du)
    | .beta (a := A) (b := B) (body := body) (u := u) da db dt du => by
        simpa only [embedTerm_app, embedTermBody_lambda, embedTermBody_instantiate,
          embedTypeBody_instantiate, embedTypeParameter_code] using
          Derivation.beta (A := embedTypeParameter A) (B := embedTypeBody B) (body := embedTermBody body)
            (a := embedTerm u)
            (by simpa only [embedTypeParameter_code] using formationForward da)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open] using formationForward db)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open, embedTermBody_open] using typingForward dt)
            (by simpa only [embedTypeParameter_code] using typingForward du)
    | .eta (a := A) (b := B) (f := f) (g := g) da db df dg de => by
        simpa only [embedPi_code] using
          Derivation.eta (A := embedTypeParameter A) (B := embedTypeBody B) (f := embedTerm f) (g := embedTerm g)
            (by simpa only [embedTypeParameter_code] using formationForward da)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open] using formationForward db)
            (by simpa only [embedPi_code] using typingForward df)
            (by simpa only [embedPi_code] using typingForward dg)
            (by simpa only [embedContext, embedTypeParameter_code, embedTypeBody_open,
              bind_projection_embedTerm, embedTerm_app, embedTerm_zero] using termEqualityForward de)
  termination_by structural d
end

end Mettapedia.Languages.Agda.StaticAdequacy
