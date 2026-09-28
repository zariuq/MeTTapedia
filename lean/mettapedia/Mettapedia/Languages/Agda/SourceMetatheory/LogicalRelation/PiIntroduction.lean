import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PiApplicationEquality

/-!
Semantic lambda introduction and function extensionality. The lambda proof
uses source beta contractions after actual formed worlds. Extensionality
recovers the source eta premise at a fresh variable, then retains its source
equality evidence together with the all-world semantic comparisons.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

def typedBetaAt {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {body : Abs n}
    (domain : FormTy Γ A) (codomain : FormTy (Γ.snoc A) B.open)
    (typedBody : Typing (Γ.snoc A) body.open B.open)
    {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ) {a : Term m}
    (argument : Typing Δ a (A.rename ρ)) :
    TypedRed Δ ((Term.lam (body.rename ρ)).app a) ((body.rename ρ).instantiate a)
      ((B.rename ρ).instantiate a) := by
  have newDomain := domain.rename ρ world.respects world.targetFormed
  let lifted := world.lift domain
  have newCodomain := codomain.rename (Renaming.lift ρ) lifted.respects lifted.targetFormed
  have newBody := typedBody.rename (Renaming.lift ρ) lifted.respects lifted.targetFormed
  have step := TypedStep.beta (body := body.rename ρ) (B := B.rename ρ) newDomain
    (by simpa only [TyAbs.open_rename] using newCodomain)
    (by simpa only [Abs.open_rename, TyAbs.open_rename] using newBody) argument
  exact .step step (.refl step.endpoints.right)

theorem piLambda {bound : Nat} {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {family : PiFamily Γ A B} {body : Abs n}
    (domain : FormTy Γ A) (codomain : FormTy (Γ.snoc A) B.open)
    (typedBody : Typing (Γ.snoc A) body.open B.open)
    (domains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ),
      LogRel bound Δ (A.rename ρ) (family.domain world))
    (codomains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (argument : (family.domain world).redTm a),
      LogRel bound Δ ((B.rename ρ).instantiate a) (family.codomain world argument))
    (bodyMembers : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (argument : (family.domain world).redTm a),
      (family.codomain world argument).redTm ((body.rename ρ).instantiate a))
    (bodyEqualities : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a b : Term m} (left : (family.domain world).redTm a) (_right : (family.domain world).redTm b),
      (family.domain world).eqTm a b →
      (family.codomain world left).eqTm ((body.rename ρ).instantiate a) ((body.rename ρ).instantiate b)) :
    PiRedTm family (.lam body) := by
  refine ⟨.lam body, ⟨.refl (.lam domain codomain typedBody)⟩, ⟨.lam body⟩, ?_, ?_⟩
  · intro m Δ ρ world a argument
    obtain ⟨argumentTyped⟩ := (domains world).escape.typing argument
    exact (codomains world argument).expandTerm
      (typedBetaAt domain codomain typedBody world argumentTyped) (bodyMembers world argument)
  · intro m Δ ρ world a b left right comparison
    obtain ⟨leftTyped⟩ := (domains world).escape.typing left
    obtain ⟨rightTyped⟩ := (domains world).escape.typing right
    obtain ⟨resultEqual⟩ := (codomains world left).escape.typeEquality
      (family.extension world left right comparison)
    exact (codomains world left).expandTermEquality
      (typedBetaAt domain codomain typedBody world leftTyped)
      (typedRedConvert (typedBetaAt domain codomain typedBody world rightTyped) resultEqual.symm)
      (bodyEqualities world left right comparison)

theorem piFunctionExtensionality {bound : Nat} {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {family : PiFamily Γ A B} (domain : FormTy Γ A) (codomain : FormTy (Γ.snoc A) B.open)
    (domains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ),
      LogRel bound Δ (A.rename ρ) (family.domain world))
    (codomains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (argument : (family.domain world).redTm a),
      LogRel bound Δ ((B.rename ρ).instantiate a) (family.codomain world argument))
    {f g : Term n} (left : PiRedTm family f) (right : PiRedTm family g)
    (applications : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (argument : (family.domain world).redTm a),
      (family.codomain world argument).eqTm ((f.rename ρ).app a) ((g.rename ρ).app a)) :
    (piPack Γ A B family).eqTm f g := by
  let freshWorld := World.weaken domain
  have freshTyped : Typing (Γ.snoc A) (.var 0) (A.rename Fin.succ) :=
    .var 0 (.snoc domain.context domain)
  have freshMember := (domains freshWorld).neutralReflection.term (.var 0) freshTyped
  obtain ⟨pointwise⟩ := (codomains freshWorld freshMember).escape.termEquality
    (applications freshWorld freshMember)
  have etaPremise : TermEq (Γ.snoc A) (f.weaken.app (.var 0)) (g.weaken.app (.var 0)) B.open := by
    simpa only [TyAbs.instantiate_weaken_var, Term.weaken] using pointwise
  have leftCopy := left
  have rightCopy := right
  obtain ⟨_, ⟨leftPath⟩, _⟩ := leftCopy
  obtain ⟨_, ⟨rightPath⟩, _⟩ := rightCopy
  have sourceEqual := TermEq.eta domain codomain leftPath.endpoints.left rightPath.endpoints.left etaPremise
  exact ⟨left, right, f, g, ⟨.refl leftPath.endpoints.left⟩, ⟨.refl rightPath.endpoints.left⟩,
    ⟨sourceEqual⟩, applications⟩

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
