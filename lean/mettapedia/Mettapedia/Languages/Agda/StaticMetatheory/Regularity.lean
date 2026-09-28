import Mettapedia.Languages.Agda.StaticSpecification.Eta

/-!
Derived regularity for the frozen finite-Set, relevant-Pi reference calculus.
The rule references are those in `StaticSpecification.Judgments`: Cockx's
Agda Core at `2fb9574e78326ec532dcb2af8272631c765e947d`, the Pi fragment of
`logrel-mltt` at `9d6e290064962a1987c9e1a131c2fb967d6ef928`, and Agda's typed
function comparison at `cccf42fa88eae25ccbe2623f489021d2075f6f73`.
The only typing and conversion constructors used here are those of that source
calculus. Substitution functionality first derives lambda congruence from typed
eta and beta, then lifts equal substitutions over the left substituted domain.
Endpoint regularity can consequently use dependent result-type transport without
adding it as an inference rule or assuming the desired endpoint derivations.

This module does not extend the frozen source language to administrative spines.
Context conversion and equal substitutions retain their supplied derivation
trees; no quotient of raw syntax or equality of evidence compositions is asserted.
-/

namespace Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.StaticSpecification

/-- Identity on raw terms, with an actual conversion at the changed declaration. -/
def changeLastSub {Γ : RawContext n} {A B : Ty n}
    (formedA : FormTy Γ A) (formedB : FormTy Γ B) (eq : TypeEq Γ A B) :
    SubDeriv (Γ.snoc A) (Γ.snoc B) Term.var where
  source := .snoc formedA.context formedA
  target := .snoc formedB.context formedB
  lookup := fun i => Fin.cases
    (by simpa only [RawContext.lookup_zero, Ty.subst_id] using
      (Typing.conv (Typing.var 0 (FormCtx.snoc formedB.context formedB))
        (eq.symm.weaken formedB)))
    (fun j : Fin n => by
      simpa only [RawContext.lookup_succ, Ty.subst_id] using
        (Typing.var j.succ (FormCtx.snoc formedB.context formedB))) i

def changeLastFormation {Γ : RawContext n} {A B : Ty n} {C : Ty (n + 1)}
    (formedA : FormTy Γ A) (formedB : FormTy Γ B) (eq : TypeEq Γ A B)
    (d : FormTy (Γ.snoc A) C) : FormTy (Γ.snoc B) C := by
  simpa only [Ty.subst_id] using d.substitute (changeLastSub formedA formedB eq)

def changeLastTyping {Γ : RawContext n} {A B : Ty n} {t : Term (n + 1)} {C : Ty (n + 1)}
    (formedA : FormTy Γ A) (formedB : FormTy Γ B) (eq : TypeEq Γ A B)
    (d : Typing (Γ.snoc A) t C) : Typing (Γ.snoc B) t C := by
  simpa only [Ty.subst_id, Term.subst_id] using d.substitute (changeLastSub formedA formedB eq)

theorem instantiate_weaken_var (body : Abs n) :
    (body.rename Fin.succ).instantiate (.var 0) = body.open := by
  simp only [Abs.instantiate, Abs.open_rename, Term.rename_lift_single_var]

/-- Pointwise beta for an arbitrary well-typed binding or nonbinding lambda. -/
def betaAtNewest {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {body : Abs n}
    (domain : FormTy Γ A) (codomain : FormTy (Γ.snoc A) B.open)
    (typed : Typing (Γ.snoc A) body.open B.open) :
    TermEq (Γ.snoc A) ((Term.lam body).weaken.app (.var 0)) body.open B.open := by
  have formed := FormCtx.snoc domain.context domain
  have da := domain.weaken domain
  have lifted := (Renaming.respects_weaken Γ A).lift A
  have db := codomain.rename (Renaming.lift Fin.succ) lifted (.snoc formed da)
  have dt := typed.rename (Renaming.lift Fin.succ) lifted (.snoc formed da)
  have dx := Typing.var 0 formed
  have beta := TermEq.beta (a := A.weaken) (b := B.rename Fin.succ)
    (body := body.rename Fin.succ) da
    (by simpa only [TyAbs.open_rename, Ty.weaken] using db)
    (by simpa only [Abs.open_rename, TyAbs.open_rename, Ty.weaken] using dt) dx
  simpa only [instantiate_weaken_var, TyAbs.instantiate_weaken_var,
    Term.weaken, Term.rename] using beta

/-- Lambda congruence is derived, with both body typing trees supplied explicitly. -/
def lambdaCong {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {left right : Abs n}
    (domain : FormTy Γ A) (codomain : FormTy (Γ.snoc A) B.open)
    (leftTyped : Typing (Γ.snoc A) left.open B.open)
    (rightTyped : Typing (Γ.snoc A) right.open B.open)
    (bodies : TermEq (Γ.snoc A) left.open right.open B.open) :
    TermEq Γ (.lam left) (.lam right) (Ty.pi A B) :=
  .eta domain codomain (.lam domain codomain leftTyped) (.lam domain codomain rightTyped)
    (.trans (betaAtNewest domain codomain leftTyped)
      (.trans bodies (.symm (betaAtNewest domain codomain rightTyped))))

/-- Actual substitutions and pointwise equality at the left substituted type. -/
structure EqualSubstitution (Γ : RawContext n) (Δ : RawContext m)
    (σ τ : Substitution n m) where
  left : SubDeriv Γ Δ σ
  right : SubDeriv Γ Δ τ
  equal : (i : Fin n) → TermEq Δ (σ i) (τ i) ((Γ.lookup i).subst σ)

/-- The right lift uses domain conversion, in the left extended target context. -/
def EqualSubstitution.lift {Γ : RawContext n} {Δ : RawContext m} {σ τ : Substitution n m}
    (d : EqualSubstitution Γ Δ σ τ) {A : Ty n} (domain : FormTy Γ A)
    (domainEq : TypeEq Δ (A.subst σ) (A.subst τ)) :
    EqualSubstitution (Γ.snoc A) (Δ.snoc (A.subst σ))
      (Substitution.lift σ) (Substitution.lift τ) where
  left := d.left.lift domain (domain.substitute d.left)
  right := {
    source := .snoc d.right.source domain
    target := .snoc d.right.target (domain.substitute d.left)
    lookup := fun i => Fin.cases
      (by simpa only [Substitution.lift_zero, RawContext.lookup_zero, Ty.subst_weaken] using
        (Typing.conv (Typing.var 0 (FormCtx.snoc d.right.target (domain.substitute d.left)))
          (domainEq.weaken (domain.substitute d.left))))
      (fun j => by simpa only [Substitution.lift_succ, RawContext.lookup_succ,
        Ty.subst_weaken] using (d.right.lookup j).weaken (domain.substitute d.left)) i }
  equal := fun i => Fin.cases
    (by simpa only [Substitution.lift_zero, RawContext.lookup_zero, Ty.subst_weaken] using
      TermEq.refl (Typing.var 0 (FormCtx.snoc d.left.target (domain.substitute d.left))))
    (fun j => by simpa only [Substitution.lift_succ, RawContext.lookup_succ,
      Ty.subst_weaken] using (d.equal j).weaken (domain.substitute d.left)) i

mutual
  def formationFunctionality {Γ : RawContext n} {A : Ty n} (formed : FormTy Γ A)
      {Δ : RawContext m} {σ τ : Substitution n m} (d : EqualSubstitution Γ Δ σ τ) :
      TypeEq Δ (A.subst σ) (A.subst τ) :=
    match formed with
    | .ofTyping typed => .atSort (typingFunctionality typed d)
  termination_by structural formed

  def typingFunctionality {Γ : RawContext n} {t : Term n} {A : Ty n} (typed : Typing Γ t A)
      {Δ : RawContext m} {σ τ : Substitution n m} (d : EqualSubstitution Γ Δ σ τ) :
      TermEq Δ (t.subst σ) (t.subst τ) (A.subst σ) :=
    match typed with
    | .sort k _ => .refl (.sort k d.left.target)
    | .var i _ => d.equal i
    | .pi (a := A) (b := B) domain codomain => by
        have domainEq := formationFunctionality domain d
        have codomainEq := formationFunctionality codomain (d.lift domain domainEq)
        simpa only [Term.subst, Ty.universe_subst, Ty.level_subst, TyAbs.level_subst] using
          TermEq.piCong (b := B.subst σ) (b' := B.subst τ) (domain.substitute d.left) domainEq
            (by simpa only [TyAbs.open_subst] using codomainEq)
    | .lam (a := A) (b := B) (body := body) domain codomain bodyTyped => by
        have domainEq := formationFunctionality domain d
        have lifted := d.lift domain domainEq
        have codomainEq := formationFunctionality codomain lifted
        have bodyEq := typingFunctionality bodyTyped lifted
        have bodyLeft := bodyTyped.substitute lifted.left
        have bodyRight := Typing.conv (bodyTyped.substitute lifted.right) codomainEq.symm
        simpa only [Term.subst, Ty.pi_subst] using
          lambdaCong (A := A.subst σ) (B := B.subst σ)
            (left := body.subst σ) (right := body.subst τ)
            (domain.substitute d.left)
            (by simpa only [TyAbs.open_subst] using codomain.substitute lifted.left)
            (by simpa only [Abs.open_subst, TyAbs.open_subst] using bodyLeft)
            (by simpa only [Abs.open_subst, TyAbs.open_subst] using bodyRight)
            (by simpa only [Abs.open_subst, TyAbs.open_subst] using bodyEq)
    | .app (b := B) function argument => by
        have functions := typingFunctionality function d
        have arguments := typingFunctionality argument d
        simpa only [Term.app_subst, TyAbs.instantiate_subst] using
          TermEq.appCong (b := B.subst σ)
            (by simpa only [Ty.pi_subst] using functions) arguments
    | .conv term eq => .conv (typingFunctionality term d) (eq.substitute d.left)
  termination_by structural typed
end

def EqualSubstitution.single {Γ : RawContext n} {A : Ty n} {u v : Term n}
    (domain : FormTy Γ A) (left : Typing Γ u A) (right : Typing Γ v A) (eq : TermEq Γ u v A) :
    EqualSubstitution (Γ.snoc A) Γ (Substitution.single u) (Substitution.single v) where
  left := SubDeriv.single domain left
  right := SubDeriv.single domain right
  equal := fun i => Fin.cases
    (by simpa only [Substitution.single_zero, RawContext.lookup_zero,
      Ty.subst_single_weaken] using eq)
    (fun j => by simpa only [Substitution.single_succ, RawContext.lookup_succ,
      Ty.subst_single_weaken] using TermEq.refl (Typing.var j domain.context)) i

/-- The dependent result type transport needed by application congruence. -/
def instantiateCongruence {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {u v : Term n}
    (domain : FormTy Γ A) (codomain : FormTy (Γ.snoc A) B.open)
    (left : Typing Γ u A) (right : Typing Γ v A) (eq : TermEq Γ u v A) :
    TypeEq Γ (B.instantiate u) (B.instantiate v) :=
  formationFunctionality codomain (EqualSubstitution.single domain left right eq)

/-- Formation data for a syntactic Pi can be recovered through conversions. -/
def typingPiParts {Γ : RawContext n} {A : Ty n} {B : TyAbs n} {C : Ty n}
    (d : Typing Γ (.pi A B) C) : FormTy Γ A × FormTy (Γ.snoc A) B.open := by
  cases d with
  | pi domain codomain => exact ⟨domain, codomain⟩
  | conv typed _ => exact typingPiParts typed
termination_by sizeOf d

def formationPiParts {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    (d : FormTy Γ (Ty.pi A B)) : FormTy Γ A × FormTy (Γ.snoc A) B.open := by
  cases d with
  | ofTyping typed => exact typingPiParts typed

/-- Both formation trees are retained, rather than their inhabitedness alone. -/
structure TypeEndpoints (Γ : RawContext n) (A B : Ty n) where
  left : FormTy Γ A
  right : FormTy Γ B

/-- The common type formation is retained with both endpoint typing trees. -/
structure TermEndpoints (Γ : RawContext n) (t u : Term n) (A : Ty n) where
  left : Typing Γ t A
  right : Typing Γ u A
  formed : FormTy Γ A

mutual
  def typingFormation {Γ : RawContext n} {t : Term n} {A : Ty n}
      (d : Typing Γ t A) : FormTy Γ A :=
    match d with
    | .sort k formed => .universe formed (k + 1)
    | .var i formed => formed.lookup i
    | .pi (a := A) (b := B) domain _ =>
        .universe domain.context (max A.level B.level)
    | .lam domain codomain _ => .pi domain codomain
    | .app function argument =>
        let parts := formationPiParts (typingFormation function)
        parts.2.substitute (SubDeriv.single parts.1 argument)
    | .conv _ eq => (typeEndpoints eq).right
  termination_by structural d

  def typeEndpoints {Γ : RawContext n} {A B : Ty n}
      (d : TypeEq Γ A B) : TypeEndpoints Γ A B :=
    match d with
    | .atSort eq =>
        let endpoints := termEndpoints eq
        ⟨.ofTyping endpoints.left, .ofTyping endpoints.right⟩
  termination_by structural d

  def termEndpoints {Γ : RawContext n} {t u : Term n} {A : Ty n}
      (d : TermEq Γ t u A) : TermEndpoints Γ t u A :=
    match d with
    | .refl typed => ⟨typed, typed, typingFormation typed⟩
    | .symm eq =>
        let endpoints := termEndpoints eq
        ⟨endpoints.right, endpoints.left, endpoints.formed⟩
    | .trans first second =>
        let left := termEndpoints first
        let right := termEndpoints second
        ⟨left.left, right.right, left.formed⟩
    | .conv eq typeEq =>
        let terms := termEndpoints eq
        let types := typeEndpoints typeEq
        ⟨.conv terms.left typeEq, .conv terms.right typeEq, types.right⟩
    | .piCong (a := A) (a' := A') (b := B) (b' := B') domain domainEq codomainEq => by
        have domains := typeEndpoints domainEq
        have codomains := typeEndpoints codomainEq
        have rightCodomain := changeLastFormation domain domains.right domainEq codomains.right
        have domainLevels := domainEq.level_eq
        have codomainLevels : B.level = B'.level := by
          simpa only [TyAbs.level_open] using codomainEq.level_eq
        exact ⟨.pi domain codomains.left,
          by simpa only [← domainLevels, ← codomainLevels] using
            (Typing.pi domains.right rightCodomain),
          .universe domain.context (max A.level B.level)⟩
    | .appCong functions arguments =>
        let rf := termEndpoints functions
        let ru := termEndpoints arguments
        let parts := formationPiParts rf.formed
        let results := instantiateCongruence parts.1 parts.2 ru.left ru.right arguments
        ⟨.app rf.left ru.left, .conv (.app rf.right ru.right) results.symm,
          parts.2.substitute (SubDeriv.single parts.1 ru.left)⟩
    | .beta domain codomain body argument =>
        ⟨.app (.lam domain codomain body) argument, body.instantiate domain argument,
          codomain.substitute (SubDeriv.single domain argument)⟩
    | .eta domain codomain left right _ => ⟨left, right, .pi domain codomain⟩
  termination_by structural d
end

/-- The source equality and the pointwise substitution equality are both used. -/
def typeEqualityFunctionality {Γ : RawContext n} {A B : Ty n}
    (eq : TypeEq Γ A B) {Δ : RawContext m} {σ τ : Substitution n m}
    (substitutions : EqualSubstitution Γ Δ σ τ) :
    TypeEq Δ (A.subst σ) (B.subst τ) :=
  (eq.substitute substitutions.left).trans
    (formationFunctionality (typeEndpoints eq).right substitutions)

def termEqualityFunctionality {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (eq : TermEq Γ t u A) {Δ : RawContext m} {σ τ : Substitution n m}
    (substitutions : EqualSubstitution Γ Δ σ τ) :
    TermEq Δ (t.subst σ) (u.subst τ) (A.subst σ) :=
  .trans (eq.substitute substitutions.left)
    (typingFunctionality (termEndpoints eq).right substitutions)

/-- Compare each declaration over the source prefix; no syntax is quotiented. -/
inductive ContextConversion : {n : Nat} → RawContext n → RawContext n → Type
  | nil : ContextConversion .nil .nil
  | snoc {Γ Δ : RawContext n} {A B : Ty n} :
      ContextConversion Γ Δ → TypeEq Γ A B →
      ContextConversion (Γ.snoc A) (Δ.snoc B)

/-- Identity raw substitution with a derived typing tree at every declaration. -/
def ContextConversion.identitySub {Γ Δ : RawContext n}
    (d : ContextConversion Γ Δ) : SubDeriv Γ Δ Term.var :=
  match d with
  | .nil => SubDeriv.identity .nil
  | .snoc previous eq => by
      have sub := previous.identitySub
      have ends := typeEndpoints eq
      have targetDomain := ends.right.substitute sub
      simp only [Ty.subst_id] at targetDomain
      have targetEq := eq.substitute sub
      simp only [Ty.subst_id] at targetEq
      let target := FormCtx.snoc sub.target targetDomain
      exact {
        source := .snoc sub.source ends.left
        target := target
        lookup := fun i => Fin.cases
          (by simpa only [RawContext.lookup_zero, Ty.subst_id] using
            (Typing.conv (Typing.var 0 target) (targetEq.symm.weaken targetDomain)))
          (fun j => by
            simpa only [RawContext.lookup_succ, Ty.subst_id, Term.weaken, Term.rename] using
              ((sub.lookup j).weaken targetDomain)) i }
termination_by structural d

def ContextConversion.formation {Γ Δ : RawContext n} (d : ContextConversion Γ Δ)
    {A : Ty n} (formed : FormTy Γ A) : FormTy Δ A := by
  simpa only [Ty.subst_id] using formed.substitute d.identitySub

def ContextConversion.typing {Γ Δ : RawContext n} (d : ContextConversion Γ Δ)
    {t : Term n} {A : Ty n} (typed : Typing Γ t A) : Typing Δ t A := by
  simpa only [Term.subst_id, Ty.subst_id] using typed.substitute d.identitySub

def ContextConversion.typeEquality {Γ Δ : RawContext n} (d : ContextConversion Γ Δ)
    {A B : Ty n} (eq : TypeEq Γ A B) : TypeEq Δ A B := by
  simpa only [Ty.subst_id] using eq.substitute d.identitySub

def ContextConversion.termEquality {Γ Δ : RawContext n} (d : ContextConversion Γ Δ)
    {t u : Term n} {A : Ty n} (eq : TermEq Γ t u A) : TermEq Δ t u A := by
  simpa only [Term.subst_id, Ty.subst_id] using eq.substitute d.identitySub

def ContextConversion.refl {Γ : RawContext n} (formed : FormCtx Γ) :
    ContextConversion Γ Γ :=
  match formed with
  | .nil => .nil
  | .snoc previous domain => .snoc (.refl previous) (.refl domain)
termination_by structural formed

def ContextConversion.symm {Γ Δ : RawContext n} (d : ContextConversion Γ Δ) :
    ContextConversion Δ Γ :=
  match d with
  | .nil => .nil
  | .snoc previous eq => .snoc previous.symm (previous.typeEquality eq).symm
termination_by structural d

def ContextConversion.trans {Γ Δ Θ : RawContext n} (d : ContextConversion Γ Δ)
    (e : ContextConversion Δ Θ) : ContextConversion Γ Θ :=
  match d, e with
  | .nil, .nil => .nil
  | .snoc previous eq, .snoc next nextEq =>
      .snoc (previous.trans next) (eq.trans (previous.symm.typeEquality nextEq))
termination_by structural d

end Mettapedia.Languages.Agda.StaticMetatheory
