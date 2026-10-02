import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Judgment

/-!
# The annotated judgment along morphisms of annotated packages

A morphism of annotated packages (`ChurchRules.Morphism`) maps universe heads so that the
universe rules of the source hold in the target, the declared constants keep their names with
their types mapped, the root steps are mapped to root steps, and the premises the target
requires of a mapped step are among the mapped premises the source requires of the step. Every
derivable annotated statement of the source, typing, typed equality or subtyping, is derivable
in the target after its heads are mapped (`CDerivable.mapHead`).

This is the annotated counterpart of `Derivable.mapHead`. Changing heads commutes with renaming,
substitution, opening a binder, lifting a closed term and context lookup.

Positive example: the identity map is a morphism from every package to itself
(`ChurchRules.Morphism.identity`). Negative example: a map of heads that does not preserve the
typing of heads is not a morphism between two packages over rules that separate the images
(`not_morphism_of_headTyping`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {HeadOne HeadTwo : Type}

namespace CTm

/-- Changing heads commutes with renaming. -/
@[simp] theorem mapHead_rename (g : HeadOne → HeadTwo) {n m : Nat} (ρ : Ren n m)
    (t : CTm HeadOne n) : (t.rename ρ).mapHead g = (t.mapHead g).rename ρ := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [rename, mapHead, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, mapHead, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, mapHead, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [rename, mapHead, ihA, ihb]
  | app f a ihf iha => simp only [rename, mapHead, ihf, iha]
  | pair a b iha ihb => simp only [rename, mapHead, iha, ihb]
  | fst p ih => simp only [rename, mapHead, ih]
  | snd p ih => simp only [rename, mapHead, ih]
  | refl a ih => simp only [rename, mapHead, ih]

/-- Changing heads commutes with lifting a substitution under a binder. -/
theorem mapHead_liftSub (g : HeadOne → HeadTwo) {n m : Nat} (σ : CSub HeadOne n m) :
    (fun i => (liftSub σ i).mapHead g) = liftSub (fun i => (σ i).mapHead g) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact mapHead_rename g wk (σ j)

/-- Changing heads commutes with substitution. -/
@[simp] theorem mapHead_subst (g : HeadOne → HeadTwo) {n m : Nat} (σ : CSub HeadOne n m)
    (t : CTm HeadOne n) :
    (t.subst σ).mapHead g = (t.mapHead g).subst (fun i => (σ i).mapHead g) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [subst, mapHead, ihA, ihB, mapHead_liftSub]
  | sigma A B ihA ihB => simp only [subst, mapHead, ihA, ihB, mapHead_liftSub]
  | id A a b ihA iha ihb => simp only [subst, mapHead, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [subst, mapHead, ihA, ihb, mapHead_liftSub]
  | app f a ihf iha => simp only [subst, mapHead, ihf, iha]
  | pair a b iha ihb => simp only [subst, mapHead, iha, ihb]
  | fst p ih => simp only [subst, mapHead, ih]
  | snd p ih => simp only [subst, mapHead, ih]
  | refl a ih => simp only [subst, mapHead, ih]

/-- Changing heads commutes with opening a binder. -/
@[simp] theorem mapHead_inst0 (g : HeadOne → HeadTwo) {n : Nat} (u : CTm HeadOne n)
    (body : CTm HeadOne (n + 1)) :
    (inst0 u body).mapHead g = inst0 (u.mapHead g) (body.mapHead g) := by
  rw [inst0, inst0, mapHead_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Changing heads commutes with lifting a closed term. -/
@[simp] theorem mapHead_liftClosed (g : HeadOne → HeadTwo) {n : Nat} (t : CTm HeadOne 0) :
    (t.liftClosed : CTm HeadOne n).mapHead g = (t.mapHead g).liftClosed :=
  mapHead_rename g Fin.elim0 t

/-- The identity map of heads changes nothing. -/
@[simp] theorem mapHead_id {n : Nat} (t : CTm HeadOne n) : t.mapHead (fun h => h) = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [mapHead, ihA, ihB]
  | sigma A B ihA ihB => simp only [mapHead, ihA, ihB]
  | id A a b ihA iha ihb => simp only [mapHead, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [mapHead, ihA, ihb]
  | app f a ihf iha => simp only [mapHead, ihf, iha]
  | pair a b iha ihb => simp only [mapHead, iha, ihb]
  | fst p ih => simp only [mapHead, ih]
  | snd p ih => simp only [mapHead, ih]
  | refl a ih => simp only [mapHead, ih]

/-- Changing heads twice is changing them once by the composite. -/
theorem mapHead_comp {HeadThree : Type} (g : HeadTwo → HeadThree) (f : HeadOne → HeadTwo)
    {n : Nat} (t : CTm HeadOne n) : (t.mapHead f).mapHead g = t.mapHead (fun h => g (f h)) := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [mapHead, ihA, ihB]
  | sigma A B ihA ihB => simp only [mapHead, ihA, ihB]
  | id A a b ihA iha ihb => simp only [mapHead, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [mapHead, ihA, ihb]
  | app f a ihf iha => simp only [mapHead, ihf, iha]
  | pair a b iha ihb => simp only [mapHead, iha, ihb]
  | fst p ih => simp only [mapHead, ih]
  | snd p ih => simp only [mapHead, ih]
  | refl a ih => simp only [mapHead, ih]

end CTm

namespace CCtx

/-- Change the heads of every type of a context. -/
def mapHead (g : HeadOne → HeadTwo) : {n : Nat} → CCtx HeadOne n → CCtx HeadTwo n
  | _, .nil => .nil
  | _, .snoc Γ A => .snoc (mapHead g Γ) (A.mapHead g)

/-- Context lookup commutes with changing heads. -/
@[simp] theorem lookup_mapHead (g : HeadOne → HeadTwo) {n : Nat} (Γ : CCtx HeadOne n)
    (i : Fin n) : (Γ.mapHead g).lookup i = (Γ.lookup i).mapHead g := by
  induction Γ with
  | nil => exact i.elim0
  | snoc Γ A ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (CTm.mapHead_rename g wk A).symm
    · change ((Γ.mapHead g).lookup j).rename wk = ((Γ.lookup j).rename wk).mapHead g
      rw [ih, CTm.mapHead_rename]

/-- The identity map of heads changes nothing. -/
@[simp] theorem mapHead_id {n : Nat} (Γ : CCtx HeadOne n) : Γ.mapHead (fun h => h) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp only [mapHead, ih, CTm.mapHead_id]

end CCtx

/-- A premise with its heads mapped. -/
def CPremise.mapHead (g : HeadOne → HeadTwo) {n : Nat} : CPremise HeadOne n → CPremise HeadTwo n
  | .typing t T => .typing (t.mapHead g) (T.mapHead g)
  | .equality a b T => .equality (a.mapHead g) (b.mapHead g) (T.mapHead g)

/-- A statement with its heads mapped. -/
def CStatement.mapHead (g : HeadOne → HeadTwo) : CStatement HeadOne → CStatement HeadTwo
  | .typing Γ t A => .typing (Γ.mapHead g) (t.mapHead g) (A.mapHead g)
  | .equality Γ a b A => .equality (Γ.mapHead g) (a.mapHead g) (b.mapHead g) (A.mapHead g)
  | .sub Γ A B => .sub (Γ.mapHead g) (A.mapHead g) (B.mapHead g)

/-- The statement of a mapped premise is the mapped statement of the premise. -/
theorem CPremise.statement_mapHead (g : HeadOne → HeadTwo) {n : Nat} (Γ : CCtx HeadOne n)
    (premise : CPremise HeadOne n) :
    (premise.statement Γ).mapHead g = (premise.mapHead g).statement (Γ.mapHead g) := by
  cases premise <;> rfl

/-- The identity map of heads changes no premise. -/
@[simp] theorem CPremise.mapHead_id {n : Nat} (premise : CPremise HeadOne n) :
    premise.mapHead (fun h => h) = premise := by
  cases premise <;> simp only [CPremise.mapHead, CTm.mapHead_id]

/-- The identity map of heads changes no statement. -/
@[simp] theorem CStatement.mapHead_id (s : CStatement HeadOne) : s.mapHead (fun h => h) = s := by
  cases s <;> simp only [CStatement.mapHead, CTm.mapHead_id, CCtx.mapHead_id]

/-- **A morphism of annotated packages** along a map of heads: the universe rules of the source
hold in the target at the mapped heads, a declared constant is declared with its type mapped, a
root step is mapped to a root step, and every premise the target requires of a mapped step is a
mapped premise the source requires of the step. -/
structure ChurchRules.Morphism {R : Rules HeadOne} {R' : Rules HeadTwo} (P : ChurchRules R)
    (P' : ChurchRules R') (g : HeadOne → HeadTwo) : Prop where
  headTyping : ∀ {h u : HeadOne}, R.headTyping h u → R'.headTyping (g h) (g u)
  isUniverse : ∀ {u : HeadOne}, R.isUniverse u → R'.isUniverse (g u)
  join : ∀ {u v w : HeadOne}, R.join u v w → R'.join (g u) (g v) (g w)
  cumulative : ∀ {u v : HeadOne}, R.cumulative u v → R'.cumulative (g u) (g v)
  headEq : ∀ {h h' : HeadOne}, R.headEq h h' → R'.headEq (g h) (g h')
  constantType : ∀ {c : DeclName} {T : CTm HeadOne 0}, P.constantType c = some T →
    P'.constantType c = some (T.mapHead g)
  computation : ∀ {n : Nat} {l r : CTm HeadOne n}, P.computation.step l r →
    P'.computation.step (l.mapHead g) (r.mapHead g)
  requires : ∀ {n : Nat} {l r : CTm HeadOne n} {premises : List (CPremise HeadOne n)},
    P.computation.step l r → P.computation.requires l r premises →
      ∃ premises', P'.computation.requires (l.mapHead g) (r.mapHead g) premises' ∧
        ∀ premise ∈ premises', ∃ source ∈ premises, premise = source.mapHead g

/-- Every annotated package has its identity morphism. -/
theorem ChurchRules.Morphism.identity {R : Rules HeadOne} (P : ChurchRules R) :
    P.Morphism P (fun h => h) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => by rw [CTm.mapHead_id]; exact declared
  computation := fun step => by rw [CTm.mapHead_id, CTm.mapHead_id]; exact step
  requires := fun {_ _ _ premises} _ required =>
    ⟨premises, by rw [CTm.mapHead_id, CTm.mapHead_id]; exact required,
      fun premise member => ⟨premise, member, (CPremise.mapHead_id premise).symm⟩⟩

/-- **Transport along a morphism of annotated packages.** Every derivable annotated statement
of the source is derivable in the target with its heads mapped. -/
theorem CDerivable.mapHead {R : Rules HeadOne} {R' : Rules HeadTwo} {P : ChurchRules R}
    {P' : ChurchRules R'} {g : HeadOne → HeadTwo} (morphism : P.Morphism P' g)
    {s : CStatement HeadOne} (derivation : CDerivable P s) : CDerivable P' (s.mapHead g) := by
  induction derivation with
  | headType typing => exact .headType (morphism.headTyping typing)
  | @var n Γ i =>
      simp only [CStatement.mapHead, CTm.mapHead]
      rw [← CCtx.lookup_mapHead]
      exact .var i
  | const declared _ hu ihType =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_liftClosed, CCtx.mapHead]
        at ihType ⊢
      exact .const (morphism.constantType declared) ihType (morphism.isUniverse hu)
  | piForm _ hu _ hv join ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihA ihB ⊢
      exact .piForm ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv) (morphism.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihA ihB ⊢
      exact .sigmaForm ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv)
        (morphism.join join)
  | lamIntro _ hw _ hu _ ihA ihPi ihBody =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihA ihPi ihBody ⊢
      exact .lamIntro ihA (morphism.isUniverse hw) ihPi (morphism.isUniverse hu) ihBody
  | appElim _ _ ihF ihA =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ihF ihA ⊢
      exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .pairIntro ihS (morphism.isUniverse hu) ihA ihB
  | fstElim _ ih =>
      simp only [CStatement.mapHead, CTm.mapHead] at ih ⊢
      exact .fstElim ih
  | sndElim _ ih =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ih ⊢
      exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb =>
      simp only [CStatement.mapHead, CTm.mapHead] at ihA iha ihb ⊢
      exact .idForm ihA (morphism.isUniverse hu) iha ihb
  | reflIntro _ ih =>
      simp only [CStatement.mapHead, CTm.mapHead] at ih ⊢
      exact .reflIntro ih
  | sub _ _ ihT ihLe =>
      simp only [CStatement.mapHead] at ihT ihLe ⊢
      exact .sub ihT ihLe
  | conv _ _ hu ihT ihE =>
      simp only [CStatement.mapHead, CTm.mapHead] at ihT ihE ⊢
      exact .conv ihT ihE (morphism.isUniverse hu)
  | refl _ ih =>
      simp only [CStatement.mapHead] at ih ⊢
      exact .refl ih
  | symm _ ih =>
      simp only [CStatement.mapHead] at ih ⊢
      exact .symm ih
  | trans _ _ ih₁ ih₂ =>
      simp only [CStatement.mapHead] at ih₁ ih₂ ⊢
      exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihT =>
      simp only [CStatement.mapHead, CTm.mapHead] at ih ihT ⊢
      exact .convEq ih ihT (morphism.isUniverse hu)
  | subEq _ _ ihE ihLe =>
      simp only [CStatement.mapHead] at ihE ihLe ⊢
      exact .subEq ihE ihLe
  | headEq same _ _ ih ih' =>
      simp only [CStatement.mapHead, CTm.mapHead] at ih ih' ⊢
      exact .headEq (morphism.headEq same) ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihA ihB ⊢
      exact .piCong ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv) (morphism.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihA ihB ⊢
      exact .sigmaCong ihA (morphism.isUniverse hu) ihB (morphism.isUniverse hv)
        (morphism.join join)
  | idCong _ hu _ _ ihA iha ihb =>
      simp only [CStatement.mapHead, CTm.mapHead] at ihA iha ihb ⊢
      exact .idCong ihA (morphism.isUniverse hu) iha ihb
  | lamCong _ hw _ hu _ ihA ihPi ihBody =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihA ihPi ihBody ⊢
      exact .lamCong ihA (morphism.isUniverse hw) ihPi (morphism.isUniverse hu) ihBody
  | appCong _ _ ihF ihA =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ihF ihA ⊢
      exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .pairCong ihS (morphism.isUniverse hu) ihA ihB
  | fstCong _ ih =>
      simp only [CStatement.mapHead, CTm.mapHead] at ih ⊢
      exact .fstCong ih
  | sndCong _ ih =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ih ⊢
      exact .sndCong ih
  | reflCong _ ih =>
      simp only [CStatement.mapHead, CTm.mapHead] at ih ⊢
      exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody ihA =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0, CCtx.mapHead]
        at ihPi ihBody ihA ⊢
      exact .betaPi ihPi (morphism.isUniverse hu) ihBody ihA
  | betaFst _ hu _ _ ihS ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .betaFst ihS (morphism.isUniverse hu) ihA ihB
  | betaSnd _ hu _ _ ihS ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ihS ihA ihB ⊢
      exact .betaSnd ihS (morphism.isUniverse hu) ihA ihB
  | root step required _ _ _ ihPremises ihL ihR =>
      obtain ⟨premises', required', among⟩ := morphism.requires step required
      simp only [CStatement.mapHead] at ihL ihR ⊢
      refine .root (morphism.computation step) required' (fun premise member => ?_) ihL ihR
      obtain ⟨source, memberSource, rfl⟩ := among premise member
      have mapped := ihPremises source memberSource
      rwa [CPremise.statement_mapHead] at mapped
  | etaPi _ _ _ ihF ihG ihApps =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_rename, CCtx.mapHead]
        at ihF ihG ihApps ⊢
      exact .etaPi ihF ihG ihApps
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      simp only [CStatement.mapHead, CTm.mapHead, CTm.mapHead_inst0] at ihP ihQ ihFst ihSnd ⊢
      exact .etaSigma ihP ihQ ihFst ihSnd
  | subEqual _ hu ih =>
      simp only [CStatement.mapHead, CTm.mapHead] at ih ⊢
      exact .subEqual ih (morphism.isUniverse hu)
  | subUniv c =>
      simp only [CStatement.mapHead, CTm.mapHead]
      exact .subUniv (morphism.cumulative c)
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihPi ihPi' ihA ihB ⊢
      exact .subPi ihPi (morphism.isUniverse hu) ihPi' (morphism.isUniverse hu') ihA
        (morphism.isUniverse hw) ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      simp only [CStatement.mapHead, CTm.mapHead, CCtx.mapHead] at ihS ihS' ihA ihB ⊢
      exact .subSigma ihS (morphism.isUniverse hu) ihS' (morphism.isUniverse hu') ihA ihB
  | subTrans _ _ ih₁ ih₂ =>
      simp only [CStatement.mapHead] at ih₁ ih₂ ⊢
      exact .subTrans ih₁ ih₂

/-- Along a morphism with the identity map of heads, statements are unchanged. -/
theorem CDerivable.of_morphism {R R' : Rules HeadOne} {P : ChurchRules R} {P' : ChurchRules R'}
    (morphism : P.Morphism P' (fun h => h)) {s : CStatement HeadOne}
    (derivation : CDerivable P s) : CDerivable P' s := by
  have mapped := derivation.mapHead morphism
  rwa [CStatement.mapHead_id] at mapped

/-- **A map of heads that does not preserve the typing of heads is not a morphism**: if a head
is typed in the source and its image is not typed at the image in the target, no morphism of
annotated packages goes along the map. -/
theorem not_morphism_of_headTyping {R : Rules HeadOne} {R' : Rules HeadTwo} {P : ChurchRules R}
    {P' : ChurchRules R'} {g : HeadOne → HeadTwo} {h u : HeadOne} (typed : R.headTyping h u)
    (untyped : ¬ R'.headTyping (g h) (g u)) : ¬ P.Morphism P' g :=
  fun morphism => untyped (morphism.headTyping typed)

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
