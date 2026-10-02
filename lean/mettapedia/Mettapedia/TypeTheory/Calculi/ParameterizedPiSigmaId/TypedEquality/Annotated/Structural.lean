import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Judgment

/-!
# Structural metatheory of the annotated judgment

The annotated judgment is stable under renaming along compatible contexts and
under substitution by typed substitutions; a typed term substituted by two
pointwise equal substitutions gives equal terms (functionality). Each is one
induction over derivations, as for `Derivable` (`TypedEquality.Structural`,
`TypedEquality.Functionality`).

Functionality is where the annotations show: an abstraction substituted by two
equal substitutions has two substituted domains, which `lamCong` compares, and
the induction compares them through the domain's own formation premise of
`lamIntro`.

Generation: a typing ends with the rule of the term's former followed by
conversions and subtyping steps (`CTypeLe`), and `CGenerationAt` states what the
rule of each former needs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type} {R : Rules Head}

/-! ## Renaming -/

/-- What renaming along a compatible context map gives for a statement. -/
abbrev CStatement.Renames (P : ChurchRules R) : CStatement Head → Prop
  | .typing Γ t A => ∀ {m : Nat} {Δ : CCtx Head m} {ρ : Ren _ m},
      CCtxRen Γ Δ ρ → CTyped P Δ (t.rename ρ) (A.rename ρ)
  | .equality Γ a b A => ∀ {m : Nat} {Δ : CCtx Head m} {ρ : Ren _ m},
      CCtxRen Γ Δ ρ → CEqual P Δ (a.rename ρ) (b.rename ρ) (A.rename ρ)
  | .sub Γ A B => ∀ {m : Nat} {Δ : CCtx Head m} {ρ : Ren _ m},
      CCtxRen Γ Δ ρ → CBelow P Δ (A.rename ρ) (B.rename ρ)

/-- What renaming gives for the statement of a premise is the statement of the renamed
premise. -/
theorem CPremise.renames {P : ChurchRules R} {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m}
    {ρ : Ren n m} {premise : CPremise Head n} (renames : (premise.statement Γ).Renames P)
    (c : CCtxRen Γ Δ ρ) : CDerivable P ((premise.rename ρ).statement Δ) := by
  cases premise with
  | typing t T => exact renames c
  | equality a b T => exact renames c

theorem CDerivable.renames {P : ChurchRules R} {statement : CStatement Head}
    (derivation : CDerivable P statement) : statement.Renames P := by
  induction derivation with
  | headType h => exact fun _ => .headType h
  | var i =>
      intro m Δ ρ c
      show CTyped P Δ (.var (ρ i)) _
      rw [← c i]
      exact .var _
  | const declared formed hu _ =>
      intro m Δ ρ c
      simpa only [CTm.rename, CTm.rename_liftClosed] using
        (CDerivable.const (Γ := Δ) declared formed hu)
  | piForm _ hu _ hv join ihA ihB => exact fun c => .piForm (ihA c) hu (ihB (c.snoc _)) hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      exact fun c => .sigmaForm (ihA c) hu (ihB (c.snoc _)) hv join
  | lamIntro _ hw _ hu _ ihA ihPi ihBody =>
      exact fun c => .lamIntro (ihA c) hw (ihPi c) hu (ihBody (c.snoc _))
  | appElim _ _ ihF ihA =>
      intro m Δ ρ c
      simpa only [CTm.rename, CTm.rename_inst0] using CDerivable.appElim (ihF c) (ihA c)
  | pairIntro _ hu _ _ ihS iha ihb =>
      intro m Δ ρ c
      have second := ihb c
      rw [CTm.rename_inst0] at second
      exact .pairIntro (ihS c) hu (iha c) second
  | fstElim _ ih => exact fun c => .fstElim (ih c)
  | sndElim _ ih =>
      intro m Δ ρ c
      simpa only [CTm.rename, CTm.rename_inst0] using CDerivable.sndElim (ih c)
  | idForm _ hu _ _ ihA iha ihb => exact fun c => .idForm (ihA c) hu (iha c) (ihb c)
  | reflIntro _ ih => exact fun c => .reflIntro (ih c)
  | sub _ _ ihT ihLe => exact fun c => .sub (ihT c) (ihLe c)
  | conv _ _ hu ihT ihE => exact fun c => .conv (ihT c) (ihE c) hu
  | refl _ ih => exact fun c => .refl (ih c)
  | symm _ ih => exact fun c => .symm (ih c)
  | trans _ _ ih₁ ih₂ => exact fun c => .trans (ih₁ c) (ih₂ c)
  | convEq _ _ hu ih ihE => exact fun c => .convEq (ih c) (ihE c) hu
  | subEq _ _ ih ihLe => exact fun c => .subEq (ih c) (ihLe c)
  | headEq e _ _ ih ih' => exact fun c => .headEq e (ih c) (ih' c)
  | piCong _ hu _ hv join ihA ihB => exact fun c => .piCong (ihA c) hu (ihB (c.snoc _)) hv join
  | sigmaCong _ hu _ hv join ihA ihB =>
      exact fun c => .sigmaCong (ihA c) hu (ihB (c.snoc _)) hv join
  | idCong _ hu _ _ ihA iha ihb => exact fun c => .idCong (ihA c) hu (iha c) (ihb c)
  | lamCong _ hw _ hu _ ihA ihPi ihBody =>
      exact fun c => .lamCong (ihA c) hw (ihPi c) hu (ihBody (c.snoc _))
  | appCong _ _ ihF ihA =>
      intro m Δ ρ c
      simpa only [CTm.rename, CTm.rename_inst0] using CDerivable.appCong (ihF c) (ihA c)
  | pairCong _ hu _ _ ihS iha ihb =>
      intro m Δ ρ c
      have second := ihb c
      rw [CTm.rename_inst0] at second
      exact .pairCong (ihS c) hu (iha c) second
  | fstCong _ ih => exact fun c => .fstCong (ih c)
  | sndCong _ ih =>
      intro m Δ ρ c
      simpa only [CTm.rename, CTm.rename_inst0] using CDerivable.sndCong (ih c)
  | reflCong _ ih => exact fun c => .reflCong (ih c)
  | betaPi _ hu _ _ ihPi ihBody iha =>
      intro m Δ ρ c
      simpa only [CTm.rename, CTm.rename_inst0] using
        CDerivable.betaPi (ihPi c) hu (ihBody (c.snoc _)) (iha c)
  | betaFst _ hu _ _ ihS iha ihb =>
      intro m Δ ρ c
      have second := ihb c
      rw [CTm.rename_inst0] at second
      exact .betaFst (ihS c) hu (iha c) second
  | betaSnd _ hu _ _ ihS iha ihb =>
      intro m Δ ρ c
      have second := ihb c
      rw [CTm.rename_inst0] at second
      simpa only [CTm.rename, CTm.rename_inst0] using
        CDerivable.betaSnd (ihS c) hu (iha c) second
  | root step requires _ _ _ ihPremises ihL ihR =>
      exact fun c => .root (P.computation.rename _ step)
        (P.computation.requires_rename _ requires)
        (fun premise member => by
          obtain ⟨source, mem, rfl⟩ := List.mem_map.1 member
          exact CPremise.renames (ihPremises source mem) c)
        (ihL c) (ihR c)
  | etaPi _ _ _ ihF ihG ihBody =>
      intro m Δ ρ c
      have body := ihBody (c.snoc _)
      simp only [CTm.rename, CTm.rename_liftRen_wk] at body
      exact .etaPi (ihF c) (ihG c) body
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      intro m Δ ρ c
      have second := ihSnd c
      simp only [CTm.rename, CTm.rename_inst0] at second
      exact .etaSigma (ihP c) (ihQ c) (ihFst c) second
  | subEqual _ hu ih => exact fun c => .subEqual (ih c) hu
  | subUniv o => exact fun _ => .subUniv o
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      exact fun c => .subPi (ihPi c) hu (ihPi' c) hu' (ihA c) hw (ihB (c.snoc _))
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      exact fun c => .subSigma (ihS c) hu (ihS' c) hu' (ihA c) (ihB (c.snoc _))
  | subTrans _ _ ih₁ ih₂ => exact fun c => .subTrans (ih₁ c) (ih₂ c)

section Renaming

variable {P : ChurchRules R} {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m} {ρ : Ren n m}

theorem CTyped.rename {t A : CTm Head n} (typing : CTyped P Γ t A) (c : CCtxRen Γ Δ ρ) :
    CTyped P Δ (t.rename ρ) (A.rename ρ) :=
  CDerivable.renames typing c

theorem CEqual.rename {a b A : CTm Head n} (equal : CEqual P Γ a b A) (c : CCtxRen Γ Δ ρ) :
    CEqual P Δ (a.rename ρ) (b.rename ρ) (A.rename ρ) :=
  CDerivable.renames equal c

theorem CBelow.rename {A B : CTm Head n} (le : CBelow P Γ A B) (c : CCtxRen Γ Δ ρ) :
    CBelow P Δ (A.rename ρ) (B.rename ρ) :=
  CDerivable.renames le c

end Renaming

theorem CTyped.weaken {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {t A E : CTm Head n}
    (typing : CTyped P Γ t A) : CTyped P (.snoc Γ E) (t.rename wk) (A.rename wk) :=
  typing.rename (CCtxRen.wk Γ E)

theorem CEqual.weaken {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {a b A E : CTm Head n}
    (equal : CEqual P Γ a b A) : CEqual P (.snoc Γ E) (a.rename wk) (b.rename wk) (A.rename wk) :=
  equal.rename (CCtxRen.wk Γ E)

/-! ## Substitution -/

/-- A typed simultaneous substitution. -/
def CSubstMor (P : ChurchRules R) {n m : Nat} (Γ : CCtx Head n) (Δ : CCtx Head m)
    (σ : CSub Head n m) : Prop :=
  ∀ i, CTyped P Δ (σ i) ((Γ.lookup i).subst σ)

theorem CSubstMor.lift {P : ChurchRules R} {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m}
    {σ : CSub Head n m} (typed : CSubstMor P Γ Δ σ) (A : CTm Head n) :
    CSubstMor P (.snoc Γ A) (.snoc Δ (A.subst σ)) (CTm.liftSub σ) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa only [CTm.liftSub_zero, CCtx.lookup_snoc_zero, CTm.subst_liftSub_wk] using
      (CDerivable.var (P := P) (Γ := .snoc Δ (A.subst σ)) (0 : Fin (m + 1)))
  · intro j
    simpa only [CTm.liftSub_succ, CCtx.lookup_snoc_succ, CTm.subst_liftSub_wk] using
      CTyped.weaken (E := A.subst σ) (typed j)

/-- What substitution along a typed substitution gives for a statement. -/
abbrev CStatement.Substitutes (P : ChurchRules R) : CStatement Head → Prop
  | .typing Γ t A => ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head _ m},
      CSubstMor P Γ Δ σ → CTyped P Δ (t.subst σ) (A.subst σ)
  | .equality Γ a b A => ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head _ m},
      CSubstMor P Γ Δ σ → CEqual P Δ (a.subst σ) (b.subst σ) (A.subst σ)
  | .sub Γ A B => ∀ {m : Nat} {Δ : CCtx Head m} {σ : CSub Head _ m},
      CSubstMor P Γ Δ σ → CBelow P Δ (A.subst σ) (B.subst σ)

/-- What substitution gives for the statement of a premise is the statement of the
substituted premise. -/
theorem CPremise.substitutes {P : ChurchRules R} {n m : Nat} {Γ : CCtx Head n}
    {Δ : CCtx Head m} {σ : CSub Head n m} {premise : CPremise Head n}
    (substitutes : (premise.statement Γ).Substitutes P) (typed : CSubstMor P Γ Δ σ) :
    CDerivable P ((premise.subst σ).statement Δ) := by
  cases premise with
  | typing t T => exact substitutes typed
  | equality a b T => exact substitutes typed

theorem CDerivable.substitutes {P : ChurchRules R} {statement : CStatement Head}
    (derivation : CDerivable P statement) : statement.Substitutes P := by
  induction derivation with
  | headType h => exact fun _ => .headType h
  | var i => exact fun typed => typed i
  | const declared formed hu _ =>
      intro m Δ σ typed
      simpa only [CTm.subst, CTm.subst_liftClosed] using
        (CDerivable.const (Γ := Δ) declared formed hu)
  | piForm _ hu _ hv join ihA ihB =>
      exact fun typed => .piForm (ihA typed) hu (ihB (typed.lift _)) hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      exact fun typed => .sigmaForm (ihA typed) hu (ihB (typed.lift _)) hv join
  | lamIntro _ hw _ hu _ ihA ihPi ihBody =>
      exact fun typed => .lamIntro (ihA typed) hw (ihPi typed) hu (ihBody (typed.lift _))
  | appElim _ _ ihF ihA =>
      intro m Δ σ typed
      simpa only [CTm.subst, CTm.subst_inst0] using CDerivable.appElim (ihF typed) (ihA typed)
  | pairIntro _ hu _ _ ihS iha ihb =>
      intro m Δ σ typed
      have second := ihb typed
      rw [CTm.subst_inst0] at second
      exact .pairIntro (ihS typed) hu (iha typed) second
  | fstElim _ ih => exact fun typed => .fstElim (ih typed)
  | sndElim _ ih =>
      intro m Δ σ typed
      simpa only [CTm.subst, CTm.subst_inst0] using CDerivable.sndElim (ih typed)
  | idForm _ hu _ _ ihA iha ihb => exact fun typed => .idForm (ihA typed) hu (iha typed) (ihb typed)
  | reflIntro _ ih => exact fun typed => .reflIntro (ih typed)
  | sub _ _ ihT ihLe => exact fun typed => .sub (ihT typed) (ihLe typed)
  | conv _ _ hu ihT ihE => exact fun typed => .conv (ihT typed) (ihE typed) hu
  | refl _ ih => exact fun typed => .refl (ih typed)
  | symm _ ih => exact fun typed => .symm (ih typed)
  | trans _ _ ih₁ ih₂ => exact fun typed => .trans (ih₁ typed) (ih₂ typed)
  | convEq _ _ hu ih ihE => exact fun typed => .convEq (ih typed) (ihE typed) hu
  | subEq _ _ ih ihLe => exact fun typed => .subEq (ih typed) (ihLe typed)
  | headEq e _ _ ih ih' => exact fun typed => .headEq e (ih typed) (ih' typed)
  | piCong _ hu _ hv join ihA ihB =>
      exact fun typed => .piCong (ihA typed) hu (ihB (typed.lift _)) hv join
  | sigmaCong _ hu _ hv join ihA ihB =>
      exact fun typed => .sigmaCong (ihA typed) hu (ihB (typed.lift _)) hv join
  | idCong _ hu _ _ ihA iha ihb => exact fun typed => .idCong (ihA typed) hu (iha typed) (ihb typed)
  | lamCong _ hw _ hu _ ihA ihPi ihBody =>
      exact fun typed => .lamCong (ihA typed) hw (ihPi typed) hu (ihBody (typed.lift _))
  | appCong _ _ ihF ihA =>
      intro m Δ σ typed
      simpa only [CTm.subst, CTm.subst_inst0] using CDerivable.appCong (ihF typed) (ihA typed)
  | pairCong _ hu _ _ ihS iha ihb =>
      intro m Δ σ typed
      have second := ihb typed
      rw [CTm.subst_inst0] at second
      exact .pairCong (ihS typed) hu (iha typed) second
  | fstCong _ ih => exact fun typed => .fstCong (ih typed)
  | sndCong _ ih =>
      intro m Δ σ typed
      simpa only [CTm.subst, CTm.subst_inst0] using CDerivable.sndCong (ih typed)
  | reflCong _ ih => exact fun typed => .reflCong (ih typed)
  | betaPi _ hu _ _ ihPi ihBody iha =>
      intro m Δ σ typed
      simpa only [CTm.subst, CTm.subst_inst0] using
        CDerivable.betaPi (ihPi typed) hu (ihBody (typed.lift _)) (iha typed)
  | betaFst _ hu _ _ ihS iha ihb =>
      intro m Δ σ typed
      have second := ihb typed
      rw [CTm.subst_inst0] at second
      exact .betaFst (ihS typed) hu (iha typed) second
  | betaSnd _ hu _ _ ihS iha ihb =>
      intro m Δ σ typed
      have second := ihb typed
      rw [CTm.subst_inst0] at second
      simpa only [CTm.subst, CTm.subst_inst0] using
        CDerivable.betaSnd (ihS typed) hu (iha typed) second
  | root step requires _ _ _ ihPremises ihL ihR =>
      exact fun typed => .root (P.computation.substitute _ step)
        (P.computation.requires_substitute _ requires)
        (fun premise member => by
          obtain ⟨source, mem, rfl⟩ := List.mem_map.1 member
          exact CPremise.substitutes (ihPremises source mem) typed)
        (ihL typed) (ihR typed)
  | etaPi _ _ _ ihF ihG ihBody =>
      intro m Δ σ typed
      have body := ihBody (typed.lift _)
      simp only [CTm.subst, CTm.subst_liftSub_wk, CTm.liftSub_zero] at body
      exact .etaPi (ihF typed) (ihG typed) body
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      intro m Δ σ typed
      have second := ihSnd typed
      simp only [CTm.subst, CTm.subst_inst0] at second
      exact .etaSigma (ihP typed) (ihQ typed) (ihFst typed) second
  | subEqual _ hu ih => exact fun typed => .subEqual (ih typed) hu
  | subUniv o => exact fun _ => .subUniv o
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      exact fun typed =>
        .subPi (ihPi typed) hu (ihPi' typed) hu' (ihA typed) hw (ihB (typed.lift _))
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      exact fun typed => .subSigma (ihS typed) hu (ihS' typed) hu' (ihA typed) (ihB (typed.lift _))
  | subTrans _ _ ih₁ ih₂ => exact fun typed => .subTrans (ih₁ typed) (ih₂ typed)

section Substitution

variable {P : ChurchRules R} {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m} {σ : CSub Head n m}

theorem CTyped.substitute {t A : CTm Head n} (typing : CTyped P Γ t A)
    (typed : CSubstMor P Γ Δ σ) : CTyped P Δ (t.subst σ) (A.subst σ) :=
  CDerivable.substitutes typing typed

theorem CEqual.substitute {a b A : CTm Head n} (equal : CEqual P Γ a b A)
    (typed : CSubstMor P Γ Δ σ) : CEqual P Δ (a.subst σ) (b.subst σ) (A.subst σ) :=
  CDerivable.substitutes equal typed

theorem CBelow.substitute {A B : CTm Head n} (le : CBelow P Γ A B)
    (typed : CSubstMor P Γ Δ σ) : CBelow P Δ (A.subst σ) (B.subst σ) :=
  CDerivable.substitutes le typed

end Substitution

/-- The substitution opening one binder at a typed argument. -/
theorem CSubstMor.single {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n}
    (typing : CTyped P Γ a A) : CSubstMor P (.snoc Γ A) Γ (CTm.subst0 a) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · change CTyped P Γ a (CTm.inst0 a (A.rename wk))
    rw [CTm.inst0_rename_wk]
    exact typing
  · intro j
    change CTyped P Γ (.var j) (CTm.inst0 a ((Γ.lookup j).rename wk))
    rw [CTm.inst0_rename_wk]
    exact .var j

section Instantiate

variable {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n}

theorem CTyped.instantiate {body B : CTm Head (n + 1)} (typing : CTyped P (.snoc Γ A) body B)
    (argument : CTyped P Γ a A) : CTyped P Γ (CTm.inst0 a body) (CTm.inst0 a B) :=
  typing.substitute (CSubstMor.single argument)

theorem CEqual.instantiate {l r B : CTm Head (n + 1)} (equal : CEqual P (.snoc Γ A) l r B)
    (argument : CTyped P Γ a A) : CEqual P Γ (CTm.inst0 a l) (CTm.inst0 a r) (CTm.inst0 a B) :=
  equal.substitute (CSubstMor.single argument)

theorem CBelow.instantiate {B C : CTm Head (n + 1)} (le : CBelow P (.snoc Γ A) B C)
    (argument : CTyped P Γ a A) : CBelow P Γ (CTm.inst0 a B) (CTm.inst0 a C) :=
  le.substitute (CSubstMor.single argument)

end Instantiate

/-! ## Functionality -/

/-- Two substitutions that agree up to equality at the types the first one
assigns, the first one typed. -/
def CSubstEq (P : ChurchRules R) {n m : Nat} (Γ : CCtx Head n) (Δ : CCtx Head m)
    (σ τ : CSub Head n m) : Prop :=
  CSubstMor P Γ Δ σ ∧ ∀ i, CEqual P Δ (σ i) (τ i) ((Γ.lookup i).subst σ)

theorem CSubstEq.lift {P : ChurchRules R} {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m}
    {σ τ : CSub Head n m} (equal : CSubstEq P Γ Δ σ τ) (A : CTm Head n) :
    CSubstEq P (.snoc Γ A) (.snoc Δ (A.subst σ)) (CTm.liftSub σ) (CTm.liftSub τ) := by
  refine ⟨equal.1.lift A, ?_⟩
  intro i
  refine Fin.cases ?_ ?_ i
  · have := equal.1.lift A 0
    simp only [CTm.liftSub_zero] at this ⊢
    exact .refl this
  · intro j
    simpa only [CTm.liftSub_succ, CCtx.lookup_snoc_succ, CTm.subst_liftSub_wk] using
      CEqual.weaken (E := A.subst σ) (equal.2 j)

/-- What functionality gives for a statement. -/
abbrev CStatement.Functional (P : ChurchRules R) : CStatement Head → Prop
  | .typing Γ t A => ∀ {m : Nat} {Δ : CCtx Head m} {σ τ : CSub Head _ m},
      CSubstEq P Γ Δ σ τ → CEqual P Δ (t.subst σ) (t.subst τ) (A.subst σ)
  | .equality _ _ _ _ => True
  | .sub _ _ _ => True

/-- **Functionality**: a typed term substituted by two equal substitutions
gives equal terms. -/
theorem CDerivable.functional {P : ChurchRules R} {statement : CStatement Head}
    (derivation : CDerivable P statement) : statement.Functional P := by
  induction derivation with
  | headType h => exact fun _ => .refl (.headType h)
  | var i => exact fun equal => equal.2 i
  | const declared formed hu _ =>
      intro m Δ σ τ equal
      simpa only [CTm.subst, CTm.subst_liftClosed] using
        (CDerivable.refl (CDerivable.const (Γ := Δ) declared formed hu))
  | piForm _ hu _ hv join ihA ihB =>
      exact fun equal => .piCong (ihA equal) hu (ihB (equal.lift _)) hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      exact fun equal => .sigmaCong (ihA equal) hu (ihB (equal.lift _)) hv join
  | lamIntro _ hw tPi hu _ ihA _ ihBody =>
      exact fun equal => .lamCong (ihA equal) hw (CTyped.substitute tPi equal.1) hu
        (ihBody (equal.lift _))
  | appElim _ _ ihF ihA =>
      intro m Δ σ τ equal
      simpa only [CTm.subst, CTm.subst_inst0] using CDerivable.appCong (ihF equal) (ihA equal)
  | pairIntro tS hu _ _ _ iha ihb =>
      intro m Δ σ τ equal
      have second := ihb equal
      rw [CTm.subst_inst0] at second
      exact .pairCong (CTyped.substitute tS equal.1) hu (iha equal) second
  | fstElim _ ih => exact fun equal => .fstCong (ih equal)
  | sndElim _ ih =>
      intro m Δ σ τ equal
      simpa only [CTm.subst, CTm.subst_inst0] using CDerivable.sndCong (ih equal)
  | idForm _ hu _ _ ihA iha ihb => exact fun equal => .idCong (ihA equal) hu (iha equal) (ihb equal)
  | reflIntro _ ih => exact fun equal => .reflCong (ih equal)
  | sub _ le ihT _ => exact fun equal => .subEq (ihT equal) (CBelow.substitute le equal.1)
  | conv _ e hu ihT _ => exact fun equal => .convEq (ihT equal) (CEqual.substitute e equal.1) hu
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | convEq => trivial
  | subEq => trivial
  | headEq => trivial
  | piCong => trivial
  | sigmaCong => trivial
  | idCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | pairCong => trivial
  | fstCong => trivial
  | sndCong => trivial
  | reflCong => trivial
  | betaPi => trivial
  | betaFst => trivial
  | betaSnd => trivial
  | root => trivial
  | etaPi => trivial
  | etaSigma => trivial
  | subEqual => trivial
  | subUniv => trivial
  | subPi => trivial
  | subSigma => trivial
  | subTrans => trivial

/-- Opening a binder at two equal arguments gives equal results. -/
theorem CTyped.instantiateEq {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {A x y : CTm Head n}
    {body B : CTm Head (n + 1)} (typing : CTyped P (.snoc Γ A) body B)
    (argument : CTyped P Γ x A) (equal : CEqual P Γ x y A) :
    CEqual P Γ (CTm.inst0 x body) (CTm.inst0 y body) (CTm.inst0 x B) := by
  apply CDerivable.functional typing
  refine ⟨CSubstMor.single argument, ?_⟩
  intro i
  refine Fin.cases ?_ ?_ i
  · change CEqual P Γ x y (CTm.inst0 x (A.rename wk))
    rw [CTm.inst0_rename_wk]
    exact equal
  · intro j
    change CEqual P Γ (.var j) (.var j) (CTm.inst0 x ((Γ.lookup j).rename wk))
    rw [CTm.inst0_rename_wk]
    exact .refl (.var j)

/-! ## Generation -/

/-- The closure of the typing rules that do not follow the syntax: conversion
and subtyping. -/
inductive CTypeLe (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) :
    CTm Head n → CTm Head n → Prop where
  | refl (A : CTm Head n) : CTypeLe P Γ A A
  | conv {A B C : CTm Head n} {u : Head} : CEqual P Γ A B (.head u) → R.isUniverse u →
      CTypeLe P Γ B C → CTypeLe P Γ A C
  | sub {A B C : CTm Head n} : CBelow P Γ A B → CTypeLe P Γ B C → CTypeLe P Γ A C

section TypeLe

variable {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n}

theorem CTypeLe.trans {A B C : CTm Head n} (first : CTypeLe P Γ A B)
    (second : CTypeLe P Γ B C) : CTypeLe P Γ A C := by
  induction first with
  | refl => exact second
  | conv e hu _ ih => exact .conv e hu (ih second)
  | sub le _ ih => exact .sub le (ih second)

theorem CTyped.subsume {t A B : CTm Head n} (typing : CTyped P Γ t A) (le : CTypeLe P Γ A B) :
    CTyped P Γ t B := by
  induction le generalizing t with
  | refl => exact typing
  | conv e hu _ ih => exact ih (.conv typing e hu)
  | sub le _ ih => exact ih (.sub typing le)

theorem CEqual.subsume {a b A B : CTm Head n} (equal : CEqual P Γ a b A)
    (le : CTypeLe P Γ A B) : CEqual P Γ a b B := by
  induction le generalizing a b with
  | refl => exact equal
  | conv e hu _ ih => exact ih (.convEq equal e hu)
  | sub le _ ih => exact ih (.subEq equal le)

end TypeLe

/-- What a typing of a term says, by the term's former. -/
def CGenerationAt (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) :
    CTm Head n → CTm Head n → Prop
  | .var i, T => CTypeLe P Γ (Γ.lookup i) T
  | .const name, T => ∃ type u, P.constantType name = some type ∧
      CTyped P .nil type (.head u) ∧ R.isUniverse u ∧ CTypeLe P Γ type.liftClosed T
  | .head h, T => ∃ u, R.headTyping h u ∧ CTypeLe P Γ (.head u) T
  | .pi A B, T => ∃ u v w, CTyped P Γ A (.head u) ∧ R.isUniverse u ∧
      CTyped P (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧ R.join u v w ∧
      CTypeLe P Γ (.head w) T
  | .sigma A B, T => ∃ u v w, CTyped P Γ A (.head u) ∧ R.isUniverse u ∧
      CTyped P (.snoc Γ A) B (.head v) ∧ R.isUniverse v ∧ R.join u v w ∧
      CTypeLe P Γ (.head w) T
  | .id A a b, T => ∃ u, CTyped P Γ A (.head u) ∧ R.isUniverse u ∧ CTyped P Γ a A ∧
      CTyped P Γ b A ∧ CTypeLe P Γ (.head u) T
  | .lam A body, T => ∃ B u w, CTyped P Γ A (.head w) ∧ R.isUniverse w ∧
      CTyped P Γ (.pi A B) (.head u) ∧ R.isUniverse u ∧ CTyped P (.snoc Γ A) body B ∧
      CTypeLe P Γ (.pi A B) T
  | .app f a, T => ∃ A B, CTyped P Γ f (.pi A B) ∧ CTyped P Γ a A ∧
      CTypeLe P Γ (CTm.inst0 a B) T
  | .pair a b, T => ∃ A B u, CTyped P Γ (.sigma A B) (.head u) ∧ R.isUniverse u ∧
      CTyped P Γ a A ∧ CTyped P Γ b (CTm.inst0 a B) ∧ CTypeLe P Γ (.sigma A B) T
  | .fst p, T => ∃ A B, CTyped P Γ p (.sigma A B) ∧ CTypeLe P Γ A T
  | .snd p, T => ∃ A B, CTyped P Γ p (.sigma A B) ∧ CTypeLe P Γ (CTm.inst0 (.fst p) B) T
  | .refl a, T => ∃ A, CTyped P Γ a A ∧ CTypeLe P Γ (.id A a a) T

theorem CGenerationAt.mono {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {t T T' : CTm Head n}
    (generation : CGenerationAt P Γ t T) (le : CTypeLe P Γ T T') : CGenerationAt P Γ t T' := by
  cases t with
  | var i => exact CTypeLe.trans generation le
  | const name =>
      obtain ⟨type, u, d, typing, hu, le'⟩ := generation
      exact ⟨type, u, d, typing, hu, le'.trans le⟩
  | head h =>
      obtain ⟨u, typing, le'⟩ := generation
      exact ⟨u, typing, le'.trans le⟩
  | pi A B =>
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le'⟩ := generation
      exact ⟨u, v, w, tA, hu, tB, hv, join, le'.trans le⟩
  | sigma A B =>
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le'⟩ := generation
      exact ⟨u, v, w, tA, hu, tB, hv, join, le'.trans le⟩
  | id A a b =>
      obtain ⟨u, tA, hu, ta, tb, le'⟩ := generation
      exact ⟨u, tA, hu, ta, tb, le'.trans le⟩
  | lam A body =>
      obtain ⟨B, u, w, tA, hw, tPi, hu, tb, le'⟩ := generation
      exact ⟨B, u, w, tA, hw, tPi, hu, tb, le'.trans le⟩
  | app f a =>
      obtain ⟨A, B, tf, ta, le'⟩ := generation
      exact ⟨A, B, tf, ta, le'.trans le⟩
  | pair a b =>
      obtain ⟨A, B, u, tS, hu, ta, tb, le'⟩ := generation
      exact ⟨A, B, u, tS, hu, ta, tb, le'.trans le⟩
  | fst p =>
      obtain ⟨A, B, tp, le'⟩ := generation
      exact ⟨A, B, tp, le'.trans le⟩
  | snd p =>
      obtain ⟨A, B, tp, le'⟩ := generation
      exact ⟨A, B, tp, le'.trans le⟩
  | refl a =>
      obtain ⟨A, ta, le'⟩ := generation
      exact ⟨A, ta, le'.trans le⟩

/-- What a derivation says: generation for typings, nothing for the others. -/
def CGeneration (P : ChurchRules R) : CStatement Head → Prop
  | .typing Γ t T => CGenerationAt P Γ t T
  | .equality _ _ _ _ => True
  | .sub _ _ _ => True

theorem CDerivable.generation {P : ChurchRules R} {statement : CStatement Head}
    (derivation : CDerivable P statement) : CGeneration P statement := by
  induction derivation with
  | headType typing => exact ⟨_, typing, .refl _⟩
  | var i => exact .refl _
  | const declared typing hu => exact ⟨_, _, declared, typing, hu, .refl _⟩
  | piForm tA hu tB hv join => exact ⟨_, _, _, tA, hu, tB, hv, join, .refl _⟩
  | sigmaForm tA hu tB hv join => exact ⟨_, _, _, tA, hu, tB, hv, join, .refl _⟩
  | lamIntro tA hw tPi hu tb => exact ⟨_, _, _, tA, hw, tPi, hu, tb, .refl _⟩
  | appElim tf ta => exact ⟨_, _, tf, ta, .refl _⟩
  | pairIntro tS hu ta tb => exact ⟨_, _, _, tS, hu, ta, tb, .refl _⟩
  | fstElim tp => exact ⟨_, _, tp, .refl _⟩
  | sndElim tp => exact ⟨_, _, tp, .refl _⟩
  | idForm tA hu ta tb => exact ⟨_, tA, hu, ta, tb, .refl _⟩
  | reflIntro ta => exact ⟨_, ta, .refl _⟩
  | sub _ le ih => exact CGenerationAt.mono ih (.sub le (.refl _))
  | conv _ e hu ih => exact CGenerationAt.mono ih (.conv e hu (.refl _))
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | convEq => trivial
  | subEq => trivial
  | headEq => trivial
  | piCong => trivial
  | sigmaCong => trivial
  | idCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | pairCong => trivial
  | fstCong => trivial
  | sndCong => trivial
  | reflCong => trivial
  | betaPi => trivial
  | betaFst => trivial
  | betaSnd => trivial
  | root => trivial
  | etaPi => trivial
  | etaSigma => trivial
  | subEqual => trivial
  | subUniv => trivial
  | subPi => trivial
  | subSigma => trivial
  | subTrans => trivial

/-- Generation for a typing. -/
theorem CTyped.generation {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {t T : CTm Head n}
    (typing : CTyped P Γ t T) : CGenerationAt P Γ t T :=
  CDerivable.generation typing

/-! ## Induction on subtyping derivations -/

/-- Induction on a derivation of `Γ ⊢ A ⊑ B`. -/
theorem CBelow.induction {P : ChurchRules R}
    {motive : (n : Nat) → CCtx Head n → CTm Head n → CTm Head n → Prop}
    (equal : ∀ {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n} {u : Head},
      CEqual P Γ A B (.head u) → R.isUniverse u → motive n Γ A B)
    (univ : ∀ {n : Nat} {Γ : CCtx Head n} {u v : Head}, R.cumulative u v →
      motive n Γ (.head u) (.head v))
    (pi : ∀ {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u u' w : Head},
      CTyped P Γ (.pi A B) (.head u) → R.isUniverse u →
      CTyped P Γ (.pi A' B') (.head u') → R.isUniverse u' →
      CEqual P Γ A A' (.head w) → R.isUniverse w →
      CBelow P (.snoc Γ A) B B' → motive (n + 1) (.snoc Γ A) B B' →
      motive n Γ (.pi A B) (.pi A' B'))
    (sigma : ∀ {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u u' : Head},
      CTyped P Γ (.sigma A B) (.head u) → R.isUniverse u →
      CTyped P Γ (.sigma A' B') (.head u') → R.isUniverse u' →
      CBelow P Γ A A' → CBelow P (.snoc Γ A) B B' → motive n Γ A A' →
      motive (n + 1) (.snoc Γ A) B B' → motive n Γ (.sigma A B) (.sigma A' B'))
    (trans : ∀ {n : Nat} {Γ : CCtx Head n} {A B C : CTm Head n},
      CBelow P Γ A B → CBelow P Γ B C → motive n Γ A B → motive n Γ B C → motive n Γ A C)
    {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n} (le : CBelow P Γ A B) : motive n Γ A B := by
  have key : ∀ {st : CStatement Head}, CDerivable P st →
      (match st with
        | @CStatement.sub _ k Δ X Y => motive k Δ X Y
        | _ => True) := by
    intro st d
    induction d with
    | subEqual e hu _ => exact equal e hu
    | subUniv c => exact univ c
    | subPi tPi hu tPi' hu' eA hw leB _ _ _ ihB => exact pi tPi hu tPi' hu' eA hw leB ihB
    | subSigma tS hu tS' hu' leA leB _ _ ihA ihB => exact sigma tS hu tS' hu' leA leB ihA ihB
    | subTrans le₁ le₂ ih₁ ih₂ => exact trans le₁ le₂ ih₁ ih₂
    | headType => trivial
    | var => trivial
    | const => trivial
    | piForm => trivial
    | sigmaForm => trivial
    | lamIntro => trivial
    | appElim => trivial
    | pairIntro => trivial
    | fstElim => trivial
    | sndElim => trivial
    | idForm => trivial
    | reflIntro => trivial
    | sub => trivial
    | conv => trivial
    | refl => trivial
    | symm => trivial
    | trans => trivial
    | convEq => trivial
    | subEq => trivial
    | headEq => trivial
    | piCong => trivial
    | sigmaCong => trivial
    | idCong => trivial
    | lamCong => trivial
    | appCong => trivial
    | pairCong => trivial
    | fstCong => trivial
    | sndCong => trivial
    | reflCong => trivial
    | betaPi => trivial
    | betaFst => trivial
    | betaSnd => trivial
    | root => trivial
    | etaPi => trivial
    | etaSigma => trivial
  exact key le

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
