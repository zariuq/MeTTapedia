import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantRenaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates

/-!
# Instantiating declared constants by closed terms

`Tm.instConsts` replaces every constant by a closed term, lifted into the
ambient scope. It commutes with renaming, substitution, opening a binder and
lifting of closed terms.

`RulesInstance` keeps the universe laws. A constant declared at `T` is sent to
a closed term typed, in the empty context, at the instantiated declared type,
whenever that instantiated type is a type: the constant rule types a constant
only then, and renaming constants is the case where the closed term is itself
a constant. Each root step is sent to a root step, because the root rule of
the judgment demands a step and because one reduction step has to instantiate
to one reduction step.

Every derivable statement then instantiates (`Derivable.instConsts`).
Renaming is instantiation by constant terms (`Tm.instConsts_mapConst`), and
the renaming theorem for derivations follows (`Derivable.mapConst_by_instConsts`).
Strong normalization pulls back along an instantiation that sends root steps
to root steps (`SN.of_instConsts`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

/-! ## Terms -/

/-- Replace every constant `c` by the closed term `θ c`, lifted into the
ambient scope. -/
def Tm.instConsts (θ : DeclName → Tm Head 0) : {n : Nat} → Tm Head n → Tm Head n
  | _, .var i => .var i
  | _, .const c => liftClosed (θ c)
  | _, .head h => .head h
  | _, .pi A B => .pi (instConsts θ A) (instConsts θ B)
  | _, .sigma A B => .sigma (instConsts θ A) (instConsts θ B)
  | _, .id A a b => .id (instConsts θ A) (instConsts θ a) (instConsts θ b)
  | _, .lam body => .lam (instConsts θ body)
  | _, .app g a => .app (instConsts θ g) (instConsts θ a)
  | _, .pair a b => .pair (instConsts θ a) (instConsts θ b)
  | _, .fst p => .fst (instConsts θ p)
  | _, .snd p => .snd (instConsts θ p)
  | _, .refl a => .refl (instConsts θ a)

/-- A closed term lifted to the empty scope is itself. -/
theorem Tm.liftClosed_at_zero (t : Tm Head 0) : (liftClosed t : Tm Head 0) = t := by
  change rename Fin.elim0 t = t
  have empty : (Fin.elim0 : Ren 0 0) = idRen := by
    funext i
    exact i.elim0
  rw [empty, rename_id]

/-- Instantiation commutes with renaming. -/
@[simp] theorem Tm.instConsts_rename (θ : DeclName → Tm Head 0) {n m : Nat}
    (ρ : Ren n m) (t : Tm Head n) :
    (rename ρ t).instConsts θ = rename ρ (t.instConsts θ) := by
  induction t generalizing m with
  | var => rfl
  | const => exact (rename_liftClosed ρ (θ _)).symm
  | head => rfl
  | pi A B ihA ihB => simp only [rename, instConsts, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, instConsts, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, instConsts, ihA, iha, ihb]
  | lam body ih => simp only [rename, instConsts, ih]
  | app g a ihg iha => simp only [rename, instConsts, ihg, iha]
  | pair a b iha ihb => simp only [rename, instConsts, iha, ihb]
  | fst p ih => simp only [rename, instConsts, ih]
  | snd p ih => simp only [rename, instConsts, ih]
  | refl a ih => simp only [rename, instConsts, ih]

theorem Tm.instConsts_liftSub (θ : DeclName → Tm Head 0) {n m : Nat}
    (σ : Sub Head n m) :
    (fun i => (liftSub σ i).instConsts θ) =
      liftSub (fun i => (σ i).instConsts θ) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact Tm.instConsts_rename θ wk (σ j)

/-- Instantiation commutes with substitution. -/
@[simp] theorem Tm.instConsts_subst (θ : DeclName → Tm Head 0) {n m : Nat}
    (σ : Sub Head n m) (t : Tm Head n) :
    (subst σ t).instConsts θ =
      subst (fun i => (σ i).instConsts θ) (t.instConsts θ) := by
  induction t generalizing m with
  | var => rfl
  | const => exact (subst_liftClosed (fun i => (σ i).instConsts θ) (θ _)).symm
  | head => rfl
  | pi A B ihA ihB => simp only [subst, instConsts, ihA, ihB, Tm.instConsts_liftSub]
  | sigma A B ihA ihB => simp only [subst, instConsts, ihA, ihB, Tm.instConsts_liftSub]
  | id A a b ihA iha ihb => simp only [subst, instConsts, ihA, iha, ihb]
  | lam body ih => simp only [subst, instConsts, ih, Tm.instConsts_liftSub]
  | app g a ihg iha => simp only [subst, instConsts, ihg, iha]
  | pair a b iha ihb => simp only [subst, instConsts, iha, ihb]
  | fst p ih => simp only [subst, instConsts, ih]
  | snd p ih => simp only [subst, instConsts, ih]
  | refl a ih => simp only [subst, instConsts, ih]

/-- Instantiation commutes with opening the newest binder. -/
@[simp] theorem Tm.instConsts_inst0 (θ : DeclName → Tm Head 0) {n : Nat}
    (u : Tm Head n) (body : Tm Head (n + 1)) :
    (inst0 u body).instConsts θ = inst0 (u.instConsts θ) (body.instConsts θ) := by
  rw [inst0, inst0, Tm.instConsts_subst]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Instantiation commutes with lifting a closed term. -/
@[simp] theorem Tm.instConsts_liftClosed (θ : DeclName → Tm Head 0) {n : Nat}
    (t : Tm Head 0) :
    (liftClosed t : Tm Head n).instConsts θ = liftClosed (t.instConsts θ) :=
  Tm.instConsts_rename θ Fin.elim0 t

/-- **Instantiation by constant terms is renaming.** -/
theorem Tm.instConsts_mapConst (f : DeclName → DeclName) {n : Nat} (t : Tm Head n) :
    t.instConsts (fun c => .const (f c)) = t.mapConst f := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [instConsts, mapConst, ihA, ihB]
  | sigma A B ihA ihB => simp only [instConsts, mapConst, ihA, ihB]
  | id A a b ihA iha ihb => simp only [instConsts, mapConst, ihA, iha, ihb]
  | lam body ih => simp only [instConsts, mapConst, ih]
  | app g a ihg iha => simp only [instConsts, mapConst, ihg, iha]
  | pair a b iha ihb => simp only [instConsts, mapConst, iha, ihb]
  | fst p ih => simp only [instConsts, mapConst, ih]
  | snd p ih => simp only [instConsts, mapConst, ih]
  | refl a ih => simp only [instConsts, mapConst, ih]

/-- Instantiation fixes a term when it fixes every constant of that term. -/
theorem Tm.instConsts_of_allConstants (θ : DeclName → Tm Head 0)
    {p : DeclName → Bool} (fixes : ∀ c, p c = true → θ c = .const c) :
    ∀ {n : Nat} {t : Tm Head n}, t.allConstants p = true → t.instConsts θ = t
  | _, .var _, _ => rfl
  | _, .const c, h => by
      simp only [instConsts]
      rw [fixes c h]
      rfl
  | _, .head _, _ => rfl
  | _, .pi A B, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h.1,
        instConsts_of_allConstants θ fixes h.2]
  | _, .sigma A B, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h.1,
        instConsts_of_allConstants θ fixes h.2]
  | _, .id A a b, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h.1.1,
        instConsts_of_allConstants θ fixes h.1.2,
        instConsts_of_allConstants θ fixes h.2]
  | _, .lam body, h => by
      simp only [allConstants] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h]
  | _, .app g a, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h.1,
        instConsts_of_allConstants θ fixes h.2]
  | _, .pair a b, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h.1,
        instConsts_of_allConstants θ fixes h.2]
  | _, .fst q, h => by
      simp only [allConstants] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h]
  | _, .snd q, h => by
      simp only [allConstants] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h]
  | _, .refl a, h => by
      simp only [allConstants] at h
      simp only [instConsts, instConsts_of_allConstants θ fixes h]

/-! ## Contexts -/

/-- Instantiate every context entry. -/
def Ctx.instConsts (θ : DeclName → Tm Head 0) : {n : Nat} → Ctx Head n → Ctx Head n
  | _, .nil => .nil
  | _, .snoc Γ A => .snoc (instConsts θ Γ) (A.instConsts θ)

/-- Context lookup commutes with instantiation. -/
@[simp] theorem Ctx.lookup_instConsts (θ : DeclName → Tm Head 0) {n : Nat}
    (Γ : Ctx Head n) (i : Fin n) :
    Ctx.lookup (Γ.instConsts θ) i = (Ctx.lookup Γ i).instConsts θ := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A ih =>
      refine Fin.cases ?_ ?_ i
      · exact (Tm.instConsts_rename θ wk A).symm
      · intro j
        change rename wk (Ctx.lookup (Γ.instConsts θ) j) =
          (rename wk (Ctx.lookup Γ j)).instConsts θ
        rw [ih, Tm.instConsts_rename]

theorem Ctx.instConsts_mapConst (f : DeclName → DeclName) {n : Nat} (Γ : Ctx Head n) :
    Γ.instConsts (fun c => .const (f c)) = Γ.mapConst f := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp only [Ctx.instConsts, Ctx.mapConst, ih, Tm.instConsts_mapConst]

/-- Whether every declared name of a context satisfies `p`. -/
def Ctx.allConstants (p : DeclName → Bool) : {n : Nat} → Ctx Head n → Bool
  | _, .nil => true
  | _, .snoc Γ A => allConstants p Γ && A.allConstants p

theorem Ctx.instConsts_of_allConstants (θ : DeclName → Tm Head 0)
    {p : DeclName → Bool} (fixes : ∀ c, p c = true → θ c = .const c) :
    ∀ {n : Nat} {Γ : Ctx Head n}, Γ.allConstants p = true → Γ.instConsts θ = Γ
  | _, .nil, _ => rfl
  | _, .snoc Γ A, h => by
      simp only [Ctx.allConstants, Bool.and_eq_true] at h
      simp only [Ctx.instConsts, Ctx.instConsts_of_allConstants θ fixes h.1,
        Tm.instConsts_of_allConstants θ fixes h.2]

namespace TypedEquality

/-! ## Statements -/

/-- A statement with its constants instantiated. -/
def Statement.instConsts (θ : DeclName → Tm Head 0) : Statement Head → Statement Head
  | .typing Γ t A => .typing (Γ.instConsts θ) (t.instConsts θ) (A.instConsts θ)
  | .equality Γ a b A =>
      .equality (Γ.instConsts θ) (a.instConsts θ) (b.instConsts θ) (A.instConsts θ)
  | .sub Γ A B => .sub (Γ.instConsts θ) (A.instConsts θ) (B.instConsts θ)

/-- Whether every declared name of a statement satisfies `p`. -/
def Statement.allConstants (p : DeclName → Bool) : Statement Head → Bool
  | .typing Γ t A => Γ.allConstants p && t.allConstants p && A.allConstants p
  | .equality Γ a b A =>
      Γ.allConstants p && a.allConstants p && b.allConstants p && A.allConstants p
  | .sub Γ A B => Γ.allConstants p && A.allConstants p && B.allConstants p

theorem Statement.instConsts_mapConst (f : DeclName → DeclName) (st : Statement Head) :
    st.instConsts (fun c => .const (f c)) = st.mapConst f := by
  cases st with
  | typing => simp only [Statement.instConsts, Statement.mapConst,
      Ctx.instConsts_mapConst, Tm.instConsts_mapConst]
  | equality => simp only [Statement.instConsts, Statement.mapConst,
      Ctx.instConsts_mapConst, Tm.instConsts_mapConst]
  | sub => simp only [Statement.instConsts, Statement.mapConst,
      Ctx.instConsts_mapConst, Tm.instConsts_mapConst]

theorem Statement.instConsts_of_allConstants (θ : DeclName → Tm Head 0)
    {p : DeclName → Bool} (fixes : ∀ c, p c = true → θ c = .const c)
    {st : Statement Head} (covered : st.allConstants p = true) :
    st.instConsts θ = st := by
  cases st with
  | typing =>
      simp only [Statement.allConstants, Bool.and_eq_true] at covered
      simp only [Statement.instConsts, Ctx.instConsts_of_allConstants θ fixes covered.1.1,
        Tm.instConsts_of_allConstants θ fixes covered.1.2,
        Tm.instConsts_of_allConstants θ fixes covered.2]
  | equality =>
      simp only [Statement.allConstants, Bool.and_eq_true] at covered
      simp only [Statement.instConsts, Ctx.instConsts_of_allConstants θ fixes covered.1.1.1,
        Tm.instConsts_of_allConstants θ fixes covered.1.1.2,
        Tm.instConsts_of_allConstants θ fixes covered.1.2,
        Tm.instConsts_of_allConstants θ fixes covered.2]
  | sub =>
      simp only [Statement.allConstants, Bool.and_eq_true] at covered
      simp only [Statement.instConsts, Ctx.instConsts_of_allConstants θ fixes covered.1.1,
        Tm.instConsts_of_allConstants θ fixes covered.1.2,
        Tm.instConsts_of_allConstants θ fixes covered.2]

/-! ## Instantiation of a rule package -/

/-- **An instantiation of the declared constants of `R` in `R'`.** The universe
laws are kept. A constant declared in `R` at `T` is sent to a closed term of
`R'` typed at `T` instantiated, in the empty context, whenever that
instantiated type is a type: the constant rule of the judgment types a
constant only from a typing of its declared type, so the renaming instance
needs nothing more than that typing. Each root step of `R` is a root step of
`R'` after instantiation. A root step, rather than only an equality, is what
the root rule requires, and what sends one reduction step to one reduction
step. -/
structure RulesInstance (R R' : Rules Head) (θ : DeclName → Tm Head 0) : Prop where
  headTyping : ∀ {h u : Head}, R.headTyping h u → R'.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → R'.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → R'.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → R'.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → R'.headEq h h'
  typed : ∀ {c : DeclName} {T : Tm Head 0} {u : Head},
    R.constantType c = some T →
    Typed R' .nil (T.instConsts θ) (.head u) → R'.isUniverse u →
    Typed R' .nil (θ c) (T.instConsts θ)
  computation : ∀ {n : Nat} {l r : Tm Head n},
    R.computation.step l r →
    R'.computation.step (l.instConsts θ) (r.instConsts θ)

/-- **Every derivable statement instantiates.** -/
theorem Derivable.instConsts {R R' : Rules Head} {θ : DeclName → Tm Head 0}
    (inst : RulesInstance R R' θ) {st : Statement Head} (derivation : Derivable R st) :
    Derivable R' (st.instConsts θ) := by
  induction derivation with
  | headType typing => exact .headType (inst.headTyping typing)
  | @var n Γ i =>
      simp only [Statement.instConsts, Tm.instConsts]
      rw [← Ctx.lookup_instConsts]
      exact .var i
  | const declared _ hu ihType =>
      simp only [Statement.instConsts, Tm.instConsts] at ihType ⊢
      rw [Tm.instConsts_liftClosed]
      exact Typed.rename (ρ := Fin.elim0)
        (inst.typed declared ihType (inst.isUniverse hu)) (fun i => i.elim0)
  | piForm _ hu _ hv join ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts] at ihA ihB ⊢
      exact .piForm ihA (inst.isUniverse hu) ihB (inst.isUniverse hv) (inst.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts] at ihA ihB ⊢
      exact .sigmaForm ihA (inst.isUniverse hu) ihB (inst.isUniverse hv)
        (inst.join join)
  | lamIntro _ hu _ ihPi ihBody =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts] at ihPi ihBody ⊢
      exact .lamIntro ihPi (inst.isUniverse hu) ihBody
  | appElim _ _ ihF ihA =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0] at ihF ihA ⊢
      exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0]
        at ihS ihA ihB ⊢
      exact .pairIntro ihS (inst.isUniverse hu) ihA ihB
  | fstElim _ ih =>
      simp only [Statement.instConsts, Tm.instConsts] at ih ⊢
      exact .fstElim ih
  | sndElim _ ih =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0] at ih ⊢
      exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb =>
      simp only [Statement.instConsts, Tm.instConsts] at ihA iha ihb ⊢
      exact .idForm ihA (inst.isUniverse hu) iha ihb
  | reflIntro _ ih =>
      simp only [Statement.instConsts, Tm.instConsts] at ih ⊢
      exact .reflIntro ih
  | sub _ _ ihT ihLe =>
      simp only [Statement.instConsts] at ihT ihLe ⊢
      exact .sub ihT ihLe
  | conv _ _ hu ihT ihE =>
      simp only [Statement.instConsts, Tm.instConsts] at ihT ihE ⊢
      exact .conv ihT ihE (inst.isUniverse hu)
  | refl _ ih =>
      simp only [Statement.instConsts] at ih ⊢
      exact .refl ih
  | symm _ ih =>
      simp only [Statement.instConsts] at ih ⊢
      exact .symm ih
  | trans _ _ ih₁ ih₂ =>
      simp only [Statement.instConsts] at ih₁ ih₂ ⊢
      exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihT =>
      simp only [Statement.instConsts, Tm.instConsts] at ih ihT ⊢
      exact .convEq ih ihT (inst.isUniverse hu)
  | subEq _ _ ihE ihLe =>
      simp only [Statement.instConsts] at ihE ihLe ⊢
      exact .subEq ihE ihLe
  | headEq same _ _ ih ih' =>
      simp only [Statement.instConsts, Tm.instConsts] at ih ih' ⊢
      exact .headEq (inst.headEq same) ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts] at ihA ihB ⊢
      exact .piCong ihA (inst.isUniverse hu) ihB (inst.isUniverse hv) (inst.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts] at ihA ihB ⊢
      exact .sigmaCong ihA (inst.isUniverse hu) ihB (inst.isUniverse hv)
        (inst.join join)
  | idCong _ hu _ _ ihA iha ihb =>
      simp only [Statement.instConsts, Tm.instConsts] at ihA iha ihb ⊢
      exact .idCong ihA (inst.isUniverse hu) iha ihb
  | lamCong _ hu _ ihPi ihBody =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts] at ihPi ihBody ⊢
      exact .lamCong ihPi (inst.isUniverse hu) ihBody
  | appCong _ _ ihF ihA =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0] at ihF ihA ⊢
      exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0]
        at ihS ihA ihB ⊢
      exact .pairCong ihS (inst.isUniverse hu) ihA ihB
  | fstCong _ ih =>
      simp only [Statement.instConsts, Tm.instConsts] at ih ⊢
      exact .fstCong ih
  | sndCong _ ih =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0] at ih ⊢
      exact .sndCong ih
  | reflCong _ ih =>
      simp only [Statement.instConsts, Tm.instConsts] at ih ⊢
      exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody ihA =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0, Ctx.instConsts]
        at ihPi ihBody ihA ⊢
      exact .betaPi ihPi (inst.isUniverse hu) ihBody ihA
  | betaFst _ hu _ _ ihS ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0]
        at ihS ihA ihB ⊢
      exact .betaFst ihS (inst.isUniverse hu) ihA ihB
  | betaSnd _ hu _ _ ihS ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0]
        at ihS ihA ihB ⊢
      exact .betaSnd ihS (inst.isUniverse hu) ihA ihB
  | root step _ _ ihL ihR =>
      simp only [Statement.instConsts] at ihL ihR ⊢
      exact .root (inst.computation step) ihL ihR
  | etaPi _ _ _ ihF ihG ihApps =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_rename, Ctx.instConsts]
        at ihF ihG ihApps ⊢
      exact .etaPi ihF ihG ihApps
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      simp only [Statement.instConsts, Tm.instConsts, Tm.instConsts_inst0]
        at ihP ihQ ihFst ihSnd ⊢
      exact .etaSigma ihP ihQ ihFst ihSnd
  | subEqual _ hu ih =>
      simp only [Statement.instConsts, Tm.instConsts] at ih ⊢
      exact .subEqual ih (inst.isUniverse hu)
  | subUniv c =>
      simp only [Statement.instConsts, Tm.instConsts]
      exact .subUniv (inst.cumulative c)
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts]
        at ihPi ihPi' ihA ihB ⊢
      exact .subPi ihPi (inst.isUniverse hu) ihPi' (inst.isUniverse hu') ihA
        (inst.isUniverse hw) ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      simp only [Statement.instConsts, Tm.instConsts, Ctx.instConsts]
        at ihS ihS' ihA ihB ⊢
      exact .subSigma ihS (inst.isUniverse hu) ihS' (inst.isUniverse hu') ihA ihB
  | subTrans _ _ ih₁ ih₂ =>
      simp only [Statement.instConsts] at ih₁ ih₂ ⊢
      exact .subTrans ih₁ ih₂

theorem Typed.instConsts {R R' : Rules Head} {θ : DeclName → Tm Head 0}
    (inst : RulesInstance R R' θ) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typed : Typed R Γ t A) :
    Typed R' (Γ.instConsts θ) (t.instConsts θ) (A.instConsts θ) :=
  Derivable.instConsts inst typed

theorem Equal.instConsts {R R' : Rules Head} {θ : DeclName → Tm Head 0}
    (inst : RulesInstance R R' θ) {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (equal : Equal R Γ a b A) :
    Equal R' (Γ.instConsts θ) (a.instConsts θ) (b.instConsts θ) (A.instConsts θ) :=
  Derivable.instConsts inst equal

/-- Renaming is an instantiation by constant terms. -/
theorem RulesInstance.of_renaming {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) :
    RulesInstance R R' (fun c => .const (f c)) where
  headTyping := ren.headTyping
  isUniverse := ren.isUniverse
  join := ren.join
  cumulative := ren.cumulative
  headEq := ren.headEq
  typed := by
    intro c T u declared formed hu
    rw [Tm.instConsts_mapConst] at formed ⊢
    have typedConst :=
      Derivable.const (Γ := .nil) (ren.constantType declared) formed hu
    rw [Tm.liftClosed_at_zero] at typedConst
    exact typedConst
  computation := by
    intro n l r step
    rw [Tm.instConsts_mapConst, Tm.instConsts_mapConst]
    exact ren.computation step

/-- **`Derivable.mapConst` follows from instantiation** at constant terms. -/
theorem Derivable.mapConst_by_instConsts {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) {st : Statement Head} (derivation : Derivable R st) :
    Derivable R' (st.mapConst f) := by
  rw [← Statement.instConsts_mapConst]
  exact Derivable.instConsts (RulesInstance.of_renaming ren) derivation

theorem Typed.mapConst_by_instConsts {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typed : Typed R Γ t A) :
    Typed R' (Γ.mapConst f) (t.mapConst f) (A.mapConst f) :=
  Derivable.mapConst_by_instConsts ren typed

theorem Equal.mapConst_by_instConsts {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (equal : Equal R Γ a b A) :
    Equal R' (Γ.mapConst f) (a.mapConst f) (b.mapConst f) (A.mapConst f) :=
  Derivable.mapConst_by_instConsts ren equal

/-- A root step in which every constant is fixed by `θ` is still a root step
after instantiation. Computing constants occur in root steps, so they stay
fixed; a rigid constant that occurs in no root step may be sent to a closed
term. -/
theorem Rules.computation_fixed {R : Rules Head} (θ : DeclName → Tm Head 0)
    {p : DeclName → Bool} (fixes : ∀ c, p c = true → θ c = .const c)
    (covered : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      l.allConstants p = true ∧ r.allConstants p = true)
    {n : Nat} {l r : Tm Head n} (step : R.computation.step l r) :
    R.computation.step (l.instConsts θ) (r.instConsts θ) := by
  obtain ⟨hl, hr⟩ := covered step
  rw [Tm.instConsts_of_allConstants θ fixes hl, Tm.instConsts_of_allConstants θ fixes hr]
  exact step

namespace StrongNormalization

/-- A step instantiates to a step when root steps instantiate to root steps. -/
theorem Reduces.instConsts {R R' : Rules Head} (θ : DeclName → Tm Head 0)
    (roots : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R'.computation.step (l.instConsts θ) (r.instConsts θ)) :
    ∀ {n : Nat} {t u : Tm Head n}, Reduces R t u →
      Reduces R' (t.instConsts θ) (u.instConsts θ)
  | _, _, _, .betaPi _ _ => by
      simp only [Tm.instConsts, Tm.instConsts_inst0]
      exact .betaPi _ _
  | _, _, _, .betaSigmaFst _ _ => by
      simp only [Tm.instConsts]
      exact .betaSigmaFst _ _
  | _, _, _, .betaSigmaSnd _ _ => by
      simp only [Tm.instConsts]
      exact .betaSigmaSnd _ _
  | _, _, _, .head same => nomatch same
  | _, _, _, .root step => .root (roots step)
  | _, _, _, .congPiDom h => .congPiDom (Reduces.instConsts θ roots h)
  | _, _, _, .congPiCod h => .congPiCod (Reduces.instConsts θ roots h)
  | _, _, _, .congSigmaDom h => .congSigmaDom (Reduces.instConsts θ roots h)
  | _, _, _, .congSigmaCod h => .congSigmaCod (Reduces.instConsts θ roots h)
  | _, _, _, .congIdTy h => .congIdTy (Reduces.instConsts θ roots h)
  | _, _, _, .congIdLeft h => .congIdLeft (Reduces.instConsts θ roots h)
  | _, _, _, .congIdRight h => .congIdRight (Reduces.instConsts θ roots h)
  | _, _, _, .congLam h => .congLam (Reduces.instConsts θ roots h)
  | _, _, _, .congAppFun h => .congAppFun (Reduces.instConsts θ roots h)
  | _, _, _, .congAppArg h => .congAppArg (Reduces.instConsts θ roots h)
  | _, _, _, .congPairFst h => .congPairFst (Reduces.instConsts θ roots h)
  | _, _, _, .congPairSnd h => .congPairSnd (Reduces.instConsts θ roots h)
  | _, _, _, .congFst h => .congFst (Reduces.instConsts θ roots h)
  | _, _, _, .congSnd h => .congSnd (Reduces.instConsts θ roots h)
  | _, _, _, .congRefl h => .congRefl (Reduces.instConsts θ roots h)

/-- **Strong normalization pulls back along an instantiation** that sends root
steps to root steps. -/
theorem SN.of_instConsts {R R' : Rules Head} (θ : DeclName → Tm Head 0)
    (roots : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R'.computation.step (l.instConsts θ) (r.instConsts θ))
    {n : Nat} {t : Tm Head n} (sn : SN R' (t.instConsts θ)) : SN R t := by
  have key : ∀ s, SN R' s → ∀ t : Tm Head n, t.instConsts θ = s → SN R t := by
    intro s hs
    induction hs with
    | intro s _ ih =>
        intro t ht
        exact SN.intro fun u step =>
          ih (u.instConsts θ) (ht ▸ Reduces.instConsts θ roots step) u rfl
  exact key _ sn t rfl

/-- `Reduces.mapConst` follows from instantiation at constant terms. -/
theorem Reduces.mapConst_by_instConsts {R R' : Rules Head} {f : DeclName → DeclName}
    (roots : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R'.computation.step (l.mapConst f) (r.mapConst f)) :
    ∀ {n : Nat} {t u : Tm Head n}, Reduces R t u →
      Reduces R' (t.mapConst f) (u.mapConst f) := by
  intro n t u step
  have mapped := Reduces.instConsts (fun c => .const (f c))
    (fun {_n} {_l} {_r} s => by
      rw [Tm.instConsts_mapConst, Tm.instConsts_mapConst]
      exact roots s) step
  rw [Tm.instConsts_mapConst, Tm.instConsts_mapConst] at mapped
  exact mapped

/-- `SN.of_mapConst` follows from instantiation at constant terms. -/
theorem SN.of_mapConst_by_instConsts {R R' : Rules Head} {f : DeclName → DeclName}
    (roots : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R'.computation.step (l.mapConst f) (r.mapConst f))
    {n : Nat} {t : Tm Head n} (sn : SN R' (t.mapConst f)) : SN R t := by
  rw [← Tm.instConsts_mapConst] at sn
  exact SN.of_instConsts (fun c => .const (f c))
    (fun {_n} {_l} {_r} s => by
      rw [Tm.instConsts_mapConst, Tm.instConsts_mapConst]
      exact roots s) sn

end StrongNormalization

end TypedEquality

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
