import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Validity

/-!
# Instantiating declared constants by closed terms

**Instantiation** (`CTm.instConsts`) replaces every constant `c` of an annotated term by a
closed term `θ c`. It commutes with renaming, substitution, opening a binder and lifting
closed terms (`instConsts_rename`, `instConsts_subst`, `instConsts_inst0`,
`instConsts_liftClosed`), and with looking up a variable's type (`CCtx.instConsts_lookup`).

**Instantiating derivations** (`CDerivable.instConsts`): when the universe rules of one
annotated package are among those of another, each declared constant of the first is sent to
a closed term of the second typed at its instantiated declared type whenever that type is a
type of the second, and each root step of the first is sent to a root step of the second,
every derivation of the first instantiates to a derivation of the second (`ConstInstance`).
This is the δ-instantiation of a conservative extension by declared constants: the constants
are definable in the smaller package. Renaming the constants is an instantiation by constants:
instantiating twice is instantiating once (`CTm.instConsts_instConsts`), and instantiating
each constant by itself changes nothing (`CTm.instConsts_const`). Formed contexts and equations
of types instantiate (`CCtxFormed.instConsts`, `CTypeEq.instConsts`).

**Constant-free terms** (`CTm.constFree`) are left unchanged by every instantiation
(`CTm.instConsts_of_constFree`). In a package that declares no constant and has no root step,
every derivable statement over a constant-free context mentions no constant
(`CDerivable.constFree`); so does every formed context (`CCtxFormed.constFree`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type}

/-! ## Instantiation of terms -/

namespace CTm

/-- Replace every constant `c` by the closed term `θ c`. -/
def instConsts (θ : DeclName → CTm Head 0) {n : Nat} : CTm Head n → CTm Head n
  | .var i => .var i
  | .const c => (θ c).liftClosed
  | .head h => .head h
  | .pi A B => .pi (instConsts θ A) (instConsts θ B)
  | .sigma A B => .sigma (instConsts θ A) (instConsts θ B)
  | .id A a b => .id (instConsts θ A) (instConsts θ a) (instConsts θ b)
  | .lam A b => .lam (instConsts θ A) (instConsts θ b)
  | .app f a => .app (instConsts θ f) (instConsts θ a)
  | .pair a b => .pair (instConsts θ a) (instConsts θ b)
  | .fst p => .fst (instConsts θ p)
  | .snd p => .snd (instConsts θ p)
  | .refl a => .refl (instConsts θ a)

variable (θ : DeclName → CTm Head 0)

/-- Instantiation commutes with renaming. -/
theorem instConsts_rename {n m : Nat} (ρ : Ren n m) (t : CTm Head n) :
    (t.rename ρ).instConsts θ = (t.instConsts θ).rename ρ := by
  induction t generalizing m with
  | var => rfl
  | const c => exact (rename_liftClosed ρ (θ c)).symm
  | head => rfl
  | pi A B ihA ihB => simp only [rename, instConsts, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, instConsts, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, instConsts, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [rename, instConsts, ihA, ihb]
  | app f a ihf iha => simp only [rename, instConsts, ihf, iha]
  | pair a b iha ihb => simp only [rename, instConsts, iha, ihb]
  | fst p ih => simp only [rename, instConsts, ih]
  | snd p ih => simp only [rename, instConsts, ih]
  | refl a ih => simp only [rename, instConsts, ih]

theorem instConsts_liftSub {n m : Nat} (σ : CSub Head n m) (i : Fin (n + 1)) :
    (liftSub σ i).instConsts θ = liftSub (fun j => (σ j).instConsts θ) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact instConsts_rename θ wk (σ j)

/-- Instantiation commutes with substitution. -/
theorem instConsts_subst {n m : Nat} (σ : CSub Head n m) (t : CTm Head n) :
    (t.subst σ).instConsts θ = (t.instConsts θ).subst (fun i => (σ i).instConsts θ) := by
  induction t generalizing m with
  | var => rfl
  | const c => exact (subst_liftClosed _ (θ c)).symm
  | head => rfl
  | pi A B ihA ihB =>
      simp only [subst, instConsts, ihA, ihB]
      rw [subst_ext (instConsts_liftSub θ σ)]
  | sigma A B ihA ihB =>
      simp only [subst, instConsts, ihA, ihB]
      rw [subst_ext (instConsts_liftSub θ σ)]
  | id A a b ihA iha ihb => simp only [subst, instConsts, ihA, iha, ihb]
  | lam A b ihA ihb =>
      simp only [subst, instConsts, ihA, ihb]
      rw [subst_ext (instConsts_liftSub θ σ)]
  | app f a ihf iha => simp only [subst, instConsts, ihf, iha]
  | pair a b iha ihb => simp only [subst, instConsts, iha, ihb]
  | fst p ih => simp only [subst, instConsts, ih]
  | snd p ih => simp only [subst, instConsts, ih]
  | refl a ih => simp only [subst, instConsts, ih]

/-- Instantiation commutes with opening the newest binder. -/
theorem instConsts_inst0 {n : Nat} (u : CTm Head n) (body : CTm Head (n + 1)) :
    (inst0 u body).instConsts θ = inst0 (u.instConsts θ) (body.instConsts θ) := by
  unfold inst0
  rw [instConsts_subst]
  apply subst_ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Instantiation commutes with lifting a closed term. -/
theorem instConsts_liftClosed {n : Nat} (t : CTm Head 0) :
    (t.liftClosed : CTm Head n).instConsts θ = (t.instConsts θ).liftClosed :=
  instConsts_rename θ Fin.elim0 t

/-- A closed term lifted to the empty telescope is itself. -/
@[simp] theorem liftClosed_zero (t : CTm Head 0) : (t.liftClosed : CTm Head 0) = t := by
  unfold liftClosed
  rw [rename_ext (ξ := idRen) (fun i => i.elim0) t]
  exact rename_id t

/-- **Instantiating twice** is instantiating by the instantiated terms. -/
theorem instConsts_instConsts (θ' : DeclName → CTm Head 0) {n : Nat} (t : CTm Head n) :
    (t.instConsts θ).instConsts θ' = t.instConsts (fun c => (θ c).instConsts θ') := by
  induction t with
  | var => rfl
  | const c => exact instConsts_liftClosed θ' (θ c)
  | head => rfl
  | pi A B ihA ihB => simp only [instConsts, ihA, ihB]
  | sigma A B ihA ihB => simp only [instConsts, ihA, ihB]
  | id A a b ihA iha ihb => simp only [instConsts, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [instConsts, ihA, ihb]
  | app f a ihf iha => simp only [instConsts, ihf, iha]
  | pair a b iha ihb => simp only [instConsts, iha, ihb]
  | fst p ih => simp only [instConsts, ih]
  | snd p ih => simp only [instConsts, ih]
  | refl a ih => simp only [instConsts, ih]

/-- **Instantiating every constant by itself** changes nothing. -/
@[simp] theorem instConsts_const {n : Nat} (t : CTm Head n) :
    t.instConsts (fun c => .const c) = t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [instConsts, ihA, ihB]
  | sigma A B ihA ihB => simp only [instConsts, ihA, ihB]
  | id A a b ihA iha ihb => simp only [instConsts, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [instConsts, ihA, ihb]
  | app f a ihf iha => simp only [instConsts, ihf, iha]
  | pair a b iha ihb => simp only [instConsts, iha, ihb]
  | fst p ih => simp only [instConsts, ih]
  | snd p ih => simp only [instConsts, ih]
  | refl a ih => simp only [instConsts, ih]

end CTm

/-! ## Instantiation of contexts and statements -/

namespace CCtx

/-- Instantiate every entry. -/
def instConsts (θ : DeclName → CTm Head 0) : {n : Nat} → CCtx Head n → CCtx Head n
  | _, .nil => .nil
  | _, .snoc Γ A => .snoc (instConsts θ Γ) (A.instConsts θ)

/-- Looking up a variable's type commutes with instantiation. -/
theorem instConsts_lookup (θ : DeclName → CTm Head 0) :
    ∀ {n : Nat} (Γ : CCtx Head n) (i : Fin n),
      (Γ.lookup i).instConsts θ = (Γ.instConsts θ).lookup i
  | _, .nil, i => i.elim0
  | _, .snoc Γ A, i => by
      refine Fin.cases ?_ ?_ i
      · exact CTm.instConsts_rename θ wk A
      · intro j
        change ((Γ.lookup j).rename wk).instConsts θ = ((Γ.instConsts θ).lookup j).rename wk
        rw [CTm.instConsts_rename, instConsts_lookup θ Γ j]

/-- Instantiating a context twice is instantiating it by the instantiated terms. -/
theorem instConsts_instConsts (θ θ' : DeclName → CTm Head 0) :
    ∀ {n : Nat} (Γ : CCtx Head n),
      (Γ.instConsts θ).instConsts θ' = Γ.instConsts (fun c => (θ c).instConsts θ')
  | _, .nil => rfl
  | _, .snoc Γ A => by
      simp only [instConsts, instConsts_instConsts θ θ' Γ, CTm.instConsts_instConsts]

/-- Instantiating every constant of a context by itself changes nothing. -/
@[simp] theorem instConsts_const : ∀ {n : Nat} (Γ : CCtx Head n),
    Γ.instConsts (fun c => .const c) = Γ
  | _, .nil => rfl
  | _, .snoc Γ A => by simp only [instConsts, instConsts_const Γ, CTm.instConsts_const]

end CCtx

/-- Instantiate every term of a statement. -/
def CStatement.instConsts (θ : DeclName → CTm Head 0) : CStatement Head → CStatement Head
  | .typing Γ t A => .typing (Γ.instConsts θ) (t.instConsts θ) (A.instConsts θ)
  | .equality Γ a b A =>
      .equality (Γ.instConsts θ) (a.instConsts θ) (b.instConsts θ) (A.instConsts θ)
  | .sub Γ A B => .sub (Γ.instConsts θ) (A.instConsts θ) (B.instConsts θ)

/-- Instantiate every term of a premise. -/
def CPremise.instConsts {n : Nat} (θ : DeclName → CTm Head 0) :
    CPremise Head n → CPremise Head n
  | .typing t T => .typing (t.instConsts θ) (T.instConsts θ)
  | .equality a b T => .equality (a.instConsts θ) (b.instConsts θ) (T.instConsts θ)

/-- The instantiated statement of a premise is the statement of the instantiated premise. -/
theorem CPremise.statement_instConsts {n : Nat} (θ : DeclName → CTm Head 0) (Γ : CCtx Head n)
    (premise : CPremise Head n) :
    (premise.statement Γ).instConsts θ = (premise.instConsts θ).statement (Γ.instConsts θ) := by
  cases premise <;> rfl

/-! ## Instantiation of derivations -/

/-- **An instantiation of the declared constants of `P` in `Q`**: the universe rules of `P`
are among those of `Q`, each declared constant of `P` goes to a closed term of `Q` typed at
the instantiated declared type whenever that type is a type of `Q`, and each root step of
`P` instantiates to a root step of `Q`, its premises to premises of that step. The typing is asked only at a type of `Q`: the rule
for constants types a constant only when its declared type is a type, so a constant
instantiated by itself needs no more than the instantiated formation of its declared type. -/
structure ConstInstance {R R' : Rules Head} (P : ChurchRules R) (Q : ChurchRules R')
    (θ : DeclName → CTm Head 0) : Prop where
  headTyping : ∀ {h u : Head}, R.headTyping h u → R'.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → R'.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → R'.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → R'.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → R'.headEq h h'
  typed : ∀ {c : DeclName} {D : CTm Head 0} {u : Head}, P.constantType c = some D →
    CTyped Q .nil (D.instConsts θ) (.head u) → R'.isUniverse u →
      CTyped Q .nil (θ c) (D.instConsts θ)
  steps : ∀ {n : Nat} {l r : CTm Head n}, P.computation.step l r →
    Q.computation.step (l.instConsts θ) (r.instConsts θ)
  requires : ∀ {n : Nat} {l r : CTm Head n} {premises : List (CPremise Head n)},
    P.computation.step l r → P.computation.requires l r premises →
      Q.computation.requires (l.instConsts θ) (r.instConsts θ)
        (premises.map (CPremise.instConsts θ))

/-- **Every derivation instantiates.** -/
theorem CDerivable.instConsts {R R' : Rules Head} {P : ChurchRules R} {Q : ChurchRules R'}
    {θ : DeclName → CTm Head 0} (inst : ConstInstance P Q θ) {statement : CStatement Head}
    (derivation : CDerivable P statement) : CDerivable Q (statement.instConsts θ) := by
  induction derivation with
  | headType h => exact .headType (inst.headTyping h)
  | @var n Γ i =>
      show CTyped Q (Γ.instConsts θ) (.var i) ((Γ.lookup i).instConsts θ)
      rw [CCtx.instConsts_lookup]
      exact .var i
  | @const n Γ name type u declared _ hu ih =>
      show CTyped Q (Γ.instConsts θ) ((θ name).liftClosed) ((type.liftClosed).instConsts θ)
      rw [CTm.instConsts_liftClosed]
      exact (inst.typed declared ih (inst.isUniverse hu)).rename (fun i => i.elim0)
  | piForm _ hu _ hv join ihA ihB =>
      exact .piForm ihA (inst.isUniverse hu) ihB (inst.isUniverse hv) (inst.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      exact .sigmaForm ihA (inst.isUniverse hu) ihB (inst.isUniverse hv) (inst.join join)
  | lamIntro _ hw _ hu _ ihA ihPi ihBody =>
      exact .lamIntro ihA (inst.isUniverse hw) ihPi (inst.isUniverse hu) ihBody
  | @appElim n Γ g a A B _ _ ihF ihA =>
      show CTyped Q (Γ.instConsts θ) (.app (g.instConsts θ) (a.instConsts θ))
        ((CTm.inst0 a B).instConsts θ)
      rw [CTm.instConsts_inst0]
      exact .appElim ihF ihA
  | @pairIntro n Γ a b A B u _ hu _ _ ihS iha ihb =>
      have second : CTyped Q (Γ.instConsts θ) (b.instConsts θ) ((CTm.inst0 a B).instConsts θ) :=
        ihb
      rw [CTm.instConsts_inst0] at second
      exact .pairIntro ihS (inst.isUniverse hu) iha second
  | fstElim _ ih => exact .fstElim ih
  | @sndElim n Γ p A B _ ih =>
      show CTyped Q (Γ.instConsts θ) (.snd (p.instConsts θ))
        ((CTm.inst0 (.fst p) B).instConsts θ)
      rw [CTm.instConsts_inst0]
      exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb => exact .idForm ihA (inst.isUniverse hu) iha ihb
  | reflIntro _ ih => exact .reflIntro ih
  | sub _ _ ihT ihLe => exact .sub ihT ihLe
  | conv _ _ hu ihT ihE => exact .conv ihT ihE (inst.isUniverse hu)
  | refl _ ih => exact .refl ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihE => exact .convEq ih ihE (inst.isUniverse hu)
  | subEq _ _ ih ihLe => exact .subEq ih ihLe
  | headEq e _ _ ih ih' => exact .headEq (inst.headEq e) ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      exact .piCong ihA (inst.isUniverse hu) ihB (inst.isUniverse hv) (inst.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      exact .sigmaCong ihA (inst.isUniverse hu) ihB (inst.isUniverse hv) (inst.join join)
  | idCong _ hu _ _ ihA iha ihb => exact .idCong ihA (inst.isUniverse hu) iha ihb
  | lamCong _ hw _ hu _ ihA ihPi ihBody =>
      exact .lamCong ihA (inst.isUniverse hw) ihPi (inst.isUniverse hu) ihBody
  | @appCong n Γ f g a b A B _ _ ihF ihA =>
      show CEqual Q (Γ.instConsts θ) (.app (f.instConsts θ) (a.instConsts θ))
        (.app (g.instConsts θ) (b.instConsts θ)) ((CTm.inst0 a B).instConsts θ)
      rw [CTm.instConsts_inst0]
      exact .appCong ihF ihA
  | @pairCong n Γ a a' b b' A B u _ hu _ _ ihS iha ihb =>
      have second : CEqual Q (Γ.instConsts θ) (b.instConsts θ) (b'.instConsts θ)
          ((CTm.inst0 a B).instConsts θ) := ihb
      rw [CTm.instConsts_inst0] at second
      exact .pairCong ihS (inst.isUniverse hu) iha second
  | fstCong _ ih => exact .fstCong ih
  | @sndCong n Γ p q A B _ ih =>
      show CEqual Q (Γ.instConsts θ) (.snd (p.instConsts θ)) (.snd (q.instConsts θ))
        ((CTm.inst0 (.fst p) B).instConsts θ)
      rw [CTm.instConsts_inst0]
      exact .sndCong ih
  | reflCong _ ih => exact .reflCong ih
  | @betaPi n Γ A a body B u _ hu _ _ ihPi ihBody iha =>
      show CEqual Q (Γ.instConsts θ) (.app (.lam (A.instConsts θ) (body.instConsts θ))
        (a.instConsts θ)) ((CTm.inst0 a body).instConsts θ) ((CTm.inst0 a B).instConsts θ)
      rw [CTm.instConsts_inst0, CTm.instConsts_inst0]
      exact .betaPi ihPi (inst.isUniverse hu) ihBody iha
  | @betaFst n Γ A a b B u _ hu _ _ ihS iha ihb =>
      have second : CTyped Q (Γ.instConsts θ) (b.instConsts θ) ((CTm.inst0 a B).instConsts θ) :=
        ihb
      rw [CTm.instConsts_inst0] at second
      exact .betaFst ihS (inst.isUniverse hu) iha second
  | @betaSnd n Γ A a b B u _ hu _ _ ihS iha ihb =>
      have second : CTyped Q (Γ.instConsts θ) (b.instConsts θ) ((CTm.inst0 a B).instConsts θ) :=
        ihb
      rw [CTm.instConsts_inst0] at second
      show CEqual Q (Γ.instConsts θ) (.snd (.pair (a.instConsts θ) (b.instConsts θ)))
        (b.instConsts θ) ((CTm.inst0 a B).instConsts θ)
      rw [CTm.instConsts_inst0]
      exact .betaSnd ihS (inst.isUniverse hu) iha second
  | root step requires _ _ _ ihPremises ihL ihR =>
      refine .root (inst.steps step) (inst.requires step requires) (fun premise member => ?_)
        ihL ihR
      obtain ⟨source, mem, rfl⟩ := List.mem_map.1 member
      have instantiated := ihPremises source mem
      rwa [CPremise.statement_instConsts] at instantiated
  | @etaPi n Γ f g A B _ _ _ ihF ihG ihBody =>
      have body : CEqual Q ((Γ.instConsts θ).snoc (A.instConsts θ))
          (.app ((f.rename wk).instConsts θ) (.var 0))
          (.app ((g.rename wk).instConsts θ) (.var 0)) (B.instConsts θ) := ihBody
      rw [CTm.instConsts_rename, CTm.instConsts_rename] at body
      exact .etaPi ihF ihG body
  | @etaSigma n Γ p q A B _ _ _ _ ihP ihQ ihFst ihSnd =>
      have second : CEqual Q (Γ.instConsts θ) (.snd (p.instConsts θ)) (.snd (q.instConsts θ))
          ((CTm.inst0 (.fst p) B).instConsts θ) := ihSnd
      rw [CTm.instConsts_inst0] at second
      exact .etaSigma ihP ihQ ihFst second
  | subEqual _ hu ih => exact .subEqual ih (inst.isUniverse hu)
  | subUniv o => exact .subUniv (inst.cumulative o)
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      exact .subPi ihPi (inst.isUniverse hu) ihPi' (inst.isUniverse hu') ihA (inst.isUniverse hw)
        ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      exact .subSigma ihS (inst.isUniverse hu) ihS' (inst.isUniverse hu') ihA ihB
  | subTrans _ _ ih₁ ih₂ => exact .subTrans ih₁ ih₂

/-- **Formed contexts instantiate.** -/
theorem CCtxFormed.instConsts {R R' : Rules Head} {P : ChurchRules R} {Q : ChurchRules R'}
    {θ : DeclName → CTm Head 0} (inst : ConstInstance P Q θ) {n : Nat} {Γ : CCtx Head n}
    (formed : CCtxFormed P Γ) : CCtxFormed Q (Γ.instConsts θ) := by
  induction formed with
  | nil => exact .nil
  | snoc _ type ih =>
      obtain ⟨u, hu, typing⟩ := type
      exact .snoc ih ⟨u, inst.isUniverse hu, CDerivable.instConsts inst typing⟩

/-- **Equations of types instantiate.** -/
theorem CTypeEq.instConsts {R R' : Rules Head} {P : ChurchRules R} {Q : ChurchRules R'}
    {θ : DeclName → CTm Head 0} (inst : ConstInstance P Q θ) {n : Nat} {Γ : CCtx Head n}
    {A B : CTm Head n} (equal : CTypeEq P Γ A B) :
    CTypeEq Q (Γ.instConsts θ) (A.instConsts θ) (B.instConsts θ) := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, inst.isUniverse hu, CDerivable.instConsts inst e⟩

/-! ## Constant-free terms -/

namespace CTm

/-- A term in which no constant occurs. -/
def constFree {n : Nat} : CTm Head n → Bool
  | .var _ => true
  | .const _ => false
  | .head _ => true
  | .pi A B => A.constFree && B.constFree
  | .sigma A B => A.constFree && B.constFree
  | .id A a b => A.constFree && a.constFree && b.constFree
  | .lam A b => A.constFree && b.constFree
  | .app f a => f.constFree && a.constFree
  | .pair a b => a.constFree && b.constFree
  | .fst p => p.constFree
  | .snd p => p.constFree
  | .refl a => a.constFree

/-- **Instantiation leaves a constant-free term unchanged.** -/
theorem instConsts_of_constFree (θ : DeclName → CTm Head 0) {n : Nat} {t : CTm Head n}
    (free : t.constFree = true) : t.instConsts θ = t := by
  induction t with
  | var => rfl
  | const => cases free
  | head => rfl
  | pi A B ihA ihB =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [instConsts, ihA free.1, ihB free.2]
  | sigma A B ihA ihB =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [instConsts, ihA free.1, ihB free.2]
  | id A a b ihA iha ihb =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [instConsts, ihA free.1.1, iha free.1.2, ihb free.2]
  | lam A b ihA ihb =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [instConsts, ihA free.1, ihb free.2]
  | app f a ihf iha =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [instConsts, ihf free.1, iha free.2]
  | pair a b iha ihb =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [instConsts, iha free.1, ihb free.2]
  | fst p ih => simp only [instConsts, ih free]
  | snd p ih => simp only [instConsts, ih free]
  | refl a ih => simp only [instConsts, ih free]

/-- Renaming keeps a term constant-free. -/
theorem constFree_rename {n m : Nat} (ρ : Ren n m) (t : CTm Head n) :
    (t.rename ρ).constFree = t.constFree := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [rename, constFree, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, constFree, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, constFree, ihA, iha, ihb]
  | lam A b ihA ihb => simp only [rename, constFree, ihA, ihb]
  | app f a ihf iha => simp only [rename, constFree, ihf, iha]
  | pair a b iha ihb => simp only [rename, constFree, iha, ihb]
  | fst p ih => simp only [rename, constFree, ih]
  | snd p ih => simp only [rename, constFree, ih]
  | refl a ih => simp only [rename, constFree, ih]

/-- Substituting constant-free terms keeps a term constant-free. -/
theorem constFree_subst {n m : Nat} {σ : CSub Head n m} (hσ : ∀ i, (σ i).constFree = true)
    {t : CTm Head n} (free : t.constFree = true) : (t.subst σ).constFree = true := by
  induction t generalizing m with
  | var i => exact hσ i
  | const => cases free
  | head => rfl
  | pi A B ihA ihB =>
      simp only [constFree, Bool.and_eq_true] at free
      have hσ' : ∀ i, (liftSub σ i).constFree = true := fun i =>
        Fin.cases rfl (fun j => (constFree_rename wk (σ j)).trans (hσ j)) i
      simp only [subst, constFree, ihA hσ free.1, ihB hσ' free.2, Bool.and_self]
  | sigma A B ihA ihB =>
      simp only [constFree, Bool.and_eq_true] at free
      have hσ' : ∀ i, (liftSub σ i).constFree = true := fun i =>
        Fin.cases rfl (fun j => (constFree_rename wk (σ j)).trans (hσ j)) i
      simp only [subst, constFree, ihA hσ free.1, ihB hσ' free.2, Bool.and_self]
  | id A a b ihA iha ihb =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [subst, constFree, ihA hσ free.1.1, iha hσ free.1.2, ihb hσ free.2,
        Bool.and_self]
  | lam A b ihA ihb =>
      simp only [constFree, Bool.and_eq_true] at free
      have hσ' : ∀ i, (liftSub σ i).constFree = true := fun i =>
        Fin.cases rfl (fun j => (constFree_rename wk (σ j)).trans (hσ j)) i
      simp only [subst, constFree, ihA hσ free.1, ihb hσ' free.2, Bool.and_self]
  | app f a ihf iha =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [subst, constFree, ihf hσ free.1, iha hσ free.2, Bool.and_self]
  | pair a b iha ihb =>
      simp only [constFree, Bool.and_eq_true] at free
      simp only [subst, constFree, iha hσ free.1, ihb hσ free.2, Bool.and_self]
  | fst p ih => exact ih hσ free
  | snd p ih => exact ih hσ free
  | refl a ih => exact ih hσ free

/-- Opening a binder at a constant-free term keeps a term constant-free. -/
theorem constFree_inst0 {n : Nat} {u : CTm Head n} {body : CTm Head (n + 1)}
    (hu : u.constFree = true) (hb : body.constFree = true) :
    (inst0 u body).constFree = true :=
  constFree_subst (fun i => Fin.cases hu (fun _ => rfl) i) hb

end CTm

namespace CCtx

/-- A context in which no constant occurs. -/
def constFree : {n : Nat} → CCtx Head n → Bool
  | _, .nil => true
  | _, .snoc Γ A => Γ.constFree && A.constFree

/-- The type of a variable of a constant-free context is constant-free. -/
theorem constFree_lookup : ∀ {n : Nat} {Γ : CCtx Head n}, Γ.constFree = true →
    ∀ i : Fin n, (Γ.lookup i).constFree = true
  | _, .nil, _, i => i.elim0
  | _, .snoc Γ A, free, i => by
      simp only [constFree, Bool.and_eq_true] at free
      refine Fin.cases ?_ ?_ i
      · exact (CTm.constFree_rename wk A).trans free.2
      · intro j
        exact (CTm.constFree_rename wk (Γ.lookup j)).trans (constFree_lookup free.1 j)

/-- Instantiation leaves a constant-free context unchanged. -/
theorem instConsts_of_constFree (θ : DeclName → CTm Head 0) :
    ∀ {n : Nat} {Γ : CCtx Head n}, Γ.constFree = true → Γ.instConsts θ = Γ
  | _, .nil, _ => rfl
  | _, .snoc Γ A, free => by
      simp only [constFree, Bool.and_eq_true] at free
      simp only [instConsts, instConsts_of_constFree θ free.1,
        CTm.instConsts_of_constFree θ free.2]

end CCtx

/-- The context of a statement is constant-free. -/
def CStatement.ctxConstFree : CStatement Head → Bool
  | .typing Γ _ _ => Γ.constFree
  | .equality Γ _ _ _ => Γ.constFree
  | .sub Γ _ _ => Γ.constFree

/-- The terms of a statement are constant-free. -/
def CStatement.termsConstFree : CStatement Head → Bool
  | .typing _ t A => t.constFree && A.constFree
  | .equality _ a b A => a.constFree && b.constFree && A.constFree
  | .sub _ A B => A.constFree && B.constFree

section ConstFree

variable {R : Rules Head} {P : ChurchRules R}

/-- **In a package without declared constants and root steps, a derivable statement over a
constant-free context mentions no constant.** -/
theorem CDerivable.constFree (noConstants : ∀ c, P.constantType c = none)
    (noSteps : ∀ {n : Nat} {l r : CTm Head n}, ¬ P.computation.step l r)
    {statement : CStatement Head} (derivation : CDerivable P statement) :
    statement.ctxConstFree = true → statement.termsConstFree = true := by
  induction derivation with
  | headType h => exact fun _ => rfl
  | @var n Γ i =>
      intro free
      exact Bool.and_eq_true_iff.2 ⟨rfl, CCtx.constFree_lookup free i⟩
  | const declared _ _ _ =>
      rw [noConstants] at declared
      cases declared
  | piForm _ _ _ _ _ ihA ihB =>
      intro free
      have hA := (Bool.and_eq_true_iff.1 (ihA free)).1
      have hB := (Bool.and_eq_true_iff.1 (ihB (Bool.and_eq_true_iff.2 ⟨free, hA⟩))).1
      simp only [CStatement.termsConstFree, CTm.constFree, hA, hB, Bool.and_self]
  | sigmaForm _ _ _ _ _ ihA ihB =>
      intro free
      have hA := (Bool.and_eq_true_iff.1 (ihA free)).1
      have hB := (Bool.and_eq_true_iff.1 (ihB (Bool.and_eq_true_iff.2 ⟨free, hA⟩))).1
      simp only [CStatement.termsConstFree, CTm.constFree, hA, hB, Bool.and_self]
  | lamIntro _ _ _ _ _ ihA ihPi ihBody =>
      intro free
      have hA := (Bool.and_eq_true_iff.1 (ihA free)).1
      have hPi := (Bool.and_eq_true_iff.1 (ihPi free)).1
      have hb := Bool.and_eq_true_iff.1 (ihBody (Bool.and_eq_true_iff.2 ⟨free, hA⟩))
      simp only [CTm.constFree, Bool.and_eq_true] at hPi
      simp only [CStatement.termsConstFree, CTm.constFree, hA, hb.1, hPi.2, Bool.and_self]
  | appElim _ _ ihF ihA =>
      intro free
      have hF := Bool.and_eq_true_iff.1 (ihF free)
      have ha := (Bool.and_eq_true_iff.1 (ihA free)).1
      have hPi := hF.2
      simp only [CTm.constFree, Bool.and_eq_true] at hPi
      simp only [CStatement.termsConstFree, CTm.constFree, hF.1, ha, CTm.constFree_inst0 ha hPi.2,
        Bool.and_self]
  | pairIntro _ _ _ _ ihS iha ihb =>
      intro free
      have hS := (Bool.and_eq_true_iff.1 (ihS free)).1
      have ha := (Bool.and_eq_true_iff.1 (iha free)).1
      have hb := (Bool.and_eq_true_iff.1 (ihb free)).1
      simp only [CStatement.termsConstFree, CTm.constFree, ha, hb, Bool.and_self]
      exact hS
  | fstElim _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have hS := h.2
      simp only [CTm.constFree, Bool.and_eq_true] at hS
      simp only [CStatement.termsConstFree, CTm.constFree, h.1, hS.1, Bool.and_self]
  | @sndElim n Γ p A B _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have hS := h.2
      simp only [CTm.constFree, Bool.and_eq_true] at hS
      have hfst : (CTm.fst p).constFree = true := h.1
      simp only [CStatement.termsConstFree, CTm.constFree, h.1, CTm.constFree_inst0 hfst hS.2,
        Bool.and_self]
  | idForm _ _ _ _ ihA iha ihb =>
      intro free
      have hA := (Bool.and_eq_true_iff.1 (ihA free)).1
      have ha := (Bool.and_eq_true_iff.1 (iha free)).1
      have hb := (Bool.and_eq_true_iff.1 (ihb free)).1
      simp only [CStatement.termsConstFree, CTm.constFree, hA, ha, hb, Bool.and_self]
  | reflIntro _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      simp only [CStatement.termsConstFree, CTm.constFree, h.1, h.2, Bool.and_self]
  | sub _ _ ihT ihLe =>
      intro free
      have ht := (Bool.and_eq_true_iff.1 (ihT free)).1
      have hB := (Bool.and_eq_true_iff.1 (ihLe free)).2
      simp only [CStatement.termsConstFree, ht, hB, Bool.and_self]
  | conv _ _ _ ihT ihE =>
      intro free
      have ht := (Bool.and_eq_true_iff.1 (ihT free)).1
      have hB := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihE free)).1).2
      simp only [CStatement.termsConstFree, ht, hB, Bool.and_self]
  | refl _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      simp only [CStatement.termsConstFree, h.1, h.2, Bool.and_self]
  | symm _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have h' := Bool.and_eq_true_iff.1 h.1
      simp only [CStatement.termsConstFree, h'.1, h'.2, h.2, Bool.and_self]
  | trans _ _ ih₁ ih₂ =>
      intro free
      have h₁ := Bool.and_eq_true_iff.1 (ih₁ free)
      have h₂ := Bool.and_eq_true_iff.1 (ih₂ free)
      have h₁' := Bool.and_eq_true_iff.1 h₁.1
      have h₂' := Bool.and_eq_true_iff.1 h₂.1
      simp only [CStatement.termsConstFree, h₁'.1, h₂'.2, h₁.2, Bool.and_self]
  | convEq _ _ _ ih ihE =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have hE := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihE free)).1
      simp only [CStatement.termsConstFree, h.1, hE.2, Bool.and_self]
  | subEq _ _ ih ihLe =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have hB := (Bool.and_eq_true_iff.1 (ihLe free)).2
      simp only [CStatement.termsConstFree, h.1, hB, Bool.and_self]
  | @headEq n Γ h h' A _ _ _ ih _ =>
      intro free
      have hA : A.constFree = true := ih free
      simp only [CStatement.termsConstFree, CTm.constFree, hA, Bool.and_self]
  | piCong _ _ _ _ _ ihA ihB =>
      intro free
      have hA := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihA free)).1
      have hB := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1
        (ihB (Bool.and_eq_true_iff.2 ⟨free, hA.1⟩))).1
      simp only [CStatement.termsConstFree, CTm.constFree, hA.1, hA.2, hB.1, hB.2, Bool.and_self]
  | sigmaCong _ _ _ _ _ ihA ihB =>
      intro free
      have hA := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihA free)).1
      have hB := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1
        (ihB (Bool.and_eq_true_iff.2 ⟨free, hA.1⟩))).1
      simp only [CStatement.termsConstFree, CTm.constFree, hA.1, hA.2, hB.1, hB.2, Bool.and_self]
  | idCong _ _ _ _ ihA iha ihb =>
      intro free
      have hA := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihA free)).1
      have ha := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (iha free)).1
      have hb := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihb free)).1
      simp only [CStatement.termsConstFree, CTm.constFree, hA.1, hA.2, ha.1, ha.2, hb.1, hb.2,
        Bool.and_self]
  | lamCong _ _ _ _ _ ihA ihPi ihBody =>
      intro free
      have hA := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihA free)).1
      have hPi := (Bool.and_eq_true_iff.1 (ihPi free)).1
      have hb := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1
        (ihBody (Bool.and_eq_true_iff.2 ⟨free, hA.1⟩))).1
      simp only [CTm.constFree, Bool.and_eq_true] at hPi
      simp only [CStatement.termsConstFree, CTm.constFree, hA.1, hA.2, hb.1, hb.2, hPi.2,
        Bool.and_self]
  | appCong _ _ ihF ihA =>
      intro free
      have hF := Bool.and_eq_true_iff.1 (ihF free)
      have hF' := Bool.and_eq_true_iff.1 hF.1
      have hA := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihA free)).1
      have hPi := hF.2
      simp only [CTm.constFree, Bool.and_eq_true] at hPi
      simp only [CStatement.termsConstFree, CTm.constFree, hF'.1, hF'.2, hA.1, hA.2,
        CTm.constFree_inst0 hA.1 hPi.2, Bool.and_self]
  | pairCong _ _ _ _ ihS iha ihb =>
      intro free
      have hS := (Bool.and_eq_true_iff.1 (ihS free)).1
      have ha := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (iha free)).1
      have hb := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ihb free)).1
      simp only [CStatement.termsConstFree, CTm.constFree, ha.1, ha.2, hb.1, hb.2, Bool.and_self]
      exact hS
  | fstCong _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have h' := Bool.and_eq_true_iff.1 h.1
      have hS := h.2
      simp only [CTm.constFree, Bool.and_eq_true] at hS
      simp only [CStatement.termsConstFree, CTm.constFree, h'.1, h'.2, hS.1, Bool.and_self]
  | @sndCong n Γ p q A B _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have h' := Bool.and_eq_true_iff.1 h.1
      have hS := h.2
      simp only [CTm.constFree, Bool.and_eq_true] at hS
      have hfst : (CTm.fst p).constFree = true := h'.1
      simp only [CStatement.termsConstFree, CTm.constFree, h'.1, h'.2,
        CTm.constFree_inst0 hfst hS.2, Bool.and_self]
  | reflCong _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (ih free)
      have h' := Bool.and_eq_true_iff.1 h.1
      simp only [CStatement.termsConstFree, CTm.constFree, h'.1, h'.2, h.2, Bool.and_self]
  | betaPi _ _ _ _ ihPi ihBody iha =>
      intro free
      have hPi := (Bool.and_eq_true_iff.1 (ihPi free)).1
      simp only [CTm.constFree, Bool.and_eq_true] at hPi
      have hb := Bool.and_eq_true_iff.1 (ihBody (Bool.and_eq_true_iff.2 ⟨free, hPi.1⟩))
      have ha := (Bool.and_eq_true_iff.1 (iha free)).1
      simp only [CStatement.termsConstFree, CTm.constFree, hPi.1, hb.1, ha,
        CTm.constFree_inst0 ha hb.1, CTm.constFree_inst0 ha hPi.2, Bool.and_self]
  | betaFst _ _ _ _ _ iha ihb =>
      intro free
      have ha := Bool.and_eq_true_iff.1 (iha free)
      have hb := (Bool.and_eq_true_iff.1 (ihb free)).1
      simp only [CStatement.termsConstFree, CTm.constFree, ha.1, ha.2, hb, Bool.and_self]
  | betaSnd _ _ _ _ _ iha ihb =>
      intro free
      have ha := (Bool.and_eq_true_iff.1 (iha free)).1
      have hb := Bool.and_eq_true_iff.1 (ihb free)
      simp only [CStatement.termsConstFree, CTm.constFree, ha, hb.1, hb.2, Bool.and_self]
  | root step _ _ _ _ => exact (noSteps step).elim
  | etaPi _ _ _ ihF ihG _ =>
      intro free
      have hF := Bool.and_eq_true_iff.1 (ihF free)
      have hG := (Bool.and_eq_true_iff.1 (ihG free)).1
      simp only [CStatement.termsConstFree, hF.1, hG, hF.2, Bool.and_self]
  | etaSigma _ _ _ _ ihP ihQ _ _ =>
      intro free
      have hP := Bool.and_eq_true_iff.1 (ihP free)
      have hQ := (Bool.and_eq_true_iff.1 (ihQ free)).1
      simp only [CStatement.termsConstFree, hP.1, hQ, hP.2, Bool.and_self]
  | subEqual _ _ ih =>
      intro free
      have h := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (ih free)).1
      simp only [CStatement.termsConstFree, h.1, h.2, Bool.and_self]
  | subUniv _ => exact fun _ => rfl
  | subPi _ _ _ _ _ _ _ ihPi ihPi' _ _ =>
      intro free
      have h := (Bool.and_eq_true_iff.1 (ihPi free)).1
      have h' := (Bool.and_eq_true_iff.1 (ihPi' free)).1
      simp only [CStatement.termsConstFree, h, h', Bool.and_self]
  | subSigma _ _ _ _ _ _ ihS ihS' _ _ =>
      intro free
      have h := (Bool.and_eq_true_iff.1 (ihS free)).1
      have h' := (Bool.and_eq_true_iff.1 (ihS' free)).1
      simp only [CStatement.termsConstFree, h, h', Bool.and_self]
  | subTrans _ _ ih₁ ih₂ =>
      intro free
      have h₁ := Bool.and_eq_true_iff.1 (ih₁ free)
      have h₂ := Bool.and_eq_true_iff.1 (ih₂ free)
      simp only [CStatement.termsConstFree, h₁.1, h₂.2, Bool.and_self]

/-- **A formed context of a package without declared constants and root steps mentions no
constant.** -/
theorem CCtxFormed.constFree (noConstants : ∀ c, P.constantType c = none)
    (noSteps : ∀ {n : Nat} {l r : CTm Head n}, ¬ P.computation.step l r) {n : Nat}
    {Γ : CCtx Head n} (formed : CCtxFormed P Γ) : Γ.constFree = true := by
  induction formed with
  | nil => rfl
  | snoc _ type ih =>
      obtain ⟨u, _, typing⟩ := type
      exact Bool.and_eq_true_iff.2
        ⟨ih, (Bool.and_eq_true_iff.1 (CDerivable.constFree noConstants noSteps typing ih)).1⟩

end ConstFree

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
