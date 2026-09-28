import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DecoderComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates

/-!
# Renaming declared constants

A map `f` on declared names acts on terms, contexts and statements by renaming
every constant (`Tm.mapConst`). It commutes with renaming and substitution of
variables, with closed lifting and with spines, and it fixes every term whose
constants it fixes (`Tm.mapConst_eq_self`).

**Renaming derivations.** A renaming of the constants of one rule package into
another (`RulesRenaming`) keeps the universe rules, sends each declared constant
to a constant declared at the renamed type, and each root step to a root step
between the renamed sides. Every derivable statement of the first package is
then derivable in the second once renamed (`Derivable.mapConst`).

**Renaming reductions.** When root steps are sent to root steps, every step of
the directed reduction is (`Reduces.mapConst`), so strong normalization pulls
back along the renaming (`SN.of_mapConst`).

**The declared computations commute with renaming.** The eliminator's linear rule
at a constant is sent to the rule at the renamed constant, and a recursor's rules
to the rules of the renamed recursor when the constructors are fixed. A
definition by one equation, a definition by structural recursion, and the
decoding of codes are sent to themselves when the renaming fixes the names and
right-hand sides they mention.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

/-! ## Terms and contexts -/

/-- Functorial action on declared names. -/
def Tm.mapConst (f : DeclName → DeclName) : {n : Nat} → Tm Head n → Tm Head n
  | _, .var i => .var i
  | _, .const c => .const (f c)
  | _, .head h => .head h
  | _, .pi A B => .pi (mapConst f A) (mapConst f B)
  | _, .sigma A B => .sigma (mapConst f A) (mapConst f B)
  | _, .id A a b => .id (mapConst f A) (mapConst f a) (mapConst f b)
  | _, .lam body => .lam (mapConst f body)
  | _, .app g a => .app (mapConst f g) (mapConst f a)
  | _, .pair a b => .pair (mapConst f a) (mapConst f b)
  | _, .fst p => .fst (mapConst f p)
  | _, .snd p => .snd (mapConst f p)
  | _, .refl a => .refl (mapConst f a)

/-- Whether every declared name of a term satisfies `p`. -/
def Tm.allConstants (p : DeclName → Bool) : {n : Nat} → Tm Head n → Bool
  | _, .var _ => true
  | _, .const c => p c
  | _, .head _ => true
  | _, .pi A B => allConstants p A && allConstants p B
  | _, .sigma A B => allConstants p A && allConstants p B
  | _, .id A a b => allConstants p A && allConstants p a && allConstants p b
  | _, .lam body => allConstants p body
  | _, .app g a => allConstants p g && allConstants p a
  | _, .pair a b => allConstants p a && allConstants p b
  | _, .fst q => allConstants p q
  | _, .snd q => allConstants p q
  | _, .refl a => allConstants p a

section Terms

variable (f : DeclName → DeclName)

@[simp] theorem Tm.mapConst_id {n : Nat} (t : Tm Head n) : t.mapConst (fun c => c) = t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [mapConst, ihA, ihB]
  | sigma A B ihA ihB => simp only [mapConst, ihA, ihB]
  | id A a b ihA iha ihb => simp only [mapConst, ihA, iha, ihb]
  | lam body ih => simp only [mapConst, ih]
  | app g a ihg iha => simp only [mapConst, ihg, iha]
  | pair a b iha ihb => simp only [mapConst, iha, ihb]
  | fst p ih => simp only [mapConst, ih]
  | snd p ih => simp only [mapConst, ih]
  | refl a ih => simp only [mapConst, ih]

/-- A renaming fixes a term whose constants it fixes. -/
theorem Tm.mapConst_eq_self {p : DeclName → Bool} (fixes : ∀ c, p c = true → f c = c) :
    ∀ {n : Nat} {t : Tm Head n}, t.allConstants p = true → t.mapConst f = t
  | _, .var _, _ => rfl
  | _, .const c, h => congrArg Tm.const (fixes c h)
  | _, .head _, _ => rfl
  | _, .pi A B, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [mapConst, mapConst_eq_self fixes h.1, mapConst_eq_self fixes h.2]
  | _, .sigma A B, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [mapConst, mapConst_eq_self fixes h.1, mapConst_eq_self fixes h.2]
  | _, .id A a b, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [mapConst, mapConst_eq_self fixes h.1.1, mapConst_eq_self fixes h.1.2,
        mapConst_eq_self fixes h.2]
  | _, .lam body, h => by
      simp only [allConstants] at h
      simp only [mapConst, mapConst_eq_self fixes h]
  | _, .app g a, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [mapConst, mapConst_eq_self fixes h.1, mapConst_eq_self fixes h.2]
  | _, .pair a b, h => by
      simp only [allConstants, Bool.and_eq_true] at h
      simp only [mapConst, mapConst_eq_self fixes h.1, mapConst_eq_self fixes h.2]
  | _, .fst q, h => by
      simp only [allConstants] at h
      simp only [mapConst, mapConst_eq_self fixes h]
  | _, .snd q, h => by
      simp only [allConstants] at h
      simp only [mapConst, mapConst_eq_self fixes h]
  | _, .refl a, h => by
      simp only [allConstants] at h
      simp only [mapConst, mapConst_eq_self fixes h]

/-- Renaming constants commutes with renaming variables. -/
@[simp] theorem Tm.mapConst_rename {n m : Nat} (ρ : Ren n m) (t : Tm Head n) :
    (rename ρ t).mapConst f = rename ρ (t.mapConst f) := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [rename, mapConst, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, mapConst, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, mapConst, ihA, iha, ihb]
  | lam body ih => simp only [rename, mapConst, ih]
  | app g a ihg iha => simp only [rename, mapConst, ihg, iha]
  | pair a b iha ihb => simp only [rename, mapConst, iha, ihb]
  | fst p ih => simp only [rename, mapConst, ih]
  | snd p ih => simp only [rename, mapConst, ih]
  | refl a ih => simp only [rename, mapConst, ih]

theorem Tm.mapConst_liftSub {n m : Nat} (σ : Sub Head n m) :
    (fun i => (liftSub σ i).mapConst f) = liftSub (fun i => (σ i).mapConst f) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact Tm.mapConst_rename f wk (σ j)

/-- Renaming constants commutes with substitution. -/
@[simp] theorem Tm.mapConst_subst {n m : Nat} (σ : Sub Head n m) (t : Tm Head n) :
    (subst σ t).mapConst f = subst (fun i => (σ i).mapConst f) (t.mapConst f) := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [subst, mapConst, ihA, ihB, Tm.mapConst_liftSub]
  | sigma A B ihA ihB => simp only [subst, mapConst, ihA, ihB, Tm.mapConst_liftSub]
  | id A a b ihA iha ihb => simp only [subst, mapConst, ihA, iha, ihb]
  | lam body ih => simp only [subst, mapConst, ih, Tm.mapConst_liftSub]
  | app g a ihg iha => simp only [subst, mapConst, ihg, iha]
  | pair a b iha ihb => simp only [subst, mapConst, iha, ihb]
  | fst p ih => simp only [subst, mapConst, ih]
  | snd p ih => simp only [subst, mapConst, ih]
  | refl a ih => simp only [subst, mapConst, ih]

@[simp] theorem Tm.mapConst_inst0 {n : Nat} (u : Tm Head n) (body : Tm Head (n + 1)) :
    (inst0 u body).mapConst f = inst0 (u.mapConst f) (body.mapConst f) := by
  rw [inst0, inst0, Tm.mapConst_subst]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem Tm.mapConst_liftClosed {n : Nat} (t : Tm Head 0) :
    (liftClosed t : Tm Head n).mapConst f = liftClosed (t.mapConst f) :=
  Tm.mapConst_rename f Fin.elim0 t

/-- Rename the constants of every context entry. -/
def Ctx.mapConst : {n : Nat} → Ctx Head n → Ctx Head n
  | _, .nil => .nil
  | _, .snoc Γ A => .snoc (Ctx.mapConst Γ) (A.mapConst f)

/-- Context lookup commutes with renaming constants. -/
@[simp] theorem Ctx.lookup_mapConst {n : Nat} (Γ : Ctx Head n) (i : Fin n) :
    Ctx.lookup (Γ.mapConst f) i = (Ctx.lookup Γ i).mapConst f := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A ih =>
      refine Fin.cases ?_ ?_ i
      · exact (Tm.mapConst_rename f wk A).symm
      · intro j
        change rename wk (Ctx.lookup (Γ.mapConst f) j) = (rename wk (Ctx.lookup Γ j)).mapConst f
        rw [ih, Tm.mapConst_rename]

@[simp] theorem Ctx.mapConst_id {n : Nat} (Γ : Ctx Head n) : Γ.mapConst (fun c => c) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp only [Ctx.mapConst, ih, Tm.mapConst_id]

end Terms

namespace TypedEquality

/-! ## Statements and derivations -/

/-- A statement with its constants renamed. -/
def Statement.mapConst (f : DeclName → DeclName) : Statement Head → Statement Head
  | .typing Γ t A => .typing (Γ.mapConst f) (t.mapConst f) (A.mapConst f)
  | .equality Γ a b A => .equality (Γ.mapConst f) (a.mapConst f) (b.mapConst f) (A.mapConst f)
  | .sub Γ A B => .sub (Γ.mapConst f) (A.mapConst f) (B.mapConst f)

/-- **A renaming of the constants of one rule package into another**: the
universe rules are kept, each declared constant is sent to a constant declared at
the renamed type, and each root step to a root step between the renamed sides. -/
structure RulesRenaming (R R' : Rules Head) (f : DeclName → DeclName) : Prop where
  headTyping : ∀ {h u : Head}, R.headTyping h u → R'.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → R'.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → R'.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → R'.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → R'.headEq h h'
  constantType : ∀ {name : DeclName} {type : Tm Head 0},
    R.constantType name = some type → R'.constantType (f name) = some (type.mapConst f)
  computation : ∀ {n : Nat} {l r : Tm Head n},
    R.computation.step l r → R'.computation.step (l.mapConst f) (r.mapConst f)

/-- **Renaming derivations**: every derivable statement of a package is derivable,
renamed, in a package it renames into. -/
theorem Derivable.mapConst {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) {st : Statement Head} (derivation : Derivable R st) :
    Derivable R' (st.mapConst f) := by
  induction derivation with
  | headType typing => exact .headType (ren.headTyping typing)
  | @var n Γ i =>
      simp only [Statement.mapConst, Tm.mapConst]
      rw [← Ctx.lookup_mapConst]
      exact .var i
  | const declared _ hu ihType =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_liftClosed, Ctx.mapConst]
        at ihType ⊢
      exact .const (ren.constantType declared) ihType (ren.isUniverse hu)
  | piForm _ hu _ hv join ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihA ihB ⊢
      exact .piForm ihA (ren.isUniverse hu) ihB (ren.isUniverse hv) (ren.join join)
  | sigmaForm _ hu _ hv join ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihA ihB ⊢
      exact .sigmaForm ihA (ren.isUniverse hu) ihB (ren.isUniverse hv)
        (ren.join join)
  | lamIntro _ hu _ ihPi ihBody =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihPi ihBody ⊢
      exact .lamIntro ihPi (ren.isUniverse hu) ihBody
  | appElim _ _ ihF ihA =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ihF ihA ⊢
      exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ihS ihA ihB ⊢
      exact .pairIntro ihS (ren.isUniverse hu) ihA ihB
  | fstElim _ ih =>
      simp only [Statement.mapConst, Tm.mapConst] at ih ⊢
      exact .fstElim ih
  | sndElim _ ih =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ih ⊢
      exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb =>
      simp only [Statement.mapConst, Tm.mapConst] at ihA iha ihb ⊢
      exact .idForm ihA (ren.isUniverse hu) iha ihb
  | reflIntro _ ih =>
      simp only [Statement.mapConst, Tm.mapConst] at ih ⊢
      exact .reflIntro ih
  | sub _ _ ihT ihLe =>
      simp only [Statement.mapConst] at ihT ihLe ⊢
      exact .sub ihT ihLe
  | conv _ _ hu ihT ihE =>
      simp only [Statement.mapConst, Tm.mapConst] at ihT ihE ⊢
      exact .conv ihT ihE (ren.isUniverse hu)
  | refl _ ih =>
      simp only [Statement.mapConst] at ih ⊢
      exact .refl ih
  | symm _ ih =>
      simp only [Statement.mapConst] at ih ⊢
      exact .symm ih
  | trans _ _ ih₁ ih₂ =>
      simp only [Statement.mapConst] at ih₁ ih₂ ⊢
      exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihT =>
      simp only [Statement.mapConst, Tm.mapConst] at ih ihT ⊢
      exact .convEq ih ihT (ren.isUniverse hu)
  | subEq _ _ ihE ihLe =>
      simp only [Statement.mapConst] at ihE ihLe ⊢
      exact .subEq ihE ihLe
  | headEq same _ _ ih ih' =>
      simp only [Statement.mapConst, Tm.mapConst] at ih ih' ⊢
      exact .headEq (ren.headEq same) ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihA ihB ⊢
      exact .piCong ihA (ren.isUniverse hu) ihB (ren.isUniverse hv) (ren.join join)
  | sigmaCong _ hu _ hv join ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihA ihB ⊢
      exact .sigmaCong ihA (ren.isUniverse hu) ihB (ren.isUniverse hv)
        (ren.join join)
  | idCong _ hu _ _ ihA iha ihb =>
      simp only [Statement.mapConst, Tm.mapConst] at ihA iha ihb ⊢
      exact .idCong ihA (ren.isUniverse hu) iha ihb
  | lamCong _ hu _ ihPi ihBody =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihPi ihBody ⊢
      exact .lamCong ihPi (ren.isUniverse hu) ihBody
  | appCong _ _ ihF ihA =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ihF ihA ⊢
      exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ihS ihA ihB ⊢
      exact .pairCong ihS (ren.isUniverse hu) ihA ihB
  | fstCong _ ih =>
      simp only [Statement.mapConst, Tm.mapConst] at ih ⊢
      exact .fstCong ih
  | sndCong _ ih =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ih ⊢
      exact .sndCong ih
  | reflCong _ ih =>
      simp only [Statement.mapConst, Tm.mapConst] at ih ⊢
      exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody ihA =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0, Ctx.mapConst]
        at ihPi ihBody ihA ⊢
      exact .betaPi ihPi (ren.isUniverse hu) ihBody ihA
  | betaFst _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ihS ihA ihB ⊢
      exact .betaFst ihS (ren.isUniverse hu) ihA ihB
  | betaSnd _ hu _ _ ihS ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ihS ihA ihB ⊢
      exact .betaSnd ihS (ren.isUniverse hu) ihA ihB
  | root step _ _ ihL ihR =>
      simp only [Statement.mapConst] at ihL ihR ⊢
      exact .root (ren.computation step) ihL ihR
  | etaPi _ _ _ ihF ihG ihApps =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_rename, Ctx.mapConst]
        at ihF ihG ihApps ⊢
      exact .etaPi ihF ihG ihApps
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      simp only [Statement.mapConst, Tm.mapConst, Tm.mapConst_inst0] at ihP ihQ ihFst ihSnd ⊢
      exact .etaSigma ihP ihQ ihFst ihSnd
  | subEqual _ hu ih =>
      simp only [Statement.mapConst, Tm.mapConst] at ih ⊢
      exact .subEqual ih (ren.isUniverse hu)
  | subUniv c =>
      simp only [Statement.mapConst, Tm.mapConst]
      exact .subUniv (ren.cumulative c)
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihPi ihPi' ihA ihB ⊢
      exact .subPi ihPi (ren.isUniverse hu) ihPi' (ren.isUniverse hu') ihA
        (ren.isUniverse hw) ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      simp only [Statement.mapConst, Tm.mapConst, Ctx.mapConst] at ihS ihS' ihA ihB ⊢
      exact .subSigma ihS (ren.isUniverse hu) ihS' (ren.isUniverse hu') ihA ihB
  | subTrans _ _ ih₁ ih₂ =>
      simp only [Statement.mapConst] at ih₁ ih₂ ⊢
      exact .subTrans ih₁ ih₂

theorem Typed.mapConst {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typed : Typed R Γ t A) : Typed R' (Γ.mapConst f) (t.mapConst f) (A.mapConst f) :=
  Derivable.mapConst ren typed

theorem Equal.mapConst {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (equal : Equal R Γ a b A) :
    Equal R' (Γ.mapConst f) (a.mapConst f) (b.mapConst f) (A.mapConst f) :=
  Derivable.mapConst ren equal

namespace Normalization

theorem CtxFormed.mapConst {R R' : Rules Head} {f : DeclName → DeclName}
    (ren : RulesRenaming R R' f) :
    ∀ {n : Nat} {Γ : Ctx Head n}, CtxFormed R Γ → CtxFormed R' (Γ.mapConst f)
  | _, _, .nil => .nil
  | _, _, .snoc formed ⟨u, hu, typed⟩ =>
      .snoc (CtxFormed.mapConst ren formed)
        ⟨u, ren.isUniverse hu, typed.mapConst ren⟩

/-! ## Spines -/

theorem Tm.mapConst_appSpine (f : DeclName → DeclName) {n : Nat} (g : Tm Head n) :
    ∀ as : List (Tm Head n),
      (appSpine g as).mapConst f = appSpine (g.mapConst f) (as.map (Tm.mapConst f))
  | [] => rfl
  | a :: as => Tm.mapConst_appSpine f (.app g a) as

end Normalization

/-! ## Reductions -/

namespace StrongNormalization

open Normalization

/-- A step of one package's directed reduction, renamed, is a step of another's
whose root steps contain the renamed root steps. -/
theorem Reduces.mapConst {R R' : Rules Head} {f : DeclName → DeclName}
    (roots : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R'.computation.step (l.mapConst f) (r.mapConst f)) :
    ∀ {n : Nat} {t u : Tm Head n}, Reduces R t u → Reduces R' (t.mapConst f) (u.mapConst f)
  | _, _, _, .betaPi body a => by
      simp only [Tm.mapConst, Tm.mapConst_inst0]
      exact .betaPi _ _
  | _, _, _, .betaSigmaFst a b => .betaSigmaFst _ _
  | _, _, _, .betaSigmaSnd a b => .betaSigmaSnd _ _
  | _, _, _, .head same => nomatch same
  | _, _, _, .root step => .root (roots step)
  | _, _, _, .congPiDom h => .congPiDom (Reduces.mapConst roots h)
  | _, _, _, .congPiCod h => .congPiCod (Reduces.mapConst roots h)
  | _, _, _, .congSigmaDom h => .congSigmaDom (Reduces.mapConst roots h)
  | _, _, _, .congSigmaCod h => .congSigmaCod (Reduces.mapConst roots h)
  | _, _, _, .congIdTy h => .congIdTy (Reduces.mapConst roots h)
  | _, _, _, .congIdLeft h => .congIdLeft (Reduces.mapConst roots h)
  | _, _, _, .congIdRight h => .congIdRight (Reduces.mapConst roots h)
  | _, _, _, .congLam h => .congLam (Reduces.mapConst roots h)
  | _, _, _, .congAppFun h => .congAppFun (Reduces.mapConst roots h)
  | _, _, _, .congAppArg h => .congAppArg (Reduces.mapConst roots h)
  | _, _, _, .congPairFst h => .congPairFst (Reduces.mapConst roots h)
  | _, _, _, .congPairSnd h => .congPairSnd (Reduces.mapConst roots h)
  | _, _, _, .congFst h => .congFst (Reduces.mapConst roots h)
  | _, _, _, .congSnd h => .congSnd (Reduces.mapConst roots h)
  | _, _, _, .congRefl h => .congRefl (Reduces.mapConst roots h)

/-- **Strong normalization pulls back along a renaming** that sends root steps to
root steps: a term whose renaming is strongly normalizing is. -/
theorem SN.of_mapConst {R R' : Rules Head} {f : DeclName → DeclName}
    (roots : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R'.computation.step (l.mapConst f) (r.mapConst f))
    {n : Nat} {t : Tm Head n} (sn : SN R' (t.mapConst f)) : SN R t := by
  have key : ∀ s, SN R' s → ∀ t : Tm Head n, t.mapConst f = s → SN R t := by
    intro s hs
    induction hs with
    | intro s _ ih =>
        intro t ht
        exact SN.intro fun u step => ih (u.mapConst f) (ht ▸ Reduces.mapConst roots step) u rfl
  exact key _ sn t rfl

end StrongNormalization

/-! ## The declared computations along renamings -/

namespace Normalization

open TelescopeAbstraction (applyClosed)

section Computations

variable (f : DeclName → DeclName)

theorem Tm.mapConst_applyClosed {n m : Nat} (Θ : Ctx Head n) (σ : Sub Head n m)
    (t : Tm Head m) :
    (applyClosed Θ σ t).mapConst f =
      applyClosed Θ (fun i => (σ i).mapConst f) (t.mapConst f) := by
  induction Θ with
  | nil => rfl
  | snoc Θ _ ih =>
      simp only [applyClosed, Presentation.Tm.mapConst]
      rw [ih]

/-- The eliminator's linear rule at `J`, renamed, is the rule at the renamed
constant. -/
theorem eliminatorComputation_mapConst {J : DeclName} {n : Nat} {l r : Tm Head n}
    (step : (eliminatorComputation J).step l r) :
    (eliminatorComputation (f J)).step (l.mapConst f) (r.mapConst f) := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ := step
  exact ⟨_, _, _, _, _, _, by rw [Tm.mapConst_appSpine]; rfl, rfl⟩

/-- A definition by one equation is sent to itself by a renaming that fixes its
name and its right-hand side. -/
theorem DefinitionStep.mapConst {g : DeclName} {k : Nat} {Θ : Ctx Head k} {rhs : Tm Head k}
    (fixName : f g = g) (fixRhs : rhs.mapConst f = rhs) {n : Nat} {l r : Tm Head n}
    (step : DefinitionStep g Θ rhs l r) :
    DefinitionStep g Θ rhs (l.mapConst f) (r.mapConst f) := by
  obtain ⟨σ, rfl, rfl⟩ := step
  refine ⟨fun i => (σ i).mapConst f, ?_, ?_⟩
  · rw [Tm.mapConst_applyClosed]
    simp only [Presentation.Tm.mapConst, fixName]
  · rw [Presentation.Tm.mapConst_subst, fixRhs]

theorem Tm.mapConst_recApp {n : Nat} (rec : DeclName) (pre : List (Tm Head n)) (t : Tm Head n) :
    (recApp rec pre t).mapConst f = recApp (f rec) (pre.map (Presentation.Tm.mapConst f))
      (t.mapConst f) := by
  simp only [recApp, Tm.mapConst_appSpine, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- The rules of a recursor, renamed, are the rules of the renamed recursor, when
the renaming fixes the constructors. -/
theorem IotaStep.mapConst {rec : DeclName} {ctors : List (DeclName × List (Field Head))}
    (fixCtors : ∀ entry ∈ ctors, f entry.1 = entry.1) {n : Nat} {l r : Tm Head n}
    (step : IotaStep rec ctors l r) :
    IotaStep (f rec) ctors (l.mapConst f) (r.mapConst f) := by
  obtain ⟨p, ms, i, k, fields, args, mt, hms, hi, has, hm, rfl, rfl⟩ := step
  have fixK : f k = k := fixCtors (k, fields) (List.mem_of_getElem? hi)
  refine ⟨p.mapConst f, ms.map (Presentation.Tm.mapConst f), i, k, fields,
    args.map (Presentation.Tm.mapConst f), mt.mapConst f, by simp [hms], hi, by simp [has],
    by simp [hm], ?_, ?_⟩
  · rw [Tm.mapConst_recApp, Tm.mapConst_appSpine]
    simp only [Presentation.Tm.mapConst, fixK, List.map_cons]
  · rw [Tm.mapConst_appSpine, List.map_append, List.map_map, ← map_recArgs]
    simp only [List.map_map, Function.comp_def, Tm.mapConst_recApp, List.map_cons]

theorem Tm.mapConst_extendSub {n m : Nat} (ρ : Sub Head n m) (values : Nat → Tm Head m) :
    ∀ (b : Nat), (fun ι => (extendSub ρ values b ι).mapConst f) =
      extendSub (fun i => (ρ i).mapConst f) (fun l => (values l).mapConst f) b
  | 0 => rfl
  | b + 1 => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show (extendSub ρ values b i).mapConst f = extendSub _ _ b i
        exact congrFun (Tm.mapConst_extendSub ρ values b) i

theorem Tm.mapConst_getD {n : Nat} (fixDefault : f .anonymous = .anonymous) :
    ∀ (as : List (Tm Head n)) (l : Nat),
      (as.getD l defaultTm).mapConst f = (as.map (Presentation.Tm.mapConst f)).getD l defaultTm
  | [], _ => by simp only [List.getD_nil, defaultTm, Presentation.Tm.mapConst, fixDefault,
      List.map_nil]
  | _ :: _, 0 => rfl
  | _ :: as, l + 1 => Tm.mapConst_getD fixDefault as l

theorem Tm.mapConst_matchSub {m s a : Nat} (fixDefault : f .anonymous = .anonymous)
    (as : List (Tm Head m)) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      (fun ι => (matchSub s a as d σ ι).mapConst f) =
        matchSub s a (as.map (Presentation.Tm.mapConst f)) d (fun i => (σ i).mapConst f)
  | 0, σ => by
      show (fun ι => (extendSub (tailSub σ) (fun l => as.getD l defaultTm) a ι).mapConst f) = _
      rw [Tm.mapConst_extendSub]
      exact congrArg (fun values => extendSub (fun i => (tailSub σ i).mapConst f) values a)
        (funext fun l => Tm.mapConst_getD f fixDefault as l)
  | d + 1, σ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show (matchSub s a as d (tailSub σ) i).mapConst f =
          matchSub s a (as.map (Presentation.Tm.mapConst f)) d
            (tailSub fun i => (σ i).mapConst f) i
        exact congrFun (Tm.mapConst_matchSub fixDefault as d (tailSub σ)) i

theorem Tm.mapConst_replaceScrut {m s : Nat} (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      (fun ι => (replaceScrut s x d σ ι).mapConst f) =
        replaceScrut s (x.mapConst f) d (fun i => (σ i).mapConst f)
  | 0, _ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · rfl
  | d + 1, σ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show (replaceScrut s x d (tailSub σ) i).mapConst f =
          replaceScrut s (x.mapConst f) d (tailSub fun i => (σ i).mapConst f) i
        exact congrFun (Tm.mapConst_replaceScrut x d (tailSub σ)) i

theorem Tm.mapConst_callSub (fixDefault : f .anonymous = .anonymous) (s a d l : Nat) :
    (fun ι => (callSub (Head := Head) s a d l ι).mapConst f) = callSub s a d l := by
  funext ι
  refine Fin.cases ?_ (fun i => ?_) ι
  · show (if h : l < a then (.var ⟨d + (a - 1 - l), by omega⟩ : Tm Head (s + a + d))
        else defaultTm).mapConst f = if h : l < a then .var ⟨d + (a - 1 - l), by omega⟩
        else defaultTm
    split
    · rfl
    · simp only [defaultTm, Presentation.Tm.mapConst, fixDefault]
  · rfl

theorem Tm.mapConst_hypSub {g : DeclName} (fixName : f g = g)
    (fixDefault : f .anonymous = .anonymous) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (fields : List (Field Head)) :
    (fun ι => (hypSub g e s d fields ι).mapConst f) = hypSub g e s d fields := by
  unfold hypSub
  rw [Tm.mapConst_extendSub]
  congr 1
  funext j
  simp only [recCall, Tm.mapConst_applyClosed, Presentation.Tm.mapConst, fixName,
    Tm.mapConst_callSub f fixDefault]

/-- A definition by structural recursion is sent to itself by a renaming that
fixes its name, its constructors, the default term and its right-hand sides. -/
theorem RecursionStep.mapConst {g : DeclName} {ctors : List (DeclName × List (Field Head))}
    {e : (i : Nat) → Tm Head i} {s d : Nat}
    {body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)}
    (fixName : f g = g) (fixCtors : ∀ entry ∈ ctors, f entry.1 = entry.1)
    (fixDefault : f .anonymous = .anonymous)
    (fixBody : ∀ entry ∈ ctors, (body entry.1 entry.2).mapConst f = body entry.1 entry.2)
    {n : Nat} {l r : Tm Head n} (step : RecursionStep g ctors e s d body l r) :
    RecursionStep g ctors e s d body (l.mapConst f) (r.mapConst f) := by
  obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := step
  have fixK : f k = k := fixCtors (k, fields) mem
  refine ⟨k, fields, fun i => (σ i).mapConst f, as.map (Presentation.Tm.mapConst f), mem,
    by simp [has], ?_, ?_⟩
  · rw [Tm.mapConst_applyClosed, Tm.mapConst_replaceScrut, Tm.mapConst_appSpine]
    simp only [Presentation.Tm.mapConst, fixK, fixName]
  · rw [Presentation.Tm.mapConst_subst, Presentation.Tm.mapConst_subst,
      Tm.mapConst_matchSub f fixDefault, Tm.mapConst_hypSub f fixName fixDefault,
      fixBody (k, fields) mem]

/-- The decoding of codes is sent to itself by a renaming that fixes the decoder,
implication, and the code constants with their carriers. -/
theorem DecoderStep.mapConst {D : Decoders Head} (fixHolds : f D.holds = D.holds)
    (fixImp : f D.imp = D.imp)
    (fixAll : ∀ {a : DeclName} {A : Tm Head 0}, D.allCarrier a = some A → f a = a)
    (fixEq : ∀ {c : DeclName} {A : Tm Head 0}, D.eqCarrier c = some A → f c = c)
    (fixAllCarrier : ∀ {a : DeclName} {A : Tm Head 0}, D.allCarrier a = some A →
      A.mapConst f = A)
    (fixEqCarrier : ∀ {c : DeclName} {A : Tm Head 0}, D.eqCarrier c = some A →
      A.mapConst f = A) {n : Nat} {l r : Tm Head n} (step : DecoderStep D l r) :
    DecoderStep D (l.mapConst f) (r.mapConst f) := by
  cases step with
  | imp p q =>
      simp only [Presentation.Tm.mapConst, fixHolds, fixImp, Presentation.Tm.mapConst_rename]
      exact .imp _ _
  | all carrier g =>
      simp only [Presentation.Tm.mapConst, fixHolds, fixAll carrier,
        Presentation.Tm.mapConst_rename, Presentation.Tm.mapConst_liftClosed,
        fixAllCarrier carrier]
      exact .all carrier _
  | eq carrier x y =>
      simp only [Presentation.Tm.mapConst, fixHolds, fixEq carrier,
        Presentation.Tm.mapConst_liftClosed, fixEqCarrier carrier]
      exact .eq carrier _ _

end Computations

end Normalization

end TypedEquality

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
