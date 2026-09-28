import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-!
# Written λ-domains and their erasure

An authored λ may state its domain. `ATm` is the calculus's term grammar in
which a λ is either bare or carries a written domain: one λ, whose domain is
an optional contract. `ATm.erase` drops every written domain and gives the
term of the calculus that computation runs on.

Erasure commutes with renaming and with simultaneous substitution. So
instantiating a binder never makes a written domain matter for computation:
the domain is a contract that checking honours and erasure forgets.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-- Terms whose λs may carry a written domain. -/
inductive ATm (Head : Type) : Nat → Type where
  | var {n : Nat} : Fin n → ATm Head n
  | const {n : Nat} : DeclName → ATm Head n
  | head {n : Nat} : Head → ATm Head n
  | pi {n : Nat} : ATm Head n → ATm Head (n + 1) → ATm Head n
  | sigma {n : Nat} : ATm Head n → ATm Head (n + 1) → ATm Head n
  | id {n : Nat} : ATm Head n → ATm Head n → ATm Head n → ATm Head n
  /-- A λ whose domain is not written. -/
  | lamBare {n : Nat} : ATm Head (n + 1) → ATm Head n
  /-- A λ with its domain written. -/
  | lamTyped {n : Nat} : ATm Head n → ATm Head (n + 1) → ATm Head n
  | app {n : Nat} : ATm Head n → ATm Head n → ATm Head n
  | pair {n : Nat} : ATm Head n → ATm Head n → ATm Head n
  | fst {n : Nat} : ATm Head n → ATm Head n
  | snd {n : Nat} : ATm Head n → ATm Head n
  | refl {n : Nat} : ATm Head n → ATm Head n

namespace ATm

variable {Head : Type}

/-- Drop every written domain. -/
def erase : {n : Nat} → ATm Head n → Tm Head n
  | _, .var i => .var i
  | _, .const c => .const c
  | _, .head h => .head h
  | _, .pi A B => .pi (erase A) (erase B)
  | _, .sigma A B => .sigma (erase A) (erase B)
  | _, .id A a b => .id (erase A) (erase a) (erase b)
  | _, .lamBare body => .lam (erase body)
  | _, .lamTyped _ body => .lam (erase body)
  | _, .app g a => .app (erase g) (erase a)
  | _, .pair a b => .pair (erase a) (erase b)
  | _, .fst p => .fst (erase p)
  | _, .snd p => .snd (erase p)
  | _, .refl a => .refl (erase a)

/-- A term of the calculus, with no domain written. -/
def ofTm : {n : Nat} → Tm Head n → ATm Head n
  | _, .var i => .var i
  | _, .const c => .const c
  | _, .head h => .head h
  | _, .pi A B => .pi (ofTm A) (ofTm B)
  | _, .sigma A B => .sigma (ofTm A) (ofTm B)
  | _, .id A a b => .id (ofTm A) (ofTm a) (ofTm b)
  | _, .lam body => .lamBare (ofTm body)
  | _, .app g a => .app (ofTm g) (ofTm a)
  | _, .pair a b => .pair (ofTm a) (ofTm b)
  | _, .fst p => .fst (ofTm p)
  | _, .snd p => .snd (ofTm p)
  | _, .refl a => .refl (ofTm a)

/-- Every λ outside a written domain carries its domain. -/
def Written : {n : Nat} → ATm Head n → Prop
  | _, .var _ => True
  | _, .const _ => True
  | _, .head _ => True
  | _, .pi A B => Written A ∧ Written B
  | _, .sigma A B => Written A ∧ Written B
  | _, .id A a b => Written A ∧ Written a ∧ Written b
  | _, .lamBare _ => False
  | _, .lamTyped _ body => Written body
  | _, .app g a => Written g ∧ Written a
  | _, .pair a b => Written a ∧ Written b
  | _, .fst p => Written p
  | _, .snd p => Written p
  | _, .refl a => Written a

/-- Renaming; a written domain is renamed with its λ. -/
def rename {n m : Nat} (ρ : Ren n m) : ATm Head n → ATm Head m
  | .var i => .var (ρ i)
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (rename ρ A) (rename (liftRen ρ) B)
  | .sigma A B => .sigma (rename ρ A) (rename (liftRen ρ) B)
  | .id A a b => .id (rename ρ A) (rename ρ a) (rename ρ b)
  | .lamBare body => .lamBare (rename (liftRen ρ) body)
  | .lamTyped A body => .lamTyped (rename ρ A) (rename (liftRen ρ) body)
  | .app g a => .app (rename ρ g) (rename ρ a)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .fst p => .fst (rename ρ p)
  | .snd p => .snd (rename ρ p)
  | .refl a => .refl (rename ρ a)

/-- Simultaneous substitutions of annotated terms. -/
abbrev ASub (Head : Type) (n m : Nat) := Fin n → ATm Head m

def liftSub {n m : Nat} (σ : ASub Head n m) : ASub Head (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => rename wk (σ i))

/-- Simultaneous substitution; a written domain is substituted with its λ. -/
def subst {n m : Nat} (σ : ASub Head n m) : ATm Head n → ATm Head m
  | .var i => σ i
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (subst σ A) (subst (liftSub σ) B)
  | .sigma A B => .sigma (subst σ A) (subst (liftSub σ) B)
  | .id A a b => .id (subst σ A) (subst σ a) (subst σ b)
  | .lamBare body => .lamBare (subst (liftSub σ) body)
  | .lamTyped A body => .lamTyped (subst σ A) (subst (liftSub σ) body)
  | .app g a => .app (subst σ g) (subst σ a)
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .fst p => .fst (subst σ p)
  | .snd p => .snd (subst σ p)
  | .refl a => .refl (subst σ a)

def subst0 {n : Nat} (u : ATm Head n) : ASub Head (n + 1) n :=
  Fin.cases u (fun i => .var i)

def inst0 {n : Nat} (u : ATm Head n) (body : ATm Head (n + 1)) : ATm Head n :=
  subst (subst0 u) body

/-- The identity substitution. -/
def ids {n : Nat} : ASub Head n n := fun i => .var i

/-- Erase every term of a substitution. -/
def eraseSub {n m : Nat} (σ : ASub Head n m) : Sub Head n m := fun i => erase (σ i)

@[simp] theorem eraseSub_apply {n m : Nat} (σ : ASub Head n m) (i : Fin n) :
    eraseSub σ i = erase (σ i) := rfl

@[simp] theorem eraseSub_ids {n : Nat} : eraseSub (ids : ASub Head n n) = Presentation.ids := rfl

theorem liftSub_ids {n : Nat} : liftSub (ids : ASub Head n n) = ids := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem subst_ids {n : Nat} (t : ATm Head n) : subst ids t = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [subst, liftSub_ids, ihA, ihB]
  | sigma A B ihA ihB => simp only [subst, liftSub_ids, ihA, ihB]
  | id A a b ihA iha ihb => simp only [subst, ihA, iha, ihb]
  | lamBare body ih => simp only [subst, liftSub_ids, ih]
  | lamTyped A body ihA ih => simp only [subst, liftSub_ids, ihA, ih]
  | app g a ihg iha => simp only [subst, ihg, iha]
  | pair a b iha ihb => simp only [subst, iha, ihb]
  | fst p ih => simp only [subst, ih]
  | snd p ih => simp only [subst, ih]
  | refl a ih => simp only [subst, ih]

/-! ## Erasure commutes with the structure -/

/-- A term with no written domain erases to itself. -/
@[simp] theorem erase_ofTm {n : Nat} (t : Tm Head n) : erase (ofTm t) = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [ofTm, erase, ihA, ihB]
  | sigma A B ihA ihB => simp only [ofTm, erase, ihA, ihB]
  | id A a b ihA iha ihb => simp only [ofTm, erase, ihA, iha, ihb]
  | lam body ih => simp only [ofTm, erase, ih]
  | app g a ihg iha => simp only [ofTm, erase, ihg, iha]
  | pair a b iha ihb => simp only [ofTm, erase, iha, ihb]
  | fst p ih => simp only [ofTm, erase, ih]
  | snd p ih => simp only [ofTm, erase, ih]
  | refl a ih => simp only [ofTm, erase, ih]

@[simp] theorem erase_rename {n m : Nat} (ρ : Ren n m) (t : ATm Head n) :
    erase (rename ρ t) = Presentation.rename ρ (erase t) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [rename, erase, Presentation.rename, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, erase, Presentation.rename, ihA, ihB]
  | id A a b ihA iha ihb =>
      simp only [rename, erase, Presentation.rename, ihA, iha, ihb]
  | lamBare body ih => simp only [rename, erase, Presentation.rename, ih]
  | lamTyped A body ihA ih => simp only [rename, erase, Presentation.rename, ih]
  | app g a ihg iha => simp only [rename, erase, Presentation.rename, ihg, iha]
  | pair a b iha ihb => simp only [rename, erase, Presentation.rename, iha, ihb]
  | fst p ih => simp only [rename, erase, Presentation.rename, ih]
  | snd p ih => simp only [rename, erase, Presentation.rename, ih]
  | refl a ih => simp only [rename, erase, Presentation.rename, ih]

theorem erase_liftSub {n m : Nat} (σ : ASub Head n m) :
    eraseSub (liftSub σ) = Presentation.liftSub (eraseSub σ) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact erase_rename wk (σ j)

@[simp] theorem erase_subst {n m : Nat} (σ : ASub Head n m) (t : ATm Head n) :
    erase (subst σ t) = Presentation.subst (eraseSub σ) (erase t) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB =>
      simp only [subst, erase, Presentation.subst, ihA, ihB, erase_liftSub]
  | sigma A B ihA ihB =>
      simp only [subst, erase, Presentation.subst, ihA, ihB, erase_liftSub]
  | id A a b ihA iha ihb =>
      simp only [subst, erase, Presentation.subst, ihA, iha, ihb]
  | lamBare body ih =>
      simp only [subst, erase, Presentation.subst, ih, erase_liftSub]
  | lamTyped A body ihA ih =>
      simp only [subst, erase, Presentation.subst, ih, erase_liftSub]
  | app g a ihg iha => simp only [subst, erase, Presentation.subst, ihg, iha]
  | pair a b iha ihb => simp only [subst, erase, Presentation.subst, iha, ihb]
  | fst p ih => simp only [subst, erase, Presentation.subst, ih]
  | snd p ih => simp only [subst, erase, Presentation.subst, ih]
  | refl a ih => simp only [subst, erase, Presentation.subst, ih]

theorem erase_subst0 {n : Nat} (u : ATm Head n) :
    eraseSub (subst0 u) = Presentation.subst0 (erase u) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Opening a binder commutes with erasure. -/
@[simp] theorem erase_inst0 {n : Nat} (u : ATm Head n) (body : ATm Head (n + 1)) :
    erase (inst0 u body) = Presentation.inst0 (erase u) (erase body) := by
  simp only [inst0, Presentation.inst0, erase_subst, erase_subst0]

/-! ## Which written terms erase to a given former -/

theorem erase_eq_var {n : Nat} {t : ATm Head n} {i : Fin n} (equal : erase t = .var i) :
    t = .var i := by
  cases t <;> simp only [erase, Tm.var.injEq, reduceCtorEq] at equal
  rw [equal]

theorem erase_eq_head {n : Nat} {t : ATm Head n} {h : Head} (equal : erase t = .head h) :
    t = .head h := by
  cases t <;> simp only [erase, Tm.head.injEq, reduceCtorEq] at equal
  rw [equal]

theorem erase_eq_pi {n : Nat} {t : ATm Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (equal : erase t = .pi A B) : ∃ A' B', t = .pi A' B' ∧ erase A' = A ∧ erase B' = B := by
  cases t <;> simp only [erase, Tm.pi.injEq, reduceCtorEq] at equal
  exact ⟨_, _, rfl, equal⟩

theorem erase_eq_sigma {n : Nat} {t : ATm Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (equal : erase t = .sigma A B) :
    ∃ A' B', t = .sigma A' B' ∧ erase A' = A ∧ erase B' = B := by
  cases t <;> simp only [erase, Tm.sigma.injEq, reduceCtorEq] at equal
  exact ⟨_, _, rfl, equal⟩

theorem erase_eq_id {n : Nat} {t : ATm Head n} {A a b : Tm Head n}
    (equal : erase t = .id A a b) :
    ∃ A' a' b', t = .id A' a' b' ∧ erase A' = A ∧ erase a' = a ∧ erase b' = b := by
  cases t <;> simp only [erase, Tm.id.injEq, reduceCtorEq] at equal
  exact ⟨_, _, _, rfl, equal⟩

/-- A term erasing to a λ is a λ, with or without its domain written. -/
theorem erase_eq_lam {n : Nat} {t : ATm Head n} {body : Tm Head (n + 1)}
    (equal : erase t = .lam body) :
    ∃ body', (t = .lamBare body' ∨ ∃ domain, t = .lamTyped domain body') ∧
      erase body' = body := by
  cases t <;> simp only [erase, Tm.lam.injEq, reduceCtorEq] at equal
  · exact ⟨_, .inl rfl, equal⟩
  · exact ⟨_, .inr ⟨_, rfl⟩, equal⟩

theorem erase_eq_app {n : Nat} {t : ATm Head n} {g a : Tm Head n}
    (equal : erase t = .app g a) : ∃ g' a', t = .app g' a' ∧ erase g' = g ∧ erase a' = a := by
  cases t <;> simp only [erase, Tm.app.injEq, reduceCtorEq] at equal
  exact ⟨_, _, rfl, equal⟩

theorem erase_eq_pair {n : Nat} {t : ATm Head n} {a b : Tm Head n}
    (equal : erase t = .pair a b) :
    ∃ a' b', t = .pair a' b' ∧ erase a' = a ∧ erase b' = b := by
  cases t <;> simp only [erase, Tm.pair.injEq, reduceCtorEq] at equal
  exact ⟨_, _, rfl, equal⟩

theorem erase_eq_fst {n : Nat} {t : ATm Head n} {p : Tm Head n} (equal : erase t = .fst p) :
    ∃ p', t = .fst p' ∧ erase p' = p := by
  cases t <;> simp only [erase, Tm.fst.injEq, reduceCtorEq] at equal
  exact ⟨_, rfl, equal⟩

theorem erase_eq_snd {n : Nat} {t : ATm Head n} {p : Tm Head n} (equal : erase t = .snd p) :
    ∃ p', t = .snd p' ∧ erase p' = p := by
  cases t <;> simp only [erase, Tm.snd.injEq, reduceCtorEq] at equal
  exact ⟨_, rfl, equal⟩

theorem erase_eq_refl {n : Nat} {t : ATm Head n} {a : Tm Head n} (equal : erase t = .refl a) :
    ∃ a', t = .refl a' ∧ erase a' = a := by
  cases t <;> simp only [erase, Tm.refl.injEq, reduceCtorEq] at equal
  exact ⟨_, rfl, equal⟩

/-! ## Steps and their erasure -/

/-- One step on terms with written domains: β for both λs, the projections of
a pair, the head equality and declared root computations of a rule package,
closed under every former, including inside a written domain. A declared
root computation acts on the erasure of its redex and yields its declared
result, which has no written domain. -/
inductive Step (root : RootComputation Head) (headEq : Head → Head → Prop) :
    {n : Nat} → ATm Head n → ATm Head n → Prop where
  | betaBare {n : Nat} (body : ATm Head (n + 1)) (a : ATm Head n) :
      Step root headEq (.app (.lamBare body) a) (inst0 a body)
  | betaTyped {n : Nat} (domain : ATm Head n) (body : ATm Head (n + 1)) (a : ATm Head n) :
      Step root headEq (.app (.lamTyped domain body) a) (inst0 a body)
  | fstPair {n : Nat} (a b : ATm Head n) : Step root headEq (.fst (.pair a b)) a
  | sndPair {n : Nat} (a b : ATm Head n) : Step root headEq (.snd (.pair a b)) b
  | head {n : Nat} {left right : Head} :
      headEq left right → Step root headEq (.head left : ATm Head n) (.head right)
  | root {n : Nat} {t : ATm Head n} {result : Tm Head n} :
      root.step (erase t) result → Step root headEq t (ofTm result)
  | congPiDom {n : Nat} {A A' : ATm Head n} {B : ATm Head (n + 1)} :
      Step root headEq A A' → Step root headEq (.pi A B) (.pi A' B)
  | congPiCod {n : Nat} {A : ATm Head n} {B B' : ATm Head (n + 1)} :
      Step root headEq B B' → Step root headEq (.pi A B) (.pi A B')
  | congSigmaDom {n : Nat} {A A' : ATm Head n} {B : ATm Head (n + 1)} :
      Step root headEq A A' → Step root headEq (.sigma A B) (.sigma A' B)
  | congSigmaCod {n : Nat} {A : ATm Head n} {B B' : ATm Head (n + 1)} :
      Step root headEq B B' → Step root headEq (.sigma A B) (.sigma A B')
  | congIdTy {n : Nat} {A A' a b : ATm Head n} :
      Step root headEq A A' → Step root headEq (.id A a b) (.id A' a b)
  | congIdLeft {n : Nat} {A a a' b : ATm Head n} :
      Step root headEq a a' → Step root headEq (.id A a b) (.id A a' b)
  | congIdRight {n : Nat} {A a b b' : ATm Head n} :
      Step root headEq b b' → Step root headEq (.id A a b) (.id A a b')
  | congLamBare {n : Nat} {body body' : ATm Head (n + 1)} :
      Step root headEq body body' → Step root headEq (.lamBare body) (.lamBare body')
  /-- A step inside a written domain. -/
  | congLamDomain {n : Nat} {domain domain' : ATm Head n} {body : ATm Head (n + 1)} :
      Step root headEq domain domain' →
        Step root headEq (.lamTyped domain body) (.lamTyped domain' body)
  | congLamTyped {n : Nat} {domain : ATm Head n} {body body' : ATm Head (n + 1)} :
      Step root headEq body body' →
        Step root headEq (.lamTyped domain body) (.lamTyped domain body')
  | congAppFun {n : Nat} {g g' a : ATm Head n} :
      Step root headEq g g' → Step root headEq (.app g a) (.app g' a)
  | congAppArg {n : Nat} {g a a' : ATm Head n} :
      Step root headEq a a' → Step root headEq (.app g a) (.app g a')
  | congPairFst {n : Nat} {a a' b : ATm Head n} :
      Step root headEq a a' → Step root headEq (.pair a b) (.pair a' b)
  | congPairSnd {n : Nat} {a b b' : ATm Head n} :
      Step root headEq b b' → Step root headEq (.pair a b) (.pair a b')
  | congFst {n : Nat} {p p' : ATm Head n} :
      Step root headEq p p' → Step root headEq (.fst p) (.fst p')
  | congSnd {n : Nat} {p p' : ATm Head n} :
      Step root headEq p p' → Step root headEq (.snd p) (.snd p')
  | congRefl {n : Nat} {a a' : ATm Head n} :
      Step root headEq a a' → Step root headEq (.refl a) (.refl a')

/-- Finitely many steps on terms with written domains. -/
abbrev Steps (root : RootComputation Head) (headEq : Head → Head → Prop) {n : Nat}
    (t u : ATm Head n) : Prop :=
  Relation.ReflTransGen (Step root headEq) t u

section Simulation

variable {root : RootComputation Head} {headEq : Head → Head → Prop}

private theorem reflGen_map {α β : Type} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (map : ∀ {a b : α}, r a b → s (f a) (f b)) {a b : α} (related : Relation.ReflGen r a b) :
    Relation.ReflGen s (f a) (f b) := by
  cases related with
  | refl => exact .refl
  | single step => exact .single (map step)

/-- A step on written terms erases to at most one step of the calculus: a step
inside a written domain erases to none. -/
theorem Step.erasure {n : Nat} {t t' : ATm Head n} (step : Step root headEq t t') :
    Relation.ReflGen (StepCore root headEq) (erase t) (erase t') := by
  induction step with
  | betaBare body a =>
      rw [erase_inst0]
      exact .single (.betaPi _ _)
  | betaTyped domain body a =>
      rw [erase_inst0]
      exact .single (.betaPi _ _)
  | fstPair a b => exact .single (.betaSigmaFst _ _)
  | sndPair a b => exact .single (.betaSigmaSnd _ _)
  | head same => exact .single (.head same)
  | root computes =>
      rw [erase_ofTm]
      exact .single (.root computes)
  | @congPiDom _ _ _ B _ ih =>
      exact reflGen_map (fun X => Tm.pi X (ATm.erase B)) StepCore.congPiDom ih
  | @congPiCod _ A _ _ _ ih =>
      exact reflGen_map (fun X => Tm.pi (ATm.erase A) X) StepCore.congPiCod ih
  | @congSigmaDom _ _ _ B _ ih =>
      exact reflGen_map (fun X => Tm.sigma X (ATm.erase B)) StepCore.congSigmaDom ih
  | @congSigmaCod _ A _ _ _ ih =>
      exact reflGen_map (fun X => Tm.sigma (ATm.erase A) X) StepCore.congSigmaCod ih
  | @congIdTy _ _ _ a b _ ih =>
      exact reflGen_map (fun X => Tm.id X (ATm.erase a) (ATm.erase b)) StepCore.congIdTy ih
  | @congIdLeft _ A _ _ b _ ih =>
      exact reflGen_map (fun X => Tm.id (ATm.erase A) X (ATm.erase b)) StepCore.congIdLeft ih
  | @congIdRight _ A a _ _ _ ih =>
      exact reflGen_map (fun X => Tm.id (ATm.erase A) (ATm.erase a) X) StepCore.congIdRight ih
  | congLamBare _ ih => exact reflGen_map Tm.lam StepCore.congLam ih
  | congLamDomain _ _ => exact .refl
  | congLamTyped _ ih => exact reflGen_map Tm.lam StepCore.congLam ih
  | @congAppFun _ _ _ a _ ih =>
      exact reflGen_map (fun X => Tm.app X (ATm.erase a)) StepCore.congAppFun ih
  | @congAppArg _ g _ _ _ ih =>
      exact reflGen_map (fun X => Tm.app (ATm.erase g) X) StepCore.congAppArg ih
  | @congPairFst _ _ _ b _ ih =>
      exact reflGen_map (fun X => Tm.pair X (ATm.erase b)) StepCore.congPairFst ih
  | @congPairSnd _ a _ _ _ ih =>
      exact reflGen_map (fun X => Tm.pair (ATm.erase a) X) StepCore.congPairSnd ih
  | congFst _ ih => exact reflGen_map Tm.fst StepCore.congFst ih
  | congSnd _ ih => exact reflGen_map Tm.snd StepCore.congSnd ih
  | congRefl _ ih => exact reflGen_map Tm.refl StepCore.congRefl ih

/-- Finitely many steps on written terms erase to finitely many steps. -/
theorem Steps.erasure {n : Nat} {t t' : ATm Head n} (steps : Steps root headEq t t') :
    Relation.ReflTransGen (StepCore root headEq) (erase t) (erase t') := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (Step.erasure step).to_reflTransGen

/-- Every step of the calculus from an erasure is the erasure of one step on
the written term. -/
theorem Step.lift {n : Nat} {s s' : Tm Head n} (step : StepCore root headEq s s') :
    ∀ {t : ATm Head n}, erase t = s → ∃ t', Step root headEq t t' ∧ erase t' = s' := by
  induction step with
  | betaPi body a =>
      intro t equal
      obtain ⟨g, a', rfl, eg, rfl⟩ := erase_eq_app equal
      obtain ⟨body', shape, rfl⟩ := erase_eq_lam eg
      rcases shape with rfl | ⟨domain, rfl⟩
      · exact ⟨_, .betaBare body' a', erase_inst0 a' body'⟩
      · exact ⟨_, .betaTyped domain body' a', erase_inst0 a' body'⟩
  | betaSigmaFst a b =>
      intro t equal
      obtain ⟨p, rfl, ep⟩ := erase_eq_fst equal
      obtain ⟨a', b', rfl, rfl, rfl⟩ := erase_eq_pair ep
      exact ⟨a', .fstPair a' b', rfl⟩
  | betaSigmaSnd a b =>
      intro t equal
      obtain ⟨p, rfl, ep⟩ := erase_eq_snd equal
      obtain ⟨a', b', rfl, rfl, rfl⟩ := erase_eq_pair ep
      exact ⟨b', .sndPair a' b', rfl⟩
  | head same =>
      intro t equal
      rw [erase_eq_head equal]
      exact ⟨.head _, .head same, rfl⟩
  | root computes =>
      intro t equal
      subst equal
      exact ⟨_, .root computes, erase_ofTm _⟩
  | congPiDom _ ih =>
      intro t equal
      obtain ⟨A, B, rfl, rfl, rfl⟩ := erase_eq_pi equal
      obtain ⟨A', step, rfl⟩ := ih rfl
      exact ⟨.pi A' B, .congPiDom step, rfl⟩
  | congPiCod _ ih =>
      intro t equal
      obtain ⟨A, B, rfl, rfl, rfl⟩ := erase_eq_pi equal
      obtain ⟨B', step, rfl⟩ := ih rfl
      exact ⟨.pi A B', .congPiCod step, rfl⟩
  | congSigmaDom _ ih =>
      intro t equal
      obtain ⟨A, B, rfl, rfl, rfl⟩ := erase_eq_sigma equal
      obtain ⟨A', step, rfl⟩ := ih rfl
      exact ⟨.sigma A' B, .congSigmaDom step, rfl⟩
  | congSigmaCod _ ih =>
      intro t equal
      obtain ⟨A, B, rfl, rfl, rfl⟩ := erase_eq_sigma equal
      obtain ⟨B', step, rfl⟩ := ih rfl
      exact ⟨.sigma A B', .congSigmaCod step, rfl⟩
  | congIdTy _ ih =>
      intro t equal
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := erase_eq_id equal
      obtain ⟨A', step, rfl⟩ := ih rfl
      exact ⟨.id A' a b, .congIdTy step, rfl⟩
  | congIdLeft _ ih =>
      intro t equal
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := erase_eq_id equal
      obtain ⟨a', step, rfl⟩ := ih rfl
      exact ⟨.id A a' b, .congIdLeft step, rfl⟩
  | congIdRight _ ih =>
      intro t equal
      obtain ⟨A, a, b, rfl, rfl, rfl, rfl⟩ := erase_eq_id equal
      obtain ⟨b', step, rfl⟩ := ih rfl
      exact ⟨.id A a b', .congIdRight step, rfl⟩
  | congLam _ ih =>
      intro t equal
      obtain ⟨body, shape, rfl⟩ := erase_eq_lam equal
      obtain ⟨body', step, rfl⟩ := ih rfl
      rcases shape with rfl | ⟨domain, rfl⟩
      · exact ⟨.lamBare body', .congLamBare step, rfl⟩
      · exact ⟨.lamTyped domain body', .congLamTyped step, rfl⟩
  | congAppFun _ ih =>
      intro t equal
      obtain ⟨g, a, rfl, rfl, rfl⟩ := erase_eq_app equal
      obtain ⟨g', step, rfl⟩ := ih rfl
      exact ⟨.app g' a, .congAppFun step, rfl⟩
  | congAppArg _ ih =>
      intro t equal
      obtain ⟨g, a, rfl, rfl, rfl⟩ := erase_eq_app equal
      obtain ⟨a', step, rfl⟩ := ih rfl
      exact ⟨.app g a', .congAppArg step, rfl⟩
  | congPairFst _ ih =>
      intro t equal
      obtain ⟨a, b, rfl, rfl, rfl⟩ := erase_eq_pair equal
      obtain ⟨a', step, rfl⟩ := ih rfl
      exact ⟨.pair a' b, .congPairFst step, rfl⟩
  | congPairSnd _ ih =>
      intro t equal
      obtain ⟨a, b, rfl, rfl, rfl⟩ := erase_eq_pair equal
      obtain ⟨b', step, rfl⟩ := ih rfl
      exact ⟨.pair a b', .congPairSnd step, rfl⟩
  | congFst _ ih =>
      intro t equal
      obtain ⟨p, rfl, rfl⟩ := erase_eq_fst equal
      obtain ⟨p', step, rfl⟩ := ih rfl
      exact ⟨.fst p', .congFst step, rfl⟩
  | congSnd _ ih =>
      intro t equal
      obtain ⟨p, rfl, rfl⟩ := erase_eq_snd equal
      obtain ⟨p', step, rfl⟩ := ih rfl
      exact ⟨.snd p', .congSnd step, rfl⟩
  | congRefl _ ih =>
      intro t equal
      obtain ⟨a, rfl, rfl⟩ := erase_eq_refl equal
      obtain ⟨a', step, rfl⟩ := ih rfl
      exact ⟨.refl a', .congRefl step, rfl⟩

/-- Finitely many steps of the calculus from an erasure are the erasure of as
many steps on the written term. -/
theorem Steps.lift {n : Nat} {t : ATm Head n} {s : Tm Head n}
    (steps : Relation.ReflTransGen (StepCore root headEq) (erase t) s) :
    ∃ t', Steps root headEq t t' ∧ erase t' = s := by
  induction steps with
  | refl => exact ⟨t, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨t₁, steps₁, rfl⟩ := ih
      obtain ⟨t₂, step₂, rfl⟩ := Step.lift step rfl
      exact ⟨t₂, steps₁.tail step₂, rfl⟩

end Simulation

/-! ## Controls -/

/-- Erasure forgets which domain was written. -/
theorem erase_forgets_domain {n : Nat} (A B : ATm Head n) (body : ATm Head (n + 1)) :
    erase (lamTyped A body) = erase (lamTyped B body) := rfl

/-- ... while the two written terms differ whenever their domains do. -/
theorem lamTyped_ne_of_domain_ne {n : Nat} {A B : ATm Head n} {body : ATm Head (n + 1)}
    (different : A ≠ B) : lamTyped A body ≠ lamTyped B body := by
  intro equal
  cases equal
  exact different rfl

/-- A written domain is not the bare λ: erasure identifies them, the written
terms do not. -/
theorem lamTyped_ne_lamBare {n : Nat} (A : ATm Head n) (body : ATm Head (n + 1)) :
    lamTyped A body ≠ lamBare body ∧ erase (lamTyped A body) = erase (lamBare body) :=
  ⟨(fun equal => nomatch equal), rfl⟩

/-- A step inside a written domain changes the written term and not its
erasure: the simulation of a step can take no step of the calculus. -/
theorem domainStep_erases_to_no_step (root : RootComputation Head)
    (headEq : Head → Head → Prop) {n : Nat} (h : Head) (body : ATm Head (n + 1)) :
    Step root headEq (lamTyped (app (lamBare (var 0)) (head h)) body) (lamTyped (head h) body) ∧
      lamTyped (app (lamBare (var 0)) (head h)) body ≠ lamTyped (head h) body ∧
      erase (lamTyped (app (lamBare (var 0)) (head h)) body) = erase (lamTyped (head h) body) :=
  ⟨.congLamDomain (.betaBare (var 0) (head h)), (fun equal => nomatch equal), rfl⟩

/-- β on a λ with a written domain erases to β of the calculus. -/
theorem betaTyped_erases_to_beta (root : RootComputation Head)
    (headEq : Head → Head → Prop) {n : Nat} (domain : ATm Head n)
    (body : ATm Head (n + 1)) (argument : ATm Head n) :
    StepCore root headEq (erase (app (lamTyped domain body) argument))
      (erase (inst0 argument body)) := by
  rw [erase_inst0]
  exact .betaPi _ _

end ATm

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
