import Mathlib.Logic.Relation

/-!
# Parameterized dependent Pi/Sigma/identity syntax and judgments

Locally scoped terms, simultaneous substitution, contextual reduction and typing
are parameterized by universe heads and declared rules. Identity formation and
reflexivity are primitive; eliminators may be supplied by declarations with their
own typing and computation qualifications. No universe profile or language is
selected here. Concrete profiles are in `Instances.UniverseProfiles`.
-/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

abbrev DeclName := Lean.Name

/-! ## A universe-head-parameterized term grammar -/

/-- The shared dependent term grammar.  `Head` supplies only the universe
and distinguished-ground heads; it does not alter binding or computation. -/
inductive Tm (Head : Type) : Nat → Type where
  | var : Fin n → Tm Head n
  | const : DeclName → Tm Head n
  | head : Head → Tm Head n
  | pi : Tm Head n → Tm Head (n + 1) → Tm Head n
  | sigma : Tm Head n → Tm Head (n + 1) → Tm Head n
  | id : Tm Head n → Tm Head n → Tm Head n → Tm Head n
  | lam : Tm Head (n + 1) → Tm Head n
  | app : Tm Head n → Tm Head n → Tm Head n
  | pair : Tm Head n → Tm Head n → Tm Head n
  | fst : Tm Head n → Tm Head n
  | snd : Tm Head n → Tm Head n
  | refl : Tm Head n → Tm Head n
  deriving DecidableEq, Repr

/-- Functorial action on the universe-head parameter. -/
def Tm.mapHead (f : Head₁ → Head₂) : Tm Head₁ n → Tm Head₂ n
  | .var i => .var i
  | .const c => .const c
  | .head h => .head (f h)
  | .pi A B => .pi (mapHead f A) (mapHead f B)
  | .sigma A B => .sigma (mapHead f A) (mapHead f B)
  | .id A a b => .id (mapHead f A) (mapHead f a) (mapHead f b)
  | .lam body => .lam (mapHead f body)
  | .app g a => .app (mapHead f g) (mapHead f a)
  | .pair a b => .pair (mapHead f a) (mapHead f b)
  | .fst p => .fst (mapHead f p)
  | .snd p => .snd (mapHead f p)
  | .refl a => .refl (mapHead f a)

@[simp] theorem Tm.mapHead_id (t : Tm Head n) :
    t.mapHead (fun h => h) = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [mapHead, ihA, ihB]
  | sigma A B ihA ihB => simp only [mapHead, ihA, ihB]
  | id A a b ihA iha ihb => simp only [mapHead, ihA, iha, ihb]
  | lam body ih => simp only [mapHead, ih]
  | app g a ihg iha => simp only [mapHead, ihg, iha]
  | pair a b iha ihb => simp only [mapHead, iha, ihb]
  | fst p ih => simp only [mapHead, ih]
  | snd p ih => simp only [mapHead, ih]
  | refl a ih => simp only [mapHead, ih]

@[simp] theorem Tm.mapHead_comp (g : Head₂ → Head₃)
    (f : Head₁ → Head₂) (t : Tm Head₁ n) :
    (t.mapHead f).mapHead g = t.mapHead (g ∘ f) := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [mapHead, ihA, ihB]
  | sigma A B ihA ihB => simp only [mapHead, ihA, ihB]
  | id A a b ihA iha ihb => simp only [mapHead, ihA, iha, ihb]
  | lam body ih => simp only [mapHead, ih]
  | app h a ihh iha => simp only [mapHead, ihh, iha]
  | pair a b iha ihb => simp only [mapHead, iha, ihb]
  | fst p ih => simp only [mapHead, ih]
  | snd p ih => simp only [mapHead, ih]
  | refl a ih => simp only [mapHead, ih]

/-! ## Binding operations shared by both presentations -/

abbrev Ren (n m : Nat) := Fin n → Fin m

def idRen : Ren n n := fun i => i

def wk : Ren n (n + 1) := Fin.succ

def liftRen (ρ : Ren n m) : Ren (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def rename (ρ : Ren n m) : Tm Head n → Tm Head m
  | .var i => .var (ρ i)
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (rename ρ A) (rename (liftRen ρ) B)
  | .sigma A B => .sigma (rename ρ A) (rename (liftRen ρ) B)
  | .id A a b => .id (rename ρ A) (rename ρ a) (rename ρ b)
  | .lam body => .lam (rename (liftRen ρ) body)
  | .app g a => .app (rename ρ g) (rename ρ a)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .fst p => .fst (rename ρ p)
  | .snd p => .snd (rename ρ p)
  | .refl a => .refl (rename ρ a)

/-- Changing universe heads commutes with term-variable renaming. -/
@[simp] theorem Tm.mapHead_rename (f : Head₁ → Head₂)
    (ρ : Ren n m) (t : Tm Head₁ n) :
    (rename ρ t).mapHead f = rename ρ (t.mapHead f) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [rename, mapHead, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, mapHead, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, mapHead, ihA, iha, ihb]
  | lam body ih => simp only [rename, mapHead, ih]
  | app g a ihg iha => simp only [rename, mapHead, ihg, iha]
  | pair a b iha ihb => simp only [rename, mapHead, iha, ihb]
  | fst p ih => simp only [rename, mapHead, ih]
  | snd p ih => simp only [rename, mapHead, ih]
  | refl a ih => simp only [rename, mapHead, ih]

abbrev Sub (Head : Type) (n m : Nat) := Fin n → Tm Head m

def ids : Sub Head n n := fun i => .var i

def liftSub (σ : Sub Head n m) : Sub Head (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => rename wk (σ i))

def subst (σ : Sub Head n m) : Tm Head n → Tm Head m
  | .var i => σ i
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (subst σ A) (subst (liftSub σ) B)
  | .sigma A B => .sigma (subst σ A) (subst (liftSub σ) B)
  | .id A a b => .id (subst σ A) (subst σ a) (subst σ b)
  | .lam body => .lam (subst (liftSub σ) body)
  | .app g a => .app (subst σ g) (subst σ a)
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .fst p => .fst (subst σ p)
  | .snd p => .snd (subst σ p)
  | .refl a => .refl (subst σ a)

def subst0 (u : Tm Head n) : Sub Head (n + 1) n :=
  Fin.cases u (fun i => .var i)

def inst0 (u : Tm Head n) (body : Tm Head (n + 1)) : Tm Head n :=
  subst (subst0 u) body

/-- A closed term can be used in every ambient telescope.  Keeping this
operation explicit prevents declaration types from acquiring accidental
dependencies on local variables. -/
def liftClosed (term : Tm Head 0) : Tm Head n :=
  rename Fin.elim0 term

/-- Mapping a substitution across heads commutes with lifting it under a
binder. -/
theorem Tm.mapHead_liftSub (f : Head₁ → Head₂) (σ : Sub Head₁ n m) :
    (fun i => (liftSub σ i).mapHead f) =
      liftSub (fun i => (σ i).mapHead f) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact Tm.mapHead_rename f wk (σ j)

/-- Changing universe heads commutes with simultaneous term substitution. -/
@[simp] theorem Tm.mapHead_subst (f : Head₁ → Head₂)
    (σ : Sub Head₁ n m) (t : Tm Head₁ n) :
    (subst σ t).mapHead f =
      subst (fun i => (σ i).mapHead f) (t.mapHead f) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB =>
      simp only [subst, mapHead, ihA, ihB, Tm.mapHead_liftSub]
  | sigma A B ihA ihB =>
      simp only [subst, mapHead, ihA, ihB, Tm.mapHead_liftSub]
  | id A a b ihA iha ihb => simp only [subst, mapHead, ihA, iha, ihb]
  | lam body ih => simp only [subst, mapHead, ih, Tm.mapHead_liftSub]
  | app g a ihg iha => simp only [subst, mapHead, ihg, iha]
  | pair a b iha ihb => simp only [subst, mapHead, iha, ihb]
  | fst p ih => simp only [subst, mapHead, ih]
  | snd p ih => simp only [subst, mapHead, ih]
  | refl a ih => simp only [subst, mapHead, ih]

/-- In particular, changing heads commutes with opening one binder. -/
@[simp] theorem Tm.mapHead_inst0 (f : Head₁ → Head₂)
    (u : Tm Head₁ n) (body : Tm Head₁ (n + 1)) :
    (inst0 u body).mapHead f = inst0 (u.mapHead f) (body.mapHead f) := by
  rw [inst0, inst0, Tm.mapHead_subst]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-! ## Contexts, computation, and conversion -/

/-- Telescope contexts over the shared grammar. -/
inductive Ctx (Head : Type) : Nat → Type where
  | nil : Ctx Head 0
  | snoc : Ctx Head n → Tm Head n → Ctx Head (n + 1)
  deriving Repr

def Ctx.lookup : Ctx Head n → Fin n → Tm Head n
  | .nil, i => nomatch i
  | .snoc Γ A, i =>
      Fin.cases (rename wk A) (fun j => rename wk (lookup Γ j)) i

/-- Map the universe heads of every context entry. -/
def Ctx.mapHead (f : Head₁ → Head₂) : Ctx Head₁ n → Ctx Head₂ n
  | .nil => .nil
  | .snoc Γ A => .snoc (mapHead f Γ) (A.mapHead f)

@[simp] theorem Ctx.mapHead_id (Γ : Ctx Head n) :
    Γ.mapHead (fun head => head) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ type ih => simp only [mapHead, ih, Tm.mapHead_id]

@[simp] theorem Ctx.mapHead_comp (g : Head₂ → Head₃)
    (f : Head₁ → Head₂) (Γ : Ctx Head₁ n) :
    (Γ.mapHead f).mapHead g = Γ.mapHead (g ∘ f) := by
  induction Γ with
  | nil => rfl
  | snoc Γ type ih => simp only [mapHead, ih, Tm.mapHead_comp]

/-- Context lookup commutes with changing universe heads. -/
@[simp] theorem Ctx.lookup_mapHead (f : Head₁ → Head₂)
    (Γ : Ctx Head₁ n) (i : Fin n) :
    lookup (mapHead f Γ) i = (lookup Γ i).mapHead f := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A ih =>
      refine Fin.cases ?_ ?_ i
      · exact (Tm.mapHead_rename f wk A).symm
      · intro j
        change rename wk (lookup (mapHead f Γ) j) =
          (rename wk (lookup Γ j)).mapHead f
        rw [ih]
        exact (Tm.mapHead_rename f wk (lookup Γ j)).symm

/-- Declaration-specific root computation, together with the two structural
laws required for safely using it under binders.  Delta rules and inductive
iota rules are instances of this interface; the sealed presentation uses
`empty`. -/
structure RootComputation (Head : Type) where
  step : {n : Nat} → Tm Head n → Tm Head n → Prop
  rename : ∀ {n m : Nat} (rho : Ren n m) {left right : Tm Head n},
    step left right → step (Presentation.rename rho left) (Presentation.rename rho right)
  substitute : ∀ {n m : Nat} (sigma : Sub Head n m) {left right : Tm Head n},
    step left right → step (subst sigma left) (subst sigma right)

/-- The presentation with no declaration-specific computation. -/
def RootComputation.empty : RootComputation Head where
  step := fun _ _ => False
  rename := by
    intro n m rho left right impossible
    exact impossible.elim
  substitute := by
    intro n m sigma left right impossible
    exact impossible.elim

/-- One computational or universe-head equality step, closed under all
term constructors.  Symmetry and transitivity are supplied by `Conv`.
Declaration-specific root steps are supplied by the rule package. -/
inductive StepCore (root : RootComputation Head)
    (headEq : Head → Head → Prop) : Tm Head n → Tm Head n → Prop where
  | betaPi (body : Tm Head (n + 1)) (a : Tm Head n) :
      StepCore root headEq (.app (.lam body) a) (inst0 a body)
  | betaSigmaFst (a b : Tm Head n) :
      StepCore root headEq (.fst (.pair a b)) a
  | betaSigmaSnd (a b : Tm Head n) :
      StepCore root headEq (.snd (.pair a b)) b
  | head {left right : Head} :
      headEq left right → StepCore root headEq (.head left) (.head right)
  | root {left right : Tm Head n} :
      root.step left right → StepCore root headEq left right
  | congPiDom {A A' : Tm Head n} {B : Tm Head (n + 1)} :
      StepCore root headEq A A' → StepCore root headEq (.pi A B) (.pi A' B)
  | congPiCod {A : Tm Head n} {B B' : Tm Head (n + 1)} :
      StepCore root headEq B B' → StepCore root headEq (.pi A B) (.pi A B')
  | congSigmaDom {A A' : Tm Head n} {B : Tm Head (n + 1)} :
      StepCore root headEq A A' → StepCore root headEq (.sigma A B) (.sigma A' B)
  | congSigmaCod {A : Tm Head n} {B B' : Tm Head (n + 1)} :
      StepCore root headEq B B' → StepCore root headEq (.sigma A B) (.sigma A B')
  | congIdTy {A A' a b : Tm Head n} :
      StepCore root headEq A A' → StepCore root headEq (.id A a b) (.id A' a b)
  | congIdLeft {A a a' b : Tm Head n} :
      StepCore root headEq a a' → StepCore root headEq (.id A a b) (.id A a' b)
  | congIdRight {A a b b' : Tm Head n} :
      StepCore root headEq b b' → StepCore root headEq (.id A a b) (.id A a b')
  | congLam {body body' : Tm Head (n + 1)} :
      StepCore root headEq body body' → StepCore root headEq (.lam body) (.lam body')
  | congAppFun {g g' a : Tm Head n} :
      StepCore root headEq g g' → StepCore root headEq (.app g a) (.app g' a)
  | congAppArg {g a a' : Tm Head n} :
      StepCore root headEq a a' → StepCore root headEq (.app g a) (.app g a')
  | congPairFst {a a' b : Tm Head n} :
      StepCore root headEq a a' → StepCore root headEq (.pair a b) (.pair a' b)
  | congPairSnd {a b b' : Tm Head n} :
      StepCore root headEq b b' → StepCore root headEq (.pair a b) (.pair a b')
  | congFst {p p' : Tm Head n} :
      StepCore root headEq p p' → StepCore root headEq (.fst p) (.fst p')
  | congSnd {p p' : Tm Head n} :
      StepCore root headEq p p' → StepCore root headEq (.snd p) (.snd p')
  | congRefl {a a' : Tm Head n} :
      StepCore root headEq a a' → StepCore root headEq (.refl a) (.refl a')

/-- Compatibility-facing order: existing sealed developments may continue to
write `Step headEq left right`, while declaration-aware developments pass the
root computation as the final argument. -/
abbrev Step (headEq : Head → Head → Prop) (left right : Tm Head n)
    (root : RootComputation Head := RootComputation.empty) : Prop :=
  StepCore root headEq left right

namespace Step

export StepCore (betaPi betaSigmaFst betaSigmaSnd head root congPiDom
  congPiCod congSigmaDom congSigmaCod congIdTy congIdLeft congIdRight congLam
  congAppFun congAppArg congPairFst congPairSnd congFst congSnd congRefl)

end Step

abbrev Conv (headEq : Head → Head → Prop) (left right : Tm Head n)
    (root : RootComputation Head := RootComputation.empty) : Prop :=
  Relation.EqvGen (StepCore root headEq) left right

/-! ## A generic declarative typing spine -/

/-- The pieces in which universe presentations differ. -/
structure Rules (Head : Type) where
  headTyping : Head → Head → Prop
  isUniverse : Head → Prop
  join : Head → Head → Head → Prop
  cumulative : Head → Head → Prop
  headEq : Head → Head → Prop
  constantType : DeclName → Option (Tm Head 0) := fun _ => none
  computation : RootComputation Head := RootComputation.empty

/-- Declarative dependent typing over a chosen universe presentation and its
declaration signature. -/
inductive HasType (R : Rules Head) : Ctx Head n → Tm Head n → Tm Head n → Prop where
  | headType {Γ : Ctx Head n} {h u : Head} :
      R.headTyping h u → HasType R Γ (.head h) (.head u)
  | var {Γ : Ctx Head n} (i : Fin n) :
      HasType R Γ (.var i) (Ctx.lookup Γ i)
  | const {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} :
      R.constantType name = some type →
      HasType R Γ (.const name) (liftClosed type)
  | piForm {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} :
      HasType R Γ A (.head u) → R.isUniverse u →
      HasType R (.snoc Γ A) B (.head v) → R.isUniverse v →
      R.join u v w →
      HasType R Γ (.pi A B) (.head w)
  | sigmaForm {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} :
      HasType R Γ A (.head u) → R.isUniverse u →
      HasType R (.snoc Γ A) B (.head v) → R.isUniverse v →
      R.join u v w →
      HasType R Γ (.sigma A B) (.head w)
  | lamIntro {Γ : Ctx Head n} {A : Tm Head n}
      {body B : Tm Head (n + 1)} :
      HasType R (.snoc Γ A) body B →
      HasType R Γ (.lam body) (.pi A B)
  | appElim {Γ : Ctx Head n} {g a A : Tm Head n}
      {B : Tm Head (n + 1)} :
      HasType R Γ g (.pi A B) → HasType R Γ a A →
      HasType R Γ (.app g a) (inst0 a B)
  | pairIntro {Γ : Ctx Head n} {a b A : Tm Head n}
      {B : Tm Head (n + 1)} :
      HasType R Γ a A → HasType R Γ b (inst0 a B) →
      HasType R Γ (.pair a b) (.sigma A B)
  | fstElim {Γ : Ctx Head n} {p A : Tm Head n}
      {B : Tm Head (n + 1)} :
      HasType R Γ p (.sigma A B) → HasType R Γ (.fst p) A
  | sndElim {Γ : Ctx Head n} {p A : Tm Head n}
      {B : Tm Head (n + 1)} :
      HasType R Γ p (.sigma A B) →
      HasType R Γ (.snd p) (inst0 (.fst p) B)
  | idForm {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head} :
      HasType R Γ A (.head u) → R.isUniverse u →
      HasType R Γ a A → HasType R Γ b A →
      HasType R Γ (.id A a b) (.head u)
  | reflIntro {Γ : Ctx Head n} {a A : Tm Head n} :
      HasType R Γ a A → HasType R Γ (.refl a) (.id A a a)
  | cumul {Γ : Ctx Head n} {t : Tm Head n} {u v : Head} :
      HasType R Γ t (.head u) → R.cumulative u v →
      HasType R Γ t (.head v)
  | conv {Γ : Ctx Head n} {t A B : Tm Head n} :
      HasType R Γ t A → Conv R.headEq A B R.computation → HasType R Γ t B

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
