import Mathlib.Logic.Relation
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.LevelAlgebra

/-!
# Sealed and cumulative universe presentations

This module keeps the existing two-head fragment and the future cumulative
tower as genuinely different data.  Both instantiate one parameterized term
grammar, so their common lambda-calculus structure is definitionally visible,
but their universe heads and universe rules cannot be confused.

The migration map is deliberately not `u0 ↦ U 0`.  The old `u0` is a
distinguished ground type and maps to the opaque tower head `legacyGround`;
the old untyped formation marker `u1` maps to `U 0`.  Thus

```
old u0 : old u1    ↦    legacyGround : U 0,
```

while the independent tower rule is `U l : U (succ l)`.  This separation is
the invariant needed by the later conservativity theorem.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

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

/-! ## The sealed legacy presentation -/

namespace Legacy

/-- The old heads, named by their actual roles rather than `u0`/`u1`. -/
inductive Head where
  | ground
  | marker
  deriving DecidableEq, Repr

abbrev Tm (n : Nat) := Presentation.Tm Head n
abbrev Ctx (n : Nat) := Presentation.Ctx Head n

inductive HeadTyping : Head → Head → Prop where
  | groundMarker : HeadTyping .ground .marker

inductive IsUniverse : Head → Prop where
  | marker : IsUniverse .marker

inductive Join : Head → Head → Head → Prop where
  | marker : Join .marker .marker .marker

/-- The sealed fragment has no cumulative lifting rule. -/
def Cumulative (_ _ : Head) : Prop := False

/-- Legacy head equality is ordinary constructor equality. -/
def HeadEq (left right : Head) : Prop := left = right

def rules : Rules Head where
  headTyping := HeadTyping
  isUniverse := IsUniverse
  join := Join
  cumulative := Cumulative
  headEq := HeadEq

abbrev HasType {n : Nat} := @Presentation.HasType Head rules n

/-- Exact re-presentation of the existing sealed grammar. -/
def ofPure :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n → Tm n
  | .var i => .var i
  | .const c => .const c
  | .u0 => .head .ground
  | .u1 => .head .marker
  | .pi A B => .pi (ofPure A) (ofPure B)
  | .sigma A B => .sigma (ofPure A) (ofPure B)
  | .id A a b => .id (ofPure A) (ofPure a) (ofPure b)
  | .lam body => .lam (ofPure body)
  | .app g a => .app (ofPure g) (ofPure a)
  | .pair a b => .pair (ofPure a) (ofPure b)
  | .fst p => .fst (ofPure p)
  | .snd p => .snd (ofPure p)
  | .refl a => .refl (ofPure a)

/-- Inverse translation back to the existing sealed grammar. -/
def toPure : Tm n →
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n
  | .var i => .var i
  | .const c => .const c
  | .head .ground => .u0
  | .head .marker => .u1
  | .pi A B => .pi (toPure A) (toPure B)
  | .sigma A B => .sigma (toPure A) (toPure B)
  | .id A a b => .id (toPure A) (toPure a) (toPure b)
  | .lam body => .lam (toPure body)
  | .app g a => .app (toPure g) (toPure a)
  | .pair a b => .pair (toPure a) (toPure b)
  | .fst p => .fst (toPure p)
  | .snd p => .snd (toPure p)
  | .refl a => .refl (toPure a)

@[simp] theorem toPure_ofPure
    (t : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n) :
    toPure (ofPure t) = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | u0 => rfl
  | u1 => rfl
  | pi A B ihA ihB => simp only [ofPure, toPure, ihA, ihB]
  | sigma A B ihA ihB => simp only [ofPure, toPure, ihA, ihB]
  | id A a b ihA iha ihb => simp only [ofPure, toPure, ihA, iha, ihb]
  | lam body ih => simp only [ofPure, toPure, ih]
  | app g a ihg iha => simp only [ofPure, toPure, ihg, iha]
  | pair a b iha ihb => simp only [ofPure, toPure, iha, ihb]
  | fst p ih => simp only [ofPure, toPure, ih]
  | snd p ih => simp only [ofPure, toPure, ih]
  | refl a ih => simp only [ofPure, toPure, ih]

@[simp] theorem ofPure_toPure (t : Tm n) : ofPure (toPure t) = t := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => cases h <;> rfl
  | pi A B ihA ihB => simp only [toPure, ofPure, ihA, ihB]
  | sigma A B ihA ihB => simp only [toPure, ofPure, ihA, ihB]
  | id A a b ihA iha ihb => simp only [toPure, ofPure, ihA, iha, ihb]
  | lam body ih => simp only [toPure, ofPure, ih]
  | app g a ihg iha => simp only [toPure, ofPure, ihg, iha]
  | pair a b iha ihb => simp only [toPure, ofPure, iha, ihb]
  | fst p ih => simp only [toPure, ofPure, ih]
  | snd p ih => simp only [toPure, ofPure, ih]
  | refl a ih => simp only [toPure, ofPure, ih]

end Legacy

/-! ## The cumulative tower presentation -/

namespace Tower

open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower

/-- The future tower has an opaque legacy ground head plus explicit
predicative universe levels. -/
inductive Head where
  | legacyGround
  | sort : LevelExpr → Head
  deriving DecidableEq, Repr

abbrev Tm (n : Nat) := Presentation.Tm Head n
abbrev Ctx (n : Nat) := Presentation.Ctx Head n

def zero : LevelExpr := .const 0

inductive HeadTyping : Head → Head → Prop where
  | legacyGround : HeadTyping .legacyGround (.sort zero)
  | sort (level : LevelExpr) : HeadTyping (.sort level) (.sort (.succ level))

inductive IsUniverse : Head → Prop where
  | sort (level : LevelExpr) : IsUniverse (.sort level)

/-- Pi, Sigma, and identity formation live in the maximum input
universe.  Semantic level conversion may subsequently canonicalize it. -/
inductive Join : Head → Head → Head → Prop where
  | sorts (left right : LevelExpr) :
      Join (.sort left) (.sort right) (.sort (.max left right))

/-- Cumulativity is semantic order of explicit levels. -/
def Cumulative : Head → Head → Prop
  | .sort left, .sort right =>
      ∀ v, LevelExpr.eval v left ≤ LevelExpr.eval v right
  | _, _ => False

/-- Universe heads are convertible exactly when their explicit levels
denote the same value under every valuation.  The opaque ground head only
converts to itself. -/
def HeadEq : Head → Head → Prop
  | .legacyGround, .legacyGround => True
  | .sort left, .sort right =>
      ∀ v, LevelExpr.eval v left = LevelExpr.eval v right
  | _, _ => False

instance instDecidableCumulative (left right : Head) :
    Decidable (Cumulative left right) := by
  unfold Cumulative
  split <;> infer_instance

instance instDecidableHeadEq (left right : Head) :
    Decidable (HeadEq left right) := by
  unfold HeadEq
  split <;> infer_instance

def rules : Rules Head where
  headTyping := HeadTyping
  isUniverse := IsUniverse
  join := Join
  cumulative := Cumulative
  headEq := HeadEq

abbrev HasType {n : Nat} := @Presentation.HasType Head rules n

end Tower

/-- The tower universe term at an explicit level.  This constructor belongs
to the shared cumulative presentation rather than to any particular schema
elaboration. -/
def sortTm (level : LevelExpr) : Tower.Tm n := .head (.sort level)

/-! ## The migration map and executable boundary witnesses -/

namespace Legacy.Head

/-- The only sanctioned head migration.  In particular, `ground` does not
map to `Tower.sort Tower.zero`. -/
def embed : Legacy.Head → Tower.Head
  | .ground => .legacyGround
  | .marker => .sort Tower.zero

theorem embed_injective : Function.Injective embed := by
  intro left right h
  cases left <;> cases right <;> simp [embed] at h ⊢

end Legacy.Head

namespace Tower.Head

/-- Forget all explicit tower levels while preserving the distinction
between the legacy ground head and universe heads.  This is a syntactic
retraction of `Legacy.Head.embed`, not a typing translation for arbitrary
tower terms. -/
def forget : Tower.Head → Legacy.Head
  | .legacyGround => .ground
  | .sort _ => .marker

@[simp] theorem forget_embed (head : Legacy.Head) :
    forget head.embed = head := by
  cases head <;> rfl

end Tower.Head

namespace Legacy

/-- Structural embedding of sealed terms into the cumulative presentation. -/
def embed (t : Tm n) : Tower.Tm n := t.mapHead Head.embed

/-- Context embedding uses the same structural head map. -/
def embedCtx (Γ : Ctx n) : Tower.Ctx n := Γ.mapHead Head.embed

/-- Erase explicit levels from tower syntax.  This is used only as a
syntactic retraction and as a conversion invariant; arbitrary erased tower
typing derivations need not be legacy derivations. -/
def forget (t : Tower.Tm n) : Tm n := t.mapHead Tower.Head.forget

/-- Level erasure on contexts. -/
def forgetCtx (Γ : Tower.Ctx n) : Ctx n := Γ.mapHead Tower.Head.forget

@[simp] theorem forget_embed (t : Tm n) : forget (embed t) = t := by
  rw [forget, embed, Tm.mapHead_comp]
  simp [Function.comp_def]

theorem embed_injective : Function.Injective (@embed n) := by
  intro left right h
  have := congrArg forget h
  simpa using this

@[simp] theorem forgetCtx_embedCtx (Γ : Ctx n) :
    forgetCtx (embedCtx Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih =>
      simp only [forgetCtx, embedCtx, Ctx.mapHead]
      have hA : Tm.mapHead Tower.Head.forget
          (Tm.mapHead Head.embed A) = A := by
        rw [Tm.mapHead_comp]
        simp [Function.comp_def]
      exact congrArg₂ Ctx.snoc ih hA

end Legacy

/-- Positive legacy witness: the distinguished ground type is typed by the
sealed marker. -/
example : Legacy.HasType (.nil : Legacy.Ctx 0)
    (.head .ground) (.head .marker) :=
  .headType .groundMarker

/-- Negative legacy witness: the marker itself has no head-typing rule. -/
example : ¬ Legacy.HeadTyping .marker candidate := by
  intro h
  cases h

/-- Positive tower witness: every explicit sort inhabits its successor. -/
example (level :
    Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.LevelExpr) :
    Tower.HasType (.nil : Tower.Ctx 0)
      (.head (.sort level)) (.head (.sort (.succ level))) :=
  .headType (.sort level)

/-- Positive cumulative witness. -/
example : Tower.Cumulative (.sort (.const 0)) (.sort (.const 1)) := by
  intro v
  simp [Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.LevelExpr.eval]

/-- Negative cumulative witness: successor levels cannot be lowered. -/
example : ¬ Tower.Cumulative (.sort (.succ (.param 0))) (.sort (.param 0)) := by
  decide

/-- The migration anti-confusion invariant is executable. -/
example : Legacy.Head.embed .ground ≠ .sort Tower.zero := by
  decide

/-- The old universe axiom embeds as ground-formation, not as the tower's
universe-successor axiom. -/
example : Tower.HasType (.nil : Tower.Ctx 0)
    (Legacy.embed (.head .ground : Legacy.Tm 0))
    (Legacy.embed (.head .marker : Legacy.Tm 0)) :=
  .headType .legacyGround

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
