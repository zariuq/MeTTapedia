import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.AlgorithmSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHeadNormalization
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicParallel

/-!
# The algorithmic equality

The conversion algorithm directed by weak-head normal forms, as a relation with
typing premises. Types and terms are reduced to weak-head normal forms and
compared by their formers:

* at a dependent function type, terms are applied to a fresh variable;
* at a dependent pair type, their projections are compared;
* at a universe, they are compared as types;
* at an identity type, reflexivity proofs are compared by their subjects;
* at the remaining types, whose values are neutral terms and constructor
  spines, they are compared as spines: equal heads, and arguments compared at
  the types the head's type assigns.

This is the search the kernel's conversion performs (`regular_conv_at`,
`regular_conv_neutral` and `regular_conv_types` in the C runtime), reducing
with the weak-head reduction of the model (`regular_whnf`). Every derivation
is a derivation of the kernel's conversion relation `Algorithm`, so the
algorithmic equality is sound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open AlgebraicParallel (stepStar_rename stepStar_substitute)

variable {Head : Type}

/-! ## Weak-head reduction is reduction -/

section Reduction

variable {R : Rules Head} {roles : Roles Head}

theorem stepCore_appSpine {n : Nat} :
    ∀ (args : List (Tm Head n)) {f f' : Tm Head n},
      StepCore R.computation R.headEq f f' →
      StepCore R.computation R.headEq (appSpine f args) (appSpine f' args)
  | [], _, _, step => step
  | _ :: args, _, _, step => stepCore_appSpine args (.congAppFun step)

/-- A step of one argument of a spine is a step of the spine. -/
theorem stepCore_appSpine_arg {n : Nat} {f : Tm Head n} (before after : List (Tm Head n))
    {x y : Tm Head n} (step : StepCore R.computation R.headEq x y) :
    StepCore R.computation R.headEq (appSpine f (before ++ x :: after))
      (appSpine f (before ++ y :: after)) := by
  rw [appSpine_append, appSpine_append]
  exact stepCore_appSpine _ (.congAppArg step)

theorem WhStep.stepCore {n : Nat} {t u : Tm Head n} (step : WhStep R roles t u) :
    StepCore R.computation R.headEq t u := by
  induction step with
  | beta body a => exact .betaPi body a
  | fstPair a b => exact .betaSigmaFst a b
  | sndPair a b => exact .betaSigmaSnd a b
  | root step => exact .root step
  | appFun _ ih => exact .congAppFun ih
  | fst _ ih => exact .congFst ih
  | snd _ ih => exact .congSnd ih
  | scrutinee _ _ focus _ ih =>
      obtain ⟨before, after, x, y, rfl, rfl, step⟩ :=
        focus.lift (fun _ before after {_ _} step => stepCore_appSpine_arg before after step)
          (.congRefl ·) ih
      exact stepCore_appSpine_arg before after step

theorem WhRed.reduces {n : Nat} {t u : Tm Head n} (red : WhRed R roles t u) :
    Reduces R t u := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (WhStep.stepCore step)

theorem Reduces.congr {n m : Nat} {f : Tm Head n → Tm Head m}
    (step : ∀ {a b : Tm Head n}, StepCore R.computation R.headEq a b →
      StepCore R.computation R.headEq (f a) (f b))
    {a b : Tm Head n} (red : Reduces R a b) : Reduces R (f a) (f b) := by
  induction red with
  | refl => exact .refl
  | tail _ s ih => exact .tail ih (step s)

theorem Reduces.appWk {n : Nat} {a a' : Tm Head n} (red : Reduces R a a') :
    Reduces R (.app (Presentation.rename wk a) (.var 0))
      (.app (Presentation.rename wk a') (.var 0)) :=
  Reduces.congr (f := fun t => Tm.app t (.var 0)) (fun step => .congAppFun step)
    (stepStar_rename wk red)

theorem Reduces.fstArg {n : Nat} {a a' : Tm Head n} (red : Reduces R a a') :
    Reduces R (.fst a) (.fst a') :=
  Reduces.congr (f := Tm.fst) (fun step => .congFst step) red

theorem Reduces.sndArg {n : Nat} {a a' : Tm Head n} (red : Reduces R a a') :
    Reduces R (.snd a) (.snd a') :=
  Reduces.congr (f := Tm.snd) (fun step => .congSnd step) red

theorem Reduces.inst0Arg {n : Nat} {a a' : Tm Head n} (red : Reduces R a a')
    (B : Tm Head (n + 1)) : Reduces R (inst0 a B) (inst0 a' B) := by
  refine stepStar_substitute (fun i => ?_) B
  refine Fin.cases ?_ (fun j => ?_) i
  · exact red
  · exact Relation.ReflTransGen.refl

end Reduction

/-! ## The relation -/

/-- The weak-head normal types at which values are compared as spines:
identity types, inductive types, neutral types and heads that are not
universes. -/
def SpineType (R : Rules Head) (roles : Roles Head) {n : Nat} (A : Tm Head n) : Prop :=
  (∃ C a b, A = .id C a b) ∨ Neutral roles A ∨
    (∃ T ctors, roles T = .inductive ctors ∧ A = .const T) ∨
      (∃ h, A = .head h ∧ ¬ R.isUniverse h)

/-- The values compared as spines: neutral terms and constructor spines. -/
def SpineForm (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  Neutral roles t ∨ ∃ k arity args, roles k = .constructor arity ∧ t = appSpine (.const k) args

/-- The judgments of the algorithmic equality. The `W` forms compare weak-head
normal forms; `spines` records the type the head of the left spine assigns. -/
inductive AlgorithmicStatement (Head : Type) : Type where
  | types {n : Nat} (context : Ctx Head n) (left right : Tm Head n)
  | typesW {n : Nat} (context : Ctx Head n) (left right : Tm Head n)
  | terms {n : Nat} (context : Ctx Head n) (left right type : Tm Head n)
  | termsW {n : Nat} (context : Ctx Head n) (left right type : Tm Head n)
  | spines {n : Nat} (context : Ctx Head n) (left right type : Tm Head n)
  | spinesW {n : Nat} (context : Ctx Head n) (left right type : Tm Head n)

/-- Derivations of the algorithmic equality. -/
inductive Algorithmic (R : Rules Head) (roles : Roles Head) :
    AlgorithmicStatement Head → Prop where
  -- Types
  | types {n : Nat} {Γ : Ctx Head n} {A A' B B' : Tm Head n} :
      RedTy R roles Γ A A' → RedTy R roles Γ B B' → IsTypeForm roles A' →
      IsTypeForm roles B' → Algorithmic R roles (.typesW Γ A' B') →
      Algorithmic R roles (.types Γ A B)
  | heads {n : Nat} {Γ : Ctx Head n} {h h' u : Head} :
      HeadSame R h h' → Typed R Γ (.head h) (.head u) → Typed R Γ (.head h') (.head u) →
      R.isUniverse u → Algorithmic R roles (.typesW Γ (.head h) (.head h'))
  | pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} :
      IsType R Γ A → Algorithmic R roles (.types Γ A A') →
      Algorithmic R roles (.types (.snoc Γ A) B B') →
      Algorithmic R roles (.typesW Γ (.pi A B) (.pi A' B'))
  | sigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} :
      IsType R Γ A → Algorithmic R roles (.types Γ A A') →
      Algorithmic R roles (.types (.snoc Γ A) B B') →
      Algorithmic R roles (.typesW Γ (.sigma A B) (.sigma A' B'))
  | id {n : Nat} {Γ : Ctx Head n} {A A' x x' y y' : Tm Head n} :
      Algorithmic R roles (.types Γ A A') → Algorithmic R roles (.terms Γ x x' A) →
      Algorithmic R roles (.terms Γ y y' A) →
      Algorithmic R roles (.typesW Γ (.id A x y) (.id A' x' y'))
  | inductiveType {n : Nat} {Γ : Ctx Head n} {T : DeclName}
      {ctors : List (DeclName × List (Field Head))} :
      roles T = .inductive ctors → IsType R Γ (.const T) →
      Algorithmic R roles (.typesW Γ (.const T) (.const T))
  | neutralTypes {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head} :
      Neutral roles A → Neutral roles B → R.isUniverse u →
      Algorithmic R roles (.spinesW Γ A B (.head u)) →
      Algorithmic R roles (.typesW Γ A B)
  -- Terms
  | terms {n : Nat} {Γ : Ctx Head n} {t t' u u' A A' : Tm Head n} :
      RedTy R roles Γ A A' → IsTypeForm roles A' → RedTm R roles Γ t t' A' →
      RedTm R roles Γ u u' A' → Algorithmic R roles (.termsW Γ t' u' A') →
      Algorithmic R roles (.terms Γ t u A)
  | univ {n : Nat} {Γ : Ctx Head n} {t u : Tm Head n} {h : Head} :
      R.isUniverse h → Typed R Γ t (.head h) → Typed R Γ u (.head h) →
      Algorithmic R roles (.typesW Γ t u) → Algorithmic R roles (.termsW Γ t u (.head h))
  | eta {n : Nat} {Γ : Ctx Head n} {f g A : Tm Head n} {B : Tm Head (n + 1)} :
      IsType R Γ A → Typed R Γ f (.pi A B) → IsFun roles f → Typed R Γ g (.pi A B) →
      IsFun roles g →
      Algorithmic R roles (.terms (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0))
        (.app (Presentation.rename wk g) (.var 0)) B) →
      Algorithmic R roles (.termsW Γ f g (.pi A B))
  | sigmaEta {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)} :
      Typed R Γ p (.sigma A B) → IsPair roles p → Typed R Γ q (.sigma A B) → IsPair roles q →
      Algorithmic R roles (.terms Γ (.fst p) (.fst q) A) →
      Algorithmic R roles (.terms Γ (.snd p) (.snd q) (inst0 (.fst p) B)) →
      Algorithmic R roles (.termsW Γ p q (.sigma A B))
  | refl {n : Nat} {Γ : Ctx Head n} {x x' A a b : Tm Head n} :
      Typed R Γ (.refl x) (.id A a b) → Typed R Γ (.refl x') (.id A a b) →
      Algorithmic R roles (.terms Γ x x' A) →
      Algorithmic R roles (.termsW Γ (.refl x) (.refl x') (.id A a b))
  | spine {n : Nat} {Γ : Ctx Head n} {t u A U : Tm Head n} :
      SpineType R roles A → SpineForm roles t → SpineForm roles u → Typed R Γ t A →
      Typed R Γ u A → Algorithmic R roles (.spinesW Γ t u U) →
      Algorithmic R roles (.termsW Γ t u A)
  -- Spines
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      Algorithmic R roles (.spines Γ (.var i) (.var i) (Ctx.lookup Γ i))
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} :
      R.constantType name = some type → Typed R Γ (.const name) (liftClosed type) →
      Algorithmic R roles (.spines Γ (.const name) (.const name) (liftClosed type))
  | app {n : Nat} {Γ : Ctx Head n} {f g a b A : Tm Head n} {B : Tm Head (n + 1)} :
      Algorithmic R roles (.spinesW Γ f g (.pi A B)) → Algorithmic R roles (.terms Γ a b A) →
      Algorithmic R roles (.spines Γ (.app f a) (.app g b) (inst0 a B))
  | fst {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)} :
      Algorithmic R roles (.spinesW Γ p q (.sigma A B)) →
      Algorithmic R roles (.spines Γ (.fst p) (.fst q) A)
  | snd {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)} :
      Algorithmic R roles (.spinesW Γ p q (.sigma A B)) →
      Algorithmic R roles (.spines Γ (.snd p) (.snd q) (inst0 (.fst p) B))
  | spinesW {n : Nat} {Γ : Ctx Head n} {t u U U' : Tm Head n} :
      Algorithmic R roles (.spines Γ t u U) → RedTy R roles Γ U U' → IsTypeForm roles U' →
      Algorithmic R roles (.spinesW Γ t u U')

/-! ## The kernel's conversion relation, expanded -/

section Expansion

variable {R : Rules Head}

/-- The judgments of the kernel's conversion relation remain derivable when
the compared terms and the type are reduced from further up. -/
def Expands (R : Rules Head) : AlgorithmStatement Head → Prop
  | .compare Γ a b T => ∀ {T' a' b'}, Reduces R T' T → Reduces R a' a → Reduces R b' b →
      Algorithm R (.compare Γ a' b' T')
  | .neutral Γ a b U => Algorithm R (.neutral Γ a b U)
  | .types Γ A B => ∀ {A' B'}, Reduces R A' A → Reduces R B' B → Algorithm R (.types Γ A' B')

theorem Algorithm.expands {st : AlgorithmStatement Head} (derivation : Algorithm R st) :
    Expands R st := by
  induction derivation with
  | pi red _ ih =>
      intro T' a' b' rT ra rb
      exact .pi (rT.trans red) (ih .refl (Reduces.appWk ra) (Reduces.appWk rb))
  | sigma red _ _ ih₁ ih₂ =>
      intro T' a' b' rT ra rb
      exact .sigma (rT.trans red) (ih₁ .refl (Reduces.fstArg ra) (Reduces.fstArg rb))
        (ih₂ (Reduces.inst0Arg (Reduces.fstArg ra) _) (Reduces.sndArg ra) (Reduces.sndArg rb))
  | sort red hu _ ih =>
      intro T' a' b' rT ra rb
      exact .sort (rT.trans red) hu (ih ra rb)
  | reflexivity red ra₀ rb₀ _ ih =>
      intro T' a' b' rT ra rb
      exact .reflexivity (rT.trans red) (ra.trans ra₀) (rb.trans rb₀) (ih .refl .refl .refl)
  | neutralAt ra₀ rb₀ _ ih =>
      intro T' a' b' _ ra rb
      exact .neutralAt (ra.trans ra₀) (rb.trans rb₀) ih
  | var i => exact .var i
  | const declared => exact .const declared
  | app _ red _ ihf iha => exact .app ihf red (iha .refl .refl .refl)
  | fst _ red ih => exact .fst ih red
  | snd _ red ih => exact .snd ih red
  | heads rA rB same =>
      intro A' B' rA' rB'
      exact .heads (rA'.trans rA) (rB'.trans rB) same
  | piTypes rA rB _ _ ih₁ ih₂ =>
      intro A' B' rA' rB'
      exact .piTypes (rA'.trans rA) (rB'.trans rB) (ih₁ .refl .refl) (ih₂ .refl .refl)
  | sigmaTypes rA rB _ _ ih₁ ih₂ =>
      intro A' B' rA' rB'
      exact .sigmaTypes (rA'.trans rA) (rB'.trans rB) (ih₁ .refl .refl) (ih₂ .refl .refl)
  | idTypes rA rB _ _ _ ihC ihx ihy =>
      intro A' B' rA' rB'
      exact .idTypes (rA'.trans rA) (rB'.trans rB) (ihC .refl .refl) (ihx .refl .refl .refl)
        (ihy .refl .refl .refl)
  | neutralTypes rA rB _ ih =>
      intro A' B' rA' rB'
      exact .neutralTypes (rA'.trans rA) (rB'.trans rB) ih

end Expansion

/-! ## Every derivation is one of the kernel's conversion relation -/

section Refinement

variable {R : Rules Head} {roles : Roles Head}

/-- The statement of the kernel's conversion relation a judgment refines. -/
def Refines (R : Rules Head) : AlgorithmicStatement Head → Prop
  | .types Γ A B => Algorithm R (.types Γ A B)
  | .typesW Γ A B => Algorithm R (.types Γ A B)
  | .terms Γ t u A => Algorithm R (.compare Γ t u A)
  | .termsW Γ t u A => Algorithm R (.compare Γ t u A)
  | .spines Γ t u U => Algorithm R (.neutral Γ t u U)
  | .spinesW Γ t u U => ∃ U₀, Algorithm R (.neutral Γ t u U₀) ∧ Reduces R U₀ U

theorem Algorithmic.refines {st : AlgorithmicStatement Head}
    (derivation : Algorithmic R roles st) : Refines R st := by
  induction derivation with
  | types rA rB _ _ _ ih => exact (Algorithm.expands ih) rA.red.reduces rB.red.reduces
  | heads same _ _ _ => exact .heads .refl .refl same
  | pi _ _ _ ihA ihB => exact .piTypes .refl .refl ihA ihB
  | sigma _ _ _ ihA ihB => exact .sigmaTypes .refl .refl ihA ihB
  | id _ _ _ ihA ihx ihy => exact .idTypes .refl .refl ihA ihx ihy
  | inductiveType _ isType =>
      obtain ⟨_, _, typed⟩ := isType
      obtain ⟨_, _, declared, _⟩ := Typed.generation typed
      exact .neutralTypes .refl .refl (.const declared)
  | neutralTypes _ _ _ _ ih =>
      obtain ⟨_, derivation, _⟩ := ih
      exact .neutralTypes .refl .refl derivation
  | terms rA _ rt ru _ ih =>
      exact (Algorithm.expands ih) rA.red.reduces rt.red.reduces ru.red.reduces
  | univ hu _ _ _ ih => exact .sort .refl hu ih
  | eta _ _ _ _ _ _ ih => exact .pi .refl ih
  | sigmaEta _ _ _ _ _ _ ih₁ ih₂ => exact .sigma .refl ih₁ ih₂
  | refl _ _ _ ih => exact .reflexivity .refl .refl .refl ih
  | spine _ _ _ _ _ _ ih =>
      obtain ⟨_, derivation, _⟩ := ih
      exact .neutralAt .refl .refl derivation
  | var i => exact .var i
  | const declared _ => exact .const declared
  | app _ _ ihf iha =>
      obtain ⟨_, derivation, red⟩ := ihf
      exact .app derivation red iha
  | fst _ ih =>
      obtain ⟨_, derivation, red⟩ := ih
      exact .fst derivation red
  | snd _ ih =>
      obtain ⟨_, derivation, red⟩ := ih
      exact .snd derivation red
  | spinesW _ rU _ ih => exact ⟨_, ih, rU.red.reduces⟩

end Refinement

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
