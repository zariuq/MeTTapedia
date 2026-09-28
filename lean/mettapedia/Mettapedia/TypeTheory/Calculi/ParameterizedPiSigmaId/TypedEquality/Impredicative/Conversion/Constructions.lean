import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Candidates
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Algebra

/-!
# The constructions of equality candidates, and their realizer algebra

Each construction reads the weak-head form of the realizer type, reached by
typed reduction. At a realizer type of the matching former it relates the terms
of its clause. At every other type it relates what `bot` relates: the terms
that reduce to neutral terms `E` compares. Every candidate must relate those,
so they are added at every type, and at a type of the matching former the
clause already contains them.

* `top` relates the typed terms that `E` relates; it is the greatest candidate
  (`le_top`).
* `inter F` is the meet of a family over any index type, with `top`.
* `reaching F` relates what `top` relates between terms that both reach, by
  typed reduction at the realizer type, a weak-head form of the class `F`,
  which contains the neutral terms. The types (`types`), the terms reaching the
  weak-head form of a type, realize the values of a universe; the constructed
  terms (`constructed`), those reaching a constructor applied to as many
  arguments as it declares or a neutral term, realize the codes.
* `piOver d c` is Girard's clause over an index: at `Π D C`, both terms reach
  weak-head normal functions, `E` relates them, and at every index `i`, after
  every renaming into a formed context, arguments related by `d i` give
  applications related by `c i` at the codomain instantiated at the argument.
  The index is quantified by a plain universal, so the clause depends only on
  the pairs `(d i, c i)` (`piOver_congr`).
* `sigmaOver X Y` relates, at `Σ D C`, terms reaching weak-head normal pairs
  whose projections are related by `X` and by `Y`, after every renaming.
* `ident P` relates, at an identity type, terms reaching reflexivity proofs
  when `P` holds.
* `ctorReal I k Xs` relates, at the inductive type `I`, terms reaching the
  constructor `k` of `I` applied to arguments related field by field by `Xs`,
  at the field types that `I` declares; `stuckReal I` is `bot`.

The laws of each construction are those of a candidate. Typed equality of the
realizer type is handled by the facts about weak-head forms of the realizer
side: equal types reach matching forms, whose parts are equal, and the
candidates the construction is built from are invariant under equality of
those parts. Subtyping of the realizer type is handled by its inversion
(`RealizerSide.pi_of_below`, `RealizerSide.sigma_of_below`,
`RealizerSide.typeEq_of_below`): a type usable at another reaching a dependent
function type makes the other reach one, with an equal domain and a codomain
usable at the other's; dependent pair types keep both components usable at the
other's; an identity type or the type constant of an inductive type is usable
only at types equal to it. The candidates the construction is built from are
cumulative along those parts, and neutral terms that `E` compares at a type are
compared at every type it is usable at.

The realizer algebra of equality candidates (`ecandAlgebra`) has the laws of a
realizer algebra (`ecandAlgebra_laws`): the meet of a nonempty constant family
is its value, and meets and Girard's clause depend only on what they range
over. Membership facts, such as which proofs of a true proposition `ident`
relates, stay with the model, and so do inclusions: the constructions are
monotone in what they range over (`piOver_mono`, `inter_mono`,
`sigmaOver_mono`, `ident_mono`, `ctorReal_mono`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)
open ValueSide (RealizerAlgebra)

variable {Head L : Type} [LevelOrder L] {T : RealizerSide Head L}

/-! ## Realizer types of a dependent function or pair type, in a world -/

section Forms

variable {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k} {ρ : Ren m k} {A D : Tm Head m}
  {C : Tm Head (m + 1)}

/-- A type reaches at most one dependent function type. -/
theorem pi_unique {D' : Tm Head m} {C' : Tm Head (m + 1)}
    (h : RedTy T.R T.roles Δ A (.pi D C)) (h' : RedTy T.R T.roles Δ A (.pi D' C')) :
    D = D' ∧ C = C' := by
  have e := WhRed.whnf_unique T.shape h.red h'.red (pi_whnf T.shape D C) (pi_whnf T.shape D' C')
  cases e
  exact ⟨rfl, rfl⟩

/-- A type reaches at most one dependent pair type. -/
theorem sigma_unique {D' : Tm Head m} {C' : Tm Head (m + 1)}
    (h : RedTy T.R T.roles Δ A (.sigma D C)) (h' : RedTy T.R T.roles Δ A (.sigma D' C')) :
    D = D' ∧ C = C' := by
  have e := WhRed.whnf_unique T.shape h.red h'.red (sigma_whnf T.shape D C)
    (sigma_whnf T.shape D' C')
  cases e
  exact ⟨rfl, rfl⟩

/-- After a renaming, a type reducing to `Π D C` is equal to the renamed
dependent function type. -/
theorem pi_typeEq (hA : RedTy T.R T.roles Δ A (.pi D C)) (ren : CtxRen Δ Θ ρ) :
    TypeEq T.R Θ (Presentation.rename ρ A)
      (.pi (Presentation.rename ρ D) (Presentation.rename (liftRen ρ) C)) :=
  hA.typeEq.rename ren

/-- The codomain of a type reducing to `Π D C` is a type family over `D`,
after every renaming. -/
theorem pi_family (hA : RedTy T.R T.roles Δ A (.pi D C)) (ren : CtxRen Δ Θ ρ) :
    ∃ v, T.R.isUniverse v ∧ Typed T.R (.snoc Θ (Presentation.rename ρ D))
      (Presentation.rename (liftRen ρ) C) (.head v) := by
  obtain ⟨-, v, hv, tC⟩ := IsType.pi_parts hA.targetType
  exact ⟨v, hv, Typed.rename tC (ren.snoc D)⟩

/-- Equal arguments instantiate the codomain of a dependent function type at
equal types, after every renaming. -/
theorem pi_codEq (hA : RedTy T.R T.roles Δ A (.pi D C)) (ren : CtxRen Δ Θ ρ)
    {s s' : Tm Head k} (ts : Typed T.R Θ s (Presentation.rename ρ D))
    (e : Equal T.R Θ s s' (Presentation.rename ρ D)) :
    TypeEq T.R Θ (inst0 s (Presentation.rename (liftRen ρ) C))
      (inst0 s' (Presentation.rename (liftRen ρ) C)) := by
  obtain ⟨v, hv, tC⟩ := pi_family hA ren
  exact TypeEq.of_instantiateEq tC hv ts e

/-- An application, after a renaming, of a term of a type reducing to `Π D C`. -/
theorem pi_appTyped (hA : RedTy T.R T.roles Δ A (.pi D C)) (ren : CtxRen Δ Θ ρ)
    {t : Tm Head m} (ht : Typed T.R Δ t A) {s : Tm Head k}
    (ts : Typed T.R Θ s (Presentation.rename ρ D)) :
    Typed T.R Θ (.app (Presentation.rename ρ t) s) (inst0 s (Presentation.rename (liftRen ρ) C)) :=
  .appElim (Typed.convType (Typed.rename ht ren) (pi_typeEq hA ren)) ts

/-- Typed reduction of a function, after a renaming, reduces its applications. -/
theorem pi_appRed (hA : RedTy T.R T.roles Δ A (.pi D C)) (ren : CtxRen Δ Θ ρ)
    {t u : Tm Head m} (red : RedTm T.R T.roles Δ t u A) {s : Tm Head k}
    (ts : Typed T.R Θ s (Presentation.rename ρ D)) :
    RedTm T.R T.roles Θ (.app (Presentation.rename ρ t) s) (.app (Presentation.rename ρ u) s)
      (inst0 s (Presentation.rename (liftRen ρ) C)) :=
  ((red.rename ren).conv (pi_typeEq hA ren)).app ts

/-- After a renaming, a type reducing to `Σ D C` is equal to the renamed
dependent pair type. -/
theorem sigma_typeEq (hA : RedTy T.R T.roles Δ A (.sigma D C)) (ren : CtxRen Δ Θ ρ) :
    TypeEq T.R Θ (Presentation.rename ρ A)
      (.sigma (Presentation.rename ρ D) (Presentation.rename (liftRen ρ) C)) :=
  hA.typeEq.rename ren

/-- The codomain of a type reducing to `Σ D C` is a type family over `D`, after
every renaming. -/
theorem sigma_family (hA : RedTy T.R T.roles Δ A (.sigma D C)) (ren : CtxRen Δ Θ ρ) :
    ∃ v, T.R.isUniverse v ∧ Typed T.R (.snoc Θ (Presentation.rename ρ D))
      (Presentation.rename (liftRen ρ) C) (.head v) := by
  obtain ⟨-, v, hv, tC⟩ := IsType.sigma_parts hA.targetType
  exact ⟨v, hv, Typed.rename tC (ren.snoc D)⟩

/-- Equal first projections instantiate the codomain of a dependent pair type
at equal types, after every renaming. -/
theorem sigma_codEq (hA : RedTy T.R T.roles Δ A (.sigma D C)) (ren : CtxRen Δ Θ ρ)
    {s s' : Tm Head k} (ts : Typed T.R Θ s (Presentation.rename ρ D))
    (e : Equal T.R Θ s s' (Presentation.rename ρ D)) :
    TypeEq T.R Θ (inst0 s (Presentation.rename (liftRen ρ) C))
      (inst0 s' (Presentation.rename (liftRen ρ) C)) := by
  obtain ⟨v, hv, tC⟩ := sigma_family hA ren
  exact TypeEq.of_instantiateEq tC hv ts e

/-- Typed reduction of a pair, after a renaming, reduces its first projection. -/
theorem sigma_fstRed (hA : RedTy T.R T.roles Δ A (.sigma D C)) (ren : CtxRen Δ Θ ρ)
    {t u : Tm Head m} (red : RedTm T.R T.roles Δ t u A) :
    RedTm T.R T.roles Θ (.fst (Presentation.rename ρ t)) (.fst (Presentation.rename ρ u))
      (Presentation.rename ρ D) :=
  ((red.rename ren).conv (sigma_typeEq hA ren)).fst

/-- Typed reduction of a pair, after a renaming, reduces its second projection. -/
theorem sigma_sndRed (hA : RedTy T.R T.roles Δ A (.sigma D C)) (ren : CtxRen Δ Θ ρ)
    {t u : Tm Head m} (red : RedTm T.R T.roles Δ t u A) :
    RedTm T.R T.roles Θ (.snd (Presentation.rename ρ t)) (.snd (Presentation.rename ρ u))
      (inst0 (.fst (Presentation.rename ρ t)) (Presentation.rename (liftRen ρ) C)) := by
  obtain ⟨v, hv, tC⟩ := sigma_family hA ren
  exact RedTm.snd tC hv ((red.rename ren).conv (sigma_typeEq hA ren))

/-- The second projection, after a renaming, of a term of a type reducing to
`Σ D C`. -/
theorem sigma_sndTyped (hA : RedTy T.R T.roles Δ A (.sigma D C)) (ren : CtxRen Δ Θ ρ)
    {t : Tm Head m} (ht : Typed T.R Δ t A) :
    Typed T.R Θ (.snd (Presentation.rename ρ t))
      (inst0 (.fst (Presentation.rename ρ t)) (Presentation.rename (liftRen ρ) C)) :=
  .sndElim (Typed.convType (Typed.rename ht ren) (sigma_typeEq hA ren))

/-- Two families over one domain, the first usable at the second, instantiated
at one argument of the domain. -/
theorem below_instantiate {R : Rules Head} {X Y : Tm Head (k + 1)} {s : Tm Head k}
    (le : Below R (.snoc Θ (Presentation.rename ρ D)) X Y)
    (typing : Typed R Θ s (Presentation.rename ρ D)) : Below R Θ (inst0 s X) (inst0 s Y) :=
  Derivable.substitutes le (SubstMor.single typing)

end Forms

namespace ECand

variable {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

/-! ## The greatest candidate -/

variable (T) in
/-- The greatest candidate: the terms typed at the realizer type that `E`
relates. -/
def top : ECand T where
  rel := fun Δ A t t' => Typed T.R Δ t A ∧ Typed T.R Δ t' A ∧ T.E.convTm Δ t t' A
  typed := fun h => ⟨h.1, h.2.1⟩
  escape := fun h => h.2.2
  neutral := fun nt nt' ht ht' cv => ⟨ht, ht', T.laws.convTm_of_convNe (.inl nt) (.inl nt') cv⟩
  expand := fun red red' h => ⟨red.source, red'.source, T.laws.convTm_expand red red' h.2.2⟩
  symm := fun h => ⟨h.2.1, h.1, T.laws.convTm_symm h.2.2⟩
  trans := fun h h' => ⟨h.1, h'.2.1, T.laws.convTm_trans h.2.2 h'.2.2⟩
  rename := fun ren formed h =>
    ⟨Typed.rename h.1 ren, Typed.rename h.2.1 ren, T.laws.convTm_rename ren formed h.2.2⟩
  typeConv := fun _ equal => funext fun _ => funext fun _ => propext
    ⟨fun h => ⟨Typed.convType h.1 equal, Typed.convType h.2.1 equal,
        T.laws.convTm_conv h.2.2 equal⟩,
      fun h => ⟨Typed.convType h.1 equal.symm, Typed.convType h.2.1 equal.symm,
        T.laws.convTm_conv h.2.2 equal.symm⟩⟩
  below := fun _ le h => ⟨.sub h.1 le, .sub h.2.1 le, T.laws.convTm_below h.2.2 le⟩

/-- **`top` is the greatest candidate.** -/
theorem le_top (X : ECand T) (h : X.rel Δ A t t') : (top T).rel Δ A t t' :=
  ⟨(X.typed h).1, (X.typed h).2, X.escape h⟩

/-! ## Meets -/

/-- The meet of a family of candidates: the terms `top` relates that every
candidate of the family relates. -/
def inter {ι : Type} (F : ι → ECand T) : ECand T where
  rel := fun Δ A t t' => (top T).rel Δ A t t' ∧ ∀ i, (F i).rel Δ A t t'
  typed := fun h => (top T).typed h.1
  escape := fun h => (top T).escape h.1
  neutral := fun nt nt' ht ht' cv =>
    ⟨(top T).neutral nt nt' ht ht' cv, fun i => (F i).neutral nt nt' ht ht' cv⟩
  expand := fun red red' h => ⟨(top T).expand red red' h.1, fun i => (F i).expand red red' (h.2 i)⟩
  symm := fun h => ⟨(top T).symm h.1, fun i => (F i).symm (h.2 i)⟩
  trans := fun h h' => ⟨(top T).trans h.1 h'.1, fun i => (F i).trans (h.2 i) (h'.2 i)⟩
  rename := fun ren formed h =>
    ⟨(top T).rename ren formed h.1, fun i => (F i).rename ren formed (h.2 i)⟩
  typeConv := fun formed equal => funext fun _ => funext fun _ => propext
    ⟨fun h => ⟨(top T).conv formed equal h.1, fun i => (F i).conv formed equal (h.2 i)⟩,
      fun h => ⟨(top T).conv formed equal.symm h.1,
        fun i => (F i).conv formed equal.symm (h.2 i)⟩⟩
  below := fun formed le h =>
    ⟨(top T).below formed le h.1, fun i => (F i).below formed le (h.2 i)⟩

end ECand

/-! ## Terms reaching a weak-head form -/

/-- A class of weak-head forms that contains every neutral term and is closed
under renaming: the forms a candidate may ask its terms to reach. -/
structure FormClass (roles : Roles Head) where
  /-- The forms. -/
  holds : ∀ {m : Nat}, Tm Head m → Prop
  /-- Every neutral term is a form. -/
  neutral : ∀ {m : Nat} {t : Tm Head m}, Neutral roles t → holds t
  /-- A renamed form is a form. -/
  rename : ∀ {m k : Nat} (ρ : Ren m k) {t : Tm Head m}, holds t →
    holds (Presentation.rename ρ t)

variable (T) in
/-- A term that reaches, by typed reduction at `A`, a form of the class `F`. -/
def ReachesForm (F : FormClass T.roles) {m : Nat} (Δ : Ctx Head m) (A t : Tm Head m) : Prop :=
  ∃ w, RedTm T.R T.roles Δ t w A ∧ F.holds w

namespace ReachesForm

variable {F : FormClass T.roles} {m : Nat} {Δ : Ctx Head m} {A t : Tm Head m}

/-- A typed neutral term reaches a form: itself. -/
theorem of_neutral (nt : Neutral T.roles t) (ht : Typed T.R Δ t A) : ReachesForm T F Δ A t :=
  ⟨t, .refl ht, F.neutral nt⟩

theorem expand {u : Tm Head m} (red : RedTm T.R T.roles Δ t u A) (h : ReachesForm T F Δ A u) :
    ReachesForm T F Δ A t := by
  obtain ⟨w, r, fw⟩ := h
  exact ⟨w, red.trans r, fw⟩

theorem rename {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k} (ren : CtxRen Δ Θ ρ)
    (h : ReachesForm T F Δ A t) :
    ReachesForm T F Θ (Presentation.rename ρ A) (Presentation.rename ρ t) := by
  obtain ⟨w, r, fw⟩ := h
  exact ⟨_, r.rename ren, F.rename ρ fw⟩

theorem below {B : Tm Head m} (le : Below T.R Δ A B) (h : ReachesForm T F Δ A t) :
    ReachesForm T F Δ B t := by
  obtain ⟨w, r, fw⟩ := h
  exact ⟨w, r.below le, fw⟩

end ReachesForm

namespace ECand

/-- **The terms reaching a form of a class**: the terms `top` relates that both
reach, by typed reduction at the realizer type, a form of the class `F`. -/
def reaching (F : FormClass T.roles) : ECand T where
  rel := fun Δ A t t' =>
    (top T).rel Δ A t t' ∧ ReachesForm T F Δ A t ∧ ReachesForm T F Δ A t'
  typed := fun h => (top T).typed h.1
  escape := fun h => (top T).escape h.1
  neutral := fun nt nt' ht ht' cv =>
    ⟨(top T).neutral nt nt' ht ht' cv, .of_neutral nt ht, .of_neutral nt' ht'⟩
  expand := fun red red' h => ⟨(top T).expand red red' h.1, h.2.1.expand red, h.2.2.expand red'⟩
  symm := fun h => ⟨(top T).symm h.1, h.2.2, h.2.1⟩
  trans := fun h h' => ⟨(top T).trans h.1 h'.1, h.2.1, h'.2.2⟩
  rename := fun ren formed h =>
    ⟨(top T).rename ren formed h.1, h.2.1.rename ren, h.2.2.rename ren⟩
  typeConv := fun formed equal => funext fun _ => funext fun _ => propext
    ⟨fun h => ⟨(top T).conv formed equal h.1, h.2.1.below equal.below,
        h.2.2.below equal.below⟩,
      fun h => ⟨(top T).conv formed equal.symm h.1, h.2.1.below equal.symm.below,
        h.2.2.below equal.symm.below⟩⟩
  below := fun formed le h => ⟨(top T).below formed le h.1, h.2.1.below le, h.2.2.below le⟩

end ECand

/-- The weak-head forms of types, as a class of forms. -/
def typeForms (roles : Roles Head) : FormClass roles where
  holds := fun t => IsTypeForm roles t
  neutral := fun neutral => .inr (.inr (.inr (.inr (.inl neutral))))
  rename := fun ρ _ form => form.rename ρ

/-- A constructor applied to as many arguments as it declares, or a neutral
term. -/
def IsCtorForm (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  (∃ k a args, roles k = .constructor a ∧ args.length = a ∧ t = appSpine (.const k) args) ∨
    Neutral roles t

theorem IsCtorForm.rename {roles : Roles Head} {n m : Nat} {t : Tm Head n}
    (form : IsCtorForm roles t) (ρ : Ren n m) : IsCtorForm roles (Presentation.rename ρ t) := by
  rcases form with ⟨k, a, args, role, length, rfl⟩ | neutral
  · refine .inl ⟨k, a, args.map (Presentation.rename ρ), role, ?_, rename_appSpine ρ _ args⟩
    rw [List.length_map]
    exact length
  · exact .inr (neutral.rename ρ)

/-- Constructors applied to their arguments, and neutral terms, as a class of
forms. -/
def ctorForms (roles : Roles Head) : FormClass roles where
  holds := fun t => IsCtorForm roles t
  neutral := fun neutral => .inr neutral
  rename := fun ρ _ form => form.rename ρ

namespace ECand

variable (T) in
/-- **The types**: the terms `top` relates that reach the weak-head form of a
type. They realize the values of a universe. -/
def types : ECand T := reaching (typeForms T.roles)

variable (T) in
/-- **The constructed terms**: the terms `top` relates that reach a constructor
applied to as many arguments as it declares, or a neutral term. At a type of
codes, whose typed constructor spines are the code constructors applied to
their arguments, they are the codes. -/
def constructed : ECand T := reaching (ctorForms T.roles)

variable {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

/-- The types relate the terms `top` relates that reach type forms. -/
theorem types_rel : (types T).rel Δ A t t' ↔ (top T).rel Δ A t t' ∧
    (∃ w, RedTm T.R T.roles Δ t w A ∧ IsTypeForm T.roles w) ∧
      ∃ w', RedTm T.R T.roles Δ t' w' A ∧ IsTypeForm T.roles w' :=
  Iff.rfl

/-- The constructed terms relate the terms `top` relates that reach constructor
forms. -/
theorem constructed_rel : (constructed T).rel Δ A t t' ↔ (top T).rel Δ A t t' ∧
    (∃ w, RedTm T.R T.roles Δ t w A ∧ IsCtorForm T.roles w) ∧
      ∃ w', RedTm T.R T.roles Δ t' w' A ∧ IsCtorForm T.roles w' :=
  Iff.rfl

end ECand

/-! ## Girard's clause over an index -/

variable (T) in
/-- A term that reaches, typed at `A`, a weak-head normal form of a function. -/
def FunNf {m : Nat} (Δ : Ctx Head m) (A t : Tm Head m) : Prop :=
  ∃ w, RedTm T.R T.roles Δ t w A ∧ IsFun T.roles w

/-- Applications after every renaming into a formed context: arguments related
by `X` at the renamed domain `D` give applications related by `Y` at the
codomain `C` instantiated at the left argument. -/
def AppClause (X Y : ECand T) {m : Nat} (Δ : Ctx Head m) (D : Tm Head m) (C : Tm Head (m + 1))
    (t t' : Tm Head m) : Prop :=
  ∀ {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k}, World T.toSetting Δ Θ ρ →
    ∀ {s s' : Tm Head k}, X.rel Θ (Presentation.rename ρ D) s s' →
      Y.rel Θ (inst0 s (Presentation.rename (liftRen ρ) C))
        (.app (Presentation.rename ρ t) s) (.app (Presentation.rename ρ t') s')

/-- Girard's clause at a realizer type reducing to `Π D C`: both terms reach
weak-head normal functions, `E` relates them, and at every index `i` their
applications satisfy `AppClause (d i) (c i)`. -/
def PiClause {ι : Type} (d c : ι → ECand T) {m : Nat} (Δ : Ctx Head m) (A t t' : Tm Head m) :
    Prop :=
  ∃ D C, RedTy T.R T.roles Δ A (.pi D C) ∧ FunNf T Δ A t ∧ FunNf T Δ A t' ∧
    T.E.convTm Δ t t' A ∧ ∀ i, AppClause (d i) (c i) Δ D C t t'

namespace PiClause

variable {ι : Type} {d c : ι → ECand T} {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

theorem typed (h : PiClause d c Δ A t t') : Typed T.R Δ t A ∧ Typed T.R Δ t' A := by
  obtain ⟨-, -, -, ⟨_, r, -⟩, ⟨_, r', -⟩, -⟩ := h
  exact ⟨r.source, r'.source⟩

theorem escape (h : PiClause d c Δ A t t') : T.E.convTm Δ t t' A := by
  obtain ⟨-, -, -, -, -, cv, -⟩ := h
  exact cv

theorem expand {u u' : Tm Head m} (red : RedTm T.R T.roles Δ t u A)
    (red' : RedTm T.R T.roles Δ t' u' A) (h : PiClause d c Δ A u u') :
    PiClause d c Δ A t t' := by
  obtain ⟨D, C, hA, ⟨w, r, fw⟩, ⟨w', r', fw'⟩, cv, app⟩ := h
  refine ⟨D, C, hA, ⟨w, red.trans r, fw⟩, ⟨w', red'.trans r', fw'⟩,
    T.laws.convTm_expand red red' cv, fun i => ?_⟩
  intro k Θ ρ world s s' hs
  obtain ⟨ts, ts'⟩ := (d i).typed hs
  have e := pi_codEq hA world.1 ts ((d i).equal hs)
  exact (c i).expand (pi_appRed hA world.1 red ts) ((pi_appRed hA world.1 red' ts').conv e.symm)
    (app i world hs)

theorem symm (h : PiClause d c Δ A t t') : PiClause d c Δ A t' t := by
  obtain ⟨D, C, hA, f, f', cv, app⟩ := h
  refine ⟨D, C, hA, f', f, T.laws.convTm_symm cv, fun i => ?_⟩
  intro k Θ ρ world s s' hs
  have e := pi_codEq hA world.1 ((d i).typed hs).2 ((d i).equal ((d i).symm hs))
  exact (c i).conv world.2 e ((c i).symm (app i world ((d i).symm hs)))

theorem trans {t'' : Tm Head m} (h : PiClause d c Δ A t t') (h' : PiClause d c Δ A t' t'') :
    PiClause d c Δ A t t'' := by
  obtain ⟨D, C, hA, f, -, cv, app⟩ := h
  obtain ⟨D', C', hA', -, f'', cv', app'⟩ := h'
  obtain ⟨rfl, rfl⟩ := pi_unique hA hA'
  refine ⟨D, C, hA, f, f'', T.laws.convTm_trans cv cv', fun i => ?_⟩
  intro k Θ ρ world s s' hs
  exact (c i).trans (app i world ((d i).refl_left hs)) (app' i world hs)

theorem rename {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k} (world : World T.toSetting Δ Θ ρ)
    (h : PiClause d c Δ A t t') :
    PiClause d c Θ (Presentation.rename ρ A) (Presentation.rename ρ t)
      (Presentation.rename ρ t') := by
  obtain ⟨D, C, hA, ⟨w, r, fw⟩, ⟨w', r', fw'⟩, cv, app⟩ := h
  refine ⟨Presentation.rename ρ D, Presentation.rename (liftRen ρ) C, hA.rename world.1,
    ⟨_, r.rename world.1, fw.rename ρ⟩, ⟨_, r'.rename world.1, fw'.rename ρ⟩,
    T.laws.convTm_rename world.1 world.2 cv, fun i => ?_⟩
  intro k' Θ' ρ' world' s s' hs
  rw [rename_rename] at hs
  have h := app i (world.comp world') hs
  rw [rename_rename_lift, rename_rename ρ ρ' t, rename_rename ρ ρ' t']
  exact h

theorem conv {B : Tm Head m} (formed : CtxFormed T.R Δ) (equal : TypeEq T.R Δ A B)
    (h : PiClause d c Δ A t t') : PiClause d c Δ B t t' := by
  obtain ⟨D, C, hA, ⟨w, r, fw⟩, ⟨w', r', fw'⟩, cv, app⟩ := h
  obtain ⟨D', C', hB, eD, eC⟩ := RealizerSide.pi_of_typeEq formed hA equal
  refine ⟨D', C', hB, ⟨w, r.conv equal, fw⟩, ⟨w', r'.conv equal, fw'⟩,
    T.laws.convTm_conv cv equal, fun i => ?_⟩
  intro k Θ ρ world s s' hs
  have hs' : (d i).rel Θ (Presentation.rename ρ D) s s' :=
    (d i).conv world.2 (eD.rename world.1).symm hs
  have eC' := TypeEq.instantiate (eC.rename (world.1.snoc D)) ((d i).typed hs').1
  exact (c i).conv world.2 eC' (app i world hs')

/-- Girard's clause at a realizer type holds at every type it is usable at: that
type reduces to a dependent function type with an equal domain, whose codomain
the first codomain is usable at, and the codomain candidates are cumulative. -/
theorem below {B : Tm Head m} (formed : CtxFormed T.R Δ) (le : Below T.R Δ A B)
    (h : PiClause d c Δ A t t') : PiClause d c Δ B t t' := by
  obtain ⟨D, C, hA, ⟨w, r, fw⟩, ⟨w', r', fw'⟩, cv, app⟩ := h
  obtain ⟨D', C', hB, eD, leC⟩ := RealizerSide.pi_of_below formed hA le
  refine ⟨D', C', hB, ⟨w, r.below le, fw⟩, ⟨w', r'.below le, fw'⟩,
    T.laws.convTm_below cv le, fun i => ?_⟩
  intro k Θ ρ world s s' hs
  have hs' : (d i).rel Θ (Presentation.rename ρ D) s s' :=
    (d i).conv world.2 (eD.rename world.1).symm hs
  exact (c i).below world.2
    (below_instantiate (Derivable.renames leC (world.1.snoc D)) ((d i).typed hs').1)
    (app i world hs')

/-- At a type reducing to a dependent function type, the terms reducing to
neutral terms that `E` compares satisfy Girard's clause. -/
theorem of_neRel {D : Tm Head m} {C : Tm Head (m + 1)} (hA : RedTy T.R T.roles Δ A (.pi D C))
    (h : NeRel T Δ A t t') : PiClause d c Δ A t t' := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  refine ⟨D, C, hA, ⟨w, r, .inr (.inl nw)⟩, ⟨w', r', .inr (.inl nw')⟩,
    NeRel.escape ⟨w, w', r, r', nw, nw', cv⟩, fun i => ?_⟩
  intro k Θ ρ world s s' hs
  obtain ⟨ts, ts'⟩ := (d i).typed hs
  have e := pi_codEq hA world.1 ts ((d i).equal hs)
  have cvw := T.laws.convNe_conv (T.laws.convNe_rename world.1 world.2 cv) (pi_typeEq hA world.1)
  have related := (c i).neutral (.app (nw.rename ρ)) (.app (nw'.rename ρ))
    (pi_appTyped hA world.1 r.target ts)
    (Typed.convType (pi_appTyped hA world.1 r'.target ts') e.symm)
    (T.laws.convNe_app cvw ((d i).escape hs))
  exact (c i).expand (pi_appRed hA world.1 r ts) ((pi_appRed hA world.1 r' ts').conv e.symm)
    related

/-- Girard's clause depends only on the pairs of candidates it ranges over. -/
theorem congr {κ : Type} {d' c' : κ → ECand T}
    (fg : ∀ i, ∃ j, d i = d' j ∧ c i = c' j) (gf : ∀ j, ∃ i, d i = d' j ∧ c i = c' j) :
    PiClause d c Δ A t t' ↔ PiClause d' c' Δ A t t' := by
  constructor
  · rintro ⟨D, C, hA, f, f', cv, app⟩
    refine ⟨D, C, hA, f, f', cv, fun j => ?_⟩
    obtain ⟨i, ed, ec⟩ := gf j
    rw [← ed, ← ec]
    exact app i
  · rintro ⟨D, C, hA, f, f', cv, app⟩
    refine ⟨D, C, hA, f, f', cv, fun i => ?_⟩
    obtain ⟨j, ed, ec⟩ := fg i
    rw [ed, ec]
    exact app j

end PiClause

namespace ECand

/-- **Girard's clause over an index**: at a realizer type reducing to a dependent
function type, the terms of `PiClause`; at every type, the terms reducing to
neutral terms that `E` compares. -/
def piOver {ι : Type} (d c : ι → ECand T) : ECand T where
  rel := fun Δ A t t' => NeRel T Δ A t t' ∨ PiClause d c Δ A t t'
  typed := fun h => h.elim NeRel.typed PiClause.typed
  escape := fun h => h.elim NeRel.escape PiClause.escape
  neutral := fun nt nt' ht ht' cv => .inl (NeRel.of_neutral nt nt' ht ht' cv)
  expand := fun red red' h => h.imp (NeRel.expand red red') (PiClause.expand red red')
  symm := fun h => h.imp NeRel.symm PiClause.symm
  trans := fun h h' => by
    rcases h with h | h <;> rcases h' with h' | h'
    · exact .inl (h.trans h')
    · rcases id h' with ⟨D, C, hA, -⟩
      exact .inr ((PiClause.of_neRel hA h).trans h')
    · rcases id h with ⟨D, C, hA, -⟩
      exact .inr (h.trans (PiClause.of_neRel hA h'))
    · exact .inr (h.trans h')
  rename := fun ren formed h => h.imp (NeRel.rename ren formed) (PiClause.rename ⟨ren, formed⟩)
  typeConv := fun formed equal => funext fun _ => funext fun _ => propext
    ⟨fun h => h.imp (NeRel.conv equal) (PiClause.conv formed equal),
      fun h => h.imp (NeRel.conv equal.symm) (PiClause.conv formed equal.symm)⟩
  below := fun formed le h => h.imp (NeRel.below le) (PiClause.below formed le)

variable {ι : Type} {d c : ι → ECand T} {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

/-- At a realizer type reducing to `Π D C`, Girard's clause is exactly: weak-head
normal functions, related by `E`, whose applications satisfy `AppClause` at
every index. -/
theorem piOver_rel_pi {D : Tm Head m} {C : Tm Head (m + 1)}
    (hA : RedTy T.R T.roles Δ A (.pi D C)) :
    (piOver d c).rel Δ A t t' ↔ FunNf T Δ A t ∧ FunNf T Δ A t' ∧ T.E.convTm Δ t t' A ∧
      ∀ i, AppClause (d i) (c i) Δ D C t t' := by
  constructor
  · intro h
    obtain ⟨D', C', hA', f, f', cv, app⟩ := h.elim (PiClause.of_neRel hA) id
    obtain ⟨rfl, rfl⟩ := pi_unique hA hA'
    exact ⟨f, f', cv, app⟩
  · rintro ⟨f, f', cv, app⟩
    exact .inr ⟨D, C, hA, f, f', cv, app⟩

/-- At a realizer type that reaches no dependent function type, Girard's clause
is `bot`. -/
theorem piOver_rel_of_not_pi (hA : ∀ D C, ¬ RedTy T.R T.roles Δ A (.pi D C)) :
    (piOver d c).rel Δ A t t' ↔ (bot T).rel Δ A t t' :=
  ⟨fun h => h.elim id fun ⟨D, C, h, _⟩ => absurd h (hA D C), .inl⟩

end ECand

/-! ## Pairs -/

variable (T) in
/-- A term that reaches, typed at `A`, a weak-head normal form of a pair. -/
def PairNf {m : Nat} (Δ : Ctx Head m) (A t : Tm Head m) : Prop :=
  ∃ w, RedTm T.R T.roles Δ t w A ∧ IsPair T.roles w

/-- Projections after every renaming into a formed context: first projections
related by `X` at the renamed domain `D`, second projections related by `Y` at
the codomain `C` instantiated at the left first projection. -/
def ProjClause (X Y : ECand T) {m : Nat} (Δ : Ctx Head m) (D : Tm Head m) (C : Tm Head (m + 1))
    (t t' : Tm Head m) : Prop :=
  ∀ {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k}, World T.toSetting Δ Θ ρ →
    X.rel Θ (Presentation.rename ρ D) (.fst (Presentation.rename ρ t))
        (.fst (Presentation.rename ρ t')) ∧
      Y.rel Θ (inst0 (.fst (Presentation.rename ρ t)) (Presentation.rename (liftRen ρ) C))
        (.snd (Presentation.rename ρ t)) (.snd (Presentation.rename ρ t'))

/-- The pairs at a realizer type reducing to `Σ D C`: both terms reach weak-head
normal pairs, `E` relates them, and their projections satisfy `ProjClause`. -/
def SigmaClause (X Y : ECand T) {m : Nat} (Δ : Ctx Head m) (A t t' : Tm Head m) : Prop :=
  ∃ D C, RedTy T.R T.roles Δ A (.sigma D C) ∧ PairNf T Δ A t ∧ PairNf T Δ A t' ∧
    T.E.convTm Δ t t' A ∧ ProjClause X Y Δ D C t t'

namespace SigmaClause

variable {X Y : ECand T} {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

theorem typed (h : SigmaClause X Y Δ A t t') : Typed T.R Δ t A ∧ Typed T.R Δ t' A := by
  obtain ⟨-, -, -, ⟨_, r, -⟩, ⟨_, r', -⟩, -⟩ := h
  exact ⟨r.source, r'.source⟩

theorem escape (h : SigmaClause X Y Δ A t t') : T.E.convTm Δ t t' A := by
  obtain ⟨-, -, -, -, -, cv, -⟩ := h
  exact cv

theorem expand {u u' : Tm Head m} (red : RedTm T.R T.roles Δ t u A)
    (red' : RedTm T.R T.roles Δ t' u' A) (h : SigmaClause X Y Δ A u u') :
    SigmaClause X Y Δ A t t' := by
  obtain ⟨D, C, hA, ⟨w, r, pw⟩, ⟨w', r', pw'⟩, cv, proj⟩ := h
  refine ⟨D, C, hA, ⟨w, red.trans r, pw⟩, ⟨w', red'.trans r', pw'⟩,
    T.laws.convTm_expand red red' cv, ?_⟩
  intro k Θ ρ world
  obtain ⟨h₁, h₂⟩ := proj world
  have f := sigma_fstRed hA world.1 red
  have f' := sigma_fstRed hA world.1 red'
  have first := X.expand f f' h₁
  have e := sigma_codEq hA world.1 f.target f.equal.symm
  have e' := sigma_codEq hA world.1 f'.source (X.equal (X.symm first))
  exact ⟨first, Y.expand (sigma_sndRed hA world.1 red) ((sigma_sndRed hA world.1 red').conv e')
    (Y.conv world.2 e h₂)⟩

theorem symm (h : SigmaClause X Y Δ A t t') : SigmaClause X Y Δ A t' t := by
  obtain ⟨D, C, hA, p, p', cv, proj⟩ := h
  refine ⟨D, C, hA, p', p, T.laws.convTm_symm cv, ?_⟩
  intro k Θ ρ world
  obtain ⟨h₁, h₂⟩ := proj world
  have e := sigma_codEq hA world.1 (X.typed h₁).1 (X.equal h₁)
  exact ⟨X.symm h₁, Y.conv world.2 e (Y.symm h₂)⟩

theorem trans {t'' : Tm Head m} (h : SigmaClause X Y Δ A t t') (h' : SigmaClause X Y Δ A t' t'') :
    SigmaClause X Y Δ A t t'' := by
  obtain ⟨D, C, hA, p, -, cv, proj⟩ := h
  obtain ⟨D', C', hA', -, p'', cv', proj'⟩ := h'
  obtain ⟨rfl, rfl⟩ := sigma_unique hA hA'
  refine ⟨D, C, hA, p, p'', T.laws.convTm_trans cv cv', ?_⟩
  intro k Θ ρ world
  obtain ⟨h₁, h₂⟩ := proj world
  obtain ⟨h₁', h₂'⟩ := proj' world
  have e := sigma_codEq hA world.1 (X.typed h₁).2 (X.equal (X.symm h₁))
  exact ⟨X.trans h₁ h₁', Y.trans h₂ (Y.conv world.2 e h₂')⟩

theorem rename {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k} (world : World T.toSetting Δ Θ ρ)
    (h : SigmaClause X Y Δ A t t') :
    SigmaClause X Y Θ (Presentation.rename ρ A) (Presentation.rename ρ t)
      (Presentation.rename ρ t') := by
  obtain ⟨D, C, hA, ⟨w, r, pw⟩, ⟨w', r', pw'⟩, cv, proj⟩ := h
  refine ⟨Presentation.rename ρ D, Presentation.rename (liftRen ρ) C, hA.rename world.1,
    ⟨_, r.rename world.1, pw.rename ρ⟩, ⟨_, r'.rename world.1, pw'.rename ρ⟩,
    T.laws.convTm_rename world.1 world.2 cv, ?_⟩
  intro k' Θ' ρ' world'
  have h := proj (world.comp world')
  rw [rename_rename, rename_rename_lift, rename_rename ρ ρ' t, rename_rename ρ ρ' t']
  exact h

theorem conv {B : Tm Head m} (formed : CtxFormed T.R Δ) (equal : TypeEq T.R Δ A B)
    (h : SigmaClause X Y Δ A t t') : SigmaClause X Y Δ B t t' := by
  obtain ⟨D, C, hA, ⟨w, r, pw⟩, ⟨w', r', pw'⟩, cv, proj⟩ := h
  obtain ⟨D', C', hB, eD, eC⟩ := RealizerSide.sigma_of_typeEq formed hA equal
  refine ⟨D', C', hB, ⟨w, r.conv equal, pw⟩, ⟨w', r'.conv equal, pw'⟩,
    T.laws.convTm_conv cv equal, ?_⟩
  intro k Θ ρ world
  obtain ⟨h₁, h₂⟩ := proj world
  have eC' := TypeEq.instantiate (eC.rename (world.1.snoc D)) (X.typed h₁).1
  exact ⟨X.conv world.2 (eD.rename world.1) h₁, Y.conv world.2 eC' h₂⟩

/-- Pairs at a realizer type are pairs at every type it is usable at: that type
reduces to a dependent pair type whose domain and codomain the first's are
usable at, and the candidates of the projections are cumulative. -/
theorem below {B : Tm Head m} (formed : CtxFormed T.R Δ) (le : Below T.R Δ A B)
    (h : SigmaClause X Y Δ A t t') : SigmaClause X Y Δ B t t' := by
  obtain ⟨D, C, hA, ⟨w, r, pw⟩, ⟨w', r', pw'⟩, cv, proj⟩ := h
  obtain ⟨D', C', hB, leD, leC⟩ := RealizerSide.sigma_of_below formed hA le
  refine ⟨D', C', hB, ⟨w, r.below le, pw⟩, ⟨w', r'.below le, pw'⟩,
    T.laws.convTm_below cv le, ?_⟩
  intro k Θ ρ world
  obtain ⟨h₁, h₂⟩ := proj world
  exact ⟨X.below world.2 (Derivable.renames leD world.1) h₁,
    Y.below world.2
      (below_instantiate (Derivable.renames leC (world.1.snoc D)) (X.typed h₁).1) h₂⟩

/-- At a type reducing to a dependent pair type, the terms reducing to neutral
terms that `E` compares are related pairs. -/
theorem of_neRel {D : Tm Head m} {C : Tm Head (m + 1)} (hA : RedTy T.R T.roles Δ A (.sigma D C))
    (h : NeRel T Δ A t t') : SigmaClause X Y Δ A t t' := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  refine ⟨D, C, hA, ⟨w, r, .inr nw⟩, ⟨w', r', .inr nw'⟩,
    NeRel.escape ⟨w, w', r, r', nw, nw', cv⟩, ?_⟩
  intro k Θ ρ world
  have cvw := T.laws.convNe_conv (T.laws.convNe_rename world.1 world.2 cv)
    (sigma_typeEq hA world.1)
  have f := sigma_fstRed hA world.1 r
  have f' := sigma_fstRed hA world.1 r'
  have firstNe := X.neutral (.fst (nw.rename ρ)) (.fst (nw'.rename ρ)) f.target f'.target
    (T.laws.convNe_fst cvw)
  have first := X.expand f f' firstNe
  have e₁ := sigma_codEq hA world.1 f'.target (X.equal (X.symm firstNe))
  have secondNe := Y.neutral (.snd (nw.rename ρ)) (.snd (nw'.rename ρ))
    (sigma_sndTyped hA world.1 r.target)
    (Typed.convType (sigma_sndTyped hA world.1 r'.target) e₁) (T.laws.convNe_snd cvw)
  have e₂ := sigma_codEq hA world.1 f.target f.equal.symm
  have e₃ := sigma_codEq hA world.1 f'.source (X.equal (X.symm first))
  exact ⟨first, Y.expand (sigma_sndRed hA world.1 r) ((sigma_sndRed hA world.1 r').conv e₃)
    (Y.conv world.2 e₂ secondNe)⟩

end SigmaClause

namespace ECand

/-- **Pairs**: at a realizer type reducing to a dependent pair type, the terms of
`SigmaClause`; at every type, the terms reducing to neutral terms that `E`
compares. -/
def sigmaOver (X Y : ECand T) : ECand T where
  rel := fun Δ A t t' => NeRel T Δ A t t' ∨ SigmaClause X Y Δ A t t'
  typed := fun h => h.elim NeRel.typed SigmaClause.typed
  escape := fun h => h.elim NeRel.escape SigmaClause.escape
  neutral := fun nt nt' ht ht' cv => .inl (NeRel.of_neutral nt nt' ht ht' cv)
  expand := fun red red' h => h.imp (NeRel.expand red red') (SigmaClause.expand red red')
  symm := fun h => h.imp NeRel.symm SigmaClause.symm
  trans := fun h h' => by
    rcases h with h | h <;> rcases h' with h' | h'
    · exact .inl (h.trans h')
    · rcases id h' with ⟨D, C, hA, -⟩
      exact .inr ((SigmaClause.of_neRel hA h).trans h')
    · rcases id h with ⟨D, C, hA, -⟩
      exact .inr (h.trans (SigmaClause.of_neRel hA h'))
    · exact .inr (h.trans h')
  rename := fun ren formed h =>
    h.imp (NeRel.rename ren formed) (SigmaClause.rename ⟨ren, formed⟩)
  typeConv := fun formed equal => funext fun _ => funext fun _ => propext
    ⟨fun h => h.imp (NeRel.conv equal) (SigmaClause.conv formed equal),
      fun h => h.imp (NeRel.conv equal.symm) (SigmaClause.conv formed equal.symm)⟩
  below := fun formed le h => h.imp (NeRel.below le) (SigmaClause.below formed le)

/-- At a realizer type reducing to `Σ D C`, the pairs are exactly: weak-head
normal pairs, related by `E`, whose projections satisfy `ProjClause`. -/
theorem sigmaOver_rel_sigma {X Y : ECand T} {m : Nat} {Δ : Ctx Head m} {A t t' D : Tm Head m}
    {C : Tm Head (m + 1)} (hA : RedTy T.R T.roles Δ A (.sigma D C)) :
    (sigmaOver X Y).rel Δ A t t' ↔ PairNf T Δ A t ∧ PairNf T Δ A t' ∧ T.E.convTm Δ t t' A ∧
      ProjClause X Y Δ D C t t' := by
  constructor
  · intro h
    obtain ⟨D', C', hA', p, p', cv, proj⟩ := h.elim (SigmaClause.of_neRel hA) id
    obtain ⟨rfl, rfl⟩ := sigma_unique hA hA'
    exact ⟨p, p', cv, proj⟩
  · rintro ⟨p, p', cv, proj⟩
    exact .inr ⟨D, C, hA, p, p', cv, proj⟩

end ECand

/-! ## Identity proofs -/

variable (T) in
/-- A term that reaches, typed at `A`, a reflexivity proof. -/
def ReflNf {m : Nat} (Δ : Ctx Head m) (A t : Tm Head m) : Prop :=
  ∃ x, RedTm T.R T.roles Δ t (.refl x) A

variable (T) in
/-- Identity proofs whose endpoints are related exactly when `P` holds: at a
realizer type reducing to an identity type, terms reaching reflexivity proofs
that `E` relates, when `P` holds. -/
def IdentClause (P : Prop) {m : Nat} (Δ : Ctx Head m) (A t t' : Tm Head m) : Prop :=
  (∃ D a b, RedTy T.R T.roles Δ A (.id D a b)) ∧ ReflNf T Δ A t ∧ ReflNf T Δ A t' ∧
    T.E.convTm Δ t t' A ∧ P

namespace IdentClause

variable {P : Prop} {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

theorem typed (h : IdentClause T P Δ A t t') : Typed T.R Δ t A ∧ Typed T.R Δ t' A := by
  obtain ⟨-, ⟨_, r⟩, ⟨_, r'⟩, -⟩ := h
  exact ⟨r.source, r'.source⟩

theorem escape (h : IdentClause T P Δ A t t') : T.E.convTm Δ t t' A := h.2.2.2.1

theorem expand {u u' : Tm Head m} (red : RedTm T.R T.roles Δ t u A)
    (red' : RedTm T.R T.roles Δ t' u' A) (h : IdentClause T P Δ A u u') :
    IdentClause T P Δ A t t' := by
  obtain ⟨hA, ⟨x, r⟩, ⟨x', r'⟩, cv, p⟩ := h
  exact ⟨hA, ⟨x, red.trans r⟩, ⟨x', red'.trans r'⟩, T.laws.convTm_expand red red' cv, p⟩

theorem symm (h : IdentClause T P Δ A t t') : IdentClause T P Δ A t' t := by
  obtain ⟨hA, x, x', cv, p⟩ := h
  exact ⟨hA, x', x, T.laws.convTm_symm cv, p⟩

theorem trans {t'' : Tm Head m} (h : IdentClause T P Δ A t t')
    (h' : IdentClause T P Δ A t' t'') : IdentClause T P Δ A t t'' := by
  obtain ⟨hA, x, -, cv, p⟩ := h
  obtain ⟨-, -, x'', cv', -⟩ := h'
  exact ⟨hA, x, x'', T.laws.convTm_trans cv cv', p⟩

theorem rename {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k} (world : World T.toSetting Δ Θ ρ)
    (h : IdentClause T P Δ A t t') :
    IdentClause T P Θ (Presentation.rename ρ A) (Presentation.rename ρ t)
      (Presentation.rename ρ t') := by
  obtain ⟨⟨D, a, b, hA⟩, ⟨x, r⟩, ⟨x', r'⟩, cv, p⟩ := h
  exact ⟨⟨_, _, _, hA.rename world.1⟩, ⟨_, r.rename world.1⟩, ⟨_, r'.rename world.1⟩,
    T.laws.convTm_rename world.1 world.2 cv, p⟩

theorem conv {B : Tm Head m} (formed : CtxFormed T.R Δ) (equal : TypeEq T.R Δ A B)
    (h : IdentClause T P Δ A t t') : IdentClause T P Δ B t t' := by
  obtain ⟨⟨D, a, b, hA⟩, ⟨x, r⟩, ⟨x', r'⟩, cv, p⟩ := h
  exact ⟨RealizerSide.id_of_typeEq formed hA equal, ⟨x, r.conv equal⟩, ⟨x', r'.conv equal⟩,
    T.laws.convTm_conv cv equal, p⟩

/-- Identity proofs at a realizer type are identity proofs at every type it is
usable at: a type reducing to an identity type is usable only at types equal to
it. -/
theorem below {B : Tm Head m} (formed : CtxFormed T.R Δ) (le : Below T.R Δ A B)
    (h : IdentClause T P Δ A t t') : IdentClause T P Δ B t t' := by
  obtain ⟨⟨D, a, b, hA⟩, -⟩ := id h
  exact h.conv formed (RealizerSide.typeEq_of_below formed hA
    (.inr (.inr (.inr (.inl ⟨D, a, b, rfl⟩)))) (fun _ => nofun) (fun _ _ => nofun)
    (fun _ _ => nofun) le)

/-- A reflexivity proof is not related to a term reducing to a neutral term. -/
theorem not_neRel_left {t'' : Tm Head m} (h : IdentClause T P Δ A t t')
    (h' : NeRel T Δ A t' t'') : False := by
  obtain ⟨-, -, ⟨x, r⟩, -⟩ := h
  exact (h'.left_whnf r (refl_whnf T.shape x)).ne_refl rfl

/-- A term reducing to a neutral term is not related to a reflexivity proof. -/
theorem not_neRel_right {t'' : Tm Head m} (h : NeRel T Δ A t t')
    (h' : IdentClause T P Δ A t' t'') : False := by
  obtain ⟨-, ⟨x, r⟩, -⟩ := h'
  exact (h.right_whnf r (refl_whnf T.shape x)).ne_refl rfl

end IdentClause

namespace ECand

variable (T) in
/-- **Identity proofs** whose endpoints are related exactly when `P` holds: at a
realizer type reducing to an identity type, the terms of `IdentClause`; at every
type, the terms reducing to neutral terms that `E` compares. -/
def ident (P : Prop) : ECand T where
  rel := fun Δ A t t' => NeRel T Δ A t t' ∨ IdentClause T P Δ A t t'
  typed := fun h => h.elim NeRel.typed IdentClause.typed
  escape := fun h => h.elim NeRel.escape IdentClause.escape
  neutral := fun nt nt' ht ht' cv => .inl (NeRel.of_neutral nt nt' ht ht' cv)
  expand := fun red red' h => h.imp (NeRel.expand red red') (IdentClause.expand red red')
  symm := fun h => h.imp NeRel.symm IdentClause.symm
  trans := fun h h' => by
    rcases h with h | h <;> rcases h' with h' | h'
    · exact .inl (h.trans h')
    · exact (IdentClause.not_neRel_right h h').elim
    · exact (IdentClause.not_neRel_left h h').elim
    · exact .inr (h.trans h')
  rename := fun ren formed h =>
    h.imp (NeRel.rename ren formed) (IdentClause.rename ⟨ren, formed⟩)
  typeConv := fun formed equal => funext fun _ => funext fun _ => propext
    ⟨fun h => h.imp (NeRel.conv equal) (IdentClause.conv formed equal),
      fun h => h.imp (NeRel.conv equal.symm) (IdentClause.conv formed equal.symm)⟩
  below := fun formed le h => h.imp (NeRel.below le) (IdentClause.below formed le)

/-- At a realizer type that reaches no identity type, the identity candidate is
`bot`. -/
theorem ident_rel_of_not_id {P : Prop} {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}
    (hA : ∀ D a b, ¬ RedTy T.R T.roles Δ A (.id D a b)) :
    (ident T P).rel Δ A t t' ↔ (bot T).rel Δ A t t' :=
  ⟨fun h => h.elim id fun ⟨⟨D, a, b, h⟩, _⟩ => absurd h (hA D a b), .inl⟩

end ECand

/-! ## Constructors of inductive types -/

/-- The realizer type of a field of a constructor of the inductive type `I`: `I`
itself for a recursive field, the closed field type otherwise. -/
def fieldType (I : DeclName) {m : Nat} : Field Head → Tm Head m
  | .recursive => .const I
  | .closed F => liftClosed F

theorem rename_fieldType (I : DeclName) {m k : Nat} (ρ : Ren m k) (f : Field Head) :
    Presentation.rename ρ (fieldType I f : Tm Head m) = fieldType I f := by
  cases f with
  | recursive => rfl
  | closed F => exact rename_liftClosed ρ F

/-- Arguments related field by field, each at its field's realizer type. -/
inductive FieldsRel (I : DeclName) {m : Nat} (Δ : Ctx Head m) :
    List (ECand T) → List (Field Head) → List (Tm Head m) → List (Tm Head m) → Prop where
  | nil : FieldsRel I Δ [] [] [] []
  | cons {X : ECand T} {Xs : List (ECand T)} {f : Field Head} {fs : List (Field Head)}
      {a a' : Tm Head m} {as as' : List (Tm Head m)} :
      X.rel Δ (fieldType I f) a a' → FieldsRel I Δ Xs fs as as' →
      FieldsRel I Δ (X :: Xs) (f :: fs) (a :: as) (a' :: as')

namespace FieldsRel

variable {I : DeclName} {m : Nat} {Δ : Ctx Head m} {Xs : List (ECand T)} {fs : List (Field Head)}
  {as as' : List (Tm Head m)}

theorem symm (h : FieldsRel I Δ Xs fs as as') : FieldsRel I Δ Xs fs as' as := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (ECand.symm _ hx) ih

theorem trans {as'' : List (Tm Head m)} (h : FieldsRel I Δ Xs fs as as')
    (h' : FieldsRel I Δ Xs fs as' as'') : FieldsRel I Δ Xs fs as as'' := by
  induction h generalizing as'' with
  | nil => cases h'; exact .nil
  | cons hx _ ih =>
      cases h' with
      | cons hx' rest => exact .cons (ECand.trans _ hx hx') (ih rest)

theorem rename {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k} (ren : CtxRen Δ Θ ρ)
    (formed : CtxFormed T.R Θ) (h : FieldsRel I Δ Xs fs as as') :
    FieldsRel I Θ Xs fs (as.map (Presentation.rename ρ)) (as'.map (Presentation.rename ρ)) := by
  induction h with
  | nil => exact .nil
  | @cons X Xs f fs a a' as as' hx _ ih =>
      have hx' := ECand.rename X ren formed hx
      rw [rename_fieldType] at hx'
      exact .cons hx' ih

end FieldsRel

/-- A constructor spine is weak-head normal. -/
theorem ctorSpine_whnf {k : DeclName} {a : Nat} (ctor : T.roles k = .constructor a) {m : Nat}
    (as : List (Tm Head m)) : Whnf T.R T.roles (appSpine (.const k) as) :=
  constSpine_whnf T.shape (by intro _ _ e; rw [ctor] at e; cases e) as

/-- A constructor spine is not neutral. -/
theorem ctorSpine_not_neutral {k : DeclName} {a : Nat} (ctor : T.roles k = .constructor a)
    {m : Nat} (as : List (Tm Head m)) : ¬ Neutral T.roles (appSpine (.const k) as) := by
  intro neutral
  rcases neutral.constSpine rfl with rigid | ⟨_, _, _, _, _, _, computes, _⟩
  · rw [ctor] at rigid; cases rigid
  · rw [ctor] at computes; cases computes

variable (T) in
/-- The values of the inductive type `I` built by the constructor `k`: at a
realizer type reducing to `I`, terms reaching `k`, as `I` declares it, applied to
arguments related field by field by `Xs`, that `E` relates. -/
def CtorClause (I k : DeclName) (Xs : List (ECand T)) {m : Nat} (Δ : Ctx Head m)
    (A t t' : Tm Head m) : Prop :=
  ∃ (cs : List (DeclName × List (Field Head))) (fs : List (Field Head))
    (as as' : List (Tm Head m)), T.roles I = .inductive cs ∧ (k, fs) ∈ cs ∧
    RedTy T.R T.roles Δ A (.const I) ∧ RedTm T.R T.roles Δ t (appSpine (.const k) as) A ∧
    RedTm T.R T.roles Δ t' (appSpine (.const k) as') A ∧ T.E.convTm Δ t t' A ∧
    FieldsRel I Δ Xs fs as as'

namespace CtorClause

variable {I k : DeclName} {Xs : List (ECand T)} {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

theorem typed (h : CtorClause T I k Xs Δ A t t') : Typed T.R Δ t A ∧ Typed T.R Δ t' A := by
  obtain ⟨_, _, _, _, _, _, _, r, r', _⟩ := h
  exact ⟨r.source, r'.source⟩

theorem escape (h : CtorClause T I k Xs Δ A t t') : T.E.convTm Δ t t' A := by
  obtain ⟨_, _, _, _, _, _, _, _, _, cv, _⟩ := h
  exact cv

theorem expand {u u' : Tm Head m} (red : RedTm T.R T.roles Δ t u A)
    (red' : RedTm T.R T.roles Δ t' u' A) (h : CtorClause T I k Xs Δ A u u') :
    CtorClause T I k Xs Δ A t t' := by
  obtain ⟨cs, fs, as, as', role, mem, hA, r, r', cv, fields⟩ := h
  exact ⟨cs, fs, as, as', role, mem, hA, red.trans r, red'.trans r',
    T.laws.convTm_expand red red' cv, fields⟩

theorem symm (h : CtorClause T I k Xs Δ A t t') : CtorClause T I k Xs Δ A t' t := by
  obtain ⟨cs, fs, as, as', role, mem, hA, r, r', cv, fields⟩ := h
  exact ⟨cs, fs, as', as, role, mem, hA, r', r, T.laws.convTm_symm cv, fields.symm⟩

theorem trans {t'' : Tm Head m} (h : CtorClause T I k Xs Δ A t t')
    (h' : CtorClause T I k Xs Δ A t' t'') : CtorClause T I k Xs Δ A t t'' := by
  obtain ⟨cs, fs, as, as', role, mem, hA, r, r', cv, fields⟩ := h
  obtain ⟨cs₂, fs₂, bs, bs', role₂, mem₂, -, q, q', cv', fields'⟩ := h'
  obtain rfl : cs = cs₂ := Role.inductive.inj (role.symm.trans role₂)
  obtain rfl : fs = fs₂ := T.constructors.fields_unique role mem mem₂
  have ctor := T.constructors.arity role mem
  obtain ⟨-, rfl⟩ := appSpine_const_injective
    (WhRed.whnf_unique T.shape r'.red q.red (ctorSpine_whnf ctor as') (ctorSpine_whnf ctor bs))
  exact ⟨cs, fs, as, bs', role, mem, hA, r, q', T.laws.convTm_trans cv cv', fields.trans fields'⟩

theorem rename {k' : Nat} {Θ : Ctx Head k'} {ρ : Ren m k'} (world : World T.toSetting Δ Θ ρ)
    (h : CtorClause T I k Xs Δ A t t') :
    CtorClause T I k Xs Θ (Presentation.rename ρ A) (Presentation.rename ρ t)
      (Presentation.rename ρ t') := by
  obtain ⟨cs, fs, as, as', role, mem, hA, r, r', cv, fields⟩ := h
  have q := r.rename world.1
  have q' := r'.rename world.1
  rw [rename_appSpine] at q q'
  exact ⟨cs, fs, _, _, role, mem, hA.rename world.1, q, q',
    T.laws.convTm_rename world.1 world.2 cv, fields.rename world.1 world.2⟩

theorem conv {B : Tm Head m} (formed : CtxFormed T.R Δ) (equal : TypeEq T.R Δ A B)
    (h : CtorClause T I k Xs Δ A t t') : CtorClause T I k Xs Δ B t t' := by
  obtain ⟨cs, fs, as, as', role, mem, hA, r, r', cv, fields⟩ := h
  exact ⟨cs, fs, as, as', role, mem, RealizerSide.inductive_of_typeEq role formed hA equal,
    r.conv equal, r'.conv equal, T.laws.convTm_conv cv equal, fields⟩

/-- Values of an inductive type at a realizer type are values at every type it
is usable at: a type reducing to the type constant of an inductive type is
usable only at types equal to it. -/
theorem below {B : Tm Head m} (formed : CtxFormed T.R Δ) (le : Below T.R Δ A B)
    (h : CtorClause T I k Xs Δ A t t') : CtorClause T I k Xs Δ B t t' := by
  obtain ⟨cs, -, -, -, role, -, hA, -⟩ := id h
  exact h.conv formed (RealizerSide.typeEq_of_below formed hA
    (.inr (.inr (.inr (.inr (.inr ⟨I, cs, role, rfl⟩))))) (fun _ => nofun) (fun _ _ => nofun)
    (fun _ _ => nofun) le)

/-- A constructor spine is not related to a term reducing to a neutral term. -/
theorem not_neRel_left {t'' : Tm Head m} (h : CtorClause T I k Xs Δ A t t')
    (h' : NeRel T Δ A t' t'') : False := by
  obtain ⟨cs, fs, _, as', role, mem, _, _, r', _⟩ := h
  have ctor := T.constructors.arity role mem
  exact ctorSpine_not_neutral ctor as' (h'.left_whnf r' (ctorSpine_whnf ctor as'))

/-- A term reducing to a neutral term is not related to a constructor spine. -/
theorem not_neRel_right {t'' : Tm Head m} (h : NeRel T Δ A t t')
    (h' : CtorClause T I k Xs Δ A t' t'') : False := by
  obtain ⟨cs, fs, as, _, role, mem, _, r, _⟩ := h'
  have ctor := T.constructors.arity role mem
  exact ctorSpine_not_neutral ctor as (h.right_whnf r (ctorSpine_whnf ctor as))

end CtorClause

namespace ECand

variable (T) in
/-- **A value of the inductive type `I` built by the constructor `k`** from fields
realized by `Xs`: at a realizer type reducing to `I`, the terms of `CtorClause`;
at every type, the terms reducing to neutral terms that `E` compares. -/
def ctorReal (I k : DeclName) (Xs : List (ECand T)) : ECand T where
  rel := fun Δ A t t' => NeRel T Δ A t t' ∨ CtorClause T I k Xs Δ A t t'
  typed := fun h => h.elim NeRel.typed CtorClause.typed
  escape := fun h => h.elim NeRel.escape CtorClause.escape
  neutral := fun nt nt' ht ht' cv => .inl (NeRel.of_neutral nt nt' ht ht' cv)
  expand := fun red red' h => h.imp (NeRel.expand red red') (CtorClause.expand red red')
  symm := fun h => h.imp NeRel.symm CtorClause.symm
  trans := fun h h' => by
    rcases h with h | h <;> rcases h' with h' | h'
    · exact .inl (h.trans h')
    · exact (CtorClause.not_neRel_right h h').elim
    · exact (CtorClause.not_neRel_left h h').elim
    · exact .inr (h.trans h')
  rename := fun ren formed h =>
    h.imp (NeRel.rename ren formed) (CtorClause.rename ⟨ren, formed⟩)
  typeConv := fun formed equal => funext fun _ => funext fun _ => propext
    ⟨fun h => h.imp (NeRel.conv equal) (CtorClause.conv formed equal),
      fun h => h.imp (NeRel.conv equal.symm) (CtorClause.conv formed equal.symm)⟩
  below := fun formed le h => h.imp (NeRel.below le) (CtorClause.below formed le)

end ECand

/-! ## Inclusions

Along a world morphism a value may have fewer valid arguments, and the
realizers of the renamed value then include those of the value. Such facts are
inclusions, not equalities, so they are no laws of the algebra. The
constructions are monotone in what they range over.
-/

/-- Arguments related field by field by candidates that are each included in
another list of candidates are related by that list. -/
theorem FieldsRel.mono {I : DeclName} {m : Nat} {Δ : Ctx Head m} {Xs Ys : List (ECand T)}
    (hXY : List.Forall₂ (fun X Y : ECand T => ∀ {k : Nat} {Θ : Ctx Head k} {B s s' : Tm Head k},
      X.rel Θ B s s' → Y.rel Θ B s s') Xs Ys)
    {fs : List (Field Head)} {as as' : List (Tm Head m)} (h : FieldsRel I Δ Xs fs as as') :
    FieldsRel I Δ Ys fs as as' := by
  induction h generalizing Ys with
  | nil =>
      cases hXY
      exact .nil
  | cons hx _ ih =>
      cases hXY with
      | cons hxy rest => exact .cons (hxy hx) (ih rest)

namespace ECand

variable {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

/-- A meet includes the meet of a family whose members all occur in its own
family. -/
theorem inter_mono {ι κ : Type} {F : ι → ECand T} {G : κ → ECand T}
    (cover : ∀ j, ∃ i, F i = G j) (h : (inter F).rel Δ A t t') : (inter G).rel Δ A t t' :=
  ⟨h.1, fun j => by
    obtain ⟨i, e⟩ := cover j
    rw [← e]
    exact h.2 i⟩

/-- Girard's clause over an index includes Girard's clause over an index whose
pairs of candidates all occur in its own. -/
theorem piOver_mono {ι κ : Type} {d c : ι → ECand T} {d' c' : κ → ECand T}
    (cover : ∀ j, ∃ i, d i = d' j ∧ c i = c' j) (h : (piOver d c).rel Δ A t t') :
    (piOver d' c').rel Δ A t t' :=
  h.imp id fun ⟨D, C, hA, f, f', cv, app⟩ => ⟨D, C, hA, f, f', cv, fun j => by
    obtain ⟨i, ed, ec⟩ := cover j
    rw [← ed, ← ec]
    exact app i⟩

/-- Pairs are monotone in the candidates of their projections. -/
theorem sigmaOver_mono {X X' Y Y' : ECand T}
    (hX : ∀ {k : Nat} {Θ : Ctx Head k} {B s s' : Tm Head k}, X.rel Θ B s s' → X'.rel Θ B s s')
    (hY : ∀ {k : Nat} {Θ : Ctx Head k} {B s s' : Tm Head k}, Y.rel Θ B s s' → Y'.rel Θ B s s')
    (h : (sigmaOver X Y).rel Δ A t t') : (sigmaOver X' Y').rel Δ A t t' :=
  h.imp id fun ⟨D, C, hA, p, p', cv, proj⟩ => ⟨D, C, hA, p, p', cv, by
    intro k Θ ρ world
    exact ⟨hX (proj world).1, hY (proj world).2⟩⟩

/-- The identity candidate is monotone in its proposition. -/
theorem ident_mono {P Q : Prop} (hPQ : P → Q) (h : (ident T P).rel Δ A t t') :
    (ident T Q).rel Δ A t t' :=
  h.imp id fun ⟨hA, x, x', cv, p⟩ => ⟨hA, x, x', cv, hPQ p⟩

/-- A constructor candidate is monotone in the candidates of its fields. -/
theorem ctorReal_mono {I k : DeclName} {Xs Ys : List (ECand T)}
    (hXY : List.Forall₂ (fun X Y : ECand T => ∀ {k : Nat} {Θ : Ctx Head k} {B s s' : Tm Head k},
      X.rel Θ B s s' → Y.rel Θ B s s') Xs Ys)
    (h : (ctorReal T I k Xs).rel Δ A t t') : (ctorReal T I k Ys).rel Δ A t t' :=
  h.imp id fun ⟨cs, fs, as, as', role, mem, hA, r, r', cv, fields⟩ =>
    ⟨cs, fs, as, as', role, mem, hA, r, r', cv, fields.mono hXY⟩

end ECand

/-! ## The realizer algebra -/

variable (T) in
/-- **The realizer algebra of equality candidates.** A type, as a value of a
universe, is realized by the terms reaching the weak-head form of a type; a
code by the terms reaching a constructor applied to its arguments or a neutral
term; a value stuck on the daimon by `bot`. -/
def ecandAlgebra : RealizerAlgebra Head where
  Cand := ECand T
  top := ECand.top T
  univ := ECand.types T
  codes := ECand.constructed T
  meet := ECand.inter
  piOver := ECand.piOver
  sigmaOver := ECand.sigmaOver
  ident := ECand.ident T
  ctorReal := ECand.ctorReal T
  stuckReal := fun _ => ECand.bot T

variable (T) in
/-- **The laws of the realizer algebra of equality candidates**: the meet of a
nonempty constant family is its value, and meets and Girard's clause depend
only on what they range over. -/
theorem ecandAlgebra_laws : (ecandAlgebra T).Laws where
  meet_const := fun f x all nonempty => by
    obtain ⟨i⟩ := nonempty
    refine ECand.ext fun Δ A t t' => ⟨fun h => ?_, fun h => ⟨x.le_top h, fun j => ?_⟩⟩
    · have hi := h.2 i
      rwa [all i] at hi
    · rw [all j]
      exact h
  meet_congr := fun f g fg gf => ECand.ext fun Δ A t t' =>
    ⟨fun h => ⟨h.1, fun j => by
        obtain ⟨i, e⟩ := gf j
        rw [← e]
        exact h.2 i⟩,
      fun h => ⟨h.1, fun i => by
        obtain ⟨j, e⟩ := fg i
        rw [e]
        exact h.2 j⟩⟩
  piOver_congr := fun _ _ _ _ fg gf => ECand.ext fun _ _ _ _ =>
    or_congr Iff.rfl (PiClause.congr fg gf)

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
