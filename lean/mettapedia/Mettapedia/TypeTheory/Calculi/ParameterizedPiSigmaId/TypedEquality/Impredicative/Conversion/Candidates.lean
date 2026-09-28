import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.TypeForms

/-!
# Equality candidates

The conversion model realizes its values by *equality candidates*: partial
equivalences on the typed terms of every context at every realizer type, over
the generic equality `E` of the realizer side. A candidate

* relates only terms typed at the realizer type (`typed`) that `E` relates
  there (`escape`);
* relates every two neutral terms that `E` compares as head spines (`neutral`);
* is closed under typed weak-head expansion of both sides (`expand`);
* is symmetric and transitive (`symm`, `trans`);
* survives every renaming into a formed context (`rename`);
* depends on the realizer type only up to typed equality, in a formed context
  (`typeConv`);
* is cumulative: what it relates at a realizer type it relates at every type
  that type is usable at, in a formed context (`below`).

The candidates form a type fixed before any type is interpreted. Their
relations are propositions, so quantifying over all candidates inside a
relation stays in `Prop`.

The realizer side is a normalization setting whose generic equality has its
laws and respects typed weak-head reduction of both sides, together with the
facts about weak-head forms of types (`FormFacts`): every type of a formed
context reduces to a weak-head form, and the weak-head forms of equal types
match. The constructions of candidates read the weak-head form of the realizer
type. With these facts, a construction gives the same relation at typed-equal
realizer types, and what it relates at a realizer type it relates at every type
that type is usable at. For a package whose declared constants are semantic in
the one-sided model, the facts are consequences of that model
(`FormFacts.ofSemantic`).

Subtyping of realizer types is inverted by these facts alone: a type reducing
to a dependent function or pair type is usable only at types reducing to one
with parts related as subtyping requires (`RealizerSide.pi_of_below`,
`RealizerSide.sigma_of_below`), and a type reaching a weak-head form that is no
head, dependent function or pair type is usable only at types equal to it
(`RealizerSide.typeEq_of_below`).

The least candidate `bot` relates the terms that reduce, typed, to neutral
terms that `E` compares as head spines (`bot_le`). A candidate contains every
variable of its realizer type (`ECand.var`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## The realizer side -/

/-- A generic equality respects typed weak-head reduction of both sides: it
relates the typed reducts of the terms it relates, the converse of its closure
under expansion. -/
def RespectsReduction (R : Rules Head) (roles : Roles Head) (E : GenericEquality Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {t t' u u' A : Tm Head n},
    RedTm R roles Γ t t' A → RedTm R roles Γ u u' A → E.convTm Γ t u A → E.convTm Γ t' u' A

/-- The realizer side of the conversion model: a normalization setting whose
generic equality has its laws and respects typed weak-head reduction, with the
facts about weak-head forms of types. -/
structure RealizerSide (Head L : Type) [LevelOrder L] extends Setting Head L where
  laws : E.Laws R roles
  /-- The generic equality of terms respects typed weak-head reduction of both
  sides: the converse of its closure under expansion. -/
  reduce : ∀ {n : Nat} {Γ : Ctx Head n} {t t' u u' A : Tm Head n},
    RedTm R roles Γ t t' A → RedTm R roles Γ u u' A → E.convTm Γ t u A → E.convTm Γ t' u' A
  facts : FormFacts R roles

/-- Typed equality respects typed weak-head reduction. -/
theorem declarative_convTm_reduce {R : Rules Head} {roles : Roles Head} {n : Nat}
    {Γ : Ctx Head n} {t t' u u' A : Tm Head n} (red : RedTm R roles Γ t t' A)
    (red' : RedTm R roles Γ u u' A) (h : (declarative R).convTm Γ t u A) :
    (declarative R).convTm Γ t' u' A :=
  .trans (.symm red.equal) (.trans h red'.equal)

namespace RealizerSide

variable {T : RealizerSide Head L}

/-- A type of a formed context equal to a type in weak-head form reaches a
weak-head form that matches it. -/
theorem matching_form {n : Nat} {Γ : Ctx Head n} {A A' B : Tm Head n} (formed : CtxFormed T.R Γ)
    (hA : RedTy T.R T.roles Γ A A') (form : IsTypeForm T.roles A') (equal : TypeEq T.R Γ A B)
    (typeB : IsType T.R Γ B) :
    ∃ B', RedTy T.R T.roles Γ B B' ∧ FormsMatch T.R T.roles Γ A' B' := by
  obtain ⟨B', hB, form'⟩ := T.facts.typeForm typeB formed
  refine ⟨B', hB, T.facts.forms ?_ formed form form'⟩
  exact TypeEq.trans T.levels hA.typeEq.symm (TypeEq.trans T.levels equal hB.typeEq)

/-- A type equal to a type reducing to a dependent function type reduces to a
dependent function type with equal parts. -/
theorem pi_of_typeEq {n : Nat} {Γ : Ctx Head n} {A B D : Tm Head n} {C : Tm Head (n + 1)}
    (formed : CtxFormed T.R Γ) (hA : RedTy T.R T.roles Γ A (.pi D C))
    (equal : TypeEq T.R Γ A B) :
    ∃ D' C', RedTy T.R T.roles Γ B (.pi D' C') ∧ TypeEq T.R Γ D D' ∧
      TypeEq T.R (.snoc Γ D) C C' := by
  obtain ⟨B', hB, forms⟩ :=
    matching_form formed hA (.inr (.inl ⟨D, C, rfl⟩)) equal (TypeEq.isType equal formed).2
  obtain ⟨D', C', rfl, eD, eC⟩ := forms.pi_left
  exact ⟨D', C', hB, eD, eC⟩

/-- A type equal to a type reducing to a dependent pair type reduces to a
dependent pair type with equal parts. -/
theorem sigma_of_typeEq {n : Nat} {Γ : Ctx Head n} {A B D : Tm Head n} {C : Tm Head (n + 1)}
    (formed : CtxFormed T.R Γ) (hA : RedTy T.R T.roles Γ A (.sigma D C))
    (equal : TypeEq T.R Γ A B) :
    ∃ D' C', RedTy T.R T.roles Γ B (.sigma D' C') ∧ TypeEq T.R Γ D D' ∧
      TypeEq T.R (.snoc Γ D) C C' := by
  obtain ⟨B', hB, forms⟩ := matching_form formed hA (.inr (.inr (.inl ⟨D, C, rfl⟩))) equal
    (TypeEq.isType equal formed).2
  obtain ⟨D', C', rfl, eD, eC⟩ := forms.sigma_left
  exact ⟨D', C', hB, eD, eC⟩

/-- A type equal to a type reducing to an identity type reduces to an identity
type. -/
theorem id_of_typeEq {n : Nat} {Γ : Ctx Head n} {A B D a b : Tm Head n}
    (formed : CtxFormed T.R Γ) (hA : RedTy T.R T.roles Γ A (.id D a b))
    (equal : TypeEq T.R Γ A B) :
    ∃ D' a' b', RedTy T.R T.roles Γ B (.id D' a' b') := by
  obtain ⟨B', hB, forms⟩ := matching_form formed hA (.inr (.inr (.inr (.inl ⟨D, a, b, rfl⟩))))
    equal (TypeEq.isType equal formed).2
  obtain ⟨D', a', b', rfl, -⟩ := forms.id_left
  exact ⟨D', a', b', hB⟩

/-- A type equal to a type reducing to the type constant of an inductive type
reduces to that type constant. -/
theorem inductive_of_typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {I : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : T.roles I = .inductive cs)
    (formed : CtxFormed T.R Γ) (hA : RedTy T.R T.roles Γ A (.const I))
    (equal : TypeEq T.R Γ A B) : RedTy T.R T.roles Γ B (.const I) := by
  obtain ⟨B', hB, forms⟩ :=
    matching_form formed hA (.inr (.inr (.inr (.inr (.inr ⟨I, cs, role, rfl⟩))))) equal
      (TypeEq.isType equal formed).2
  obtain rfl := forms.inductive_left role
  exact hB

/-! ### Inversion of subtyping -/

/-- A type reducing to a dependent function type is usable only at types
reducing to a dependent function type with an equal domain and a codomain that
its own codomain is usable at. -/
theorem pi_of_below {n : Nat} {Γ : Ctx Head n} {A B D : Tm Head n} {C : Tm Head (n + 1)}
    (formed : CtxFormed T.R Γ) (hA : RedTy T.R T.roles Γ A (.pi D C)) (le : Below T.R Γ A B) :
    ∃ D' C', RedTy T.R T.roles Γ B (.pi D' C') ∧ TypeEq T.R Γ D D' ∧
      Below T.R (.snoc Γ D) C C' := by
  obtain ⟨D₁, C₁, eB, eD, leC⟩ := Below.pi_source T.facts le formed hA.typeEq
  obtain ⟨D', C', hB, eD₁, eC₁⟩ :=
    pi_of_typeEq formed (RedTy.refl (TypeEq.isType eB formed).2) eB.symm
  exact ⟨D', C', hB, TypeEq.trans T.levels eD eD₁,
    .subTrans leC (Below.ctxConv eC₁.below eD.symm)⟩

/-- A type reducing to a dependent pair type is usable only at types reducing
to a dependent pair type with a domain and a codomain that its own are usable
at. -/
theorem sigma_of_below {n : Nat} {Γ : Ctx Head n} {A B D : Tm Head n} {C : Tm Head (n + 1)}
    (formed : CtxFormed T.R Γ) (hA : RedTy T.R T.roles Γ A (.sigma D C))
    (le : Below T.R Γ A B) :
    ∃ D' C', RedTy T.R T.roles Γ B (.sigma D' C') ∧ Below T.R Γ D D' ∧
      Below T.R (.snoc Γ D) C C' := by
  obtain ⟨D₁, C₁, eB, leD, leC⟩ := Below.sigma_source T.facts le formed hA.typeEq
  obtain ⟨D', C', hB, eD₁, eC₁⟩ :=
    sigma_of_typeEq formed (RedTy.refl (TypeEq.isType eB formed).2) eB.symm
  exact ⟨D', C', hB, .subTrans leD eD₁.below, .subTrans leC (Below.ctxBelow eC₁.below leD)⟩

/-- **A type reaching a weak-head form that is no head, dependent function or
pair type is usable only at types equal to it.** -/
theorem typeEq_of_below {n : Nat} {Γ : Ctx Head n} {A B w : Tm Head n}
    (formed : CtxFormed T.R Γ) (hA : RedTy T.R T.roles Γ A w) (form : IsTypeForm T.roles w)
    (notHead : ∀ h, w ≠ .head h) (notPi : ∀ D C, w ≠ .pi D C)
    (notSigma : ∀ D C, w ≠ .sigma D C) (le : Below T.R Γ A B) : TypeEq T.R Γ A B := by
  refine Normalization.Below.rigid (S := T.toSetting) le formed (fun u _ e => ?_)
    (fun D C e => ?_) (fun D C e => ?_)
  · obtain ⟨h', e', -⟩ := (T.facts.forms (TypeEq.trans T.levels e.symm hA.typeEq) formed
      (.inl ⟨u, rfl⟩) form).head_left
    exact notHead h' e'
  · obtain ⟨D', C', e', -⟩ := (T.facts.forms (TypeEq.trans T.levels e.symm hA.typeEq) formed
      (.inr (.inl ⟨D, C, rfl⟩)) form).pi_left
    exact notPi D' C' e'
  · obtain ⟨D', C', e', -⟩ := (T.facts.forms (TypeEq.trans T.levels e.symm hA.typeEq) formed
      (.inr (.inr (.inl ⟨D, C, rfl⟩))) form).sigma_left
    exact notSigma D' C' e'

end RealizerSide

/-! ## Terms that reduce to neutral terms -/

variable {T : RealizerSide Head L}

/-- Terms that reduce, typed at `A`, to neutral terms that `E` compares as head
spines. -/
def NeRel (T : RealizerSide Head L) {m : Nat} (Δ : Ctx Head m) (A t t' : Tm Head m) : Prop :=
  ∃ w w', RedTm T.R T.roles Δ t w A ∧ RedTm T.R T.roles Δ t' w' A ∧ Neutral T.roles w ∧
    Neutral T.roles w' ∧ T.E.convNe Δ w w' A

namespace NeRel

variable {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

theorem typed (h : NeRel T Δ A t t') : Typed T.R Δ t A ∧ Typed T.R Δ t' A := by
  obtain ⟨_, _, r, r', -⟩ := h
  exact ⟨r.source, r'.source⟩

theorem escape (h : NeRel T Δ A t t') : T.E.convTm Δ t t' A := by
  obtain ⟨_, _, r, r', nw, nw', cv⟩ := h
  exact T.laws.convTm_expand r r' (T.laws.convTm_of_convNe (.inl nw) (.inl nw') cv)

theorem of_neutral (nt : Neutral T.roles t) (nt' : Neutral T.roles t') (ht : Typed T.R Δ t A)
    (ht' : Typed T.R Δ t' A) (cv : T.E.convNe Δ t t' A) : NeRel T Δ A t t' :=
  ⟨t, t', .refl ht, .refl ht', nt, nt', cv⟩

theorem expand {u u' : Tm Head m} (red : RedTm T.R T.roles Δ t u A)
    (red' : RedTm T.R T.roles Δ t' u' A) (h : NeRel T Δ A u u') : NeRel T Δ A t t' := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  exact ⟨w, w', red.trans r, red'.trans r', nw, nw', cv⟩

theorem symm (h : NeRel T Δ A t t') : NeRel T Δ A t' t := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  exact ⟨w', w, r', r, nw', nw, T.laws.convNe_symm cv⟩

theorem trans {t'' : Tm Head m} (h : NeRel T Δ A t t') (h' : NeRel T Δ A t' t'') :
    NeRel T Δ A t t'' := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  obtain ⟨v, v', q, q', nv, nv', cv'⟩ := h'
  obtain rfl := WhRed.whnf_unique T.shape r'.red q.red (nw'.whnf T.shape) (nv.whnf T.shape)
  exact ⟨w, v', r, q', nw, nv', T.laws.convNe_trans cv cv'⟩

theorem rename {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k} (ren : CtxRen Δ Θ ρ)
    (formed : CtxFormed T.R Θ) (h : NeRel T Δ A t t') :
    NeRel T Θ (Presentation.rename ρ A) (Presentation.rename ρ t) (Presentation.rename ρ t') := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  exact ⟨_, _, r.rename ren, r'.rename ren, nw.rename ρ, nw'.rename ρ,
    T.laws.convNe_rename ren formed cv⟩

theorem conv {B : Tm Head m} (equal : TypeEq T.R Δ A B) (h : NeRel T Δ A t t') :
    NeRel T Δ B t t' := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  exact ⟨w, w', r.conv equal, r'.conv equal, nw, nw', T.laws.convNe_conv cv equal⟩

theorem below {B : Tm Head m} (le : Below T.R Δ A B) (h : NeRel T Δ A t t') :
    NeRel T Δ B t t' := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  exact ⟨w, w', r.below le, r'.below le, nw, nw', T.laws.convNe_below cv le⟩

/-- Every weak-head normal form that the left term reaches is neutral. -/
theorem left_whnf (h : NeRel T Δ A t t') {v B : Tm Head m} (red : RedTm T.R T.roles Δ t v B)
    (normal : Whnf T.R T.roles v) : Neutral T.roles v := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  obtain rfl := WhRed.whnf_unique T.shape r.red red.red (nw.whnf T.shape) normal
  exact nw

/-- Every weak-head normal form that the right term reaches is neutral. -/
theorem right_whnf (h : NeRel T Δ A t t') {v B : Tm Head m} (red : RedTm T.R T.roles Δ t' v B)
    (normal : Whnf T.R T.roles v) : Neutral T.roles v :=
  h.symm.left_whnf red normal

end NeRel

/-! ## Equality candidates -/

/-- **Equality candidates** over the realizer side `T`: a relation between terms
at a realizer type in a context, which relates only typed terms that `E`
relates, relates the neutral terms `E` compares, and is closed under typed
weak-head expansion, symmetric, transitive, stable under renaming into formed
contexts, invariant under typed equality of the realizer type, and cumulative:
what it relates at a realizer type of a formed context it relates at every type
that type is usable at. -/
structure ECand (T : RealizerSide Head L) where
  /-- `rel Δ A t t'`: `t` and `t'` are related at the realizer type `A` in `Δ`. -/
  rel : ∀ {m : Nat}, Ctx Head m → Tm Head m → Tm Head m → Tm Head m → Prop
  typed : ∀ {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}, rel Δ A t t' →
    Typed T.R Δ t A ∧ Typed T.R Δ t' A
  escape : ∀ {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}, rel Δ A t t' →
    T.E.convTm Δ t t' A
  neutral : ∀ {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}, Neutral T.roles t →
    Neutral T.roles t' → Typed T.R Δ t A → Typed T.R Δ t' A → T.E.convNe Δ t t' A →
    rel Δ A t t'
  expand : ∀ {m : Nat} {Δ : Ctx Head m} {A t t' u u' : Tm Head m},
    RedTm T.R T.roles Δ t u A → RedTm T.R T.roles Δ t' u' A → rel Δ A u u' → rel Δ A t t'
  symm : ∀ {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}, rel Δ A t t' → rel Δ A t' t
  trans : ∀ {m : Nat} {Δ : Ctx Head m} {A t t' t'' : Tm Head m}, rel Δ A t t' →
    rel Δ A t' t'' → rel Δ A t t''
  rename : ∀ {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k} {ρ : Ren m k} {A t t' : Tm Head m},
    CtxRen Δ Θ ρ → CtxFormed T.R Θ → rel Δ A t t' →
    rel Θ (Presentation.rename ρ A) (Presentation.rename ρ t) (Presentation.rename ρ t')
  typeConv : ∀ {m : Nat} {Δ : Ctx Head m} {A B : Tm Head m}, CtxFormed T.R Δ →
    TypeEq T.R Δ A B → rel Δ A = rel Δ B
  below : ∀ {m : Nat} {Δ : Ctx Head m} {A B t t' : Tm Head m}, CtxFormed T.R Δ →
    Below T.R Δ A B → rel Δ A t t' → rel Δ B t t'

namespace ECand

/-- Candidates with the same relation are equal. -/
theorem ext {X Y : ECand T}
    (h : ∀ {m : Nat} (Δ : Ctx Head m) (A t t' : Tm Head m), X.rel Δ A t t' ↔ Y.rel Δ A t t') :
    X = Y := by
  obtain ⟨rX, _, _, _, _, _, _, _, _, _⟩ := X
  obtain ⟨rY, _, _, _, _, _, _, _, _, _⟩ := Y
  have same : @rX = @rY := by
    funext m Δ A t t'
    exact propext (h Δ A t t')
  subst same
  rfl

variable (X : ECand T) {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}

/-- A related term is related to itself. -/
theorem refl_left (h : X.rel Δ A t t') : X.rel Δ A t t :=
  X.trans h (X.symm h)

/-- A related term is related to itself. -/
theorem refl_right (h : X.rel Δ A t t') : X.rel Δ A t' t' :=
  X.trans (X.symm h) h

/-- Related terms are equal at the realizer type. -/
theorem equal (h : X.rel Δ A t t') : Equal T.R Δ t t' A :=
  T.laws.convTm_sound (X.escape h)

/-- Conversion of the realizer type along a typed equality. -/
theorem conv {B : Tm Head m} (formed : CtxFormed T.R Δ) (equal : TypeEq T.R Δ A B)
    (h : X.rel Δ A t t') : X.rel Δ B t t' :=
  (congrFun (congrFun (X.typeConv formed equal) t) t').mp h

/-- A candidate reads its realizer type through the type's typed weak-head
reducts. -/
theorem redTy {B : Tm Head m} (formed : CtxFormed T.R Δ) (red : RedTy T.R T.roles Δ A B) :
    X.rel Δ A = X.rel Δ B :=
  X.typeConv formed red.typeEq

/-- Expansion of the left side. -/
theorem expand_left {u : Tm Head m} (red : RedTm T.R T.roles Δ t u A) (h : X.rel Δ A u t') :
    X.rel Δ A t t' :=
  X.expand red (.refl (X.typed h).2) h

/-- Expansion of the right side. -/
theorem expand_right {u' : Tm Head m} (red' : RedTm T.R T.roles Δ t' u' A)
    (h : X.rel Δ A t u') : X.rel Δ A t t' :=
  X.expand (.refl (X.typed h).1) red' h

/-- A candidate contains every variable of its realizer type. -/
theorem var (i : Fin m) (typing : Typed T.R Δ (.var i) A) : X.rel Δ A (.var i) (.var i) :=
  X.neutral (.var i) (.var i) typing typing (T.laws.convNe_var i typing)

/-- Weakening past one entry of a formed context. -/
theorem weaken {B : Tm Head m} (formed : CtxFormed T.R (.snoc Δ B)) (h : X.rel Δ A t t') :
    X.rel (.snoc Δ B) (Presentation.rename wk A) (Presentation.rename wk t)
      (Presentation.rename wk t') :=
  X.rename (CtxRen.wk Δ B) formed h

end ECand

/-! ## The least candidate -/

namespace ECand

variable (T) in
/-- The least candidate: terms that reduce, typed, to neutral terms that `E`
compares as head spines. -/
def bot : ECand T where
  rel := fun Δ A t t' => NeRel T Δ A t t'
  typed := NeRel.typed
  escape := NeRel.escape
  neutral := NeRel.of_neutral
  expand := NeRel.expand
  symm := NeRel.symm
  trans := NeRel.trans
  rename := NeRel.rename
  typeConv := fun _ equal =>
    funext fun _ => funext fun _ => propext ⟨NeRel.conv equal, NeRel.conv equal.symm⟩
  below := fun _ le => NeRel.below le

/-- **`bot` is the least candidate.** -/
theorem bot_le (X : ECand T) {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m}
    (h : (bot T).rel Δ A t t') : X.rel Δ A t t' := by
  obtain ⟨w, w', r, r', nw, nw', cv⟩ := h
  exact X.expand r r' (X.neutral nw nw' r.target r'.target cv)

end ECand

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
