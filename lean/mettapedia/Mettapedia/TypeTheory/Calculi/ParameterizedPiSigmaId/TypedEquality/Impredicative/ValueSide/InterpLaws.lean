import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Interp

/-!
# Laws of the interpretation: reduction, expansion and determinism

The reading of codes over a realizer algebra has the laws of a reading when
the algebra has its laws (`algebraReading_laws`), so a code has at most one
meaning.

A daimonic type is neutral, hence weak-head normal. It is not a head or a type
former, and it is neither an inductive type, nor the codes or a decoding,
whose constants are rigid and differ from the daimon. It is no constructor
spine either: by the laws of the value model, the constructors that inductive
types list are declared as constructors (`ConstructorsDeclared`), so a listed
constructor applied to arguments is weak-head normal, and a term reduces to at
most one such spine.

A type has the interpretation of its weak-head expansions and of its weak-head
reducts: every clause reads a weak-head normal form, which every reduct of the
type still reaches. A type has at most one interpretation at a level: every
clause reads a normal form of its own shape; the pack of a dependent function
or pair type is determined by the packs of its domain and codomain, and the
pack of a simple inductive type by the packs of its closed field types, which
it reads at those types only (`indPack_congr`).

Inversion reads the clause of a type from the normal form it reduces to.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph Truth)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L]

/-! ## The reading of codes -/

/-- **The laws of the reading over a realizer algebra**: those of the data
setting of the shapes of numbers; daimonic codes are neutral and are no
implication, quantifier, equation or generic spine; and the meet of a nonempty
constant family is its value, by the laws of the algebra. -/
theorem algebraReading_laws {S : Consistency.Setting Head} {star num : DeclName}
    {A : RealizerAlgebra Head} (laws : S.Laws) (rigid : S.roles star = .rigid)
    (alg : A.Laws) : (algebraReading S star num A).Laws where
  toDataLaws := laws.shapes rigid
  neutral_whnf := fun daimonic => (daimonic.neutral rigid).whnf laws.shape
  neutral_ne_imp := fun {_ _ p q} daimonic e => by
    have role : S.roles S.imp = .constructor 2 := laws.imp
    rcases Daimonic.constSpine (c := S.imp) (args := [p, q]) daimonic e with
      same | ⟨_, _, computes⟩
    · rw [same, rigid] at role
      cases role
    · rw [role] at computes
      cases computes
  neutral_ne_all := fun {_ _ f a _} daimonic carrier e => by
    have role : S.roles a = .constructor 1 := laws.all carrier
    rcases Daimonic.constSpine (c := a) (args := [f]) daimonic e with same | ⟨_, _, computes⟩
    · rw [same, rigid] at role
      cases role
    · rw [role] at computes
      cases computes
  neutral_ne_eq := fun {_ _ x y e' _} daimonic carrier e => by
    have role : S.roles e' = .constructor 2 := laws.eq carrier
    rcases Daimonic.constSpine (c := e') (args := [x, y]) daimonic e with
      same | ⟨_, _, computes⟩
    · rw [same, rigid] at role
      cases role
    · rw [role] at computes
      cases computes
  neutral_ne_var := fun daimonic => daimonic.ne_varSpine
  meet_const := alg.meet_const

/-! ## Weak-head normal forms -/

/-- A weak-head normal form reduces only to itself. -/
theorem whRed_of_whnf {R : Rules Head} {roles : Roles Head} {n : Nat} {w w' : Tm Head n}
    (normal : Whnf R roles w) (red : WhRed R roles w w') : w' = w := by
  cases red using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ => exact absurd step (normal _)

/-! ## Daimonic terms and constructor spines -/

namespace Model.Laws

variable {V : Model Head L}

/-- The laws of the model's reading of codes. -/
theorem reading (laws : V.Laws) : V.reading.Laws :=
  algebraReading_laws laws.values.truth laws.star laws.alg

/-- A daimonic term is no spine of a constant that is not the daimon and does
not compute. -/
theorem daimonic_ne_constSpine {n : Nat} {t : Tm Head n}
    (daimonic : Daimonic V.roles V.star t) {c : DeclName} (notStar : c ≠ V.star)
    (notComputing : ∀ arity inspect, V.roles c ≠ .computes arity inspect)
    {args : List (Tm Head n)} : t ≠ appSpine (.const c) args := fun e => by
  rcases daimonic.constSpine e with same | ⟨arity, inspect, computes⟩
  · exact notStar same
  · exact notComputing arity inspect computes

variable (laws : V.Laws)
include laws

/-- A daimonic term is neutral, the daimon being rigid. -/
theorem daimonic_neutral {n : Nat} {t : Tm Head n} (daimonic : Daimonic V.roles V.star t) :
    Neutral V.roles t :=
  daimonic.neutral laws.star

/-- A daimonic term is not a head, a dependent function or pair type, or an
identity type. -/
theorem daimonic_not_former {n : Nat} {t : Tm Head n} (daimonic : Daimonic V.roles V.star t) :
    (∀ h, t ≠ .head h) ∧ (∀ A B, t ≠ .pi A B) ∧ (∀ A B, t ≠ .sigma A B) ∧
      (∀ A a b, t ≠ .id A a b) :=
  (laws.daimonic_neutral daimonic).not_former

/-- A daimonic term is no spine of an inductive type. -/
theorem daimonic_ne_inductive {n : Nat} {t : Tm Head n} (daimonic : Daimonic V.roles V.star t)
    {T : DeclName} {cs : List (DeclName × List (Field Head))} (role : V.roles T = .inductive cs)
    {args : List (Tm Head n)} : t ≠ appSpine (.const T) args :=
  daimonic_ne_constSpine daimonic
    (fun e => by
      rw [e, laws.star] at role
      cases role)
    (fun _ _ h => by
      rw [role] at h
      cases h)

/-- A daimonic term is not the type of codes. -/
theorem daimonic_ne_prop {n : Nat} {t : Tm Head n} (daimonic : Daimonic V.roles V.star t) :
    t ≠ .const V.prop :=
  daimonic_ne_constSpine (args := []) daimonic laws.starNotProp.symm
    (fun _ _ h => by
      rw [laws.values.prop] at h
      cases h)

/-- A daimonic term is not a decoding. -/
theorem daimonic_ne_holds {n : Nat} {t : Tm Head n} (daimonic : Daimonic V.roles V.star t)
    {c : Tm Head n} : t ≠ .app (.const V.holds) c :=
  daimonic_ne_constSpine (args := [c]) daimonic laws.starNotHolds.symm
    (fun _ _ h => by
      rw [laws.values.holds] at h
      cases h)

/-- A daimonic term is not a type constant. -/
theorem daimonic_ne_typeConst {n : Nat} {t : Tm Head n} (daimonic : Daimonic V.roles V.star t)
    {c : DeclName} (hc : TypeConst V c) : t ≠ .const c := by
  rcases hc with rfl | ⟨cs, role⟩
  · exact laws.daimonic_ne_prop daimonic
  · exact laws.daimonic_ne_inductive (args := []) daimonic role

/-! ### Constructor spines -/

/-- A constructor an inductive type lists, applied to arguments, is weak-head
normal. -/
theorem ctorSpine_whnf {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) {k : DeclName} {fs : List (Field Head)}
    (mem : (k, fs) ∈ cs) {n : Nat} (args : List (Tm Head n)) :
    Whnf V.rules V.roles (appSpine (.const k) args) :=
  constSpine_whnf laws.shape
    (fun _ _ h => by
      rw [laws.declared.arity role mem] at h
      cases h) args

/-- A daimonic term is no spine of a constructor an inductive type lists. -/
theorem daimonic_ne_ctorSpine {n : Nat} {t : Tm Head n}
    (daimonic : Daimonic V.roles V.star t) {T : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : V.roles T = .inductive cs)
    {k : DeclName} {fs : List (Field Head)} (mem : (k, fs) ∈ cs)
    {args : List (Tm Head n)} : t ≠ appSpine (.const k) args := by
  have ctor := laws.declared.arity role mem
  exact daimonic_ne_constSpine daimonic
    (fun e => by
      rw [e, laws.star] at ctor
      cases ctor)
    (fun _ _ h => by
      rw [ctor] at h
      cases h)

/-- A term reduces to at most one spine of a listed constructor, whose fields
are then the listed ones. -/
theorem ctorSpine_unique {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) {k k' : DeclName} {fs fs' : List (Field Head)}
    (mem : (k, fs) ∈ cs) (mem' : (k', fs') ∈ cs) {n : Nat} {t : Tm Head n}
    {args args' : List (Tm Head n)} (red : WhRed V.rules V.roles t (appSpine (.const k) args))
    (red' : WhRed V.rules V.roles t (appSpine (.const k') args')) :
    k = k' ∧ fs = fs' ∧ args = args' := by
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective
    (laws.unique red red' (laws.ctorSpine_whnf role mem args)
      (laws.ctorSpine_whnf role mem' args'))
  exact ⟨rfl, laws.declared.fields_unique role mem mem', rfl⟩

/-- A term that reduces to a spine of a listed constructor reduces to no
daimonic term. -/
theorem ctorSpine_not_daimonic {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) {k : DeclName} {fs : List (Field Head)}
    (mem : (k, fs) ∈ cs) {n : Nat} {t u : Tm Head n} {args : List (Tm Head n)}
    (red : WhRed V.rules V.roles t (appSpine (.const k) args))
    (red' : WhRed V.rules V.roles t u) (daimonic : Daimonic V.roles V.star u) : False :=
  laws.daimonic_ne_ctorSpine daimonic role mem
    (laws.unique red' red (laws.daimonic_whnf daimonic)
      (laws.ctorSpine_whnf role mem args))

end Model.Laws

/-! ## Expansion and reduction -/

variable {V : Model Head L} {l : L} {below : L → IPack V}

/-- A type has the interpretation of its weak-head reducts. -/
theorem SInterp.expand {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n} {P : Pack V n}
    (red : WhRed V.rules V.roles A A') (interp : SInterp V l below ξ A' P) :
    SInterp V l below ξ A P := by
  cases interp with
  | sort isUniverse level r => exact .sort isUniverse level (red.trans r)
  | ground notUniverse r => exact .ground notUniverse (red.trans r)
  | pi r P domInterp codInterp codRespect =>
      exact .pi (red.trans r) P domInterp codInterp codRespect
  | sigma r P domInterp codInterp codRespect =>
      exact .sigma (red.trans r) P domInterp codInterp codRespect
  | ident r R tyInterp lhsVal rhsVal => exact .ident (red.trans r) R tyInterp lhsVal rhsVal
  | ind r role field fieldInterp => exact .ind (red.trans r) role field fieldInterp
  | prop r => exact .prop (red.trans r)
  | holds r truth => exact .holds (red.trans r) truth
  | rigid r role notProp notHolds => exact .rigid (red.trans r) role notProp notHolds
  | daimon r daimonic => exact .daimon (red.trans r) daimonic

/-- A type has the interpretation of its weak-head reducts too: every clause
reads a weak-head normal form, which every reduct reaches. -/
theorem SInterp.reduce (laws : V.Laws) {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n}
    {P : Pack V n} (interp : SInterp V l below ξ A P) (red : WhRed V.rules V.roles A A') :
    SInterp V l below ξ A' P := by
  cases interp with
  | sort isUniverse level r =>
      exact .sort isUniverse level (WhRed.to_whnf laws.shape r (head_whnf laws.shape _) red)
  | ground notUniverse r =>
      exact .ground notUniverse (WhRed.to_whnf laws.shape r (head_whnf laws.shape _) red)
  | pi r P domInterp codInterp codRespect =>
      exact .pi (WhRed.to_whnf laws.shape r (pi_whnf laws.shape _ _) red) P domInterp codInterp
        codRespect
  | sigma r P domInterp codInterp codRespect =>
      exact .sigma (WhRed.to_whnf laws.shape r (sigma_whnf laws.shape _ _) red) P domInterp
        codInterp codRespect
  | ident r R tyInterp lhsVal rhsVal =>
      exact .ident (WhRed.to_whnf laws.shape r (id_whnf laws.shape _ _ _) red) R tyInterp
        lhsVal rhsVal
  | ind r role field fieldInterp =>
      exact .ind (WhRed.to_whnf laws.shape r (inductive_whnf laws.shape role) red) role field
        fieldInterp
  | prop r => exact .prop (WhRed.to_whnf laws.shape r laws.values.whnf_prop red)
  | holds r truth => exact .holds (WhRed.to_whnf laws.shape r (laws.values.whnf_holds _) red) truth
  | rigid r role notProp notHolds =>
      exact .rigid (WhRed.to_whnf laws.shape r (laws.values.whnf_rigidSpine role _) red) role
        notProp notHolds
  | daimon r daimonic =>
      exact .daimon (WhRed.to_whnf laws.shape r (laws.daimonic_whnf daimonic) red) daimonic

/-- **An interpreted type reduces to a type form**, at every level and over
every table of the levels below. -/
theorem SInterp.typeForm {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ X P) : ∃ w, WhRed V.rules V.roles X w ∧ TypeForm V w := by
  cases interp with
  | sort hu _ red => exact ⟨_, red, .inl ⟨_, rfl, hu⟩⟩
  | ground hu red => exact ⟨_, red, .inr (.inr (.inr (.inr (.inl (.inl ⟨_, rfl, hu⟩)))))⟩
  | pi red => exact ⟨_, red, .inr (.inr (.inl ⟨_, _, rfl⟩))⟩
  | sigma red => exact ⟨_, red, .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))⟩
  | ident red =>
      exact ⟨_, red, .inr (.inr (.inr (.inr (.inl (.inr (.inl ⟨_, _, _, rfl⟩))))))⟩
  | ind red role => exact ⟨_, red, .inr (.inl ⟨_, .inr ⟨_, role⟩, rfl⟩)⟩
  | prop red => exact ⟨_, red, .inr (.inl ⟨_, .inl rfl, rfl⟩)⟩
  | holds red =>
      exact ⟨_, red, .inr (.inr (.inr (.inr (.inl (.inr (.inr (.inl ⟨_, rfl⟩)))))))⟩
  | rigid red role notProp notHolds =>
      exact ⟨_, red, .inr (.inr (.inr (.inr (.inl (.inr (.inr (.inr
        ⟨_, _, rfl, role, notProp, notHolds⟩)))))))⟩
  | daimon red daimonic => exact ⟨_, red, .inr (.inr (.inr (.inr (.inr daimonic))))⟩

/-! ## Packs of dependent function and pair types -/

namespace PiPack

variable {n : Nat} {ξ : World V.reading n} {P P' : PiPack V ξ}

/-- A family of packs is determined by its packs of domains and of codomains. -/
theorem ext
    (dom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
      P.dom w = P'.dom w)
    (cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : (P.dom w).Val a) (ha' : (P'.dom w).Val a),
        P.cod w ha = P'.cod w ha') :
    P = P' := by
  cases P with
  | mk dom₁ cod₁ =>
      cases P' with
      | mk dom₂ cod₂ =>
          obtain rfl : @dom₁ = @dom₂ := by
            funext m ξ' ρ w
            exact dom w
          obtain rfl : @cod₁ = @cod₂ := by
            funext m ξ' ρ w a ha
            exact cod w ha ha
          rfl

/-- The pack of a dependent function type is determined by the packs of its
domain and codomain. -/
theorem piPack_ext
    (dom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
      P.dom w = P'.dom w)
    (cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : (P.dom w).Val a) (ha' : (P'.dom w).Val a),
        P.cod w ha = P'.cod w ha') :
    P.piPack = P'.piPack := by
  rw [ext dom cod]

/-- The pack of a dependent pair type is determined by the packs of its domain
and codomain. -/
theorem sigmaPack_ext
    (dom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
      P.dom w = P'.dom w)
    (cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : (P.dom w).Val a) (ha' : (P'.dom w).Val a),
        P.cod w ha = P'.cod w ha') :
    P.sigmaPack = P'.sigmaPack := by
  rw [ext dom cod]

/-- A family that interprets a domain and a codomain for `I` interprets them
for every interpretation containing `I`. -/
theorem Interprets.mono {Q : PiPack V ξ} {I I' : IPack V} {A : Tm Head n}
    {B : Tm Head (n + 1)} (interprets : Q.Interprets I A B)
    (incl : ∀ {k : Nat} {ζ : World V.reading k} {X : Tm Head k} {R : Pack V k},
      I ζ X R → I' ζ X R) : Q.Interprets I' A B :=
  ⟨fun w => incl (interprets.dom w), fun {_ _ _} w {_} ha => incl (interprets.cod w ha),
    interprets.codRespect⟩

end PiPack

/-! ## Packs of simple inductive types -/

/-- The closed field types of a listed constructor are closed fields of the
inductive type. -/
theorem mem_closedFields {cs : List (DeclName × List (Field Head))} {k : DeclName}
    {fs : List (Field Head)} (mem : (k, fs) ∈ cs) {F : Tm Head 0}
    (hF : Field.closed F ∈ fs) : F ∈ closedFields cs := by
  unfold closedFields
  exact List.mem_flatMap.mpr ⟨(k, fs), mem, List.mem_filterMap.mpr ⟨.closed F, hF, rfl⟩⟩

section Inductive

variable {n : Nat} {cs : List (DeclName × List (Field Head))}

/-- Relations at an inductive type grow with the relations of its closed field
types. -/
theorem IndRel.mono {field field' : Tm Head 0 → Pack V n}
    (grow : ∀ {F : Tm Head 0}, F ∈ closedFields cs → ∀ {a b : Tm Head n},
      (field F).rel a b → (field' F).rel a b)
    {t t' : Tm Head n} (related : IndRel V cs field t t') : IndRel V cs field' t t' := by
  refine IndRel.rec (motive_1 := fun t t' _ => IndRel V cs field' t t')
    (motive_2 := fun fs as as' _ => (∀ {F : Tm Head 0}, Field.closed F ∈ fs →
      F ∈ closedFields cs) → IndFields V cs field' fs as as') ?_ ?_ ?_ ?_ ?_ related
  · intro k fs t t' as as' mem red red' _ ih
    exact .ctor mem red red' (ih fun hF => mem_closedFields mem hF)
  · intro t t' u u' red daimonic red' daimonic'
    exact .star red daimonic red' daimonic'
  · intro _
    exact .nil
  · intro fs t t' as as' _ _ ihHead ihRest closed
    exact .recursive ihHead (ihRest fun hF => closed (List.mem_cons_of_mem _ hF))
  · intro F fs t t' as as' hF _ ihRest closed
    exact .closed (grow (closed List.mem_cons_self) hF)
      (ihRest fun hF' => closed (List.mem_cons_of_mem _ hF'))

/-- The relation at an inductive type reads the packs of its closed field types
only. -/
theorem indRel_congr {field field' : Tm Head 0 → Pack V n}
    (same : ∀ {F : Tm Head 0}, F ∈ closedFields cs → field F = field' F) :
    IndRel V cs field = IndRel V cs field' := by
  funext t t'
  exact propext ⟨IndRel.mono fun {_} hF {_ _} h => same hF ▸ h,
    IndRel.mono fun {_} hF {_ _} h => (same hF).symm ▸ h⟩

/-- The realizers of a shape of a value read the packs of the closed field
types only. -/
theorem IndShape.real_congr (T : DeclName) {field field' : Tm Head 0 → Pack V n}
    (same : ∀ {F : Tm Head 0}, F ∈ closedFields cs → field F = field' F) {a : Tm Head n}
    {s : IndShape Head n} (shape : HasIndShape V cs a s) :
    s.real V T field = s.real V T field' := by
  refine HasIndShape.rec (motive_1 := fun _ s _ => s.real V T field = s.real V T field')
    (motive_2 := fun fs _ fields _ => (∀ {F : Tm Head 0}, Field.closed F ∈ fs →
      F ∈ closedFields cs) →
        IndShapes.reals V T field fields = IndShapes.reals V T field' fields)
    ?_ ?_ ?_ ?_ ?_ shape
  · intro k fs t as fields mem _ _ ih
    simp only [IndShape.real, ih fun hF => mem_closedFields mem hF]
  · intro t u _ _
    rfl
  · intro _
    rfl
  · intro fs a as shape rest _ _ ihShape ihRest closed
    simp only [IndShapes.reals, ihShape, ihRest fun hF => closed (List.mem_cons_of_mem _ hF)]
  · intro F fs a as rest _ ihRest closed
    simp only [IndShapes.reals, same (closed List.mem_cons_self),
      ihRest fun hF => closed (List.mem_cons_of_mem _ hF)]

/-- **The pack of an inductive type reads the packs of its closed field types
only.** -/
theorem indPack_congr (T : DeclName) {field field' : Tm Head 0 → Pack V n}
    (same : ∀ {F : Tm Head 0}, F ∈ closedFields cs → field F = field' F) :
    indPack V T cs field = indPack V T cs field' := by
  unfold indPack
  rw [indRel_congr same]
  congr 1
  funext a
  congr 1
  funext s
  exact IndShape.real_congr T same s.2

end Inductive

/-! ## Determinism -/

/-- **A type has at most one interpretation at a level.** -/
theorem SInterp.deterministic (laws : V.Laws) {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {P P' : Pack V n} (first : SInterp V l below ξ A P)
    (second : SInterp V l below ξ A P') : P = P' := by
  induction first with
  | @sort n ξ A u isUniverse _ red =>
      have normal : Whnf V.rules V.roles (.head u : Tm Head n) := head_whnf laws.shape u
      cases second with
      | sort _ _ red' =>
          cases laws.unique red red' normal (head_whnf laws.shape _)
          rfl
      | ground notUniverse red' =>
          cases laws.unique red red' normal (head_whnf laws.shape _)
          exact absurd isUniverse notUniverse
      | pi red' => cases laws.unique red red' normal (pi_whnf laws.shape _ _)
      | sigma red' => cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
      | ident red' => cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
      | ind red' role => cases laws.unique red red' normal (inductive_whnf laws.shape role)
      | prop red' => cases laws.unique red red' normal laws.values.whnf_prop
      | holds red' => cases laws.unique red red' normal (laws.values.whnf_holds _)
      | rigid red' role =>
          have e := laws.unique red red' normal (laws.values.whnf_rigidSpine role _)
          exact absurd e.symm Consistency.appSpine_const_ne_head
      | daimon red' daimonic =>
          exact absurd (laws.unique red red' normal (laws.daimonic_whnf daimonic)).symm
            ((laws.daimonic_not_former daimonic).1 _)
  | @ground n ξ A h notUniverse red =>
      have normal : Whnf V.rules V.roles (.head h : Tm Head n) := head_whnf laws.shape h
      cases second with
      | ground _ _ => rfl
      | rigid _ _ _ _ => rfl
      | daimon _ _ => rfl
      | sort isUniverse _ red' =>
          cases laws.unique red red' normal (head_whnf laws.shape _)
          exact absurd isUniverse notUniverse
      | pi red' => cases laws.unique red red' normal (pi_whnf laws.shape _ _)
      | sigma red' => cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
      | ident red' => cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
      | ind red' role => cases laws.unique red red' normal (inductive_whnf laws.shape role)
      | prop red' => cases laws.unique red red' normal laws.values.whnf_prop
      | holds red' => cases laws.unique red red' normal (laws.values.whnf_holds _)
  | @pi n ξ A dom cod red P _ _ _ domIH codIH =>
      have normal : Whnf V.rules V.roles (.pi dom cod) := pi_whnf laws.shape dom cod
      cases second with
      | pi red' P' domInterp' codInterp' =>
          cases laws.unique red red' normal (pi_whnf laws.shape _ _)
          exact PiPack.piPack_ext (fun w => domIH w (domInterp' w))
            (fun {_ _ _} w {_} ha ha' => codIH w ha (codInterp' w ha'))
      | sort _ _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | ground _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | sigma red' => cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
      | ident red' => cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
      | ind red' role => cases laws.unique red red' normal (inductive_whnf laws.shape role)
      | prop red' => cases laws.unique red red' normal laws.values.whnf_prop
      | holds red' => cases laws.unique red red' normal (laws.values.whnf_holds _)
      | rigid red' role =>
          have e := laws.unique red red' normal (laws.values.whnf_rigidSpine role _)
          exact absurd e.symm Consistency.appSpine_const_ne_pi
      | daimon red' daimonic =>
          exact absurd (laws.unique red red' normal (laws.daimonic_whnf daimonic)).symm
            ((laws.daimonic_not_former daimonic).2.1 _ _)
  | @sigma n ξ A dom cod red P _ _ _ domIH codIH =>
      have normal : Whnf V.rules V.roles (.sigma dom cod) := sigma_whnf laws.shape dom cod
      cases second with
      | sigma red' P' domInterp' codInterp' =>
          cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
          exact PiPack.sigmaPack_ext (fun w => domIH w (domInterp' w))
            (fun {_ _ _} w {_} ha ha' => codIH w ha (codInterp' w ha'))
      | sort _ _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | ground _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | pi red' => cases laws.unique red red' normal (pi_whnf laws.shape _ _)
      | ident red' => cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
      | ind red' role => cases laws.unique red red' normal (inductive_whnf laws.shape role)
      | prop red' => cases laws.unique red red' normal laws.values.whnf_prop
      | holds red' => cases laws.unique red red' normal (laws.values.whnf_holds _)
      | rigid red' role =>
          have e := laws.unique red red' normal (laws.values.whnf_rigidSpine role _)
          exact absurd e.symm Consistency.appSpine_const_ne_sigma
      | daimon red' daimonic =>
          exact absurd (laws.unique red red' normal (laws.daimonic_whnf daimonic)).symm
            ((laws.daimonic_not_former daimonic).2.2.1 _ _)
  | @ident n ξ A ty lhs rhs red R _ _ _ tyIH =>
      have normal : Whnf V.rules V.roles (.id ty lhs rhs) := id_whnf laws.shape ty lhs rhs
      cases second with
      | ident red' R' tyInterp' =>
          cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
          cases tyIH tyInterp'
          rfl
      | sort _ _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | ground _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | pi red' => cases laws.unique red red' normal (pi_whnf laws.shape _ _)
      | sigma red' => cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
      | ind red' role => cases laws.unique red red' normal (inductive_whnf laws.shape role)
      | prop red' => cases laws.unique red red' normal laws.values.whnf_prop
      | holds red' => cases laws.unique red red' normal (laws.values.whnf_holds _)
      | rigid red' role =>
          have e := laws.unique red red' normal (laws.values.whnf_rigidSpine role _)
          exact absurd e.symm Consistency.appSpine_const_ne_id
      | daimon red' daimonic =>
          exact absurd (laws.unique red red' normal (laws.daimonic_whnf daimonic)).symm
            ((laws.daimonic_not_former daimonic).2.2.2 _ _ _)
  | @ind n ξ A T cs red role field _ fieldIH =>
      have normal : Whnf V.rules V.roles (.const T : Tm Head n) := inductive_whnf laws.shape role
      cases second with
      | ind red' role' field' fieldInterp' =>
          cases laws.unique red red' normal (inductive_whnf laws.shape role')
          rw [role] at role'
          cases role'
          exact indPack_congr T fun hF => fieldIH hF (fieldInterp' hF)
      | sort _ _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | ground _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | pi red' => cases laws.unique red red' normal (pi_whnf laws.shape _ _)
      | sigma red' => cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
      | ident red' => cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
      | prop red' =>
          have e := Tm.const.inj (laws.unique red red' normal laws.values.whnf_prop)
          rw [e, laws.values.prop] at role
          cases role
      | holds red' => cases laws.unique red red' normal (laws.values.whnf_holds _)
      | rigid red' role' =>
          have e := laws.unique red red' normal (laws.values.whnf_rigidSpine role' _)
          obtain ⟨rfl, -⟩ := Consistency.appSpine_const_eq_const e.symm
          rw [role] at role'
          cases role'
      | daimon red' daimonic =>
          exact absurd (laws.unique red red' normal (laws.daimonic_whnf daimonic)).symm
            (laws.daimonic_ne_inductive (args := []) daimonic role)
  | @prop n ξ A red =>
      have normal : Whnf V.rules V.roles (.const V.prop : Tm Head n) := laws.values.whnf_prop
      cases second with
      | prop _ => rfl
      | sort _ _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | ground _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | pi red' => cases laws.unique red red' normal (pi_whnf laws.shape _ _)
      | sigma red' => cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
      | ident red' => cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
      | ind red' role =>
          have e := Tm.const.inj (laws.unique red red' normal (inductive_whnf laws.shape role))
          rw [← e, laws.values.prop] at role
          cases role
      | holds red' => cases laws.unique red red' normal (laws.values.whnf_holds _)
      | rigid red' role notProp =>
          have e := laws.unique red red' normal (laws.values.whnf_rigidSpine role _)
          exact absurd (Consistency.appSpine_const_eq_const e.symm).1 notProp
      | daimon red' daimonic =>
          exact absurd (laws.unique red red' normal (laws.daimonic_whnf daimonic)).symm
            (laws.daimonic_ne_prop daimonic)
  | @holds n ξ A c X red truth =>
      have normal : Whnf V.rules V.roles (.app (.const V.holds) c) := laws.values.whnf_holds c
      cases second with
      | holds red' truth' =>
          cases laws.unique red red' normal (laws.values.whnf_holds _)
          cases Consistency.Truth.deterministic laws.reading truth truth'
          rfl
      | sort _ _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | ground _ red' => cases laws.unique red red' normal (head_whnf laws.shape _)
      | pi red' => cases laws.unique red red' normal (pi_whnf laws.shape _ _)
      | sigma red' => cases laws.unique red red' normal (sigma_whnf laws.shape _ _)
      | ident red' => cases laws.unique red red' normal (id_whnf laws.shape _ _ _)
      | ind red' role => cases laws.unique red red' normal (inductive_whnf laws.shape role)
      | prop red' => cases laws.unique red red' normal laws.values.whnf_prop
      | rigid red' role _ notHolds =>
          have e := laws.unique red red' normal (laws.values.whnf_rigidSpine role _)
          exact absurd (Consistency.appSpine_const_eq_app e.symm).1 notHolds
      | daimon red' daimonic =>
          exact absurd (laws.unique red red' normal (laws.daimonic_whnf daimonic)).symm
            (laws.daimonic_ne_holds daimonic)
  | @rigid n ξ A T args red role notProp notHolds =>
      have normal : Whnf V.rules V.roles (appSpine (.const T) args) :=
        laws.values.whnf_rigidSpine role args
      cases second with
      | rigid _ _ _ _ => rfl
      | ground _ _ => rfl
      | daimon _ _ => rfl
      | sort _ _ red' =>
          exact absurd (laws.unique red red' normal (head_whnf laws.shape _))
            Consistency.appSpine_const_ne_head
      | pi red' =>
          exact absurd (laws.unique red red' normal (pi_whnf laws.shape _ _))
            Consistency.appSpine_const_ne_pi
      | sigma red' =>
          exact absurd (laws.unique red red' normal (sigma_whnf laws.shape _ _))
            Consistency.appSpine_const_ne_sigma
      | ident red' =>
          exact absurd (laws.unique red red' normal (id_whnf laws.shape _ _ _))
            Consistency.appSpine_const_ne_id
      | ind red' role' =>
          have e := laws.unique red red' normal (inductive_whnf laws.shape role')
          obtain ⟨rfl, -⟩ := Consistency.appSpine_const_eq_const e
          rw [role] at role'
          cases role'
      | prop red' =>
          have e := laws.unique red red' normal laws.values.whnf_prop
          exact absurd (Consistency.appSpine_const_eq_const e).1 notProp
      | holds red' =>
          have e := laws.unique red red' normal (laws.values.whnf_holds _)
          exact absurd (Consistency.appSpine_const_eq_app e).1 notHolds
  | @daimon n ξ A u red daimonic =>
      have normal := laws.daimonic_whnf daimonic
      cases second with
      | daimon _ _ => rfl
      | ground _ _ => rfl
      | rigid _ _ _ _ => rfl
      | sort _ _ red' =>
          exact absurd (laws.unique red red' normal (head_whnf laws.shape _))
            ((laws.daimonic_not_former daimonic).1 _)
      | pi red' =>
          exact absurd (laws.unique red red' normal (pi_whnf laws.shape _ _))
            ((laws.daimonic_not_former daimonic).2.1 _ _)
      | sigma red' =>
          exact absurd (laws.unique red red' normal (sigma_whnf laws.shape _ _))
            ((laws.daimonic_not_former daimonic).2.2.1 _ _)
      | ident red' =>
          exact absurd (laws.unique red red' normal (id_whnf laws.shape _ _ _))
            ((laws.daimonic_not_former daimonic).2.2.2 _ _ _)
      | ind red' role =>
          exact absurd (laws.unique red red' normal (inductive_whnf laws.shape role))
            (laws.daimonic_ne_inductive (args := []) daimonic role)
      | prop red' =>
          exact absurd (laws.unique red red' normal laws.values.whnf_prop)
            (laws.daimonic_ne_prop daimonic)
      | holds red' =>
          exact absurd (laws.unique red red' normal (laws.values.whnf_holds _))
            (laws.daimonic_ne_holds daimonic)

/-- A type that reduces to a daimonic term denotes the total pack. -/
theorem SInterp.eq_total_of_daimonic (laws : V.Laws) {n : Nat} {ξ : World V.reading n}
    {A u : Tm Head n} {P : Pack V n} (interp : SInterp V l below ξ A P)
    (red : WhRed V.rules V.roles A u) (daimonic : Daimonic V.roles V.star u) :
    P = Pack.total V n :=
  interp.deterministic laws (.daimon red daimonic)

/-! ## Inversion -/

section Inversion

variable (laws : V.Laws)
include laws

/-- A type that reduces to a dependent function type denotes the functions of a
family that interprets its domain and codomain. -/
theorem SInterp.pi_inv {n : Nat} {ξ : World V.reading n} {X A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (interp : SInterp V l below ξ X P)
    (red : WhRed V.rules V.roles X (.pi A B)) :
    ∃ Q : PiPack V ξ, P = Q.piPack ∧ Q.Interprets (SInterp V l below) A B := by
  have normal := pi_whnf laws.shape A B
  cases interp.reduce laws red with
  | pi r Q domInterp codInterp codRespect =>
      cases whRed_of_whnf normal r
      exact ⟨Q, rfl, domInterp, codInterp, codRespect⟩
  | sort _ _ r => cases whRed_of_whnf normal r
  | ground _ r => cases whRed_of_whnf normal r
  | sigma r => cases whRed_of_whnf normal r
  | ident r => cases whRed_of_whnf normal r
  | ind r => cases whRed_of_whnf normal r
  | prop r => cases whRed_of_whnf normal r
  | holds r => cases whRed_of_whnf normal r
  | rigid r =>
      exact absurd (whRed_of_whnf normal r) Consistency.appSpine_const_ne_pi
  | daimon r daimonic =>
      exact absurd (whRed_of_whnf normal r)
        ((laws.daimonic_not_former daimonic).2.1 _ _)

/-- A type that reduces to a dependent pair type denotes the pairs of a family
that interprets its domain and codomain. -/
theorem SInterp.sigma_inv {n : Nat} {ξ : World V.reading n} {X A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (interp : SInterp V l below ξ X P)
    (red : WhRed V.rules V.roles X (.sigma A B)) :
    ∃ Q : PiPack V ξ, P = Q.sigmaPack ∧ Q.Interprets (SInterp V l below) A B := by
  have normal := sigma_whnf laws.shape A B
  cases interp.reduce laws red with
  | sigma r Q domInterp codInterp codRespect =>
      cases whRed_of_whnf normal r
      exact ⟨Q, rfl, domInterp, codInterp, codRespect⟩
  | sort _ _ r => cases whRed_of_whnf normal r
  | ground _ r => cases whRed_of_whnf normal r
  | pi r => cases whRed_of_whnf normal r
  | ident r => cases whRed_of_whnf normal r
  | ind r => cases whRed_of_whnf normal r
  | prop r => cases whRed_of_whnf normal r
  | holds r => cases whRed_of_whnf normal r
  | rigid r =>
      exact absurd (whRed_of_whnf normal r) Consistency.appSpine_const_ne_sigma
  | daimon r daimonic =>
      exact absurd (whRed_of_whnf normal r)
        ((laws.daimonic_not_former daimonic).2.2.1 _ _)

/-- A type that reduces to an identity type denotes the identity pack of the
pack of its carrier, at which the endpoints are valid. -/
theorem SInterp.id_inv {n : Nat} {ξ : World V.reading n} {X A a b : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ X P) (red : WhRed V.rules V.roles X (.id A a b)) :
    ∃ R : Pack V n, P = identPack R a b ∧ SInterp V l below ξ A R ∧ R.Val a ∧ R.Val b := by
  have normal := id_whnf laws.shape A a b
  cases interp.reduce laws red with
  | ident r R tyInterp lhsVal rhsVal =>
      cases whRed_of_whnf normal r
      exact ⟨R, rfl, tyInterp, lhsVal, rhsVal⟩
  | sort _ _ r => cases whRed_of_whnf normal r
  | ground _ r => cases whRed_of_whnf normal r
  | pi r => cases whRed_of_whnf normal r
  | sigma r => cases whRed_of_whnf normal r
  | ind r => cases whRed_of_whnf normal r
  | prop r => cases whRed_of_whnf normal r
  | holds r => cases whRed_of_whnf normal r
  | rigid r =>
      exact absurd (whRed_of_whnf normal r) Consistency.appSpine_const_ne_id
  | daimon r daimonic =>
      exact absurd (whRed_of_whnf normal r)
        ((laws.daimonic_not_former daimonic).2.2.2 _ _ _)

/-- A type that reduces to a head denotes the pack of the universe below the
level at its level, when the head is a universe, and the total pack
otherwise. -/
theorem SInterp.head_inv {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {u : Head}
    {P : Pack V n} (interp : SInterp V l below ξ X P) (red : WhRed V.rules V.roles X (.head u)) :
    (V.rules.isUniverse u ∧ V.levels.level u < l ∧
        P = universePack V (below (V.levels.level u)) ξ) ∨
      (¬ V.rules.isUniverse u ∧ P = Pack.total V n) := by
  have normal := head_whnf laws.shape (n := n) u
  cases interp.reduce laws red with
  | sort isUniverse level r =>
      cases whRed_of_whnf normal r
      exact .inl ⟨isUniverse, level, rfl⟩
  | ground notUniverse r =>
      cases whRed_of_whnf normal r
      exact .inr ⟨notUniverse, rfl⟩
  | pi r => cases whRed_of_whnf normal r
  | sigma r => cases whRed_of_whnf normal r
  | ident r => cases whRed_of_whnf normal r
  | ind r => cases whRed_of_whnf normal r
  | prop r => cases whRed_of_whnf normal r
  | holds r => cases whRed_of_whnf normal r
  | rigid r =>
      exact absurd (whRed_of_whnf normal r) Consistency.appSpine_const_ne_head
  | daimon r daimonic =>
      exact absurd (whRed_of_whnf normal r)
        ((laws.daimonic_not_former daimonic).1 _)

/-- A type that reduces to a universe denotes that universe's pack, over the
interpretation below the level at the universe's level. -/
theorem SInterp.univ_inv {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {u : Head}
    {P : Pack V n} (interp : SInterp V l below ξ X P) (red : WhRed V.rules V.roles X (.head u))
    (isUniverse : V.rules.isUniverse u) :
    V.levels.level u < l ∧ P = universePack V (below (V.levels.level u)) ξ := by
  rcases interp.head_inv laws red with ⟨_, level, rfl⟩ | ⟨notUniverse, -⟩
  · exact ⟨level, rfl⟩
  · exact absurd isUniverse notUniverse

/-- A type that reduces to an inductive type denotes its inductive pack, over
packs that interpret its closed field types. -/
theorem SInterp.ind_inv {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {T : DeclName}
    {cs : List (DeclName × List (Field Head))} {P : Pack V n} (interp : SInterp V l below ξ X P)
    (red : WhRed V.rules V.roles X (.const T)) (role : V.roles T = .inductive cs) :
    ∃ field : Tm Head 0 → Pack V n, P = indPack V T cs field ∧
      ∀ {F : Tm Head 0}, F ∈ closedFields cs →
        SInterp V l below ξ (liftClosed F) (field F) := by
  have normal : Whnf V.rules V.roles (.const T : Tm Head n) := inductive_whnf laws.shape role
  cases interp.reduce laws red with
  | ind r role' field fieldInterp =>
      cases whRed_of_whnf normal r
      rw [role] at role'
      cases role'
      exact ⟨field, rfl, fieldInterp⟩
  | sort _ _ r => cases whRed_of_whnf normal r
  | ground _ r => cases whRed_of_whnf normal r
  | pi r => cases whRed_of_whnf normal r
  | sigma r => cases whRed_of_whnf normal r
  | ident r => cases whRed_of_whnf normal r
  | prop r =>
      have e := Tm.const.inj (whRed_of_whnf normal r)
      rw [← e, laws.values.prop] at role
      cases role
  | holds r => cases whRed_of_whnf normal r
  | rigid r role' =>
      obtain ⟨rfl, -⟩ := Consistency.appSpine_const_eq_const (whRed_of_whnf normal r)
      rw [role] at role'
      cases role'
  | daimon r daimonic =>
      exact absurd (whRed_of_whnf normal r)
        (laws.daimonic_ne_inductive (args := []) daimonic role)

/-- A type that reduces to a decoding denotes the pack of the meaning of the
code. -/
theorem SInterp.holds_inv {n : Nat} {ξ : World V.reading n} {X c : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ X P) (red : WhRed V.rules V.roles X (.app (.const V.holds) c)) :
    ∃ Y : V.alg.Cand, Truth V.reading ξ c Y ∧ P = holdsPack V n Y := by
  have normal := laws.values.whnf_holds c
  cases interp.reduce laws red with
  | holds r truth =>
      cases whRed_of_whnf normal r
      exact ⟨_, truth, rfl⟩
  | sort _ _ r => cases whRed_of_whnf normal r
  | ground _ r => cases whRed_of_whnf normal r
  | pi r => cases whRed_of_whnf normal r
  | sigma r => cases whRed_of_whnf normal r
  | ident r => cases whRed_of_whnf normal r
  | ind r => cases whRed_of_whnf normal r
  | prop r => cases whRed_of_whnf normal r
  | rigid r _ _ notHolds =>
      exact absurd (Consistency.appSpine_const_eq_app (whRed_of_whnf normal r)).1
        notHolds
  | daimon r daimonic =>
      exact absurd (whRed_of_whnf normal r) (laws.daimonic_ne_holds daimonic)

end Inversion

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
