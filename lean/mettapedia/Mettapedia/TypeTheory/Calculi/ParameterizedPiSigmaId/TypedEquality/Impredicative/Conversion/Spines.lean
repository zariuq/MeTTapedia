import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Root
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Inclusion

/-!
# Structural inclusion and the typing facts of spines and heads

A root step whose two sides need the typing of the redex is validated with the
facts a typing derivation records about a spine of a declared constant: its
arguments are valid inputs of the constant's declared telescope, with realizer
instances related to themselves at some realizer type, and what remains of the
declared type lies structurally below the type the spine is typed at, or that
type relates every pair (`SpineFactsN`). The facts start at a declared constant,
extend along an application, and pass along inclusion and conversion. Structural
inclusion is the value side's (`ValueSide.SLe`), read under related valuations
(`ValidLeStructN`).

A typing of a head records the same kind of fact: the type of a head lies
structurally above a universe under related valuations (`HeadFactsN`), so it is
a universe there (`HeadFactsN.type_universe`). A head starts it at its universe, and
inclusion and conversion carry it to the new type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open ValueSide (SLe universeAt)

variable {Head L : Type} [LevelOrder L] {M : NModel Head L}

/-! ## The facts of a spine -/

variable (M) in
/-- Per world: the arguments `as`, with realizer instances `ss` in the realizer
context `Δ`, are valid inputs of the declared partial type `D` in order, each
realizer related to itself at some realizer type by the realizers of its value,
and the rest of `D` is included in `X`. -/
def SpineOKN {m r : Nat} (ξ : World M.reading m) (Δ : Ctx Head r) :
    Tm Head m → List (Tm Head m) → List (Tm Head r) → Tm Head m → Prop
  | D, [], [], X => SLe M.value ξ D X
  | D, a :: as, s :: ss, X => ∃ A B, WhRed M.rules M.roles D (.pi A B) ∧
      (∃ P : NPack M m, DenN M ξ A P ∧ P.Val a ∧ ∃ Y, (P.real a).rel Δ Y s s) ∧
      SpineOKN ξ Δ (Presentation.inst0 a B) as ss X
  | _, [], _ :: _, _ => False
  | _, _ :: _, [], _ => False

namespace SpineOKN

variable {m r : Nat} {ξ : World M.reading m} {Δ : Ctx Head r}

/-- The facts pass along inclusion of the type. -/
theorem mono : ∀ {D : Tm Head m} {as : List (Tm Head m)} {ss : List (Tm Head r)}
    {X Y : Tm Head m}, SpineOKN M ξ Δ D as ss X → SLe M.value ξ X Y → SpineOKN M ξ Δ D as ss Y
  | _, [], [], _, _, h, le => .trans h le
  | _, _ :: _, _ :: _, _, _, ⟨A, B, red, val, rest⟩, le => ⟨A, B, red, val, mono rest le⟩
  | _, [], _ :: _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, h, _ => h.elim

/-- **An application extends the facts**: an argument valid at the domain of a
dependent function type the spine is included in is a valid input of the
declared telescope, whose rest is included in the codomain at the argument; or
the codomain there is hereditarily total. -/
theorem app (laws : M.Laws) : ∀ {D : Tm Head m} {as : List (Tm Head m)}
    {ss : List (Tm Head r)} {A : Tm Head m} {B : Tm Head (m + 1)} {a : Tm Head m}
    {s : Tm Head r}, SpineOKN M ξ Δ D as ss (.pi A B) →
      (∀ {P : NPack M m}, DenN M ξ A P → P.Val a ∧ ∃ Y, (P.real a).rel Δ Y s s) →
      SpineOKN M ξ Δ D (as ++ [a]) (ss ++ [s]) (Presentation.inst0 a B) ∨
        ValueSide.Shape M.value (DenN M) .total ξ (Presentation.inst0 a B)
          (Presentation.inst0 a B)
  | _, [], [], A, B, a, s, h, valid => by
      rcases ValueSide.SLe.pi_right laws.value h .refl with t | ⟨A₀, B₀, red, dom, cod⟩
      · obtain ⟨-, P, hP⟩ := ValueSide.SLe.den h
        obtain ⟨Q, rfl, iQ⟩ := (DenN.facts laws).piPack hP .refl
        exact .inr (ValueSide.total_cod laws.value t .refl iQ.dom_id (valid iQ.dom_id).1)
      · obtain ⟨D₀, hA₀, hA, -⟩ := dom (Morph.id ξ)
        rw [rename_id] at hA₀ hA
        obtain ⟨val, real⟩ := valid hA
        refine .inl ⟨A₀, B₀, red, ⟨D₀, hA₀, val, real⟩, ?_⟩
        have c := cod (Morph.id ξ) (by rwa [rename_id]) val
        rwa [liftRen_id, rename_id, rename_id] at c
  | _, _ :: _, _ :: _, _, _, _, _, ⟨A₀, B₀, red, val₀, rest⟩, valid => by
      rcases app laws rest valid with h | h
      · exact .inl ⟨A₀, B₀, red, val₀, h⟩
      · exact .inr h
  | _, [], _ :: _, _, _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, _, _, h, _ => h.elim

end SpineOKN

/-- The typing facts of a spine of a declared constant: under related
valuations, the instances of its arguments are valid inputs of the constant's
declared telescope, with realizer instances related to themselves, and the rest
of the declared type is included in the instance of the type, or that instance
is hereditarily total. -/
def SpineFactsN (R : Rules Head) (M : NModel Head L) {n : Nat} (Γ : Ctx Head n)
    (t A : Tm Head n) : Prop :=
  ∀ {c : DeclName} {args : List (Tm Head n)} {T : Tm Head 0},
    t = appSpine (.const c) args → R.constantType c = some T →
      ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
        {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
          SpineOKN M ξ Δ (liftClosed T) (args.map (Presentation.subst σ))
              (args.map (Presentation.subst ς)) (Presentation.subst σ A) ∨
            ValueSide.Shape M.value (DenN M) .total ξ (Presentation.subst σ A)
              (Presentation.subst σ A)

variable (M) in
/-- A type structurally below another under related valuations. -/
def ValidLeStructN {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
      SLe M.value ξ (Presentation.subst σ A) (Presentation.subst σ B)

variable (M) in
/-- The typing facts of a head: the type of a head lies structurally above a
universe under related valuations. -/
def HeadFactsN {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) : Prop :=
  ∀ {h : Head}, t = .head h → ∃ u, M.rules.isUniverse u ∧ ValidLeStructN M Γ (.head u) A

/-! ## Structural inclusion under valuations -/

section Valuations

variable (laws : M.Laws)
include laws

/-- Validly equal types of a universe are related in it under the first of two
related valuations. -/
theorem ValidEqN.universe_left {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (eq : ValidEqN M Γ A B (.head u)) (hu : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ A)
      (Presentation.subst σ B) := by
  have den := ValueSide.DenS.sort (V := M.value) hu ξ
  have h₁ : (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ A)
      (Presentation.subst σ' B) := (eq.universe hu e).1
  have h₂ : (universeAt M.value (M.levels.level u) ξ).rel (Presentation.subst σ B)
      (Presentation.subst σ' B) := (ValidTmN.universe eq.2.1 hu e).1
  intro k ξ' ρ w
  exact ValueSide.DenS.trans laws.value den h₁ (ValueSide.DenS.symm laws.value den h₂) w

/-- Validly equal types of a universe are structurally included. -/
theorem ValidLeStructN.ofEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (eq : ValidEqN M Γ A B (.head u)) (hu : M.rules.isUniverse u) : ValidLeStructN M Γ A B :=
  fun e => ValueSide.SLe.of_universe laws.value (ValidEqN.universe_left laws eq hu e)

omit laws in
/-- Universes are included along cumulativity. -/
theorem ValidLeStructN.univ {n : Nat} {Γ : Ctx Head n} {u v : Head}
    (cumulative : M.rules.cumulative u v) : ValidLeStructN M Γ (.head u) (.head v) := by
  obtain ⟨hu, hv, le⟩ := M.levels.cumulative_universe cumulative
  exact fun _ => .univ .refl .refl hu hv le

/-- Dependent function types with equal domains of a universe and included
codomains are included. -/
theorem ValidLeStructN.pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {w : Head} (validPi : ValidTyN M Γ (.pi A B))
    (validPi' : ValidTyN M Γ (.pi A' B')) (eqA : ValidEqN M Γ A A' (.head w))
    (hw : M.rules.isUniverse w) (leB : ValidLeStructN M (.snoc Γ A) B B') :
    ValidLeStructN M Γ (.pi A B) (.pi A' B') := by
  intro m r ξ σ σ' Δ ς ς' e
  obtain ⟨P, den, -, types⟩ := validPi e
  obtain ⟨P', den', -, -⟩ := validPi' e
  obtain ⟨typeA, -⟩ := IsType.pi_parts types.left
  refine .pi den den' .refl .refl (fun {_ _ ρ} mor => ?_)
    (fun {_ ξ' ρ} mor {D} hD {a} ha => ?_)
  · obtain ⟨D, hA, hA', s⟩ := ValueSide.universeAt.den
      (ValidEqN.universe_left laws eqA hw (EqSubstN.rename laws e mor))
    rw [rename_subst, rename_subst]
    exact ⟨D, ⟨_, hA⟩, ⟨_, hA'⟩, s.mono (ValueSide.InterpAt.facts laws.value _)
      (fun h => ⟨_, h⟩) (DenN.facts laws).deterministic⟩
  · have hD' : DenN M ξ' (Presentation.subst (fun i => Presentation.rename ρ (σ i)) A) D := by
      rwa [← rename_subst]
    have h := leB ((EqSubstN.rename laws e mor).consVar typeA hD' ha)
    rwa [← inst0_rename_subst_liftSub, ← inst0_rename_subst_liftSub] at h

omit laws in
/-- Dependent pair types with included domains and codomains are included. -/
theorem ValidLeStructN.sigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (validS : ValidTyN M Γ (.sigma A B))
    (validS' : ValidTyN M Γ (.sigma A' B')) (leA : ValidLeStructN M Γ A A')
    (leB : ValidLeStructN M (.snoc Γ A) B B') :
    ValidLeStructN M Γ (.sigma A B) (.sigma A' B') := by
  intro m r ξ σ σ' Δ ς ς' e
  obtain ⟨P, den, -, types⟩ := validS e
  obtain ⟨P', den', -, -⟩ := validS' e
  obtain ⟨typeA, -⟩ := IsType.sigma_parts types.left
  refine .sigma den den' .refl .refl (leA e) (fun {D} hD {a} ha => ?_)
  have h := leB (e.consVar typeA hD ha)
  rwa [← inst0_subst_liftSub, ← inst0_subst_liftSub] at h

omit laws in
/-- Structural inclusion composes. -/
theorem ValidLeStructN.trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (first : ValidLeStructN M Γ A B) (second : ValidLeStructN M Γ B C) :
    ValidLeStructN M Γ A C :=
  fun e => .trans (first e) (second e)

end Valuations

/-! ## The facts of spines along the typing rules -/

namespace SpineFactsN

variable {R : Rules Head}

/-- A term that is no spine of a constant has the facts vacuously. -/
theorem of_not_spine {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (notSpine : ∀ (c : DeclName) (args : List (Tm Head n)), t ≠ appSpine (.const c) args) :
    SpineFactsN R M Γ t A :=
  fun e => absurd e (notSpine _ _)

/-- A term that is neither a constant nor an application is no spine of a
constant. -/
theorem of_ne {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (notConst : ∀ c : DeclName, t ≠ .const c) (notApp : ∀ f a : Tm Head n, t ≠ .app f a) :
    SpineFactsN R M Γ t A :=
  of_not_spine fun c args e => by
    rcases Normalization.appSpine_const_cases c args with e' | ⟨f, a, e'⟩
    · exact notConst c (e.trans e')
    · exact notApp f a (e.trans e')

/-- **A declared constant starts a spine**: no arguments, and its declared type
included in itself. -/
theorem const (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0}
    {u : Head} (declared : R.constantType name = some type)
    (validType : ValidTmN M Γ (liftClosed type) (.head u)) (hu : M.rules.isUniverse u) :
    SpineFactsN R M Γ (.const name) (liftClosed type) := by
  intro c args T e declared' m r ξ σ σ' Δ ς ς' eq
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective (as := []) e
  obtain rfl := Option.some.inj (declared.symm.trans declared')
  refine .inl ?_
  have related : (universeAt M.value (M.levels.level u) ξ).rel
      (Presentation.subst σ (liftClosed type)) (Presentation.subst σ' (liftClosed type)) :=
    (ValidTmN.universe validType hu eq).1
  rw [subst_liftClosed, subst_liftClosed] at related
  rw [subst_liftClosed]
  exact ValueSide.SLe.of_universe laws.value related

/-- **An application extends a spine.** -/
theorem app (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n}
    {B : Tm Head (n + 1)} (facts : SpineFactsN R M Γ g (.pi A B))
    (validA : ValidTmN M Γ a A) : SpineFactsN R M Γ (.app g a) (Presentation.inst0 a B) := by
  intro c args T e declared m r ξ σ σ' Δ ς ς' eq
  obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app e.symm
  have valid : ∀ {P : NPack M m}, DenN M ξ (Presentation.subst σ A) P →
      P.Val (Presentation.subst σ a) ∧
        ∃ Y, (P.real (Presentation.subst σ a)).rel Δ Y (Presentation.subst ς a)
          (Presentation.subst ς a) := fun {P} den =>
    ⟨ValueSide.DenS.refl_left laws.value den (validA.2 eq den).1, _,
      (P.real _).refl_left (validA.2 eq den).2⟩
  rw [subst_inst0, List.map_append, List.map_append]
  rcases facts rfl declared eq with h | t
  · exact SpineOKN.app laws h valid
  · obtain ⟨P, hP⟩ := t.total_interp
    obtain ⟨Q, rfl, iQ⟩ := (DenN.facts laws).piPack hP .refl
    exact .inr (ValueSide.total_cod laws.value t .refl iQ.dom_id (valid iQ.dom_id).1)

/-- **The facts pass along structural inclusion** of the type. -/
theorem below (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (facts : SpineFactsN R M Γ t A) (le : ValidLeStructN M Γ A B) : SpineFactsN R M Γ t B := by
  intro c args T e declared m r ξ σ σ' Δ ς ς' eq
  rcases facts e declared eq with h | t
  · exact .inl (h.mono (le eq))
  · exact .inr ((le eq).total laws.value t)

end SpineFactsN

/-! ## The facts of heads along the typing rules -/

namespace HeadFactsN

/-- A term that is no head has the facts vacuously. -/
theorem of_ne {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (notHead : ∀ h : Head, t ≠ .head h) :
    HeadFactsN M Γ t A :=
  fun e => absurd e (notHead _)

/-- **A head typed by a universe starts the facts at that universe.** -/
theorem head {n : Nat} {Γ : Ctx Head n} {h u : Head} (hu : M.rules.isUniverse u) :
    HeadFactsN M Γ (.head h) (.head u) :=
  fun _ => ⟨u, hu, fun _ => .univ .refl .refl hu hu le_rfl⟩

/-- **The facts pass along structural inclusion** of the type. -/
theorem below {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n} (facts : HeadFactsN M Γ t A)
    (le : ValidLeStructN M Γ A B) : HeadFactsN M Γ t B := fun e => by
  obtain ⟨u, hu, le₀⟩ := facts e
  exact ⟨u, hu, le₀.trans le⟩

/-- **The type of a head is a universe under related valuations.** -/
theorem type_universe (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {h : Head} {A : Tm Head n}
    (facts : HeadFactsN M Γ (.head h) A) {m r : Nat} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {Δ : Ctx Head r} {ς ς' : Sub Head n r}
    (e : EqSubstN M Γ ξ σ σ' Δ ς ς') :
    ∃ v, M.rules.isUniverse v ∧ WhRed M.rules M.roles (Presentation.subst σ A) (.head v) := by
  obtain ⟨u, hu, le⟩ := facts rfl
  obtain ⟨v, red, hv⟩ := ValueSide.SLe.univ_left laws.value (le e) .refl hu
  exact ⟨v, hv, red⟩

end HeadFactsN

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
