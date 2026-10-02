import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Equality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Inclusion

/-!
# Structural inclusion and the typing facts of spines

A root step whose two sides need the typing of the redex (identity elimination
at reflexivity, read by transport) is validated with the facts a typing
derivation records about a spine of a declared constant: its arguments are
valid inputs of the constant's declared telescope, and what remains of the
declared type lies structurally below the type the spine is typed at.

**Structural inclusion** (`SLe`, the value side's) is read in one world, between
two denoted types:

* types of one shape whose packs have one relation (conversion, and a type with
  itself);
* universes, by level (cumulativity);
* dependent function types whose domains have one pack and one shape at every
  world reached by a morphism, and whose codomains are included at every valid
  argument (inclusion of function types keeps domains equal);
* dependent pair types whose domains and codomains are included;
* and the composites of these.

It includes value relations (`ValueSide.SLe.rel`), and it carries hereditary totality
forward (`SLe.total`). Its inversion at a dependent function type on the right
(`SLe.pi_right`) is the step of a spine: either the type is hereditarily total,
or the included type is a dependent function type too, with a domain of one
pack, so an argument valid at the one domain is valid, realizers included, at
the other, and with included codomains. The domain carries its whole pack
because the universe relation's clause for dependent function types does
(`ValueSide.Shape.pi`).

**The facts of a spine** (`SpineFacts`), under related valuations, are
`SpineOK`: the instances of the arguments, with their realizer instances, are
valid inputs of the declared telescope in order, and the rest of the declared
type is included in the instance of the type; or that instance is hereditarily
total, and every pair of values is related there anyway. The facts start at a
declared constant, extend along an application, and pass along inclusion and
conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-! ## Structural inclusion in a world -/

variable (M) in
/-- **Structural inclusion** of types in a world: the value side's. -/
abbrev SLe {n : Nat} (ξ : World M.reading n) (X Y : Tm Head n) : Prop :=
  ValueSide.SLe M.value ξ X Y

/-- **Hereditary totality passes forward** along inclusion. -/
theorem SLe.total (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {X Y : Tm Head n}
    (le : SLe M ξ X Y) :
    Shape M.value (DenS M.value) .total ξ X X → Shape M.value (DenS M.value) .total ξ Y Y :=
  ValueSide.SLe.total laws.value le

/-! ## Inversion at dependent function types -/

variable (M) in
/-- The premises of the clause of dependent function types: the value side's. -/
abbrev PiLe {n : Nat} (ξ : World M.reading n) (A A' : Tm Head n) (B B' : Tm Head (n + 1)) :
    Prop :=
  ValueSide.PiLe M.value ξ A A' B B'

section Inversion

variable (laws : M.Laws)
include laws

/-- **Inversion at a dependent function type on the right.** A type included in
a dependent function type is hereditarily total there, or is a dependent
function type with a domain of one pack and one shape and included codomains. -/
theorem SLe.pi_right {n : Nat} {ξ : World M.reading n} {X Y : Tm Head n}
    (le : SLe M ξ X Y) :
    ∀ {A' : Tm Head n} {B' : Tm Head (n + 1)}, WhRed M.rules M.roles Y (.pi A' B') →
      Shape M.value (DenS M.value) .total ξ Y Y ∨
        ∃ A B, WhRed M.rules M.roles X (.pi A B) ∧ PiLe M ξ A A' B B' :=
  ValueSide.SLe.pi_right laws.value le

/-- A hereditarily total dependent function type has hereditarily total
codomains at the valid arguments of its domain. -/
theorem total_cod {n : Nat} {ξ : World M.reading n} {X A : Tm Head n} {B : Tm Head (n + 1)}
    (t : Shape M.value (DenS M.value) .total ξ X X) (red : WhRed M.rules M.roles X (.pi A B))
    {D : Pack M.value n} (hD : DenS M.value ξ A D) {a : Tm Head n} (ha : D.Val a) :
    Shape M.value (DenS M.value) .total ξ (inst0 a B) (inst0 a B) :=
  ValueSide.total_cod laws.value t red hD ha

end Inversion

/-! ## The facts of a spine -/

variable (M) in
/-- Per world: the arguments `as`, with realizer instances `ss`, are valid inputs
of the declared partial type `D` in order, and the rest of `D` is included in
`X`. -/
def SpineOK {m r : Nat} (ξ : World M.reading m) :
    Tm Head m → List (Tm Head m) → List (Tm Head r) → Tm Head m → Prop
  | D, [], [], X => SLe M ξ D X
  | D, a :: as, s :: ss, X => ∃ A B, WhRed M.rules M.roles D (.pi A B) ∧
      (∃ P, DenS M.value ξ A P ∧ P.Val a ∧ (P.real a).mem s) ∧ SpineOK ξ (inst0 a B) as ss X
  | _, [], _ :: _, _ => False
  | _, _ :: _, [], _ => False

namespace SpineOK

variable {m r : Nat} {ξ : World M.reading m}

/-- The facts pass along inclusion of the type. -/
theorem mono : ∀ {D : Tm Head m} {as : List (Tm Head m)} {ss : List (Tm Head r)}
    {X Y : Tm Head m}, SpineOK M ξ D as ss X → SLe M ξ X Y → SpineOK M ξ D as ss Y
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
    {s : Tm Head r}, SpineOK M ξ D as ss (.pi A B) →
      (∀ {P : Pack M.value m}, DenS M.value ξ A P → P.Val a ∧ (P.real a).mem s) →
      SpineOK M ξ D (as ++ [a]) (ss ++ [s]) (inst0 a B) ∨
        Shape M.value (DenS M.value) .total ξ (inst0 a B) (inst0 a B)
  | _, [], [], A, B, a, s, h, valid => by
      rcases SLe.pi_right laws h .refl with t | ⟨A₀, B₀, red, dom, cod⟩
      · obtain ⟨-, P, hP⟩ := SLe.den h
        obtain ⟨Q, rfl, iQ⟩ := (DenS.facts laws.value).piPack hP .refl
        exact .inr (total_cod laws t .refl iQ.dom_id (valid iQ.dom_id).1)
      · obtain ⟨D₀, hA₀, hA, -⟩ := dom (Morph.id ξ)
        rw [rename_id] at hA₀ hA
        obtain ⟨val, mem⟩ := valid hA
        refine .inl ⟨A₀, B₀, red, ⟨D₀, hA₀, val, mem⟩, ?_⟩
        have c := cod (Morph.id ξ) (by rwa [rename_id]) val
        rwa [liftRen_id, rename_id, rename_id] at c
  | _, _ :: _, _ :: _, _, _, _, _, ⟨A₀, B₀, red, val₀, rest⟩, valid => by
      rcases app laws rest valid with h | h
      · exact .inl ⟨A₀, B₀, red, val₀, h⟩
      · exact .inr h
  | _, [], _ :: _, _, _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, _, _, h, _ => h.elim

end SpineOK

/-- The typing facts of a spine of a declared constant: under related
valuations, the instances of its arguments are valid inputs of the constant's
declared telescope and the rest of the declared type is included in the
instance of the type, or that instance is hereditarily total. -/
def SpineFacts (R : Rules Head) (M : SNModel Head L) {n : Nat} (Γ : Ctx Head n)
    (t A : Tm Head n) : Prop :=
  ∀ {c : DeclName} {args : List (Tm Head n)} {T : Tm Head 0},
    t = appSpine (.const c) args → R.constantType c = some T →
      ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
        EqSubstS M Γ ξ σ σ' ς →
          SpineOK M ξ (liftClosed T) (args.map (Presentation.subst σ))
              (args.map (Presentation.subst ς)) (Presentation.subst σ A) ∨
            Shape M.value (DenS M.value) .total ξ (Presentation.subst σ A)
              (Presentation.subst σ A)

variable (M) in
/-- A type structurally below another under related valuations. -/
def ValidLeStructS {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
    EqSubstS M Γ ξ σ σ' ς → SLe M ξ (Presentation.subst σ A) (Presentation.subst σ B)

/-! ## Structural inclusion under valuations -/

section Valuations

variable (laws : M.Laws)
include laws

/-- Validly equal types of a universe are related in it under the first of two
related valuations. -/
theorem ValidEqS.universe_left {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (eq : ValidEqS M Γ A B (.head u)) (hu : M.rules.isUniverse u) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ A) (Presentation.subst σ B) := by
  have den := ValueSide.DenS.sort (V := M.value) hu ξ
  have h₁ : (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ A)
      (Presentation.subst σ' B) := eq.universe hu e
  have h₂ : (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ B)
      (Presentation.subst σ' B) := (ValidTmS.universe eq.2.1 hu e).1
  intro k ξ' ρ w
  exact den.trans laws.value h₁ (den.symm laws.value h₂) w

/-- Validly equal types of a universe are structurally included. -/
theorem ValidLeStructS.ofEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (eq : ValidEqS M Γ A B (.head u)) (hu : M.rules.isUniverse u) : ValidLeStructS M Γ A B :=
  fun e => SLe.of_universe laws.value (ValidEqS.universe_left laws eq hu e)

omit laws in
/-- Universes are included along cumulativity. -/
theorem ValidLeStructS.univ {n : Nat} {Γ : Ctx Head n} {u v : Head}
    (cumulative : M.rules.cumulative u v) : ValidLeStructS M Γ (.head u) (.head v) := by
  obtain ⟨hu, hv, le⟩ := M.levels.cumulative_universe cumulative
  exact fun _ => .univ .refl .refl hu hv le

/-- Dependent function types with equal domains of a universe and included
codomains are included. -/
theorem ValidLeStructS.pi {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {w : Head} (validPi : ValidTyS M Γ (.pi A B))
    (validPi' : ValidTyS M Γ (.pi A' B')) (eqA : ValidEqS M Γ A A' (.head w))
    (hw : M.rules.isUniverse w) (leB : ValidLeStructS M (.snoc Γ A) B B') :
    ValidLeStructS M Γ (.pi A B) (.pi A' B') := by
  intro m r ξ σ σ' ς e
  obtain ⟨P, den, -, -⟩ := validPi e
  obtain ⟨P', den', -, -⟩ := validPi' e
  refine .pi den den' .refl .refl (fun {_ _ ρ} mor => ?_)
    (fun {_ ξ' ρ} mor {D} hD {a} ha => ?_)
  · obtain ⟨D, hA, hA', s⟩ :=
      universeAt.den (ValidEqS.universe_left laws eqA hw (EqSubstS.rename laws e mor))
    rw [rename_subst, rename_subst]
    exact ⟨D, ⟨_, hA⟩, ⟨_, hA'⟩, s.mono (InterpAt.facts laws.value _) (fun h => ⟨_, h⟩)
      (DenS.facts laws.value).deterministic⟩
  · have hD' : DenS M.value ξ'
        (Presentation.subst (fun i => Presentation.rename ρ (σ i)) A) D := by
      rwa [← rename_subst]
    have h := leB ((EqSubstS.rename laws e mor).consVar hD' ha)
    rwa [← inst0_rename_subst_liftSub, ← inst0_rename_subst_liftSub] at h

omit laws in
/-- Dependent pair types with included domains and codomains are included. -/
theorem ValidLeStructS.sigma {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (validS : ValidTyS M Γ (.sigma A B))
    (validS' : ValidTyS M Γ (.sigma A' B')) (leA : ValidLeStructS M Γ A A')
    (leB : ValidLeStructS M (.snoc Γ A) B B') :
    ValidLeStructS M Γ (.sigma A B) (.sigma A' B') := by
  intro m r ξ σ σ' ς e
  obtain ⟨P, den, -, -⟩ := validS e
  obtain ⟨P', den', -, -⟩ := validS' e
  refine .sigma den den' .refl .refl (leA e) (fun {D} hD {a} ha => ?_)
  have h := leB (e.consVar hD ha)
  rwa [← inst0_subst_liftSub, ← inst0_subst_liftSub] at h

omit laws in
/-- Structural inclusion composes. -/
theorem ValidLeStructS.trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (first : ValidLeStructS M Γ A B) (second : ValidLeStructS M Γ B C) :
    ValidLeStructS M Γ A C :=
  fun e => .trans (first e) (second e)

end Valuations

/-! ## The facts of spines along the typing rules -/

namespace SpineFacts

variable {R : Rules Head}

/-- A term that is no spine of a constant has the facts vacuously. -/
theorem of_not_spine {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (notSpine : ∀ (c : DeclName) (args : List (Tm Head n)), t ≠ appSpine (.const c) args) :
    SpineFacts R M Γ t A :=
  fun e => absurd e (notSpine _ _)

/-- A term that is neither a constant nor an application is no spine of a
constant. -/
theorem of_ne {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (notConst : ∀ c : DeclName, t ≠ .const c) (notApp : ∀ f a : Tm Head n, t ≠ .app f a) :
    SpineFacts R M Γ t A :=
  of_not_spine fun c args e => by
    rcases Normalization.appSpine_const_cases c args with e' | ⟨f, a, e'⟩
    · exact notConst c (e.trans e')
    · exact notApp f a (e.trans e')

/-- **A declared constant starts a spine**: no arguments, and its declared type
included in itself. -/
theorem const (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0}
    {u : Head} (declared : R.constantType name = some type)
    (validType : ValidTmS M Γ (liftClosed type) (.head u)) (hu : M.rules.isUniverse u) :
    SpineFacts R M Γ (.const name) (liftClosed type) := by
  intro c args T e declared' m r ξ σ σ' ς eq
  obtain ⟨rfl, rfl⟩ := appSpine_const_injective (as := []) e
  obtain rfl := Option.some.inj (declared.symm.trans declared')
  refine .inl ?_
  have related : (universeAt M (M.levels.level u) ξ).rel
      (Presentation.subst σ (liftClosed type)) (Presentation.subst σ' (liftClosed type)) :=
    (ValidTmS.universe validType hu eq).1
  rw [subst_liftClosed, subst_liftClosed] at related
  rw [subst_liftClosed]
  exact SLe.of_universe laws.value related

/-- **An application extends a spine.** -/
theorem app (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n}
    {B : Tm Head (n + 1)} (facts : SpineFacts R M Γ g (.pi A B))
    (validA : ValidTmS M Γ a A) : SpineFacts R M Γ (.app g a) (inst0 a B) := by
  intro c args T e declared m r ξ σ σ' ς eq
  obtain ⟨init, rfl, rfl⟩ := appSpine_const_eq_app e.symm
  have valid : ∀ {P : Pack M.value m}, DenS M.value ξ (Presentation.subst σ A) P →
      P.Val (Presentation.subst σ a) ∧
        (P.real (Presentation.subst σ a)).mem (Presentation.subst ς a) := fun den =>
    ⟨den.refl_left laws.value (validA.2 eq den).1, (validA.2 eq den).2⟩
  rw [subst_inst0, List.map_append, List.map_append]
  rcases facts rfl declared eq with h | t
  · exact SpineOK.app laws h valid
  · obtain ⟨P, hP⟩ := t.total_interp
    obtain ⟨Q, rfl, iQ⟩ := (DenS.facts laws.value).piPack hP .refl
    exact .inr (total_cod laws t .refl iQ.dom_id (valid iQ.dom_id).1)

/-- **The facts pass along structural inclusion** of the type. -/
theorem below (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (facts : SpineFacts R M Γ t A) (le : ValidLeStructS M Γ A B) : SpineFacts R M Γ t B := by
  intro c args T e declared m r ξ σ σ' ς eq
  rcases facts e declared eq with h | t
  · exact .inl (h.mono (le eq))
  · exact .inr ((le eq).total laws t)

end SpineFacts

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
