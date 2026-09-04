import Mettapedia.Logic.HOL.Semantics.Extensionality
import Mathlib.Data.Fintype.Card

/-!
# Independent properties of Henkin models

This module names semantic properties of the Church-style HOL models without
using a product name as a mathematical classifier.  In particular, full
function spaces, extensionality, Hilbert choice, and Dedekind infinity remain
separate assumptions.

Excluded middle is recorded separately: propositions in this semantics are
interpreted in the ambient `Prop`, so every model validates formula-level
excluded middle when the ambient metatheory is classical.  It is therefore not
additional data carried by a Henkin model.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinModel

/-- Every ambient value belongs to its Henkin quantifier domain. -/
def FullDomains (M : HenkinModel.{u, v, w} Base Const) : Prop :=
  ∀ (τ : Ty Base) (x : Ty.denote M.Carrier τ), M.adm τ x

/-- Standard models have no Henkin-domain restriction. -/
theorem fullDomains_standard
    (Carrier : Base → Type (max (u + 1) w))
    (constDen : {τ : Ty Base} → Const τ → Ty.denote Carrier τ) :
    (HenkinModel.standard Carrier constDen).FullDomains := by
  intro _ _
  trivial

/-- A selected admissible inhabitant of every simple type. -/
structure InhabitedDomains (M : HenkinModel.{u, v, w} Base Const) where
  witness : (τ : Ty Base) → Ty.denote M.Carrier τ
  witness_admissible : ∀ τ, M.adm τ (witness τ)

/-- Propositional existence of an admissible inhabitant family. -/
def HasInhabitedDomains (M : HenkinModel.{u, v, w} Base Const) : Prop :=
  Nonempty M.InhabitedDomains

/-- A canonical ambient inhabitant of every simple type, given inhabitants of
the base carriers.  This is semantic data; it need not be denoted by syntax. -/
def defaultValue (M : HenkinModel.{u, v, w} Base Const)
    (baseWitness : (b : Base) → M.Carrier b) :
    (τ : Ty Base) → Ty.denote M.Carrier τ
  | .prop => .up True
  | .base b => baseWitness b
  | .arr _ τ => fun _ => M.defaultValue baseWitness τ

/-- Full domains turn ambient base inhabitants into admissible inhabitants at
every simple type. -/
def inhabitedDomains_of_fullDomains
    (M : HenkinModel.{u, v, w} Base Const) (hFull : M.FullDomains)
    (baseWitness : (b : Base) → M.Carrier b) : M.InhabitedDomains where
  witness := M.defaultValue baseWitness
  witness_admissible τ := hFull τ (M.defaultValue baseWitness τ)

/-- Formula-level excluded middle is valid under every admissible valuation. -/
def ValidatesExcludedMiddle (M : HenkinModel.{u, v, w} Base Const) : Prop :=
  ∀ {Γ : Ctx Base} (φ : Formula Const Γ) (ρ : M.Valuation Γ),
    M.ValuationAdmissible ρ → (M.denote (.or φ (.not φ)) ρ).down

/-- `Prop`-valued Henkin semantics validates excluded middle in a classical
ambient metatheory; this is not extra structure on a model. -/
theorem validatesExcludedMiddle (M : HenkinModel.{u, v, w} Base Const) :
    M.ValidatesExcludedMiddle := by
  classical
  intro Γ φ ρ _hρ
  change (M.denote φ ρ).down ∨ ¬ (M.denote φ ρ).down
  exact Classical.em _

/-- Under full domains, recursive Henkin equality coincides with ambient
equality at every simple type. -/
theorem eq_of_eqv_of_fullDomains (M : HenkinModel.{u, v, w} Base Const)
    (hFull : M.FullDomains) :
    ∀ {τ : Ty Base} {x y : Ty.denote M.Carrier τ}, M.Eqv τ x y → x = y
  | .prop, p, q, h => by
      apply ULift.down_injective
      exact propext h
  | .base _, _, _, h => h
  | .arr σ τ, f, g, h => by
      funext x
      exact eq_of_eqv_of_fullDomains M hFull (h x (hFull σ x))

/-- Full domains imply the argument-congruence property required by the
extensional derivation overlay. -/
theorem functionsRespectEqv_of_fullDomains
    (M : HenkinModel.{u, v, w} Base Const) (hFull : M.FullDomains) :
    M.FunctionsRespectEqv := by
  intro σ τ f x y hf hx _hy hxy
  have hxy' : x = y := eq_of_eqv_of_fullDomains M hFull hxy
  subst y
  exact M.eqv_refl (M.app_mem hf hx)

/-- The always-true predicate at a simple type. -/
def truePredicate (M : HenkinModel.{u, v, w} Base Const) (τ : Ty Base) :
    Ty.denote M.Carrier (τ ⇒ .prop) :=
  fun _ => .up True

/-- The always-true predicate is admissible because it is denoted by the closed
term `λx. ⊤`. -/
theorem truePredicate_admissible (M : HenkinModel.{u, v, w} Base Const)
    (τ : Ty Base) : M.adm (τ ⇒ .prop) (M.truePredicate τ) := by
  let t : Term Const [] (τ ⇒ .prop) := .lam .top
  let ρ : M.Valuation ([] : Ctx Base) := fun {_} v => nomatch v
  have hρ : M.ValuationAdmissible ρ := by
    intro _ v
    nomatch v
  have ht := M.denote_admissible (ρ := ρ) hρ t
  change M.adm (τ ⇒ .prop) (fun _ => .up True) at ht
  exact ht

/-- A semantic Hilbert-choice family.  `choose τ` is itself an admissible
function from admissible predicates on `τ` to values of `τ`, and it selects a
witness whenever the predicate has an admissible witness. -/
structure HilbertChoice (M : HenkinModel.{u, v, w} Base Const) where
  choose : (τ : Ty Base) → Ty.denote M.Carrier ((τ ⇒ .prop) ⇒ τ)
  choose_admissible : ∀ τ, M.adm ((τ ⇒ .prop) ⇒ τ) (choose τ)
  specified : ∀ (τ : Ty Base) (p : Ty.denote M.Carrier (τ ⇒ .prop)),
    M.adm (τ ⇒ .prop) p →
      (∃ x, M.adm τ x ∧ (p x).down) →
        (p (choose τ p)).down

/-- Propositional existence of a semantic Hilbert-choice family. -/
def HasHilbertChoice (M : HenkinModel.{u, v, w} Base Const) : Prop :=
  Nonempty M.HilbertChoice

namespace HilbertChoice

/-- A total admissible choice family supplies an admissible inhabitant at every
type by choosing from the always-true predicate. -/
def inhabitedDomains {M : HenkinModel.{u, v, w} Base Const}
    (choice : M.HilbertChoice) : M.InhabitedDomains where
  witness τ := choice.choose τ (M.truePredicate τ)
  witness_admissible τ :=
    M.app_mem (choice.choose_admissible τ) (M.truePredicate_admissible τ)

/-- Full, inhabited domains support the usual metatheoretic choice construction.
The full-domain premise is what admits the resulting choice function as a
Henkin value; inhabitance supplies its behavior when the predicate is empty. -/
noncomputable def ofFullInhabitedDomains
    {M : HenkinModel.{u, v, w} Base Const}
    (hFull : M.FullDomains) (domains : M.InhabitedDomains) : M.HilbertChoice := by
  classical
  refine
    { choose := fun τ p =>
        if h : ∃ x, M.adm τ x ∧ (p x).down then
          Classical.choose h
        else
          domains.witness τ
      choose_admissible := fun τ => hFull _ _
      specified := ?_ }
  intro τ p _hp h
  simp only [dif_pos h]
  exact (Classical.choose_spec h).2

end HilbertChoice

/-- Data witnessing Dedekind infinity of one distinguished base carrier. -/
structure DedekindInfinityWitness
    (M : HenkinModel.{u, v, w} Base Const) (b : Base) where
  successor : M.Carrier b → M.Carrier b
  successor_admissible : M.adm (.base b ⇒ .base b) successor
  successor_injective : Function.Injective successor
  omitted : M.Carrier b
  omitted_not_image : ∀ x, successor x ≠ omitted

/-- The omitted point of a base-carrier infinity witness is automatically in
the quantifier domain: base domains are full in every Henkin model here. -/
theorem DedekindInfinityWitness.omitted_admissible
    {M : HenkinModel.{u, v, w} Base Const} {b : Base}
    (witness : M.DedekindInfinityWitness b) :
    M.adm (.base b) witness.omitted :=
  M.base_mem b witness.omitted

/-- A base carrier is Dedekind-infinite when such a witness exists. -/
def HasDedekindInfiniteBase
    (M : HenkinModel.{u, v, w} Base Const) (b : Base) : Prop :=
  Nonempty (M.DedekindInfinityWitness b)

/-- No finite base carrier admits a Dedekind-infinity witness. -/
theorem not_hasDedekindInfiniteBase_of_finite
    (M : HenkinModel.{u, v, w} Base Const) (b : Base)
    [Finite (M.Carrier b)] : ¬ M.HasDedekindInfiniteBase b := by
  rintro ⟨witness⟩
  have hSurjective : Function.Surjective witness.successor :=
    Finite.surjective_of_injective witness.successor_injective
  obtain ⟨x, hx⟩ := hSurjective witness.omitted
  exact witness.omitted_not_image x hx

/-- The independent semantic assumptions traditionally combined by one common
classical HOL family: extensional application, Hilbert choice, and a selected
Dedekind-infinite base carrier.  Formula-level excluded middle is not a field,
because `validatesExcludedMiddle` holds for every model in this semantics. -/
structure ExtensionalChoiceInfinity
    (M : HenkinModel.{u, v, w} Base Const) (b : Base) where
  extensional : M.FunctionsRespectEqv
  choice : M.HilbertChoice
  infinity : M.DedekindInfinityWitness b

/-- Propositional existence of the combined property bundle. -/
def HasExtensionalChoiceInfinity
    (M : HenkinModel.{u, v, w} Base Const) (b : Base) : Prop :=
  Nonempty (M.ExtensionalChoiceInfinity b)

/-! ## Positive and negative semantic canaries -/

namespace ModelPropertyCanary

/-- Empty constant family used only to isolate model properties. -/
abbrev NoConstants (B : Type) : Ty B → Type := fun _ => Empty

abbrev LiftedEmpty := ULift.{1, 0} Empty
abbrev LiftedNat := ULift.{1, 0} Nat
abbrev LiftedBool := ULift.{1, 0} Bool

/-- A full standard model may still have an empty base carrier. -/
def emptyBaseModel : HenkinModel.{0, 0, 0} Unit (NoConstants Unit) :=
  HenkinModel.standard (fun _ => LiftedEmpty) (fun {_} c => nomatch c)

theorem emptyBaseModel_fullDomains : emptyBaseModel.FullDomains := by
  intro _ _
  trivial

/-- Negative canary: fullness of every existing domain element does not create
an inhabitant of an empty base carrier. -/
theorem emptyBaseModel_not_inhabitedDomains :
    ¬ emptyBaseModel.HasInhabitedDomains := by
  rintro ⟨domains⟩
  have witness : LiftedEmpty := domains.witness (.base ())
  exact nomatch witness.down

/-- A semantic Hilbert-choice family would in particular inhabit every simple
type, so the empty-base model cannot support one. -/
theorem emptyBaseModel_not_hilbertChoice :
    ¬ emptyBaseModel.HasHilbertChoice := by
  rintro ⟨choice⟩
  exact emptyBaseModel_not_inhabitedDomains
    ⟨choice.inhabitedDomains⟩

/-- Full domains do not entail inhabitance; the empty-base standard model is
an explicit counterexample. -/
theorem fullDomains_do_not_force_inhabitedDomains :
    emptyBaseModel.FullDomains ∧
      ¬ emptyBaseModel.HasInhabitedDomains :=
  ⟨emptyBaseModel_fullDomains, emptyBaseModel_not_inhabitedDomains⟩

/-- Full extensional domains, and therefore the formula-level classicality of
this semantics, do not entail Hilbert choice. -/
theorem fullDomains_do_not_force_hilbertChoice :
    emptyBaseModel.FullDomains ∧
      ¬ emptyBaseModel.HasHilbertChoice :=
  ⟨emptyBaseModel_fullDomains, emptyBaseModel_not_hilbertChoice⟩

/-- The standard one-base model with natural-number base carrier. -/
def naturalBaseModel : HenkinModel.{0, 0, 0} Unit (NoConstants Unit) :=
  HenkinModel.standard (fun _ => LiftedNat) (fun {_} c => nomatch c)

theorem naturalBaseModel_fullDomains : naturalBaseModel.FullDomains := by
  intro _ _
  trivial

def naturalBaseModel_inhabitedDomains : naturalBaseModel.InhabitedDomains :=
  naturalBaseModel.inhabitedDomains_of_fullDomains
    naturalBaseModel_fullDomains
    (fun _ => (ULift.up (0 : Nat) : LiftedNat))

noncomputable def naturalBaseModel_choice : naturalBaseModel.HilbertChoice :=
  HilbertChoice.ofFullInhabitedDomains naturalBaseModel_fullDomains
    naturalBaseModel_inhabitedDomains

def naturalBaseModel_infinity :
    naturalBaseModel.DedekindInfinityWitness () where
  successor := fun n : LiftedNat => ULift.up (Nat.succ n.down)
  successor_admissible := by trivial
  successor_injective := by
    intro (x : LiftedNat) (y : LiftedNat) h
    apply ULift.down_injective (α := Nat)
    exact Nat.succ_injective (congrArg ULift.down h)
  omitted := (ULift.up (0 : Nat) : LiftedNat)
  omitted_not_image := by
    intro x h
    have hDown := congrArg ULift.down h
    exact Nat.succ_ne_zero x.down hDown

/-- Positive canary: the standard natural-number base model realizes the
extensionality, choice, and infinity property bundle. -/
noncomputable def naturalBaseModel_extensionalChoiceInfinity :
    naturalBaseModel.ExtensionalChoiceInfinity () where
  extensional := naturalBaseModel.functionsRespectEqv_of_fullDomains
    naturalBaseModel_fullDomains
  choice := naturalBaseModel_choice
  infinity := naturalBaseModel_infinity

theorem naturalBaseModel_has_extensionalChoiceInfinity :
    naturalBaseModel.HasExtensionalChoiceInfinity () :=
  ⟨naturalBaseModel_extensionalChoiceInfinity⟩

/-- The standard one-base model with a finite Boolean base carrier. -/
def booleanBaseModel : HenkinModel.{0, 0, 0} Unit (NoConstants Unit) :=
  HenkinModel.standard (fun _ => LiftedBool) (fun {_} c => nomatch c)

theorem booleanBaseModel_fullDomains : booleanBaseModel.FullDomains := by
  intro _ _
  trivial

def booleanBaseModel_inhabitedDomains : booleanBaseModel.InhabitedDomains :=
  booleanBaseModel.inhabitedDomains_of_fullDomains
    booleanBaseModel_fullDomains
    (fun _ => (ULift.up false : LiftedBool))

noncomputable def booleanBaseModel_choice : booleanBaseModel.HilbertChoice :=
  HilbertChoice.ofFullInhabitedDomains booleanBaseModel_fullDomains
    booleanBaseModel_inhabitedDomains

/-- Negative canary: even full domains plus semantic Hilbert choice do not
force Dedekind infinity of a distinguished base carrier. -/
theorem booleanBaseModel_not_infinite :
    ¬ booleanBaseModel.HasDedekindInfiniteBase () := by
  letI : Finite (booleanBaseModel.Carrier ()) := by
    change Finite LiftedBool
    infer_instance
  exact booleanBaseModel.not_hasDedekindInfiniteBase_of_finite ()

/-- Full domains and semantic Hilbert choice do not entail infinity; the
finite Boolean base model is an explicit counterexample. -/
theorem fullDomains_and_choice_do_not_force_infinity :
    booleanBaseModel.FullDomains ∧
      booleanBaseModel.HasHilbertChoice ∧
        ¬ booleanBaseModel.HasDedekindInfiniteBase () :=
  ⟨booleanBaseModel_fullDomains, ⟨booleanBaseModel_choice⟩,
    booleanBaseModel_not_infinite⟩

end ModelPropertyCanary

end HenkinModel

end Mettapedia.Logic.HOL
