import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallAbstraction

/-!
# Neutral spines over closed arrow types

In a context where every variable has a closed arrow type `d₁ → … → dₖ → r` over a base result
(a universe or a sort), and every declared constant too, an η-long neutral term is a head applied
to normal arguments, at the type that remains of its head's arrow (`spine_view`): projections are
impossible, since no closed arrow type is a dependent pair type.

This is the inversion that reads η-long terms over translated telescopes back as second-order
terms (`ContextualDependentFibreAdequacy`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFibre

open CategoryTheory Interface Interface.Translation
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Closed arrow types -/

/-- The closed arrow type `d₁ → … → dₖ → r`. -/
def arrows : List (Tm Head 0) → Tm Head 0 → Tm Head 0
  | [], r => r
  | d :: ds, r => BindingSignatureEmbedding.closedArrow d (arrows ds r)

theorem arrows_append : ∀ (xs ys : List (Tm Head 0)) (r : Tm Head 0),
    arrows (xs ++ ys) r = arrows xs (arrows ys r)
  | [], _, _ => rfl
  | x :: xs, ys, r => by
      show BindingSignatureEmbedding.closedArrow x (arrows (xs ++ ys) r) = _
      rw [arrows_append xs ys r]
      rfl

theorem liftClosed_injective {n : Nat} {t t' : Tm Head 0}
    (same : (liftClosed t : Tm Head n) = liftClosed t') : t = t' :=
  rename_injective (fun a => a.elim0) same

section Signature

variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)

theorem argumentsType_arrows : ∀ (as : List (List sig.Srt × sig.Srt)) (r : Tm Head 0),
    BindingSignatureEmbedding.argumentsType names as r =
      arrows (as.map fun a => BindingSignatureEmbedding.bindingType names a.1 a.2) r
  | [], _ => rfl
  | (bound, s) :: as, r => by
      show BindingSignatureEmbedding.closedArrow _ (BindingSignatureEmbedding.argumentsType names as r) = _
      rw [argumentsType_arrows as r]
      rfl

theorem telescopeType_arrows : ∀ (P : List sig.Srt) (r : Tm Head 0),
    BindingSignatureEmbedding.telescopeType names P r =
      arrows (P.reverse.map fun p => BindingSignatureEmbedding.sortType names p) r
  | [], _ => rfl
  | p :: P, r => by
      show BindingSignatureEmbedding.telescopeType names P
        (BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names p) r) = _
      rw [telescopeType_arrows P, List.reverse_cons, List.map_append, arrows_append]
      rfl

/-- A base result: a universe or a sort. -/
def BaseResult (r : Tm Head 0) : Prop :=
  (∃ u, S.R.isUniverse u ∧ r = .head u) ∨ ∃ s, r = BindingSignatureEmbedding.sortType names s

variable (facts : FormFacts S.R S.roles) (rigid : ∀ name, S.roles name = .rigid)
include facts rigid

/-- A base result is not a dependent function or pair type. -/
theorem BaseResult.base {r : Tm Head 0} (base : BaseResult (S := S) names r) {n : Nat}
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) : Base S.R Γ (liftClosed r) := by
  rcases base with ⟨u, _, rfl⟩ | ⟨s, rfl⟩
  · exact ⟨fun _ _ e => TypeEq.pi_ne_head facts formed e.symm,
      fun _ _ e => TypeEq.sigma_ne_head facts formed e.symm⟩
  · exact sort_base facts rigid names formed s

/-- A closed arrow type with a base result is a dependent function type only when it has a
domain. -/
theorem arrows_pi {ds : List (Tm Head 0)} {r : Tm Head 0} (base : BaseResult (S := S) names r)
    {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n} {B : Tm Head (n + 1)}
    (equal : TypeEq S.R Γ (liftClosed (arrows ds r)) (.pi A B)) :
    ∃ d rest, ds = d :: rest ∧ TypeEq S.R Γ (liftClosed d) A ∧
      TypeEq S.R (.snoc Γ (liftClosed d)) (liftClosed (arrows rest r)) B := by
  cases ds with
  | nil => exact absurd equal ((base.base names facts rigid formed).1 A B)
  | cons d rest =>
      have lifted : (liftClosed (arrows (d :: rest) r) : Tm Head n) =
          .pi (liftClosed d) (liftClosed (arrows rest r)) :=
        BindingSignatureEmbedding.liftClosed_closedArrow d (arrows rest r)
      rw [lifted] at equal
      exact ⟨d, rest, rfl, TypeEq.pi_injective facts equal formed⟩

/-- A closed arrow type with a base result is never a dependent pair type. -/
theorem arrows_not_sigma {ds : List (Tm Head 0)} {r : Tm Head 0} (base : BaseResult (S := S) names r)
    {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n} {B : Tm Head (n + 1)} :
    ¬ TypeEq S.R Γ (liftClosed (arrows ds r)) (.sigma A B) := by
  intro equal
  cases ds with
  | nil => exact (base.base names facts rigid formed).2 A B equal
  | cons d rest =>
      have lifted : (liftClosed (arrows (d :: rest) r) : Tm Head n) =
          .pi (liftClosed d) (liftClosed (arrows rest r)) :=
        BindingSignatureEmbedding.liftClosed_closedArrow d (arrows rest r)
      rw [lifted] at equal
      exact TypeEq.pi_ne_sigma facts formed equal

omit facts rigid

/-! ## The view of a neutral spine -/

/-- Every variable has a closed arrow type with a base result. -/
def ArrowContext {n : Nat} (Γ : Ctx Head n) : Prop :=
  ∀ j, ∃ ds r, BaseResult (S := S) names r ∧ Ctx.lookup Γ j = liftClosed (arrows ds r)

/-- Every declared constant has a closed arrow type with a base result. -/
def ArrowConstants : Prop :=
  ∀ {c : DeclName} {T : Tm Head 0}, S.R.constantType c = some T →
    ∃ ds r, BaseResult (S := S) names r ∧ T = arrows ds r

/-- `h` is a head of closed arrow type `ds → r`. -/
def HeadOf {n : Nat} (Γ : Ctx Head n) (h : Tm Head n) (ds : List (Tm Head 0)) (r : Tm Head 0) :
    Prop :=
  BaseResult (S := S) names r ∧
    ((∃ j, h = .var j ∧ Ctx.lookup Γ j = liftClosed (arrows ds r)) ∨
      ∃ c, h = .const c ∧ S.R.constantType c = some (arrows ds r))

/-- What the view of a neutral spine gives. -/
def SpineViewAt : LongStatement Head → Prop
  | .spine Γ t U => CtxFormed S.R Γ → ArrowContext (S := S) names Γ →
      ∃ (h : Tm _ _) (args : List (Tm _ _)) (ds₁ ds₂ : List (Tm Head 0)) (r : Tm Head 0),
        t = appSpine h args ∧ HeadOf (S := S) names Γ h (ds₁ ++ ds₂) r ∧
        List.Forall₂ (fun a d => Long S.R S.roles (.term Γ a (liftClosed d))) args ds₁ ∧
        TypeEq S.R Γ U (liftClosed (arrows ds₂ r))
  | _ => True

theorem forall₂_concat {α β : Type} {Rel : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {x : α} {y : β}, List.Forall₂ Rel xs ys → Rel x y →
      List.Forall₂ Rel (xs ++ [x]) (ys ++ [y])
  | [], [], _, _, .nil, related => .cons related .nil
  | _ :: _, _ :: _, _, _, .cons head tail, related => .cons head (forall₂_concat tail related)

variable (facts : FormFacts S.R S.roles) (rigid : ∀ name, S.roles name = .rigid)
  (constants : ArrowConstants (S := S) names)
include facts rigid constants

/-- **The view of a neutral spine** over closed arrow types: a head applied to normal arguments
at its domains, with the remaining arrow as its type. -/
theorem spine_view {st : LongStatement Head} (long : Long S.R S.roles st) :
    SpineViewAt (S := S) names st := by
  induction long with
  | @var n Γ U j e =>
      intro _ context
      obtain ⟨ds, r, base, lookup⟩ := context j
      exact ⟨.var j, [], [], ds, r, rfl, ⟨base, .inl ⟨j, rfl, lookup⟩⟩, .nil, by rw [← lookup]; exact e⟩
  | @const n Γ U c type _ declared _ e =>
      intro _ _
      obtain ⟨ds, r, base, rfl⟩ := constants declared
      exact ⟨.const c, [], [], ds, r, rfl, ⟨base, .inr ⟨c, rfl, declared⟩⟩, .nil, e⟩
  | @app n Γ f a U F A B _ eF la eU ihf _ =>
      intro formed context
      obtain ⟨h, args, ds₁, ds₂, r, rfl, head, related, eF'⟩ := ihf formed context
      obtain ⟨d, rest, rfl, eA, eB⟩ :=
        arrows_pi names facts rigid head.1 formed (TypeEq.trans S.levels eF'.symm eF)
      have ta : Typed S.R Γ a (liftClosed d) := Typed.convType la.typed eA.symm
      have la' : Long S.R S.roles (.term Γ a (liftClosed d)) := la.convType S.levels eA.symm
      have eInst : TypeEq S.R Γ (inst0 a B) (liftClosed (arrows rest r)) := by
        have moved := TypeEq.instantiate eB ta
        rw [inst0, subst_liftClosed] at moved
        exact moved.symm
      refine ⟨h, args ++ [a], ds₁ ++ [d], rest, r, ?_, ?_, forall₂_concat related la',
        TypeEq.trans S.levels eU eInst⟩
      · rw [appSpine_append]
        rfl
      · rw [List.append_assoc]
        exact head
  | @fst n Γ p U P A B _ eP _ ihp =>
      intro formed context
      obtain ⟨_, _, _, ds₂, r, _, head, _, eP'⟩ := ihp formed context
      exact absurd (TypeEq.trans S.levels eP'.symm eP) (arrows_not_sigma names facts rigid head.1 formed)
  | @snd n Γ p U P A B _ eP _ ihp =>
      intro formed context
      obtain ⟨_, _, _, ds₂, r, _, head, _, eP'⟩ := ihp formed context
      exact absurd (TypeEq.trans S.levels eP'.symm eP) (arrows_not_sigma names facts rigid head.1 formed)
  | _ => trivial

end Signature

end ContextualDependentFibre
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
