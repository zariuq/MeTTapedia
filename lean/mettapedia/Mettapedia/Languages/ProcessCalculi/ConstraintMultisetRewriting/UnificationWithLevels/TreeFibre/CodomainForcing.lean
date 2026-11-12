import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopeConsequence

/-!
# Unknowns at codomain positions: what a type of a universe forces of them

The narrowing of flex–rigid equations reads every unknown of the rigid side along domains (`HoldsVar`): an instance of
the side that is a type of `U_u` sends each such unknown to a type equal to one of `U_u`. Here the codomain of a
function type that does not use its argument is read too (`HoldsAt`).

* **Normal forms come back through a weakening** (`strengthen_normal`): a normal type of `Γ` whose weakening is a type
  of `U_u` under one more declaration is a type of `U_u` over `Γ`. This is the tree's typing reflection for normal
  terms through an inclusion (`normal_typing_reflects`), at the weakening.
* **The codomain case** (`small_codomain`): when a type of `U_u` is equal to `Π (_ : A). C`, with `C` a type that
  does not mention the argument, `C` is equal to a type of `U_u`. The codomain of the small Π type is equal, under its
  domain, to the weakening of `C`'s normal form; that weakening is a type of `U_u` there, and comes back.
* **What a type of a universe forces** (`HoldsAt.small`): for a normal type `t` of the store's telescope and a typed
  substitution `σ`, a type of `U_u` equal to `σ t` makes `σ y` equal to a type of `U_u` for every `y` at a type
  position of `t`, codomains included.
* **Normal subterms** (`normal_pi_domain`, `normal_pi_codomain`, `normal_of_rename`, ...): no step of a subterm, so no
  step of the whole.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentUniverseInjective
open ContextualDependentNormalChecking ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Type positions, codomains included -/

/-- **`y` occurs at a type position of `t`**: the code itself, along a domain, along the codomain of a function type
that does not use its argument, along the first component of a pair type, or as the carrier of an identity type. -/
inductive HoldsAt {n : Nat} (y : Fin n) : Tm Head n → Prop where
  | here : HoldsAt y (.var y)
  | piDomain {A : Tm Head n} {B : Tm Head (n + 1)} : HoldsAt y A → HoldsAt y (.pi A B)
  | piCodomain {A B : Tm Head n} : HoldsAt y B → HoldsAt y (.pi A (Presentation.rename wk B))
  | sigmaFirst {A : Tm Head n} {B : Tm Head (n + 1)} : HoldsAt y A → HoldsAt y (.sigma A B)
  | id {A a b : Tm Head n} : HoldsAt y A → HoldsAt y (.id A a b)

/-- A position read along domains is a type position. -/
theorem HoldsAt.of_holdsVar {n : Nat} {y : Fin n} {t : Tm Head n} (holds : HoldsVar (Head := Head) y t) :
    HoldsAt y t := by
  induction holds with
  | here => exact .here
  | piDomain _ ih => exact .piDomain ih
  | sigmaFirst _ ih => exact .sigmaFirst ih
  | id _ ih => exact .id ih

/-! ## Normal subterms -/

section Normal

variable {S : Setting Head L}

theorem normal_pi_domain {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (normal : Normal (S := S) (.pi A B)) :
    Normal (S := S) A :=
  fun _ step => normal _ (.congPiDom step)

theorem normal_pi_codomain {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (normal : Normal (S := S) (.pi A B)) :
    Normal (S := S) B :=
  fun _ step => normal _ (.congPiCod step)

theorem normal_sigma_domain {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)}
    (normal : Normal (S := S) (.sigma A B)) : Normal (S := S) A :=
  fun _ step => normal _ (.congSigmaDom step)

theorem normal_id_type {n : Nat} {A a b : Tm Head n} (normal : Normal (S := S) (.id A a b)) : Normal (S := S) A :=
  fun _ step => normal _ (.congIdTy step)

theorem normal_of_rename {n m : Nat} {ρ : Ren n m} {B : Tm Head n} (normal : Normal (S := S) (Presentation.rename ρ B)) :
    Normal (S := S) B :=
  fun _ step => normal _ (StepCore.renameTerms step ρ)

end Normal

/-! ## Normal forms come back through a weakening -/

section Strengthen

variable {S : Setting Head L}

/-- **The weakening, as an inclusion of telescopes.** -/
def weakInclusion {n : Nat} (Γ : Ctx Head n) (formed : CtxFormed S.R Γ) (A : Tm Head n)
    (formedA : CtxFormed S.R (.snoc Γ A)) :
    Inclusion (⟨n, Γ, formed⟩ : Context S.R) (⟨n + 1, .snoc Γ A, formedA⟩ : Context S.R) where
  forward := wk
  injective := Fin.succ_injective _
  typed := by
    intro i
    have t := Derivable.var (R := S.R) (Γ := .snoc Γ A) i.succ
    rw [Ctx.lookup_snoc_succ] at t
    change Typed S.R (.snoc Γ A) (.var (wk i)) (Presentation.subst (renSub wk) (Ctx.lookup Γ i))
    rw [subst_renSub]
    exact t

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **A normal term whose weakening is a type of a universe is one already.** -/
theorem strengthen_normal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n}
    (formedA : CtxFormed S.R (.snoc Γ A)) {u : Head} (hu : S.R.isUniverse u) {N : Tm Head n}
    (normal : Normal (S := S) (Presentation.rename wk N))
    (typed : Typed S.R (.snoc Γ A) (Presentation.rename wk N) (.head u)) : Typed S.R Γ N (.head u) := by
  have isU : IsType S.R Γ (.head u) := IsType.head_of_universe hu
  obtain ⟨w, hw, tw⟩ := isU
  exact ContextualDependentCheckingReplay.normal_typing_reflects facts algebra headTypingUnique complete roots heads
    declared (ContextualDependentScopeConsequence.root_reflection rigid) (weakInclusion Γ formed A formedA)
    (CtxRen.wk Γ A) ⟨.head u, w, hw, tw⟩ N typed normal

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **The codomain case**: a type of `U_u` equal to `Π (_ : A). C`, with `C` a type of the outer telescope, makes `C`
equal to a type of `U_u`. -/
theorem small_codomain {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed S.R Δ) {u v : Head} (hu : S.R.isUniverse u)
    (hv : S.R.isUniverse v) {s A C : Tm Head m} (ts : Typed S.R Δ s (.head u)) (tC : Typed S.R Δ C (.head v))
    (equal : TypeEq S.R Δ s (.pi A (Presentation.rename wk C))) :
    ∃ small, Typed S.R Δ small (.head u) ∧ TypeEq S.R Δ small C := by
  obtain ⟨A', B', _, _, tB', eB'⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
  have formedA' : CtxFormed S.R (.snoc Δ A') := by
    obtain ⟨k, hk, tA'⟩ := (show IsType S.R Δ A' from ⟨u, hu, by assumption⟩)
    exact formed.snoc ⟨k, hk, tA'⟩
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨v, hv, tC⟩
  obtain ⟨_, eN⟩ := atN hv tC
  have lN' : Long S.R S.roles (.type (.snoc Δ A') (Presentation.rename wk N)) :=
    Long.rename facts lN (CtxRen.wk Δ A') formed formedA'
  have eN' : Equal S.R (.snoc Δ A') (Presentation.rename wk C) (Presentation.rename wk N) (.head v) :=
    eN.rename (CtxRen.wk Δ A')
  have tN' : Typed S.R (.snoc Δ A') (Presentation.rename wk N) (.head u) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedA' hu tB'
      (TypeEq.trans S.levels eB' ⟨v, hv, eN'⟩) lN'
  have tN : Typed S.R Δ N (.head u) :=
    strengthen_normal facts roots heads algebra rigid complete headTypingUnique declared formed formedA' hu
      (long_type_normal rigid lN') tN'
  exact ⟨N, tN, ⟨v, hv, eN.symm⟩⟩

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **What a type of a universe forces at the type positions of a normal type**, codomains included. -/
theorem HoldsAt.small {n : Nat} {y : Fin n} {t : Tm Head n} (holds : HoldsAt (Head := Head) y t) :
    ∀ {Θ : Ctx Head n}, CtxFormed S.R Θ → ∀ {w : Head}, S.R.isUniverse w → Typed S.R Θ t (.head w) →
      Normal (S := S) t →
      ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ → ∀ {u : Head}, S.R.isUniverse u → ∀ (σ : Sub Head n m),
        SubstMor S.R Θ Δ σ → ∀ {s : Tm Head m}, Typed S.R Δ s (.head u) → TypeEq S.R Δ s (Presentation.subst σ t) →
          ∃ small, Typed S.R Δ small (.head u) ∧ TypeEq S.R Δ small (σ y) := by
  induction holds with
  | here =>
      intro Θ _ _ _ _ _ m Δ _ u _ σ _ s ts equal
      exact ⟨s, ts, equal⟩
  | @piDomain A B _ ih =>
      intro Θ formedΘ w hw tt normal m Δ formed u hu σ typedσ s ts equal
      have generation : GenerationAt S.R Θ (.pi A B) (.head w) := Typed.generation tt
      obtain ⟨u₁, _, _, tA, hu₁, _, _, _, _⟩ := generation
      obtain ⟨_, _, tA', eA', _, _⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      exact ih formedΘ hu₁ tA (normal_pi_domain normal) formed hu σ typedσ tA' eA'
  | @piCodomain A B _ ih =>
      intro Θ formedΘ w hw tt normal m Δ formed u hu σ typedσ s ts equal
      have generation : GenerationAt S.R Θ (.pi A (Presentation.rename wk B)) (.head w) := Typed.generation tt
      obtain ⟨u₁, u₂, _, tA, _, tB, hu₂, _, _⟩ := generation
      have formedΘA : CtxFormed S.R (.snoc Θ A) := formedΘ.snoc ⟨u₁, by assumption, tA⟩
      have normalB' : Normal (S := S) (Presentation.rename wk B) := normal_pi_codomain normal
      have tB₀ : Typed S.R Θ B (.head u₂) :=
        strengthen_normal facts roots heads algebra rigid complete headTypingUnique declared formedΘ formedΘA hu₂
          normalB' tB
      have tσB : Typed S.R Δ (Presentation.subst σ B) (.head u₂) := tB₀.substitute typedσ
      have equal' : TypeEq S.R Δ s (.pi (Presentation.subst σ A) (Presentation.rename wk (Presentation.subst σ B))) := by
        have e := equal
        change TypeEq S.R Δ s (.pi (Presentation.subst σ A)
          (Presentation.subst (liftSub σ) (Presentation.rename wk B))) at e
        rw [subst_liftSub_wk] at e
        exact e
      obtain ⟨N, tN, eN⟩ := small_codomain facts roots heads algebra rigid complete headTypingUnique declared formed hu
        hu₂ ts tσB equal'
      exact ih formedΘ hu₂ tB₀ (normal_of_rename normalB') formed hu σ typedσ tN eN
  | @sigmaFirst A B _ ih =>
      intro Θ formedΘ w hw tt normal m Δ formed u hu σ typedσ s ts equal
      have generation : GenerationAt S.R Θ (.sigma A B) (.head w) := Typed.generation tt
      obtain ⟨u₁, _, _, tA, hu₁, _, _, _, _⟩ := generation
      obtain ⟨_, _, tA', eA', _, _⟩ := small_sigma facts roots heads algebra rigid complete formed hu ts equal
      exact ih formedΘ hu₁ tA (normal_sigma_domain normal) formed hu σ typedσ tA' eA'
  | @id A a b _ ih =>
      intro Θ formedΘ w hw tt normal m Δ formed u hu σ typedσ s ts equal
      have generation : GenerationAt S.R Θ (.id A a b) (.head w) := Typed.generation tt
      obtain ⟨u₁, tA, hu₁, _, _, _⟩ := generation
      obtain ⟨_, tA', eA'⟩ := small_id facts roots heads algebra rigid complete formed hu ts equal
      exact ih formedΘ hu₁ tA (normal_id_type normal) formed hu σ typedσ tA' eA'

end Strengthen

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
