import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerSyntaxEval

/-!
# Typed syntax against a true inductive family: injectivity, and equality of proofs

**The type former of typed expressions is injective, at every index**: `exp x ≡ exp y` gives
`x ≡ y` at `ty`, for arbitrary, possibly open, `x` and `y` (`exp_injective`). The family is
`exp t = Σ (r : raw). typed r t`; at the bound variable `r` the typing relation is stuck, so the
codomains `typed r x` and `typed r y` are neutral types, and equal neutral spines of `typed` have
equal arguments by the completeness of the algorithmic equality. In this respect the encoding behaves
like an inductive family, and unlike the recursive family `vec`, whose type former is not injective at
length zero.

The proof inverts the algorithmic equality: the injectivity of dependent pair types gives the
codomains equal in the context extended by `r : raw`; completeness turns that equality into an
algorithmic comparison of the two neutral spines `typed r x` and `typed r y`; its last argument is
compared at the declared domain `ty` of `typed`; soundness and the substitution of a closed
expression for `r` give `x ≡ y`.

**Two typing proofs of one untyped expression give elements equal in the identity type**
(`same_raw_propositionally_equal`): `(rnum 0, p)` and `(rnum 0, q)`, for proof variables
`p q : unit`, are not equal by conversion (`same_raw_not_equal`), and an identity proof between them
is built by induction on `p` and on `q` with the unit type's recursor. A true inductive family has no
proof component, so there the two would be one element.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt unitRec unitCtors U0 numC zeroC unitC ttC unitRecC TowerLike)

namespace TowerSyntaxModel

variable (lv : LevelExpr Nat)

/-! ## Inverting the algorithmic equality of the package -/

section Inversion

variable {n : Nat} {Γ : Ctx Tower.Head n}

theorem alg_terms_inv {t u A : Tm Tower.Head n} (h : Algorithmic (rules lv) roles (.terms Γ t u A)) :
    ∃ A' t' u', RedTy (rules lv) roles Γ A A' ∧ RedTm (rules lv) roles Γ t t' A' ∧
      RedTm (rules lv) roles Γ u u' A' ∧ Algorithmic (rules lv) roles (.termsW Γ t' u' A') := by
  cases h with
  | terms rA _ rt ru w => exact ⟨_, _, _, rA, rt, ru, w⟩

theorem alg_spinesW_inv {t u U' : Tm Tower.Head n} (h : Algorithmic (rules lv) roles (.spinesW Γ t u U')) :
    ∃ U, Algorithmic (rules lv) roles (.spines Γ t u U) ∧ RedTy (rules lv) roles Γ U U' := by
  cases h with
  | spinesW s red _ => exact ⟨_, s, red⟩

theorem alg_spines_const_inv {c c' : DeclName} {U : Tm Tower.Head n}
    (h : Algorithmic (rules lv) roles (.spines Γ (.const c) (.const c') U)) :
    c = c' ∧ ∃ type, (rules lv).constantType c = some type ∧ U = liftClosed type := by
  cases h with
  | const declared _ => exact ⟨rfl, _, declared, rfl⟩

/-- Peel the last argument off two compared application spines. -/
theorem alg_peel {f g a b U' : Tm Tower.Head n}
    (h : Algorithmic (rules lv) roles (.spinesW Γ (.app f a) (.app g b) U')) :
    ∃ (A : Tm Tower.Head n) (B : Tm Tower.Head (n + 1)),
      Algorithmic (rules lv) roles (.spinesW Γ f g (.pi A B)) ∧ Algorithmic (rules lv) roles (.terms Γ a b A) ∧
        RedTy (rules lv) roles Γ (inst0 a B) U' := by
  cases h with
  | spinesW s red _ =>
      cases s with
      | app hf ha => exact ⟨_, _, hf, ha, red⟩

/-- Two applications compared at a universe are compared as spines. -/
theorem alg_termsW_univ_app {f g a b : Tm Tower.Head n} {h : Tower.Head}
    (w : Algorithmic (rules lv) roles (.termsW Γ (.app f a) (.app g b) (.head h))) :
    ∃ U, Algorithmic (rules lv) roles (.spinesW Γ (.app f a) (.app g b) U) := by
  cases w with
  | univ _ _ _ w' =>
      cases w' with
      | neutralTypes _ _ _ s => exact ⟨_, s⟩
  | spine _ _ _ _ _ s => exact ⟨_, s⟩

end Inversion

/-! ## Injectivity -/

section Injectivity

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- The typing relation is stuck on a variable expression. -/
theorem typing_var_neutral (t : Tm Tower.Head n) (i : Fin n) : Neutral roles (typingC (.var i) t) :=
  Neutral.stuck_single (before := []) (after := [t]) roles_typing rfl (.var i)

/-- **The type former of typed expressions is injective, at every index**: `exp x ≡ exp y` gives
`x ≡ y` at the object types, for arbitrary, possibly open, `x` and `y`. -/
theorem exp_injective (formed : CtxFormed (rules lv) Γ) {x y : Tm Tower.Head n}
    (equal : TypeEq (rules lv) Γ (expC x) (expC y)) : Equal (rules lv) Γ x y tyC := by
  obtain ⟨-, u, _, eB⟩ := TypeEq.sigma_injective (facts lv) equal formed
  have formedR : CtxFormed (rules lv) (.snoc Γ rawC) :=
    .snoc formed ⟨_, LevelTower.IsUniverse.sort _, raw_typed lv⟩
  obtain ⟨A', t', u', rA, rt, ru, w⟩ := alg_terms_inv lv (complete lv formedR eB)
  obtain rfl := WhRed.eq_of_whnf (S := setting lv fun _ => 0) (head_whnf (shape lv) u) rA.red
  obtain rfl := WhRed.eq_of_whnf (S := setting lv fun _ => 0)
    ((typing_var_neutral (Presentation.rename wk x) 0).whnf (shape lv)) rt.red
  obtain rfl := WhRed.eq_of_whnf (S := setting lv fun _ => 0)
    ((typing_var_neutral (Presentation.rename wk y) 0).whnf (shape lv)) ru.red
  obtain ⟨U, spines⟩ := alg_termsW_univ_app lv w
  obtain ⟨A₂, B₂, h₂, args, _⟩ := alg_peel lv spines
  obtain ⟨A₁, B₁, h₁, _, red₁⟩ := alg_peel lv h₂
  obtain ⟨U₁, s₁, r₁⟩ := alg_spinesW_inv lv h₁
  obtain ⟨-, type, declared, rfl⟩ := alg_spines_const_inv lv s₁
  have known : (rules lv).constantType typing = some typingType := rfl
  rw [known] at declared
  obtain rfl := Option.some.inj declared
  have lifted : (liftClosed typingType : Tm Tower.Head (n + 1)) = .pi rawC (.pi tyC U0) := rfl
  rw [lifted] at r₁
  have first := WhRed.eq_of_whnf (S := setting lv fun _ => 0) (pi_whnf (shape lv) _ _) r₁.red
  injection first with _ _ sameB₁
  subst sameB₁
  have opened : (inst0 (.var 0) (.pi tyC U0) : Tm Tower.Head (n + 1)) = .pi tyC U0 := rfl
  rw [opened] at red₁
  have second := WhRed.eq_of_whnf (S := setting lv fun _ => 0) (pi_whnf (shape lv) _ _) red₁.red
  injection second with _ sameA₂ _
  subst sameA₂
  obtain ⟨C, a, b, rC, ra, rb, _⟩ := alg_terms_inv lv args
  obtain rfl := WhRed.eq_of_whnf (S := setting lv fun _ => 0) (inductive_whnf (shape lv) roles_ty) rC.red
  have eq' : Equal (rules lv) (.snoc Γ rawC) (Presentation.rename wk x) (Presentation.rename wk y) tyC :=
    Algorithm.sound (S := setting lv fun _ => 0) (facts lv) (roots lv) (heads lv) (algebra lv) args.refines
      formedR ra.source rb.source
  have sub := Equal.substitute eq' (SubstMor.single ((rawD lv).rnum_app (zero_typed lv)))
  change Equal (rules lv) Γ (inst0 (rnumC zeroC) (Presentation.rename wk x))
    (inst0 (rnumC zeroC) (Presentation.rename wk y)) tyC at sub
  rwa [inst0_rename_wk, inst0_rename_wk] at sub

/-- **Negative example**: at two different closed indices the types differ, so injectivity is not
vacuous; the two expressions `lit 0 : exp tnum` and `blit true : exp tbool` live in different types. -/
theorem exp_tnum_tbool_differ (formed : CtxFormed (rules lv) Γ) :
    ¬ TypeEq (rules lv) Γ (expC tnumC) (expC tboolC) :=
  exp_tnum_ne_tbool lv formed

end Injectivity

/-! ## Two proofs of one untyped expression: equal in the identity type, not by conversion -/

section SameRaw

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- The unit type's recursor at a motive, a base case and a scrutinee. -/
theorem unitRec_app_typed {P d t : Tm Tower.Head n} (tP : Typed (rules lv) Γ P (.pi unitC (.head (.sort lv))))
    (td : Typed (rules lv) Γ d (.app P ttC)) (tt' : Typed (rules lv) Γ t unitC) :
    Typed (rules lv) Γ (unitRecC P d t) (.app P t) := by
  obtain ⟨w, hw, typed⟩ := (tw_rules lv).unitRecType_typed rfl rfl lv
  have tc : Typed (rules lv) Γ (.const unitRec) (liftClosed (recType unit (.sort lv) unitCtors)) :=
    .const rfl typed hw
  have m₀ : SubstMor (rules lv) .nil Γ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (recTele unit (.sort lv) unitCtors) Γ
      (consSub t (consSub d (consSub P fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tP) td) tt'
  exact Typed.telescope_apply mor tc

/-- The expression `(rnum 0, x)`, for a proof `x` of `typed (rnum 0) tnum ≡ unit`. -/
abbrev zeroE {m : Nat} (x : Tm Tower.Head m) : Tm Tower.Head m := .pair (rnumC zeroC) x

theorem zeroE_typed {x : Tm Tower.Head n} (tx : Typed (rules lv) Γ x unitC) :
    Typed (rules lv) Γ (zeroE x) (expC tnumC) :=
  .pairIntro (exp_typed lv (tnum_typed lv)) (LevelTower.IsUniverse.sort _) ((rawD lv).rnum_app (zero_typed lv))
    (Typed.convType tx ⟨_, LevelTower.IsUniverse.sort _, (typing_rnum_tnum lv (zero_typed lv)).symm⟩)

/-- The motive of the inner induction, on the second proof: `λ y. Id (exp tnum) (rnum 0, tt) (rnum 0, y)`. -/
abbrev innerMotive : Tm Tower.Head 2 := .lam (.id (expC tnumC) (zeroE ttC) (zeroE (.var 0)))

/-- The motive of the outer induction, on the first proof: `λ x. Id (exp tnum) (rnum 0, x) (rnum 0, q)`. -/
abbrev outerMotive : Tm Tower.Head 2 := .lam (.id (expC tnumC) (zeroE (.var 0)) (zeroE (.var 1)))

/-- The proof: induction on the first proof, then on the second, ending in reflexivity. -/
abbrev sameRawProof : Tm Tower.Head 2 :=
  unitRecC outerMotive (unitRecC innerMotive (.refl (zeroE ttC)) (.var 0)) (.var 1)

/-- **Equal in the identity type**: the two expressions of `same_raw_not_equal`, with the same untyped
expression `rnum 0` and the two proof variables `p q : unit`, are propositionally equal, by induction on
`p` and on `q`. So two typing proofs of one untyped expression give elements that are equal in the
identity type and not by conversion. -/
theorem same_raw_propositionally_equal :
    Typed (rules lv) twoProofs sameRawProof
      (.id (expC tnumC) (.pair (rnumC zeroC) (.var 1)) (.pair (rnumC zeroC) (.var 0))) := by
  have tw := tw_rules lv
  have tMty : Typed (rules lv) twoProofs (.pi unitC (.head (.sort lv))) (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm (unit_typed lv) (LevelTower.IsUniverse.sort _) (.headType (tw.headTyping _))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
  have tExp : Typed (rules lv) (.snoc twoProofs unitC) (expC tnumC) U0 := exp_typed lv (tnum_typed lv)
  have tInnerBody : Typed (rules lv) (.snoc twoProofs unitC) (.id (expC tnumC) (zeroE ttC) (zeroE (.var 0)))
      (.head (.sort lv)) :=
    tw.lift (.idForm tExp (LevelTower.IsUniverse.sort _) (zeroE_typed lv (tt_typed lv)) (zeroE_typed lv (.var 0))) lv
  have tOuterBody : Typed (rules lv) (.snoc twoProofs unitC) (.id (expC tnumC) (zeroE (.var 0)) (zeroE (.var 1)))
      (.head (.sort lv)) :=
    tw.lift (.idForm tExp (LevelTower.IsUniverse.sort _) (zeroE_typed lv (.var 0)) (zeroE_typed lv (.var 1))) lv
  have tInner : Typed (rules lv) twoProofs innerMotive (.pi unitC (.head (.sort lv))) :=
    .lamIntro tMty (LevelTower.IsUniverse.sort _) tInnerBody
  have tOuter : Typed (rules lv) twoProofs outerMotive (.pi unitC (.head (.sort lv))) :=
    .lamIntro tMty (LevelTower.IsUniverse.sort _) tOuterBody
  -- the base: reflexivity at `(rnum 0, tt)`
  have tRefl : Typed (rules lv) twoProofs (.refl (zeroE ttC)) (.id (expC tnumC) (zeroE ttC) (zeroE ttC)) :=
    .reflIntro (zeroE_typed lv (tt_typed lv))
  have betaInnerTt : Equal (rules lv) twoProofs (.app innerMotive ttC)
      (.id (expC tnumC) (zeroE ttC) (zeroE ttC)) (.head (.sort lv)) :=
    .betaPi tMty (LevelTower.IsUniverse.sort _) tInnerBody (tt_typed lv)
  have tBase : Typed (rules lv) twoProofs (.refl (zeroE ttC)) (.app innerMotive ttC) :=
    Typed.convType tRefl ⟨_, LevelTower.IsUniverse.sort _, betaInnerTt.symm⟩
  -- the inner induction, on `q`
  have tInnerRec : Typed (rules lv) twoProofs (unitRecC innerMotive (.refl (zeroE ttC)) (.var 0))
      (.app innerMotive (.var 0)) :=
    unitRec_app_typed lv tInner tBase (.var 0)
  have betaInnerQ : Equal (rules lv) twoProofs (.app innerMotive (.var 0))
      (.id (expC tnumC) (zeroE ttC) (zeroE (.var 0))) (.head (.sort lv)) :=
    .betaPi tMty (LevelTower.IsUniverse.sort _) tInnerBody (.var 0)
  have betaOuterTt : Equal (rules lv) twoProofs (.app outerMotive ttC)
      (.id (expC tnumC) (zeroE ttC) (zeroE (.var 0))) (.head (.sort lv)) :=
    .betaPi tMty (LevelTower.IsUniverse.sort _) tOuterBody (tt_typed lv)
  have tBase₂ : Typed (rules lv) twoProofs (unitRecC innerMotive (.refl (zeroE ttC)) (.var 0))
      (.app outerMotive ttC) :=
    Typed.convType tInnerRec ⟨_, LevelTower.IsUniverse.sort _, .trans betaInnerQ betaOuterTt.symm⟩
  -- the outer induction, on `p`
  have tOuterRec : Typed (rules lv) twoProofs sameRawProof (.app outerMotive (.var 1)) :=
    unitRec_app_typed lv tOuter tBase₂ (.var 1)
  have betaOuterP : Equal (rules lv) twoProofs (.app outerMotive (.var 1))
      (.id (expC tnumC) (zeroE (.var 1)) (zeroE (.var 0))) (.head (.sort lv)) :=
    .betaPi tMty (LevelTower.IsUniverse.sort _) tOuterBody (.var 1)
  exact Typed.convType tOuterRec ⟨_, LevelTower.IsUniverse.sort _, betaOuterP⟩

end SameRaw

end TowerSyntaxModel

#print axioms TowerSyntaxModel.exp_injective
#print axioms TowerSyntaxModel.typing_var_neutral
#print axioms TowerSyntaxModel.same_raw_propositionally_equal

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
