import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsLookup

/-!
# Head by the dependent eliminator, with a large motive

`head` on vectors of a successor length, written with the eliminator `vec-elim` and a motive
computed from the length:

`head A k v = vec-elim A (λ n _. below-step (λ _. A) n) tt (λ n a w ih. a) (succ k) v`,

where `below-step (λ _. A) zero ≡ unit` and `below-step (λ _. A) (succ n) ≡ A`. The case of the
empty vector returns the trivial `tt : unit`: the impossible case costs nothing and needs no
unification on indices.

`head_typed`: it has type `A`. `head_fst`: on an open vector `v : vec A (succ k)` it is equal to
the projection `fst v`. `head_pair`: `head A k (pair a w) ≡ a`.

Every program is a judgment in the context of its variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TowerVectorsModel TowerVectorsPrograms TowerVectorsLookup
open TowerNumbersModel (num zero succ u)

namespace TowerVectorsHead

variable (lv : LevelExpr Nat)

/-- The motive of head: `λ n _. below-step (λ _. A) n`, which is `unit` at zero and `A` at a
successor. -/
def headMotive {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.lam (belowStepC (.lam (Presentation.rename wk (Presentation.rename wk
    (Presentation.rename wk A)))) (.var 1)))

/-- The method of head for `pair`: `λ n a w ih. a`. -/
def headMethod {n : Nat} : Tm Tower.Head n := .lam (.lam (.lam (.lam (.var 2))))

/-- **Head, by the eliminator.** -/
def headTm {n : Nat} (A k v : Tm Tower.Head n) : Tm Tower.Head n :=
  vecElimC A (headMotive A) ttC headMethod (succC k) v

/-- The context of head's variables: `A : U0, k : num, v : vec A (succ k)`. -/
abbrev headCtx : Ctx Tower.Head 3 :=
  .snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (succC (.var 0)))

theorem headCtx_formed : CtxFormed (rules lv) headCtx := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 1) U0 := .var 1
  have tk : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 0) numC := .var 0
  exact .snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA (D.succ_typed tk)⟩

/-- The constant family `λ _. A` over the numbers. -/
theorem constFamily_typed {n : Nat} {Γ : Ctx Tower.Head n} {A' : Tm Tower.Head (n + 1)}
    (tA : Typed (rules lv) (.snoc Γ numC) A' U0) : Typed (rules lv) Γ (.lam A') (.pi numC U0) :=
  .lamIntro (family_typed (towerLike_rules lv) rfl) ((towerLike_rules lv).isUniverse _) tA

/-- The motive at its type. -/
theorem headMotive_typed : Typed (rules lv) headCtx (headMotive (.var 2)) (vecMotive (.var 2)) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc (.snoc (.snoc headCtx numC) (vecC (.var 3) (.var 0))) numC) (.var 5)
      U0 := .var 5
  have tk : Typed (rules lv) (.snoc (.snoc headCtx numC) (vecC (.var 3) (.var 0))) (.var 1) numC := .var 1
  have tBody : Typed (rules lv) (.snoc (.snoc headCtx numC) (vecC (.var 3) (.var 0)))
      (belowStepC (.lam (.var 5)) (.var 1)) U0 := belowStep_typed lv (constFamily_typed lv tA) tk
  have tA₁ : Typed (rules lv) (.snoc headCtx numC) (.var 3) U0 := .var 3
  have tk₁ : Typed (rules lv) (.snoc headCtx numC) (.var 0) numC := .var 0
  have tInner : Typed (rules lv) (.snoc headCtx numC) (.pi (vecC (.var 3) (.var 0)) U0)
      (.head (.sort (.max (.const 0) (.succ (.const 0))))) :=
    .piForm (D.vec_typed tA₁ tk₁) (D.tower.isUniverse _) D.tower.u0_typed (D.tower.isUniverse _)
      (D.tower.join _ _)
  have tOuter : Typed (rules lv) headCtx (vecMotive (.var 2))
      (.head (.sort (.max (.const 0) (.max (.const 0) (.succ (.const 0)))))) :=
    .piForm D.num_typed (D.tower.isUniverse _) tInner (D.tower.isUniverse _) (D.tower.join _ _)
  exact .lamIntro tOuter (D.tower.isUniverse _) (.lamIntro tInner (D.tower.isUniverse _) tBody)

/-- The method's context: `headCtx, n : num, a : A, w : vec A n, ih : P n w`. -/
abbrev headCtx₇ : Ctx Tower.Head 7 :=
  .snoc (.snoc (.snoc (.snoc headCtx numC) (.var 3)) (vecC (.var 4) (.var 1)))
    (.app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
      (headMotive (.var 2))))) (.var 2)) (.var 0))

theorem headIh_typed :
    Typed (rules lv) (.snoc (.snoc (.snoc headCtx numC) (.var 3)) (vecC (.var 4) (.var 1)))
      (.app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (headMotive (.var 2))))) (.var 2)) (.var 0)) U0 := by
  have tP : Typed (rules lv) (.snoc (.snoc (.snoc headCtx numC) (.var 3)) (vecC (.var 4) (.var 1)))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (headMotive (.var 2)))))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (vecMotive (.var 2))))) :=
    (headMotive_typed lv).weaken.weaken.weaken
  have tk : Typed (rules lv) (.snoc (.snoc (.snoc headCtx numC) (.var 3)) (vecC (.var 4) (.var 1)))
      (.var 2) numC := .var 2
  have tw : Typed (rules lv) (.snoc (.snoc (.snoc headCtx numC) (.var 3)) (vecC (.var 4) (.var 1)))
      (.var 0) (vecC (.var 5) (.var 2)) := .var 0
  exact .appElim (.appElim tP tk) tw

theorem headCtx₇_formed : CtxFormed (rules lv) headCtx₇ := by
  have D := vecDeclared_rules lv
  have tA₄ : Typed (rules lv) (.snoc headCtx numC) (.var 3) U0 := .var 3
  have tA₅ : Typed (rules lv) (.snoc (.snoc headCtx numC) (.var 3)) (.var 4) U0 := .var 4
  have tk₅ : Typed (rules lv) (.snoc (.snoc headCtx numC) (.var 3)) (.var 1) numC := .var 1
  exact .snoc (.snoc (.snoc (.snoc (headCtx_formed lv) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, tA₄⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA₅ tk₅⟩)
    ⟨_, D.tower.isUniverse _, headIh_typed lv⟩

/-- **The method at its type**: `a : P (succ n) (pair a w)`, because
`P (succ n) (pair a w) ≡ below-step (λ _. A) (succ n) ≡ A`. -/
theorem headMethod_typed :
    Typed (rules lv) headCtx headMethod (vecMethod (.var 2) (headMotive (.var 2))) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) headCtx₇ (.var 6) U0 := .var 6
  have tk : Typed (rules lv) headCtx₇ (.var 3) numC := .var 3
  have ta : Typed (rules lv) headCtx₇ (.var 2) (.var 6) := .var 2
  have tw : Typed (rules lv) headCtx₇ (.var 1) (vecC (.var 6) (.var 3)) := .var 1
  have tP : Typed (rules lv) headCtx₇
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (headMotive (.var 2))))))
      (.pi numC (.pi (vecC (.var 7) (.var 0)) U0)) :=
    (headMotive_typed lv).weaken.weaken.weaken.weaken
  have tTarget : Typed (rules lv) headCtx₇ (.app (.app (Presentation.rename wk (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (headMotive (.var 2)))))) (succC (.var 3)))
      (.pair (.var 2) (.var 1))) U0 :=
    .appElim (.appElim tP (D.succ_typed tk)) (D.cons_typed tA tk ta tw)
  have eTarget : TypeEq (rules lv) headCtx₇ (.app (.app (Presentation.rename wk (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (headMotive (.var 2)))))) (succC (.var 3)))
      (.pair (.var 2) (.var 1))) (.var 6) := by
    refine typeEq_of_reduces lv (headCtx₇_formed lv) ?_ tTarget
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.root (belowStep_succ_step lv _ _)) ?_
    refine .head (.betaPi _ _) ?_
    exact .refl
  have tBody : Typed (rules lv) headCtx₇ (.var 2) (.app (.app (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (headMotive (.var 2))))))
      (succC (.var 3))) (.pair (.var 2) (.var 1))) := Typed.convType ta eTarget.symm
  have tA₄ : Typed (rules lv) (.snoc headCtx numC) (.var 3) U0 := .var 3
  have tA₅ : Typed (rules lv) (.snoc (.snoc headCtx numC) (.var 3)) (.var 4) U0 := .var 4
  have tk₅ : Typed (rules lv) (.snoc (.snoc headCtx numC) (.var 3)) (.var 1) numC := .var 1
  have p₄ := D.tower.pi_small (headIh_typed lv) tTarget
  have p₃ := D.tower.pi_small (D.vec_typed tA₅ tk₅) p₄
  have p₂ := D.tower.pi_small tA₄ p₃
  have p₁ := D.tower.pi_small D.num_typed p₂
  exact .lamIntro p₁ (D.tower.isUniverse _) (.lamIntro p₂ (D.tower.isUniverse _)
    (.lamIntro p₃ (D.tower.isUniverse _) (.lamIntro p₄ (D.tower.isUniverse _) tBody)))

/-- **Head is typed at `A`**: the motive at a successor length computes to `A`. -/
theorem head_typed : Typed (rules lv) headCtx (headTm (.var 2) (.var 1) (.var 0)) (.var 2) := by
  have D := vecDeclared_rules lv
  have formed := headCtx_formed lv
  have tA : Typed (rules lv) headCtx (.var 2) U0 := .var 2
  have tk : Typed (rules lv) headCtx (.var 1) numC := .var 1
  have tv : Typed (rules lv) headCtx (.var 0) (vecC (.var 2) (succC (.var 1))) := .var 0
  have tP := headMotive_typed lv
  -- `tt : P zero tt`, since `P zero tt ≡ unit`
  have tPzt : Typed (rules lv) headCtx (.app (.app (headMotive (.var 2)) zeroC) ttC) U0 :=
    .appElim (.appElim tP D.zero_typed) (D.nil_typed tA)
  have ePzt : TypeEq (rules lv) headCtx (.app (.app (headMotive (.var 2)) zeroC) ttC) unitC := by
    refine typeEq_of_reduces lv formed ?_ tPzt
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.root (belowStep_zero_step lv _)) ?_
    exact .refl
  have tpn : Typed (rules lv) headCtx ttC (.app (.app (headMotive (.var 2)) zeroC) ttC) :=
    Typed.convType D.tt_typed ePzt.symm
  have typing := D.vecElim_typed rfl tA tP tpn (headMethod_typed lv) (D.succ_typed tk) tv
  -- `P (succ k) v ≡ A`
  have tPsv : Typed (rules lv) headCtx (.app (.app (headMotive (.var 2)) (succC (.var 1))) (.var 0)) U0 :=
    .appElim (.appElim tP (D.succ_typed tk)) tv
  have ePsv : TypeEq (rules lv) headCtx (.app (.app (headMotive (.var 2)) (succC (.var 1))) (.var 0))
      (.var 2) := by
    refine typeEq_of_reduces lv formed ?_ tPsv
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.root (belowStep_succ_step lv _ _)) ?_
    refine .head (.betaPi _ _) ?_
    exact .refl
  exact Typed.convType typing ePsv

/-- **Head by the eliminator is the projection**, on an open vector: `head A k v ≡ fst v : A`. -/
theorem head_fst :
    Equal (rules lv) headCtx (headTm (.var 2) (.var 1) (.var 0)) (.fst (.var 0)) (.var 2) := by
  have red : Reduces (rules lv) (headTm (.var 2) (.var 1) (.var 0) : Tm Tower.Head 3) (.fst (.var 0)) := by
    refine .head (.root (elim_succ_step lv (.var 2) (headMotive (.var 2)) ttC headMethod (.var 1)
      (.var 0))) ?_
    refine .head (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _)))) ?_
    refine .head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    exact .refl
  exact (TowerVectors.reduces_preserve (headCtx_formed lv) red (head_typed lv)).2

/-- **Head on an extended vector**: `head A k (pair a w) ≡ a : A`, in the context
`A : U0, k : num, a : A, w : vec A k`. -/
theorem head_pair :
    Equal (rules lv) fzCtx (headTm (.var 3) (.var 2) (.pair (.var 1) (.var 0))) (.var 1) (.var 3) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) fzCtx (.var 3) U0 := .var 3
  have tk : Typed (rules lv) fzCtx (.var 2) numC := .var 2
  have ta : Typed (rules lv) fzCtx (.var 1) (.var 3) := .var 1
  have tw : Typed (rules lv) fzCtx (.var 0) (vecC (.var 3) (.var 2)) := .var 0
  have m₀ : SubstMor (rules lv) .nil fzCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) headCtx fzCtx
      (consSub (.pair (.var 1) (.var 0)) (consSub (.var 2) (consSub (.var 3) fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) tk) (D.cons_typed tA tk ta tw)
  have projected : Equal (rules lv) fzCtx (headTm (.var 3) (.var 2) (.pair (.var 1) (.var 0)))
      (.fst (.pair (.var 1) (.var 0))) (.var 3) := (head_fst lv).substitute mor
  exact .trans projected (head_cons lv tA tk ta tw)

end TowerVectorsHead

#print axioms TowerVectorsHead.headMotive_typed
#print axioms TowerVectorsHead.headMethod_typed
#print axioms TowerVectorsHead.head_typed
#print axioms TowerVectorsHead.head_fst
#print axioms TowerVectorsHead.head_pair

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
