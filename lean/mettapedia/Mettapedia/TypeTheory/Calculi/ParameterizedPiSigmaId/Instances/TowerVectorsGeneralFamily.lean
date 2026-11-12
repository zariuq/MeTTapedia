import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsIdentity

/-!
# A general indexed family: a constructor at an index that is not a pattern

`vec` and `below` are indexed families whose index decides the constructor, so they are declared
by recursion on the index. A general indexed family has constructors at arbitrary index
expressions. With the identity eliminator in the package, such a family can be presented as a
dependent pair type with an identity constraint on the index, its dependent eliminator being a
program. This module does it for one family.

The family of doubles has one constructor, `mk k : double (add k k)`, at the index `add k k`,
which is not a constructor pattern:

  `double n = Σ (k : num). Id num (add k k) n`,   `mk k = pair k (refl (add k k))`.

* `double_typed`, `mk_typed`: formation and introduction, with the index.
* **The dependent eliminator** (`elim_typed`): for a motive `P : Π (n : num). double n → U0` and a
  method `m : Π (k : num). P (add k k) (mk k)`, `double-elim P m n h : P n h` at every index `n` and
  every `h : double n`. It is the identity eliminator along the constraint of `h`, with the motive
  `λ y p. P y (pair (fst h) p)`, and eta for pairs.
* **Its computation rule** (`elim_mk`): `double-elim P m (add k k) (mk k) ≡ m k`, on an open `k`.
* Controls: the eliminator is stuck on a variable (`elim_stuck`); the ill-indexed constructor
  application `mk zero : double (succ zero)` is rejected (`mk_ill_indexed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerVectorsModel TowerVectorsPrograms TowerVectorsLookup TowerVectorsIdentity
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)

namespace TowerVectorsGeneralFamily

variable (lv : LevelExpr Nat)

/-! ## The family, its constructor and its eliminator -/

/-- **The family of doubles**: `double n = Σ (k : num). Id num (add k k) n`. -/
def doubleC {n : Nat} (t : Tm Tower.Head n) : Tm Tower.Head n :=
  .sigma numC (.id numC (addC (.var 0) (.var 0)) (Presentation.rename wk t))

/-- **Its constructor**: `mk k : double (add k k)`. -/
def mkC {n : Nat} (k : Tm Tower.Head n) : Tm Tower.Head n := .pair k (.refl (addC k k))

/-- The type of motives: `Π (n : num). double n → U0`. -/
def motiveType {n : Nat} : Tm Tower.Head n := .pi numC (.pi (doubleC (.var 0)) U0)

/-- The type of methods over a motive `P`: `Π (k : num). P (add k k) (mk k)`. -/
def methodType {n : Nat} (P : Tm Tower.Head n) : Tm Tower.Head n :=
  .pi numC (.app (.app (Presentation.rename wk P) (addC (.var 0) (.var 0))) (mkC (.var 0)))

/-- The motive handed to the identity eliminator: `λ y p. P y (pair (fst h) p)`. -/
def elimMotive {n : Nat} (P h : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk P)) (.var 1))
    (.pair (.fst (Presentation.rename wk (Presentation.rename wk h))) (.var 0))))

/-- **The dependent eliminator** `double-elim P m k h`. -/
def elimTm {n : Nat} (P m k h : Tm Tower.Head n) : Tm Tower.Head n :=
  idElimC numC (addC (.fst h) (.fst h)) (elimMotive P h) (.app m (.fst h)) k (.snd h)

/-! ## Formation and introduction -/

/-- **Formation**: `double t` is a small type, for every number `t`. -/
theorem double_typed {n : Nat} {Γ : Ctx Tower.Head n} {t : Tm Tower.Head n}
    (typed : Typed (rules lv) Γ t numC) : Typed (rules lv) Γ (doubleC t) U0 := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) (.snoc Γ numC) (.var 0) numC := .var 0
  exact D.tower.sigma_small D.num_typed
    (.idForm D.num_typed (D.tower.isUniverse _) (add_typed lv tk tk) typed.weaken)

/-- **Introduction, with its index**: `mk k : double (add k k)`. -/
theorem mk_typed {n : Nat} {Γ : Ctx Tower.Head n} {k : Tm Tower.Head n}
    (typed : Typed (rules lv) Γ k numC) : Typed (rules lv) Γ (mkC k) (doubleC (addC k k)) := by
  have D := vecDeclared_rules lv
  have sum := add_typed lv typed typed
  have proof : Typed (rules lv) Γ (.refl (addC k k))
      (inst0 k (.id numC (addC (.var 0) (.var 0)) (Presentation.rename wk (addC k k)))) := by
    show Typed (rules lv) Γ (.refl (addC k k))
      (.id numC (addC k k) (inst0 k (Presentation.rename wk (addC k k))))
    rw [inst0_rename_wk]
    exact .reflIntro sum
  exact .pairIntro (double_typed lv sum) (D.tower.isUniverse _) typed proof

theorem motiveType_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    ∃ w, (rules lv).isUniverse w ∧ Typed (rules lv) Γ motiveType (.head w) := by
  have D := vecDeclared_rules lv
  have tn : Typed (rules lv) (.snoc Γ numC) (.var 0) numC := .var 0
  have inner := Derivable.piForm (double_typed lv tn) (D.tower.isUniverse _)
    (D.tower.u0_typed : Typed (rules lv) (.snoc (.snoc Γ numC) (doubleC (.var 0))) U0 _)
    (D.tower.isUniverse _) (D.tower.join _ _)
  exact ⟨_, D.tower.isUniverse _, .piForm D.num_typed (D.tower.isUniverse _) inner
    (D.tower.isUniverse _) (D.tower.join _ _)⟩

/-- The context of a motive, a method and an index:
`P : Π (n : num). double n → U0, m : Π (k : num). P (add k k) (mk k), n : num`. -/
abbrev baseCtx : Ctx Tower.Head 3 := .snoc (.snoc (.snoc .nil motiveType) (methodType (.var 0))) numC

/-- With a member of the family at the index: `h : double n`. -/
abbrev elimCtx : Ctx Tower.Head 4 := .snoc baseCtx (doubleC (.var 0))

theorem baseCtx_formed : CtxFormed (rules lv) baseCtx := by
  have D := vecDeclared_rules lv
  obtain ⟨w, hw, tMotive⟩ := motiveType_typed lv (Γ := .nil)
  have tP : Typed (rules lv) (.snoc (.snoc .nil motiveType) numC) (.var 1) motiveType := .var 1
  have tk : Typed (rules lv) (.snoc (.snoc .nil motiveType) numC) (.var 0) numC := .var 0
  have tBody : Typed (rules lv) (.snoc (.snoc .nil motiveType) numC)
      (.app (.app (.var 1) (addC (.var 0) (.var 0))) (mkC (.var 0))) U0 :=
    .appElim (.appElim tP (add_typed lv tk tk)) (mk_typed lv tk)
  exact .snoc (.snoc (.snoc .nil ⟨w, hw, tMotive⟩)
    ⟨_, D.tower.isUniverse _, D.tower.pi_small D.num_typed tBody⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩

theorem elimCtx_formed : CtxFormed (rules lv) elimCtx := by
  have D := vecDeclared_rules lv
  have tn : Typed (rules lv) baseCtx (.var 0) numC := .var 0
  exact .snoc (baseCtx_formed lv) ⟨_, D.tower.isUniverse _, double_typed lv tn⟩

/-! ## The dependent eliminator -/

/-- The motive of the identity eliminator is a family over the numbers equal to
`add (fst h) (fst h)`. -/
theorem elimMotive_typed :
    Typed (rules lv) elimCtx (elimMotive (.var 3) (.var 0))
      (.pi numC (.pi (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0))
        (.head (.sort lv)))) := by
  have D := vecDeclared_rules lv
  have th₅ : Typed (rules lv) (.snoc elimCtx numC) (.var 1) (doubleC (.var 2)) := .var 1
  have tfst₅ : Typed (rules lv) (.snoc elimCtx numC) (.fst (.var 1)) numC := .fstElim th₅
  have ty₅ : Typed (rules lv) (.snoc elimCtx numC) (.var 0) numC := .var 0
  have tId : Typed (rules lv) (.snoc elimCtx numC)
      (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)) U0 :=
    .idForm D.num_typed (D.tower.isUniverse _) (add_typed lv tfst₅ tfst₅) ty₅
  have tP₆ : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.var 5) motiveType := .var 5
  have ty₆ : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.var 1) numC := .var 1
  have th₆ : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.var 2) (doubleC (.var 3)) := .var 2
  have tfst₆ : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.fst (.var 2)) numC := .fstElim th₆
  have tp₆ : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.var 0) (.id numC (addC (.fst (.var 2)) (.fst (.var 2))) (.var 1)) := .var 0
  have tpair : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.pair (.fst (.var 2)) (.var 0)) (doubleC (.var 1)) :=
    .pairIntro (double_typed lv ty₆) (D.tower.isUniverse _) tfst₆ tp₆
  have tBody : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.app (.app (.var 5) (.var 1)) (.pair (.fst (.var 2)) (.var 0))) (.head (.sort lv)) :=
    D.tower.lift (.appElim (.appElim tP₆ ty₆) tpair) lv
  have pInner := Derivable.piForm tId (D.tower.isUniverse _)
    (.headType (D.tower.headTyping _) : Typed (rules lv)
      (.snoc (.snoc elimCtx numC) (.id numC (addC (.fst (.var 1)) (.fst (.var 1))) (.var 0)))
      (.head (.sort lv)) (.head (.sort (.succ lv)))) (D.tower.isUniverse _) (D.tower.join _ _)
  have pOuter := Derivable.piForm D.num_typed (D.tower.isUniverse _) pInner (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact .lamIntro pOuter (D.tower.isUniverse _) (.lamIntro pInner (D.tower.isUniverse _) tBody)

/-- **The dependent eliminator is typed**: `double-elim P m n h : P n h`, at every index `n` and
every member `h` of the family there. -/
theorem elim_typed :
    Typed (rules lv) elimCtx (elimTm (.var 3) (.var 2) (.var 1) (.var 0))
      (.app (.app (.var 3) (.var 1)) (.var 0)) := by
  have D := vecDeclared_rules lv
  have formed := elimCtx_formed lv
  have tPvar : Typed (rules lv) elimCtx (.var 3) motiveType := .var 3
  have tm : Typed (rules lv) elimCtx (.var 2) (methodType (.var 3)) := .var 2
  have tn : Typed (rules lv) elimCtx (.var 1) numC := .var 1
  have th : Typed (rules lv) elimCtx (.var 0) (doubleC (.var 1)) := .var 0
  have tfst : Typed (rules lv) elimCtx (.fst (.var 0)) numC := .fstElim th
  have tsnd : Typed (rules lv) elimCtx (.snd (.var 0))
      (.id numC (addC (.fst (.var 0)) (.fst (.var 0))) (.var 1)) := .sndElim th
  have tx : Typed (rules lv) elimCtx (addC (.fst (.var 0)) (.fst (.var 0))) numC :=
    add_typed lv tfst tfst
  have tP := elimMotive_typed lv
  -- the method at the witness, at the motive at reflexivity
  have tmk : Typed (rules lv) elimCtx (.app (.var 2) (.fst (.var 0)))
      (.app (.app (.var 3) (addC (.fst (.var 0)) (.fst (.var 0)))) (mkC (.fst (.var 0)))) :=
    .appElim tm tfst
  have tAtRefl : Typed (rules lv) elimCtx
      (.app (.app (elimMotive (.var 3) (.var 0)) (addC (.fst (.var 0)) (.fst (.var 0))))
        (.refl (addC (.fst (.var 0)) (.fst (.var 0))))) (.head (.sort lv)) :=
    .appElim (.appElim tP tx) (.reflIntro tx)
  have eRefl : TypeEq (rules lv) elimCtx
      (.app (.app (elimMotive (.var 3) (.var 0)) (addC (.fst (.var 0)) (.fst (.var 0))))
        (.refl (addC (.fst (.var 0)) (.fst (.var 0)))))
      (.app (.app (.var 3) (addC (.fst (.var 0)) (.fst (.var 0)))) (mkC (.fst (.var 0)))) :=
    typeEq_of_reduces_at lv formed (.head (.congAppFun (.betaPi _ _)) (.head (.betaPi _ _) .refl))
      tAtRefl
  have td : Typed (rules lv) elimCtx (.app (.var 2) (.fst (.var 0)))
      (.app (.app (elimMotive (.var 3) (.var 0)) (addC (.fst (.var 0)) (.fst (.var 0))))
        (.refl (addC (.fst (.var 0)) (.fst (.var 0))))) := Typed.convType tmk eRefl.symm
  have tJ := idElim_typed lv D.num_typed tx tP td tn tsnd
  -- the result, at the motive of the family
  have tAtPath : Typed (rules lv) elimCtx
      (.app (.app (elimMotive (.var 3) (.var 0)) (.var 1)) (.snd (.var 0))) (.head (.sort lv)) :=
    .appElim (.appElim tP tn) tsnd
  have ePath : TypeEq (rules lv) elimCtx
      (.app (.app (elimMotive (.var 3) (.var 0)) (.var 1)) (.snd (.var 0)))
      (.app (.app (.var 3) (.var 1)) (.pair (.fst (.var 0)) (.snd (.var 0)))) :=
    typeEq_of_reduces_at lv formed (.head (.congAppFun (.betaPi _ _)) (.head (.betaPi _ _) .refl))
      tAtPath
  -- eta for pairs: `h ≡ pair (fst h) (snd h)`
  have tS : Typed (rules lv) elimCtx (doubleC (.var 1)) U0 := double_typed lv tn
  have tpair : Typed (rules lv) elimCtx (.pair (.fst (.var 0)) (.snd (.var 0))) (doubleC (.var 1)) :=
    .pairIntro tS (D.tower.isUniverse _) tfst tsnd
  have eta : Equal (rules lv) elimCtx (.var 0) (.pair (.fst (.var 0)) (.snd (.var 0)))
      (doubleC (.var 1)) :=
    .etaSigma th tpair (.symm (.betaFst tS (D.tower.isUniverse _) tfst tsnd))
      (.symm (.betaSnd tS (D.tower.isUniverse _) tfst tsnd))
  have tPn : Typed (rules lv) elimCtx (.app (.var 3) (.var 1)) (.pi (doubleC (.var 1)) U0) :=
    .appElim tPvar tn
  have eEta : TypeEq (rules lv) elimCtx (.app (.app (.var 3) (.var 1)) (.var 0))
      (.app (.app (.var 3) (.var 1)) (.pair (.fst (.var 0)) (.snd (.var 0)))) :=
    ⟨u, D.tower.isUniverse _, .appCong (.refl tPn) eta⟩
  exact Typed.convType (Typed.convType tJ ePath) eEta.symm

/-! ## Its computation rule -/

/-- **The eliminator computes on the constructor**, at an open `k`:
`double-elim P m (add k k) (mk k) ≡ m k : P (add k k) (mk k)`. -/
theorem elim_mk :
    Equal (rules lv) baseCtx (elimTm (.var 2) (.var 1) (addC (.var 0) (.var 0)) (mkC (.var 0)))
      (.app (.var 1) (.var 0)) (.app (.app (.var 2) (addC (.var 0) (.var 0))) (mkC (.var 0))) := by
  have tP : Typed (rules lv) baseCtx (.var 2) motiveType := .var 2
  have tm : Typed (rules lv) baseCtx (.var 1) (methodType (.var 2)) := .var 1
  have tk : Typed (rules lv) baseCtx (.var 0) numC := .var 0
  have m₀ : SubstMor (rules lv) .nil baseCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) elimCtx baseCtx
      (consSub (mkC (.var 0)) (consSub (addC (.var 0) (.var 0)) (consSub (.var 1) (consSub (.var 2)
        fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tP) tm) (add_typed lv tk tk))
      (mk_typed lv tk)
  have typing := (elim_typed lv).substitute mor
  have red : Reduces (rules lv)
      (elimTm (.var 2) (.var 1) (addC (.var 0) (.var 0)) (mkC (.var 0)) : Tm Tower.Head 3)
      (.app (.var 1) (.var 0)) := by
    refine .head (.congAppArg (.betaSigmaSnd _ _)) ?_
    refine .head (.root (idElim_step lv _ _ _ _ _ _)) ?_
    refine .head (.congAppArg (.betaSigmaFst _ _)) ?_
    exact .refl
  exact (TowerVectors.reduces_preserve (baseCtx_formed lv) red typing).2

/-! ## Controls -/

/-- **Negative control: stuck on a variable.** `double-elim P m k x` is neutral when `x` is a
variable: the identity eliminator inspects the constraint `snd x`. -/
theorem elim_stuck {n : Nat} {P m k : Tm Tower.Head n} (x : Fin n) :
    Neutral roles (elimTm P m k (.var x)) ∧ Whnf (rules lv) roles (elimTm P m k (.var x)) := by
  have neutral : Neutral roles (elimTm P m k (.var x)) :=
    Neutral.stuck_single
      (before := [numC, addC (.fst (.var x)) (.fst (.var x)), elimMotive P (.var x),
        .app m (.fst (.var x)), k]) (after := []) roles_idElim rfl (.snd (.var x))
  exact ⟨neutral, neutral.whnf (shape lv)⟩

/-- **Negative control: an ill-indexed constructor application is rejected.** `mk zero` is not
a member of `double (succ zero)`: its constraint would equate `add zero zero` with `succ zero`. -/
theorem mk_ill_indexed : ¬ Typed (rules lv) .nil (mkC zeroC) (doubleC (succC zeroC)) := by
  intro typing
  have D := vecDeclared_rules lv
  obtain ⟨_, proof⟩ := Typed.pair_inv (S := setting lv fun _ => 0) (facts lv) typing .nil
  have atIndex : Typed (rules lv) .nil (.refl (addC zeroC zeroC))
      (.id numC (addC zeroC zeroC) (succC zeroC)) := proof
  obtain ⟨A, _, le⟩ := Typed.generation atIndex
  have e := TypeLe.id_eq (S := setting lv fun _ => 0) (facts lv) le
    (Typed.isType (S := setting lv fun _ => 0) atIndex .nil) .nil
  obtain ⟨eA, _, ends⟩ := TypeEq.id_injective (facts lv) e .nil
  have sum : Equal (rules lv) .nil (addC zeroC zeroC) (succC zeroC) numC := Equal.convType ends eA
  exact TowerVectors.zero_ne_succ .nil (.trans (.symm (TowerVectors.add_zero D.zero_typed)) sum)

/-- **Positive twin**: `mk zero` is a member of the family at its own index, `add zero zero`. -/
theorem mk_zero_typed : Typed (rules lv) .nil (mkC zeroC) (doubleC (addC zeroC zeroC)) :=
  mk_typed lv (vecDeclared_rules lv).zero_typed

end TowerVectorsGeneralFamily

#print axioms TowerVectorsGeneralFamily.double_typed
#print axioms TowerVectorsGeneralFamily.mk_typed
#print axioms TowerVectorsGeneralFamily.elim_typed
#print axioms TowerVectorsGeneralFamily.elim_mk
#print axioms TowerVectorsGeneralFamily.elim_stuck
#print axioms TowerVectorsGeneralFamily.mk_ill_indexed
#print axioms TowerVectorsGeneralFamily.mk_zero_typed

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
