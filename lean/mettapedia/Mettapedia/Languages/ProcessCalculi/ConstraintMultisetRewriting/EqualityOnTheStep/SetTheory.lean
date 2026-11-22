import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Quotient

/-!
# A small set theory on the step

Sets over `U0` are predicates `U0 → U0`; membership `A ∈ S` is the type `S A`; equality of sets is
`setEq` (`Codes`), proved by rows and used by transport (`Run`, `Transport`); the quotient by it is
`Quotient`.

* **Comprehension** (`comprehension_typed`, `comprehension_beta`): `{X | φ}` is `λX. φ`, and
  `A ∈ {X | φ}` is `φ[A/X]` in the knowledge. No evidence is needed.
* **Intersection** (`inter`, `inter_typed`): `S ∩ T = λX. Σ (_ : S X). T X`. The two sets of
  `SetExtensionality` are intersections: `S` is `I ∩ G` and `T` is `G ∩ I` in the knowledge, for
  `I = {X | X}` and `G = {X | Ground}` (`s_is_inter`, `t_is_inter`). So limit F4 is the commutativity
  of intersection: the knowledge refuses `I ∩ G ≐ G ∩ I` (`inter_commutation_refused`), and the
  extensionality rule of `Run` proves it with evidence.
* **Extensional equality is an equivalence** (`setEq_refl`, `setEq_symm`, `setEq_trans`), each a
  closed term over a frame of set variables, so for all sets by substitution.
* **Union, one universe up** (`union`, `union_typed`): the grammar has no sum former, so `S ∪ T` is
  Church-encoded, `λX. Π (C : U0). (S X → C) → (T X → C) → C`, a predicate valued in `U1`, not a set
  of `U0 → U0`. The left introduction is `union_inl_typed`. Its eliminator is application at a type
  `C` of `U0`, so it eliminates only into `U0`; it has no dependent elimination.
* **Non-membership transports** (`negFamily`, `negRespect_typed`): `λS. S X → ⊥` has the respect term
  `λS T e n m. n (snd (e X) m)`, which uses the backward map.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.SetTheory

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-! ## Comprehension -/

/-- **A comprehension is a set**: `{X | φ} = λX. φ`. -/
theorem comprehension_typed {n : Nat} {Γ : Tower.Ctx n} {φ : Tower.Tm (n + 1)}
    (tφ : Typed Tower.rules (.snoc Γ U0) φ U0) : Typed Tower.rules Γ (.lam φ) setType :=
  .lamIntro (setType_formed Γ) (.sort _) tφ

/-- **Comprehension is definitional**: `A ∈ {X | φ}` is `φ[A/X]` in the knowledge. -/
theorem comprehension_beta {n : Nat} {Γ : Tower.Ctx n} {φ : Tower.Tm (n + 1)} {A : Tower.Tm n}
    (tφ : Typed Tower.rules (.snoc Γ U0) φ U0) (tA : Typed Tower.rules Γ A U0) :
    Equal Tower.rules Γ (.app (.lam φ) A) (inst0 A φ) U0 :=
  Derivable.betaPi (setType_formed Γ) (.sort _) tφ tA

/-! ## Intersection -/

/-- **Intersection**: `S ∩ T = λX. Σ (_ : S X). T X`. -/
def inter {n : Nat} (S T : Tower.Tm n) : Tower.Tm n :=
  .lam (.sigma (.app (Presentation.rename wk S) (.var 0))
    (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)))

theorem inter_typed {n : Nat} {Γ : Tower.Ctx n} {S T : Tower.Tm n}
    (tS : Typed Tower.rules Γ S setType) (tT : Typed Tower.rules Γ T setType) :
    Typed Tower.rules Γ (inter S T) setType := by
  have SX : Typed Tower.rules (.snoc Γ U0) (.app (Presentation.rename wk S) (.var 0)) U0 :=
    Run.app_small tS.weaken (Derivable.var 0)
  have TX : Typed Tower.rules (.snoc (.snoc Γ U0) (.app (Presentation.rename wk S) (.var 0)))
      (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)) U0 :=
    Run.app_small tT.weaken.weaken (Derivable.var 1)
  exact comprehension_typed (.cumul (.sigmaForm SX (.sort _) TX (.sort _) (.sorts _ _)) collapse)

/-- `I = {X | X}`. -/
def idSet {n : Nat} : Tower.Tm n := .lam (.var 0)

/-- `G = {X | Ground}`. -/
def groundSet {n : Nat} : Tower.Tm n := .lam ground

theorem idSet_typed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ idSet setType :=
  comprehension_typed (Derivable.var 0)

theorem groundSet_typed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ groundSet setType :=
  comprehension_typed (ground_typed _)

/-- **`S` is `I ∩ G`** in the knowledge. -/
theorem s_is_inter {n : Nat} (Γ : Tower.Ctx n) :
    Equal Tower.rules Γ (inter idSet groundSet) sCode setType := by
  have first : Equal Tower.rules (.snoc Γ U0) (.app idSet (.var 0)) (.var 0) U0 :=
    comprehension_beta (Derivable.var 0) (Derivable.var 0)
  have second : Equal Tower.rules (.snoc (.snoc Γ U0) (.app idSet (.var 0))) (.app groundSet (.var 1)) ground U0 :=
    comprehension_beta (ground_typed _) (Derivable.var 1)
  have bodies : Equal Tower.rules (.snoc Γ U0) (.sigma (.app idSet (.var 0)) (.app groundSet (.var 1)))
      (.sigma (.var 0) ground) U0 :=
    .cumulEq (.sigmaCong first (.sort _) second (.sort _) (.sorts _ _)) collapse
  exact .lamCong (setType_formed Γ) (.sort _) bodies

/-- **`T` is `G ∩ I`** in the knowledge. -/
theorem t_is_inter {n : Nat} (Γ : Tower.Ctx n) :
    Equal Tower.rules Γ (inter groundSet idSet) tCode setType := by
  have first : Equal Tower.rules (.snoc Γ U0) (.app groundSet (.var 0)) ground U0 :=
    comprehension_beta (ground_typed _) (Derivable.var 0)
  have second : Equal Tower.rules (.snoc (.snoc Γ U0) (.app groundSet (.var 0))) (.app idSet (.var 1)) (.var 1) U0 :=
    comprehension_beta (Derivable.var 0) (Derivable.var 1)
  have bodies : Equal Tower.rules (.snoc Γ U0) (.sigma (.app groundSet (.var 0)) (.app idSet (.var 1)))
      (.sigma ground (.var 1)) U0 :=
    .cumulEq (.sigmaCong first (.sort _) second (.sort _) (.sorts _ _)) collapse
  exact .lamCong (setType_formed Γ) (.sort _) bodies

/-- **Commutativity of intersection is refused by the knowledge**, at every frame: it would equate
`S` and `T`. -/
theorem inter_commutation_refused {Θ : Context Tower.rules}
    (equal : Equal Tower.rules Θ.raw (inter idSet groundSet) (inter groundSet idSet) setType) : False :=
  Quotient.sets_apart (Θ := Θ) (.trans (.symm (s_is_inter _)) (.trans equal (t_is_inter _)))

/-! ## Extensional equality is an equivalence -/

/-- The frame `S : U0 → U0`. -/
abbrev sets1 : Tower.Ctx 1 := .snoc .nil setType

/-- The frame `S T : U0 → U0`. -/
abbrev sets2 : Tower.Ctx 2 := .snoc sets1 setType

/-- The frame `S T U : U0 → U0`. -/
abbrev sets3 : Tower.Ctx 3 := .snoc sets2 setType

/-- `λX. (λp. p, λp. p)`. -/
def reflCode : Tower.Tm 1 := .lam (.pair (.lam (.var 0)) (.lam (.var 0)))

/-- **Reflexivity**: `S ≈ S`. -/
theorem setEq_refl : Typed Tower.rules sets1 reflCode (setEq (.var 0) (.var 0)) := by
  have tS : Typed Tower.rules sets1 (.var 0) setType := Derivable.var 0
  have identity := Derivable.lamIntro (setEqForward_formed tS tS) (.sort _)
    (Derivable.var (R := Tower.rules)
      (Γ := .snoc (.snoc sets1 U0) (.app (Presentation.rename wk (.var 0)) (.var 0))) 0)
  have body := Derivable.pairIntro (setEqBody_formed tS tS) (.sort _) identity identity
  exact .lamIntro (setEq_formed tS tS) (.sort _) body

/-- `λe. λX. (snd (e X), fst (e X))`. -/
def symmCode : Tower.Tm 2 :=
  .lam (.lam (.pair (.snd (.app (.var 1) (.var 0))) (.fst (.app (.var 1) (.var 0)))))

/-- **Symmetry**: `S ≈ T → T ≈ S`. -/
theorem setEq_symm :
    Typed Tower.rules sets2 symmCode (.pi (setEq (.var 1) (.var 0)) (setEq (.var 1) (.var 2))) := by
  have tS : Typed Tower.rules (.snoc sets2 (setEq (.var 1) (.var 0))) (.var 2) setType := Derivable.var 2
  have tT : Typed Tower.rules (.snoc sets2 (setEq (.var 1) (.var 0))) (.var 1) setType := Derivable.var 1
  have e := Derivable.var (R := Tower.rules) (Γ := .snoc (.snoc sets2 (setEq (.var 1) (.var 0))) U0) 1
  have X := Derivable.var (R := Tower.rules) (Γ := .snoc (.snoc sets2 (setEq (.var 1) (.var 0))) U0) 0
  have eX := Derivable.appElim e X
  have body := Derivable.pairIntro (setEqBody_formed tT tS) (.sort _) (Derivable.sndElim eX) (Derivable.fstElim eX)
  have inner := Derivable.lamIntro (setEq_formed tT tS) (.sort _) body
  have formed : Typed Tower.rules sets2 (.pi (setEq (.var 1) (.var 0)) (setEq (.var 1) (.var 2))) (.head large) :=
    .cumul (.piForm (setEq_formed (Derivable.var 1) (Derivable.var 0)) (.sort _) (setEq_formed tT tS) (.sort _)
      (.sorts _ _)) large_of_one_one
  exact .lamIntro formed (.sort _) inner

/-- `λe e'. λX. (λp. fst (e' X) (fst (e X) p), λq. snd (e X) (snd (e' X) q))`. -/
def transCode : Tower.Tm 3 :=
  .lam (.lam (.lam (.pair
    (.lam (.app (.fst (.app (.var 2) (.var 1))) (.app (.fst (.app (.var 3) (.var 1))) (.var 0))))
    (.lam (.app (.snd (.app (.var 3) (.var 1))) (.app (.snd (.app (.var 2) (.var 1))) (.var 0)))))))

/-- The frame `S T U, e : S ≈ T`. -/
abbrev transCtx4 : Tower.Ctx 4 := .snoc sets3 (setEq (.var 2) (.var 1))

/-- The frame `S T U, e : S ≈ T, e' : T ≈ U`. -/
abbrev transCtx5 : Tower.Ctx 5 := .snoc transCtx4 (setEq (.var 2) (.var 1))

/-- **Transitivity**: `S ≈ T → T ≈ U → S ≈ U`. -/
theorem setEq_trans :
    Typed Tower.rules sets3 transCode
      (.pi (setEq (.var 2) (.var 1)) (.pi (setEq (.var 2) (.var 1)) (setEq (.var 4) (.var 2)))) := by
  have tS : Typed Tower.rules transCtx5 (.var 4) setType := Derivable.var 4
  have tU : Typed Tower.rules transCtx5 (.var 2) setType := Derivable.var 2
  -- the forward component, over `X : U0, p : S X`
  have e1 := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 4)) (.var 0))) 3
  have e2 := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 4)) (.var 0))) 2
  have x1 := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 4)) (.var 0))) 1
  have p0 := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 4)) (.var 0))) 0
  have toT := Derivable.appElim (Derivable.fstElim (Derivable.appElim e1 x1)) p0
  have toU := Derivable.appElim (Derivable.fstElim (Derivable.appElim e2 x1)) toT
  have first := Derivable.lamIntro (setEqForward_formed tS tU) (.sort _) toU
  -- the backward component, over `X : U0, q : U X`
  have e1' := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 2)) (.var 0))) 3
  have e2' := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 2)) (.var 0))) 2
  have x1' := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 2)) (.var 0))) 1
  have q0 := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc transCtx5 U0) (.app (Presentation.rename wk (.var 2)) (.var 0))) 0
  have backT := Derivable.appElim (Derivable.sndElim (Derivable.appElim e2' x1')) q0
  have backS := Derivable.appElim (Derivable.sndElim (Derivable.appElim e1' x1')) backT
  have second := Derivable.lamIntro (setEqForward_formed tU tS) (.sort _) backS
  have body := Derivable.pairIntro (setEqBody_formed tS tU) (.sort _) first second
  have inner := Derivable.lamIntro (setEq_formed tS tU) (.sort _) body
  have tT4 : Typed Tower.rules transCtx4 (.var 2) setType := Derivable.var 2
  have tU4 : Typed Tower.rules transCtx4 (.var 1) setType := Derivable.var 1
  have middleFormed : Typed Tower.rules transCtx4 (.pi (setEq (.var 2) (.var 1)) (setEq (.var 4) (.var 2)))
      (.head large) :=
    .cumul (.piForm (setEq_formed tT4 tU4) (.sort _) (setEq_formed tS tU) (.sort _) (.sorts _ _)) large_of_one_one
  have middle := Derivable.lamIntro middleFormed (.sort _) inner
  have outerFormed : Typed Tower.rules sets3
      (.pi (setEq (.var 2) (.var 1)) (.pi (setEq (.var 2) (.var 1)) (setEq (.var 4) (.var 2)))) (.head large) :=
    .cumul (.piForm (setEq_formed (Derivable.var 2) (Derivable.var 1)) (.sort _) middleFormed (.sort _)
      (.sorts _ _)) large_of_one_one
  exact .lamIntro outerFormed (.sort _) middle

/-! ## Union, one universe up -/

/-- `U0 → U1`: predicates whose members are types of `U1`. -/
def largeSetType {n : Nat} : Tower.Tm n := .pi U0 (.head large)

theorem largeSetType_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ largeSetType (.head (.sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero))))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

/-- **Union, Church-encoded**: `S ∪ T = λX. Π (C : U0). (S X → C) → (T X → C) → C`. -/
def union {n : Nat} (S T : Tower.Tm n) : Tower.Tm n :=
  .lam (.pi U0 (.pi (.pi (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) (.var 1))
    (.pi (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk T))) (.var 2)) (.var 2))
      (.var 2))))

/-- The Church type of `A ∈ S ∪ T`, over `X : U0`. -/
theorem unionBody_typed {n : Nat} {Γ : Tower.Ctx n} {S T : Tower.Tm n}
    (tS : Typed Tower.rules Γ S setType) (tT : Typed Tower.rules Γ T setType) :
    Typed Tower.rules (.snoc Γ U0)
      (.pi U0 (.pi (.pi (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) (.var 1))
        (.pi (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk T))) (.var 2))
          (.var 2)) (.var 2)))) (.head large) := by
  have SX : Typed Tower.rules (.snoc (.snoc Γ U0) U0)
      (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) U0 :=
    Run.app_small tS.weaken.weaken (Derivable.var 1)
  have C3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) U0)
      (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1))) (.var 1) U0 := Derivable.var 1
  have kType : Typed Tower.rules (.snoc (.snoc Γ U0) U0)
      (.pi (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) (.var 1)) U0 :=
    .cumul (.piForm SX (.sort _) C3 (.sort _) (.sorts _ _)) collapse
  have TX : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) U0)
      (.pi (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) (.var 1)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk T))) (.var 2)) U0 :=
    Run.app_small tT.weaken.weaken.weaken (Derivable.var 2)
  have C4 : Typed Tower.rules (.snoc (.snoc (.snoc (.snoc Γ U0) U0)
      (.pi (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) (.var 1)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk T))) (.var 2))) (.var 2) U0 :=
    Derivable.var 2
  have lType : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) U0)
      (.pi (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) (.var 1)))
      (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk T))) (.var 2)) (.var 2)) U0 :=
    .cumul (.piForm TX (.sort _) C4 (.sort _) (.sorts _ _)) collapse
  have C5 : Typed Tower.rules (.snoc (.snoc (.snoc (.snoc Γ U0) U0)
      (.pi (.app (Presentation.rename wk (Presentation.rename wk S)) (.var 1)) (.var 1)))
      (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk T))) (.var 2)) (.var 2)))
      (.var 2) U0 := Derivable.var 2
  have rest := Derivable.cumul (.piForm lType (.sort _) C5 (.sort _) (.sorts _ _)) collapse
  have body := Derivable.cumul (.piForm kType (.sort _) rest (.sort _) (.sorts _ _)) collapse
  exact .cumul (.piForm (.headType (.sort _)) (.sort _) body (.sort _) (.sorts _ _)) large_of_one_zero

/-- **Union is a predicate valued in `U1`**, not a set. -/
theorem union_typed {n : Nat} {Γ : Tower.Ctx n} {S T : Tower.Tm n}
    (tS : Typed Tower.rules Γ S setType) (tT : Typed Tower.rules Γ T setType) :
    Typed Tower.rules Γ (union S T) largeSetType :=
  .lamIntro (largeSetType_formed Γ) (.sort _) (unionBody_typed tS tT)

/-- `λC k l. k (x, g)`: the member `(x, g) : X ∈ S` as a member of `S ∪ T`, over
`X : U0, x : X, g : Ground`. -/
def unionInl : Tower.Tm 3 := .lam (.lam (.lam (.app (.var 1) (.pair (.var 4) (.var 3)))))

/-- **The left introduction of union**: `(x, g) ∈ S` gives a member of the Church type of
`X ∈ S ∪ T`. -/
theorem union_inl_typed :
    Typed Tower.rules triple.raw unionInl
      (.pi U0 (.pi (.pi (.app sCode (.var 3)) (.var 1)) (.pi (.pi (.app tCode (.var 4)) (.var 2)) (.var 2)))) := by
  have member : Typed Tower.rules
      (.snoc (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
        (.pi (.app tCode (.var 4)) (.var 2)))
      (.pair (.var 4) (.var 3)) (.app sCode (.var 5)) := by
    have x : Typed Tower.rules (.snoc (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
        (.pi (.app tCode (.var 4)) (.var 2))) (.var 4) (.var 5) := Derivable.var 4
    have g : Typed Tower.rules (.snoc (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
        (.pi (.app tCode (.var 4)) (.var 2))) (.var 3) ground := Derivable.var 3
    have formed : Typed Tower.rules (.snoc (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
        (.pi (.app tCode (.var 4)) (.var 2))) (.sigma (.var 5) ground) U0 :=
      .cumul (.sigmaForm (Derivable.var 5) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
    exact .conv (.pairIntro formed (.sort _) x g) (.symm (s_beta (Derivable.var 5))) (.sort _)
  have k := Derivable.var (R := Tower.rules)
    (Γ := .snoc (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
      (.pi (.app tCode (.var 4)) (.var 2))) 1
  have applied := Derivable.appElim k member
  have SX : Typed Tower.rules (.snoc triple.raw U0) (.app sCode (.var 3)) U0 :=
    Run.app_small (s_typed _) (Derivable.var 3)
  have kFormed : Typed Tower.rules (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)) U0 :=
    .cumul (.piForm SX (.sort _) (Derivable.var 1) (.sort _) (.sorts _ _)) collapse
  have TX : Typed Tower.rules (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
      (.app tCode (.var 4)) U0 := Run.app_small (t_typed _) (Derivable.var 4)
  have lFormed : Typed Tower.rules (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
      (.pi (.app tCode (.var 4)) (.var 2)) U0 :=
    .cumul (.piForm TX (.sort _) (Derivable.var 2) (.sort _) (.sorts _ _)) collapse
  have restFormed : Typed Tower.rules (.snoc (.snoc triple.raw U0) (.pi (.app sCode (.var 3)) (.var 1)))
      (.pi (.pi (.app tCode (.var 4)) (.var 2)) (.var 2)) U0 :=
    .cumul (.piForm lFormed (.sort _) (Derivable.var 2) (.sort _) (.sorts _ _)) collapse
  have bodyFormed : Typed Tower.rules (.snoc triple.raw U0)
      (.pi (.pi (.app sCode (.var 3)) (.var 1)) (.pi (.pi (.app tCode (.var 4)) (.var 2)) (.var 2))) U0 :=
    .cumul (.piForm kFormed (.sort _) restFormed (.sort _) (.sorts _ _)) collapse
  have allFormed : Typed Tower.rules triple.raw
      (.pi U0 (.pi (.pi (.app sCode (.var 3)) (.var 1)) (.pi (.pi (.app tCode (.var 4)) (.var 2)) (.var 2))))
      (.head large) :=
    .cumul (.piForm (.headType (.sort _)) (.sort _) bodyFormed (.sort _) (.sorts _ _)) large_of_one_zero
  exact .lamIntro allFormed (.sort _) (.lamIntro bodyFormed (.sort _) (.lamIntro restFormed (.sort _) applied))

/-! ## Negation transports; absence does not (`Controls`) -/

theorem large_of_zero_one : Tower.rules.cumulative (.sort (.max Tower.zero (.succ Tower.zero))) large := by
  change LevelTower.Cumulative (.sort (.max Tower.zero (.succ Tower.zero))) (.sort (.succ Tower.zero))
  intro valuation
  simp [LevelExpr.eval]

/-- The empty type `Π (C : U0). C`. -/
def emptyType {n : Nat} : Tower.Tm n := .pi U0 (.var 0)

theorem emptyType_formed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ emptyType (.head large) :=
  .cumul (.piForm (.headType (.sort _)) (.sort _) (Derivable.var 0) (.sort _) (.sorts _ _)) large_of_one_zero

/-- **Non-membership at `A`**: the family `λS. S A → ⊥`. -/
def negFamily {n : Nat} (A : Tower.Tm n) : Tower.Tm n :=
  .lam (.pi (.app (.var 0) (Presentation.rename wk A)) emptyType)

theorem negFamily_typed {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} (tA : Typed Tower.rules Γ A U0) :
    Typed Tower.rules Γ (negFamily A) famType := by
  have SA : Typed Tower.rules (.snoc Γ setType) (.app (.var 0) (Presentation.rename wk A)) U0 :=
    Run.app_small (Derivable.var 0) tA.weaken
  exact .lamIntro (famType_formed Γ) (.sort _)
    (.cumul (.piForm SA (.sort _) (emptyType_formed _) (.sort _) (.sorts _ _)) large_of_zero_one)

/-- **The respect term of non-membership** at the variable `X` of `X : U0, x : X, g : Ground`:
`λS T e n m. n (snd (e X) m)`. It uses the backward map. -/
def negRespect : Tower.Tm 3 :=
  .lam (.lam (.lam (.lam (.lam (.app (.var 1) (.app (.snd (.app (.var 2) (.var 7))) (.var 0)))))))

/-- The frame `X : U0, x : X, g : Ground, S T, e : setEq S T, n : S X → ⊥`. -/
abbrev negCtx7 : Tower.Ctx 7 :=
  .snoc (.snoc (.snoc (.snoc triple.raw setType) setType) (setEq (.var 1) (.var 0)))
    (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
      (negFamily (.var 2 : Tower.Tm 3))))) (.var 2))

/-- And `m : T X`. -/
abbrev negCtx8 : Tower.Ctx 8 := .snoc negCtx7 (.app (.var 2) (.var 6))

theorem neg_inner_typed :
    Typed Tower.rules negCtx8 (.app (.var 1) (.app (.snd (.app (.var 2) (.var 7))) (.var 0))) emptyType := by
  have negBody9 : Typed Tower.rules (.snoc negCtx8 setType) (.pi (.app (.var 0) (.var 8)) emptyType) (.head large) :=
    .cumul (.piForm (Run.app_small (Derivable.var 0) (Derivable.var 8)) (.sort _) (emptyType_formed _) (.sort _)
      (.sorts _ _)) large_of_zero_one
  have atS : Equal Tower.rules negCtx8 (.app (.lam (.pi (.app (.var 0) (.var 8)) emptyType)) (.var 4))
      (.pi (.app (.var 4) (.var 7)) emptyType) (.head large) :=
    Derivable.betaPi (famType_formed _) (.sort _) negBody9 (Derivable.var 4)
  have n : Typed Tower.rules negCtx8 (.var 1) (.app (.lam (.pi (.app (.var 0) (.var 8)) emptyType)) (.var 4)) :=
    Derivable.var 1
  have n' : Typed Tower.rules negCtx8 (.var 1) (.pi (.app (.var 4) (.var 7)) emptyType) := .conv n atS (.sort _)
  have e := Derivable.var (R := Tower.rules) (Γ := negCtx8) 2
  have X := Derivable.var (R := Tower.rules) (Γ := negCtx8) 7
  have m := Derivable.var (R := Tower.rules) (Γ := negCtx8) 0
  have toS := Derivable.appElim (Derivable.sndElim (Derivable.appElim e X)) m
  exact Derivable.appElim n' toS

theorem neg_transported_typed :
    Typed Tower.rules negCtx7 (.lam (.app (.var 1) (.app (.snd (.app (.var 2) (.var 7))) (.var 0))))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (negFamily (.var 2 : Tower.Tm 3)))))) (.var 2)) := by
  have formed : Typed Tower.rules negCtx7 (.pi (.app (.var 2) (.var 6)) emptyType) (.head large) :=
    .cumul (.piForm (Run.app_small (Derivable.var 2) (Derivable.var 6)) (.sort _) (emptyType_formed _) (.sort _)
      (.sorts _ _)) large_of_zero_one
  have fn := Derivable.lamIntro formed (.sort _) neg_inner_typed
  have negBody8 : Typed Tower.rules (.snoc negCtx7 setType) (.pi (.app (.var 0) (.var 7)) emptyType) (.head large) :=
    .cumul (.piForm (Run.app_small (Derivable.var 0) (Derivable.var 7)) (.sort _) (emptyType_formed _) (.sort _)
      (.sorts _ _)) large_of_zero_one
  have atT : Equal Tower.rules negCtx7 (.app (.lam (.pi (.app (.var 0) (.var 7)) emptyType)) (.var 2))
      (.pi (.app (.var 2) (.var 6)) emptyType) (.head large) :=
    Derivable.betaPi (famType_formed _) (.sort _) negBody8 (Derivable.var 2)
  exact .conv fn (.symm atT) (.sort _)

/-- **Non-membership respects extensional equality**, by the backward map: `λS T e n m. n (snd (e X) m)`
is a respect term for `λS. S X → ⊥`. So `X ∉ S` transports to `X ∉ T` by `Transport.transportBy`,
while the absence of rows of `S X` does not transport (`Controls.absence_does_not_transport`). -/
theorem negRespect_typed :
    Typed Tower.rules triple.raw negRespect (respType (negFamily (.var 2 : Tower.Tm 3))) := by
  have tP : Typed Tower.rules triple.raw (negFamily (.var 2 : Tower.Tm 3)) famType :=
    negFamily_typed (Derivable.var 2)
  have l4 := Derivable.lamIntro (respInner_formed tP) (.sort _) neg_transported_typed
  have l3 := Derivable.lamIntro (respThird_formed tP) (.sort _) l4
  have l2 := Derivable.lamIntro (respSecond_formed tP) (.sort _) l3
  exact Derivable.lamIntro (respType_formed tP) (.sort _) l2

end EqualityOnTheStep.SetTheory

#print axioms EqualityOnTheStep.SetTheory.comprehension_typed
#print axioms EqualityOnTheStep.SetTheory.comprehension_beta
#print axioms EqualityOnTheStep.SetTheory.inter_typed
#print axioms EqualityOnTheStep.SetTheory.s_is_inter
#print axioms EqualityOnTheStep.SetTheory.t_is_inter
#print axioms EqualityOnTheStep.SetTheory.inter_commutation_refused
#print axioms EqualityOnTheStep.SetTheory.setEq_refl
#print axioms EqualityOnTheStep.SetTheory.setEq_symm
#print axioms EqualityOnTheStep.SetTheory.setEq_trans
#print axioms EqualityOnTheStep.SetTheory.union_typed
#print axioms EqualityOnTheStep.SetTheory.union_inl_typed
#print axioms EqualityOnTheStep.SetTheory.negFamily_typed
#print axioms EqualityOnTheStep.SetTheory.negRespect_typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
