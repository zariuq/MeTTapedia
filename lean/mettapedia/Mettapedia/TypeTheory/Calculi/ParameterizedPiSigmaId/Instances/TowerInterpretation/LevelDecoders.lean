import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.ParametricFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment

/-!
# The decoders of the level names

A type over a variable level name `x` cannot mention the universe at `x`: a universe carries a
level expression, and `x` is a term. The two *decoders* of the names below a bound `c` supply
it. Each is a family from one check (`ParametricFamilies`):

* `univ : names c → U_c`, from the one term `U_l`: the universe at the level of a name
  (`univFamily`);
* `el : Π (x : names c). univ x → U_c`, from the one term `λ (A : U_l). A`: the type of a
  member of that universe (`elFamily`).

They are admitted over any admitted list of families (`decoders_admitted_over`), and several
pairs with different bounds live in one package.

At the name of a level expression below the bound, closed or with level parameters, the
decoders compute away: `univ (name e) = U_e` (`univ_at`) and `el (name e) A = A` (`el_at`). So
a type written with the decoders over a variable name is, at the name of a parameter, the type
written with the tower's own universes.

Positive examples.

* The polymorphic identity as a term, `λ (x : names c). λ (A : univ x). λ (a : el x A). a`,
  typed once under a variable name (`polyId_typed`); at the name of a level it is the identity
  on the universe at that level (`polyId_at`); and applied to a variable name, a member of the
  universe it names and an element, it computes to the element (`polyId_apply`), because the
  term is an abstraction. Hence the identity law for every level below the bound has one
  proof, by reflexivity: `λ x A a. refl a : Π x A a. Id (el x A) (polyId x A a) a`
  (`polyId_law`).
* The polymorphic identity as a family from one check of `λ (A : U_l). λ (a : A). a` against
  the decoder-written type at the name of the parameter (`identity_admitted`); it has the type
  of the polymorphic identity (`identity_typed'`) and at the name of a level it is the identity
  on the universe at that level (`identity_at`).
* The product of the universes at all the levels below `c` is a type at `c`
  (`allUniverses_formed`).
* **A level above.** With decoders at two bounds `c < c'` in one package, the names below `c`
  are names below `c'`, the two decoders agree at every name below `c` (`decoders_agree_at`),
  and the product of the universes below `c` is a member of the universe named by the name of
  `c` (`allUniverses_mem_above`). Over the notations below `ε₀`: the type of the families of
  types over the finite levels is a member of the universe named by `ω`
  (`finiteLevels_mem_omega`).

Negative example: a step that decodes by a code of a universe, `el s (ucode y) ⟶ univ y`,
would make the universe at a variable name a member of the next one. It does not combine with
decoding by the name: with both, the package is not Church–Rosser
(`overlap_not_churchRosser`).

Scope: the annotated judgment. At a λ-bound name the decoders are neutral, so two types
written with decoders at such a name are equal only when they are the same term up to the
equality of the terms in them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace LevelNames

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.TypeTheory.UniverseLevel
open LevelBounds (LeUnder EqUnder Admissible unbounded valid_unbounded positive_unbounded)
open LevelTower (oneBound oneBound_zero oneBound_other)

variable {L : Type}

/-! ## The two decoders -/

/-- The decoder of members under the parameter: the identity on the universe at the
parameter. -/
def elTerm : CTm (Head L) 0 := .lam (universeAt (.param 0)) (.var 0)

theorem elTerm_only : OnlyParamZero (elTerm (L := L)) := by
  intro σ τ same
  show CTm.lam (universeAt (σ 0)) (.var 0) = .lam (universeAt (τ 0)) (.var 0)
  rw [same]

/-- The polymorphic identity under the parameter. -/
def identityTerm : CTm (Head L) 0 := .lam (universeAt (.param 0)) (.lam (.var 0) (.var 0))

theorem identityTerm_only : OnlyParamZero (identityTerm (L := L)) := by
  intro σ τ same
  show CTm.lam (universeAt (σ 0)) (.lam (.var 0) (.var 0)) =
    .lam (universeAt (τ 0)) (.lam (.var 0) (.var 0))
  rw [same]

section Decoders

variable (c : L) (univ el : DeclName)

/-- **The decoder**: at the name of a level, the universe at that level, a member of the
universe at the bound. -/
abbrev univFamily : Family L := Family.uniform univ c (CU c) universesTerm

/-- **The decoder of members**: at the name of a level, the identity on the universe at that
level, as a function into the universe at the bound. -/
abbrev elFamily : Family L :=
  Family.uniform el c (.pi (.app (.const univ) (.var 0)) (CU c)) elTerm

/-- The two decoders, the decoder of members declared last. -/
abbrev decoders : List (Family L) := [elFamily c univ el, univFamily c univ]

/-- The values of the decoders mention no constant. -/
theorem decoders_constFree :
    ∀ F ∈ decoders c univ el, ∀ e : LevelExpr L, termConsts (F.body e) = [] := by
  intro F mem e
  rcases List.mem_cons.mp mem with rfl | mem
  · rfl
  · obtain rfl := List.mem_singleton.mp mem
    rfl

/-- `Π (x : names c). univ x`: the product of the universes at all the levels below `c`. -/
def allUniverses : CTm (Head L) 0 := .pi (levelsBelow (.const c)) (.app (.const univ) (.var 0))

/-- The type of the polymorphic identity at a variable name:
`Π (A : univ x). el x A → el x A`. -/
def polyIdBodyType : CTm (Head L) 1 :=
  .pi (.app (.const univ) (.var 0))
    (.pi (.app (.app (.const el) (.var 1)) (.var 0))
      (.app (.app (.const el) (.var 2)) (.var 1)))

/-- `Π (x : names c). Π (A : univ x). el x A → el x A`. -/
def polyIdType : CTm (Head L) 0 := .pi (levelsBelow (.const c)) (polyIdBodyType univ el)

/-- **The polymorphic identity as a term**:
`λ (x : names c). λ (A : univ x). λ (a : el x A). a`. -/
def polyId : CTm (Head L) 0 :=
  .lam (levelsBelow (.const c)) (.lam (.app (.const univ) (.var 0))
    (.lam (.app (.app (.const el) (.var 1)) (.var 0)) (.var 0)))

/-- **The polymorphic identity as a family**, from the one term `λ (A : U_l). λ (a : A). a`,
at the type of the polymorphic identity. -/
abbrev identityFamily (identity : DeclName) : Family L :=
  Family.uniform identity c (polyIdBodyType univ el) identityTerm

end Decoders

variable [LevelOrder L] {c : L} {univ el : DeclName}

/-! ## Admission -/

section Admission

variable {Fs : List (Family L)}

/-- The decoder is admitted over every admitted list of families that does not use its
name. -/
theorem univ_admitted_over (admitted : Admitted Fs) (univFresh : declared Fs univ = none)
    (univUnused : ∀ F' ∈ Fs, ∀ d, d < F'.bound → univ ∉ termConsts (F'.body (.const d))) :
    Admitted (univFamily c univ :: Fs) :=
  admitted_uniform admitted (.succ (.const c)) univFresh univUnused
    (fun used => absurd used List.not_mem_nil) (fun _ => rfl) universesTerm_only
    (lift_bare (universeAt_typed _))
    (lift_bare (universeAt_mem (LevelBounds.succ_le_of_lt_bound (oneBound_zero c))))

/-- The decoder at the name of a level below the bound is the universe at that level. -/
theorem univ_at_first (first : Admitted (univFamily c univ :: Fs)) {Δ : LevelBounds L}
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (univFamily c univ :: Fs))
      (.equality .nil (.app (.const univ) (levelName e)) (universeAt e) (CU c)) := by
  have computed := family_at first positive (e := e) trivial below
  have value : (univFamily c univ).body e = universeAt e := by
    show universeAt (LevelExpr.instantiate 0 e 0) = _
    rw [instantiate_zero]
  rw [value] at computed
  exact computed

/-- The identity on the universe at a level below the bound is a function from the decoder at
the name of that level into the universe at the bound. -/
theorem elBody_typed (first : Admitted (univFamily c univ :: Fs)) {Δ : LevelBounds L}
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (univFamily c univ :: Fs))
      (.typing .nil (.lam (universeAt e) (.var 0))
        (.pi (.app (.const univ) (levelName e)) (CU c))) := by
  have member : CDerivable (church Δ (univFamily c univ :: Fs))
      (.typing (.snoc .nil (universeAt e)) (.var 0) (universeAt e)) := .var 0
  have source : CDerivable (church Δ (univFamily c univ :: Fs))
      (.typing .nil (.pi (universeAt e) (universeAt e))
        (universeAt (.max (.succ e) (.succ e)))) :=
    .piForm (lift_bare (universeAt_typed e)) (.tower (.sort _)) (lift_bare (universeAt_typed e))
      (.tower (.sort _)) (.tower (.sorts _ _))
  have identity : CDerivable (church Δ (univFamily c univ :: Fs))
      (.typing .nil (.lam (universeAt e) (.var 0)) (.pi (universeAt e) (universeAt e))) :=
    .lamIntro (lift_bare (universeAt_typed e)) (.tower (.sort _)) source (.tower (.sort _)) member
  have decoded : CDerivable (church Δ (univFamily c univ :: Fs))
      (.typing .nil (.app (.const univ) (levelName e)) (CU c)) :=
    family_app_typed first below
  have target : CDerivable (church Δ (univFamily c univ :: Fs))
      (.typing .nil (.pi (.app (.const univ) (levelName e)) (CU c))
        (universeAt (.max (.const c) (.succ (.const c))))) :=
    .piForm decoded (.tower (.sort _)) (lift_bare (universeAt_typed _)) (.tower (.sort _))
      (.tower (.sorts _ _))
  exact .sub identity
    (.subPi source (.tower (.sort _)) target (.tower (.sort _))
      (.symm (univ_at_first first positive below)) (.tower (.sort _))
      (.subUniv fun ν valid => le_trans (LevelOrder.le_succ _) (below ν valid)))

/-- **The two decoders are admitted** over every admitted list of families that does not use
their names, for a bound above the least level: one check each. -/
theorem decoders_admitted_over (positive : LevelOrder.bot < c) (admitted : Admitted Fs)
    (univFresh : declared Fs univ = none)
    (univUnused : ∀ F' ∈ Fs, ∀ d, d < F'.bound → univ ∉ termConsts (F'.body (.const d)))
    (elFresh : declared Fs el = none)
    (elUnused : ∀ F' ∈ Fs, ∀ d, d < F'.bound → el ∉ termConsts (F'.body (.const d)))
    (distinct : el ≠ univ) :
    Admitted (elFamily c univ el :: univFamily c univ :: Fs) := by
  have first := univ_admitted_over (c := c) admitted univFresh univUnused
  have applied : CDerivable (church (unbounded L) (univFamily c univ :: Fs))
      (.typing (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)) (CU c)) :=
    .appElim (A := levelsBelow (.const c)) (B := CU c) (family_const_typed first) (.var 0)
  refine admitted_uniform first (.max (.const c) (.succ (.const c))) ?_ ?_
    (fun used => absurd used List.not_mem_nil) (fun _ => rfl) elTerm_only
    (.piForm applied (.tower (.sort _)) (lift_bare (universeAt_typed _)) (.tower (.sort _))
      (.tower (.sorts _ _)))
    (elBody_typed first (oneBound_positive positive)
      (LevelBounds.succ_le_of_lt_bound (oneBound_zero c)))
  · show (if el = univ then some (CTm.pi (levelsBelow (.const c)) (CU c)) else declared Fs el) =
      none
    rw [if_neg distinct]
    exact elFresh
  · intro F' mem d below used
    rcases List.mem_cons.mp mem with rfl | earlier
    · exact absurd used List.not_mem_nil
    · exact elUnused F' earlier d below used

/-- **The two decoders are admitted**, for a bound above the least level. -/
theorem decoders_admitted (positive : LevelOrder.bot < c) (distinct : el ≠ univ) :
    Admitted (decoders c univ el) :=
  decoders_admitted_over positive .nil rfl (fun _ mem => nomatch mem) rfl
    (fun _ mem => nomatch mem) distinct

end Admission

/-! ## Typings and computation of the decoders -/

section Typings

variable {Fs : List (Family L)} {Δ : LevelBounds L} {n : Nat} {Γ : CCtx (Head L) n}

/-- The decoder is a function from the names below the bound into the universe at the
bound. -/
theorem univ_typed (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ (.const univ) (.pi (levelsBelow (.const c)) (CU c))) :=
  lift_cons admitted (family_const_typed admitted.tail)

/-- **The decoder at a name below the bound is a type at the bound.** -/
theorem univ_app_typed (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    {x : CTm (Head L) n}
    (hx : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ x (levelsBelow (.const c)))) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ (.app (.const univ) x) (CU c)) :=
  .appElim (A := levelsBelow (.const c)) (B := CU c) (univ_typed admitted) hx

/-- **The decoder at the name of a level below the bound is the universe at that level**, for
closed levels and under level parameters. -/
theorem univ_at (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality Γ (.app (.const univ) (levelName e)) (universeAt e) (CU c)) :=
  CEqual.rename (ρ := fun i => i.elim0)
    (lift_cons admitted (univ_at_first admitted.tail positive below)) (fun i => i.elim0)

/-- The decoder of members: `el : Π (x : names c). univ x → U_c`. -/
theorem el_typed (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ (.const el)
        (.pi (levelsBelow (.const c)) (.pi (.app (.const univ) (.var 0)) (CU c)))) :=
  family_const_typed admitted

/-- **A member of the universe named by a name decodes to a type at the bound.** -/
theorem el_app_typed (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    {x A : CTm (Head L) n}
    (hx : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ x (levelsBelow (.const c))))
    (hA : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ A (.app (.const univ) x))) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ (.app (.app (.const el) x) A) (CU c)) :=
  .appElim (A := .app (.const univ) x) (B := CU c)
    (.appElim (A := levelsBelow (.const c)) (B := .pi (.app (.const univ) (.var 0)) (CU c))
      (el_typed admitted) hx) hA

/-- A member of the universe named by the name of a level is a member of the universe at that
level. -/
theorem member_at (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c))
    {A : CTm (Head L) n}
    (hA : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ A (.app (.const univ) (levelName e)))) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ A (universeAt e)) :=
  .conv hA (univ_at admitted positive below) (.tower (.sort _))

/-- **At the name of a level the decoder of members steps to the identity on the universe at
that level**, as a function on the universe the name names. -/
theorem el_step (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality Γ (.app (.const el) (levelName e)) (.lam (universeAt e) (.var 0))
        (.pi (.app (.const univ) (levelName e)) (CU c))) := by
  have computed := family_at_in admitted positive (e := e) trivial below Γ
  have value : (elFamily c univ el).body e = .lam (universeAt e) (.var 0) := by
    show CTm.lam (universeAt (LevelExpr.instantiate 0 e 0)) (.var 0) = _
    rw [instantiate_zero]
  rw [value] at computed
  exact computed

/-- **At the name of a level, the decoder of members is the identity**: a member of the
universe named by that name decodes to itself. The decoder steps to the identity on the
universe at the level, and the identity applied to the member computes. -/
theorem el_at (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c))
    {A : CTm (Head L) n}
    (hA : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ A (.app (.const univ) (levelName e)))) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality Γ (.app (.app (.const el) (levelName e)) A) A (CU c)) := by
  have stepped : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality Γ (.app (.const el) (levelName e)) (.lam (universeAt e) (.var 0))
        (.pi (.app (.const univ) (levelName e)) (CU c))) := el_step admitted positive below
  have applied : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality Γ (.app (.app (.const el) (levelName e)) A)
        (.app (.lam (universeAt e) (.var 0)) A) (CU c)) :=
    .appCong (A := .app (.const univ) (levelName e)) (B := CU c) stepped (.refl hA)
  have source : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing Γ (.pi (universeAt e) (universeAt e))
        (universeAt (.max (.succ e) (.succ e)))) :=
    .piForm (lift_bare (universeAt_typed e)) (.tower (.sort _)) (lift_bare (universeAt_typed e))
      (.tower (.sort _)) (.tower (.sorts _ _))
  have member : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing (.snoc Γ (universeAt e)) (.var 0) (universeAt e)) := .var 0
  have reduced : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality Γ (.app (.lam (universeAt e) (.var 0)) A) A (universeAt e)) :=
    .betaPi (A := universeAt e) (B := universeAt e) (body := .var 0) source (.tower (.sort _))
      member (member_at admitted positive below hA)
  exact .trans applied
    (.subEq reduced (.subUniv fun ν valid => le_trans (LevelOrder.le_succ _) (below ν valid)))

/-- **The product of the universes below the bound is a type at the bound.** -/
theorem allUniverses_formed (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing .nil (allUniverses c univ) (universeAt (.max (.const c) (.const c)))) :=
  .piForm (lift_bare (levelsBelow_typed _)) (.tower (.sort _))
    (univ_app_typed admitted (.var 0)) (.tower (.sort _)) (.tower (.sorts _ _))

/-! ### The polymorphic identity as a term -/

/-- The type of the polymorphic identity at a variable name is a type at the bound. -/
theorem polyIdBodyType_formed
    (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing (.snoc .nil (levelsBelow (.const c))) (polyIdBodyType univ el)
        (universeAt (.max (.const c) (.max (.const c) (.const c))))) :=
  .piForm (univ_app_typed admitted (.var 0)) (.tower (.sort _))
    (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
      (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _)))
    (.tower (.sort _)) (.tower (.sorts _ _))

/-- The type of the polymorphic identity is a type at the bound. -/
theorem polyIdType_formed (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing .nil (polyIdType c univ el)
        (universeAt (.max (.const c) (.max (.const c) (.max (.const c) (.const c)))))) :=
  .piForm (lift_bare (levelsBelow_typed _)) (.tower (.sort _)) (polyIdBodyType_formed admitted)
    (.tower (.sort _)) (.tower (.sorts _ _))

/-- **The polymorphic identity is typed**: one term, checked once under a variable name. -/
theorem polyId_typed (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing .nil (polyId c univ el) (polyIdType c univ el)) :=
  .lamIntro (lift_bare (levelsBelow_typed _)) (.tower (.sort _)) (polyIdType_formed admitted)
    (.tower (.sort _))
    (.lamIntro (univ_app_typed admitted (.var 0)) (.tower (.sort _))
      (polyIdBodyType_formed admitted) (.tower (.sort _))
      (.lamIntro (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
        (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
          (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _)) (.var 0)))

/-- **At the name of a level, the type of the polymorphic identity is the type of the identity
on the universe at that level**: the two decoders compute away. -/
theorem polyIdType_at (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality .nil
        (.pi (.app (.const univ) (levelName e))
          (.pi (.app (.app (.const el) (levelName e)) (.var 0))
            (.app (.app (.const el) (levelName e)) (.var 1))))
        (.pi (universeAt e) (.pi (.var 0) (.var 1)))
        (universeAt (.max (.const c) (.max (.const c) (.const c))))) := by
  have inner : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality (.snoc .nil (.app (.const univ) (levelName e)))
        (.pi (.app (.app (.const el) (levelName e)) (.var 0))
          (.app (.app (.const el) (levelName e)) (.var 1)))
        (.pi (.var 0) (.var 1))
        (universeAt (.max (.const c) (.const c)))) :=
    .piCong (el_at admitted positive below (.var 0)) (.tower (.sort _))
      (el_at admitted positive below (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _))
  exact .piCong (univ_at admitted positive below) (.tower (.sort _)) inner (.tower (.sort _))
    (.tower (.sorts _ _))

/-- **At the name of a level, the polymorphic identity is the identity on the universe at that
level**: `polyId (name e) : Π (A : U_e). A → A`. -/
theorem polyId_at (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs))
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing .nil (.app (polyId c univ el) (levelName e))
        (.pi (universeAt e) (.pi (.var 0) (.var 1)))) := by
  have applied : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing .nil (.app (polyId c univ el) (levelName e))
        (.pi (.app (.const univ) (levelName e))
          (.pi (.app (.app (.const el) (levelName e)) (.var 0))
            (.app (.app (.const el) (levelName e)) (.var 1))))) :=
    .appElim (A := levelsBelow (.const c)) (B := polyIdBodyType univ el) (polyId_typed admitted)
      (lift_bare (levelName_typed below))
  exact .conv applied (polyIdType_at admitted positive below) (.tower (.sort _))

/-- **At a variable name the polymorphic identity computes.** In a context with a name `x`, a
member `A` of the universe it names and an element `a` of the type `A` decodes to,
`polyId x A a ≡ a`. The term is an abstraction, so the judgment's own rule applies it at every
name, a variable included; a family computes only at the name of a level expression. -/
theorem polyId_apply (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (.app (.app (.app (polyId c univ el).liftClosed (.var 2)) (.var 1)) (.var 0))
        (.var 0) (.app (.app (.const el) (.var 2)) (.var 1))) := by
  have first : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (.app (.lam (levelsBelow (.const c)) (.lam (.app (.const univ) (.var 0))
          (.lam (.app (.app (.const el) (.var 1)) (.var 0)) (.var 0)))) (.var 2))
        (.lam (.app (.const univ) (.var 2))
          (.lam (.app (.app (.const el) (.var 3)) (.var 0)) (.var 0)))
        (.pi (.app (.const univ) (.var 2))
          (.pi (.app (.app (.const el) (.var 3)) (.var 0))
            (.app (.app (.const el) (.var 4)) (.var 1))))) :=
    .betaPi (A := levelsBelow (.const c))
      (B := .pi (.app (.const univ) (.var 0))
        (.pi (.app (.app (.const el) (.var 1)) (.var 0))
          (.app (.app (.const el) (.var 2)) (.var 1))))
      (body := .lam (.app (.const univ) (.var 0))
        (.lam (.app (.app (.const el) (.var 1)) (.var 0)) (.var 0)))
      (a := .var 2)
      (.piForm (lift_bare (levelsBelow_typed _)) (.tower (.sort _))
        (.piForm (univ_app_typed admitted (.var 0)) (.tower (.sort _))
          (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
            (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _)))
          (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _)) (.tower (.sorts _ _)))
      (.tower (.sort _))
      (.lamIntro (univ_app_typed admitted (.var 0)) (.tower (.sort _))
        (.piForm (univ_app_typed admitted (.var 0)) (.tower (.sort _))
          (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
            (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _)))
          (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _))
        (.lamIntro (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
          (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
            (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _)))
          (.tower (.sort _)) (.var 0)))
      (.var 2)
  have second : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (.app (.lam (.app (.const univ) (.var 2))
          (.lam (.app (.app (.const el) (.var 3)) (.var 0)) (.var 0))) (.var 1))
        (.lam (.app (.app (.const el) (.var 2)) (.var 1)) (.var 0))
        (.pi (.app (.app (.const el) (.var 2)) (.var 1))
          (.app (.app (.const el) (.var 3)) (.var 2)))) :=
    .betaPi (A := .app (.const univ) (.var 2))
      (B := .pi (.app (.app (.const el) (.var 3)) (.var 0))
        (.app (.app (.const el) (.var 4)) (.var 1)))
      (body := .lam (.app (.app (.const el) (.var 3)) (.var 0)) (.var 0)) (a := .var 1)
      (.piForm (univ_app_typed admitted (.var 2)) (.tower (.sort _))
        (.piForm (el_app_typed admitted (.var 3) (.var 0)) (.tower (.sort _))
          (el_app_typed admitted (.var 4) (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _)) (.tower (.sorts _ _)))
      (.tower (.sort _))
      (.lamIntro (el_app_typed admitted (.var 3) (.var 0)) (.tower (.sort _))
        (.piForm (el_app_typed admitted (.var 3) (.var 0)) (.tower (.sort _))
          (el_app_typed admitted (.var 4) (.var 1)) (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _)) (.var 0))
      (.var 1)
  have third : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.equality
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (.app (.lam (.app (.app (.const el) (.var 2)) (.var 1)) (.var 0)) (.var 0))
        (.var 0) (.app (.app (.const el) (.var 2)) (.var 1))) :=
    .betaPi (A := .app (.app (.const el) (.var 2)) (.var 1))
      (B := .app (.app (.const el) (.var 3)) (.var 2)) (body := .var 0) (a := .var 0)
      (.piForm (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _))
        (el_app_typed admitted (.var 3) (.var 2)) (.tower (.sort _)) (.tower (.sorts _ _)))
      (.tower (.sort _)) (.var 0) (.var 0)
  exact .trans (.appCong (.trans (.appCong first (.refl (.var 1))) second) (.refl (.var 0)))
    third

/-- **The identity law, proved once for every level below the bound**: the term
`λ x A a. refl a` has the type `Π (x : names c). Π (A : univ x). Π (a : el x A).
Id (el x A) (polyId x A a) a`. The proof is reflexivity, because the polymorphic identity
computes at the variable name `x`. -/
theorem polyId_law (admitted : Admitted (elFamily c univ el :: univFamily c univ :: Fs)) :
    CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing .nil
        (.lam (levelsBelow (.const c)) (.lam (.app (.const univ) (.var 0))
          (.lam (.app (.app (.const el) (.var 1)) (.var 0)) (.refl (.var 0)))))
        (.pi (levelsBelow (.const c)) (.pi (.app (.const univ) (.var 0))
          (.pi (.app (.app (.const el) (.var 1)) (.var 0))
            (.id (.app (.app (.const el) (.var 2)) (.var 1))
              (.app (.app (.app (polyId c univ el).liftClosed (.var 2)) (.var 1)) (.var 0))
              (.var 0)))))) := by
  have lifted : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (polyId c univ el).liftClosed
        (.pi (levelsBelow (.const c)) (.pi (.app (.const univ) (.var 0))
          (.pi (.app (.app (.const el) (.var 1)) (.var 0))
            (.app (.app (.const el) (.var 2)) (.var 1)))))) :=
    CTyped.rename (ρ := fun i => i.elim0) (polyId_typed admitted) (fun i => i.elim0)
  have applied : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (.app (.app (.app (polyId c univ el).liftClosed (.var 2)) (.var 1)) (.var 0))
        (.app (.app (.const el) (.var 2)) (.var 1))) :=
    .appElim (A := .app (.app (.const el) (.var 2)) (.var 1))
      (B := .app (.app (.const el) (.var 3)) (.var 2))
      (.appElim (A := .app (.const univ) (.var 2))
        (B := .pi (.app (.app (.const el) (.var 3)) (.var 0))
          (.app (.app (.const el) (.var 4)) (.var 1)))
        (.appElim (A := levelsBelow (.const c))
          (B := .pi (.app (.const univ) (.var 0))
            (.pi (.app (.app (.const el) (.var 1)) (.var 0))
              (.app (.app (.const el) (.var 2)) (.var 1))))
          lifted (.var 2))
        (.var 1))
      (.var 0)
  have element : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (.var 0) (.app (.app (.const el) (.var 2)) (.var 1))) := .var 0
  have body : CDerivable (church Δ (elFamily c univ el :: univFamily c univ :: Fs))
      (.typing
        (.snoc (.snoc (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0)))
          (.app (.app (.const el) (.var 1)) (.var 0)))
        (.refl (.var 0))
        (.id (.app (.app (.const el) (.var 2)) (.var 1))
          (.app (.app (.app (polyId c univ el).liftClosed (.var 2)) (.var 1)) (.var 0))
          (.var 0))) :=
    .conv (.reflIntro element)
      (.idCong (.refl (el_app_typed admitted (.var 2) (.var 1))) (.tower (.sort _))
        (.symm (polyId_apply admitted)) (.refl element))
      (.tower (.sort _))
  exact .lamIntro (lift_bare (levelsBelow_typed _)) (.tower (.sort _))
    (.piForm (lift_bare (levelsBelow_typed _)) (.tower (.sort _))
      (.piForm (univ_app_typed admitted (.var 0)) (.tower (.sort _))
        (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
          (.idForm (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) applied element)
          (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _)) (.tower (.sorts _ _)))
      (.tower (.sort _)) (.tower (.sorts _ _)))
    (.tower (.sort _))
    (.lamIntro (univ_app_typed admitted (.var 0)) (.tower (.sort _))
      (.piForm (univ_app_typed admitted (.var 0)) (.tower (.sort _))
        (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
          (.idForm (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) applied element)
          (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _)) (.tower (.sorts _ _)))
      (.tower (.sort _))
      (.lamIntro (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
        (.piForm (el_app_typed admitted (.var 1) (.var 0)) (.tower (.sort _))
          (.idForm (el_app_typed admitted (.var 2) (.var 1)) (.tower (.sort _)) applied element)
          (.tower (.sort _)) (.tower (.sorts _ _)))
        (.tower (.sort _)) body))

end Typings

/-! ## The polymorphic identity as a family from one check -/

section Identity

variable {identity : DeclName}

/-- **The polymorphic identity is admitted by one check**: under `l < c`,
`λ (A : U_l). λ (a : A). a` has the decoder-written type of the family at the name of `l`,
because the decoders compute at the name of a parameter. -/
theorem identity_admitted (positive : LevelOrder.bot < c) (distinct : el ≠ univ)
    (notUniv : identity ≠ univ) (notEl : identity ≠ el) :
    Admitted (identityFamily c univ el identity :: decoders c univ el) := by
  have admitted := decoders_admitted (c := c) positive distinct
  refine admitted_uniform admitted (.max (.const c) (.max (.const c) (.const c))) ?_ ?_
    (fun used => absurd used List.not_mem_nil) (fun _ => rfl) identityTerm_only
    (polyIdBodyType_formed admitted) ?_
  · refine declared_eq_none fun F mem => ?_
    rcases List.mem_cons.mp mem with rfl | mem
    · exact notEl
    · obtain rfl := List.mem_singleton.mp mem
      exact notUniv
  · intro F' mem d _ used
    rw [decoders_constFree c univ el F' mem] at used
    exact absurd used List.not_mem_nil
  · exact .conv (lift_bare (LevelNames.identity_typed (oneBound c) (.param 0)))
      (.symm (polyIdType_at admitted (oneBound_positive positive)
        (LevelBounds.succ_le_of_lt_bound (oneBound_zero c))))
      (.tower (.sort _))

/-- **The polymorphic identity as a family has the type of the polymorphic identity.** -/
theorem identity_typed' (positive : LevelOrder.bot < c) (distinct : el ≠ univ)
    (notUniv : identity ≠ univ) (notEl : identity ≠ el) {Δ : LevelBounds L} :
    CDerivable (church Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing .nil (.const identity) (polyIdType c univ el)) :=
  family_typed (identity_admitted positive distinct notUniv notEl)

/-- **At the name of a level it is the identity on the universe at that level**, at the type
`Π (A : U_e). A → A`. -/
theorem identity_at (positive : LevelOrder.bot < c) (distinct : el ≠ univ)
    (notUniv : identity ≠ univ) (notEl : identity ≠ el) {Δ : LevelBounds L}
    (positiveBounds : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (identityFamily c univ el identity :: decoders c univ el))
      (.equality .nil (.app (.const identity) (levelName e))
        (.lam (universeAt e) (.lam (.var 0) (.var 0)))
        (.pi (universeAt e) (.pi (.var 0) (.var 1)))) := by
  have admitted := identity_admitted (identity := identity) positive distinct notUniv notEl
  have computed := family_at admitted positiveBounds (e := e) trivial below
  have value : (identityFamily c univ el identity).body e =
      .lam (universeAt e) (.lam (.var 0) (.var 0)) := by
    show CTm.lam (universeAt (LevelExpr.instantiate 0 e 0)) (.lam (.var 0) (.var 0)) = _
    rw [instantiate_zero]
  rw [value] at computed
  exact .convEq computed
    (lift_cons admitted (polyIdType_at admitted.tail positiveBounds below)) (.tower (.sort _))

end Identity

/-! ## A level above -/

section Above

variable {c' : L} {univ' el' : DeclName}

/-- **Decoders at two bounds are admitted in one package.** -/
theorem twoDecoders_admitted (positive : LevelOrder.bot < c) (positive' : LevelOrder.bot < c')
    (distinct : el ≠ univ) (distinct' : el' ≠ univ') (univNotEl : univ' ≠ el)
    (univNotUniv : univ' ≠ univ) (elNotEl : el' ≠ el) (elNotUniv : el' ≠ univ) :
    Admitted (decoders c' univ' el' ++ decoders c univ el) := by
  refine decoders_admitted_over positive' (decoders_admitted positive distinct) ?_ ?_ ?_ ?_
    distinct'
  · refine declared_eq_none fun F mem => ?_
    rcases List.mem_cons.mp mem with rfl | mem
    · exact univNotEl
    · obtain rfl := List.mem_singleton.mp mem
      exact univNotUniv
  · intro F' mem d _ used
    rw [decoders_constFree c univ el F' mem] at used
    exact absurd used List.not_mem_nil
  · refine declared_eq_none fun F mem => ?_
    rcases List.mem_cons.mp mem with rfl | mem
    · exact elNotEl
    · obtain rfl := List.mem_singleton.mp mem
      exact elNotUniv
  · intro F' mem d _ used
    rw [decoders_constFree c univ el F' mem] at used
    exact absurd used List.not_mem_nil

/-- **The decoders at two bounds agree at the name of every level below the smaller bound.** -/
theorem decoders_agree_at (lower : c ≤ c')
    (admitted : Admitted (decoders c' univ' el' ++ decoders c univ el)) {Δ : LevelBounds L}
    (positive : Δ.Positive) {e : LevelExpr L} (below : LeUnder Δ (.succ e) (.const c)) :
    CDerivable (church Δ (decoders c' univ' el' ++ decoders c univ el))
      (.equality .nil (.app (.const univ) (levelName e)) (.app (.const univ') (levelName e))
        (CU c')) := by
  have atLower : CDerivable (church Δ (decoders c' univ' el' ++ decoders c univ el))
      (.equality .nil (.app (.const univ) (levelName e)) (universeAt e) (CU c)) :=
    lift_append (Gs := decoders c' univ' el') admitted
      (univ_at admitted.tail.tail positive below)
  have atUpper := univ_at (Γ := .nil) admitted positive (e := e)
    (fun ν valid => le_trans (below ν valid) lower)
  exact .trans (.subEq atLower (.subUniv fun _ _ => lower)) (.symm atUpper)

/-- **The product of the universes below a bound is a member of the universe named by the name
of that bound**, in the package with decoders at a greater bound. -/
theorem allUniverses_mem_above (strict : c < c')
    (admitted : Admitted (decoders c' univ' el' ++ decoders c univ el)) :
    CDerivable (church (unbounded L) (decoders c' univ' el' ++ decoders c univ el))
      (.typing .nil (allUniverses c univ) (.app (.const univ') (levelName (.const c)))) := by
  have formed : CDerivable (church (unbounded L) (decoders c' univ' el' ++ decoders c univ el))
      (.typing .nil (allUniverses c univ) (universeAt (.max (.const c) (.const c)))) :=
    lift_append (Gs := decoders c' univ' el') admitted (allUniverses_formed admitted.tail.tail)
  have atName := univ_at (Γ := .nil) admitted positive_unbounded (e := .const c)
    (fun _ _ => LevelOrder.succ_le_of_lt strict)
  have narrowed : CDerivable
      (church (unbounded L) (decoders c' univ' el' ++ decoders c univ el))
      (.typing .nil (allUniverses c univ) (CU c)) :=
    .sub formed (.subUniv fun _ _ => le_of_eq (max_self c))
  exact .conv narrowed (.symm atName) (.tower (.sort _))

end Above

/-! ## Negative example: decoding by a code of a universe

To make the universe at a variable name a member of the next one, the package would need a
code `ucode y` of the universe named by `y`, decoded by `el s (ucode y) ⟶ univ y`. That step
decodes by its second argument, and the decoder of members decodes by the first. -/

section CodeDecoding

variable (c : L) (univ el ucode : DeclName)

/-- The steps of the decoders together with decoding by a code of a universe. -/
inductive OverlapStep : {n : Nat} → Tm (Head L) n → Tm (Head L) n → Prop
  | base {n : Nat} {l r : Tm (Head L) n} : Step (decoders c univ el) l r → OverlapStep l r
  | code {n : Nat} (s y : Tm (Head L) n) :
      OverlapStep (.app (.app (.const el) s) (.app (.const ucode) y)) (.app (.const univ) y)

/-- The package of the decoders with decoding by a code added. -/
def overlapRules : Rules (Head L) :=
  { baseRules (unbounded L) with
    constantType := fun n => (declared (decoders c univ el) n).map CTm.erase
    computation :=
      { step := OverlapStep c univ el ucode
        rename := by
          intro n m ρ left right step
          cases step with
          | base s => exact .base ((computation (decoders c univ el)).rename ρ s)
          | code s y => exact .code _ _
        substitute := by
          intro n m σ left right step
          cases step with
          | base s => exact .base ((computation (decoders c univ el)).substitute σ s)
          | code s y => exact .code _ _ } }

variable {c univ el ucode}

/-- A variable is normal. -/
theorem overlap_var_normal {n : Nat} (i : Fin n) :
    ConstructorSystem.Normal (overlapRules c univ el ucode) (.var i : Tm (Head L) n) := by
  intro target step
  cases step with
  | root rootStep =>
    cases rootStep with
    | base s => cases s

/-- The code of the universe named by a variable is normal. -/
theorem overlap_code_normal {n : Nat} (i : Fin n) :
    ConstructorSystem.Normal (overlapRules c univ el ucode)
      (.app (.const ucode) (.var i) : Tm (Head L) n) := by
  refine ConstructorSystem.Normal.app (ConstructorSystem.Normal.const ucode ?_)
    (overlap_var_normal i) (fun body impossible => nomatch impossible) ?_
  · intro target rootStep
    cases rootStep with
    | base s => cases s
  · intro target rootStep
    cases rootStep with
    | base s => exact Step.not_at_var s

/-- The decoder at a variable name is normal. -/
theorem overlap_univ_normal {n : Nat} (i : Fin n) :
    ConstructorSystem.Normal (overlapRules c univ el ucode)
      (.app (.const univ) (.var i) : Tm (Head L) n) := by
  refine ConstructorSystem.Normal.app (ConstructorSystem.Normal.const univ ?_)
    (overlap_var_normal i) (fun body impossible => nomatch impossible) ?_
  · intro target rootStep
    cases rootStep with
    | base s => cases s
  · intro target rootStep
    cases rootStep with
    | base s => exact Step.not_at_var s

/-- **Decoding by a code does not combine with decoding by the name**: with both steps the
package is not Church–Rosser. At the name of a level, `el (name d) (ucode x)` reduces to
`ucode x` by the name and to `univ x` by the code, and at a variable `x` both are normal. -/
theorem overlap_not_churchRosser (distinct : ucode ≠ univ) (d : L) :
    ¬ ConversionCoherence.ChurchRosser (overlapRules c univ el ucode) := by
  intro churchRosser
  have decoded : StepCore (overlapRules c univ el ucode).computation
      (overlapRules c univ el ucode).headEq
      (.app (.app (.const el) (.head (.name (.const d)))) (.app (.const ucode) (.var 0)) :
        Tm (Head L) 1)
      (.app (.lam (.var 0)) (.app (.const ucode) (.var 0))) :=
    .congAppFun (.root (.base
      (Step.family (F := elFamily c univ el) (e := .const d) (.head _) trivial)))
  have applied : StepCore (overlapRules c univ el ucode).computation
      (overlapRules c univ el ucode).headEq
      (.app (.lam (.var 0)) (.app (.const ucode) (.var 0)) : Tm (Head L) 1)
      (.app (.const ucode) (.var 0)) :=
    .betaPi (.var 0) (.app (.const ucode) (.var 0))
  have byCode : StepCore (overlapRules c univ el ucode).computation
      (overlapRules c univ el ucode).headEq
      (.app (.app (.const el) (.head (.name (.const d)))) (.app (.const ucode) (.var 0)) :
        Tm (Head L) 1)
      (.app (.const univ) (.var 0)) := .root (.code _ _)
  obtain ⟨common, fromCode, fromUniv⟩ := churchRosser (n := 1)
    (.trans _ _ _ (.symm _ _ (.trans _ _ _ (.rel _ _ decoded) (.rel _ _ applied)))
      (.rel _ _ byCode))
  have atCode := ConstructorSystem.Normal.stepStar (overlap_code_normal 0) fromCode
  have atUniv := ConstructorSystem.Normal.stepStar (overlap_univ_normal 0) fromUniv
  have same : (.app (.const ucode) (.var 0) : Tm (Head L) 1) =
      .app (.const univ) (.var 0) := atCode.symm.trans atUniv
  cases same
  exact distinct rfl

end CodeDecoding

/-! ## Over the notations below `ε₀` -/

/-- Over the notations: the decoder at the name of the level `7` is the universe at `7`, in the
universe at `ω`. -/
theorem univ_seven_equal :
    CDerivable
      (church (unbounded Level)
        (decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.equality .nil
        (.app (.const (.str .anonymous "univ")) (levelName (.const (Level.ofNat 7))))
        (universeAt (.const (Level.ofNat 7))) (CU Level.omega)) :=
  univ_at (decoders_admitted Level.isLimit_omega.1 (by decide)) positive_unbounded
    (fun _ _ => LevelOrder.succ_le_of_lt (Level.ofNat_lt_omega 7))

/-- Over the notations: the polymorphic identity over the finite levels, as a family from one
check, is the identity on the universe at `7` at the name of `7`. -/
theorem finiteIdentity_at_seven :
    CDerivable
      (church (unbounded Level)
        (identityFamily Level.omega (.str .anonymous "univ") (.str .anonymous "el")
            (.str .anonymous "identity") ::
          decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.equality .nil
        (.app (.const (.str .anonymous "identity")) (levelName (.const (Level.ofNat 7))))
        (.lam (universeAt (.const (Level.ofNat 7))) (.lam (.var 0) (.var 0)))
        (.pi (universeAt (.const (Level.ofNat 7))) (.pi (.var 0) (.var 1)))) :=
  identity_at Level.isLimit_omega.1 (by decide) (by decide) (by decide) positive_unbounded
    (fun _ _ => LevelOrder.succ_le_of_lt (Level.ofNat_lt_omega 7))

/-- **Over the notations, the type of the families of types over the finite levels is a member
of the universe named by `ω`**, in the package with decoders below `ω` and below `ω + 1`. -/
theorem finiteLevels_mem_omega :
    CDerivable
      (church (unbounded Level)
        (decoders (LevelOrder.succ Level.omega) (.str .anonymous "univAbove")
            (.str .anonymous "elAbove") ++
          decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.typing .nil (allUniverses Level.omega (.str .anonymous "univ"))
        (.app (.const (.str .anonymous "univAbove")) (levelName (.const Level.omega)))) :=
  allUniverses_mem_above (LevelOrder.lt_succ Level.omega)
    (twoDecoders_admitted Level.isLimit_omega.1
      (lt_trans Level.isLimit_omega.1 (LevelOrder.lt_succ Level.omega))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

end LevelNames
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
