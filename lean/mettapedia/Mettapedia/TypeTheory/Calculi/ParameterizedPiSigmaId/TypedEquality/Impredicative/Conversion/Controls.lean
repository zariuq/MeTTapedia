import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Reading

/-!
# Controls for equality candidates

Positive:

* the identity function realizes every implication `X ⇒ X`, at the realizer
  type `Π D D` of every type `D` (`lam_var_arrow`): the function space is
  inhabited by the expected realizer, with `E` relating it to itself by
  extensionality at a fresh variable;
* the universe tower `U₀ : U₁ : …`, cumulative, with no declared constant, is a
  realizer side: its generic equality is typed equality, and the facts about
  weak-head forms come from the one-sided model (`Tower.side`). There the
  identity function realizes `X ⇒ X` at `Π U₀ U₀` for every candidate `X`
  (`Tower.lam_var_arrow`);
* the realizers of numbers and the quantification of the equality reading are
  checked against their shape-by-shape and clause-by-clause readings in
  `Reading` (`ecand_numReal`, `ecand_real_num`,
  `equalityReading_allMeaning_pi`, `equalityReading_impMeaning_pi`).

Negative:

* in every realizer side with a typed head, the identity candidate of a
  proposition is not `top` (`ident_ne_top`). At the head's type, a universe,
  `top` relates the head to itself, but that type is no identity type, and
  there the identity candidate relates only terms that reduce to neutral
  terms. In the universe tower this gives `Tower.ident_true_ne_top`;
* where `top` is included in the identity candidate of a true proposition,
  every typed term that `E` relates to itself reaches a reflexivity proof or a
  neutral term (`canonical_of_top_le_ident`, `canonical_of_ident_eq_top`). At an
  identity type that is the canonical-forms fact, a property of the realizer
  side and not of the construction.

So `ident True = top` is no law of the realizer algebra of equality candidates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {T : RealizerSide Head L}

/-! ## The identity function -/

/-- Applications of the identity function, after a renaming, to arguments
related by `X` are related by `X`, at the instantiated codomain of `Π D D`. -/
theorem lam_var_app (X : ECand T) {m : Nat} {Δ : Ctx Head m} {D : Tm Head m} {u : Head}
    (hu : T.R.isUniverse u) (hD : Typed T.R Δ D (.head u)) {k : Nat} {Θ : Ctx Head k}
    {ρ : Ren m k} (ren : CtxRen Δ Θ ρ) {s s' : Tm Head k}
    (hs : X.rel Θ (Presentation.rename ρ D) s s') :
    X.rel Θ (inst0 s (Presentation.rename (liftRen ρ) (Presentation.rename wk D)))
      (.app (Presentation.rename ρ (.lam (.var 0))) s)
      (.app (Presentation.rename ρ (.lam (.var 0))) s') := by
  obtain ⟨w, join⟩ := T.levels.join_exists hu hu
  have hw := (T.levels.join_level join).1
  have hD' : Typed T.R Θ (Presentation.rename ρ D) (.head u) := Typed.rename hD ren
  have hPi : Typed T.R Θ (.pi (Presentation.rename ρ D)
      (Presentation.rename wk (Presentation.rename ρ D))) (.head w) :=
    .piForm hD' hu (Typed.weaken hD') hu join
  have beta : ∀ {a : Tm Head k}, Typed T.R Θ a (Presentation.rename ρ D) →
      RedTm T.R T.roles Θ (.app (.lam (.var 0)) a) a (Presentation.rename ρ D) := by
    intro a ha
    have red := RedTm.beta (roles := T.roles) hPi hw (Derivable.var 0) ha
    rw [inst0_rename_wk] at red
    exact red
  rw [rename_liftRen_wk, inst0_rename_wk]
  exact X.expand (beta (X.typed hs).1) (beta (X.typed hs).2) hs

/-- **The identity function realizes every implication `X ⇒ X`**, at the
realizer type `Π D D` of every type `D`. -/
theorem lam_var_arrow (X : ECand T) {m : Nat} {Δ : Ctx Head m} {D : Tm Head m} {u : Head}
    (hu : T.R.isUniverse u) (hD : Typed T.R Δ D (.head u)) :
    ((ecandAlgebra T).arrow X X).rel Δ (.pi D (Presentation.rename wk D)) (.lam (.var 0))
      (.lam (.var 0)) := by
  obtain ⟨w, join⟩ := T.levels.join_exists hu hu
  have hw := (T.levels.join_level join).1
  have hPi : Typed T.R Δ (.pi D (Presentation.rename wk D)) (.head w) :=
    .piForm hD hu (Typed.weaken hD) hu join
  have hLam : Typed T.R Δ (.lam (.var 0)) (.pi D (Presentation.rename wk D)) :=
    .lamIntro hPi hw (Derivable.var 0)
  have normal : FunNf T Δ (.pi D (Presentation.rename wk D)) (.lam (.var 0)) :=
    ⟨_, .refl hLam, .inl ⟨_, rfl⟩⟩
  have app : AppClause X X Δ D (Presentation.rename wk D) (.lam (.var 0)) (.lam (.var 0)) := by
    intro k Θ ρ world s s' hs
    exact lam_var_app X hu hD world.1 hs
  have body : T.E.convTm (.snoc Δ D) (.app (Presentation.rename wk (.lam (.var 0))) (.var 0))
      (.app (Presentation.rename wk (.lam (.var 0))) (.var 0)) (Presentation.rename wk D) := by
    have h := lam_var_app X hu hD (CtxRen.wk Δ D) (X.var 0 (Derivable.var 0))
    rw [rename_liftRen_wk, inst0_rename_wk] at h
    exact X.escape h
  have eta := T.laws.convTm_etaPi ⟨u, hu, hD⟩ ⟨u, hu, Typed.weaken hD⟩ hLam (.inl ⟨_, rfl⟩) hLam
    (.inl ⟨_, rfl⟩) body
  exact (ECand.piOver_rel_pi (d := fun _ : Unit => X) (c := fun _ => X)
    (RedTy.refl ⟨w, hw, hPi⟩)).mpr ⟨normal, normal, eta, fun _ => app⟩

/-! ## The identity candidate is not `top` -/

/-- **The identity candidate of a proposition is not `top`**, in every realizer
side with a typed head: at the head's type, a universe, `top` relates the head
to itself, while the identity candidate relates there only terms reducing to
neutral terms. -/
theorem ident_ne_top {u v : Head} (typing : T.R.headTyping u v) (P : Prop) :
    ECand.ident T P ≠ ECand.top T := by
  intro e
  have hv : T.R.isUniverse v := T.levels.ground_typing typing
  have tu : Typed T.R (.nil : Ctx Head 0) (.head u) (.head v) := .headType typing
  have related : (ECand.ident T P).rel .nil (.head v) (.head u) (.head u) := by
    rw [e]
    exact ⟨tu, tu, T.laws.convTm_head (.inl rfl) tu tu hv⟩
  rcases related with ne | ⟨⟨D, a, b, hA⟩, -⟩
  · exact (ne.left_whnf (.refl tu) (head_whnf T.shape u)).not_former.1 u rfl
  · exact nomatch WhRed.eq_of_whnf (S := T.toSetting) (head_whnf T.shape v) hA.red

/-- **Including `top` in the identity candidate of a true proposition forces
canonical forms**: at a realizer type where it holds, every typed term that `E`
relates to itself reaches, typed, a reflexivity proof or a neutral term. -/
theorem canonical_of_top_le_ident {m : Nat} {Δ : Ctx Head m} {A : Tm Head m}
    (le : ∀ t t', (ECand.top T).rel Δ A t t' → (ECand.ident T True).rel Δ A t t')
    {t : Tm Head m} (ht : Typed T.R Δ t A) (self : T.E.convTm Δ t t A) :
    ∃ w, RedTm T.R T.roles Δ t w A ∧ ((∃ x, w = .refl x) ∨ Neutral T.roles w) := by
  rcases le t t ⟨ht, ht, self⟩ with ⟨w, -, r, -, nw, -⟩ | ⟨-, ⟨x, r⟩, -⟩
  · exact ⟨w, r, .inr nw⟩
  · exact ⟨_, r, .inl ⟨x, rfl⟩⟩

/-- If the identity candidate of a true proposition were `top`, every typed term
that `E` relates to itself, at every realizer type, would reach a reflexivity
proof or a neutral term. -/
theorem canonical_of_ident_eq_top (e : ECand.ident T True = ECand.top T) {m : Nat}
    {Δ : Ctx Head m} {A t : Tm Head m} (ht : Typed T.R Δ t A) (self : T.E.convTm Δ t t A) :
    ∃ w, RedTm T.R T.roles Δ t w A ∧ ((∃ x, w = .refl x) ∨ Neutral T.roles w) :=
  canonical_of_top_le_ident (fun t t' h => by rw [e]; exact h) ht self

/-! ## A realizer side: the universe tower -/

namespace Tower

/-- The universe tower `U₀ : U₁ : …`, cumulative, with no declared constant and
no computation. -/
def rules : Rules Nat where
  headTyping u v := v = u + 1
  isUniverse _ := True
  join u v w := w = max u v
  cumulative u v := u ≤ v
  headEq _ _ := False

/-- The levels of the tower: `Uₙ` has level `n`. -/
def levels : LevelModel rules Nat where
  level u := u
  successor := fun {u} _ => ⟨u + 1, trivial, rfl, rfl⟩
  universe_typing := fun _ typing => ⟨trivial, typing⟩
  ground_typing := fun _ => trivial
  cumulative_universe := fun le => ⟨trivial, trivial, le⟩
  headEq_level := fun e => nomatch e
  join_level := fun join => ⟨trivial, join⟩
  join_exists := fun {u v} _ _ => ⟨max u v, rfl⟩
  join_upper := fun {u v w} join => by
    change w = max u v at join
    subst join
    exact ⟨le_max_left u v, le_max_right u v⟩
  cumulative_refl := fun {u} _ => le_refl u
  headEq_symm := fun e => nomatch e
  headEq_trans := fun e _ => nomatch e
  universe_decided := fun _ => .inl trivial

/-- The tower has no root computation. -/
theorem shape : RootShape rules (fun _ => .rigid) where
  spine := fun step => nomatch step
  deterministic := fun step _ => nomatch step

/-- The normalization setting of the tower, with typed equality as its generic
equality. -/
def setting : Setting Nat Nat where
  R := rules
  roles := fun _ => .rigid
  E := declarative rules
  levels := levels
  shape := shape
  constructors := ConstructorsDeclared.of_no_inductive fun _ _ role => nomatch role

/-- The tower declares no constant, so every declared constant is semantic. -/
theorem constants : SemanticConstants setting := fun declared _ _ => nomatch declared

/-- **The universe tower is a realizer side**: typed equality has the laws of a
generic equality, and the facts about weak-head forms of types are consequences
of the one-sided model. -/
def side : RealizerSide Nat Nat where
  toSetting := setting
  laws := declarative_laws _ levels
  reduce := declarative_convTm_reduce
  facts := FormFacts.ofSemantic (declarative_laws _ levels) constants

/-- In the universe tower, the identity function realizes `X ⇒ X` at `Π U₀ U₀`,
for every candidate `X`. -/
theorem lam_var_arrow (X : ECand side) :
    ((ecandAlgebra side).arrow X X).rel .nil (.pi (.head 0) (.head 0)) (.lam (.var 0))
      (.lam (.var 0)) :=
  Conversion.lam_var_arrow X (u := 1) trivial (.headType rfl)

/-- **In the universe tower, the identity candidate of a true proposition is not
`top`.** -/
theorem ident_true_ne_top : (ecandAlgebra side).ident True ≠ (ecandAlgebra side).top :=
  ident_ne_top (T := side) (u := 0) (v := 1) rfl True

end Tower

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
