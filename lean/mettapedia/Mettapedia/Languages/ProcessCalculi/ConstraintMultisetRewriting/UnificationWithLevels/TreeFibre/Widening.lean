import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativePrincipal

/-!
# The meet lemma on normal forms: widening keeps a type small above the widened declarations

A normal type over `x : U_{pB}` may be a type of a smaller universe `U_c` once `x` is narrowed to `U_{pA}`. Its
universe over the wide declaration is then at most the larger of `c` and `pB`: the declaration of `x` enters a
normal type only through `x` itself at a type position, and every other part of the type keeps its universe.

* `NarrowsBelow R u Γ Δ`: `Δ` is `Γ` with some universe declarations lowered, each of `Γ`'s lying below `u`.
* **`typed_widen`**: a normal type of `Γ` that is a type of `U_u` in such a `Δ` is a type of `U_u` in `Γ`. By
  structure: universes and other heads keep their universe; Π, Σ and identity types are formed again at `u` from
  their parts; a neutral type headed by a lowered declaration is that declaration, of a universe below `u`; any
  other neutral type keeps its principal type (`spine_small_wide`).
* **`small_of_widen`**, the meet lemma: a type `t` of `U_v` over `Γ` that is equal over `Δ` to a type of `U_u` is
  equal over `Γ` to a type of `U_u`, its normal form.

The hypothesis that the widened declarations lie below `u` is needed: over `x : U1`, the variable `x` is equal over
`x : U0` to a type of `U0` and is a type of no universe below `U1` (the cross store, `cross_no_principal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Narrowings below a universe -/

section Narrowings

variable {R : Rules Head}

/-- **`Δ` narrows `Γ` below `u`**: the same telescope, except at universe declarations, where `Δ` declares a universe
below `Γ`'s and `Γ`'s lies below `u`. -/
inductive NarrowsBelow (R : Rules Head) (u : Head) : {n : Nat} → Ctx Head n → Ctx Head n → Prop where
  | nil : NarrowsBelow R u .nil .nil
  | same {n : Nat} {Γ Δ : Ctx Head n} (A : Tm Head n) : NarrowsBelow R u Γ Δ →
      NarrowsBelow R u (.snoc Γ A) (.snoc Δ A)
  | lower {n : Nat} {Γ Δ : Ctx Head n} {w v : Head} : NarrowsBelow R u Γ Δ → R.cumulative v w → R.cumulative w u →
      NarrowsBelow R u (.snoc Γ (.head w)) (.snoc Δ (.head v))

/-- Every telescope narrows itself below every universe. -/
theorem NarrowsBelow.refl (u : Head) : ∀ {n : Nat} (Γ : Ctx Head n), NarrowsBelow R u Γ Γ
  | _, .nil => .nil
  | _, .snoc Γ A => .same A (NarrowsBelow.refl u Γ)

/-- A narrowing below a universe is a narrowing. -/
theorem NarrowsBelow.narrows {u : Head} {n : Nat} {Γ Δ : Ctx Head n} (nb : NarrowsBelow R u Γ Δ) :
    CtxNarrows R Γ Δ := by
  induction nb with
  | nil => exact .nil
  | same A _ ih => exact .same A ih
  | lower _ c _ ih => exact .lower ih c

/-- Every declaration of `Δ` is the one of `Γ`, or a universe below `Γ`'s, which lies below `u`. -/
theorem NarrowsBelow.lookup {u : Head} {n : Nat} {Γ Δ : Ctx Head n} (nb : NarrowsBelow R u Γ Δ) :
    ∀ i, Ctx.lookup Δ i = Ctx.lookup Γ i ∨
      ∃ w v, Ctx.lookup Γ i = .head w ∧ Ctx.lookup Δ i = .head v ∧ R.cumulative v w ∧ R.cumulative w u := by
  induction nb with
  | nil => intro i; exact i.elim0
  | same A _ ih =>
      intro i
      refine Fin.cases (.inl rfl) (fun j => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih j with same | ⟨w, v, eΓ, eΔ, c, cu⟩
      · exact .inl (by rw [same])
      · exact .inr ⟨w, v, by rw [eΓ]; rfl, by rw [eΔ]; rfl, c, cu⟩
  | lower _ c cu ih =>
      intro i
      refine Fin.cases (.inr ⟨_, _, rfl, rfl, c, cu⟩) (fun j => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih j with same | ⟨w, v, eΓ, eΔ, c', cu'⟩
      · exact .inl (by rw [same])
      · exact .inr ⟨w, v, by rw [eΓ]; rfl, by rw [eΔ]; rfl, c', cu'⟩

end Narrowings

/-! ## Widening -/

section Widening

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts algebra in
/-- **Widening keeps a normal type small above the widened declarations**: a normal type of `Γ` that is a type of
`U_u` in a narrowing of `Γ` below `u` is a type of `U_u` in `Γ`. -/
theorem typed_widen : ∀ {n : Nat} (V : Tm Head n) {Γ Δ : Ctx Head n} {u : Head}, S.R.isUniverse u →
    NarrowsBelow S.R u Γ Δ → CtxFormed S.R Γ → CtxFormed S.R Δ → Long S.R S.roles (.type Γ V) →
    Typed S.R Δ V (.head u) → Typed S.R Γ V (.head u) := by
  intro n V
  induction V with
  | var i =>
      intro Γ Δ u _ nb formedΓ formedΔ long small
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | var _ e =>
              rcases nb.lookup i with same | ⟨w, _, eΓ, _, _, cu⟩
              · exact spine_small_wide facts algebra nb.narrows formedΓ formedΔ (.var i e)
                  (.var i (by rw [same]; exact typeEq_narrow nb.narrows e)) htop le small
              · have typed : Typed S.R Γ (.var i) (.head w) := by
                  have t := Derivable.var (R := S.R) (Γ := Γ) i
                  rw [eΓ] at t
                  exact t
                exact Derivable.cumul typed cu
  | const c =>
      intro Γ Δ u _ nb formedΓ formedΔ long small
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | const role declared typed e =>
              exact spine_small_wide facts algebra nb.narrows formedΓ formedΔ (.const role declared typed e)
                (.const role declared (typed_narrow nb.narrows typed) (typeEq_narrow nb.narrows e)) htop le small
  | head h =>
      intro Γ Δ u hu _ _ formedΔ _ small
      obtain ⟨above, typing, c⟩ := head_typed_cumulative facts algebra formedΔ hu small
      exact Derivable.cumul (Derivable.headType typing) c
  | pi A B ihA ihB =>
      intro Γ Δ u hu nb formedΓ formedΔ long small
      cases long with
      | pi lA lB _ =>
          have generation : GenerationAt S.R Δ (.pi A B) (.head u) := Typed.generation small
          obtain ⟨u₁, u₂, w, tA, _, tB, _, join, le⟩ := generation
          have cw : S.R.cumulative w u :=
            typeLe_head_cumulative facts algebra formedΔ (S.levels.join_level join).1 hu le
          obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
          have isA : IsType S.R Γ A := lA.isType
          have tA' := ihA hu nb formedΓ formedΔ lA (Derivable.cumul tA (algebra.trans c₁ cw))
          have tB' := ihB hu (nb.same A) (formedΓ.snoc isA) (formedΔ.snoc (isType_narrow nb.narrows isA)) lB
            (Derivable.cumul tB (algebra.trans c₂ cw))
          obtain ⟨w', join'⟩ := S.levels.join_exists hu hu
          exact Derivable.cumul (Derivable.piForm tA' hu tB' hu join')
            (algebra.join_least join' (S.levels.cumulative_refl hu) (S.levels.cumulative_refl hu))
      | neutralType ls _ _ => cases ls
  | sigma A B ihA ihB =>
      intro Γ Δ u hu nb formedΓ formedΔ long small
      cases long with
      | sigma lA lB _ =>
          have generation : GenerationAt S.R Δ (.sigma A B) (.head u) := Typed.generation small
          obtain ⟨u₁, u₂, w, tA, _, tB, _, join, le⟩ := generation
          have cw : S.R.cumulative w u :=
            typeLe_head_cumulative facts algebra formedΔ (S.levels.join_level join).1 hu le
          obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
          have isA : IsType S.R Γ A := lA.isType
          have tA' := ihA hu nb formedΓ formedΔ lA (Derivable.cumul tA (algebra.trans c₁ cw))
          have tB' := ihB hu (nb.same A) (formedΓ.snoc isA) (formedΔ.snoc (isType_narrow nb.narrows isA)) lB
            (Derivable.cumul tB (algebra.trans c₂ cw))
          obtain ⟨w', join'⟩ := S.levels.join_exists hu hu
          exact Derivable.cumul (Derivable.sigmaForm tA' hu tB' hu join')
            (algebra.join_least join' (S.levels.cumulative_refl hu) (S.levels.cumulative_refl hu))
      | neutralType ls _ _ => cases ls
  | id A a b ihA _ _ =>
      intro Γ Δ u hu nb formedΓ formedΔ long small
      cases long with
      | id lA la lb _ =>
          have generation : GenerationAt S.R Δ (.id A a b) (.head u) := Typed.generation small
          obtain ⟨u₁, tA, hu₁, _, _, le⟩ := generation
          have c : S.R.cumulative u₁ u := typeLe_head_cumulative facts algebra formedΔ hu₁ hu le
          exact Derivable.idForm (ihA hu nb formedΓ formedΔ lA (Derivable.cumul tA c)) hu la.typed lb.typed
      | neutralType ls _ _ => cases ls
  | lam _ _ =>
      intro Γ Δ u _ _ _ _ long _
      cases long with
      | neutralType ls _ _ => cases ls
  | app f a _ _ =>
      intro Γ Δ u _ nb formedΓ formedΔ long small
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | app lf eF la eU =>
              rcases Long.narrow facts lf nb.narrows formedΓ formedΔ with kept | ⟨_, _, e, _, _⟩
              · exact spine_small_wide facts algebra nb.narrows formedΓ formedΔ (.app lf eF la eU)
                  (.app kept (typeEq_narrow nb.narrows eF) (Long.term_narrow facts la nb.narrows formedΓ formedΔ)
                    (typeEq_narrow nb.narrows eU)) htop le small
              · exact absurd (TypeEq.trans S.levels eF.symm e) (TypeEq.pi_ne_head facts formedΓ)
  | pair _ _ _ _ =>
      intro Γ Δ u _ _ _ _ long _
      cases long with
      | neutralType ls _ _ => cases ls
  | fst p _ =>
      intro Γ Δ u _ nb formedΓ formedΔ long small
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | fst lp eP eU =>
              rcases Long.narrow facts lp nb.narrows formedΓ formedΔ with kept | ⟨_, _, e, _, _⟩
              · exact spine_small_wide facts algebra nb.narrows formedΓ formedΔ (.fst lp eP eU)
                  (.fst kept (typeEq_narrow nb.narrows eP) (typeEq_narrow nb.narrows eU)) htop le small
              · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedΓ)
  | snd p _ =>
      intro Γ Δ u _ nb formedΓ formedΔ long small
      cases long with
      | neutralType ls htop le =>
          cases ls with
          | snd lp eP eU =>
              rcases Long.narrow facts lp nb.narrows formedΓ formedΔ with kept | ⟨_, _, e, _, _⟩
              · exact spine_small_wide facts algebra nb.narrows formedΓ formedΔ (.snd lp eP eU)
                  (.snd kept (typeEq_narrow nb.narrows eP) (typeEq_narrow nb.narrows eU)) htop le small
              · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedΓ)
  | refl _ _ =>
      intro Γ Δ u _ _ _ _ long _
      cases long with
      | neutralType ls _ _ => cases ls

include facts roots heads algebra rigid complete in
/-- **The meet lemma on normal forms.** A type `t` of `U_v` over `Γ` that is equal, over a narrowing of `Γ` below
`u`, to a type of `U_u` is equal over `Γ`, at `U_v`, to a type of `U_u`: its normal form. -/
theorem small_of_widen {n : Nat} {Γ Δ : Ctx Head n} {u v : Head} (hu : S.R.isUniverse u) (hv : S.R.isUniverse v)
    (nb : NarrowsBelow S.R u Γ Δ) (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) {t s : Tm Head n}
    (tt : Typed S.R Γ t (.head v)) (ts : Typed S.R Δ s (.head u)) (equal : TypeEq S.R Δ s t) :
    ∃ N, Typed S.R Γ N (.head u) ∧ Equal S.R Γ t N (.head v) := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedΓ ⟨v, hv, tt⟩
  obtain ⟨_, eZ⟩ := atZ hv tt
  have smallΔ : Typed S.R Δ Z (.head u) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedΔ hu ts
      (TypeEq.trans S.levels equal ⟨v, hv, equal_narrow nb.narrows eZ⟩)
      (Long.type_narrow facts lZ nb.narrows formedΓ formedΔ)
  exact ⟨Z, typed_widen facts algebra Z hu nb formedΓ formedΔ lZ smallΔ, eZ⟩

end Widening

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
