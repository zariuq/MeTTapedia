import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Truth

/-!
# Laws of truth: expansion and renaming

Truth and meaning are read from weak-head normal forms, so a term has the
meaning of its reducts. A world morphism renames generics while keeping their
meanings, and every truth value and meaning survives it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

variable {Head : Type} {S : Reading Head}

/-! ## Data values along reduction and renaming -/

/-- A term that reduces to a term related to itself at a data carrier has its
value. -/
theorem Read.data_expand {n : Nat} {ξ : World S n} {t t' : Tm Head n} {D : Carrier .data}
    (red : WhRed S.rules S.roles t t') (related : DataEq S D t' t') :
    Read S ξ t D (dataValue S D t' related) := by
  have relT : DataEq S D t t := DataEq.expand red red related
  rw [← dataValue_sound relT related (DataEq.expand red .refl related)]
  exact .data relT

/-- A renamed term related to itself at a data carrier keeps its value. -/
theorem Read.data_rename {n m : Nat} {ξ : World S m} {t : Tm Head n} {D : Carrier .data}
    (related : DataEq S D t t) (ρ : Ren n m) :
    Read S ξ (Presentation.rename ρ t) D (dataValue S D t related) := by
  rw [← dataValue_rename related ρ (related.rename₂ ρ)]
  exact .data (related.rename₂ ρ)

/-! ## Expansion -/

theorem Truth.expand {n : Nat} {ξ : World S n} {t t' : Tm Head n} {P : S.P}
    (red : WhRed S.rules S.roles t t') (truth : Truth S ξ t' P) : Truth S ξ t P := by
  cases truth with
  | imp r p q => exact .imp (red.trans r) p q
  | all carrier r f => exact .all carrier (red.trans r) f
  | eq carrier r x y => exact .eq carrier (red.trans r) x y
  | generic r apply => exact .generic (red.trans r) apply
  | neutral r neutral => exact .neutral (red.trans r) neutral

theorem Read.expand : ∀ {n : Nat} {ξ : World S n} {t t' : Tm Head n} {k : Kind}
    {A : Carrier k} {v : A.V S},
    WhRed S.rules S.roles t t' → Read S ξ t' A v → Read S ξ t A v
  | _, _, _, _, _, _, _, red, .prop truth => .prop (truth.expand red)
  | _, _, _, _, _, _, _, _, .rigid => .rigid
  | _, _, _, _, _, _, _, red, .data related => Read.data_expand red related
  | _, _, _, _, _, _, _, red, .dataArg read =>
      .dataArg fun {_ _ _} morph {_} related =>
        Read.expand ((red.rename _).app _) (read morph related)
  | _, _, _, _, _, _, _, red, .genericArg read =>
      .genericArg fun v => Read.expand ((red.rename wk).app _) (read v)

/-! ## Renaming along world morphisms -/

mutual

theorem Truth.rename : ∀ {n m : Nat} {ξ : World S n} {ξ' : World S m} {ρ : Ren n m}
    {t : Tm Head n} {P : S.P},
    Morph ξ ξ' ρ → Truth S ξ t P → Truth S ξ' (Presentation.rename ρ t) P
  | _, _, _, _, ρ, _, _, morph, .imp red p q =>
      .imp (red.rename ρ) (Truth.rename morph p) (Truth.rename morph q)
  | _, _, _, _, ρ, _, _, morph, .all carrier red f =>
      .all carrier (red.rename ρ) (Read.rename morph f)
  | _, _, _, _, ρ, _, _, morph, .eq carrier red x y =>
      .eq carrier (red.rename ρ) (Read.rename morph x) (Read.rename morph y)
  | _, _, _, _, ρ, _, _, morph, @Truth.generic _ _ _ _ _ i args _ red apply => by
      have red' := red.rename ρ
      rw [rename_appSpine] at red'
      have apply' := Apply.rename morph apply
      rw [← morph i] at apply'
      exact .generic red' apply'
  | _, _, _, _, ρ, _, _, _, .neutral red neutral =>
      .neutral (red.rename ρ) (S.neutral_rename ρ neutral)

theorem Read.rename : ∀ {n m : Nat} {ξ : World S n} {ξ' : World S m} {ρ : Ren n m}
    {t : Tm Head n} {k : Kind} {A : Carrier k} {v : A.V S},
    Morph ξ ξ' ρ → Read S ξ t A v → Read S ξ' (Presentation.rename ρ t) A v
  | _, _, _, _, _, _, _, _, _, morph, .prop truth => .prop (Truth.rename morph truth)
  | _, _, _, _, _, _, _, _, _, _, .rigid => .rigid
  | _, _, _, _, ρ, _, _, _, _, _, .data related => Read.data_rename related ρ
  | _, _, _, _, ρ, t, _, _, _, morph, .dataArg read =>
      .dataArg fun {_ _ _} morph' {_} related => by
        have h := read (morph.comp' morph') related
        rwa [← rename_comp] at h
  | _, _, _, _, ρ, t, _, _, _, morph, .genericArg read =>
      .genericArg fun v => by
        have h := Read.rename (morph.lift ⟨_, v⟩) (read v)
        have zero : liftRen ρ 0 = 0 := rfl
        simpa only [Presentation.rename, rename_liftRen_wk, zero] using h

theorem Apply.rename : ∀ {n m : Nat} {ξ : World S n} {ξ' : World S m} {ρ : Ren n m}
    {A : Carrier .gen} {v : A.V S} {args : List (Tm Head n)} {P : S.P},
    Morph ξ ξ' ρ → Apply S ξ A v args P →
      Apply S ξ' A v (args.map (Presentation.rename ρ)) P
  | _, _, _, _, _, _, _, _, _, _, .done => .done
  | _, _, _, _, _, _, _, _, _, morph, .arg read rest =>
      .arg (Read.rename morph read) (Apply.rename morph rest)

end

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
