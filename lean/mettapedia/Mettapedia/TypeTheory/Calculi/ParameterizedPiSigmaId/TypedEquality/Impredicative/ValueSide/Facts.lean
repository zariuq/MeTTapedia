import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Reflection

/-!
# The facts of the interpretation at every level

The interpretation at a level has the facts of an interpretation
(`InterpFacts`) when the interpretations below have them, read every daimonic
type by the total pack, and grow with the level (`SInterp.facts`):

* determinism, partial equivalence, expansion, renaming and the clause packs
  are the value laws;
* daimonic terms are related at every type (`SInterp.daimonic_related`), and
  related values have one realizer (`SInterp.real_eq_of_rel`);
* every interpreted type reduces to a type form (`SInterp.typeForm`);
* the relation of a universe grows with its level: a universe below the level
  reads the interpretation at its own level, and shapes grow with the
  interpretation (`Shape.mono`).

The interpretations below a level are those at the lower levels, which read
daimonic types by the total pack and grow with the level by cumulativity, so
the facts hold at every level, by induction over the level order
(`InterpAt.facts`). The universe relation at a level is a partial equivalence
and grows with the level (`universePack_per`, `universePack_mono`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-! ## The facts of the interpretation at a level -/

/-- **The interpretation at a level has the facts of an interpretation** when
the interpretations below it have them, read every daimonic type by the total
pack, and grow with the level. -/
theorem SInterp.facts (laws : V.Laws) {l : L} {below : L → IPack V}
    (belowFacts : ∀ k, k < l → InterpFacts V (below k))
    (belowDaimonic : ∀ k, k < l → ∀ {m : Nat} {ξ : World V.reading m} {u : Tm Head m},
      Daimonic V.roles V.star u → below k ξ u (Pack.total V m))
    (belowMono : ∀ k k', k ≤ k' → k' < l → ∀ {m : Nat} {ξ : World V.reading m}
      {A : Tm Head m} {P : Pack V m}, below k ξ A P → below k' ξ A P) :
    InterpFacts V (SInterp V l below) where
  deterministic := fun first second => first.deterministic laws second
  symm := fun interp => (interp.per laws belowFacts).symm
  trans := fun interp => (interp.per laws belowFacts).trans
  expand := fun red interp => interp.expand red
  expandRel := fun {_ _ _ _} interp {_ _ _ _} red red' related =>
    have expansive := interp.expandRel laws fun k lt => (belowFacts k lt).expand
    expansive.left red (expansive.right red' related)
  rename := fun {_ _ _ _} interp {_ _ _} w => by
    obtain ⟨P', interp', renamed⟩ := interp.rename laws w
    exact ⟨P', interp', renamed.rel⟩
  piPack := fun interp red => interp.pi_inv laws red
  sigmaPack := fun interp red => interp.sigma_inv laws red
  univPack := fun interp red isUniverse => ⟨_, (interp.univ_inv laws red isUniverse).2⟩
  propPack := fun interp red => interp.deterministic laws (.prop red)
  indPack := fun interp red role => interp.ind_inv laws red role
  daimonic := fun interp red daimonic => interp.deterministic laws (.daimon red daimonic)
  daimonicRel := fun interp => interp.daimonic_related laws belowDaimonic
  realEq := fun interp => interp.real_eq_of_rel laws belowFacts
  typeForm := fun interp => interp.typeForm
  univMono := fun {_ _ _ _ u u' _ _} hX hZ rX rZ hu hu' le {_ _} related => by
    obtain ⟨lt, rfl⟩ := hX.univ_inv laws rX hu
    obtain ⟨lt', rfl⟩ := hZ.univ_inv laws rZ hu'
    intro m ξ' ρ w
    obtain ⟨P, hA, hB, s⟩ := related w
    have incl : ∀ {k : Nat} {ζ : World V.reading k} {X : Tm Head k} {R : Pack V k},
        below (V.levels.level u) ζ X R → below (V.levels.level u') ζ X R :=
      fun h => belowMono _ _ le lt' h
    exact ⟨P, incl hA, incl hB,
      s.mono (belowFacts _ lt) incl (belowFacts _ lt').deterministic⟩

/-- A lower level has, below `l`, the facts it has at its own level. -/
theorem levelsBelow_facts {l k : L} (h : k < l) (facts : InterpFacts V (InterpAt V k)) :
    InterpFacts V (levelsBelow V l k) := by
  rw [levelsBelow_eq h]
  exact facts

/-! ## Laws at every level -/

section Levels

variable (laws : V.Laws)
include laws

/-- **The interpretation at every level has the facts of an interpretation**,
by induction over the level order. -/
theorem InterpAt.facts (l : L) : InterpFacts V (InterpAt V l) :=
  LevelOrder.induction (motive := fun l => InterpFacts V (InterpAt V l)) l fun _ ih =>
    SInterp.facts laws (fun k lt => levelsBelow_facts lt (ih k lt))
      (fun _ lt {_ _ _} daimonic => levelsBelow_daimonic lt daimonic)
      (fun _ _ le lt' {_ _ _ _} h => levelsBelow_mono le lt' h)

/-- The value relation of a type at a level is a partial equivalence. -/
theorem InterpAt.per {l : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : InterpAt V l ξ A P) : P.IsPER :=
  ⟨(InterpAt.facts laws l).symm interp, (InterpAt.facts laws l).trans interp⟩

/-- **Related values of a type at a level have the same realizers.** -/
theorem InterpAt.real_eq_of_rel {l : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {P : Pack V n} (interp : InterpAt V l ξ A P) {a b : Tm Head n} (related : P.rel a b) :
    P.real a = P.real b :=
  (InterpAt.facts laws l).realEq interp related

/-! ## The universe relation at a level -/

/-- **The universe relation at a level is a partial equivalence**: symmetric
and transitive by the laws of shapes over the interpretation at that level. -/
theorem universePack_per (k : L) {n : Nat} (ξ : World V.reading n) :
    (universePack V (InterpAt V k) ξ).IsPER :=
  universePack_isPER laws (InterpAt.facts laws k) ξ

/-- **The universe relation grows with the level**: types with one pack and one
shape at a level have them at every higher level, shapes growing with the
interpretation. -/
theorem universePack_mono {k k' : L} (le : k ≤ k') {n : Nat} {ξ : World V.reading n}
    {A B : Tm Head n} (related : (universePack V (InterpAt V k) ξ).rel A B) :
    (universePack V (InterpAt V k') ξ).rel A B := fun {_ _ _} w => by
  obtain ⟨P, hA, hB, s⟩ := related w
  exact ⟨P, hA.cumul le, hB.cumul le,
    s.mono (InterpAt.facts laws k) (fun h => h.cumul le)
      (fun h h' => InterpAt.deterministic laws h h')⟩

end Levels

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
