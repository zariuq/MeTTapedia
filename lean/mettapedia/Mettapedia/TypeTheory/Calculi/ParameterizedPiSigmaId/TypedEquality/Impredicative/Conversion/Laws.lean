import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Membership
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Facts

/-!
# The laws of the conversion model

For a lawful conversion model the interpretation at a level has the value side's
laws, read at the value model of the conversion model: it is deterministic, its
value relations are partial equivalences closed under weak-head expansion and
carried along world morphisms, and it is cumulative in the level
(`NInterp.deterministic`, `NInterp.per`, `NInterp.expansive`, `NInterp.rename`,
`NInterp.cumul`); it has the facts of an interpretation, hence the laws of shapes
and of the transport (`NModel.Laws.facts`, `DenN.facts`).

The conversion model relates *pairs*: two values of a pack, and two realizer
terms related by the realizers of the first value (`NPack.Related`). The laws
hold of the pairs:

* **determinism**: related values have one realizer, so either value's
  realizers may be read (`NInterp.real_eq_of_rel`);
* **partial equivalence**: `Related` is symmetric and transitive
  (`NPack.Related.symm`, `NPack.Related.trans`);
* **expansion**: closed under weak-head expansion of the values and typed
  weak-head expansion of the realizers (`NPack.Related.expand`), and the
  realizer type is read through its typed weak-head reducts
  (`NPack.Related.redTy`);
* **renaming**: along a world morphism of the values and a renaming of the
  realizers into a formed context, related pairs stay related in the renamed
  type's pack (`NPack.Related.rename`);
* **cumulativity**: a related pair is related at every realizer type its type is
  usable at (`NPack.Related.below`); the pack of a type at a level is its pack at
  every higher level (`NInterp.cumul`); and the types realizing the values of a
  universe are types of every universe above it (`types_cumul`).

**Reflection of the daimon.** The daimon is a valid value of every interpreted
type, and every two neutral terms that `E` compares at a type are related by its
realizers there (`NInterp.reflect`). So the valuation sending every variable to
the daimon on the value side and to itself on the realizer side relates each
variable to itself (`NInterp.reflect_var`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L] {M : NModel Head L}

/-! ## The value laws at the value model of the conversion model -/

section Values

variable (laws : M.Laws)
include laws

/-- The interpretation at every level has the facts of an interpretation. -/
theorem NModel.Laws.facts (l : L) : ValueSide.InterpFacts M.value (NInterp M l) :=
  ValueSide.InterpAt.facts laws.value l

/-- The denotations of the conversion model have the facts of an interpretation. -/
theorem DenN.facts : ValueSide.InterpFacts M.value (DenN M) :=
  ValueSide.DenS.facts laws.value

variable {l : L} {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {P : NPack M n}

/-- **A type has at most one pack at a level.** -/
theorem NInterp.deterministic {P' : NPack M n} (first : NInterp M l ξ A P)
    (second : NInterp M l ξ A P') : P = P' :=
  ValueSide.InterpAt.deterministic laws.value first second

/-- **The value relation of a type at a level is a partial equivalence.** -/
theorem NInterp.per (interp : NInterp M l ξ A P) : P.IsPER :=
  ValueSide.InterpAt.per laws.value interp

/-- **The value relation of a type at a level is closed under weak-head
expansion of either side.** -/
theorem NInterp.expansive (interp : NInterp M l ξ A P) : P.Expansive :=
  ValueSide.InterpAt.expansive laws.value interp

/-- **Along a world morphism a renamed type has a pack at the level relating the
renamed values.** -/
theorem NInterp.rename (interp : NInterp M l ξ A P) {m : Nat} {ξ' : World M.reading m}
    {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    ∃ P', NInterp M l ξ' (Presentation.rename ρ A) P' ∧ P.Renamed ρ P' :=
  ValueSide.InterpAt.rename laws.value interp w

/-- **Related values of a type at a level have one realizer.** -/
theorem NInterp.real_eq_of_rel (interp : NInterp M l ξ A P) {a b : Tm Head n}
    (related : P.rel a b) : P.real a = P.real b :=
  ValueSide.InterpAt.real_eq_of_rel laws.value interp related

/-- A denoted type has at most one denotation. -/
theorem DenN.deterministic {P' : NPack M n} (first : DenN M ξ A P) (second : DenN M ξ A P') :
    P = P' :=
  ValueSide.DenS.deterministic laws.value first second

end Values

/-- A type has the pack at a level of its weak-head reducts. -/
theorem NInterp.expand {l : L} {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n}
    {P : NPack M n} (red : WhRed M.rules M.roles A A') (interp : NInterp M l ξ A' P) :
    NInterp M l ξ A P :=
  ValueSide.InterpAt.expand red interp

/-- **An interpretation at a level is one at every higher level.** -/
theorem NInterp.cumul {k l : L} (le : k ≤ l) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {P : NPack M n} (interp : NInterp M k ξ A P) : NInterp M l ξ A P :=
  ValueSide.InterpAt.cumul le interp

/-! ## Related pairs -/

/-- Two values related by a pack, together with two realizer terms that the
realizers of the first value relate at a realizer type. -/
def NPack.Related {n : Nat} (P : NPack M n) (a b : Tm Head n) {m : Nat} (Δ : Ctx Head m)
    (B t t' : Tm Head m) : Prop :=
  P.rel a b ∧ (P.real a).rel Δ B t t'

namespace NPack.Related

variable (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
  {P : NPack M n} (interp : NInterp M l ξ A P) {m : Nat} {Δ : Ctx Head m} {B : Tm Head m}
include laws interp

/-- **Related pairs are symmetric.** -/
theorem symm {a b : Tm Head n} {t t' : Tm Head m} (h : P.Related a b Δ B t t') :
    P.Related b a Δ B t' t := by
  obtain ⟨hab, ht⟩ := h
  refine ⟨(NInterp.per laws interp).symm hab, ?_⟩
  rw [← NInterp.real_eq_of_rel laws interp hab]
  exact (P.real a).symm ht

/-- **Related pairs are transitive.** -/
theorem trans {a b c : Tm Head n} {t t' t'' : Tm Head m} (h : P.Related a b Δ B t t')
    (h' : P.Related b c Δ B t' t'') : P.Related a c Δ B t t'' := by
  obtain ⟨hab, ht⟩ := h
  obtain ⟨hbc, ht'⟩ := h'
  refine ⟨(NInterp.per laws interp).trans hab hbc, ?_⟩
  rw [← NInterp.real_eq_of_rel laws interp hab] at ht'
  exact (P.real a).trans ht ht'

/-- **Related pairs are closed under expansion**: weak-head expansion of the
values, and typed weak-head expansion of the realizers. -/
theorem expand {a a₀ b b₀ : Tm Head n} {t t₀ t' t₀' : Tm Head m}
    (red : WhRed M.rules M.roles a a₀) (red' : WhRed M.rules M.roles b b₀)
    (rt : RedTm M.side.R M.side.roles Δ t t₀ B) (rt' : RedTm M.side.R M.side.roles Δ t' t₀' B)
    (h : P.Related a₀ b₀ Δ B t₀ t₀') : P.Related a b Δ B t t' := by
  obtain ⟨hab, ht⟩ := h
  have expansive := NInterp.expansive laws interp
  have per := NInterp.per laws interp
  have ha₀ : P.Val a₀ := per.refl_left hab
  have haa₀ : P.rel a a₀ := expansive.left red ha₀
  refine ⟨expansive.left red (expansive.right red' hab), ?_⟩
  rw [NInterp.real_eq_of_rel laws interp haa₀]
  exact (P.real a₀).expand rt rt' ht

omit laws interp in
/-- **Related pairs read the realizer type through its typed weak-head
reducts**, in a formed context. -/
theorem redTy {a b : Tm Head n} {t t' B' : Tm Head m} (formed : CtxFormed M.side.R Δ)
    (red : RedTy M.side.R M.side.roles Δ B B') :
    P.Related a b Δ B t t' ↔ P.Related a b Δ B' t t' := by
  unfold NPack.Related
  rw [(P.real a).redTy formed red]

omit laws interp in
/-- **Related pairs are cumulative**: in a formed context, a pair related at a
realizer type is related at every type that type is usable at. -/
theorem below {a b : Tm Head n} {t t' B' : Tm Head m} (formed : CtxFormed M.side.R Δ)
    (le : Below M.side.R Δ B B') (h : P.Related a b Δ B t t') : P.Related a b Δ B' t t' :=
  ⟨h.1, (P.real a).below formed le h.2⟩

/-- **Related pairs are carried along renamings**: along a world morphism of the
values and a renaming of the realizers into a formed context, related pairs are
related in the renamed type's pack at the level. -/
theorem rename {a b : Tm Head n} {t t' : Tm Head m} (h : P.Related a b Δ B t t') {n' : Nat}
    {ξ' : World M.reading n'} {ρ : Ren n n'} (w : Morph ξ ξ' ρ) {m' : Nat} {Θ : Ctx Head m'}
    {ρr : Ren m m'} (ren : CtxRen Δ Θ ρr) (formed : CtxFormed M.side.R Θ) :
    ∃ P' : NPack M n', NInterp M l ξ' (Presentation.rename ρ A) P' ∧
      P'.Related (Presentation.rename ρ a) (Presentation.rename ρ b) Θ
        (Presentation.rename ρr B) (Presentation.rename ρr t) (Presentation.rename ρr t') := by
  obtain ⟨hab, ht⟩ := h
  obtain ⟨P', interp', renamed, reals⟩ := NInterp.real_rename laws interp w
  exact ⟨P', interp', renamed.rel hab,
    reals ((NInterp.per laws interp).refl_left hab) ((P.real a).rename ren formed ht)⟩

end NPack.Related

/-! ## Cumulativity of the types -/

/-- **The types realizing the values of a universe are types of every universe
above it.** -/
theorem types_cumul {T : RealizerSide Head L} {m : Nat} {Δ : Ctx Head m} {u v : Head}
    {A A' : Tm Head m} (c : T.R.cumulative u v) (h : (ECand.types T).rel Δ (.head u) A A') :
    (ECand.types T).rel Δ (.head v) A A' := by
  have le : Below T.R Δ (.head u) (.head v) := .subUniv c
  obtain ⟨⟨hA, hA', cv⟩, reach, reach'⟩ := h
  exact ⟨⟨.sub hA le, .sub hA' le, T.laws.convTm_below cv le⟩, reach.below le,
    reach'.below le⟩

/-! ## Reflection of the daimon -/

/-- **Reflection of the daimon.** At every level, the daimon is a valid value of
every interpreted type, and every two neutral terms that `E` compares at a
realizer type are related there by its realizers. -/
theorem NInterp.reflect (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n}
    {A : Tm Head n} {P : NPack M n} (interp : NInterp M l ξ A P) :
    P.Val (.const M.star) ∧
      ∀ {m : Nat} {Δ : Ctx Head m} {B t t' : Tm Head m}, Neutral M.side.roles t →
        Neutral M.side.roles t' → Typed M.side.R Δ t B → Typed M.side.R Δ t' B →
          M.side.E.convNe Δ t t' B → P.Related (.const M.star) (.const M.star) Δ B t t' :=
  have star := ValueSide.InterpAt.star_val laws.value interp
  ⟨star, fun nt nt' ht ht' cv => ⟨star, (P.real _).neutral nt nt' ht ht' cv⟩⟩

/-- Each variable is related to itself by the realizers of the daimon at its
type, in every interpreted type. -/
theorem NInterp.reflect_var (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n}
    {A : Tm Head n} {P : NPack M n} (interp : NInterp M l ξ A P) {m : Nat} {Δ : Ctx Head m}
    {B : Tm Head m} (i : Fin m) (typing : Typed M.side.R Δ (.var i) B) :
    P.Related (.const M.star) (.const M.star) Δ B (.var i) (.var i) :=
  (NInterp.reflect laws interp).2 (.var i) (.var i) typing typing
    (M.side.laws.convNe_var i typing)

/-- Every term stuck on the daimon is related to the daimon at every interpreted
type. -/
theorem NInterp.daimonic_related (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n}
    {A : Tm Head n} {P : NPack M n} (interp : NInterp M l ξ A P) {d d' : Tm Head n}
    (daimonic : Daimonic M.roles M.star d) (daimonic' : Daimonic M.roles M.star d') :
    P.rel d d' :=
  ValueSide.InterpAt.daimonic_related laws.value interp daimonic daimonic'

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
