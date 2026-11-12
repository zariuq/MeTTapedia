import Mettapedia.TypeTheory.ContextualSchemaTelescopes

/-!+# Opening dependent schemas in stages

The arguments for two successive relative extensions are assembled by a
recursive tuple operation. Splitting reverses that operation. The actual
substitution obtained from the combined tuple equals the substitution
obtained by opening the two telescopes in stages.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSchemaTelescopes.Extension

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

variable {C : Cwf.{u, v, w, w'}}

abbrev StagedArguments {base source : C.Ctx} (first : Extension C base)
    (second : Extension C first.target) (baseMap : C.Sub source base) :=
  Σ earlier : first.Arguments baseMap,
    second.Arguments (first.assemble baseMap earlier)

/-- Join the tuples without solving, discarding or reordering a declaration. -/
def joinArguments : {base source : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) → (baseMap : C.Sub source base) →
    StagedArguments first second baseMap → (first.append second).Arguments baseMap
  | _, _, .nil _, _, _, supplied => supplied.2
  | _, _, .cons _ rest, second, _, supplied =>
      ⟨supplied.1.1, rest.joinArguments second _ ⟨supplied.1.2, supplied.2⟩⟩

/-- Split at the declared telescope boundary, retaining the dependence of
the later tuple on the earlier one. -/
def splitArguments : {base source : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) → (baseMap : C.Sub source base) →
    (first.append second).Arguments baseMap → StagedArguments first second baseMap
  | _, _, .nil _, _, _, supplied => ⟨PUnit.unit, supplied⟩
  | _, _, .cons _ rest, second, _, supplied =>
      let divided := rest.splitArguments second _ supplied.2
      ⟨⟨supplied.1, divided.1⟩, divided.2⟩

theorem split_join : {base source : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) → (baseMap : C.Sub source base) →
    (supplied : StagedArguments first second baseMap) →
      first.splitArguments second baseMap (first.joinArguments second baseMap supplied) = supplied
  | _, _, .nil _, _, _, supplied => by
      rcases supplied with ⟨earlier, later⟩
      cases earlier
      rfl
  | _, source, .cons type rest, second, baseMap, supplied => by
      change (Σ earlier : (Σ term : C.Tm source (C.tySub type baseMap),
        rest.Arguments (C.pair baseMap type term)),
        second.Arguments (rest.assemble (C.pair baseMap type earlier.1) earlier.2)) at supplied
      rcases supplied with ⟨⟨term, earlier⟩, later⟩
      change
        (let divided := rest.splitArguments second (C.pair baseMap type term)
            (rest.joinArguments second (C.pair baseMap type term) ⟨earlier, later⟩)
         (⟨⟨term, divided.1⟩, divided.2⟩ :
           StagedArguments (.cons type rest) second baseMap)) = _
      rw [rest.split_join second (C.pair baseMap type term) ⟨earlier, later⟩]
      rfl

theorem join_split : {base source : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) → (baseMap : C.Sub source base) →
    (supplied : (first.append second).Arguments baseMap) →
      first.joinArguments second baseMap (first.splitArguments second baseMap supplied) = supplied
  | _, _, .nil _, _, _, _ => rfl
  | _, source, .cons type rest, second, baseMap, supplied => by
      change (Σ term : C.Tm source (C.tySub type baseMap),
        (rest.append second).Arguments (C.pair baseMap type term)) at supplied
      rcases supplied with ⟨term, remaining⟩
      change
        (⟨term, rest.joinArguments second (C.pair baseMap type term)
          (rest.splitArguments second (C.pair baseMap type term) remaining)⟩ :
          Σ value : C.Tm source (C.tySub type baseMap),
            (rest.append second).Arguments (C.pair baseMap type value)) = _
      rw [rest.join_split second (C.pair baseMap type term) remaining]

def stagedEquiv {base source : C.Ctx} (first : Extension C base)
    (second : Extension C first.target) (baseMap : C.Sub source base) :
    StagedArguments first second baseMap ≃ (first.append second).Arguments baseMap where
  toFun := first.joinArguments second baseMap
  invFun := first.splitArguments second baseMap
  left_inv := first.split_join second baseMap
  right_inv := first.join_split second baseMap

/-- Include the target in the equality so no dependent cast silently
identifies the targets of two differently bracketed constructions. -/
theorem assemble_staged : {base source : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) → (baseMap : C.Sub source base) →
    (supplied : StagedArguments first second baseMap) →
      (⟨(first.append second).target,
        (first.append second).assemble baseMap (first.joinArguments second baseMap supplied)⟩ :
        Σ target : C.Ctx, C.Sub source target) =
      ⟨second.target, second.assemble (first.assemble baseMap supplied.1) supplied.2⟩
  | _, _, .nil _, _, _, _ => rfl
  | _, source, .cons type rest, second, baseMap, supplied => by
      change (Σ earlier : (Σ term : C.Tm source (C.tySub type baseMap),
        rest.Arguments (C.pair baseMap type term)),
        second.Arguments (rest.assemble (C.pair baseMap type earlier.1) earlier.2)) at supplied
      rcases supplied with ⟨⟨term, earlier⟩, later⟩
      exact rest.assemble_staged second (C.pair baseMap type term) ⟨earlier, later⟩

/-- The composite opening preserves the old environment, including when
the second telescope depends on every earlier helper. -/
theorem staged_preserves_base {base source : C.Ctx} (first : Extension C base)
    (second : Extension C first.target) (baseMap : C.Sub source base)
    (supplied : StagedArguments first second baseMap) :
    C.compS (C.compS first.weaken second.weaken)
      (second.assemble (first.assemble baseMap supplied.1) supplied.2) = baseMap := by
  rw [C.comp_assoc, second.weaken_assemble, first.weaken_assemble]

end Mettapedia.TypeTheory.ContextualSchemaTelescopes.Extension
