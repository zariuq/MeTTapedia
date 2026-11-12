import Mettapedia.GSLT.Core.ContextualComprehension
import Mathlib.Logic.Equiv.Prod

/-!
# Relative dependent telescopes and their arguments

A schema extends an existing context by a finite sequence of types. Each
subsequent type lives over the context extended by its predecessors.
Arguments are an explicit dependent tuple of terms, rather than a supplied
substitution with an assumed completeness property. Iterated comprehension
identifies these tuples with substitutions into the extended context.

The empty telescope does not require an inhabited term type or a terminal
context. The equality of terms remains a property of the chosen model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSchemaTelescopes

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

/-- A finite dependent extension relative to an arbitrary existing context. -/
inductive Extension (C : Cwf.{u, v, w, w'}) : C.Ctx → Type (max u w) where
  | nil (base : C.Ctx) : Extension C base
  | cons {base : C.Ctx} (type : C.Ty base)
      (rest : Extension C (C.ext base type)) : Extension C base

namespace Extension

variable {C : Cwf.{u, v, w, w'}}

abbrev target : {base : C.Ctx} → Extension C base → C.Ctx
  | _, .nil base => base
  | _, .cons _ rest => rest.target

def weaken : {base : C.Ctx} → (telescope : Extension C base) → C.Sub telescope.target base
  | _, .nil base => C.idS base
  | _, .cons type rest => C.compS (C.wk type) rest.weaken

def length : {base : C.Ctx} → Extension C base → Nat
  | _, .nil _ => 0
  | _, .cons _ rest => rest.length + 1

/-- Open the second telescope in the context resulting from the first. -/
def append : {base : C.Ctx} → (first : Extension C base) →
    Extension C first.target → Extension C base
  | _, .nil _, second => second
  | _, .cons type rest, second => .cons type (rest.append second)

theorem append_target : {base : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) → (first.append second).target = second.target
  | _, .nil _, _ => rfl
  | _, .cons _ rest, second => rest.append_target second

theorem append_length : {base : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) →
      (first.append second).length = first.length + second.length
  | _, .nil _, second => (Nat.zero_add second.length).symm
  | _, .cons _ rest, second => by
      change (rest.append second).length + 1 = (rest.length + 1) + second.length
      rw [rest.append_length second]
      exact Nat.add_right_comm rest.length second.length 1

/-- Bundle the target with its weakening so comparison retains the dependent arrow. -/
def weakeningData {base : C.Ctx} (telescope : Extension C base) :
    Σ destination : C.Ctx, C.Sub destination base := ⟨telescope.target, telescope.weaken⟩

/-- Opening in stages composes the actual weakening substitutions. -/
theorem append_weakeningData : {base : C.Ctx} → (first : Extension C base) →
    (second : Extension C first.target) →
      (first.append second).weakeningData =
        ⟨second.target, C.compS first.weaken second.weaken⟩
  | _, .nil _, second => by
      simp only [append, weakeningData, weaken, C.id_comp]
  | base, .cons type rest, second => by
      have lifted := congrArg
        (fun arrow : Σ destination : C.Ctx, C.Sub destination (C.ext base type) =>
          (⟨arrow.1, C.compS (C.wk type) arrow.2⟩ : Σ destination : C.Ctx, C.Sub destination base))
        (rest.append_weakeningData second)
      simpa only [append, weakeningData, target, weaken, C.comp_assoc] using lifted

/-- Each supplied term has its type reindexed by the already supplied arguments. -/
def Arguments : {base : C.Ctx} → (telescope : Extension C base) →
    {source : C.Ctx} → C.Sub source base → Type w'
  | _, .nil _, _, _ => PUnit
  | _, .cons type rest, _, baseMap =>
      Σ term : C.Tm _ (C.tySub type baseMap),
        rest.Arguments (C.pair baseMap type term)

abbrev Assignment {base : C.Ctx} (telescope : Extension C base) (source : C.Ctx) :=
  Σ baseMap : C.Sub source base, telescope.Arguments baseMap

/-- Build the actual substitution by successive pairing of the explicit terms. -/
def assemble : {base : C.Ctx} → (telescope : Extension C base) →
    {source : C.Ctx} → (baseMap : C.Sub source base) →
      telescope.Arguments baseMap → C.Sub source telescope.target
  | _, .nil _, _, baseMap, _ => baseMap
  | _, .cons type rest, _, baseMap, args =>
      rest.assemble (C.pair baseMap type args.1) args.2

/-- The universal property of the entire telescope, obtained from the
independently provided one-variable comprehension equivalence. -/
def comprehensionEquiv : {base : C.Ctx} → (telescope : Extension C base) →
    (source : C.Ctx) → C.Sub source telescope.target ≃ telescope.Assignment source
  | _, .nil base, source => (Equiv.sigmaPUnit (C.Sub source base)).symm
  | base, .cons type rest, source =>
      ((rest.comprehensionEquiv source).trans
        (Equiv.sigmaCongrLeft' (C.comprehensionEquiv source base type))).trans
          (Equiv.sigmaAssoc fun baseMap term =>
            rest.Arguments (C.pair baseMap type term))

/-- The inverse of the universal equivalence is the independent pairing algorithm. -/
theorem comprehensionEquiv_symm_apply : {base : C.Ctx} →
    (telescope : Extension C base) → (source : C.Ctx) →
    (assignment : telescope.Assignment source) →
      (telescope.comprehensionEquiv source).symm assignment =
        telescope.assemble assignment.1 assignment.2
  | _, .nil _, _, _ => rfl
  | _, .cons type rest, source, ⟨baseMap, supplied⟩ => by
      change (Σ term : C.Tm source (C.tySub type baseMap),
        rest.Arguments (C.pair baseMap type term)) at supplied
      rcases supplied with ⟨term, args⟩
      change (rest.comprehensionEquiv source).symm ⟨C.pair baseMap type term, args⟩ = _
      exact rest.comprehensionEquiv_symm_apply source _

/-- Reading the argument tuple and reassembling recovers the original substitution. -/
theorem assemble_decompose {base source : C.Ctx} (telescope : Extension C base)
    (substitution : C.Sub source telescope.target) :
    telescope.assemble ((telescope.comprehensionEquiv source) substitution).1
      ((telescope.comprehensionEquiv source) substitution).2 = substitution := by
  rw [← comprehensionEquiv_symm_apply]
  exact (telescope.comprehensionEquiv source).symm_apply_apply substitution

/-- Reassembling supplied arguments does not forget their base or any component. -/
theorem decompose_assemble {base source : C.Ctx} (telescope : Extension C base)
    (baseMap : C.Sub source base) (args : telescope.Arguments baseMap) :
    telescope.comprehensionEquiv source (telescope.assemble baseMap args) = ⟨baseMap, args⟩ := by
  rw [← comprehensionEquiv_symm_apply telescope source ⟨baseMap, args⟩]
  exact (telescope.comprehensionEquiv source).apply_symm_apply _

/-- Instantiation leaves the supplied interpretation of the old context intact. -/
theorem weaken_assemble : {base : C.Ctx} → (telescope : Extension C base) →
    {source : C.Ctx} → (baseMap : C.Sub source base) →
      (args : telescope.Arguments baseMap) →
        C.compS telescope.weaken (telescope.assemble baseMap args) = baseMap
  | _, .nil _, _, baseMap, _ => C.id_comp baseMap
  | _, .cons type rest, source, baseMap, supplied => by
      change (Σ term : C.Tm source (C.tySub type baseMap),
        rest.Arguments (C.pair baseMap type term)) at supplied
      rcases supplied with ⟨term, args⟩
      change C.compS (C.compS (C.wk type) rest.weaken)
        (rest.assemble (C.pair baseMap type term) args) = baseMap
      rw [C.comp_assoc, rest.weaken_assemble, C.wk_pair]

theorem decompose_base {base source : C.Ctx} (telescope : Extension C base)
    (substitution : C.Sub source telescope.target) :
    (telescope.comprehensionEquiv source substitution).1 =
      C.compS telescope.weaken substitution := by
  have projected := telescope.weaken_assemble
    (telescope.comprehensionEquiv source substitution).1
    (telescope.comprehensionEquiv source substitution).2
  rw [telescope.assemble_decompose] at projected
  exact projected.symm

/-- Precomposition of a complete typed assignment, transported through the
proved universal property. Subsequent laws derive its functoriality. -/
def precompose {base source earlier : C.Ctx} (telescope : Extension C base)
    (assignment : telescope.Assignment source) (substitution : C.Sub earlier source) :
    telescope.Assignment earlier :=
  telescope.comprehensionEquiv earlier
    (C.compS (telescope.assemble assignment.1 assignment.2) substitution)

theorem assemble_precompose {base source earlier : C.Ctx} (telescope : Extension C base)
    (assignment : telescope.Assignment source) (substitution : C.Sub earlier source) :
    telescope.assemble (telescope.precompose assignment substitution).1
      (telescope.precompose assignment substitution).2 =
        C.compS (telescope.assemble assignment.1 assignment.2) substitution :=
  telescope.assemble_decompose _

theorem precompose_id {base source : C.Ctx} (telescope : Extension C base)
    (assignment : telescope.Assignment source) :
    telescope.precompose assignment (C.idS source) = assignment := by
  simp only [precompose, C.comp_id, decompose_assemble]

theorem precompose_comp {base source middle earlier : C.Ctx} (telescope : Extension C base)
    (assignment : telescope.Assignment source)
    (first : C.Sub middle source) (second : C.Sub earlier middle) :
    telescope.precompose (telescope.precompose assignment first) second =
      telescope.precompose assignment (C.compS first second) := by
  unfold precompose
  rw [telescope.assemble_decompose, C.comp_assoc]

theorem precompose_base {base source earlier : C.Ctx} (telescope : Extension C base)
    (assignment : telescope.Assignment source) (substitution : C.Sub earlier source) :
    (telescope.precompose assignment substitution).1 = C.compS assignment.1 substitution := by
  rw [precompose, decompose_base, ← C.comp_assoc, weaken_assemble]

end Extension

end Mettapedia.TypeTheory.ContextualSchemaTelescopes
