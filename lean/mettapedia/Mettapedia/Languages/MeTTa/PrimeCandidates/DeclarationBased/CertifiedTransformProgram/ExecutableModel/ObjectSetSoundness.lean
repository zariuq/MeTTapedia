import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetValuesControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchLifting
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.IntuitionisticImport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ChurchSoundness

/-!
# The object package is sound and consistent in the set tower

The object package's annotation has a set model in the seeded tower (`objectSetModel`): its
root steps require the typings of the instances of their metavariables and the equations of
their reflexivity positions, and at the instances that satisfy these every rewrite schema of
the package has one value on both sides.

Every derivation of the object package lifts to its annotation (`objectLiftingFacts`): the
premises of a root step are read off the typing of its redex by pattern inversion
(`objectRootPremised`). So, relative to `CofinalInaccessibles`:

* **Soundness** (`objectRules_sound_tower`): every derivation of the object package over a
  formed context is the erasure of an annotated derivation whose statement holds in the
  tower.
* **Consistency** (`objectRules_consistent_tower`): no closed term of the object package has
  the type `Π (X : U₀). X`.
* **Not every code holds** (`objectRules_not_all_true`): no closed term of the object package
  has the type `Π (p : prop). holds p`.
* **Impredicative falsity has no proof** (`objectRules_consistent_bot_tower`): no closed term
  proves `∀ p : prop. p`, the statement of `consistent_bot`, here by the set tower: applied to
  a code variable, such a term would prove every code.

Positive controls: the numerals are closed inhabitants of `num`, whose value is `ω`
(`zero_mem_num`), so the theorems above do not hold of every type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProducts (traceApp tracePiSet)

universe u

namespace CodeModel

/-- **Soundness of every derivation of the object package in the seeded tower.** Relative to
`CofinalInaccessibles`, every derivation of the object package over a formed context is the
erasure of an annotated derivation whose statement holds in the tower. -/
theorem objectRules_sound_tower (h : CofinalInaccessibles.{u}) {statement : Statement Tower.Head}
    (derivation : Derivable objectRules statement) (formed : statement.CtxFormed objectRules) :
    ∃ s : CStatement Tower.Head, CDerivable objectChurch s ∧ s.erase = statement ∧
      Holds (objHeads h) (objectSetConsts h) s :=
  Derivable.sound_elaborated ConvRules.objectLevels objectLiftingFacts (objectSetModel h)
    derivation formed

/-- **Consistency of the object package in the seeded tower.** Relative to
`CofinalInaccessibles`, no closed term of the object package has the type `Π (X : U₀). X`. -/
theorem objectRules_consistent_tower (h : CofinalInaccessibles.{u}) (t : Tower.Tm 0) :
    ¬ Derivable objectRules (.typing .nil t emptyType.erase) :=
  Derivable.no_closed_inhabitant (A := emptyType.erase) ConvRules.objectLevels objectLiftingFacts
    (objectSetModel h) rfl (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (objectSetConsts h)) t

/-- `Π (p : prop). holds p`: every code holds. -/
def objectAllTrue : Tower.Tm 0 := .pi (.const propN) (.app (.const holdsN) (.var 0))

/-- The type `Π (p : prop). holds p` has no element in the seeded tower: its element at the
false truth value would be an element of the empty set. -/
theorem ev_objectAllTrue_empty (h : CofinalInaccessibles.{u}) (z : ZFSet.{u}) :
    z ∉ ev (objHeads h) (objectSetConsts h) (liftTm objectAllTrue) Fin.elim0 := by
  intro member
  change z ∈ tracePiSet (objectSetConsts h propN)
    (fun x => traceApp (objectSetConsts h holdsN) x) at member
  rw [setConst_prop h] at member
  have value := traceApp_mem_fibre member empty_mem_truthValues
  rw [holds_apply h empty_mem_truthValues] at value
  exact ZFSet.notMem_empty _ value

/-- **Not every code holds.** Relative to `CofinalInaccessibles`, no closed term of the
object package has the type `Π (p : prop). holds p`. -/
theorem objectRules_not_all_true (h : CofinalInaccessibles.{u}) (t : Tower.Tm 0) :
    ¬ Derivable objectRules (.typing .nil t objectAllTrue) :=
  Derivable.no_closed_inhabitant (A := objectAllTrue) ConvRules.objectLevels objectLiftingFacts
    (objectSetModel h) rfl (ev_objectAllTrue_empty h) t

/-- **Consistency for impredicative falsity, by the set tower.** Relative to
`CofinalInaccessibles`, no closed term of the object package proves `∀ p : prop. p`: applied
to a code variable it would prove every code. -/
theorem objectRules_consistent_bot_tower (h : CofinalInaccessibles.{u}) (t : Tower.Tm 0) :
    ¬ Typed objectRules .nil t (programCodes.holdsOf (botCode (n := 0))) := by
  intro typed
  refine objectRules_not_all_true h (.lam (.app (Presentation.rename wk t) (.var 0))) ?_
  have family : Typed objectRules (.snoc .nil (.const propN))
      (.app (.const holdsN) (.var 0)) Package.U0 :=
    .appElim holds_typedO (.var 0)
  exact .lamIntro (piO prop_typedO family) (.sort Tower.zero)
    (botElimO (Typed.weaken typed) (.var 0))

/-- **Positive control: `num` is inhabited in the tower.** The value of zero lies in the
value of `num`, so the emptiness above is a property of those two types and not of every
type. -/
theorem zero_mem_num (h : CofinalInaccessibles.{u}) :
    ev (objHeads h) (objectSetConsts h) (czero : CTm Tower.Head 0) Fin.elim0 ∈
      ev (objHeads h) (objectSetConsts h) (cnum : CTm Tower.Head 0) Fin.elim0 :=
  objectChurch_sound_tower h (czero_typed (Γ := .nil)) Fin.elim0 (sat_nil _ _ _)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
