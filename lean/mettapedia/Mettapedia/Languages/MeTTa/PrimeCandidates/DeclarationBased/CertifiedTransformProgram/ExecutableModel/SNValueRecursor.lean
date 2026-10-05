import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueNumbers
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelTypings

/-!
# The recursor on the numbers in the transport value model

The recursor `num-rec P z s n` computes at `zero` to `z`, and at `suc m` to
`s m (num-rec P z s m)`, on the value side of the model of every extension of the transport
value model and on its realizer side alike. It is a valid term of
`Π P : num → w. P zero → (Π n : num. P n → P (suc n)) → Π n : num. P n` for
every universe `w` (`TExtension.valid_numRecS_at`), the declared type `numRecType` being
the instance at the lowest universe (`TExtension.valid_numRec`).

This is the clause of the recursor of a simple inductive type (`ModelSN.ValidTmS.inductiveRec`)
at the numbers: their type is `num` with the constructors `zero`, without fields, and `suc`, with
one recursive field (`TExtension.num_inductiveIn`), and the declared type of the recursor is the
recursor's type of that declaration. Large elimination is the same argument as small
elimination: the universe relation relates types with one pack and one shape at any level.

The step's type and its instances (`vstepType`, `vinst0_stepCod`, `vinst0_sucMotive`) are the
shapes the conversion model reads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World)
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic)
open SetProfile (zeroNative sucNative)
open Package (numRecName numT numRecType numRecApp)

namespace CodeModel

/-! ## The motive and the step -/

/-- The type of the recursor's step at a motive `P`: `Π n : num. P n → P (suc n)`. -/
abbrev vstepType {n : Nat} (P : Tower.Tm n) : Tower.Tm n :=
  .pi numT (.pi (.app (Presentation.rename wk P) (.var 0))
    (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1))))

/-- The step's type at a number `a`: `P a → P (suc a)`. -/
theorem vinst0_stepCod {n : Nat} (P a : Tower.Tm n) :
    Presentation.inst0 a (.pi (.app (Presentation.rename wk P) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1)))) =
      .pi (.app P a) (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) := by
  show Tm.pi (.app (Presentation.inst0 a (Presentation.rename wk P)) a)
      (.app (Presentation.subst (liftSub (subst0 a))
          (Presentation.rename wk (Presentation.rename wk P)))
        (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, subst_liftSub_wk]
  show Tm.pi (.app P a) (.app (Presentation.rename wk
      (Presentation.inst0 a (Presentation.rename wk P))) (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk]

/-- The motive at the successor of a number, over one more variable,
instantiated at a value. -/
theorem vinst0_sucMotive {n : Nat} (P a h : Tower.Tm n) :
    Presentation.inst0 h (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) =
      .app P (sucNative a) := by
  show Tm.app (Presentation.inst0 h (Presentation.rename wk P))
      (sucNative (Presentation.inst0 h (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, inst0_rename_wk]

namespace TExtension

variable (X : TExtension) (v : Nat → Nat)

/-- The recursor at a daimonic number is stuck on the daimon. -/
theorem numRec_daimonic {n : Nat} (P z s : Tower.Tm n) {u : Tower.Tm n}
    (daimonic : Daimonic (X.model v).roles (X.model v).star u) :
    Daimonic (X.model v).roles (X.model v).star (numRecApp P z s u) :=
  Daimonic.stuck (before := [P, z, s]) (after := []) X.extends_.numRec rfl daimonic

/-- **The recursor on the numbers is valid with its motive into every
universe**: large elimination of the numbers, the clause of the recursor of a simple inductive
type. The validity of the type and of its parts are hypotheses, which the fundamental lemma of
a smaller stage provides. -/
theorem valid_numRecS_at (w : Tower.Head) (hw : (X.model v).rules.isUniverse w)
    (validType : ModelSN.ValidTyS (X.model v) .nil (numRecTypeAt w))
    (partsType : ModelSN.StructuredS (X.model v) .nil (numRecTypeAt w)) :
    ModelSN.ValidTmS (X.model v) .nil (.const numRecName) (numRecTypeAt w) :=
  ModelSN.ValidTmS.inductiveRec (X.laws v) (X.num_inductiveIn v) hw validType partsType

/-- **The recursor on the numbers is valid**: the instance of `valid_numRecS_at` at the lowest
universe. The validity of its declared type and of that type's parts are hypotheses, which the
fundamental lemma of a smaller stage provides. -/
theorem valid_numRec (validType : ModelSN.ValidTyS (X.model v) .nil numRecType)
    (partsType : ModelSN.StructuredS (X.model v) .nil numRecType) :
    ModelSN.ValidTmS (X.model v) .nil (.const numRecName) numRecType :=
  X.valid_numRecS_at v (.sort Tower.zero) (LevelTower.IsUniverse.sort _) validType partsType

end TExtension

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
