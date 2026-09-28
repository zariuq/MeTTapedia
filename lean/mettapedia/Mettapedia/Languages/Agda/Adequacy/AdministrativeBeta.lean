import Mettapedia.Languages.Agda.Adequacy.AdministrativePiInjectivity
import Mettapedia.Languages.Agda.Structural.AdministrativeBetaAssembly

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation

open Mettapedia.OSLF.Binding
open Structural
open Structural.Statics (RawTm RawTy RawContext TermBody)
open Structural.AdministrativeStatics

noncomputable def betaBody {n : Nat} {Γ : RawContext n} {body : TermBody n}
    {argument : RawTm n} {rest : Spine (scope n)} {output : RawTy n}
    (typed : CoreDerivation (Statics.typed Γ (eliminate body.lambda (cons (apply argument) rest)) output)) :
    CoreDerivation (Statics.termEqual Γ (eliminate body.lambda (cons (apply argument) rest))
      (eliminate (body.instantiate argument) rest) output) :=
  let elimination := typed.eliminationParts
  let lambda := elimination.headTyping.lambdaParts
  let spine := BetaPreparation.consParts elimination.action
  let components := piInjectivity (BetaPreparation.piComparison lambda spine)
  BetaPreparation.betaOfComponents elimination.headTyping lambda spine components.1 components.2

noncomputable def betaBinding {n : Nat} {Γ : RawContext n} {body : RawTm (n + 1)}
    {argument : RawTm n} {rest : Spine (scope n)} {output : RawTy n}
    (typed : CoreDerivation (Statics.typed Γ (eliminate (lam body) (cons (apply argument) rest)) output)) :
    CoreDerivation (Statics.termEqual Γ (eliminate (lam body) (cons (apply argument) rest))
      (eliminate (inst body argument) rest) output) := by
  have result := betaBody (body := .bind body) typed
  change CoreDerivation (Statics.termEqual Γ (eliminate (lam body) (cons (apply argument) rest))
    (eliminate (bind (Statics.single argument) body) rest) output) at result
  exact (congrArg (fun t => CoreDerivation (Statics.termEqual Γ
    (eliminate (lam body) (cons (apply argument) rest)) (eliminate t rest) output))
      (Telescope.bind_pair_identity argument body)).mp result

noncomputable def betaNonbinding {n : Nat} {Γ : RawContext n} {body argument : RawTm n}
    {rest : Spine (scope n)} {output : RawTy n}
    (typed : CoreDerivation (Statics.typed Γ (eliminate (lamNoAbs body) (cons (apply argument) rest)) output)) :
    CoreDerivation (Statics.termEqual Γ (eliminate (lamNoAbs body) (cons (apply argument) rest))
      (eliminate body rest) output) := by
  have result := betaBody (body := .noBind body) typed
  simp only [Statics.TermBody.instantiate_noBind] at result
  exact result

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation
