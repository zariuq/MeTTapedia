import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunSwapWitness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentStateGroupoid

/-!
# Boundary maps retained by swap factorization

The factorization through canonical residuals introduces comparison maps
and their inverses. On the actual dependent state groupoid they cancel,
leaving exactly the supplied continuation boundary. This is stronger than
existence of some isomorphic endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}

namespace SimilarityWitness

theorem lastIso_symm {source target : State} {first : P.Run source} {second : P.Run target}
    (witness : T.SimilarityWitness first second) : witness.symm.lastIso = T.symm witness.lastIso := by
  induction witness with
  | nil => rfl
  | cons _ _ _ ih => exact ih

theorem lastIso_trans {source middle target : State}
    {first : P.Run source} {second : P.Run middle} {third : P.Run target}
    (one : T.SimilarityWitness first second) (two : T.SimilarityWitness second third) :
    (one.trans two).lastIso = T.trans one.lastIso two.lastIso := by
  induction one generalizing target with
  | nil comparison => cases two; rfl
  | cons comparison alike tail ih =>
      cases two with
      | cons comparison' alike' tail' => exact ih tail'

end SimilarityWitness

def SwapWitness.lastIso : {state : State} → {first second : P.Run state} →
    T.SwapWitness first second → T.Iso first.last second.last
  | _, _, _, .here _ _ _ _ _ _ tail => tail.lastIso
  | _, _, _, .later _ _ tail => tail.lastIso

end Transport

namespace DependentFull.RunStateGroupoid

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type}

theorem cancel_boundary {a b c d : State rules O}
    (first : PlainIso levels a b) (second : PlainIso levels b c) (last : PlainIso levels a d) :
    first.trans (second.trans (second.symm.trans (first.symm.trans last))) = last := by
  apply iso_ext
  simp only [PlainIso.trans, PlainIso.symm, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]

variable [DecidableEq O]

theorem factor_boundary {state : State rules O} {first second : (helperStep levels O).toStep.Run state}
    (witness : (helperTransport levels O).SwapWitness first second) :
    witness.factor.before.lastIso.trans
      (witness.factor.swap.lastIso.trans witness.factor.after.lastIso) = witness.lastIso := by
  induction witness with
  | here accepted accepted' residualFirst acceptedAfterFirst residualSecond acceptedAfterSecond tail =>
      simp only [Transport.SwapWitness.factor, Transport.SwapWitness.lastIso,
        Transport.SimilarityWitness.consSelf, Transport.SimilarityWitness.consAlike,
        Transport.SimilarityWitness.lastIso, Transport.InterchangeWitness.lastIso,
        Transport.SimilarityWitness.lastIso_trans, Transport.SimilarityWitness.lastIso_symm]
      exact cancel_boundary _ _ _
  | later candidate accepted tail ih => exact ih

theorem swap_cell_boundary {state : State rules O} {first second : (helperStep levels O).toStep.Run state}
    (witness : (helperTransport levels O).SwapWitness first second) :
    endpointMap levels O witness.cell = witness.lastIso := by
  unfold Transport.SwapWitness.cell
  rw [endpointMap_comp, endpointMap_comp,
    endpointMap_generator, endpointMap_generator, endpointMap_generator]
  exact factor_boundary witness

end DependentFull.RunStateGroupoid

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.RunStateGroupoid.swap_cell_boundary
