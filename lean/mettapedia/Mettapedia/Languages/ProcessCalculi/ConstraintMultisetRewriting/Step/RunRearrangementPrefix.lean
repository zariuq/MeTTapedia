import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangement

/-!
# Extending native run comparisons by a shared execution prefix

Prefixing carries the actual generator evidence, including the depth of an
interchange. The induced free-groupoid functor preserves composition,
identities and inverse comparisons. The prefix executes once on either side;
it is not replaced by a state-only observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}

def InterchangeWitness.prepend : {start : State} → (early : P.Run start) →
    {first second : P.Run early.last} → T.InterchangeWitness first second →
      T.InterchangeWitness (early.append first) (early.append second)
  | _, .nil _, _, _, witness => witness
  | _, .cons firing accepted rest, _, _, witness => .later firing accepted (witness.prepend rest)

theorem InterchangeWitness.depth_prepend : ∀ {start : State} (early : P.Run start)
    {first second : P.Run early.last} (witness : T.InterchangeWitness first second),
    (witness.prepend early).depth = early.word.length + witness.depth
  | _, .nil _, _, _, witness => (Nat.zero_add witness.depth).symm
  | _, .cons _ _ rest, _, _, witness => by
      change (witness.prepend rest).depth + 1 = (rest.word.length + 1) + witness.depth
      rw [InterchangeWitness.depth_prepend rest witness]
      exact Nat.add_right_comm rest.word.length witness.depth 1

namespace RunRearrangement

variable (T)

def prefixGenerators {start : State} (early : P.Run start) :
    Object T early.last ⥤q Object T start where
  obj run := early.append run
  map witness := match witness with
    | .inl similar => .inl ((SimilarityWitness.refl early).append similar)
    | .inr interchange => .inr (interchange.prepend early)

def prefixFunctor {start : State} (early : P.Run start) :
    Groupoid T early.last ⥤ Groupoid T start :=
  Quiver.freeGroupoidFunctor (prefixGenerators T early)

def prepend {start : State} (early : P.Run start) {first second : P.Run early.last}
    (cell : Cell T first second) : Cell T (early.append first) (early.append second) :=
  (prefixFunctor T early).map cell

theorem prepend_comp {start : State} (early : P.Run start)
    {first second third : P.Run early.last} (one : Cell T first second) (two : Cell T second third) :
    prepend T early (one ≫ two) = prepend T early one ≫ prepend T early two :=
  (prefixFunctor T early).map_comp one two

theorem prepend_id {start : State} (early : P.Run start) (run : P.Run early.last) :
    prepend T early (𝟙 (object T run)) = 𝟙 (object T (early.append run)) :=
  (prefixFunctor T early).map_id _

theorem prepend_inv {start : State} (early : P.Run start) {first second : P.Run early.last}
    (cell : Cell T first second) : prepend T early (inv cell) = inv (prepend T early cell) :=
  (prefixFunctor T early).map_inv cell

end RunRearrangement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.prepend_comp
