import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.GSLT.Core.RelationPresentation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.SchemaElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution

/-!
# The proof-relevant relational fragment of the cumulative Π/Σ/Id profile

This module exposes the integration seam between the cumulative Π/Σ/Id profile's intrinsic dependent
type theory and the relational equipment used by GSLT-IL.

The layers remain explicit:

* `Intrinsic` gives Russell-tower terms for proof-relevant relations and
  witness-retaining relational composition, together with formation,
  renaming, and substitution laws.
* `Semantic` gives the corresponding proof-relevant relation object and an
  exact equivalence with the equipment's loose arrows.
* representability is additional evidence.  It recovers the tight functional
  fragment only for total, proof-relevantly deterministic relations.

The semantic center is relational.  Boolean support and compiled functions
are later readouts; neither is installed as the meaning of a relation.

The intrinsic tower definitions have formation, renaming, and substitution
theorems.  The exact equipment correspondence is proved at the semantic
proof-family layer.  Connecting arbitrary intrinsic tower syntax to that
semantic layer would require the still-distinct semantic-CwF interpretation
theorem.  The live operational theorem is separately scoped to the
returned-fibre image in `GSLTILExactImage`; semantic-CwF initiality and a full
command-language universal property remain open boundaries.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace RelationalInternalLanguage

open Presentation
open Presentation.SchemaElaboration

/-! ## Intrinsic Russell-tower syntax -/

namespace Intrinsic

/-- `Rel A B` is the proof-relevant family `A -> B -> U evidenceLevel`.
The evidence universe is explicit and independent of the endpoint levels. -/
def Rel (source target : Tower.Tm n) (evidenceLevel : LevelExpr) :
    Tower.Tm n :=
  .pi source
    (.pi (Presentation.rename wk target) (sortTm evidenceLevel))

/-- Apply a relation term to its two endpoints. -/
def applyRel (relation source target : Tower.Tm n) : Tower.Tm n :=
  .app (.app relation source) target

/-- A nondependent proof pair, represented by dependent Sigma. -/
def evidenceProduct (left right : Tower.Tm n) : Tower.Tm n :=
  .sigma left (Presentation.rename wk right)

/-- Genuine relational composition.  The Sigma retains the intermediate
endpoint; the nested Sigma retains both derivations.

`Chain middle earlier later source target` denotes
`Sigma (middleValue : middle),
  earlier source middleValue × later middleValue target`.
-/
def Chain (middle earlier later source target : Tower.Tm n) : Tower.Tm n :=
  .sigma middle
    (evidenceProduct
      (applyRel (Presentation.rename wk earlier)
        (Presentation.rename wk source) (.var 0))
      (applyRel (Presentation.rename wk later)
        (.var 0) (Presentation.rename wk target)))

@[simp] theorem rename_Rel (renameMap : Ren n m)
    (source target : Tower.Tm n) (evidenceLevel : LevelExpr) :
    Presentation.rename renameMap (Rel source target evidenceLevel) =
      Rel (Presentation.rename renameMap source)
        (Presentation.rename renameMap target) evidenceLevel := by
  simp [Rel, sortTm, Presentation.rename, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem subst_Rel (substitution : Sub Tower.Head n m)
    (source target : Tower.Tm n) (evidenceLevel : LevelExpr) :
    Presentation.subst substitution (Rel source target evidenceLevel) =
      Rel (Presentation.subst substitution source)
        (Presentation.subst substitution target) evidenceLevel := by
  simp [Rel, sortTm, Presentation.subst, subst_liftSub_wk]

@[simp] theorem rename_applyRel (renameMap : Ren n m)
    (relation source target : Tower.Tm n) :
    Presentation.rename renameMap (applyRel relation source target) =
      applyRel (Presentation.rename renameMap relation)
        (Presentation.rename renameMap source)
        (Presentation.rename renameMap target) :=
  rfl

@[simp] theorem subst_applyRel (substitution : Sub Tower.Head n m)
    (relation source target : Tower.Tm n) :
    Presentation.subst substitution (applyRel relation source target) =
      applyRel (Presentation.subst substitution relation)
        (Presentation.subst substitution source)
        (Presentation.subst substitution target) :=
  rfl

@[simp] theorem rename_evidenceProduct (renameMap : Ren n m)
    (left right : Tower.Tm n) :
    Presentation.rename renameMap (evidenceProduct left right) =
      evidenceProduct (Presentation.rename renameMap left)
        (Presentation.rename renameMap right) := by
  simp [evidenceProduct, Presentation.rename, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem subst_evidenceProduct
    (substitution : Sub Tower.Head n m) (left right : Tower.Tm n) :
    Presentation.subst substitution (evidenceProduct left right) =
      evidenceProduct (Presentation.subst substitution left)
        (Presentation.subst substitution right) := by
  simp [evidenceProduct, Presentation.subst, subst_liftSub_wk]

@[simp] theorem rename_Chain (renameMap : Ren n m)
    (middle earlier later source target : Tower.Tm n) :
    Presentation.rename renameMap (Chain middle earlier later source target) =
      Chain (Presentation.rename renameMap middle)
        (Presentation.rename renameMap earlier)
        (Presentation.rename renameMap later)
        (Presentation.rename renameMap source)
        (Presentation.rename renameMap target) := by
  have renameWeaken (term : Tower.Tm n) :
      Presentation.rename (liftRen renameMap)
          (Presentation.rename wk term) =
        Presentation.rename wk (Presentation.rename renameMap term) := by
    simp [rename_comp]
    apply rename_ext
    intro index
    rfl
  simp [Chain, Presentation.rename, renameWeaken, liftRen]

@[simp] theorem subst_Chain (substitution : Sub Tower.Head n m)
    (middle earlier later source target : Tower.Tm n) :
    Presentation.subst substitution
        (Chain middle earlier later source target) =
      Chain (Presentation.subst substitution middle)
        (Presentation.subst substitution earlier)
        (Presentation.subst substitution later)
        (Presentation.subst substitution source)
        (Presentation.subst substitution target) := by
  simp [Chain, Presentation.subst, subst_liftSub_wk]

/-- Formation of the internal proof-relevant relation former. -/
theorem Rel_hasType {Gamma : Tower.Ctx n}
    {source target : Tower.Tm n}
    {sourceLevel targetLevel evidenceLevel : LevelExpr}
    (sourceTyping : Tower.HasType Gamma source (sortTm sourceLevel))
    (targetTyping : Tower.HasType Gamma target (sortTm targetLevel)) :
    Tower.HasType Gamma (Rel source target evidenceLevel)
      (sortTm
        (.max sourceLevel (.max targetLevel (.succ evidenceLevel)))) := by
  unfold Rel
  apply Presentation.HasType.piForm sourceTyping
    (Tower.IsUniverse.sort sourceLevel)
  · apply Presentation.HasType.piForm
      (by
        simpa [sortTm, Presentation.rename] using targetTyping.weaken)
      (Tower.IsUniverse.sort targetLevel)
    · exact Presentation.HasType.headType
        (Tower.HeadTyping.sort evidenceLevel)
    · exact Tower.IsUniverse.sort (.succ evidenceLevel)
    · exact Tower.Join.sorts targetLevel (.succ evidenceLevel)
  · exact Tower.IsUniverse.sort
      (.max targetLevel (.succ evidenceLevel))
  · exact Tower.Join.sorts sourceLevel
      (.max targetLevel (.succ evidenceLevel))

/-- Applying a well-typed internal relation yields an evidence type at the
declared evidence level. -/
theorem applyRel_hasType {Gamma : Tower.Ctx n}
    {sourceType targetType relation source target : Tower.Tm n}
    {evidenceLevel : LevelExpr}
    (relationTyping : Tower.HasType Gamma relation
      (Rel sourceType targetType evidenceLevel))
    (sourceTyping : Tower.HasType Gamma source sourceType)
    (targetTyping : Tower.HasType Gamma target targetType) :
    Tower.HasType Gamma (applyRel relation source target)
      (sortTm evidenceLevel) := by
  have rawFirst :=
    Presentation.HasType.appElim relationTyping sourceTyping
  have openedFirst :
      Presentation.inst0 source
          (.pi (Presentation.rename wk targetType)
            (sortTm evidenceLevel)) =
        (.pi targetType (sortTm evidenceLevel) : Tower.Tm n) := by
    change
      (Presentation.Tm.pi
        (Presentation.inst0 source (Presentation.rename wk targetType))
          (Presentation.subst (liftSub (subst0 source))
            (sortTm evidenceLevel)) : Tower.Tm n) =
        Presentation.Tm.pi targetType (sortTm evidenceLevel)
    rw [inst0_rename_wk]
    rfl
  have firstApplication :
      Tower.HasType Gamma (.app relation source)
        (.pi targetType (sortTm evidenceLevel)) := by
    change Tower.HasType Gamma (.app relation source)
      (Presentation.inst0 source
        (.pi (Presentation.rename wk targetType)
          (sortTm evidenceLevel))) at rawFirst
    rwa [openedFirst] at rawFirst
  have rawSecond :=
    Presentation.HasType.appElim firstApplication targetTyping
  change Tower.HasType Gamma (applyRel relation source target)
    (sortTm evidenceLevel)
  simpa [applyRel, Presentation.inst0, Presentation.subst, sortTm] using
    rawSecond

/-- Formation of the proof pair used inside `Chain`. -/
theorem evidenceProduct_hasType {Gamma : Tower.Ctx n}
    {left right : Tower.Tm n} {leftLevel rightLevel : LevelExpr}
    (leftTyping : Tower.HasType Gamma left (sortTm leftLevel))
    (rightTyping : Tower.HasType Gamma right (sortTm rightLevel)) :
    Tower.HasType Gamma (evidenceProduct left right)
      (sortTm (.max leftLevel rightLevel)) := by
  unfold evidenceProduct
  apply Presentation.HasType.sigmaForm leftTyping
    (Tower.IsUniverse.sort leftLevel)
  · simpa [sortTm, Presentation.rename] using rightTyping.weaken
  · exact Tower.IsUniverse.sort rightLevel
  · exact Tower.Join.sorts leftLevel rightLevel

/-- Formation of genuine relational composition.  The result level exposes
all three contributors: the middle fibre and the two evidence fibres. -/
theorem Chain_hasType {Gamma : Tower.Ctx n}
    {sourceType middleType targetType : Tower.Tm n}
    {earlier later source target : Tower.Tm n}
    {middleLevel earlierLevel laterLevel : LevelExpr}
    (middleTyping : Tower.HasType Gamma middleType (sortTm middleLevel))
    (earlierTyping : Tower.HasType Gamma earlier
      (Rel sourceType middleType earlierLevel))
    (laterTyping : Tower.HasType Gamma later
      (Rel middleType targetType laterLevel))
    (sourceTyping : Tower.HasType Gamma source sourceType)
    (targetTyping : Tower.HasType Gamma target targetType) :
    Tower.HasType Gamma
      (Chain middleType earlier later source target)
      (sortTm (.max middleLevel (.max earlierLevel laterLevel))) := by
  let extended : Tower.Ctx (n + 1) := .snoc Gamma middleType
  have middleVariable : Tower.HasType extended (.var 0)
      (Presentation.rename wk middleType) := by
    exact Presentation.HasType.var 0
  have earlierTyping' : Tower.HasType extended
      (Presentation.rename wk earlier)
      (Rel (Presentation.rename wk sourceType)
        (Presentation.rename wk middleType) earlierLevel) := by
    simpa only [rename_Rel] using earlierTyping.weaken
  have laterTyping' : Tower.HasType extended
      (Presentation.rename wk later)
      (Rel (Presentation.rename wk middleType)
        (Presentation.rename wk targetType) laterLevel) := by
    simpa only [rename_Rel] using laterTyping.weaken
  have sourceTyping' : Tower.HasType extended
      (Presentation.rename wk source) (Presentation.rename wk sourceType) :=
    sourceTyping.weaken
  have targetTyping' : Tower.HasType extended
      (Presentation.rename wk target) (Presentation.rename wk targetType) :=
    targetTyping.weaken
  have earlierEvidence : Tower.HasType extended
      (applyRel (Presentation.rename wk earlier)
        (Presentation.rename wk source) (.var 0))
      (sortTm earlierLevel) :=
    applyRel_hasType earlierTyping' sourceTyping' middleVariable
  have laterEvidence : Tower.HasType extended
      (applyRel (Presentation.rename wk later)
        (.var 0) (Presentation.rename wk target))
      (sortTm laterLevel) :=
    applyRel_hasType laterTyping' middleVariable targetTyping'
  unfold Chain
  apply Presentation.HasType.sigmaForm middleTyping
    (Tower.IsUniverse.sort middleLevel)
  · exact evidenceProduct_hasType earlierEvidence laterEvidence
  · exact Tower.IsUniverse.sort (.max earlierLevel laterLevel)
  · exact Tower.Join.sorts middleLevel (.max earlierLevel laterLevel)

end Intrinsic

/-! ## Semantic interpretation in relational equipment -/


#print axioms Intrinsic.Rel_hasType
#print axioms Intrinsic.Chain_hasType

end RelationalInternalLanguage

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
