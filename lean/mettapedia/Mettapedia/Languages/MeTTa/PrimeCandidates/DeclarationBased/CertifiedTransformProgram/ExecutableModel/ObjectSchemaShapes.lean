import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRootPreservation

/-!
# The shapes of the object package's rewrite schemas

For each rewrite schema of the object package, read off its declarations by evaluation:

* the types the positions of its left side require of its metavariables, as the lookups of
  a telescope (`…_knowledge`);
* the equations of its reflexivity positions (`…_equations`);
* its elaborated left and right sides (`…_elabLeft`, `…_elabRight`).

The typing of a schema's right side, the premises of its instances and its validity in a
model are all stated over these. The shapes of the two equations of addition and of the
equation of `eqAt` are with their root steps in `ObjectTemplates`, and those of the identity
eliminator's contractum in `ObjectRootPreservation`.

The decoding schemas are stated at every simple type (`all_knowledge`, `eq_knowledge`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open FormationSensitiveHOLInterface (typeAt typeAt_rename)
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName eqAtTelescope transportTelescope composeTelescope)
open Mettapedia.Logic

namespace CodeModel

/-! ## The shapes of the schemas -/

section Shapes

theorem numRecZero_knowledge : ∀ i, patternKnowledge objectDecls none
    (iotaLeft (Head := Tower.Head) numRecName zeroN 2 0) i = some (cRecTele.lookup i) := by
  decide

theorem numRecZero_equations :
    patternEquations objectDecls none (iotaLeft (Head := Tower.Head) numRecName zeroN 2 0) = [] := by
  decide

theorem numRecZero_elabLeft : elabLeft objectDecls (iotaLeft (Head := Tower.Head) numRecName zeroN 2 0) =
    (.app (.app (.app (.app (.const numRecName) (.var 2)) (.var 1)) (.var 0)) czero :
      CTm Tower.Head 3) := by
  decide

theorem numRecZero_elabRight : elabRight objectDecls (iotaLeft numRecName zeroN 2 0)
    (iotaRight numRecName 2 0 ([] : List CtorField)) = (.var 1 : CTm Tower.Head 3) := by
  decide

theorem numRecSuc_knowledge : ∀ i, patternKnowledge objectDecls none
    (iotaLeft (Head := Tower.Head) numRecName sucN 2 1) i =
      some ((CCtx.snoc cRecTele cnum).lookup i) := by
  decide

theorem numRecSuc_elabLeft : elabLeft objectDecls (iotaLeft (Head := Tower.Head) numRecName sucN 2 1) =
    (.app (.app (.app (.app (.const numRecName) (.var 3)) (.var 2)) (.var 1)) (csuc (.var 0)) :
      CTm Tower.Head 4) := by
  decide

theorem numRecSuc_elabRight : elabRight objectDecls (iotaLeft numRecName sucN 2 1)
    (iotaRight numRecName 2 1 [(.recursive : CtorField)]) =
      (.app (.app (.var 1) (.var 0))
        (.app (.app (.app (.app (.const numRecName) (.var 3)) (.var 2)) (.var 1)) (.var 0)) :
        CTm Tower.Head 4) := by
  decide

theorem powZero_knowledge : ∀ i, patternKnowledge objectDecls none
    (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN)) i =
      some ((CCtx.snoc .nil cset : CCtx Tower.Head 1).lookup i) := by
  decide

theorem powZero_elabLeft : elabLeft objectDecls
    (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN)) =
      (.app (.app (.const powN) czero) (.var 0) : CTm Tower.Head 1) := by
  decide

theorem powZero_elabRight : elabRight objectDecls
    (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN))
    (Presentation.subst (hypSub powN powEntries 0 1 []) (powBody zeroN [])) =
      (.var 0 : CTm Tower.Head 1) := by
  decide

theorem powSuc_knowledge : ∀ i, patternKnowledge objectDecls none
    (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN)) i =
      some ((CCtx.snoc (.snoc .nil cnum) cset : CCtx Tower.Head 2).lookup i) := by
  decide

theorem powSuc_elabLeft : elabLeft objectDecls
    (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN)) =
      (.app (.app (.const powN) (csuc (.var 1))) (.var 0) : CTm Tower.Head 2) := by
  decide

theorem powSuc_elabRight : elabRight objectDecls
    (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN))
    (Presentation.subst (hypSub powN powEntries 0 1 [.recursive]) (powBody sucN [.recursive])) =
      (.app (.const powerN) (.app (.app (.const powN) (.var 1)) (.var 0)) : CTm Tower.Head 2) := by
  decide

theorem iterZero_knowledge : ∀ i, patternKnowledge objectDecls none
    (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName)) i =
      some (cIterTele.lookup i) := by
  decide

theorem iterZero_elabLeft : elabLeft objectDecls
    (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName)) =
      (.app (.app (.app (.app (.app (.app (.const iterName) czero) (.var 4)) (.var 3)) (.var 2))
        (.var 1)) (.var 0) : CTm Tower.Head 5) := by
  decide

theorem iterZero_elabRight : elabRight objectDecls
    (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
    (Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN [])) =
      (.pair (.var 1) (.var 0) : CTm Tower.Head 5) := by
  decide

theorem iterSuc_knowledge : ∀ i, patternKnowledge objectDecls none
    (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName)) i =
      some (cIterSucTele.lookup i) := by
  decide

theorem iterSuc_elabLeft : elabLeft objectDecls
    (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName)) =
      (.app (.app (.app (.app (.app (.app (.const iterName) (csuc (.var 5))) (.var 4)) (.var 3))
        (.var 2)) (.var 1)) (.var 0) : CTm Tower.Head 6) := by
  decide

theorem iterSuc_elabRight : elabRight objectDecls
    (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
    (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive]) (iterBody sucN [.recursive])) =
      (.app (.lam (.sigma (.var 4) (.app (.var 4) (.var 0)))
          (.app (.app (.app (.app (.app (.app (.const iterName) (.var 6)) (.var 5)) (.var 4))
            (.var 3)) (.fst (.var 0))) (.snd (.var 0))))
        (.app (.app (.var 2) (.var 1)) (.var 0)) : CTm Tower.Head 6) := by
  decide

theorem j_elabLeft : elabLeft objectDecls (eliminatorLeft (Head := Tower.Head) jName) =
    (.app (.app (.app (.app (.app (.app (.const jName) (.var 5)) (.var 4)) (.var 3)) (.var 2))
      (.var 1)) (.refl (.var 0)) : CTm Tower.Head 6) := by
  decide

end Shapes

/-! ## The decoding of the codes -/

/-- The left side of the decoding of an implication, `holds (imp p q)`. -/
abbrev impLeft : Tm Tower.Head 2 :=
  .app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0))

/-- Its right side, `Π (_ : holds p). holds q`. -/
abbrev impRight : Tm Tower.Head 2 :=
  .pi (.app (.const holdsN) (.var 1)) (.app (.const holdsN) (Presentation.rename wk (.var 0)))

/-- The left side of the decoding of a quantifier, `holds (all@A f)`. -/
abbrev allLeft (type : HOL.Ty SetProfile.SetBase) : Tm Tower.Head 1 :=
  .app (.const holdsN) (.app (.const (SetProfile.allName type)) (.var 0))

/-- Its right side, `Π (x : A). holds (f x)`. -/
abbrev allRight (type : HOL.Ty SetProfile.SetBase) : Tm Tower.Head 1 :=
  .pi (liftClosed (typeAt SetProfile.types 0 type))
    (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))

/-- The left side of the decoding of an equation, `holds (eq@A x y)`. -/
abbrev eqLeft (type : HOL.Ty SetProfile.SetBase) : Tm Tower.Head 2 :=
  .app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0))

/-- Its right side, `Id A x y`. -/
abbrev eqRight (type : HOL.Ty SetProfile.SetBase) : Tm Tower.Head 2 :=
  .id (liftClosed (typeAt SetProfile.types 0 type)) (.var 1) (.var 0)

section DecoderShapes

theorem imp_knowledge : ∀ i, patternKnowledge objectDecls none impLeft i =
    some ((liftCtx (.snoc (.snoc .nil programCodes.propT) programCodes.propT)).lookup i) := by
  intro i
  revert i
  decide

theorem imp_equations : patternEquations objectDecls none impLeft = [] := by
  decide

theorem imp_elabRight : elabRight objectDecls impLeft impRight = liftTm impRight := by
  rw [elabRight, elab_lamFree _ rfl]

theorem all_knowledge (type : HOL.Ty SetProfile.SetBase) : ∀ i,
    patternKnowledge objectDecls none (allLeft type) i =
      some ((liftCtx (.snoc .nil (typeAt SetProfile.types 0 (.arr type .prop)))).lookup i) := by
  intro i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp only [patternKnowledge, elaborate, objectDecls_allName, Option.map_some, Knowledge.merge,
    Knowledge.empty, if_true]
  rw [show SetProfile.allType type = typeAt SetProfile.types 0 (.arr (.arr type .prop) .prop) from rfl,
    liftClosed_liftTm_typeAt]
  simp only [liftCtx_lookup, Ctx.lookup_snoc_zero, typeAt_rename]
  rfl

theorem liftClosed_typeAt (type : HOL.Ty SetProfile.SetBase) {n : Nat} :
    (liftClosed (typeAt SetProfile.types 0 type) : Tower.Tm n) = typeAt SetProfile.types n type := by
  unfold Presentation.liftClosed
  rw [typeAt_rename]

theorem all_elabRight (type : HOL.Ty SetProfile.SetBase) :
    elabRight objectDecls (allLeft type) (allRight type) = liftTm (allRight type) := by
  have lf : lamFree (allRight type) = true := by
    simp only [lamFree, Presentation.liftClosed, typeAt_rename, lamFree_typeAt,
      Presentation.rename, Bool.and_self]
  rw [elabRight, elab_lamFree _ lf]

theorem eq_knowledge (type : HOL.Ty SetProfile.SetBase) : ∀ i,
    patternKnowledge objectDecls none (eqLeft type) i =
      some ((liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 type))
        (typeAt SetProfile.types 1 type))).lookup i) := by
  intro i
  simp only [patternKnowledge, elaborate, objectDecls_eqName, Option.map_some,
    Knowledge.merge, Knowledge.empty, liftClosed_liftTm_eqType, CTm.inst0, CTm.subst,
    subst_liftTm_typeAt, liftCtx_lookup]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.isValue, zero_ne_one, if_false, if_true]
    rw [Ctx.lookup_snoc_zero, typeAt_rename]
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    simp only [Fin.succ_zero_eq_one, Fin.isValue, if_true]
    change some _ = some (liftTm (Presentation.rename wk (Presentation.rename wk
      (typeAt SetProfile.types 0 type))))
    rw [typeAt_rename, typeAt_rename]

theorem eq_elabRight (type : HOL.Ty SetProfile.SetBase) :
    elabRight objectDecls (eqLeft type) (eqRight type) = liftTm (eqRight type) := by
  have lf : lamFree (eqRight type) = true := by
    simp only [lamFree, Presentation.liftClosed, typeAt_rename, lamFree_typeAt, Bool.and_self]
  rw [elabRight, elab_lamFree _ lf]

end DecoderShapes

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
