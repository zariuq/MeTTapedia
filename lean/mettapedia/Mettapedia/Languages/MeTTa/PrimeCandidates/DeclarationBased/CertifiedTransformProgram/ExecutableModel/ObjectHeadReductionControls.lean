import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectHeadReduction

/-!
# Controls for the weak-head reduction of the object package

* **Positive: a closed numeral recursion** (`numRec_add_reduces`). With the motive
  `λ _. num`, the base case `0` and the step `λ m h. suc h`,
  `num-rec P 0 s (add 1 1)` reduces in four weak-head steps to
  `suc (num-rec P 0 s (add 1 0))`, a normal form (`numRec_add_normal`). The first
  step reduces the numeral `add 1 1` in place, by the scrutinee congruence; the term
  is no root redex (`numRec_add_not_root`), so without that congruence it would be
  stuck.
* **Negative: a neutral numeral** (`numRec_var_normal`). `num-rec P 0 s x` at a
  variable `x` takes no step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open TelescopeAbstraction (applyClosed)
open Package (numRecName)

namespace CodeModel
namespace HeadReductionControls

variable {n : Nat}

/-- `num-rec P z s q`, annotated. -/
abbrev cnumRecApp (P z s q : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (CTm.appSpine (.const numRecName) [P, z, s]) q

/-- The motive `λ (_ : num). num`. -/
abbrev motiveNum : CTm Tower.Head n := .lam cnum cnum

/-- The step `λ (m : num) (h : num). suc h`. -/
abbrev sucMethod : CTm Tower.Head n := .lam cnum (.lam cnum (csuc (.var 0)))

/-- The numeral `1`. -/
abbrev one : CTm Tower.Head n := csuc czero

/-- **The successor rule of `num-rec`, as an annotated root step**:
`num-rec P z s (suc a) ⟶ s a (num-rec P z s a)`. -/
theorem cnumRecSuc_step (P z s a : CTm Tower.Head n) :
    objectChurch.computation.step (cnumRecApp P z s (csuc a))
      (.app (.app s a) (cnumRecApp P z s a)) := by
  have step := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 0) (by decide))
    (L := iotaLeft numRecName sucN 2 1) (R := iotaRight numRecName 2 1 [(.recursive : CtorField)])
    (show iotaSchema numRecName ctors _ _ from ⟨1, sucN, [.recursive], rfl, rfl⟩)
    (CTm.consSub a (CTm.consSub s (CTm.consSub z (CTm.consSub P Fin.elim0))))
  have eL : elabLeft objectDecls (iotaLeft numRecName sucN 2 1) =
      (.app (.app (.app (.app (.const numRecName) (.var 3)) (.var 2)) (.var 1)) (csuc (.var 0)) :
        CTm Tower.Head 4) := by
    decide
  have eR : elabRight objectDecls (iotaLeft numRecName sucN 2 1)
      (iotaRight numRecName 2 1 [(.recursive : CtorField)]) =
      (.app (.app (.var 1) (.var 0))
        (.app (.app (.app (.app (.const numRecName) (.var 3)) (.var 2)) (.var 1)) (.var 0)) :
        CTm Tower.Head 4) := by
    decide
  rw [eL, eR] at step
  exact step

/-- `num-rec (λ _. num) 0 (λ m h. suc h) q`, closed. -/
abbrev recAt (q : CTm Tower.Head 0) : CTm Tower.Head 0 := cnumRecApp motiveNum czero sucMethod q

/-- The term of the positive control: `num-rec (λ _. num) 0 (λ m h. suc h) (add 1 1)`. -/
abbrev closedRec : CTm Tower.Head 0 := recAt (cadd one one)

/-- **Positive**: the closed recursion reduces, its numeral first in place, to
`suc (num-rec P 0 s (add 1 0))`. -/
theorem numRec_add_reduces :
    Relation.ReflTransGen objectHeadReduction.step closedRec (csuc (recAt (cadd one czero))) := by
  have s₁ : objectHeadReduction.step closedRec (recAt (csuc (cadd one czero))) :=
    objectHeadReduction_numRec (objectHeadReduction.root (caddSuc_step one czero))
  have s₂ : objectHeadReduction.step (recAt (csuc (cadd one czero)))
      (.app (.app sucMethod (cadd one czero)) (recAt (cadd one czero))) :=
    objectHeadReduction.root (cnumRecSuc_step _ _ _ _)
  have s₃ : objectHeadReduction.step
      (.app (.app sucMethod (cadd one czero)) (recAt (cadd one czero)))
      (.app (.lam cnum (csuc (.var 0))) (recAt (cadd one czero))) :=
    objectHeadReduction.appFun _ (objectHeadReduction.beta cnum (.lam cnum (csuc (.var 0))) _)
  have s₄ : objectHeadReduction.step (.app (.lam cnum (csuc (.var 0))) (recAt (cadd one czero)))
      (csuc (recAt (cadd one czero))) :=
    objectHeadReduction.beta cnum (csuc (.var 0)) _
  exact ((((Relation.ReflTransGen.single s₁).tail s₂).tail s₃).tail s₄)

/-- The end of the positive control is a weak-head normal form. -/
theorem numRec_add_normal : objectHeadReduction.Normal (csuc (recAt (cadd one czero))) :=
  objectHeadReduction.normal_suc _

/-- The closed recursion is no root redex: its numeral `add 1 1` is not a numeral in
constructor form, so the first step can only be the scrutinee step. -/
theorem numRec_add_not_root (u : CTm Tower.Head 0) :
    ¬ objectChurch.computation.step closedRec u := by
  intro root
  have root' : objectChurch.computation.step
      (CTm.appSpine (.const numRecName) ([motiveNum, czero, sucMethod] ++ cadd one one :: []))
      u := root
  exact CWhStepR.not_scrutinee_of_root objectShape (objectRoles_of_roles roles_numRec nofun)
    root' _ (CWhStepR.root (caddSuc_step one czero))

/-- **Negative**: a recursion whose numeral is a variable takes no step. -/
theorem numRec_var_normal :
    objectHeadReduction.Normal (cnumRecApp motiveNum czero sucMethod (.var 0) : CTm Tower.Head 1) :=
  fun u => CWhStepR.not_of_whnf
    ((Neutral.stuck_single (c := numRecName) (arity := 4)
      (before := [(motiveNum : CTm Tower.Head 1).erase, czero.erase, sucMethod.erase])
      (after := []) (objectRoles_of_roles roles_numRec nofun) rfl (.var 0)).whnf objectShape) u

end HeadReductionControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
