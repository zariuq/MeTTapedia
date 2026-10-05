import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredCommunication
import Mettapedia.GSLT.LanguageDef.WellSortedClosing
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping

/-!
# Named pi terms in the authored GSLT

Named processes are sorted open terms of the authored presentation. Parallel
composition carries its declared monoid laws; raw communication results and
flattened named-process results therefore represent the same semantic state.
Communication and restriction descent connect to the generated step-future
modality through those equations.

The presentation uses one process sort for its open name variables. These
comparisons concern the image of named processes and do not identify every
closed process-valued channel with a textbook atomic pi name. Scope extrusion
and structural replication unfolding require further equation comparisons.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

/-- The authored parallel constructor declares the bag monoid with inaction as its unit. -/
theorem piBagTheory : BagTheory piCalc piCalc.terms[1] (some "PiNil") where
  equationsEmpty := rfl
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  otherParameters := by
    intro rule member different parameter present
    simp only [piCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact False.elim (different rfl)
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      all_goals rfl
  unitAuthored := by
    intro unit same
    cases Option.some.inj same
    exact ⟨piCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩

private theorem typed_components {free : FreeTypeContext} {bound : List TypeExpr}
    {P : Pattern} (typed : HasType piCalc free bound P (.base "Proc")) :
    ElementsHaveType piCalc free bound (piComponents P) (.base "Proc") := by
  cases P <;> try exact .cons typed (.nil _ _)
  case collection kind elements rest =>
    cases kind <;> cases rest <;> try exact .cons typed (.nil _ _)
    exact (bag_typing piBagTheory typed rfl).2.2

/-- Parallel composition preserves the process sort in any typing context. -/
theorem piPar_hasType {free : FreeTypeContext} {bound : List TypeExpr}
    {P Q : Pattern}
    (hP : HasType piCalc free bound P (.base "Proc"))
    (hQ : HasType piCalc free bound Q (.base "Proc")) :
    HasType piCalc free bound (piPar P Q) (.base "Proc") := by
  rw [piPar_components]
  apply bag_hasType piBagTheory
  apply elementsHaveType_iff.mpr
  intro element member
  rcases List.mem_append.mp member with member | member
  · exact elementsHaveType_iff.mp (typed_components hP) element member
  · exact elementsHaveType_iff.mp (typed_components hQ) element member

/-- Flattened parallel composition is equivalent to its two-component bag. -/
theorem piPar_equivalent_bag {free : FreeTypeContext} {bound : List TypeExpr}
    {P Q : Pattern}
    (hP : HasType piCalc free bound P (.base "Proc"))
    (hQ : HasType piCalc free bound Q (.base "Proc")) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag [P, Q] none) (piPar P Q) := by
  have initial : HasType piCalc free bound (.collection .hashBag [P, Q] none)
      (.base "Proc") := bag_hasType piBagTheory (.cons hP (.cons hQ (.nil _ _)))
  have sorted : SortedAt piCalc (.collection .hashBag [P, Q] none) "Proc" :=
    ⟨free, bound, initial⟩
  unfold piPar
  split
  · rename_i first second
    have firstStep := DerivedInstance.flatten piBagTheory.bagAlgebraRule rfl
      (pre := []) (inner := first) (post := [.collection .hashBag second none]) sorted
    have intermediate := derived_hasType piBagTheory firstStep initial rfl
    have secondStep := DerivedInstance.flatten piBagTheory.bagAlgebraRule rfl
      (pre := first) (inner := second) (post := []) ⟨free, bound, intermediate⟩
    exact .trans _ _ _ (derivedInstance_equivalent firstStep)
      (by simpa only [EquationEquiv, List.append_nil, List.nil_append] using derivedInstance_equivalent secondStep)
  · rename_i first _
    exact derivedInstance_equivalent
      (.flatten piBagTheory.bagAlgebraRule rfl (pre := []) (inner := first) (post := [Q]) sorted)
  · rename_i second _
    simpa only [List.append_nil, List.cons_append, List.nil_append] using derivedInstance_equivalent
      (DerivedInstance.flatten piBagTheory.bagAlgebraRule rfl
        (pre := [P]) (inner := second) (post := []) sorted)
  · exact .refl _

/-- Free atomic names of the named fragment, at the authored process sort. -/
def piNameContext : FreeTypeContext := fun _ => some (.base "Proc")

/-- Every named process inhabits the process sort in the open name context. -/
theorem piToPattern_hasType (P : Process) :
    HasType piCalc piNameContext [] (piToPattern P) (.base "Proc") := by
  induction P with
  | nil =>
      exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 0) (by decide))
        (by simp [UsesBareCollection, piCalc]) .nil
  | par P Q ihP ihQ => exact piPar_hasType ihP ihQ
  | input channel bound P ih =>
      have body := ih.closeFVar bound (.base "Proc") rfl
      exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 2) (by decide))
        (by simp [UsesBareCollection, piCalc]) (.cons trivial rfl (.fvar rfl)
          (.cons trivial rfl (.lambda body) .nil))
  | output channel datum =>
      exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 3) (by decide))
        (by simp [UsesBareCollection, piCalc]) (.cons trivial rfl (.fvar rfl) (.cons trivial rfl (.fvar rfl) .nil))
  | nu bound P ih =>
      have body := ih.closeFVar bound (.base "Proc") rfl
      exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 4) (by decide))
        (by simp [UsesBareCollection, piCalc]) (.cons trivial rfl (.lambda body) .nil)
  | replicate channel bound P ih =>
      have body := ih.closeFVar bound (.base "Proc") rfl
      exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 5) (by decide))
        (by simp [UsesBareCollection, piCalc]) (.cons trivial rfl (.fvar rfl)
          (.cons trivial rfl (.lambda body) .nil))

/-- The encoding supplies the sort evidence required by the generated bag laws. -/
theorem piToPattern_sorted (P : Process) : SortedAt piCalc (piToPattern P) "Proc" :=
  ⟨piNameContext, [], piToPattern_hasType P⟩

/-- Named COMM reaches its exact encoded result in the equation-saturated GSLT. -/
theorem piComm_named_semantic_step (channel bound datum : Name) (P : Process) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern (.par (.input channel bound P) (.output channel datum)))
      (piToPattern (P.substitute bound datum)) := by
  refine ⟨_, _, .refl _, piComm_named_step channel bound datum P [], ?_⟩
  exact derivedInstance_equivalent (.singleton piBagTheory.bagAlgebraRule rfl
    ⟨piNameContext, [], bag_hasType piBagTheory (.cons (piToPattern_hasType _) (.nil _ _))⟩)

open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Restriction preserves semantic steps, including equation changes of representative. -/
theorem piResCong_semantic_step {source target : Pattern}
    (step : StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc source target) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc
      (.apply "PiNu" [.lambda none source])
      (.apply "PiNu" [.lambda none target]) := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  let context : OneHoleContext := .apply "PiNu" [] (.lambda none .hole) []
  exact ⟨context.fill redex, context.fill contractum,
    equationEquiv_fill context before, piResCong_step firing,
    equationEquiv_fill context after⟩

theorem piComm_named_diamond
    (property : EquationPredicate (langGSLT piCalc))
    (channel bound datum : Name) (P : Process)
    (holds : property (piToPattern (P.substitute bound datum))) :
    piCalcDiamond property
      (piToPattern (.par (.input channel bound P) (.output channel datum))) := by
  change gsltDiamond (langGSLT piCalc) property.1 _
  erw [gsltDiamond_spec]
  exact ⟨_, piComm_named_semantic_step channel bound datum P, holds⟩

theorem piBag_semantic_step {source target : Pattern} (rest : List Pattern)
    (step : StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc source target) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag (source :: rest) none)
      (.collection .hashBag (target :: rest) none) := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  let context : OneHoleContext := .collection .hashBag [] .hole rest none
  exact ⟨context.fill redex, context.fill contractum,
    equationEquiv_fill context before, piParCong_step rest firing,
    equationEquiv_fill context after⟩

theorem piPar_named_semantic_step {P P' : Process} (Q : Process)
    (step : StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern P) (piToPattern P')) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern (.par P Q)) (piToPattern (.par P' Q)) := by
  exact stepModuloEquations_change_source
    (piPar_equivalent_bag (piToPattern_hasType P) (piToPattern_hasType Q))
    (stepModuloEquations_resp_right _ _ (piBag_semantic_step [piToPattern Q] step)
      (piPar_equivalent_bag (piToPattern_hasType P') (piToPattern_hasType Q)))

theorem piRepComm_named_semantic_step (channel bound datum : Name) (P : Process) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern (.par (.replicate channel bound P) (.output channel datum)))
      (piToPattern (.par (P.substitute bound datum) (.replicate channel bound P))) := by
  exact ⟨_, _, .refl _, piRepComm_named_step channel bound datum P [],
    piPar_equivalent_bag (piToPattern_hasType _) (piToPattern_hasType _)⟩

theorem piPar_equivalent_congr {free : FreeTypeContext} {bound : List TypeExpr}
    {P P' Q Q' : Pattern}
    (hP : HasType piCalc free bound P (.base "Proc"))
    (hP' : HasType piCalc free bound P' (.base "Proc"))
    (hQ : HasType piCalc free bound Q (.base "Proc"))
    (hQ' : HasType piCalc free bound Q' (.base "Proc"))
    (first : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc P P')
    (second : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc Q Q') :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piPar P Q) (piPar P' Q') := by
  have left := equationEquiv_fill (.collection .hashBag [] .hole [Q] none) first
  have right := equationEquiv_fill (.collection .hashBag [P'] .hole [] none) second
  exact .trans _ _ _ (.symm _ _ (piPar_equivalent_bag hP hQ))
    (.trans _ _ _ left (.trans _ _ _ right (piPar_equivalent_bag hP' hQ')))

theorem piPar_equivalent_comm {free : FreeTypeContext} {bound : List TypeExpr}
    {P Q : Pattern}
    (hP : HasType piCalc free bound P (.base "Proc"))
    (hQ : HasType piCalc free bound Q (.base "Proc")) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piPar P Q) (piPar Q P) := by
  have swapped := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
    (DerivedInstance.bagPerm piBagTheory.bagCarrier
      ⟨free, bound, bag_hasType piBagTheory (.cons hP (.cons hQ (.nil _ _)))⟩
      (List.Perm.swap Q P []))
  exact .trans _ _ _ (.symm _ _ (piPar_equivalent_bag hP hQ))
    (.trans _ _ _ swapped (piPar_equivalent_bag hQ hP))

theorem piPar_equivalent_unit_left {free : FreeTypeContext} {bound : List TypeExpr}
    {P : Pattern} (hP : HasType piCalc free bound P (.base "Proc")) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piPar (.apply "PiNil" []) P) P := by
  have nilTyped : HasType piCalc free bound (.apply "PiNil" []) (.base "Proc") :=
    .constructor (List.getElem_mem (l := piCalc.terms) (n := 0) (by decide))
      (by simp [UsesBareCollection, piCalc]) .nil
  have erase := DerivedInstance.unitElim piBagTheory.bagAlgebraRule rfl
    (pre := []) (post := [P])
    ⟨free, bound, bag_hasType piBagTheory (.cons nilTyped (.cons hP (.nil _ _)))⟩
  have single := DerivedInstance.singleton piBagTheory.bagAlgebraRule rfl
    ⟨free, bound, bag_hasType piBagTheory (.cons hP (.nil _ _))⟩
  exact .trans _ _ _ (.symm _ _ (piPar_equivalent_bag nilTyped hP))
    (.trans _ _ _ (derivedInstance_equivalent erase) (derivedInstance_equivalent single))

theorem piPar_equivalent_unit_right {free : FreeTypeContext} {bound : List TypeExpr}
    {P : Pattern} (hP : HasType piCalc free bound P (.base "Proc")) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piPar P (.apply "PiNil" [])) P := by
  have nilTyped : HasType piCalc free bound (.apply "PiNil" []) (.base "Proc") :=
    .constructor (List.getElem_mem (l := piCalc.terms) (n := 0) (by decide))
      (by simp [UsesBareCollection, piCalc]) .nil
  exact .trans _ _ _ (piPar_equivalent_comm hP nilTyped) (piPar_equivalent_unit_left hP)

theorem piPar_equivalent_assoc {free : FreeTypeContext} {bound : List TypeExpr}
    {P Q R : Pattern}
    (hP : HasType piCalc free bound P (.base "Proc"))
    (hQ : HasType piCalc free bound Q (.base "Proc"))
    (hR : HasType piCalc free bound R (.base "Proc")) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piPar (piPar P Q) R) (piPar P (piPar Q R)) := by
  have leftOuter := piPar_equivalent_bag (piPar_hasType hP hQ) hR
  have leftInner := equationEquiv_fill (.collection .hashBag [] .hole [R] none)
    (.symm _ _ (piPar_equivalent_bag hP hQ))
  have leftFlat := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
    (DerivedInstance.flatten piBagTheory.bagAlgebraRule rfl
      (pre := []) (inner := [P,Q]) (post := [R])
      ⟨free, bound, bag_hasType piBagTheory (.cons
        (bag_hasType piBagTheory (.cons hP (.cons hQ (.nil _ _)))) (.cons hR (.nil _ _)))⟩)
  have rightOuter := piPar_equivalent_bag hP (piPar_hasType hQ hR)
  have rightInner := equationEquiv_fill (.collection .hashBag [P] .hole [] none)
    (.symm _ _ (piPar_equivalent_bag hQ hR))
  have rightFlat := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
    (DerivedInstance.flatten piBagTheory.bagAlgebraRule rfl
      (pre := [P]) (inner := [Q,R]) (post := [])
      ⟨free, bound, bag_hasType piBagTheory (.cons hP (.cons
        (bag_hasType piBagTheory (.cons hQ (.cons hR (.nil _ _)))) (.nil _ _)))⟩)
  have left : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piPar (piPar P Q) R) (.collection .hashBag [P,Q,R] none) :=
    .trans _ _ _ (.symm _ _ leftOuter) (.trans _ _ _ leftInner leftFlat)
  have right : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piPar P (piPar Q R)) (.collection .hashBag [P,Q,R] none) := by
    exact .trans _ _ _ (.symm _ _ rightOuter) (.trans _ _ _ rightInner rightFlat)
  exact .trans _ _ _ left (.symm _ _ right)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
