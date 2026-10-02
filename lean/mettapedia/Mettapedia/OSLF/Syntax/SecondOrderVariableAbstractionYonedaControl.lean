import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionControls
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramProducts
import Mettapedia.OSLF.Syntax.CategoricalBindingUniversal

/-!
# Contextual recovery in the selected program presheaves

The authored schema P() = c identifies every admitted instance, including
ordinary local variables. Its selected open and closed program presheaves
therefore agree on this collapse. This control checks the actual classifier
and its Yoneda program objects; it does not establish the binder comparison
for arbitrary presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open Mettapedia.OSLF.Binding.CategoricalBindingModel

abbrev noRules : List (LocalRule signature) := []
abbrev ActualClassifier := Classifier noRules equations
abbrev ActualPresheaf := Presheaf.{0} noRules equations

/-- The authored equation identifies an arbitrary contextual schema body. -/
theorem contextualTerm_eq_constant (X : Object signature) (Γ : Ctx signature)
    (t : Term (withMetas signature X.arities) Γ ()) :
    EqClosure (equations.map (liftEquation X)) t
      (embed (S := signature) (M := X.arities) constant) := by
  let body : ContextualAssignment (withMetas signature X.arities) schemaMetas Γ :=
    fun i => Fin.cases t (fun i => Fin.elim0 i) i
  have generated := EqClosure.ax (E := equations.map (liftEquation X))
    (⟨0, by simp [equations]⟩) body
    (fun _ v => Term.var v) (fun _ v => nomatch v)
  change EqClosure (equations.map (liftEquation X))
    (bind (fun _ v => Term.var v) t)
    (embed (S := signature) (M := X.arities) constant) at generated
  rw [bind_id] at generated
  exact generated

/-- The closed fragment is an instance of the contextual collapse. -/
theorem closedTerm_eq_constant (X : Object signature)
    (t : Term (withMetas signature X.arities) [] ()) :
    EqClosure (equations.map (liftEquation X)) t
      (embed (S := signature) (M := X.arities) constant) :=
  contextualTerm_eq_constant X [] t

/-- Every assignment to a selected program object is the same equation class,
for open as well as closed ordinary-variable contexts. -/
theorem programArrows_subsingleton (X : Base equations) (Γ : Ctx signature) :
    Subsingleton (X ⟶ (⟨single signature Γ ()⟩ : Base equations)) := by
  constructor
  intro f g
  induction f using Quot.ind with
  | _ first =>
    induction g using Quot.ind with
    | _ second =>
      apply _root_.CategoryTheory.Quotient.sound
      intro i
      rcases i with ⟨n, bound⟩
      have zero : n = 0 := by change n < 1 at bound; omega
      subst n
      exact (contextualTerm_eq_constant X.as Γ (first ⟨0, bound⟩)).trans
        (contextualTerm_eq_constant X.as Γ (second ⟨0, bound⟩)).symm

/-- At every classifier stage all selected program sections are unique,
including stages carrying event variables. -/
theorem program_sections_subsingleton (Γ : Ctx signature) (a : ActualClassifierᵒᵖ) :
    Subsingleton ((program.{0} noRules equations Γ ()).obj a) := by
  have : Subsingleton (a.unop.base ⟶ (⟨single signature Γ ()⟩ : Base equations)) :=
    programArrows_subsingleton a.unop.base Γ
  constructor
  intro x y
  apply ULift.ext
  apply (programHomEquiv noRules equations a.unop ⟨single signature Γ ()⟩).injective
  exact Subsingleton.elim _ _

/-- Pointwise uniqueness gives uniqueness of natural transformations into
this actual selected program presheaf. -/
theorem program_homs_subsingleton (Γ : Ctx signature) (P : ActualPresheaf) :
    Subsingleton (P ⟶ program.{0} noRules equations Γ ()) := by
  constructor
  intro f g
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  exact (program_sections_subsingleton Γ a).elim _ _

abbrev emptyProgramBase : Base equations :=
  (authoredEquationPresentation signature equations).quotientFunctor.obj oldObject
abbrev emptyProgramStage : ActualClassifier :=
  (programSection noRules equations).obj emptyProgramBase

/-- The actual equation-class assignment of an ordinary variable. -/
def ordinaryProgramArrow :
    emptyProgramStage ⟶ (programSection noRules equations).obj
      (⟨single signature [()] ()⟩ : Base equations) :=
  (programSection noRules equations).map
    ((authoredEquationPresentation signature equations).quotientFunctor.map
      ((termsRepresented signature oldObject [()] ()).symm ordinaryVariable))

/-- The actual equation-class assignment of the constant in the same context. -/
def constantProgramArrow :
    emptyProgramStage ⟶ (programSection noRules equations).obj
      (⟨single signature [()] ()⟩ : Base equations) :=
  (programSection noRules equations).map
    ((authoredEquationPresentation signature equations).quotientFunctor.map
      ((termsRepresented signature oldObject [()] ()).symm oldConstant))

/-- The ordinary-variable and constant assignments agree in the actual
contextual equation-class classifier. -/
theorem ordinaryProgramArrow_eq_constant : ordinaryProgramArrow = constantProgramArrow := by
  have same : (authoredEquationPresentation signature equations).quotientFunctor.map
      ((termsRepresented signature oldObject [()] ()).symm ordinaryVariable) =
      (authoredEquationPresentation signature equations).quotientFunctor.map
        ((termsRepresented signature oldObject [()] ()).symm oldConstant) := by
    apply _root_.CategoryTheory.Quotient.sound
    intro i
    rcases i with ⟨n, bound⟩
    have zero : n = 0 := by change n < 1 at bound; omega
    subst n
    exact ordinaryVariable_eq_constant
  exact congrArg ((programSection noRules equations).map) same

/-- The formerly discrepant open points agree after the contextual repair. -/
theorem openProgram_sections_subsingleton :
    Subsingleton ((program.{0} noRules equations [()] ()).obj
      (Opposite.op emptyProgramStage)) :=
  program_sections_subsingleton [()] (Opposite.op emptyProgramStage)

/-- The collapse is caused by the authored schema: the corresponding raw
variable and constant remain unrelated in the empty equation presentation. -/
theorem contextual_collapse_requires_equation :
    ordinaryProgramArrow = constantProgramArrow ∧
      ¬ EqClosure ([] : List (EqAxiom (withMetas signature noMetas) schemaMetas))
        ordinaryVariable oldConstant :=
  ⟨ordinaryProgramArrow_eq_constant, ordinaryVariable_ne_constant_without_equations⟩

end Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction.Controls
