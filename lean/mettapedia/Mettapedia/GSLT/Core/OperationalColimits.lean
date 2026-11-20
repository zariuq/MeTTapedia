import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Constructed colimits of forward operational theories

Stage terms are identified along the diagram's transport maps. Authored
equations remain a separate generated setoid on that carrier: equationally
equivalent terms need not be equal as carrier elements. Ambient steps are
the images of stage steps, saturated by the generated equations.

The shape is small in the terms' universe. These are general small colimits
of unstructured term carriers with equations and rewrites; term constructors
and presentation morphisms have not been added to this category. No colimit
in the covered or bisimilarity-preserving categories is asserted.

Every operational cocone has a unique descended operational translation.
This constructs the ambient object and its universal property. Finite
presentability of authored presentations, effective enumeration and the
compiler's realization of a growing presentation are separate obligations.
No coverage, finite branching, termination or stage-relative absence is
inferred from a forward diagram.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [SmallCategory J]

/-- A term with the stage in which it was authored. -/
abbrev StageTerm (diagram : J ⥤ OperationalTheory.{u}) :=
  Σ stage : J, (diagram.obj stage).theory.Term

/-- Only diagram transport generates equalities of the ambient carrier. -/
inductive Transport (diagram : J ⥤ OperationalTheory.{u}) :
    StageTerm diagram → StageTerm diagram → Prop where
  | along {first second : J} (route : first ⟶ second)
      (term : (diagram.obj first).theory.Term) :
      Transport diagram ⟨first, term⟩ ⟨second, (diagram.map route).mapTerm term⟩

abbrev Term (diagram : J ⥤ OperationalTheory.{u}) := Quot (Transport diagram)

def inject (diagram : J ⥤ OperationalTheory.{u}) (stage : J)
    (term : (diagram.obj stage).theory.Term) : Term diagram :=
  Quot.mk _ ⟨stage, term⟩

theorem inject_along (diagram : J ⥤ OperationalTheory.{u})
    {first second : J} (route : first ⟶ second)
    (term : (diagram.obj first).theory.Term) :
    inject diagram first term = inject diagram second ((diagram.map route).mapTerm term) :=
  Quot.sound (.along route term)

/-- Every carrier term has an authored stage representative. This is not
yet a common-stage factorization for a finite execution or presentation. -/
theorem term_from_stage (diagram : J ⥤ OperationalTheory.{u}) (term : Term diagram) :
    ∃ stage value, inject diagram stage value = term := by
  refine Quot.inductionOn term ?_
  rintro ⟨stage, value⟩
  exact ⟨stage, value, rfl⟩

/-- The authored equations supplied by individual stages. -/
inductive Equation (diagram : J ⥤ OperationalTheory.{u}) :
    Term diagram → Term diagram → Prop where
  | stage (site : J) {left right : (diagram.obj site).theory.Term}
      (equivalent : (diagram.obj site).theory.Equiv left right) :
      Equation diagram (inject diagram site left) (inject diagram site right)

abbrev Equivalent (diagram : J ⥤ OperationalTheory.{u}) :=
  Relation.EqvGen (Equation diagram)

/-- One witnessed stage reduction, before ambient equational saturation. -/
inductive StageStep (diagram : J ⥤ OperationalTheory.{u}) :
    Term diagram → Term diagram → Prop where
  | stage (site : J) {left right : (diagram.obj site).theory.Term}
      (step : (diagram.obj site).theory.Step left right) :
      StageStep diagram (inject diagram site left) (inject diagram site right)

def Reduction (diagram : J ⥤ OperationalTheory.{u}) (left right : Term diagram) : Prop :=
  ∃ before after, Equivalent diagram left before ∧ StageStep diagram before after ∧
    Equivalent diagram after right

def theory (diagram : J ⥤ OperationalTheory.{u}) : Mettapedia.GSLT.GSLT.{u} where
  Term := Term diagram
  equations :=
    { r := Equivalent diagram
      iseqv := ⟨fun term => .refl term, fun h => .symm _ _ h,
        fun h₁ h₂ => .trans _ _ _ h₁ h₂⟩ }
  rewrites := Reduction diagram
  rewrites_resp_left := by
    rintro left next right equivalent ⟨before, after, first, step, last⟩
    exact ⟨right, ⟨before, after, .trans _ _ _ (.symm _ _ equivalent) first, step, last⟩,
      .refl right⟩
  rewrites_resp_right := by
    rintro left right next ⟨before, after, first, step, last⟩ equivalent
    exact ⟨before, after, first, step, .trans _ _ _ last equivalent⟩

def inclusion (diagram : J ⥤ OperationalTheory.{u}) (stage : J) :
    OperationalTranslation (diagram.obj stage).theory (theory diagram) where
  mapTerm := inject diagram stage
  mapEquiv := fun equivalent => .rel _ _ (.stage stage equivalent)
  mapStep := fun step => ⟨_, _, .refl _, .stage stage step, .refl _⟩

def cocone (diagram : J ⥤ OperationalTheory.{u}) : Cocone diagram where
  pt := ⟨theory diagram⟩
  ι :=
    { app := inclusion diagram
      naturality := by
        intro first second route
        apply OperationalTranslation.ext
        funext term
        exact (inject_along diagram route term).symm }

def descendTerm {diagram : J ⥤ OperationalTheory.{u}} (target : Cocone diagram) :
    Term diagram → target.pt.theory.Term :=
  Quot.lift (fun term => (target.ι.app term.1).mapTerm term.2) (by
    intro first second transport
    cases transport with
    | @along first second route term =>
        have natural := target.w route
        exact (congrArg
          (fun translation : diagram.obj first ⟶ target.pt => translation.mapTerm term)
          natural).symm)

@[simp] theorem descendTerm_inject {diagram : J ⥤ OperationalTheory.{u}}
    (target : Cocone diagram) (stage : J) (term : (diagram.obj stage).theory.Term) :
    descendTerm target (inject diagram stage term) = (target.ι.app stage).mapTerm term := rfl

theorem descend_equations {diagram : J ⥤ OperationalTheory.{u}} (target : Cocone diagram)
    {left right : Term diagram} (equivalent : Equivalent diagram left right) :
    target.pt.theory.Equiv (descendTerm target left) (descendTerm target right) := by
  induction equivalent with
  | rel left right authored =>
      cases authored with
      | stage stage equivalent => exact (target.ι.app stage).mapEquiv equivalent
  | refl term => exact target.pt.theory.equations.iseqv.refl _
  | symm left right _ ih => exact target.pt.theory.equations.iseqv.symm ih
  | trans first middle last _ _ earlier later =>
      exact target.pt.theory.equations.iseqv.trans earlier later

theorem descend_steps {diagram : J ⥤ OperationalTheory.{u}} (target : Cocone diagram)
    {left right : Term diagram} (step : Reduction diagram left right) :
    target.pt.theory.Step (descendTerm target left) (descendTerm target right) := by
  obtain ⟨before, after, first, authored, last⟩ := step
  have beforeEq := descend_equations target first
  have afterEq := descend_equations target last
  have sourceStep : target.pt.theory.Step (descendTerm target before) (descendTerm target after) := by
    cases authored with
    | stage stage step => exact (target.ι.app stage).mapStep step
  obtain ⟨next, nextStep, nextEq⟩ := target.pt.theory.rewrites_resp_left
    (target.pt.theory.equations.iseqv.symm beforeEq) sourceStep
  exact target.pt.theory.rewrites_resp_right nextStep
    (target.pt.theory.equations.iseqv.trans
      (target.pt.theory.equations.iseqv.symm nextEq) afterEq)

def descend {diagram : J ⥤ OperationalTheory.{u}} (target : Cocone diagram) :
    (cocone diagram).pt ⟶ target.pt where
  mapTerm := descendTerm target
  mapEquiv := descend_equations target
  mapStep := descend_steps target

/-- The constructed object factors every compatible operational cocone,
with a unique carrier map, preserving its authored equations and steps. -/
def isColimit (diagram : J ⥤ OperationalTheory.{u}) : IsColimit (cocone diagram) where
  desc := descend
  fac := by
    intro target stage
    apply OperationalTranslation.ext
    rfl
  uniq := by
    intro target map commutes
    apply OperationalTranslation.ext
    funext term
    refine Quot.inductionOn term ?_
    rintro ⟨stage, value⟩
    exact congrArg
      (fun translation : diagram.obj stage ⟶ target.pt => translation.mapTerm value)
      (commutes stage)

def colimitCocone (diagram : J ⥤ OperationalTheory.{u}) : ColimitCocone diagram :=
  ⟨cocone diagram, isColimit diagram⟩

#print axioms descend_steps
#print axioms isColimit

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
