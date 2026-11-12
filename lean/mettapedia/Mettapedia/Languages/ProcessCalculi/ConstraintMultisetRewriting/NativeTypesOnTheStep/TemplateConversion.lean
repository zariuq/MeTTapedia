import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionSettling

/-!
# Conversion at the variables: the template rule

The conversion rule (`ConversionSettling`) types the made code in its frame and converts only its type.
It refuses a code that is typed only once the match refines the types of its variables, such as `f a`
with `f : X` and the information `X ≐ Π (y : U₀). U₀` (`TemplateControls`). Conversion can move inside,
to the variables:

* **A template of a made row** (`Template`): a code typed in a template frame at a formed type, with
  each template variable filled by a variable of the row's frame; the row's code is the template's code
  renamed along the filling.
* **The template rule at σ** (`Template.Holds`): each filling variable's declared type, substituted
  along σ, is usable at its template variable's type, and the template's type at the row's type. Then
  the template filled along σ is a typed substitution (`Template.substMor`) and the row is typed along
  σ (`Template.typed_of_holds`).
* **It is stable under substitution** (`Template.holds_comp`) **and closed under agreement**
  (`Template.holds_of_agree`): agreeing substitutions are equal at the filling variables at their
  declared types, hence, by the template rule, at the template variables' types, so functionality
  equates the template's types along both.
* **Full soundness** (`typedAfterMatch_of_template`): a row whose template rule holds along a principal
  answer is typed at every solution of the information.
* **It extends the conversion rule** (`template_of_convertsAlong`): conversion at the type is the
  template rule of the identity template.

**The templating step** (`templatingStep`): the settling step's plan, each made row typed by a template
along it. It admits everything the converting step admits (`converting_le_templating`), so it is
conservative over the present step (`templating_admits_of_admits`), and it is **fully sound for every
settler** (`templating_typedAfterMatch`). With the semantic settler it admits every firing whose rows
are typed by templates at every solution of an information with an initial solution
(`ideal_templating_admits`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make)
open UnificationWithLevels (Agree InitialSolution)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-! ## Templates -/

section Templates

/-- **A template of a made row**: a code typed in a template frame at a formed type, each template
variable filled by a variable of the row's frame, the row's code being the filled template. -/
structure Template {Δ : Context rules} (m : Make Δ) where
  frame : Context rules
  code : Tm Head frame.arity
  type : TypeOver frame
  fill : Fin frame.arity → Fin Δ.arity
  typed : Typed rules frame.raw code type.code
  filled : m.code = Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename fill code

omit [UniverseLevel.LevelOrder L] in
/-- The template's variables, read along a substitution of the row's frame. -/
def Template.along {M Δ : Context rules} {m : Make Δ} (t : Template m) (σ : M ⟶ Δ) :
    Sub Head t.frame.arity M.arity :=
  fun j => σ.substitution (t.fill j)

omit [UniverseLevel.LevelOrder L] in
/-- **The template rule at σ**: every filling variable's declared type, along σ, is usable at its
template variable's type, and the template's type at the row's type. -/
def Template.Holds {M Δ : Context rules} {m : Make Δ} (t : Template m) (σ : M ⟶ Δ) : Prop :=
  (∀ j : Fin t.frame.arity, Below rules M.raw (subst σ.substitution (Ctx.lookup Δ.raw (t.fill j)))
      (subst (t.along σ) (Ctx.lookup t.frame.raw j))) ∧
    Below rules M.raw (subst (t.along σ) t.type.code) (m.type.reindex σ).code

omit [UniverseLevel.LevelOrder L] in
/-- Where the template rule holds, the template filled along σ is a typed substitution. -/
theorem Template.substMor {M Δ : Context rules} {m : Make Δ} (t : Template m) {σ : M ⟶ Δ}
    (holds : t.Holds σ) : SubstMor rules t.frame.raw M.raw (t.along σ) :=
  fun j => Derivable.sub (σ.typed (t.fill j)) (holds.1 j)

omit [UniverseLevel.LevelOrder L] in
/-- **Where the template rule holds, the row is typed along σ.** -/
theorem Template.typed_of_holds {M Δ : Context rules} {m : Make Δ} (t : Template m) {σ : M ⟶ Δ}
    (holds : t.Holds σ) : (m.reindex σ).WellTyped := by
  show Typed rules M.raw (subst σ.substitution m.code) (m.type.reindex σ).code
  rw [t.filled, subst_rename]
  exact Derivable.sub (t.typed.substitute (t.substMor holds)) holds.2

omit [UniverseLevel.LevelOrder L] in
/-- **The template rule is stable under substitution.** -/
theorem Template.holds_comp {M Δ Θ : Context rules} {m : Make Δ} (t : Template m) {σ : M ⟶ Δ}
    (holds : t.Holds σ) (g : Θ ⟶ M) : t.Holds (g ≫ σ) := by
  refine ⟨fun j => ?_, ?_⟩
  · have moved : Below rules Θ.raw
        (subst g.substitution (subst σ.substitution (Ctx.lookup Δ.raw (t.fill j))))
        (subst g.substitution (subst (t.along σ) (Ctx.lookup t.frame.raw j))) :=
      below_substitute (holds.1 j) g.typed
    rw [subst_subComp, subst_subComp] at moved
    exact moved
  · have moved : Below rules Θ.raw (subst g.substitution (subst (t.along σ) t.type.code))
        (subst g.substitution (subst σ.substitution m.type.code)) :=
      below_substitute holds.2 g.typed
    rw [subst_subComp, subst_subComp] at moved
    exact moved

/-- **The template rule is closed under agreement.** -/
theorem Template.holds_of_agree {Θ Δ : Context rules} {m : Make Δ} (t : Template m)
    {τ τ' : Θ ⟶ Δ} (agree : Agree (frames levels) τ τ') (holds' : t.Holds τ') : t.Holds τ := by
  -- The filling variables' declared types agree along τ and τ'.
  have declared : ∀ j : Fin t.frame.arity,
      TypeEq rules Θ.raw (subst τ.substitution (Ctx.lookup Δ.raw (t.fill j)))
        (subst τ'.substitution (Ctx.lookup Δ.raw (t.fill j))) := by
    intro j
    obtain ⟨u, hu, typed⟩ := Δ.formed.lookup (t.fill j)
    exact typeEq_of_agree levels agree ⟨Ctx.lookup Δ.raw (t.fill j), u, hu, typed⟩
  -- The template filled along τ' and along τ are equal substitutions.
  have equal : SubstEq rules t.frame.raw Θ.raw (t.along τ') (t.along τ) := by
    refine ⟨t.substMor holds', fun i => ?_⟩
    obtain ⟨u, hu, typed⟩ := Δ.formed.lookup (t.fill i)
    let filling : TotalTerm Δ := ⟨⟨Ctx.lookup Δ.raw (t.fill i), u, hu, typed⟩, ⟨.var (t.fill i), Derivable.var _⟩⟩
    have atDeclared : Equal rules Θ.raw (τ'.substitution (t.fill i)) (τ.substitution (t.fill i))
        (subst τ.substitution (Ctx.lookup Δ.raw (t.fill i))) := .symm (agree filling).2
    obtain ⟨w, hw, e⟩ := declared i
    exact Derivable.subEq (Derivable.convEq atDeclared e hw) (holds'.1 i)
  refine ⟨fun j => ?_, ?_⟩
  · obtain ⟨u, hu, typed⟩ := t.frame.formed.lookup j
    have templateType : TypeEq rules Θ.raw (subst (t.along τ') (Ctx.lookup t.frame.raw j))
        (subst (t.along τ) (Ctx.lookup t.frame.raw j)) := ⟨u, hu, typed.functional equal⟩
    exact .subTrans (below_of_typeEq (declared j))
      (.subTrans (holds'.1 j) (below_of_typeEq templateType))
  · have templateType : TypeEq rules Θ.raw (subst (t.along τ') t.type.code) (subst (t.along τ) t.type.code) :=
      ⟨t.type.level, t.type.universeWitness, t.type.formed.functional equal⟩
    exact .subTrans (below_of_typeEq templateType.symm)
      (.subTrans holds'.2 (below_of_typeEq (typeEq_of_agree levels agree m.type).symm))

/-- **Full soundness of the template rule**: a row whose template rule holds along a principal answer
is typed at every solution of the information. -/
theorem typedAfterMatch_of_template {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {σ : M ⟶ Δ} (principal : (frames levels).Principal I σ) {m : Make Δ} (t : Template m)
    (holds : t.Holds σ) : TypedAfterMatch levels I m := by
  refine (typedAfterMatch_iff levels I m).mpr fun Θ τ solved => ?_
  obtain ⟨g, agree⟩ := principal.factors Θ τ solved
  exact t.typed_of_holds (t.holds_of_agree levels agree (t.holds_comp holds g))

/-- **Settling decides the template rule exactly**: along a principal answer it holds exactly when it
holds at every solution. -/
theorem template_iff_of_principal {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {σ : M ⟶ Δ} (principal : (frames levels).Principal I σ) {m : Make Δ} (t : Template m) :
    t.Holds σ ↔ ∀ (Θ : Context rules) (τ : Θ ⟶ Δ), (frames levels).Models τ I → t.Holds τ := by
  constructor
  · intro holds Θ τ solved
    obtain ⟨g, agree⟩ := principal.factors Θ τ solved
    exact t.holds_of_agree levels agree (t.holds_comp holds g)
  · exact fun everywhere => everywhere M σ principal.sound

omit [UniverseLevel.LevelOrder L] in
/-- **The identity template**: a code typed in its own frame at `B`. -/
def Template.identity {Δ : Context rules} (m : Make Δ) (B : TypeOver Δ) (typed : FrameTypedAt m B) :
    Template m :=
  ⟨Δ, m.code, B, idRen, typed, (rename_id m.code).symm⟩

omit [UniverseLevel.LevelOrder L] in
/-- **The template rule extends the conversion rule**: converting along σ is the template rule of the
identity template. -/
theorem template_of_convertsAlong {M Δ : Context rules} {m : Make Δ} {σ : M ⟶ Δ}
    (converts : ConvertsAlong m σ) : ∃ t : Template m, t.Holds σ := by
  obtain ⟨B, typed, inside⟩ := converts
  refine ⟨Template.identity m B typed, fun j => ?_, inside⟩
  obtain ⟨u, hu, typedLookup⟩ := Δ.formed.lookup j
  exact below_refl_of_isType ⟨u, hu, typedLookup.substitute σ.typed⟩

end Templates

/-! ## The templating step -/

section Step

open Interface.DependentFull (State Firing relabel)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {O : Type} [DecidableEq O]

omit [UniverseLevel.LevelOrder L] in
/-- A made row is **typed by a template along σ** when the rule of one of its templates holds. -/
def TemplatedAlong {M Δ : Context rules} (m : Make Δ) (σ : M ⟶ Δ) : Prop :=
  ∃ t : Template m, t.Holds σ

/-- **Templating shapes**: the step's shapes, with every made row typed by a template along the plan. -/
def TemplatingShapes (settler : Settler levels) {s : State rules O} (f : Firing levels s) : Prop :=
  f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
    ∀ m ∈ f.makes, TemplatedAlong m.2 (plan levels settler f).2

omit [DecidableEq O] in
theorem TemplatingShapes.typed {settler : Settler levels} {s : State rules O} {f : Firing levels s}
    (shapes : TemplatingShapes levels settler f) :
    ∀ m ∈ f.makes, (m.2.reindex (plan levels settler f).2).WellTyped := by
  intro m member
  obtain ⟨t, holds⟩ := shapes.2.2.2.2 m member
  exact t.typed_of_holds holds

variable (O) in
/-- **The templating settling step**: the settling step's states, firings and plan, with each made row
typed by a template along the plan. -/
noncomputable def templatingStep (settler : Settler levels) :
    Interface.Step.Standard (frames levels) O (State rules O) (Firing levels) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := f.helpers.frame
  extension f := f.helpers.weaken
  information f := f.information
  transported := (DependentFull.step levels O).transported
  Shapes f := TemplatingShapes levels settler f
  Holds f _ τ := f.Holds τ
  Admits {s} f := TemplatingShapes levels settler f ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable f.information ∧ (frames levels).Entails f.information (fun _ τ => f.Holds τ)
  admits_iff _ := Iff.rfl
  preparedResult f p := settledState levels f (plan levels settler f) (TemplatingShapes.typed levels p.1)
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (plan levels settler f).2
  knowledge_preparedResult _ _ := rfl

variable (settler : Settler levels)

/-- **The templating step admits what the converting step admits**, with the same settler. -/
theorem converting_le_templating {s : State rules O} {f : Firing levels s}
    (admitted : (convertingStep levels O settler).Admits f) : (templatingStep levels O settler).Admits f := by
  obtain ⟨⟨a, b, c, d, rows⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, fun m member => template_of_convertsAlong (rows m member)⟩, enabled, solvable, holds⟩

/-- **Conservativity**: every firing the present step admits, the templating step admits. -/
theorem templating_admits_of_admits {s : State rules O} {f : Firing levels s}
    (admitted : (DependentFull.step levels O).Admits f) : (templatingStep levels O settler).Admits f :=
  converting_le_templating levels settler (converting_admits_of_admits levels settler admitted)

/-- **Full soundness of the templating step, for every settler**: every made row of an admitted firing
is typed at every solution of its information. -/
theorem templating_typedAfterMatch {s : State rules O} {f : Firing levels s}
    (admitted : (templatingStep levels O settler).Admits f) :
    ∀ m ∈ f.makes, TypedAfterMatch levels f.information m.2 := by
  intro m member
  obtain ⟨t, holds⟩ := admitted.1.2.2.2.2 m member
  by_cases typed : FrameTyped levels f
  · exact typedAfterMatch_of_wellTyped levels _ (typed m member)
  · rw [plan_of_not_frameTyped levels settler typed] at holds
    cases verdict : settler f.information with
    | settled M σ initial =>
        rw [verdict] at holds
        exact typedAfterMatch_of_template levels (principal_of_initial levels initial) t holds
    | postponed =>
        rw [verdict] at holds
        have plain := t.typed_of_holds holds
        have frameTyped : m.2.WellTyped := by
          simpa only [Verdict.along, Make.reindex_id'] using plain
        exact typedAfterMatch_of_wellTyped levels _ frameTyped

/-- **The semantic settler realizes the template rule** wherever the information has an initial
solution: a firing whose rows are typed by templates at every solution is admitted. -/
theorem ideal_templating_admits {s : State rules O} {f : Firing levels s}
    (shapes : f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧
      f.reads.length = f.read.length)
    (rows : ∀ m ∈ f.makes, ∃ t : Template m.2, ∀ (Θ : Context rules) (τ : Θ ⟶ f.helpers.frame),
      (frames levels).Models τ f.information → t.Holds τ)
    (enabled : Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)))
    (holds : (frames levels).Entails f.information (fun _ τ => f.Holds τ))
    {M : Context rules} {σ : M ⟶ f.helpers.frame}
    (initial : InitialSolution (frames levels) f.information σ) :
    (templatingStep levels O (Settler.ideal levels)).Admits f := by
  obtain ⟨a, b, c, d⟩ := shapes
  refine ⟨⟨a, b, c, d, fun m member => ?_⟩, enabled, (principal_of_initial levels initial).solvable, holds⟩
  obtain ⟨t, everywhere⟩ := rows m member
  by_cases frameTyped : FrameTyped levels f
  · rw [plan_of_frameTyped levels _ frameTyped]
    exact template_of_convertsAlong (convertsAlong_of_wellTyped (frameTyped m member) _)
  · rw [plan_of_not_frameTyped levels _ frameTyped]
    obtain ⟨M', σ', initial', settles⟩ := Settler.ideal_settles levels initial
    rw [settles]
    exact ⟨t, everywhere M' σ' initial'.solves⟩

end Step

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.Template.substMor
#print axioms NativeTypesOnTheStep.Template.typed_of_holds
#print axioms NativeTypesOnTheStep.Template.holds_comp
#print axioms NativeTypesOnTheStep.Template.holds_of_agree
#print axioms NativeTypesOnTheStep.typedAfterMatch_of_template
#print axioms NativeTypesOnTheStep.template_iff_of_principal
#print axioms NativeTypesOnTheStep.template_of_convertsAlong
#print axioms NativeTypesOnTheStep.templatingStep
#print axioms NativeTypesOnTheStep.converting_le_templating
#print axioms NativeTypesOnTheStep.templating_admits_of_admits
#print axioms NativeTypesOnTheStep.templating_typedAfterMatch
#print axioms NativeTypesOnTheStep.ideal_templating_admits

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
