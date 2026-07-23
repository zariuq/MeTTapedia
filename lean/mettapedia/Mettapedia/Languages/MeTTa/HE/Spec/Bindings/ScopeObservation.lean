import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness

/-!
# Scoped observation of private type bindings

Function applicability may introduce a finite theory over fresh type
variables.  The published evaluator threads the resulting binding record,
whereas an implementation may discharge that private theory into its selected
type policy.  The two states are not globally solution-theory equivalent: the
private theory has additional equations.  They are equivalent only at the
finite evaluator-visible scope.

This module states that observation boundary without mentioning an evaluator
or an executable binding representation.  A normal private presentation can
extend any incoming model while preserving every name outside its keys.  The
resulting scoped equivalence is therefore a theorem of freshness, rather than
an equality or quotient imposed on the two binding carriers.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.ExactNormal
open Spec.Type.Presentation.Freshness
open Spec.Type.RuntimeRefinement

/-! ## Valuation algebra -/

mutual

/-- Applying two type valuations successively is application of their
homomorphic composite. -/
theorem applyTypeValuation_comp
    (outer inner : String → Atom) : ∀ atom,
    applyTypeValuation outer (applyTypeValuation inner atom) =
      applyTypeValuation
        (fun name => applyTypeValuation outer (inner name)) atom := by
  intro atom
  cases atom with
  | symbol name => simp [applyTypeValuation]
  | var name => simp [applyTypeValuation]
  | grounded value => simp [applyTypeValuation]
  | expression atoms =>
      simp only [applyTypeValuation, Atom.expression.injEq]
      exact applyTypeValuationList_comp outer inner atoms

/-- List companion of `applyTypeValuation_comp`. -/
theorem applyTypeValuationList_comp
    (outer inner : String → Atom) : ∀ atoms : List Atom,
    (atoms.map (applyTypeValuation inner)).map
        (applyTypeValuation outer) =
      atoms.map (applyTypeValuation
        (fun name => applyTypeValuation outer (inner name))) := by
  intro atoms
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · exact applyTypeValuation_comp outer inner atom
      · exact applyTypeValuationList_comp outer inner atoms

end

mutual

/-- Homomorphic type substitution depends only on the valuation at variables
occurring in the observed atom. -/
theorem applyTypeValuation_congr_of_typeVars
    {left right : String → Atom} (atom : Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVars atom →
      left name = right name) :
    applyTypeValuation left atom = applyTypeValuation right atom := by
  cases atom with
  | symbol name => simp [applyTypeValuation]
  | var name =>
      simpa [applyTypeValuation] using
        agrees name (by simp [TypeSubst.typeVars])
  | grounded value => simp [applyTypeValuation]
  | expression atoms =>
      simp only [applyTypeValuation, Atom.expression.injEq]
      apply applyTypeValuationList_congr_of_typeVars
      intro name member
      exact agrees name (by simpa [TypeSubst.typeVars] using member)

/-- List companion of `applyTypeValuation_congr_of_typeVars`. -/
theorem applyTypeValuationList_congr_of_typeVars
    {left right : String → Atom} (atoms : List Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVarsList atoms →
      left name = right name) :
    atoms.map (applyTypeValuation left) =
      atoms.map (applyTypeValuation right) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply applyTypeValuation_congr_of_typeVars atom
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply applyTypeValuationList_congr_of_typeVars atoms
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

end

/-- Every post-substitution of a type-presentation model is again a model.
This is the substitution-closure property of syntactic equality. -/
theorem TypeSubstSatisfied.postcompose
    {model : String → Atom} {substitution : TypeSubst}
    (satisfied : TypeSubstSatisfied model substitution)
    (post : String → Atom) :
    TypeSubstSatisfied
      (fun name => applyTypeValuation post (model name)) substitution := by
  intro name value member
  calc
    applyTypeValuation post (model name) =
        applyTypeValuation post
          (applyTypeValuation model value) :=
      congrArg (applyTypeValuation post)
        (satisfied name value member)
    _ = applyTypeValuation
          (fun other => applyTypeValuation post (model other)) value :=
      applyTypeValuation_comp post model value

/-- Extend a public valuation through a private finite presentation.  The
presentation supplies the principal shape; the public valuation supplies the
remaining free variables. -/
def extendThroughPresentation
    (base : String → Atom) (substitution : TypeSubst) : String → Atom :=
  fun name =>
    applyTypeValuation base (presentedValuation substitution name)

/-- A normal presentation's extension satisfies its private equations. -/
theorem extendThroughPresentation_satisfied
    {substitution : TypeSubst} (normal : substitution.Normal)
    (base : String → Atom) :
    TypeSubstSatisfied
      (extendThroughPresentation base substitution) substitution := by
  exact TypeSubstSatisfied.postcompose
    (normal_presentedValuation_satisfied normal) base

/-- Outside the private key set, extension is literally the public
valuation. -/
theorem extendThroughPresentation_eq_of_not_mem_keys
    {base : String → Atom} {substitution : TypeSubst} {name : String}
    (fresh : name ∉ substitution.keys) :
    extendThroughPresentation base substitution name = base name := by
  simp [extendThroughPresentation, presentedValuation, TypeSubst.apply,
    TypeSubst.lookup_eq_none_of_not_mem_keys fresh,
    applyTypeValuation, Option.getD]

/-! ## Scoped binding observation -/

/-- Every variable name mentioned by a spec binding theory, including
assignment keys, variables in assignment values, and equality endpoints. -/
def specBindingVars (bindings : Bindings) : List String :=
  bindings.assignments.flatMap
      (fun entry => entry.1 :: TypeSubst.typeVars entry.2) ++
    bindings.equalities.flatMap (fun entry => [entry.1, entry.2])

/-- Two valuations agree on a finite observable name scope. -/
def ValuationsAgreeOn
    (scope : List String) (left right : String → Atom) : Prop :=
  ∀ name ∈ scope, left name = right name

/-- Two spec binding theories have the same model observations on a finite
scope.  Each model may extend differently outside the scope; that is exactly
what permits private type variables without identifying the global theories. -/
structure BindingTheoryEquivAt
    (scope : List String) (left right : Bindings) : Prop where
  leftToRight : ∀ leftModel,
    TypeBindingSatisfied leftModel left →
      ∃ rightModel,
        TypeBindingSatisfied rightModel right ∧
          ValuationsAgreeOn scope leftModel rightModel
  rightToLeft : ∀ rightModel,
    TypeBindingSatisfied rightModel right →
      ∃ leftModel,
        TypeBindingSatisfied leftModel left ∧
          ValuationsAgreeOn scope leftModel rightModel

namespace BindingTheoryEquivAt

/-- Scoped binding observation is reflexive. -/
@[refl] theorem refl (scope : List String) (bindings : Bindings) :
    BindingTheoryEquivAt scope bindings bindings := by
  constructor <;> intro model satisfied <;>
    exact ⟨model, satisfied, fun _ _ => rfl⟩

/-- Scoped binding observation is symmetric. -/
theorem symm {scope : List String} {left right : Bindings}
    (equiv : BindingTheoryEquivAt scope left right) :
    BindingTheoryEquivAt scope right left := by
  constructor
  · intro rightModel rightSatisfied
    obtain ⟨leftModel, leftSatisfied, agrees⟩ :=
      equiv.rightToLeft rightModel rightSatisfied
    exact ⟨leftModel, leftSatisfied,
      fun name member => (agrees name member).symm⟩
  · intro leftModel leftSatisfied
    obtain ⟨rightModel, rightSatisfied, agrees⟩ :=
      equiv.leftToRight leftModel leftSatisfied
    exact ⟨rightModel, rightSatisfied,
      fun name member => (agrees name member).symm⟩

end BindingTheoryEquivAt

private theorem assignment_key_mem_specBindingVars
    {bindings : Bindings} {name : String} {value : Atom}
    (member : (name, value) ∈ bindings.assignments) :
    name ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨(name, value), member, by simp⟩

private theorem assignment_value_var_mem_specBindingVars
    {bindings : Bindings} {name varName : String} {value : Atom}
    (member : (name, value) ∈ bindings.assignments)
    (variableMember : varName ∈ TypeSubst.typeVars value) :
    varName ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨(name, value), member, by simp [variableMember]⟩

private theorem equality_left_mem_specBindingVars
    {bindings : Bindings} {left right : String}
    (member : (left, right) ∈ bindings.equalities) :
    left ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(left, right), member, by simp⟩

private theorem equality_right_mem_specBindingVars
    {bindings : Bindings} {left right : String}
    (member : (left, right) ∈ bindings.equalities) :
    right ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(left, right), member, by simp⟩

/-- One-way transport of binding satisfaction across agreement on every name
mentioned by the binding record. -/
private theorem specTypeBindingSatisfied_of_agrees
    {left right : String → Atom} {bindings : Bindings}
    (agrees : ValuationsAgreeOn (specBindingVars bindings) left right) :
    TypeBindingSatisfied left bindings →
      TypeBindingSatisfied right bindings := by
  rintro ⟨assignments, equalities⟩
  constructor
  · intro name value member
    calc
      right name = left name :=
        (agrees name
          (assignment_key_mem_specBindingVars member)).symm
      _ = applyTypeValuation left value :=
        assignments name value member
      _ = applyTypeValuation right value := by
        apply applyTypeValuation_congr_of_typeVars
        intro varName variableMember
        exact agrees varName
          (assignment_value_var_mem_specBindingVars
            member variableMember)
  · intro first second member
    calc
      right first = left first :=
        (agrees first
          (equality_left_mem_specBindingVars member)).symm
      _ = left second := equalities first second member
      _ = right second :=
        agrees second (equality_right_mem_specBindingVars member)

/-- Binding satisfaction depends only on the valuation at names mentioned by
the binding record. -/
theorem specTypeBindingSatisfied_congr_of_bindingVars
    {left right : String → Atom} {bindings : Bindings}
    (agrees : ValuationsAgreeOn (specBindingVars bindings) left right) :
    TypeBindingSatisfied left bindings ↔
      TypeBindingSatisfied right bindings := by
  constructor
  · exact specTypeBindingSatisfied_of_agrees agrees
  · exact specTypeBindingSatisfied_of_agrees
      (fun name member => (agrees name member).symm)

/-- The extension through a private presentation preserves any incoming
binding theory whose mentioned names avoid the presentation keys. -/
theorem extendThroughPresentation_preserves_binding
    {base : String → Atom} {substitution : TypeSubst}
    {bindings : Bindings}
    (fresh : ∀ name, name ∈ specBindingVars bindings →
      name ∉ substitution.keys)
    (satisfied : TypeBindingSatisfied base bindings) :
    TypeBindingSatisfied
      (extendThroughPresentation base substitution) bindings := by
  exact (specTypeBindingSatisfied_congr_of_bindingVars
    (left := base)
    (right := extendThroughPresentation base substitution)
    (fun name member =>
      (extendThroughPresentation_eq_of_not_mem_keys
        (fresh name member)).symm)).mp satisfied

/-- Exact solution-theory conjunction of an incoming spec binding record
with one finite type presentation.  This relation deliberately carries no
freshness or observation claim: a presentation may bind a caller-visible
variable, as the published applicability relation permits. -/
def PresentationExtensionRel
    (incoming : Bindings) (substitution : TypeSubst)
    (output : Bindings) : Prop :=
  ∀ valuation,
    TypeBindingSatisfied valuation output ↔
      TypeBindingSatisfied valuation incoming ∧
        TypeSubstSatisfied valuation substitution

/-- The complete semantic boundary for adjoining one private finite type
presentation to an evaluator binding state.  The output carrier is left
abstract: consumers may use any binding representation with the stated
solution theory, but must prove both freshness obligations and normality.

Keeping these four facts in one witness prevents a candidate scan from
mixing the presentation produced by one applicability check with the binding
output of another. -/
structure PrivatePresentationExtensionRel
    (scope : List String) (incoming : Bindings)
    (substitution : TypeSubst) (output : Bindings) : Prop where
  normal : substitution.Normal
  scopeFresh : ∀ name, name ∈ scope →
    name ∉ substitution.keys
  bindingFresh : ∀ name, name ∈ specBindingVars incoming →
    name ∉ substitution.keys
  solutions : ∀ valuation,
    TypeBindingSatisfied valuation output ↔
      TypeBindingSatisfied valuation incoming ∧
        TypeSubstSatisfied valuation substitution

/-- **Private-theory observation theorem.**  If `output` denotes exactly the
incoming binding theory conjoined with a normal private presentation, and the
private keys avoid both the incoming theory and the observation scope, then
`incoming` and `output` have identical observations on that scope. -/
theorem privatePresentation_observationally_inert
    {scope : List String} {incoming output : Bindings}
    {substitution : TypeSubst}
    (normal : substitution.Normal)
    (scopeFresh : ∀ name, name ∈ scope →
      name ∉ substitution.keys)
    (bindingFresh : ∀ name, name ∈ specBindingVars incoming →
      name ∉ substitution.keys)
    (solutions : ∀ valuation,
      TypeBindingSatisfied valuation output ↔
        TypeBindingSatisfied valuation incoming ∧
          TypeSubstSatisfied valuation substitution) :
    BindingTheoryEquivAt scope incoming output := by
  constructor
  · intro incomingModel incomingSatisfied
    let outputModel :=
      extendThroughPresentation incomingModel substitution
    have outputIncoming :
        TypeBindingSatisfied outputModel incoming :=
      extendThroughPresentation_preserves_binding
        bindingFresh incomingSatisfied
    have outputPrivate : TypeSubstSatisfied outputModel substitution :=
      extendThroughPresentation_satisfied normal incomingModel
    refine ⟨outputModel,
      (solutions outputModel).mpr ⟨outputIncoming, outputPrivate⟩, ?_⟩
    intro name member
    exact (extendThroughPresentation_eq_of_not_mem_keys
      (scopeFresh name member)).symm
  · intro outputModel outputSatisfied
    refine ⟨outputModel, (solutions outputModel).mp outputSatisfied |>.1,
      fun _ _ => rfl⟩

/-- A private-presentation extension is observationally inert at precisely
the scope named by its witness. -/
theorem PrivatePresentationExtensionRel.observationallyInert
    {scope : List String} {incoming output : Bindings}
    {substitution : TypeSubst}
    (extension : PrivatePresentationExtensionRel
      scope incoming substitution output) :
    BindingTheoryEquivAt scope incoming output := by
  exact privatePresentation_observationally_inert
    extension.normal extension.scopeFresh extension.bindingFresh
    extension.solutions

/-- Forgetting privacy from a private extension retains its exact
solution-theory conjunction. -/
theorem PrivatePresentationExtensionRel.toPresentationExtension
    {scope : List String} {incoming output : Bindings}
    {substitution : TypeSubst}
    (extension : PrivatePresentationExtensionRel
      scope incoming substitution output) :
    PresentationExtensionRel incoming substitution output :=
  extension.solutions

/-! ## Boundary canaries -/

private def privateT : TypeSubst := [("type#t", .symbol "A")]

private def publicX : Bindings :=
  ⟨[("x", .symbol "B")], []⟩

/-- Conjoining a finite assignment presentation with an existing spec
binding record denotes conjunction of their two equation theories. -/
theorem appendPrivatePresentation_solutions
    (valuation : String → Atom) (bindings : Bindings)
    (substitution : TypeSubst) :
    TypeBindingSatisfied valuation
        ⟨bindings.assignments ++ substitution, bindings.equalities⟩ ↔
      TypeBindingSatisfied valuation bindings ∧
        TypeSubstSatisfied valuation substitution := by
  constructor
  · rintro ⟨assignments, equalities⟩
    constructor
    · exact ⟨fun name value member =>
          assignments name value (List.mem_append_left _ member),
        equalities⟩
    · intro name value member
      exact assignments name value (List.mem_append_right _ member)
  · rintro ⟨⟨assignments, equalities⟩, privateAssignments⟩
    constructor
    · intro name value member
      rcases List.mem_append.mp member with oldMember | privateMember
      · exact assignments name value oldMember
      · exact privateAssignments name value privateMember
    · exact equalities

/-- Appending the presentation assignments to the incoming assignment list
is a concrete carrier for their exact solution-theory conjunction. -/
theorem presentationExtension_append
    (bindings : Bindings) (substitution : TypeSubst) :
    PresentationExtensionRel bindings substitution
      ⟨bindings.assignments ++ substitution, bindings.equalities⟩ :=
  fun valuation =>
    appendPrivatePresentation_solutions valuation bindings substitution

/-- Any normal presentation avoiding the complete public/caller boundary can
be adjoined to the caller binding theory.  This is the general construction
used after branch-valued applicability: it depends only on the selected
presentation's invariants, not on a particular linear scan that produced it. -/
theorem privatePresentationExtension_of_normal_avoids
    {scope : List String} {incoming : Bindings}
    {substitution : TypeSubst}
    (normal : substitution.Normal)
    (avoids : substitution.Avoids
      (scope ++ specBindingVars incoming)) :
    PrivatePresentationExtensionRel scope incoming substitution
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  refine
    { normal := normal
      scopeFresh := ?_
      bindingFresh := ?_
      solutions := fun valuation =>
        appendPrivatePresentation_solutions valuation incoming substitution }
  · intro name scopeMember keyMember
    exact avoids.keys name keyMember
      (List.mem_append_left _ scopeMember)
  · intro name bindingMember keyMember
    exact avoids.keys name keyMember
      (List.mem_append_right _ bindingMember)

/-- An empty-seed presentation fold over alpha-fresh types localizes over an
arbitrary caller binding theory.  The output is the caller theory conjoined
with the private finite presentation; freshness makes that conjunction
satisfiable and observationally inert at the public scope.

This theorem is deliberately freshness-conditioned.  Without that condition
an incoming assignment may instantiate a type variable differently from the
empty-seed fold, so the corresponding seeded match need not succeed. -/
theorem PresentationArgumentListMatchRel.privateExtension
    {scope : List String} {incoming : Bindings}
    {expected actual : List Atom} {substitution : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual [] substitution)
    (expectedFresh : AtomsAvoid expected
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid actual
      (scope ++ specBindingVars incoming)) :
    PrivatePresentationExtensionRel scope incoming substitution
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  have outputNormal : substitution.Normal :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      derivation TypeSubst.normal_empty
  have outputAvoids : substitution.Avoids
      (scope ++ specBindingVars incoming) :=
    presentationArgumentList_output_avoids derivation
      (TypeSubst.avoids_empty _) expectedFresh actualFresh
  constructor
  · exact outputNormal
  · intro name scopeMember keyMember
    exact outputAvoids.keys name keyMember
      (List.mem_append_left _ scopeMember)
  · intro name bindingMember keyMember
    exact outputAvoids.keys name keyMember
      (List.mem_append_right _ bindingMember)
  · intro valuation
    exact appendPrivatePresentation_solutions
      valuation incoming substitution

/-- The localization theorem immediately yields the evaluator-visible
observation boundary consumed by runtime correspondence. -/
theorem PresentationArgumentListMatchRel.scopedInert
    {scope : List String} {incoming : Bindings}
    {expected actual : List Atom} {substitution : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual [] substitution)
    (expectedFresh : AtomsAvoid expected
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid actual
      (scope ++ specBindingVars incoming)) :
    BindingTheoryEquivAt scope incoming
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  exact
    (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.PresentationArgumentListMatchRel.privateExtension
      derivation expectedFresh actualFresh).observationallyInert

/-- Positive: a private type equation can be conjoined without changing the
public `x` observation. -/
theorem private_type_binding_is_inert_at_public_x :
    BindingTheoryEquivAt ["x"] publicX
      ⟨publicX.assignments ++ privateT, []⟩ := by
  apply privatePresentation_observationally_inert
      (substitution := privateT)
  · simp [privateT, TypeSubst.Normal, TypeSubst.keys,
      TypeSubst.typeVars]
  · simp [privateT, TypeSubst.keys]
  · intro name member
    simp [specBindingVars, publicX, TypeSubst.typeVars] at member
    subst name
    simp [privateT, TypeSubst.keys]
  · intro valuation
    exact appendPrivatePresentation_solutions valuation publicX privateT

/-- Negative: freshness is essential.  Constraining the observed `x` to `A`
is not observationally inert at `x`. -/
theorem observed_private_key_is_not_inert :
    ¬BindingTheoryEquivAt ["x"] Bindings.empty
      ⟨[("x", .symbol "A")], []⟩ := by
  intro equiv
  let publicModel : String → Atom :=
    fun name => if name = "x" then .symbol "B" else .var name
  have emptySatisfied :
      TypeBindingSatisfied publicModel Bindings.empty := by
    simp [TypeBindingSatisfied, Bindings.empty]
  obtain ⟨privateModel, privateSatisfied, agrees⟩ :=
    equiv.leftToRight publicModel emptySatisfied
  have forced := privateSatisfied.1 "x" (.symbol "A") (by simp)
  have publicXValue : publicModel "x" = .symbol "B" := by
    simp [publicModel]
  have sameX := agrees "x" (by simp)
  simp [applyTypeValuation] at forced
  rw [← sameX, publicXValue] at forced
  contradiction

end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
