import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClassifierContext
import Mettapedia.OSLF.Syntax.IndexedRuleFiniteContextSemantics
import Mettapedia.OSLF.Syntax.IndexedRuleFreeSubstitutionNaturality
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels

/-!
# Set-valued interpretation of combined contextual syntax

A valuation into an independently supplied operational model interprets
both program metavariables and each retained contextual firing-event
variable. Free authored firing trees then evaluate by the model's own rule
action. This is the concrete interpretation required before classifying
functors into more general semantic targets.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierSetSemantics

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextChange
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierContext
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
open Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial
  (Judgment mapJudgment mapJudgment_comp)

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M)) (equations : List (EqAxiom S M))

/-- A target valuation separately supplies a binding-equation
interpretation and one semantic firing witness at every listed contextual
event variable. Distinct positions are retained even with equal endpoints. -/
structure Valuation
    (target : SubstitutionOperationalModel R equations)
    (X : EquationContexts (authoredEquationPresentation S equations))
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)) where
  program : FreeBindingClone.Hom
    (authoredEquationModelAt S equations X.as).algebra
    target.base.algebra
  event : ∀ position : Fin Γ.length,
    target.model.evidence.carrier ()
      (mapJudgment program (Γ.label position))

/-- A semantic valuation is determined by its program interpretation and
its value at each retained event-variable position. -/
@[ext (iff := false)] theorem Valuation.ext
    {target : SubstitutionOperationalModel R equations}
    {X : EquationContexts (authoredEquationPresentation S equations)}
    {Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    {first second : Valuation R equations target X Γ}
    (programEq : first.program = second.program)
    (eventEq : ∀ position, programEq ▸ first.event position =
      second.event position) : first = second := by
  cases first with
  | mk firstProgram firstEvents =>
      cases second with
      | mk secondProgram secondEvents =>
          cases programEq
          congr
          funext position
          exact eventEq position

/-- At a fixed program interpretation, an ordered contextual event-variable
list is interpreted as exactly the family of witnesses at its positions.
No quotient by endpoint equality or judgment equality occurs. -/
noncomputable def eventContextFiberEquiv
    (target : SubstitutionOperationalModel R equations)
    (X : EquationContexts (authoredEquationPresentation S equations))
    (Γ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra))
    (program : FreeBindingClone.Hom
      (authoredEquationModelAt S equations X.as).algebra
      target.base.algebra) :
    {value : Valuation R equations target X Γ //
      value.program = program} ≃
      (∀ position : Fin Γ.length,
        target.model.evidence.carrier ()
          (mapJudgment program (Γ.label position))) where
  toFun value position := value.property ▸ value.val.event position
  invFun events := ⟨⟨program, events⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨assignedProgram, assignedEvents⟩, sameProgram⟩
    cases sameProgram
    apply Subtype.ext
    rfl
  right_inv events := rfl

/-- At a fixed program interpretation, the generic one-event context has
exactly one semantic value for each witness of its contextual judgment.
The fiber condition matters because the context also varies over program
interpretations when that interpretation is not held fixed. -/
noncomputable def singletonEventEquiv
    (target : SubstitutionOperationalModel R equations)
    (X : EquationContexts (authoredEquationPresentation S equations))
    (program : FreeBindingClone.Hom
      (authoredEquationModelAt S equations X.as).algebra
      target.base.algebra)
    (judgment : Judgment (authoredEquationModelAt S equations X.as).algebra) :
    {value : Valuation R equations target X
        (singletonList R
          (authoredEquationModelAt S equations X.as).algebra judgment) //
        value.program = program} ≃
      target.model.evidence.carrier () (mapJudgment program judgment) where
  toFun value := value.property ▸ value.val.event
    ⟨0, by simp [singletonList]⟩
  invFun witness :=
    ⟨⟨program, fun _ => witness⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨assignedProgram, assignedEvents⟩, sameProgram⟩
    cases sameProgram
    apply Subtype.ext
    dsimp
    congr 1
    funext position
    have onlyPosition : position = ⟨0, by simp [singletonList]⟩ := by
      apply Fin.ext
      have bounded : position.val < 1 := by
        simpa [singletonList] using position.isLt
      change position.val = 0
      omega
    cases onlyPosition
    rfl
  right_inv witness := rfl

variable {target : SubstitutionOperationalModel R equations}
variable {X : EquationContexts (authoredEquationPresentation S equations)}
variable {Γ : ListContext
  (rules R (authoredEquationModelAt S equations X.as).algebra)}

/-- Reindex an event-variable valuation to the target binding clone.
The list position, rather than a possibly noninjective judgment, determines
which retained event is used. -/
def Valuation.eventAssignment (value : Valuation R equations target X Γ) :
    IndexedRuleFiniteContexts.Valuation
      (rules R target.base.algebra)
      (carrier := fun j => target.model.evidence.carrier () j)
      (toContext (rules R target.base.algebra)
        (pushContext R value.program Γ)) :=
  fun _ ⟨position, ⟨equal⟩⟩ => equal ▸ value.event position

/-- Interpret a complete free firing tree by mapping its binding model and
then folding its rule nodes with the target model's actual rule action. -/
noncomputable def Valuation.interpretTree
    (value : Valuation R equations target X Γ)
    (judgment : Judgment (authoredEquationModelAt S equations X.as).algebra)
    (tree : IndexedRuleFiniteContexts.Term
      (rules R (authoredEquationModelAt S equations X.as).algebra)
      (toContext (rules R (authoredEquationModelAt S equations X.as).algebra)
        Γ) judgment) :
    target.model.evidence.carrier () (mapJudgment value.program judgment) :=
  IndexedRuleFiniteContexts.interpretTerm
    (rules R target.base.algebra) target.model.evidence.rules
    value.eventAssignment
    (IntrinsicScopedConditionalFiniteContextChange.mapTerm
      R value.program Γ judgment tree)

/-- A retained event variable evaluates to exactly the witness assigned
at its original list position. -/
theorem Valuation.interpretTree_pure
    (value : Valuation R equations target X Γ)
    (position : Fin Γ.length) :
    value.interpretTree R equations (Γ.label position)
        (IndexedPolynomial.Free.pure
          (rules R (authoredEquationModelAt S equations X.as).algebra)
          ⟨position, ⟨rfl⟩⟩) =
      value.event position := by
  have mapped := IntrinsicScopedConditionalFiniteContextChange.mapTerm_pure
    R value.program Γ
    (slot := (⟨position, ⟨rfl⟩⟩ :
      (toContext
        (rules R (authoredEquationModelAt S equations X.as).algebra)
        Γ).slots (Γ.label position)))
  unfold Valuation.interpretTree
  exact (congrArg
    (IndexedRuleFiniteContexts.interpretTerm
      (rules R target.base.algebra) target.model.evidence.rules
      value.eventAssignment) mapped).trans rfl

/-- Interpreting a constructor tree applies the target model's authored
rule action to its recursively interpreted, binder-local premise events. -/
theorem Valuation.interpretTree_node
    (value : Valuation R equations target X Γ)
    {judgment : Judgment (authoredEquationModelAt S equations X.as).algebra}
    (shape : (rules R (authoredEquationModelAt S equations X.as).algebra).Shape
      PUnit.unit judgment)
    (children : ∀ position,
      IndexedRuleFiniteContexts.Term
        (rules R (authoredEquationModelAt S equations X.as).algebra)
        (toContext
          (rules R (authoredEquationModelAt S equations X.as).algebra) Γ)
        ((rules R (authoredEquationModelAt S equations X.as).algebra).next
          shape position)) :
    value.interpretTree R equations judgment
        (IndexedPolynomial.Free.node
          (rules R (authoredEquationModelAt S equations X.as).algebra)
          shape children) =
      target.model.evidence.rules.act ()
        (mapJudgment value.program judgment)
        ⟨mapShape R value.program shape,
          fun position =>
            IndexedRuleFiniteContexts.interpretTerm
              (rules R target.base.algebra)
              target.model.evidence.rules value.eventAssignment
              (((presentationMap R value.program).rules.onNext
                PUnit.unit judgment shape position).symm ▸
                IntrinsicScopedConditionalFiniteContextChange.mapTerm
                  R value.program Γ _
                  (children (((presentationMap R value.program).rules.onPosition
                    PUnit.unit judgment shape) position)))⟩ := by
  have mapped := IntrinsicScopedConditionalFiniteContextChange.mapTerm_node
    R value.program Γ shape children
  unfold Valuation.interpretTree
  exact (congrArg
    (IndexedRuleFiniteContexts.interpretTerm
      (rules R target.base.algebra) target.model.evidence.rules
      value.eventAssignment) mapped).trans rfl

/-- Reassign event variables by evaluating their full authored firing trees
without changing the interpretation of program metavariables. -/
noncomputable def Valuation.reassign
    (value : Valuation R equations target X Γ)
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (events : Γ ⟶ Δ) : Valuation R equations target X Δ where
  program := value.program
  event position := value.interpretTree R equations (Δ.label position)
    (events (Δ.label position) ⟨position, ⟨rfl⟩⟩)

/-- Identity event substitution leaves all retained occurrences intact. -/
theorem Valuation.reassign_id
    (value : Valuation R equations target X Γ) :
    value.reassign R equations (𝟙 Γ) = value := by
  apply Valuation.ext R equations rfl
  intro position
  exact value.interpretTree_pure R equations position

/-- Reindexing an event context only by a propositional equality changes
the type of the valuation, but no program assignment or firing witness. -/
theorem Valuation.reassign_eqToHom
    (value : Valuation R equations target X Γ)
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (equal : Γ = Δ) :
    value.reassign R equations (eqToHom equal) = equal ▸ value := by
  cases equal
  exact value.reassign_id R equations

/-- Evaluating after a simultaneous substitution of contextual event
variables agrees with first evaluating their assigned firing trees and then
evaluating the outer tree. This includes recursively nested rule premises. -/
theorem Valuation.interpretTree_bind
    (value : Valuation R equations target X Γ)
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (events : Γ ⟶ Δ)
    (judgment : Judgment (authoredEquationModelAt S equations X.as).algebra)
    (tree : IndexedRuleFiniteContexts.Term
      (rules R (authoredEquationModelAt S equations X.as).algebra)
      (toContext
        (rules R (authoredEquationModelAt S equations X.as).algebra) Δ)
      judgment) :
    value.interpretTree R equations judgment
        (IndexedPolynomial.Free.bind
          (rules R (authoredEquationModelAt S equations X.as).algebra)
          (fun _ index seed => events index seed)
          PUnit.unit judgment tree) =
      (value.reassign R equations events).interpretTree
        R equations judgment tree := by
  let P := rules R (authoredEquationModelAt S equations X.as).algebra
  let Q := rules R target.base.algebra
  let targetFill := fun (_ : Unit) index
      (seed : (toContext Q (pushContext R value.program Δ)).slots index) =>
    pushSubstitution R value.program events index seed
  have leaves :
      (fun index
        (seed : (toContext Q (pushContext R value.program Δ)).slots index) =>
          IndexedRuleFiniteContexts.interpretTerm Q
            target.model.evidence.rules value.eventAssignment
            (targetFill () index seed)) =
      (value.reassign R equations events).eventAssignment := by
    funext index seed
    rcases seed with ⟨position, ⟨equal⟩⟩
    cases equal
    rfl
  change value.interpretTree R equations judgment
      (IndexedPolynomial.Free.bind P
        (fun _ index seed => events index seed)
        PUnit.unit judgment tree) =
    IndexedRuleFiniteContexts.interpretTerm Q
      target.model.evidence.rules
      (value.reassign R equations events).eventAssignment
      (IntrinsicScopedConditionalFiniteContextChange.mapTerm
        R value.program Δ judgment tree)
  calc
    value.interpretTree R equations judgment
        (IndexedPolynomial.Free.bind P
          (fun _ index seed => events index seed)
          PUnit.unit judgment tree) =
      IndexedRuleFiniteContexts.interpretTerm Q
        target.model.evidence.rules value.eventAssignment
        (IndexedPolynomial.Free.bind Q targetFill PUnit.unit
          (mapJudgment value.program judgment)
          (IntrinsicScopedConditionalFiniteContextChange.mapTerm
            R value.program Δ judgment tree)) := by
            exact congrArg
              (IndexedRuleFiniteContexts.interpretTerm Q
                target.model.evidence.rules value.eventAssignment)
              (IntrinsicScopedConditionalFiniteContextChange.mapTerm_bind
                R value.program events judgment tree)
    _ = IndexedRuleFiniteContexts.interpretTerm Q
          target.model.evidence.rules
          (value.reassign R equations events).eventAssignment
          (IntrinsicScopedConditionalFiniteContextChange.mapTerm
            R value.program Δ judgment tree) := by
            unfold IndexedRuleFiniteContexts.interpretTerm
            rw [IndexedPolynomial.Free.fold_bind]
            exact congrArg
              (fun assignment => IndexedPolynomial.Free.fold Q
                (fun (_ : Unit) index seed => assignment index seed)
                target.model.evidence.rules PUnit.unit
                (mapJudgment value.program judgment)
                (IntrinsicScopedConditionalFiniteContextChange.mapTerm
                  R value.program Δ judgment tree)) leaves

/-- Simultaneous substitutions of retained events compose under every
independently supplied operational interpretation. -/
theorem Valuation.reassign_comp
    (value : Valuation R equations target X Γ)
    {Δ Θ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (earlier : Γ ⟶ Δ) (later : Δ ⟶ Θ) :
    (value.reassign R equations earlier).reassign R equations later =
      value.reassign R equations (earlier ≫ later) := by
  apply Valuation.ext R equations
    (first := (value.reassign R equations earlier).reassign R equations later)
    (second := value.reassign R equations (earlier ≫ later)) rfl
  intro position
  exact (value.interpretTree_bind R equations earlier
    (Θ.label position)
    (later (Θ.label position) ⟨position, ⟨rfl⟩⟩)).symm

/-- At a fixed program context, every event-context substitution acts on
semantic valuations by evaluation of its complete firing trees. -/
noncomputable def fiberSemantics
    (target : SubstitutionOperationalModel R equations)
    (X : EquationContexts (authoredEquationPresentation S equations)) :
    ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra) ⥤ Type where
  obj Γ := Valuation R equations target X Γ
  map events := TypeCat.ofHom (fun value => value.reassign R equations events)
  map_id Γ := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact value.reassign_id R equations
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact (value.reassign_comp R equations earlier later).symm

/-- Restrict a semantic valuation along an authored program assignment.
The event positions are retained; only their contextual judgments and the
program interpretation change. -/
noncomputable def Valuation.restrict
    {Y : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    (base : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y.as).algebra
      (authoredEquationModelAt S equations X.as).algebra)
    (value : Valuation R equations target X (pushContext R base Δ)) :
    Valuation R equations target Y Δ where
  program := FreeBindingClone.Hom.comp base value.program
  event position := by
    have indexEq :
        mapJudgment (FreeBindingClone.Hom.comp base value.program)
            (Δ.label position) =
          mapJudgment value.program (mapJudgment base (Δ.label position)) :=
      Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.mapJudgment_comp
        base value.program (Δ.label position)
    exact indexEq.symm ▸ value.event position

/-- Restricting along the identity binding model map does not change a
semantic valuation, after the canonical identity reindexing of contexts. -/
theorem Valuation.restrict_id
    (value : Valuation R equations target X
      (pushContext R
        (FreeBindingClone.Hom.id
          (authoredEquationModelAt S equations X.as).algebra) Γ)) :
    value.restrict R equations
        (FreeBindingClone.Hom.id
          (authoredEquationModelAt S equations X.as).algebra) =
      (pushContext_id R
        (authoredEquationModelAt S equations X.as).algebra Γ ▸ value) := by
  rfl

/-- Evaluation of a contextual firing tree commutes with a change of its
binding-equation model. The target algebra sees the same retained event
positions and the same ordered authored rule constructors on either route. -/
theorem Valuation.interpretTree_restrict
    {Y : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    (base : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y.as).algebra
      (authoredEquationModelAt S equations X.as).algebra)
    (value : Valuation R equations target X (pushContext R base Δ))
    (judgment : Judgment (authoredEquationModelAt S equations Y.as).algebra)
    (tree : IndexedRuleFiniteContexts.Term
      (rules R (authoredEquationModelAt S equations Y.as).algebra)
      (toContext (rules R (authoredEquationModelAt S equations Y.as).algebra) Δ)
      judgment) :
    (value.restrict R equations base).interpretTree R equations judgment tree =
      (mapJudgment_comp base value.program judgment).symm ▸
        value.interpretTree R equations (mapJudgment base judgment)
          (IntrinsicScopedConditionalFiniteContextChange.mapTerm
            R base Δ judgment tree) := by
  unfold Valuation.interpretTree
  change IndexedRuleFiniteContexts.interpretTerm
      (rules R target.base.algebra) target.model.evidence.rules
      (eventAssignment R equations (value.restrict R equations base))
      (IntrinsicScopedConditionalFiniteContextChange.mapTerm
        R (FreeBindingClone.Hom.comp base value.program) Δ judgment tree) = _
  rw [IntrinsicScopedConditionalFiniteContextChange.mapTerm_comp_base
    R base value.program Δ judgment tree]
  rfl

/-- Event-tree reassignment is natural in a binding-model change. Each
retained event position is transported independently, even if two resulting
judgments become equal. -/
theorem Valuation.restrict_reassign
    {Y : EquationContexts (authoredEquationPresentation S equations)}
    {Δ Θ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    (base : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y.as).algebra
      (authoredEquationModelAt S equations X.as).algebra)
    (value : Valuation R equations target X (pushContext R base Δ))
    (events : Δ ⟶ Θ) :
    (value.restrict R equations base).reassign R equations events =
      (value.reassign R equations
        (pushSubstitution R base events)).restrict R equations base := by
  apply Valuation.ext R equations
    (first := (value.restrict R equations base).reassign R equations events)
    (second := (value.reassign R equations
      (pushSubstitution R base events)).restrict R equations base) rfl
  intro position
  exact value.interpretTree_restrict R equations base
    (Θ.label position) (events _ ⟨position, ⟨rfl⟩⟩)

/-- Restriction along two binding-model changes agrees with restriction
along their composite, with the canonical context reindexing made explicit. -/
theorem Valuation.restrict_comp
    {Y Z : EquationContexts (authoredEquationPresentation S equations)}
    {Θ : ListContext
      (rules R (authoredEquationModelAt S equations Z.as).algebra)}
    (first : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Z.as).algebra
      (authoredEquationModelAt S equations Y.as).algebra)
    (second : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y.as).algebra
      (authoredEquationModelAt S equations X.as).algebra)
    (value : Valuation R equations target X
      (pushContext R second (pushContext R first Θ))) :
    (value.restrict R equations second).restrict R equations first =
      ((pushContext_comp R first second Θ).symm ▸ value).restrict R equations
        (FreeBindingClone.Hom.comp first second) := by
  refine Valuation.ext R equations ?_ ?_
  · apply FreeBindingClone.Hom.ext
    exact Mettapedia.OSLF.Binding.FreeBindingTerms.Hom.ext (fun _ => rfl)
  intro position
  rfl

/-- Restriction is independent of a proof that presents the same binding
model map; the input event context is transported along that equality. -/
theorem Valuation.restrict_congr_base
    {Y : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    (first second : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y.as).algebra
      (authoredEquationModelAt S equations X.as).algebra)
    (same : first = second)
    (value : Valuation R equations target X (pushContext R first Δ)) :
    value.restrict R equations first =
      ((congrArg (fun base => pushContext R base Δ) same) ▸ value).restrict
        R equations second := by
  cases same
  rfl

private theorem valuation_cast_trans
    {A : Type*} {family : A → Type*} {a b c : A}
    (first : a = b) (second : b = c) (value : family a) :
    (first.trans second) ▸ value = second ▸ (first ▸ value) := by
  cases first
  cases second
  rfl

/-- Two stages of event evaluation and program restriction combine into
one event substitution and one composite binding-model restriction. -/
theorem Valuation.reassign_restrict_comp
    {Y Z : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    {Θ : ListContext
      (rules R (authoredEquationModelAt S equations Z.as).algebra)}
    (firstBase : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y.as).algebra
      (authoredEquationModelAt S equations X.as).algebra)
    (secondBase : FreeBindingClone.Hom
      (authoredEquationModelAt S equations Z.as).algebra
      (authoredEquationModelAt S equations Y.as).algebra)
    (value : Valuation R equations target X Γ)
    (firstEvents : Γ ⟶ pushContext R firstBase Δ)
    (secondEvents : Δ ⟶ pushContext R secondBase Θ) :
    (((value.reassign R equations firstEvents).restrict R equations firstBase).reassign
      R equations secondEvents).restrict R equations secondBase =
    ((pushContext_comp R secondBase firstBase Θ).symm ▸
      value.reassign R equations
        (firstEvents ≫ pushSubstitution R firstBase secondEvents)).restrict
      R equations (FreeBindingClone.Hom.comp secondBase firstBase) := by
  rw [Valuation.restrict_reassign R equations firstBase
    (value.reassign R equations firstEvents) secondEvents]
  rw [value.reassign_comp R equations firstEvents
    (pushSubstitution R firstBase secondEvents)]
  exact Valuation.restrict_comp R equations secondBase firstBase
    (value.reassign R equations
      (firstEvents ≫ pushSubstitution R firstBase secondEvents))

/-- Identity restriction is invariant under the proof of equality used
to present its context reindexing. -/
theorem Valuation.restrict_cast_id
    (base : FreeBindingClone.Hom
      (authoredEquationModelAt S equations X.as).algebra
      (authoredEquationModelAt S equations X.as).algebra)
    (baseId : base = FreeBindingClone.Hom.id
      (authoredEquationModelAt S equations X.as).algebra)
    (equal : Γ = pushContext R base Γ)
    (value : Valuation R equations target X Γ) :
    (equal ▸ value).restrict R equations base = value := by
  cases baseId
  cases equal
  rfl

/-- A combined contextual arrow transports both the program assignment
and each event variable. Its event component is interpreted as a complete
free firing tree under the source valuation. -/
noncomputable def Valuation.transport
    (value : Valuation R equations target X Γ)
    {Y : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    (combined : object R equations X Γ ⟶ object R equations Y Δ) :
    Valuation R equations target Y Δ := by
  let parts := homEquiv R equations Γ Δ combined
  let base := authoredEquationModelMapQuot S equations parts.1
  refine ⟨FreeBindingClone.Hom.comp base value.program, ?_⟩
  intro position
  let judgment := Δ.label position
  let tree := parts.2 (mapJudgment base judgment)
    (⟨position, ⟨rfl⟩⟩ :
      (toContext (rules R
        (authoredEquationModelAt S equations X.as).algebra)
        (pushContext R base Δ)).slots (mapJudgment base judgment))
  have indexEq :
      mapJudgment (FreeBindingClone.Hom.comp base value.program) judgment =
        mapJudgment value.program (mapJudgment base judgment) :=
    Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.mapJudgment_comp
      base value.program judgment
  exact indexEq.symm ▸ value.interpretTree R equations
    (mapJudgment base judgment) tree

/-- Combined semantic transport factors canonically into event-tree
evaluation followed by restriction of the program interpretation. -/
theorem Valuation.transport_factor
    (value : Valuation R equations target X Γ)
    {Y : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    (combined : object R equations X Γ ⟶ object R equations Y Δ) :
    value.transport R equations combined =
      ((value.reassign R equations
        (homEquiv R equations Γ Δ combined).2).restrict R equations
          (authoredEquationModelMapQuot S equations
            (homEquiv R equations Γ Δ combined).1)) := by
  apply Valuation.ext R equations
    (first := value.transport R equations combined)
    (second :=
      ((value.reassign R equations
        (homEquiv R equations Γ Δ combined).2).restrict R equations
          (authoredEquationModelMapQuot S equations
            (homEquiv R equations Γ Δ combined).1))) rfl
  intro position
  rfl

/-- The program component of the identity contextual assignment remains
the original binding-equation interpretation. -/
theorem Valuation.transport_id_program
    (value : Valuation R equations target X Γ) :
    (value.transport R equations
      (𝟙 (object R equations X Γ))).program = value.program := by
  change FreeBindingClone.Hom.comp
      (authoredEquationModelMapQuot S equations (𝟙 X))
      value.program = value.program
  change FreeBindingClone.Hom.comp
      (authoredEquationModelMap S equations (𝟙 X.as))
      value.program = value.program
  rw [authoredEquationModelMap_id S equations X.as]
  apply FreeBindingClone.Hom.ext
  exact Mettapedia.OSLF.Binding.FreeBindingTerms.Hom.ext (fun _ => rfl)

/-- The combined identity leaves both program assignments and retained
event witnesses unchanged. -/
theorem Valuation.transport_id
    (value : Valuation R equations target X Γ) :
    value.transport R equations (𝟙 (object R equations X Γ)) = value := by
  rw [value.transport_factor R equations]
  simp only [homEquiv_id_base, homEquiv_id_events]
  rw [value.reassign_eqToHom R equations]
  have baseId : authoredEquationModelMapQuot S equations (𝟙 X) =
      FreeBindingClone.Hom.id
        (authoredEquationModelAt S equations X.as).algebra := by
    change authoredEquationModelMap S equations (𝟙 X.as) = _
    exact authoredEquationModelMap_id S equations X.as
  exact Valuation.restrict_cast_id R equations _ baseId _ value

/-- The program interpretation of two combined contextual assignments
agrees with the program interpretation of their composite. -/
theorem Valuation.transport_comp_program
    (value : Valuation R equations target X Γ)
    {Y Z : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    {Θ : ListContext
      (rules R (authoredEquationModelAt S equations Z.as).algebra)}
    (first : object R equations X Γ ⟶ object R equations Y Δ)
    (second : object R equations Y Δ ⟶ object R equations Z Θ) :
    ((value.transport R equations first).transport R equations second).program =
      (value.transport R equations (first ≫ second)).program := by
  have modelMapComp :
      authoredEquationModelMapQuot S equations
          ((homEquiv R equations Γ Δ first).1 ≫
            (homEquiv R equations Δ Θ second).1) =
        FreeBindingClone.Hom.comp
          (authoredEquationModelMapQuot S equations
            (homEquiv R equations Δ Θ second).1)
          (authoredEquationModelMapQuot S equations
            (homEquiv R equations Γ Δ first).1) := by
    exact (authoredEquationQuotientModelPresheaf S equations).map_comp
      ((homEquiv R equations Δ Θ second).1.op)
      ((homEquiv R equations Γ Δ first).1.op)
  change FreeBindingClone.Hom.comp
      (authoredEquationModelMapQuot S equations
        (homEquiv R equations Δ Θ second).1)
      (FreeBindingClone.Hom.comp
        (authoredEquationModelMapQuot S equations
          (homEquiv R equations Γ Δ first).1) value.program) =
    FreeBindingClone.Hom.comp
      (authoredEquationModelMapQuot S equations
        (homEquiv R equations Γ Θ (first ≫ second)).1) value.program
  rw [homEquiv_comp_base R equations first second, modelMapComp]
  apply FreeBindingClone.Hom.ext
  exact Mettapedia.OSLF.Binding.FreeBindingTerms.Hom.ext (fun _ => rfl)

/-- Transport through two combined contextual assignments agrees with
transport through their composite, including each retained firing witness. -/
theorem Valuation.transport_comp
    (value : Valuation R equations target X Γ)
    {Y Z : EquationContexts (authoredEquationPresentation S equations)}
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations Y.as).algebra)}
    {Θ : ListContext
      (rules R (authoredEquationModelAt S equations Z.as).algebra)}
    (first : object R equations X Γ ⟶ object R equations Y Δ)
    (second : object R equations Y Δ ⟶ object R equations Z Θ) :
    (value.transport R equations first).transport R equations second =
      value.transport R equations (first ≫ second) := by
  let firstPart := homEquiv R equations Γ Δ first
  let secondPart := homEquiv R equations Δ Θ second
  let firstBase := authoredEquationModelMapQuot S equations firstPart.1
  let secondBase := authoredEquationModelMapQuot S equations secondPart.1
  let firstEvents := firstPart.2
  let secondEvents := secondPart.2
  let joinedEvents := firstEvents ≫ pushSubstitution R firstBase secondEvents
  have baseComp :
      authoredEquationModelMapQuot S equations (firstPart.1 ≫ secondPart.1) =
        FreeBindingClone.Hom.comp secondBase firstBase := by
    exact (authoredEquationQuotientModelPresheaf S equations).map_comp
      secondPart.1.op firstPart.1.op
  let joinedContext :=
    reindexedContext_comp R equations Θ firstPart.1 secondPart.1
  have eventNormal :
      (homEquiv R equations Γ Θ (first ≫ second)).2 =
        joinedEvents ≫ eqToHom joinedContext := by
    simpa only [joinedEvents, joinedContext, firstEvents, secondEvents,
      Category.assoc,
      firstBase, secondBase, firstPart, secondPart] using
      (homEquiv_comp_events R equations first second)
  have reassigned :
      value.reassign R equations (joinedEvents ≫ eqToHom joinedContext) =
        joinedContext ▸ value.reassign R equations joinedEvents := by
    rw [← value.reassign_comp R equations joinedEvents
      (eqToHom joinedContext)]
    exact Valuation.reassign_eqToHom R equations
      (value.reassign R equations joinedEvents) joinedContext
  let staged := value.reassign R equations joinedEvents
  let firstContextEq := pushContext_comp R secondBase firstBase Θ
  let modelContextEq :=
    congrArg (fun base => pushContext R base Θ) baseComp.symm
  have contextProofEq :
      joinedContext = firstContextEq.symm.trans modelContextEq :=
    Subsingleton.elim _ _
  have stagedCast :
      joinedContext ▸ staged =
        modelContextEq ▸ (firstContextEq.symm ▸ staged) := by
    rw [contextProofEq]
    exact valuation_cast_trans firstContextEq.symm modelContextEq staged
  calc
    (value.transport R equations first).transport R equations second =
        (((value.reassign R equations firstEvents).restrict R equations firstBase).reassign
          R equations secondEvents).restrict R equations secondBase := by
            rw [(value.transport R equations first).transport_factor R equations second]
            rw [value.transport_factor R equations first]
    _ = ((pushContext_comp R secondBase firstBase Θ).symm ▸
          value.reassign R equations joinedEvents).restrict R equations
            (FreeBindingClone.Hom.comp secondBase firstBase) :=
          value.reassign_restrict_comp R equations firstBase secondBase
            firstEvents secondEvents
    _ = value.transport R equations (first ≫ second) := by
          rw [value.transport_factor R equations (first ≫ second)]
          change _ = (value.reassign R equations
            (homEquiv R equations Γ Θ (first ≫ second)).2).restrict
              R equations
              (authoredEquationModelMapQuot S equations
                (firstPart.1 ≫ secondPart.1))
          rw [eventNormal]
          let compositeBase := authoredEquationModelMapQuot S equations
            (firstPart.1 ≫ secondPart.1)
          calc
            ((firstContextEq.symm ▸ staged).restrict R equations
                (FreeBindingClone.Hom.comp secondBase firstBase)) =
              (modelContextEq ▸ (firstContextEq.symm ▸ staged)).restrict
                R equations compositeBase :=
                  Valuation.restrict_congr_base R equations
                    (FreeBindingClone.Hom.comp secondBase firstBase)
                    compositeBase baseComp.symm
                    (firstContextEq.symm ▸ staged)
            _ = (joinedContext ▸ staged).restrict R equations
                compositeBase := by rw [stagedCast]
            _ = (value.reassign R equations
                  (joinedEvents ≫ eqToHom joinedContext)).restrict
                R equations compositeBase :=
                  congrArg (fun assigned => assigned.restrict R equations
                    compositeBase) reassigned.symm

/-- An independently supplied substitution-operational model interprets
every combined authored context and every combined assignment. The functor
keeps individual event witnesses, rather than passing first to endpoints. -/
noncomputable def combinedSetSemantics
    (target : SubstitutionOperationalModel R equations) :
    ClassifierContext R equations ⥤ Type where
  obj contextual := Valuation R equations target
    contextual.unop.base.unop contextual.unop.fiber.unop
  map combined := TypeCat.ofHom (fun value =>
    value.transport R equations combined)
  map_id contextual := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact value.transport_id R equations
  map_comp first second := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact (value.transport_comp R equations first second).symm

/-- On a fixed program context, the combined interpretation reduces to
evaluation of the same free firing-tree substitution as the fiber model. -/
theorem Valuation.transport_fiberArrow
    (value : Valuation R equations target X Γ)
    {Δ : ListContext
      (rules R (authoredEquationModelAt S equations X.as).algebra)}
    (events : Γ ⟶ Δ) :
    value.transport R equations (fiberArrow R equations X events) =
      value.reassign R equations events := by
  let identityEvents :=
    (homEquiv R equations Δ Δ (𝟙 (object R equations X Δ))).2
  let identityContext : Δ =
      pushContext R (authoredEquationModelMapQuot S equations (𝟙 X)) Δ := by
    have baseId : authoredEquationModelMapQuot S equations (𝟙 X) =
        FreeBindingClone.Hom.id
          (authoredEquationModelAt S equations X.as).algebra := by
      change authoredEquationModelMap S equations (𝟙 X.as) = _
      exact authoredEquationModelMap_id S equations X.as
    rw [baseId]
    exact (pushContext_id R
      (authoredEquationModelAt S equations X.as).algebra Δ).symm
  have identityEventsEq : identityEvents = eqToHom identityContext := by
    simpa only [identityEvents] using homEquiv_id_events R equations Δ
  have eventNormal :
      (homEquiv R equations Γ Δ (fiberArrow R equations X events)).2 =
        events ≫ identityEvents :=
    homEquiv_fiberArrow_events R equations X events
  have assignedEq :
      value.reassign R equations (events ≫ identityEvents) =
        identityContext ▸ value.reassign R equations events := by
    rw [← value.reassign_comp R equations events identityEvents]
    rw [identityEventsEq]
    exact (value.reassign R equations events).reassign_eqToHom
      R equations identityContext
  have baseId : authoredEquationModelMapQuot S equations (𝟙 X) =
      FreeBindingClone.Hom.id
        (authoredEquationModelAt S equations X.as).algebra := by
    change authoredEquationModelMap S equations (𝟙 X.as) = _
    exact authoredEquationModelMap_id S equations X.as
  rw [value.transport_factor R equations]
  change (value.reassign R equations
    (homEquiv R equations Γ Δ (fiberArrow R equations X events)).2).restrict
      R equations (authoredEquationModelMapQuot S equations (𝟙 X)) = _
  rw [eventNormal]
  calc
    (value.reassign R equations (events ≫ identityEvents)).restrict
        R equations (authoredEquationModelMapQuot S equations (𝟙 X)) =
      (identityContext ▸ value.reassign R equations events).restrict
        R equations (authoredEquationModelMapQuot S equations (𝟙 X)) :=
          congrArg (fun assigned => assigned.restrict R equations
            (authoredEquationModelMapQuot S equations (𝟙 X))) assignedEq
    _ = value.reassign R equations events :=
      Valuation.restrict_cast_id R equations _ baseId identityContext
        (value.reassign R equations events)

/-- The combined interpretation restricts exactly to the existing
fixed-program-context interpretation of free event substitutions. -/
theorem combinedSetSemantics_fiber
    (target : SubstitutionOperationalModel R equations)
    (X : EquationContexts (authoredEquationPresentation S equations)) :
    fiberFunctor R equations X ⋙ combinedSetSemantics R equations target =
      fiberSemantics R equations target X := by
  refine CategoryTheory.Functor.hext (fun Γ => rfl) ?_
  intro Γ Δ events
  apply heq_of_eq
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact value.transport_fiberArrow R equations events

/-- The combined classifier interprets an authored rule generator by
evaluation of its free constructor tree, with every premise slot retained. -/
theorem combinedSetSemantics_constructor
    (target : SubstitutionOperationalModel R equations)
    (X : EquationContexts (authoredEquationPresentation S equations))
    {judgment : Judgment (authoredEquationModelAt S equations X.as).algebra}
    (shape : (rules R (authoredEquationModelAt S equations X.as).algebra).Shape
      PUnit.unit judgment) :
    (combinedSetSemantics R equations target).map
        (constructor R equations X shape) =
      TypeCat.ofHom (fun value => value.reassign R equations
        (constructorArrowList R
          (authoredEquationModelAt S equations X.as).algebra shape)) := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact value.transport_fiberArrow R equations
    (constructorArrowList R
      (authoredEquationModelAt S equations X.as).algebra shape)

/-- The result event of an authored constructor is the target model's
actual rule action on its individually interpreted, binder-local premises. -/
theorem Valuation.reassign_constructor_action
    {judgment : Judgment (authoredEquationModelAt S equations X.as).algebra}
    (shape : (rules R (authoredEquationModelAt S equations X.as).algebra).Shape
      PUnit.unit judgment)
    (value : Valuation R equations target X
      (arityList R (authoredEquationModelAt S equations X.as).algebra shape)) :
    (value.reassign R equations
      (constructorArrowList R
        (authoredEquationModelAt S equations X.as).algebra shape)).event
        ⟨0, by simp [singletonList]⟩ =
      target.model.evidence.rules.act ()
        (mapJudgment value.program judgment)
        ⟨mapShape R value.program shape,
          fun position =>
            IndexedRuleFiniteContexts.interpretTerm
              (rules R target.base.algebra)
              target.model.evidence.rules value.eventAssignment
              (((presentationMap R value.program).rules.onNext
                PUnit.unit judgment shape position).symm ▸
                IntrinsicScopedConditionalFiniteContextChange.mapTerm
                  R value.program
                  (arityList R
                    (authoredEquationModelAt S equations X.as).algebra shape) _
                  (IndexedPolynomial.Free.pure
                    (rules R (authoredEquationModelAt S equations X.as).algebra)
                    ⟨((presentationMap R value.program).rules.onPosition
                      PUnit.unit judgment shape) position, ⟨rfl⟩⟩))⟩ := by
  change value.interpretTree R equations judgment
      (IndexedPolynomial.Free.node
        (rules R (authoredEquationModelAt S equations X.as).algebra)
        shape (fun position =>
          IndexedPolynomial.Free.pure
            (rules R (authoredEquationModelAt S equations X.as).algebra)
            ⟨position, ⟨rfl⟩⟩)) = _
  exact value.interpretTree_node R equations shape
    (fun position => IndexedPolynomial.Free.pure
      (rules R (authoredEquationModelAt S equations X.as).algebra)
      ⟨position, ⟨rfl⟩⟩)

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierSetSemantics
