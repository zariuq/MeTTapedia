import Mettapedia.GSLT.Logic.ObservedGradedFamilyDescent
import Mettapedia.GSLT.Logic.AdmissibleContextCongruence
import Mettapedia.GSLT.Logic.ObservationSpans

/-!
# Exact finite-depth readings through all admissible contexts

The observer reads the declared bounded formulas after every admissible
context. Its kernel is the largest context-closed relation contained in
ordinary finite-depth agreement. Context identity and composition construct
actual actions on complete observation fibres. Commuting substitutions act
without selecting representatives, and material family and term descent
use the precise contextual kernel.

The context class can be infinite. This construction does not claim that
contextual finite-depth agreement is infinite behavioural bisimilarity,
that context labels admit a finite vocabulary, or that finite-depth agreement
preserves same-depth transitions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualGradedFamilyDescent

open Distinction.Constructive MinimalEnablingContext AdmissibleContextCongruence
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassFamilyDescent

universe uS uAtom uLabel uObs uV uContext uRule

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{uS}} {K : Scale V}
variable (system : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)
variable {rules : ContextualRules.{uContext, uRule} S}
variable (contexts : AdmissibleClass rules)
variable (depth : Nat)

abbrev Reading := {context : rules.Context // contexts.Admissible context} →
  ObservedGradedFamilyDescent.BoundedFormula system depth → V

def readout (source : S.Term) : Reading system contexts depth :=
  fun context => ObservedGradedFamilyDescent.readout system depth (rules.plug context.val source)

abbrev Class := ObservationClass (readout system contexts depth)

theorem readout_respects_equations {left right : S.Term} (same : S.Equiv left right) :
    readout system contexts depth left = readout system contexts depth right := by
  funext context
  exact ObservedGradedFamilyDescent.readout_respects_equations system depth
    (rules.plug_resp context.val same)

theorem readout_eq_iff (vocabulary : system.Vocabulary) (left right : S.Term) :
    readout system contexts depth left = readout system contexts depth right ↔
      ∀ context, contexts.Admissible context →
        system.depthBound vocabulary depth (rules.plug context left) (rules.plug context right) = 0 := by
  constructor
  · intro same context admitted
    exact (ObservedGradedFamilyDescent.readout_eq_iff system vocabulary depth _ _).mp
      (congrFun same ⟨context, admitted⟩)
  · intro same
    funext context
    exact (ObservedGradedFamilyDescent.readout_eq_iff system vocabulary depth _ _).mpr
      (same context.val context.property)

def contextReading (inner : rules.Context) (admitted : contexts.Admissible inner)
    (reading : Reading system contexts depth) : Reading system contexts depth :=
  fun outer => reading ⟨rules.compose outer.val inner,
    contexts.compose_mem outer.property admitted⟩

theorem contextReading_beta (inner : rules.Context) (admitted : contexts.Admissible inner)
    (source : S.Term) :
    readout system contexts depth (rules.plug inner source) =
      contextReading system contexts depth inner admitted (readout system contexts depth source) := by
  funext outer
  exact (ObservedGradedFamilyDescent.readout_respects_equations system depth
    (rules.plug_compose outer.val inner source)).symm

theorem context_kernel_closed : contexts.ClosedUnder (fun left right =>
    readout system contexts depth left = readout system contexts depth right) := by
  intro context left right admitted same
  rw [contextReading_beta system contexts depth context admitted left,
    contextReading_beta system contexts depth context admitted right, same]

theorem kernel_identity {left right : S.Term}
    (same : readout system contexts depth left = readout system contexts depth right) :
    ObservedGradedFamilyDescent.readout system depth left =
      ObservedGradedFamilyDescent.readout system depth right := by
  have atIdentity := congrFun same ⟨rules.identity, contexts.identity_mem⟩
  exact (ObservedGradedFamilyDescent.readout_respects_equations system depth
    (rules.plug_identity left)).symm.trans
      (atIdentity.trans (ObservedGradedFamilyDescent.readout_respects_equations system depth
        (rules.plug_identity right)))

/-- Maximality is proved for the actual context-closed kernel, rather than
assumed as an observation-respect field. -/
theorem greatest_context_closed_kernel (relation : S.Term → S.Term → Prop)
    (contained : ∀ ⦃left right⦄, relation left right →
      ObservedGradedFamilyDescent.readout system depth left =
        ObservedGradedFamilyDescent.readout system depth right)
    (closed : contexts.ClosedUnder relation) {left right : S.Term} (related : relation left right) :
    readout system contexts depth left = readout system contexts depth right := by
  funext context
  exact contained (closed context.property related)

def contextAction (inner : rules.Context) (admitted : contexts.Admissible inner) :
    Class system contexts depth → Class system contexts depth :=
  classMap (readout system contexts depth) (readout system contexts depth)
    (rules.plug inner) (contextReading system contexts depth inner admitted)
    (contextReading_beta system contexts depth inner admitted)

theorem contextAction_beta (inner : rules.Context) (admitted : contexts.Admissible inner)
    (source : S.Term) :
    contextAction system contexts depth inner admitted (classOf (readout system contexts depth) source) =
      classOf (readout system contexts depth) (rules.plug inner source) :=
  classMap_beta _ _ _ _ _ source

theorem contextAction_identity (observed : Class system contexts depth) :
    contextAction system contexts depth rules.identity contexts.identity_mem observed = observed := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system contexts depth) observed
  rw [contextAction_beta]
  exact (classOf_eq_iff _ _ _).mpr
    (readout_respects_equations system contexts depth (rules.plug_identity source))

theorem contextAction_compose (outer inner : rules.Context)
    (outerAdmitted : contexts.Admissible outer) (innerAdmitted : contexts.Admissible inner)
    (observed : Class system contexts depth) :
    contextAction system contexts depth (rules.compose outer inner)
        (contexts.compose_mem outerAdmitted innerAdmitted) observed =
      contextAction system contexts depth outer outerAdmitted
        (contextAction system contexts depth inner innerAdmitted observed) := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system contexts depth) observed
  rw [contextAction_beta, contextAction_beta, contextAction_beta]
  exact (classOf_eq_iff _ _ _).mpr
    (readout_respects_equations system contexts depth (rules.plug_compose outer inner source))

/-- Complete observation fibres let a kernel-preserving map act without
an inverse observer or a selected source representative. -/
def substitutionAction (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄,
      readout system contexts depth left = readout system contexts depth right →
        readout system contexts depth (substitution left) = readout system contexts depth (substitution right))
    (observed : Class system contexts depth) : Class system contexts depth :=
  ⟨{target | ∃ source, source ∈ observed.val ∧
      readout system contexts depth target = readout system contexts depth (substitution source)}, by
    obtain ⟨source, same⟩ := observed.property
    refine ⟨substitution source, ?_⟩
    funext target
    apply propext
    constructor
    · rintro ⟨witness, member, reading⟩
      rw [same] at member
      exact reading.trans (respects member)
    · intro reading
      exact ⟨source, by rw [same]; rfl, reading⟩⟩

theorem substitutionAction_beta (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄,
      readout system contexts depth left = readout system contexts depth right →
        readout system contexts depth (substitution left) = readout system contexts depth (substitution right))
    (source : S.Term) :
    substitutionAction system contexts depth substitution respects
        (classOf (readout system contexts depth) source) =
      classOf (readout system contexts depth) (substitution source) := by
  apply Subtype.ext
  funext target
  apply propext
  constructor
  · rintro ⟨witness, related, reading⟩
    exact reading.trans (respects related)
  · intro reading
    exact ⟨source, rfl, reading⟩

theorem substitutionAction_identity (observed : Class system contexts depth) :
    substitutionAction system contexts depth id (fun {_left _right} same => same) observed = observed := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system contexts depth) observed
  exact substitutionAction_beta system contexts depth id (fun {_left _right} same => same) source

theorem substitutionAction_compose (earlier later : S.Term → S.Term)
    (earlierRespects : ∀ ⦃left right⦄,
      readout system contexts depth left = readout system contexts depth right →
        readout system contexts depth (earlier left) = readout system contexts depth (earlier right))
    (laterRespects : ∀ ⦃left right⦄,
      readout system contexts depth left = readout system contexts depth right →
        readout system contexts depth (later left) = readout system contexts depth (later right))
    (observed : Class system contexts depth) :
    substitutionAction system contexts depth (later ∘ earlier)
        (fun {_left _right} same => laterRespects (earlierRespects same)) observed =
      substitutionAction system contexts depth later laterRespects
        (substitutionAction system contexts depth earlier earlierRespects observed) := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system contexts depth) observed
  rw [substitutionAction_beta, substitutionAction_beta, substitutionAction_beta]
  rfl

theorem substitutionAction_exists_iff (substitution : S.Term → S.Term) :
    (∃ action : Class system contexts depth → Class system contexts depth,
      ∀ source, action (classOf (readout system contexts depth) source) =
        classOf (readout system contexts depth) (substitution source)) ↔
      ∀ ⦃left right⦄,
        readout system contexts depth left = readout system contexts depth right →
          readout system contexts depth (substitution left) = readout system contexts depth (substitution right) := by
  constructor
  · rintro ⟨action, beta⟩ left right same
    apply (classOf_eq_iff _ _ _).mp
    exact (beta left).symm.trans
      ((congrArg action ((classOf_eq_iff _ _ _).mpr same)).trans (beta right))
  · intro respects
    exact ⟨substitutionAction system contexts depth substitution respects,
      substitutionAction_beta system contexts depth substitution respects⟩

theorem substitution_kernel_of_commuting (substitution : S.Term → S.Term)
    (baseRespects : ∀ ⦃left right⦄,
      ObservedGradedFamilyDescent.readout system depth left =
        ObservedGradedFamilyDescent.readout system depth right →
      ObservedGradedFamilyDescent.readout system depth (substitution left) =
        ObservedGradedFamilyDescent.readout system depth (substitution right))
    (commutes : ∀ context, contexts.Admissible context → ∀ source,
      S.Equiv (substitution (rules.plug context source)) (rules.plug context (substitution source)))
    {left right : S.Term} (same : readout system contexts depth left = readout system contexts depth right) :
    readout system contexts depth (substitution left) = readout system contexts depth (substitution right) := by
  funext context
  exact (ObservedGradedFamilyDescent.readout_respects_equations system depth
    (commutes context.val context.property left)).symm.trans
    ((baseRespects (congrFun same context)).trans
      (ObservedGradedFamilyDescent.readout_respects_equations system depth
        (commutes context.val context.property right)))

theorem context_substitution (inner : rules.Context) (admitted : contexts.Admissible inner)
    (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄,
      readout system contexts depth left = readout system contexts depth right →
        readout system contexts depth (substitution left) = readout system contexts depth (substitution right))
    (commutes : ∀ source,
      S.Equiv (substitution (rules.plug inner source)) (rules.plug inner (substitution source)))
    (observed : Class system contexts depth) :
    substitutionAction system contexts depth substitution respects
        (contextAction system contexts depth inner admitted observed) =
      contextAction system contexts depth inner admitted
        (substitutionAction system contexts depth substitution respects observed) := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system contexts depth) observed
  rw [contextAction_beta, substitutionAction_beta, substitutionAction_beta, contextAction_beta]
  exact (classOf_eq_iff _ _ _).mpr (readout_respects_equations system contexts depth (commutes source))

theorem predicate_descends_iff (vocabulary : system.Vocabulary) (predicate : S.Term → Prop) :
    ObservationSpans.PredicateDescends (readout system contexts depth) predicate ↔
      ∀ ⦃left right⦄,
        (∀ context, contexts.Admissible context → system.depthBound vocabulary depth
          (rules.plug context left) (rules.plug context right) = 0) →
        (predicate left ↔ predicate right) := by
  rw [ObservationSpans.predicateDescends_iff]
  constructor
  · intro descends left right zero
    exact Scope.ConstantOnFibers.iff descends
      ((readout_eq_iff system contexts depth vocabulary left right).mpr zero)
  · intro descends left right same
    exact propext (descends ((readout_eq_iff system contexts depth vocabulary left right).mp same))

theorem family_descends_iff (vocabulary : system.Vocabulary)
    (graphs : S.Term → AccessiblePointedGraph.{uS}) :
    FamilyInvariant (readout system contexts depth) graphs ↔
      ∀ ⦃left right⦄,
        (∀ context, contexts.Admissible context → system.depthBound vocabulary depth
          (rules.plug context left) (rules.plug context right) = 0) →
        HSet.mk (graphs left) = HSet.mk (graphs right) := by
  constructor
  · intro descends left right zero
    exact descends ((readout_eq_iff system contexts depth vocabulary left right).mpr zero)
  · intro descends left right same
    exact descends ((readout_eq_iff system contexts depth vocabulary left right).mp same)

theorem term_descends_iff (vocabulary : system.Vocabulary)
    (graphs : S.Term → AccessiblePointedGraph.{uS}) (term : SourceSection graphs) :
    TermCompatible (readout system contexts depth) graphs term ↔
      ∀ ⦃left right⦄,
        (∀ context, contexts.Admissible context → system.depthBound vocabulary depth
          (rules.plug context left) (rules.plug context right) = 0) →
        (term left).1 = (term right).1 := by
  constructor
  · intro descends left right zero
    exact descends ((readout_eq_iff system contexts depth vocabulary left right).mpr zero)
  · intro descends left right same
    exact descends ((readout_eq_iff system contexts depth vocabulary left right).mp same)

theorem family_decoder_exact_iff (vocabulary : system.Vocabulary)
    (graphs : S.Term → AccessiblePointedGraph.{uS}) :
    (∀ source, decodedFamily graphs (classOf (readout system contexts depth) source) =
      HSet.mk (graphs source)) ↔
      ∀ ⦃left right⦄,
        (∀ context, contexts.Admissible context → system.depthBound vocabulary depth
          (rules.plug context left) (rules.plug context right) = 0) →
        HSet.mk (graphs left) = HSet.mk (graphs right) :=
  (familyInvariant_iff_beta (readout system contexts depth) graphs).symm.trans
    (family_descends_iff system contexts depth vocabulary graphs)

theorem selected_decoder_exact_iff (vocabulary : system.Vocabulary)
    (graphs : S.Term → AccessiblePointedGraph.{uS}) (term : SourceSection graphs) :
    (∀ source, termValue graphs term (classOf (readout system contexts depth) source) =
      (term source).1) ↔
      ∀ ⦃left right⦄,
        (∀ context, contexts.Admissible context → system.depthBound vocabulary depth
          (rules.plug context left) (rules.plug context right) = 0) →
        (term left).1 = (term right).1 :=
  (termCompatible_iff_beta (readout system contexts depth) graphs term).symm.trans
    (term_descends_iff system contexts depth vocabulary graphs term)

def sectionEquiv (graphs : S.Term → AccessiblePointedGraph.{uS})
    (invariant : FamilyInvariant (readout system contexts depth) graphs) :
    (∀ observed : Class system contexts depth, El (· ∈ ·) (decodedFamily graphs observed)) ≃
      {term : SourceSection graphs // TermCompatible (readout system contexts depth) graphs term} :=
  materialSectionEquiv (readout system contexts depth) graphs invariant

theorem sectionEquiv_inverse_value (graphs : S.Term → AccessiblePointedGraph.{uS})
    (invariant : FamilyInvariant (readout system contexts depth) graphs)
    (term : {term : SourceSection graphs // TermCompatible (readout system contexts depth) graphs term})
    (source : S.Term) :
    ((sectionEquiv system contexts depth graphs invariant).symm term
      (classOf (readout system contexts depth) source)).1 = (term.val source).1 :=
  descendTerm_beta_value (readout system contexts depth) graphs invariant term.val term.property source

end Mettapedia.GSLT.ContextualGradedFamilyDescent
