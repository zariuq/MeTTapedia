import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.TypeTheory.DisplayedPresheafComprehension

/-!
# Open derivations as contextual displayed evidence

An ordered premise context and goal determine a proof-relevant carrier of
open derivations. Substitution acts by binding the actual proof vector into
that derivation. The goal label is unchanged, while the derivation and its
premise occurrences are retained. This supplies a concrete displayed family
over the category of syntactic proof contexts, not a Prime type former.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

variable (definition : Mettapedia.GSLT.LanguageDef.ValidatedCalculusLanguageDef)

/-- A contextual goal label; its transport does not change the goal. -/
def goalFace : Face (ClassifyingContext definition) :=
  (Functor.const ((ClassifyingContext definition)ᵒᵖ)).obj Pattern

/-- A contextual goal paired with its actual open derivation. Context
substitution binds the retained derivation rather than searching again for
one with the same conclusion. -/
def derivationTotalFace : Face (ClassifyingContext definition) where
  obj context := Σ goal : Pattern,
    OpenDerivation definition context.unop.judgments goal
  map substitution := TypeCat.ofHom fun answer =>
    ⟨answer.1, answer.2.bind substitution.unop⟩
  map_id context := by
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, derivation⟩
    exact congrArg (Sigma.mk goal)
      (OpenDerivation.bind_assumptionEnvironment derivation)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, derivation⟩
    exact congrArg (Sigma.mk goal)
      (OpenDerivation.bind_assoc derivation first.unop second.unop).symm

/-- Forget the retained proof while keeping its contextual goal. This is a
natural transformation because derivation binding preserves the conclusion. -/
def derivationToGoal : derivationTotalFace definition ⟶ goalFace definition where
  app _ := TypeCat.ofHom Sigma.fst
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    intro answer
    rfl

@[simp] theorem derivationToGoal_apply
    (context : (ClassifyingContext definition)ᵒᵖ)
    (answer : (derivationTotalFace definition).obj context) :
    (derivationToGoal definition).app context answer = answer.1 := rfl

@[simp] theorem derivationTotalFace_map
    {source target : (ClassifyingContext definition)ᵒᵖ}
    (substitution : source ⟶ target)
    (answer : (derivationTotalFace definition).obj source) :
    (derivationTotalFace definition).map substitution answer =
      ⟨answer.1, answer.2.bind substitution.unop⟩ := rfl

/-- The fibre of the proof-forgetting map over a contextual goal is
equivalent to the full proof-term type. This is a type equivalence, not an
existence proposition or a subsingleton receipt. -/
def derivationToGoal_fibre
    (context : (ClassifyingContext definition)ᵒᵖ) (goal : Pattern) :
    { answer : (derivationTotalFace definition).obj context //
        (derivationToGoal definition).app context answer = goal } ≃
      OpenDerivation definition context.unop.judgments goal where
  toFun
    | ⟨⟨_, derivation⟩, equal⟩ => equal ▸ derivation
  invFun derivation := ⟨⟨goal, derivation⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨_, derivation⟩, equal⟩
    cases equal
    rfl
  right_inv := by intro derivation; rfl

/-- Substitute a checked proof-bearing answer without re-running the rule
checker. The goal remains fixed, while the actual derivation is rebound to
the target premise context. -/
def reindexDerivationFibre
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source) (goal : Pattern)
    (receipt : { answer : (derivationTotalFace definition).obj (Opposite.op source) //
        (derivationToGoal definition).app (Opposite.op source) answer = goal }) :
    { answer : (derivationTotalFace definition).obj (Opposite.op target) //
        (derivationToGoal definition).app (Opposite.op target) answer = goal } :=
  ⟨⟨receipt.val.1, receipt.val.2.bind substitution⟩, receipt.property⟩

/-- The proof-relevant fibre equivalence commutes with contextual
substitution. This is a naturality law on actual derivation terms. -/
theorem derivationToGoal_fibre_reindex
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source) (goal : Pattern)
    (receipt : { answer : (derivationTotalFace definition).obj (Opposite.op source) //
        (derivationToGoal definition).app (Opposite.op source) answer = goal }) :
    derivationToGoal_fibre definition (Opposite.op target) goal
        (reindexDerivationFibre definition substitution goal receipt) =
      (derivationToGoal_fibre definition (Opposite.op source) goal receipt).bind
        substitution := by
  obtain ⟨⟨otherGoal, derivation⟩, equal⟩ := receipt
  cases equal
  rfl

@[simp] theorem reindexDerivationFibre_id
    (context : ClassifyingContext definition) (goal : Pattern)
    (receipt : { answer : (derivationTotalFace definition).obj (Opposite.op context) //
        (derivationToGoal definition).app (Opposite.op context) answer = goal }) :
    reindexDerivationFibre definition (𝟙 context) goal receipt = receipt := by
  obtain ⟨⟨otherGoal, derivation⟩, equal⟩ := receipt
  cases equal
  simp [reindexDerivationFibre, OpenDerivation.bind_assumptionEnvironment]

/-- Reindexing composes with the actual proof-vector substitution order. -/
theorem reindexDerivationFibre_comp
    {first middle last : ClassifyingContext definition}
    (earlier : middle ⟶ first) (later : last ⟶ middle)
    (goal : Pattern)
    (receipt : { answer : (derivationTotalFace definition).obj (Opposite.op first) //
        (derivationToGoal definition).app (Opposite.op first) answer = goal }) :
    reindexDerivationFibre definition (later ≫ earlier) goal receipt =
      reindexDerivationFibre definition later goal
        (reindexDerivationFibre definition earlier goal receipt) := by
  obtain ⟨⟨otherGoal, derivation⟩, equal⟩ := receipt
  cases equal
  apply Subtype.ext
  exact congrArg (Sigma.mk otherGoal)
    (OpenDerivation.bind_assoc derivation earlier later).symm

/-- Projection of proof-bearing goals is genuinely non-injective: two
distinct assumption occurrences have the same contextual goal observation. -/
theorem derivationToGoal_not_injective_on_duplicates (goal : Pattern) :
    ¬ Function.Injective
      ((derivationToGoal definition).app
        (Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition))) := by
  intro injective
  have same :
      (⟨goal,
        OpenDerivation.assumption (definition := definition)
          (context := [goal, goal]) (0 : Fin 2)⟩ :
        (derivationTotalFace definition).obj
          (Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition))) =
      ⟨goal,
        OpenDerivation.assumption (definition := definition)
          (context := [goal, goal]) (1 : Fin 2)⟩ :=
    injective rfl
  exact ClassifyingContext.duplicate_assumptions_distinct definition goal
    (eq_of_heq (Sigma.mk.inj same).2)

/-- Open derivations, displayed over a context and goal, with substitution
given by the existing proof-term binder. -/
def derivationFamily : DisplayedFamily (goalFace definition) where
  obj value := OpenDerivation definition value.1.unop.judgments value.2
  map {source target} substitution := TypeCat.ofHom fun derivation => by
    have goalEq : source.2 = target.2 := substitution.property
    exact goalEq ▸ derivation.bind substitution.val.unop
  map_id value := by
    apply ConcreteCategory.hom_ext
    intro derivation
    exact OpenDerivation.bind_assumptionEnvironment derivation
  map_comp {source middle target} earlier later := by
    apply ConcreteCategory.hom_ext
    intro derivation
    have earlierGoal : source.2 = middle.2 := earlier.property
    have laterGoal : middle.2 = target.2 := later.property
    cases source with
    | mk sourceContext sourceGoal =>
      cases middle with
      | mk middleContext middleGoal =>
        cases target with
        | mk targetContext targetGoal =>
          dsimp at earlierGoal laterGoal
          subst middleGoal
          subst targetGoal
          exact (OpenDerivation.bind_assoc derivation
            earlier.val.unop later.val.unop).symm

/-- An actual context substitution, seen at one fixed judgment label in
the category of elements of the goal presheaf. -/
def goalSubstitution {source target : ClassifyingContext definition}
    (substitution : target ⟶ source) (goal : Pattern) :=
  CategoryOfElements.homMk
    (⟨Opposite.op source, goal⟩ : (goalFace definition).Elements)
    (⟨Opposite.op target, goal⟩ : (goalFace definition).Elements)
    (Quiver.Hom.op substitution) rfl

/-- The displayed action is exactly the existing proof-term substitution,
not merely a map between propositionally inhabited fibres. -/
@[simp] theorem derivationFamily_map_goalSubstitution
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source) (goal : Pattern)
    (derivation : OpenDerivation definition source.judgments goal) :
    (derivationFamily definition).map
        (goalSubstitution definition substitution goal) derivation =
      derivation.bind substitution := rfl

/-- The goal-indexed arrows compose with the same order as proof-vector
substitution; no implicit reversal of context variance is involved. -/
theorem goalSubstitution_comp
    {first middle last : ClassifyingContext definition}
    (earlier : middle ⟶ first) (later : last ⟶ middle)
    (goal : Pattern) :
    goalSubstitution definition earlier goal ≫
        goalSubstitution definition later goal =
      goalSubstitution definition (later ≫ earlier) goal := by
  apply CategoryOfElements.ext
  rfl

/-- A derivation point retains the proof term over its context and goal. -/
def derivationPoint (context : ClassifyingContext definition)
    (goal : Pattern)
    (derivation : OpenDerivation definition context.judgments goal) :
    (derivationFamily definition).Elements :=
  point (derivationFamily definition)
    ⟨Opposite.op context, goal⟩ derivation

/-- Different premise occurrences of one goal are distinct displayed
evidence, although their projection has the same context and goal. -/
theorem duplicate_assumptions_displayed_distinct (goal : Pattern) :
    derivationPoint definition ⟨[goal, goal]⟩ goal
        (.assumption (definition := definition)
          (context := [goal, goal]) (0 : Fin 2)) ≠
      derivationPoint definition ⟨[goal, goal]⟩ goal
        (.assumption (definition := definition)
          (context := [goal, goal]) (1 : Fin 2)) := by
  intro same
  exact ClassifyingContext.duplicate_assumptions_distinct definition goal
    (point_injective (derivationFamily definition)
      ⟨Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition), goal⟩ same)

#print axioms derivationFamily
#print axioms derivationTotalFace
#print axioms derivationToGoal
#print axioms derivationToGoal_fibre
#print axioms derivationToGoal_fibre_reindex
#print axioms reindexDerivationFibre_id
#print axioms reindexDerivationFibre_comp
#print axioms derivationToGoal_not_injective_on_duplicates
#print axioms goalSubstitution
#print axioms derivationFamily_map_goalSubstitution
#print axioms goalSubstitution_comp
#print axioms derivationPoint
#print axioms duplicate_assumptions_displayed_distinct

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
