import Mettapedia.OSLF.Framework.ProfiledRewriteOccurrence
import Mettapedia.OSLF.Framework.SelectedNativeTypeVertex

/-!
# Intrinsically profiled demands for sparse native-type generation

A sparse native-type demand is an authored-order list of atomic profiled
rewrite occurrences.  Each atom packages its occurrence typing, carrier
grounding certificate, and exactly indexed local hypercube profile.  This is
the dependent-container normal form: no parallel typing/profile lists and no
post-hoc alignment proof.

The carrier foundation and indexed vertex remain available as derived views.
They are useful factors for proofs and specialized compilation, but they are
not additional stores and do not form a second generated-language
representation.  The generator still returns one flat calculus GSLT.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef

/-- Complete finite input coordinate for sparse native-type generation over
one source GSLT. -/
structure SelectedNativeTypeDemand (source : ValidatedLanguageDef) where
  occurrences : List (ProfiledRewriteOccurrence source)

namespace SelectedNativeTypeDemand

/-- Forget local profiles while retaining the exact grounded occurrence
typing stream needed by the carrier foundation. -/
def foundation {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    SelectedNativeTypeFoundation.Demand source where
  typings := demand.occurrences.map ProfiledRewriteOccurrence.typing
  grounded := by
    intro typing typingMembership
    obtain ⟨occurrence, occurrenceMembership, rfl⟩ :=
      List.mem_map.mp typingMembership
    exact occurrence.grounded

private def vertexOf {source : ValidatedLanguageDef} :
    (occurrences : List (ProfiledRewriteOccurrence source)) →
      SelectedNativeTypeVertex.Vertex
        (occurrences.map ProfiledRewriteOccurrence.typing)
  | [] => .nil
  | occurrence :: occurrences =>
      .cons occurrence.profile (vertexOf occurrences)

/-- Indexed hypercube vertex derived from the same atomic occurrence list. -/
def vertex {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    SelectedNativeTypeVertex.Vertex demand.foundation.typings :=
  vertexOf demand.occurrences

/-- Canonical authored-order profile wire.  The outer row order is the
selected occurrence order; every inner row is the exact contextual slot
order for that occurrence. -/
def choices {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    List (List CarrierUniverseSignature.Code) :=
  demand.occurrences.map ProfiledRewriteOccurrence.choices

/-- The derived indexed vertex exposes exactly the same profile wire as the
atomic occurrence list. -/
@[simp]
theorem vertex_choices {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    demand.vertex.choices = demand.choices := by
  change (vertexOf demand.occurrences).choices =
    demand.occurrences.map ProfiledRewriteOccurrence.choices
  induction demand.occurrences with
  | nil => rfl
  | cons occurrence occurrences inductionHypothesis =>
      simp [vertexOf, inductionHypothesis,
        ProfiledRewriteOccurrence.choices]

/-- Equality is ordinary list equality in the dependent-container normal
form. -/
@[ext]
theorem ext {source : ValidatedLanguageDef}
    {first second : SelectedNativeTypeDemand source}
    (occurrences : first.occurrences = second.occurrences) : first = second := by
  cases first
  cases second
  cases occurrences
  rfl

/-- The empty occurrence coordinate. -/
def empty (source : ValidatedLanguageDef) : SelectedNativeTypeDemand source where
  occurrences := []

/-- Ordered composition is ordinary concatenation of atomic selections. -/
def append {source : ValidatedLanguageDef}
    (first second : SelectedNativeTypeDemand source) :
    SelectedNativeTypeDemand source where
  occurrences := first.occurrences ++ second.occurrences

@[simp]
theorem empty_occurrences (source : ValidatedLanguageDef) :
    (empty source).occurrences = [] :=
  rfl

@[simp]
theorem append_occurrences {source : ValidatedLanguageDef}
    (first second : SelectedNativeTypeDemand source) :
    (first.append second).occurrences =
      first.occurrences ++ second.occurrences :=
  rfl

private def constantOccurrences {source : ValidatedLanguageDef}
    (foundation : SelectedNativeTypeFoundation.Demand source)
    (code : CarrierUniverseSignature.Code) :
    List (ProfiledRewriteOccurrence source) :=
  foundation.typings.attach.map fun attached =>
    ProfiledRewriteOccurrence.constant attached.1
      (foundation.grounded attached.1 attached.2) code

private theorem constantOccurrences_typings
    {source : ValidatedLanguageDef}
    (foundation : SelectedNativeTypeFoundation.Demand source)
    (code : CarrierUniverseSignature.Code) :
    (constantOccurrences foundation code).map
        ProfiledRewriteOccurrence.typing = foundation.typings := by
  unfold constantOccurrences
  rw [List.map_map]
  change foundation.typings.attach.map Subtype.val = foundation.typings
  exact List.attach_map_subtype_val foundation.typings

/-- Select a uniform endpoint profile over one grounded foundation demand. -/
def constant {source : ValidatedLanguageDef}
    (foundation : SelectedNativeTypeFoundation.Demand source)
    (code : CarrierUniverseSignature.Code) :
    SelectedNativeTypeDemand source where
  occurrences := constantOccurrences foundation code

@[simp]
theorem foundation_typings {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    demand.foundation.typings =
      demand.occurrences.map ProfiledRewriteOccurrence.typing :=
  rfl

@[simp]
theorem empty_foundation (source : ValidatedLanguageDef) :
    (empty source).foundation =
      SelectedNativeTypeFoundation.Demand.empty source := by
  apply SelectedNativeTypeFoundation.Demand.ext
  rfl

@[simp]
theorem empty_choices (source : ValidatedLanguageDef) :
    (empty source).choices = [] :=
  rfl

@[simp]
theorem append_foundation {source : ValidatedLanguageDef}
    (first second : SelectedNativeTypeDemand source) :
    (first.append second).foundation =
      first.foundation.append second.foundation := by
  apply SelectedNativeTypeFoundation.Demand.ext
  simp [foundation, append]

@[simp]
theorem append_choices {source : ValidatedLanguageDef}
    (first second : SelectedNativeTypeDemand source) :
    (first.append second).choices = first.choices ++ second.choices := by
  simp [choices, append, List.map_append]

@[simp]
theorem length_choices {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    demand.choices.length = demand.foundation.typings.length := by
  simp [choices, foundation]

@[simp]
theorem constant_foundation {source : ValidatedLanguageDef}
    (foundation : SelectedNativeTypeFoundation.Demand source)
    (code : CarrierUniverseSignature.Code) :
    (constant foundation code).foundation = foundation := by
  apply SelectedNativeTypeFoundation.Demand.ext
  exact constantOccurrences_typings foundation code

theorem empty_append {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    (empty source).append demand = demand := by
  apply ext
  simp [empty, append]

theorem append_empty {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    demand.append (empty source) = demand := by
  apply ext
  simp [empty, append]

theorem append_assoc {source : ValidatedLanguageDef}
    (first second third : SelectedNativeTypeDemand source) :
    (first.append second).append third =
      first.append (second.append third) := by
  apply ext
  simp [append, List.append_assoc]

/-- Structural reindexing transports every atomic occurrence as one unit. -/
noncomputable def map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) :
    SelectedNativeTypeDemand target where
  occurrences := demand.occurrences.map
    (ProfiledRewriteOccurrence.map morphism)

@[simp]
theorem map_foundation {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) :
    (demand.map morphism).foundation = demand.foundation.map morphism := by
  apply SelectedNativeTypeFoundation.Demand.ext
  simp [map, foundation, ProfiledRewriteOccurrence.map]

/-- Reindexing preserves the complete profile wire exactly. -/
@[simp]
theorem choices_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (demand : SelectedNativeTypeDemand source) :
    (demand.map morphism).choices = demand.choices := by
  simp [map, choices]

@[simp]
theorem map_empty {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    (empty source).map morphism = empty target := by
  apply ext
  rfl

@[simp]
theorem map_id (source : ValidatedLanguageDef)
    (demand : SelectedNativeTypeDemand source) :
    demand.map (StructuralMorphism.id source) = demand := by
  apply ext
  change demand.occurrences.map
      (ProfiledRewriteOccurrence.map (StructuralMorphism.id source)) =
    demand.occurrences
  induction demand.occurrences with
  | nil => rfl
  | cons occurrence occurrences inductionHypothesis =>
      simp [ProfiledRewriteOccurrence.map_id, inductionHypothesis]

theorem map_comp {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (demand : SelectedNativeTypeDemand first) :
    demand.map (StructuralMorphism.comp earlier later) =
      (demand.map earlier).map later := by
  apply ext
  simp [map, List.map_map, ProfiledRewriteOccurrence.map_comp]

/-- Structural reindexing is strong monoidal for ordered demand composition. -/
theorem map_append {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (first second : SelectedNativeTypeDemand source) :
    (first.append second).map morphism =
      (first.map morphism).append (second.map morphism) := by
  apply ext
  simp [map, append, List.map_append]

/-! ## Positive and negative controls -/

/-- The empty occurrence coordinate has no hidden hypercube choice. -/
theorem constant_empty_star_eq_box (source : ValidatedLanguageDef) :
    constant (SelectedNativeTypeFoundation.Demand.empty source) .star =
      constant (SelectedNativeTypeFoundation.Demand.empty source) .box := by
  apply ext
  rfl

/-- A genuinely selected occurrence retains at least the distinct all-star
and all-box endpoints. -/
theorem constant_singleton_choices_star_ne_box
    {source : ValidatedLanguageDef}
    (foundation : SelectedNativeTypeFoundation.Demand source)
    (typing : DisplayedRewriteTyping source)
    (singleton : foundation.typings = [typing]) :
    (constant foundation .star).choices ≠
      (constant foundation .box).choices := by
  simp [constant, constantOccurrences, choices, singleton,
    ProfiledRewriteOccurrence.constant, ProfiledRewriteOccurrence.choices,
    ContextualModalProfile.constant, ContextualModalProfile.choices]

/-- Distinct singleton profile wires make the complete atomic demands
distinct; proof-valued grounding fields contribute no extra coordinate. -/
theorem constant_singleton_star_ne_box
    {source : ValidatedLanguageDef}
    (foundation : SelectedNativeTypeFoundation.Demand source)
    (typing : DisplayedRewriteTyping source)
    (singleton : foundation.typings = [typing]) :
    constant foundation .star ≠ constant foundation .box := by
  intro equality
  have wireEquality := congrArg
    (fun demand : SelectedNativeTypeDemand source => demand.choices) equality
  exact constant_singleton_choices_star_ne_box
    foundation typing singleton wireEquality

#print axioms ext
#print axioms vertex_choices
#print axioms append_assoc
#print axioms constant_foundation
#print axioms map_id
#print axioms map_empty
#print axioms map_comp
#print axioms map_append
#print axioms constant_empty_star_eq_box
#print axioms constant_singleton_choices_star_ne_box
#print axioms constant_singleton_star_ne_box

end SelectedNativeTypeDemand

end Mettapedia.OSLF.Framework
