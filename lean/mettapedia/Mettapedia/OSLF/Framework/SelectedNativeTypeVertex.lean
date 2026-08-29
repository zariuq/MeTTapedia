import Mettapedia.OSLF.Framework.ContextualModalProfile
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationTransport

/-!
# Intrinsically aligned vertices for sparse native-type generation

The occurrence demand and the local hypercube choice are independent
coordinates, but they must never drift apart.  `Vertex typings` is indexed by
the exact authored-order typing list.  Its constructors enforce one local
profile per occurrence, preserving multiplicity and order without a parallel
list or a post-hoc length check.

This is generator input, not a second language representation.  The generated
artifact remains one flat calculus GSLT.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef

namespace SelectedNativeTypeVertex

/-- One local profile for every typed displayed occurrence, aligned by the
list index itself. -/
inductive Vertex {source : ValidatedLanguageDef} :
    List (DisplayedRewriteTyping source) → Type
  | nil : Vertex []
  | cons {typing : DisplayedRewriteTyping source}
      {typings : List (DisplayedRewriteTyping source)} :
      ContextualModalProfile.Profile typing →
      Vertex typings →
      Vertex (typing :: typings)

namespace Vertex

/-- A demand vertex is indexed by exactly the demand it configures. -/
abbrev ForDemand {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :=
  Vertex demand.typings

/-- Canonical nested-list wire: one authored-order code row per occurrence. -/
def choices {source : ValidatedLanguageDef}
    {typings : List (DisplayedRewriteTyping source)} :
    Vertex typings → List (List CarrierUniverseSignature.Code)
  | .nil => []
  | .cons profile rest =>
      ContextualModalProfile.choices profile :: choices rest

@[simp]
theorem choices_nil {source : ValidatedLanguageDef} :
    choices (source := source) (.nil : Vertex []) = [] :=
  rfl

@[simp]
theorem choices_cons {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source}
    {typings : List (DisplayedRewriteTyping source)}
    (profile : ContextualModalProfile.Profile typing)
    (rest : Vertex typings) :
    choices (.cons profile rest) =
      ContextualModalProfile.choices profile :: choices rest :=
  rfl

/-- The wire has exactly one row per selected occurrence. -/
@[simp]
theorem length_choices {source : ValidatedLanguageDef}
    {typings : List (DisplayedRewriteTyping source)}
    (vertex : Vertex typings) :
    vertex.choices.length = typings.length := by
  induction vertex with
  | nil => rfl
  | cons profile rest inductionHypothesis =>
      simp [choices, inductionHypothesis]

/-- Ordered composition of vertices follows ordered demand composition. -/
def append {source : ValidatedLanguageDef}
    {first second : List (DisplayedRewriteTyping source)} :
    Vertex first → Vertex second → Vertex (first ++ second)
  | .nil, later => later
  | .cons profile rest, later => .cons profile (append rest later)

@[simp]
theorem choices_append {source : ValidatedLanguageDef}
    {first second : List (DisplayedRewriteTyping source)}
    (earlier : Vertex first) (later : Vertex second) :
    choices (earlier.append later) = choices earlier ++ choices later := by
  induction earlier with
  | nil => rfl
  | cons profile rest inductionHypothesis =>
      simp [append, choices, inductionHypothesis]

/-- Uniform endpoint vertex. -/
def constant {source : ValidatedLanguageDef}
    (code : CarrierUniverseSignature.Code) :
    (typings : List (DisplayedRewriteTyping source)) → Vertex typings
  | [] => .nil
  | typing :: typings =>
      .cons (ContextualModalProfile.constant typing code)
        (constant code typings)

/-- Structural reindexing transports occurrence typings and every aligned
local choice together. -/
noncomputable def map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    {typings : List (DisplayedRewriteTyping source)} →
      Vertex typings →
      Vertex (typings.map (DisplayedRewriteTyping.map morphism))
  | [], .nil => .nil
  | _ :: _, .cons profile rest =>
      .cons (ContextualModalProfile.map morphism profile)
        (map morphism rest)

/-- Reindexing does not change, reorder, merge, or delete any profile code. -/
theorem choices_map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {typings : List (DisplayedRewriteTyping source)}
    (vertex : Vertex typings) :
    choices (vertex.map morphism) = choices vertex := by
  induction vertex with
  | nil => rfl
  | cons profile rest inductionHypothesis =>
      simp [map, choices, ContextualModalProfile.choices_map,
        inductionHypothesis]

/-- Appending vertices is associative on the canonical assignment wire. -/
theorem choices_append_assoc {source : ValidatedLanguageDef}
    {first second third : List (DisplayedRewriteTyping source)}
    (a : Vertex first) (b : Vertex second) (c : Vertex third) :
    choices ((a.append b).append c) =
      choices (a.append (b.append c)) := by
  simp [choices_append, List.append_assoc]

/-- The nested choice wire is injective for one fixed typing index. -/
theorem choices_injective {source : ValidatedLanguageDef}
    {typings : List (DisplayedRewriteTyping source)} :
    Function.Injective (@choices source typings) := by
  intro first second equality
  induction first with
  | nil =>
      cases second
      rfl
  | @cons typing typings profile rest inductionHypothesis =>
      cases second with
      | cons nextProfile nextRest =>
          have rows := List.cons.inj equality
          have profileEquality :
              profile = nextProfile :=
            ContextualModalProfile.choices_injective rows.1
          subst nextProfile
          have restEquality : rest = nextRest :=
            inductionHypothesis rows.2
          subst nextRest
          rfl

/-! ## Finite hypercube structure -/

/-- Empty assignments carry no hidden choice. -/
def nilEquiv {source : ValidatedLanguageDef} :
    Vertex ([] : List (DisplayedRewriteTyping source)) ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => .nil
  left_inv := by intro vertex; cases vertex; rfl
  right_inv := by intro value; cases value; rfl

/-- A nonempty vertex is exactly its head local profile times its tail
vertex. -/
def consEquiv {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source)
    (typings : List (DisplayedRewriteTyping source)) :
    Vertex (typing :: typings) ≃
      ContextualModalProfile.Profile typing × Vertex typings where
  toFun
    | .cons profile rest => (profile, rest)
  invFun := fun pair => .cons pair.1 pair.2
  left_inv := by intro vertex; cases vertex; rfl
  right_inv := by intro pair; cases pair; rfl

  noncomputable instance instFintype {source : ValidatedLanguageDef} :
    (typings : List (DisplayedRewriteTyping source)) → Fintype (Vertex typings)
  | [] => Fintype.ofEquiv Unit nilEquiv.symm
  | typing :: typings => by
      letI := instFintype typings
      exact Fintype.ofEquiv
        (ContextualModalProfile.Profile typing × Vertex typings)
        (consEquiv typing typings).symm

/-- The total vertex count is the product of the exact local cube sizes. -/
theorem card_vertex {source : ValidatedLanguageDef} :
    ∀ typings : List (DisplayedRewriteTyping source),
      Fintype.card (Vertex typings) =
        (typings.map fun typing =>
          2 ^ ((DisplayedContextProfile.bindings typing).length + 1)).prod
  | [] => by
      rw [Fintype.card_congr nilEquiv]
      rfl
  | typing :: typings => by
      rw [Fintype.card_congr (consEquiv typing typings),
        Fintype.card_prod, ContextualModalProfile.card_profile,
        card_vertex typings]
      rfl

/-! ## Positive and negative controls -/

/-- A singleton occurrence still exposes the two distinct all-star/all-box
endpoint vertices. -/
theorem singleton_allStar_ne_allBox {source : ValidatedLanguageDef}
    (typing : DisplayedRewriteTyping source) :
    constant .star [typing] ≠ constant .box [typing] := by
  intro equality
  have wires := congrArg choices equality
  simp [constant, choices, ContextualModalProfile.constant,
    ContextualModalProfile.choices] at wires

/-- A nonempty demand cannot be configured by an empty assignment wire. -/
theorem nonempty_vertex_has_nonempty_wire {source : ValidatedLanguageDef}
    {typing : DisplayedRewriteTyping source}
    {typings : List (DisplayedRewriteTyping source)}
    (vertex : Vertex (typing :: typings)) :
    vertex.choices ≠ [] := by
  cases vertex
  simp [choices]

#print axioms choices_append
#print axioms choices_map
#print axioms choices_append_assoc
#print axioms choices_injective
#print axioms card_vertex
#print axioms singleton_allStar_ne_allBox
#print axioms nonempty_vertex_has_nonempty_wire

end Vertex

end SelectedNativeTypeVertex

end Mettapedia.OSLF.Framework
