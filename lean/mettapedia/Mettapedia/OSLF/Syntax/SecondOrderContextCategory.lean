import Mettapedia.OSLF.Syntax.BindingSignature
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Second-order contexts and metavariable instantiation

A context of metavariables records each variable's dependency sorts and
result sort. An arrow interprets the metavariables of its target context by
terms over its source context. Composition is the already proved
capture-avoiding instantiation into another extension. A term with a fixed
dependency context is represented by an arrow to the one-metavariable
context of that arity.

This is the second-order syntactic context category. Authored equations,
operational firing evidence, and categorical closed structure require
further relative constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding

variable (S : Signature)

/-- A finite list of metavariable arities, each with its own local
dependency context and result sort. -/
structure Object where
  arities : List (MetaArity S)

/-- An arrow interprets each target metavariable as a term over the source
metavariables in the dependency context declared by that target. -/
abbrev Assignment (source target : Object S) : Type :=
  (i : Fin target.arities.length) →
    Term (withMetas S source.arities)
      (target.arities.get i).1 (target.arities.get i).2

instance : Category (Object S) where
  Hom := Assignment S
  id context := metaVar (M := context.arities)
  comp first second := fun i => instInto first (second i)
  id_comp first := by
    funext i
    exact instInto_metaVar_id (first i)
  comp_id first := by
    funext i
    exact instInto_metaVar first i
  assoc first second third := by
    funext i
    exact (instInto_instInto second first (third i)).symm

/-- A one-metavariable context represents terms with exactly the stated
dependency list and result sort. -/
def single (dependencies : Ctx S) (result : S.Srt) : Object S :=
  ⟨[(dependencies, result)]⟩

/-- The represented-term equivalence is literal: an interpretation of the
single target metavariable is a term in its dependency context. -/
def termsRepresented (source : Object S)
    (dependencies : Ctx S) (result : S.Srt) :
    (source ⟶ single S dependencies result) ≃
      Term (withMetas S source.arities) dependencies result where
  toFun assignment := assignment ⟨0, by simp [single]⟩
  invFun term := fun i =>
    match i with
    | ⟨0, _⟩ => term
    | ⟨n + 1, impossible⟩ => by
        simp [single] at impossible
  left_inv assignment := by
    funext i
    rcases i with ⟨n, bound⟩
    change n < 1 at bound
    have zero : n = 0 := by omega
    subst zero
    rfl
  right_inv _ := rfl

/-- Composition acts on represented terms by the established
metavariable-instantiation operation, including terms beneath binders. -/
theorem represented_comp {source middle : Object S}
    (dependencies : Ctx S) (result : S.Srt)
    (first : source ⟶ middle)
    (second : middle ⟶ single S dependencies result) :
    termsRepresented S source dependencies result (first ≫ second) =
      instInto first
        (termsRepresented S middle dependencies result second) := rfl

/-- Two independently declared nullary metavariables of the same sort are
different syntactic generators before any authored equation identifies them. -/
theorem distinct_nullary_generators (sort : S.Srt) :
    (metaVar (M := [([], sort), ([], sort)]) (⟨0, by decide⟩ : Fin 2) :
      Term (withMetas S [([], sort), ([], sort)]) [] sort) ≠
    metaVar (M := [([], sort), ([], sort)])
      (⟨1, by decide⟩ : Fin 2) := by
  intro same
  cases same

/-- Juxtaposition of finite metavariable contexts. -/
def productObject (left right : Object S) : Object S :=
  ⟨left.arities ++ right.arities⟩

/-- A context-indexed assignment, with every component's dependency list
and result sort taken from that exact position. -/
private abbrev Assign (source : Object S) (arities : List (MetaArity S)) : Type :=
  (i : Fin arities.length) →
    Term (withMetas S source.arities) (arities.get i).1 (arities.get i).2

/-- Dependent assignments split over concatenation. The proof recurses on
the first context, so it never identifies two equal-arity metavariables. -/
private def appendAssignments (source : Object S) :
    (left right : List (MetaArity S)) →
      Assign S source (left ++ right) ≃
        Assign S source left × Assign S source right
  | [], right => {
      toFun := fun assignment => (fun i => Fin.elim0 i, assignment)
      invFun := fun components => components.2
      left_inv := by intro assignment; rfl
      right_inv := by
        intro components
        apply Prod.ext
        · funext i
          exact Fin.elim0 i
        · rfl }
  | _ :: rest, right => by
      let shorter := appendAssignments source rest right
      refine {
        toFun := fun assignment =>
          let tail := shorter (fun i => assignment i.succ)
          (fun i => Fin.cases (assignment ⟨0, by simp⟩) tail.1 i, tail.2)
        invFun := fun components =>
          let tail := shorter.symm (fun i => components.1 i.succ, components.2)
          fun i => Fin.cases (components.1 ⟨0, by simp⟩) tail i
        left_inv := ?_
        right_inv := ?_ }
      · intro assignment
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · have roundTrip := shorter.symm_apply_apply
            (fun i => assignment i.succ)
          exact congrFun roundTrip i
      · intro components
        apply Prod.ext
        · funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · rfl
          · have roundTrip := shorter.apply_symm_apply
              (fun i => components.1 i.succ, components.2)
            exact congrFun (congrArg Prod.fst roundTrip) i
        · have roundTrip := shorter.apply_symm_apply
            (fun i => components.1 i.succ, components.2)
          change (shorter (shorter.symm
            (fun i => components.1 i.succ, components.2))).2 = components.2
          exact congrArg Prod.snd roundTrip

/-- Any pointwise relation on contextual terms is preserved when two
assignment vectors are joined. The relation need not be decidable or a
congruence; the proof follows the actual declaration positions. -/
private theorem appendAssignments_symm_pointwise (source : Object S)
    (R : ∀ (Γ : Ctx S) (sort : S.Srt),
      Term (withMetas S source.arities) Γ sort →
      Term (withMetas S source.arities) Γ sort → Prop) :
    ∀ (left right : List (MetaArity S))
      (first first' : Assign S source left)
      (second second' : Assign S source right),
      (∀ index, R _ _ (first index) (first' index)) →
      (∀ index, R _ _ (second index) (second' index)) →
      ∀ index,
        R _ _
          ((appendAssignments S source left right).symm
            (first, second) index)
          ((appendAssignments S source left right).symm
            (first', second') index)
  | [], right, first, first', second, second', _left, rightRelated, index =>
      rightRelated index
  | _ :: rest, right, first, first', second, second', leftRelated,
      rightRelated, index => by
      refine Fin.cases (leftRelated ⟨0, by simp⟩) (fun old => ?_) index
      exact appendAssignments_symm_pointwise source R rest right
        (fun i => first i.succ) (fun i => first' i.succ)
        second second' (fun i => leftRelated i.succ)
        rightRelated old

/-- Splitting a dependent assignment commutes with interpreting all of its
terms along a second-order substitution. -/
private theorem appendAssignments_natural
    {source' source : Object S} (substitution : source' ⟶ source) :
    ∀ (left right : List (MetaArity S))
      (assignment : Assign S source (left ++ right)),
      appendAssignments S source' left right
        (fun i => instInto substitution (assignment i)) =
      (fun i => instInto substitution
          ((appendAssignments S source left right assignment).1 i),
        fun i => instInto substitution
          ((appendAssignments S source left right assignment).2 i))
  | [], _, assignment => by
      apply Prod.ext
      · funext i
        exact Fin.elim0 i
      · rfl
  | _ :: rest, right, assignment => by
      have ih := appendAssignments_natural substitution rest right
        (fun i => assignment i.succ)
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · exact congrFun (congrArg Prod.fst ih) i
      · change
          ((appendAssignments S source' rest right)
            (fun i => instInto substitution (assignment i.succ))).2 =
          (fun i => instInto substitution
            (((appendAssignments S source rest right)
              (fun i => assignment i.succ)).2 i))
        exact congrArg Prod.snd ih

/-- Assignments into a juxtaposed second-order context are precisely
pairs of assignments into its two factors. -/
def productHomEquiv (source left right : Object S) :
    (source ⟶ productObject S left right) ≃
      (source ⟶ left) × (source ⟶ right) :=
  appendAssignments S source left.arities right.arities

/-- The product comparison is natural in its source context. This is the
actual universal-property compatibility, beyond a pointwise bijection of
assignment sets. -/
theorem productHomEquiv_natural {source' source left right : Object S}
    (substitution : source' ⟶ source)
    (assignment : source ⟶ productObject S left right) :
    productHomEquiv S source' left right (substitution ≫ assignment) =
      (substitution ≫ (productHomEquiv S source left right assignment).1,
        substitution ≫ (productHomEquiv S source left right assignment).2) :=
  appendAssignments_natural S substitution left.arities right.arities assignment

/-- The two product projections are determined by splitting the identity
assignment of the joined metavariable context. -/
def firstProjection (left right : Object S) :
    productObject S left right ⟶ left :=
  (productHomEquiv S (productObject S left right) left right
    (𝟙 (productObject S left right))).1

def secondProjection (left right : Object S) :
    productObject S left right ⟶ right :=
  (productHomEquiv S (productObject S left right) left right
    (𝟙 (productObject S left right))).2

/-- A pair of interpretations extends uniquely to the joined context. -/
def pair (source left right : Object S)
    (first : source ⟶ left) (second : source ⟶ right) :
    source ⟶ productObject S left right :=
  (productHomEquiv S source left right).symm (first, second)

/-- Joining two pointwise-related assignments preserves their relation at
every position of the concatenated target context. -/
theorem pair_pointwise (source left right : Object S)
    (R : ∀ (Γ : Ctx S) (sort : S.Srt),
      Term (withMetas S source.arities) Γ sort →
      Term (withMetas S source.arities) Γ sort → Prop)
    (first first' : source ⟶ left)
    (second second' : source ⟶ right)
    (leftRelated : ∀ index, R _ _ (first index) (first' index))
    (rightRelated : ∀ index, R _ _ (second index) (second' index)) :
    ∀ index, R _ _
      (pair S source left right first second index)
      (pair S source left right first' second' index) :=
  appendAssignments_symm_pointwise S source R left.arities right.arities
    first first' second second' leftRelated rightRelated

/-- Reading the first component of a paired assignment recovers it exactly. -/
theorem pair_first (source left right : Object S)
    (first : source ⟶ left) (second : source ⟶ right) :
    pair S source left right first second ≫
      firstProjection S left right = first := by
  have natural := productHomEquiv_natural S
    (pair S source left right first second)
    (𝟙 (productObject S left right))
  simp only [Category.comp_id] at natural
  have firstEq := congrArg Prod.fst natural
  have readPair := congrArg Prod.fst
    ((productHomEquiv S source left right).apply_symm_apply (first, second))
  change ((productHomEquiv S source left right)
    (pair S source left right first second)).1 = first at readPair
  rw [readPair] at firstEq
  exact firstEq.symm

/-- Reading the second component of a paired assignment recovers it exactly. -/
theorem pair_second (source left right : Object S)
    (first : source ⟶ left) (second : source ⟶ right) :
    pair S source left right first second ≫
      secondProjection S left right = second := by
  have natural := productHomEquiv_natural S
    (pair S source left right first second)
    (𝟙 (productObject S left right))
  simp only [Category.comp_id] at natural
  have secondEq := congrArg Prod.snd natural
  have readPair := congrArg Prod.snd
    ((productHomEquiv S source left right).apply_symm_apply (first, second))
  change ((productHomEquiv S source left right)
    (pair S source left right first second)).2 = second at readPair
  rw [readPair] at secondEq
  exact secondEq.symm

/-- Juxtaposition is a categorical binary product of second-order
contexts, with projections and universal lift given by authored
metavariable substitution. -/
def productIsLimit (left right : Object S) :
    IsLimit (BinaryFan.mk
      (firstProjection S left right)
      (secondProjection S left right)) := by
  refine BinaryFan.isLimitMk
    (fun cone => pair S cone.pt left right cone.fst cone.snd)
    ?_ ?_ ?_
  · intro cone
    have natural := productHomEquiv_natural S
      (pair S cone.pt left right cone.fst cone.snd)
      (𝟙 (productObject S left right))
    simp only [Category.comp_id] at natural
    have firstEq := congrArg Prod.fst natural
    have readPair := congrArg Prod.fst
      ((productHomEquiv S cone.pt left right).apply_symm_apply
        (cone.fst, cone.snd))
    change ((productHomEquiv S cone.pt left right)
      (pair S cone.pt left right cone.fst cone.snd)).1 = cone.fst
      at readPair
    rw [readPair] at firstEq
    exact firstEq.symm
  · intro cone
    have natural := productHomEquiv_natural S
      (pair S cone.pt left right cone.fst cone.snd)
      (𝟙 (productObject S left right))
    simp only [Category.comp_id] at natural
    have secondEq := congrArg Prod.snd natural
    have readPair := congrArg Prod.snd
      ((productHomEquiv S cone.pt left right).apply_symm_apply
        (cone.fst, cone.snd))
    change ((productHomEquiv S cone.pt left right)
      (pair S cone.pt left right cone.fst cone.snd)).2 = cone.snd
      at readPair
    rw [readPair] at secondEq
    exact secondEq.symm
  · intro cone candidate firstEq secondEq
    apply (productHomEquiv S cone.pt left right).injective
    have natural := productHomEquiv_natural S candidate
      (𝟙 (productObject S left right))
    simp only [Category.comp_id] at natural
    change productHomEquiv S cone.pt left right candidate =
      (candidate ≫ firstProjection S left right,
        candidate ≫ secondProjection S left right) at natural
    rw [natural, firstEq, secondEq]
    exact (productHomEquiv S cone.pt left right).apply_symm_apply _ |>.symm

/-- The empty metavariable context is terminal: it asks for no
interpretations. -/
def empty : Object S := ⟨[]⟩

def emptyIsTerminal : IsTerminal (empty S) :=
  IsTerminal.ofUniqueHom
    (fun _ index => Fin.elim0 index)
    (fun _ morphism => by funext index; exact Fin.elim0 index)

instance : HasTerminal (Object S) :=
  (emptyIsTerminal S).hasTerminal

instance hasLimitPair (left right : Object S) :
    HasLimit (Limits.pair left right) :=
  ⟨⟨BinaryFan.mk
    (firstProjection S left right)
    (secondProjection S left right),
    productIsLimit S left right⟩⟩

instance : HasBinaryProducts (Object S) :=
  hasBinaryProducts_of_hasLimit_pair (Object S)

instance : HasFiniteProducts (Object S) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

#print axioms termsRepresented
#print axioms represented_comp
#print axioms distinct_nullary_generators
#print axioms productHomEquiv
#print axioms productHomEquiv_natural
#print axioms productIsLimit
#print axioms emptyIsTerminal

end Mettapedia.OSLF.Binding.SecondOrderContext
