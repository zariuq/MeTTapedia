import Mettapedia.OSLF.Framework.GeneratedScopeRho
import Mettapedia.OSLF.Framework.SourceGenerator

/-!
# The two generated scopes, compared

The same rho name scope is now built twice in this tree.  `GeneratedScopeRho`
builds it as a least fixed point of a hand-written transformer, with membership
decided by descent; `SourceGenerator` writes it as a formula of the logic and
reads it by the semantics.  Two constructions of one object that are never
related are the kind of duplication that silently diverges, so here is the
relation, stated in both frames and in the honest direction in each.

**In the ambient powerset the formula denotes the atoms-only layer, exactly.**
The cut presents each part of a composition as a one-element collection, and no
collection is an application, so the formula's recursive disjunct is
unreachable there.  What is left is the quote of a composition of two parts each
accepted by its own predicate — the hand-written transformer with the coercion
removed.  This is an equality, not an inclusion.

**In the frame of a generated logic the formula contains the whole scope**, the
coercion included, as soon as the presentation identifies a one-element
composition with its element.  That hypothesis is asked for only at the names
the scope actually contains, so a presentation can discharge it by induction
rather than by fiat.

**What is not claimed.**  The converse of the second statement is the membership
question for equation *classes*, which `GeneratedScopeRho` explicitly declines:
its descent decides membership for representatives, and modulo the reflection
equation a name may be rewritten to a term mentioning it, so the size argument
that makes the descent terminate is unavailable there.  Nothing here supplies
it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ScopeComparison

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.FormulaFixpoint
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GeneratedScopeRho
open Mettapedia.OSLF.Framework.GeneratedScope (quote par)
open Mettapedia.OSLF.Framework.SourceGenerator

/-- A part, as the cut presents one: a composition of a single element. -/
def part (element : Pattern) : Pattern := .collection .hashBag [element] none

/-- The atom family a pair of part predicates induces.  It accepts a part
exactly when the element inside it satisfies the corresponding predicate, which
is how a predicate on processes becomes a predicate on the cut's parts. -/
def partAtoms (atomLeft atomRight : Pred) : AtomSem :=
  fun name term =>
    (name = "left" ∧ ∃ element, term = part element ∧ atomLeft element) ∨
    (name = "right" ∧ ∃ element, term = part element ∧ atomRight element)

/-- The scope formula at those two atom names. -/
abbrev scopeFormula : OSLFFormula := rhoScope "left" "right"

/-- **The atoms-only layer** of the hand-written scope: the quote of a
composition of two parts each accepted by its own predicate, with the coercion
removed. -/
def atomicLayer (atomLeft atomRight : Pred) : Pred :=
  fun name => ∃ left right,
    name = quote (par left right) ∧ atomLeft left ∧ atomRight right

/-- The layer is inside the scope, since its parts are admitted atomically. -/
theorem atomicLayer_le_generatedScope (atomLeft atomRight : Pred) (name : Pattern)
    (member : atomicLayer atomLeft atomRight name) :
    generatedScope atomLeft atomRight name := by
  obtain ⟨left, right, shape, leftAtom, rightAtom⟩ := member
  rw [shape]
  exact mem_of_atoms leftAtom rightAtom

/-! ## The ambient reading -/

/-- **In the ambient powerset the formula denotes the atoms-only layer.**  The
forward direction is the candidate argument: the layer is a candidate the body
does not leave, because the recursive disjunct asks a one-element collection to
be an application.  The converse is one unfolding. -/
theorem sem_scopeFormula_iff_atomicLayer
    (R : Pattern → Pattern → Prop) (atomLeft atomRight : Pred) (term : Pattern) :
    sem R (partAtoms atomLeft atomRight) scopeFormula term ↔
      atomicLayer atomLeft atomRight term := by
  constructor
  · intro holds
    refine holds (atomicLayer atomLeft atomRight) trivial ?_
    rintro t ⟨inner, shape, leftParts, rightParts, split, leftHolds, rightHolds⟩
    obtain ⟨left, leftShape, leftAtom⟩ :
        ∃ element, (.collection .hashBag leftParts none : Pattern) = part element ∧
          atomLeft element := by
      rcases leftHolds with (⟨-, found⟩ | ⟨wrongName, -⟩) | ⟨code, wrongShape, -⟩
      · exact found
      · exact absurd wrongName (by decide)
      · exact Pattern.noConfusion wrongShape
    obtain ⟨right, rightShape, rightAtom⟩ :
        ∃ element, (.collection .hashBag rightParts none : Pattern) = part element ∧
          atomRight element := by
      rcases rightHolds with (⟨wrongName, -⟩ | ⟨-, found⟩) | ⟨code, wrongShape, -⟩
      · exact absurd wrongName (by decide)
      · exact found
      · exact Pattern.noConfusion wrongShape
    have leftEq : leftParts = [left] := by simpa [part] using leftShape
    have rightEq : rightParts = [right] := by simpa [part] using rightShape
    subst leftEq
    subst rightEq
    exact ⟨left, right, by rw [shape, split]; rfl, leftAtom, rightAtom⟩
  · rintro ⟨left, right, shape, leftAtom, rightAtom⟩
    refine (sem_sourceScope_iff R (partAtoms atomLeft atomRight)
      "NQuote" "PDrop" "left" "right" term).mpr ?_
    exact ⟨par left right, shape, [left], [right], rfl,
      Or.inl (Or.inl ⟨rfl, left, rfl, leftAtom⟩),
      Or.inl (Or.inr ⟨rfl, right, rfl, rightAtom⟩)⟩

/-- **So the ambient reading stops one layer down**, and the obstruction is
named: a part is a one-element composition and the drop former matches no
composition. -/
theorem sem_scopeFormula_le_generatedScope
    (R : Pattern → Pattern → Prop) (atomLeft atomRight : Pred) (term : Pattern)
    (holds : sem R (partAtoms atomLeft atomRight) scopeFormula term) :
    generatedScope atomLeft atomRight term :=
  atomicLayer_le_generatedScope atomLeft atomRight term
    ((sem_scopeFormula_iff_atomicLayer R atomLeft atomRight term).mp holds)

/-! ## The containment, at the generality the argument has

The coercion is taken through an identification of a one-element composition
with its element, and that identification belongs to whatever equivalence the
frame is built from.  So the containment is a statement about a setoid, and the
readings this tree uses are instances of it. -/

/-- **The whole scope is inside the formula's reading in any frame a setoid
selects**, as soon as that setoid identifies a one-element composition of a drop
with the drop.  The identification is asked for only at the names the scope
contains, so a presentation discharges it by induction on its own grammar
rather than for every pattern. -/
theorem generatedScope_le_semEnv_setoid
    (equations : Setoid Pattern) (R : Pattern → Pattern → Prop) (I : AtomSem)
    (frameClosed : FrameClosed R (setoidFrame equations) I)
    (atomLeft atomRight : Pred)
    (leftAdmits : ∀ element, atomLeft element → I "left" (part element))
    (rightAdmits : ∀ element, atomRight element → I "right" (part element))
    (singletonDrop : ∀ name, generatedScope atomLeft atomRight name →
      equations.r (part (drop name)) (drop name))
    (name : Pattern) (member : generatedScope atomLeft atomRight name) :
    semEnv R (setoidFrame equations) I ScopeEnv.empty scopeFormula name := by
  have paired : ∀ name, generatedScope atomLeft atomRight name →
      (generatedScope atomLeft atomRight name ∧
        semEnv R (setoidFrame equations) I ScopeEnv.empty scopeFormula name) := by
    refine scope_induction (invariant := fun name =>
      generatedScope atomLeft atomRight name ∧
        semEnv R (setoidFrame equations) I ScopeEnv.empty scopeFormula name) ?_
    intro left right leftAdmitted rightAdmitted
    have weaken : ∀ (atom : Pred) (partTerm : Pattern),
        PartAdmitted atom
            (fun t => generatedScope atomLeft atomRight t ∧
              semEnv R (setoidFrame equations) I ScopeEnv.empty scopeFormula t)
            partTerm →
          PartAdmitted atom (generatedScope atomLeft atomRight) partTerm := by
      rintro atom partTerm (atomic | ⟨inner, shape, ⟨inMember, -⟩⟩)
      · exact Or.inl atomic
      · exact Or.inr ⟨inner, shape, inMember⟩
    refine ⟨mem_of_parts (weaken atomLeft left leftAdmitted)
      (weaken atomRight right rightAdmitted), ?_⟩
    rw [sourceScope_unfold_setoid equations R I frameClosed ScopeEnv.empty
      (fun _ _ _ _ => Iff.rfl) "NQuote" "PDrop" "left" "right"]
    refine (setoidFrame equations).le_close _ _ ⟨par left right, rfl, ?_⟩
    refine semEnv_cut_of_split_setoid equations R I ScopeEnv.empty
      .hashBag _ _ [left] [right] ?_ ?_
    · rcases leftAdmitted with atomic | ⟨inner, shape, ⟨inMember, inFormula⟩⟩
      · exact Or.inl (leftAdmits left atomic)
      · refine Or.inr ?_
        rw [shape]
        exact semEnv_headed_of_equiv_setoid equations R I ScopeEnv.empty "PDrop" _
          (singletonDrop inner inMember) inFormula
    · rcases rightAdmitted with atomic | ⟨inner, shape, ⟨inMember, inFormula⟩⟩
      · exact Or.inl (rightAdmits right atomic)
      · refine Or.inr ?_
        rw [shape]
        exact semEnv_headed_of_equiv_setoid equations R I ScopeEnv.empty "PDrop" _
          (singletonDrop inner inMember) inFormula
  exact (paired name member).2

/-! ## The reading in a generated logic -/

section Equational

variable (relEnv : RelationEnv) (lang : LanguageDef)

/-- The part atoms, admitted to the generated logic by saturation. -/
def equationPartAtoms (atomLeft atomRight : Pred) :
    EquationAtomSemUsing relEnv lang :=
  saturateAtomSemUsing relEnv lang (partAtoms atomLeft atomRight)

theorem equationPartAtoms_left {atomLeft atomRight : Pred} {element : Pattern}
    (holds : atomLeft element) :
    (equationPartAtoms relEnv lang atomLeft atomRight "left").1 (part element) :=
  ⟨part element, (langGSLTUsing relEnv lang).equations.iseqv.refl _,
    Or.inl ⟨rfl, element, rfl, holds⟩⟩

theorem equationPartAtoms_right {atomLeft atomRight : Pred} {element : Pattern}
    (holds : atomRight element) :
    (equationPartAtoms relEnv lang atomLeft atomRight "right").1 (part element) :=
  ⟨part element, (langGSLTUsing relEnv lang).equations.iseqv.refl _,
    Or.inr ⟨rfl, element, rfl, holds⟩⟩

/-- **The whole scope is inside the formula's reading in a generated logic.**
The coercion is taken through the presentation's identification of a one-element
composition with its element, and that identification is asked for only at the
names the scope contains, so a presentation discharges it by induction on its
own grammar rather than for every pattern. -/
theorem generatedScope_le_langSemUsing (atomLeft atomRight : Pred)
    (singletonDrop : ∀ name, generatedScope atomLeft atomRight name →
      (langGSLTUsing relEnv lang).Equiv (part (drop name)) (drop name))
    (name : Pattern) (member : generatedScope atomLeft atomRight name) :
    langSemUsing relEnv lang (equationPartAtoms relEnv lang atomLeft atomRight)
      scopeFormula name :=
  generatedScope_le_semEnv_setoid (langGSLTUsing relEnv lang).equations _ _
    (frameClosed_equationFrameUsing relEnv lang
      (equationPartAtoms relEnv lang atomLeft atomRight))
    atomLeft atomRight
    (fun _ holds => equationPartAtoms_left relEnv lang holds)
    (fun _ holds => equationPartAtoms_right relEnv lang holds)
    singletonDrop name member

end Equational

/-! ## A specimen, positive and negative

Two nullary processes for the parts.  The base case is in both readings; the
coerced name is in the hand-written scope and outside the ambient reading of the
formula, which is where the two part and why the frame is the thing that
matters. -/

namespace Specimen

def alpha : Pattern := .apply "PAlpha" []
def beta : Pattern := .apply "PBeta" []

def isAlpha : Pred := fun term => term = alpha
def isBeta : Pred := fun term => term = beta

/-- The base name: the quote of the composition of the two parts. -/
def baseName : Pattern := quote (par alpha beta)

/-- The coerced name: the quote of a composition dropping the base name. -/
def coercedName : Pattern := quote (par (drop baseName) beta)

/-- **Positive**: the base name is in the atoms-only layer. -/
theorem baseName_in_layer : atomicLayer isAlpha isBeta baseName :=
  ⟨alpha, beta, rfl, rfl, rfl⟩

/-- **Positive**: and therefore in the formula's ambient reading. -/
theorem baseName_sem (R : Pattern → Pattern → Prop) :
    sem R (partAtoms isAlpha isBeta) scopeFormula baseName :=
  (sem_scopeFormula_iff_atomicLayer R isAlpha isBeta baseName).mpr baseName_in_layer

/-- **Positive**: the coerced name is in the hand-written scope. -/
theorem coercedName_in_generatedScope :
    generatedScope isAlpha isBeta coercedName :=
  mem_of_drop_left (mem_of_atoms rfl rfl) rfl

/-- **Negative**: and it is not in the formula's ambient reading.  So the two
constructions part exactly at the coercion, and nowhere else. -/
theorem coercedName_not_sem (R : Pattern → Pattern → Prop) :
    ¬ sem R (partAtoms isAlpha isBeta) scopeFormula coercedName := by
  intro holds
  obtain ⟨left, right, shape, leftAtom, -⟩ :=
    (sem_scopeFormula_iff_atomicLayer R isAlpha isBeta coercedName).mp holds
  obtain ⟨leftEq, -⟩ := quote_par_injective shape
  rw [← leftEq] at leftAtom
  simp [isAlpha, alpha, drop] at leftAtom

/-- **The separation.**  One name, in the hand-written scope and outside the
formula's ambient reading; the coercion is the whole difference. -/
theorem constructions_separate (R : Pattern → Pattern → Prop) :
    generatedScope isAlpha isBeta coercedName ∧
      ¬ sem R (partAtoms isAlpha isBeta) scopeFormula coercedName :=
  ⟨coercedName_in_generatedScope, coercedName_not_sem R⟩

end Specimen

end Mettapedia.OSLF.Framework.ScopeComparison
