import Mettapedia.OSLF.Framework.SourceGenerator
import Mettapedia.OSLF.Framework.ScopeComparison
import Mettapedia.OSLF.Framework.SortedEquationFrame
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquationDiscipline
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquations

/-!
# The source's generator on the platform presentation

`SourceGenerator` writes the scope generator of the source material as a formula
of the one formula language and takes its recursive step in the frame of a
generated logic, conditioned on the singleton law of that presentation's
collection carrier.  Here that condition is met — by the platform's own
declarations — and the step is iterated, so the scope is inhabited by a chain of
names each of which codes the previous one rather than by a base case alone.

Two facts do the work and both belong to the presentation.  The parallel carrier
declares a collection algebra that flattens, from which the singleton law is
derived; and the sorting judgement that law is conditioned on is discharged for
the whole chain by induction on the grammar, not term by term.

The separation is stated as well as the construction.  In the ambient powerset
the same formula, at the same presentation and the same atoms, denotes exactly
its base case: a part is a one-element composition and a composition is not an
application, so the recursive disjunct is unreachable there.  The singleton law
is the only thing that changes hands between the two readings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSourceScope

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.SourceGenerator
open Mettapedia.OSLF.Framework.FormulaFixpoint
open Mettapedia.OSLF.Framework.GeneratedScopeRho
open Mettapedia.OSLF.Framework.GeneratedScope (quote par)
open Mettapedia.OSLF.Framework.SortedEquationFrame
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquations

/-! ## The grammar, used as a grammar

Five introduction rules, each read off one declaration of the presentation.
They are what lets the chain below be sorted by induction rather than by a
separate decision at every level. -/

variable (arities : List Nat)

theorem stopDeclaration_mem : stopDeclaration ∈ (rhoPlatform arities).terms := by
  simp [rhoPlatform]

theorem quoteDeclaration_mem : quoteDeclaration ∈ (rhoPlatform arities).terms := by
  simp [rhoPlatform]

theorem dropDeclaration_mem : dropDeclaration ∈ (rhoPlatform arities).terms := by
  simp [rhoPlatform]

theorem parDeclaration_mem : parDeclaration ∈ (rhoPlatform arities).terms := by
  simp [rhoPlatform]

theorem outDeclaration_mem : outDeclaration ∈ (rhoPlatform arities).terms := by
  simp [rhoPlatform]

/-- The terminated process is a process. -/
theorem stop_hasSort :
    HasSort (rhoPlatform arities) FreeTypeContext.empty []
      (.apply stopDeclaration.label []) "Proc" :=
  HasType.constructor (stopDeclaration_mem arities) (by rintro ⟨_, _, _, shape⟩; simp [stopDeclaration] at shape)
    .nil

/-- A quoted process is a name. -/
theorem quote_hasSort {process : Pattern}
    (typed : HasSort (rhoPlatform arities) FreeTypeContext.empty [] process "Proc") :
    HasSort (rhoPlatform arities) FreeTypeContext.empty []
      (.apply quoteLabel [process]) "Name" :=
  HasType.constructor (quoteDeclaration_mem arities)
    (by rintro ⟨_, _, _, shape⟩; simp [quoteDeclaration] at shape)
    (.cons trivial rfl typed .nil)

/-- A dropped name is a process. -/
theorem drop_hasSort {name : Pattern}
    (typed : HasSort (rhoPlatform arities) FreeTypeContext.empty [] name "Name") :
    HasSort (rhoPlatform arities) FreeTypeContext.empty []
      (.apply dropLabel [name]) "Proc" :=
  HasType.constructor (dropDeclaration_mem arities)
    (by rintro ⟨_, _, _, shape⟩; simp [dropDeclaration] at shape)
    (.cons trivial rfl typed .nil)

/-- An output on a name, carrying a process, is a process. -/
theorem out_hasSort {name process : Pattern}
    (nameTyped : HasSort (rhoPlatform arities) FreeTypeContext.empty [] name "Name")
    (processTyped :
      HasSort (rhoPlatform arities) FreeTypeContext.empty [] process "Proc") :
    HasSort (rhoPlatform arities) FreeTypeContext.empty []
      (.apply outLabel [name, process]) "Proc" :=
  HasType.constructor (outDeclaration_mem arities)
    (by rintro ⟨_, _, _, shape⟩; simp [outDeclaration] at shape)
    (.cons trivial rfl nameTyped (.cons trivial rfl processTyped .nil))

/-- **A bag of processes is a parallel composition**, and so is sorted at the
carrier's own category — the judgement every derived collection law carries. -/
theorem bag_sortedParts {elements : List Pattern}
    (typed : ElementsHaveType (rhoPlatform arities) FreeTypeContext.empty []
      elements (.base "Proc")) :
    sortedParts arities elements :=
  ⟨FreeTypeContext.empty, [],
    HasType.collectionConstructor (parDeclaration_mem arities) rfl typed⟩

/-! ## The chain -/

/-- The terminated process. -/
def stop : Pattern := .apply stopDeclaration.label []

/-- An output on the name of the terminated process, carrying it. -/
def output : Pattern := .apply outLabel [.apply quoteLabel [stop], stop]

/-- A part, as the cut presents one: a composition of a single element. -/
def part (term : Pattern) : Pattern := .collection .hashBag [term] none

/-- **The chain of names.**  The first codes the composition of the two parts;
each later one codes the composition of a drop of its predecessor with the
right-hand part.  This is the shape the source's generator describes. -/
def chain : Nat → Pattern
  | 0 => .apply quoteLabel [.collection .hashBag [stop, output] none]
  | step + 1 =>
      .apply quoteLabel
        [.collection .hashBag [.apply dropLabel [chain step], output] none]

theorem stop_sorted :
    HasSort (rhoPlatform arities) FreeTypeContext.empty [] stop "Proc" :=
  stop_hasSort arities

theorem output_sorted :
    HasSort (rhoPlatform arities) FreeTypeContext.empty [] output "Proc" :=
  out_hasSort arities (quote_hasSort arities (stop_sorted arities))
    (stop_sorted arities)

/-- **Every name of the chain is a name**, by induction on the grammar. -/
theorem chain_sorted :
    ∀ step, HasSort (rhoPlatform arities) FreeTypeContext.empty []
      (chain step) "Name"
  | 0 =>
      quote_hasSort arities
        (HasType.collectionConstructor (parDeclaration_mem arities) rfl
          (.cons (stop_sorted arities) (.cons (output_sorted arities) (.nil _ _))))
  | step + 1 =>
      quote_hasSort arities
        (HasType.collectionConstructor (parDeclaration_mem arities) rfl
          (.cons (drop_hasSort arities (chain_sorted step))
            (.cons (output_sorted arities) (.nil _ _))))

/-- **And the one-element composition of each drop is sorted**, which is the
hypothesis the derived singleton law carries. -/
theorem drop_chain_sortedParts (step : Nat) :
    sortedParts arities [.apply dropLabel [chain step]] :=
  bag_sortedParts arities
    (.cons (drop_hasSort arities (chain_sorted arities step)) (.nil _ _))

/-! ## The atoms, and the scope -/

/-- The presentation, at the one arity the chain uses. -/
abbrev platform : LanguageDef := rhoPlatform [2]

/-- The two part predicates: "is the terminated process, as a part" and "is the
output, as a part".  A part is a one-element composition, because that is how
the cut presents one. -/
def rawAtoms : AtomSem := fun name term =>
  (name = "Stopped" ∧ term = part stop) ∨ (name = "Emitting" ∧ term = part output)

/-- The source's generator, at this presentation's reflection formers and these
two part predicates. -/
abbrev scope : OSLFFormula := sourceScope quoteLabel dropLabel "Stopped" "Emitting"

/-! ## In the ambient powerset the recursion is inert -/

section Ambient

variable (R : Pattern → Pattern → Prop)

/-- **The base case is in the scope in every frame.** -/
theorem ambient_chain_zero : sem R rawAtoms scope (chain 0) :=
  (sem_sourceScope_iff R rawAtoms quoteLabel dropLabel "Stopped" "Emitting"
      (chain 0)).mpr
    ⟨.collection .hashBag [stop, output] none, rfl,
      [stop], [output], rfl, Or.inl (Or.inl ⟨rfl, rfl⟩), Or.inl (Or.inr ⟨rfl, rfl⟩)⟩

/-- **And it is the only thing in it.**  The recursive disjunct asks a
composition to be an application, which no composition is. -/
theorem ambient_scope_eq {term : Pattern} (holds : sem R rawAtoms scope term) :
    term = chain 0 := by
  refine holds (fun t => t = chain 0) trivial ?_
  rintro t ⟨inner, shape, leftParts, rightParts, split, leftHolds, rightHolds⟩
  have leftEq : leftParts = [stop] := by
    rcases leftHolds with (⟨-, leftAtom⟩ | ⟨wrongName, -⟩) | ⟨code, wrongShape, -⟩
    · simpa [part, stop, output] using leftAtom
    · exact absurd wrongName (by decide)
    · exact Pattern.noConfusion wrongShape
  have rightEq : rightParts = [output] := by
    rcases rightHolds with (⟨wrongName, -⟩ | ⟨-, rightAtom⟩) | ⟨code, wrongShape, -⟩
    · exact absurd wrongName (by decide)
    · simpa [part, stop, output] using rightAtom
    · exact Pattern.noConfusion wrongShape
  subst leftEq
  subst rightEq
  rw [shape, split]
  rfl

/-- **So the second link is not in the ambient scope**, and the obstruction is
the frame's poverty rather than any checker's incompleteness. -/
theorem ambient_chain_one_not : ¬ sem R rawAtoms scope (chain 1) := by
  intro holds
  have equal := ambient_scope_eq R holds
  simp [chain, stop, output] at equal

end Ambient

/-! ## In the generated logic the recursion runs -/

section Equational

variable (relEnv : RelationEnv)

/-- Admitted to the generated logic by saturation over the presentation's own
equations. -/
def atoms : EquationAtomSemUsing relEnv platform :=
  saturateAtomSemUsing relEnv platform rawAtoms

theorem atoms_stopped : (atoms relEnv "Stopped").1 (part stop) :=
  ⟨part stop, (langGSLTUsing relEnv platform).equations.iseqv.refl _,
    Or.inl ⟨rfl, rfl⟩⟩

theorem atoms_emitting : (atoms relEnv "Emitting").1 (part output) :=
  ⟨part output, (langGSLTUsing relEnv platform).equations.iseqv.refl _,
    Or.inr ⟨rfl, rfl⟩⟩

/-- **The singleton law, met at every link of the chain** — the presentation's
own derived law, at a sorting judgement discharged by induction on the
grammar. -/
theorem chain_singleton (step : Nat) :
    (langGSLTUsing relEnv platform).Equiv
      (.collection .hashBag [.apply dropLabel [chain step]] none)
      (.apply dropLabel [chain step]) :=
  platform_singleton [2] (engineBasePremises relEnv) (drop_chain_sortedParts [2] step)

/-- **The whole chain is in the scope**, read in the frame the presentation's
equations select.  Compare `ambient_scope_eq`: the same formula, the same terms,
a strictly larger extension, and the singleton law the only thing that changed
hands. -/
theorem chain_in_scope : ∀ step,
    langSemUsing relEnv platform (atoms relEnv) scope (chain step)
  | 0 => by
      rw [sourceScope_unfold_equational relEnv platform (atoms relEnv)
        quoteLabel dropLabel "Stopped" "Emitting"]
      refine (equationFrameUsing relEnv platform).le_close _ _
        ⟨.collection .hashBag [stop, output] none, rfl, ?_⟩
      exact semEnv_cut_of_split relEnv platform (atoms relEnv) ScopeEnv.empty
        .hashBag _ _ [stop] [output]
        (Or.inl (atoms_stopped relEnv)) (Or.inl (atoms_emitting relEnv))
  | step + 1 =>
      sourceScope_step relEnv platform (atoms relEnv)
        quoteLabel dropLabel "Stopped" "Emitting"
        (chain_singleton relEnv step) (chain_in_scope step) (atoms_emitting relEnv)

/-- **The separation, in one statement.**  One formula, one presentation, one
pair of part predicates: the frame of the generated logic contains the second
link of the chain and the ambient powerset does not. -/
theorem frame_separates (R : Pattern → Pattern → Prop) :
    langSemUsing relEnv platform (atoms relEnv) scope (chain 1) ∧
      ¬ sem R rawAtoms scope (chain 1) :=
  ⟨chain_in_scope relEnv 1, ambient_chain_one_not R⟩

end Equational

/-! ## The hand-written scope, and the condition its comparison carries

`ScopeComparison` relates the two constructions of the rho name scope, and the
relation in the frame of a generated logic carries one condition: the
presentation must identify a one-element composition of a drop with that drop,
at every name the scope contains.  Here that condition is discharged, and the
discharge is an induction on the grammar rather than a decision per name. -/

/-- The left part predicate: the terminated process. -/
def leftPart : Pred := fun term => term = stop

/-- The right part predicate: the output. -/
def rightPart : Pred := fun term => term = output

/-- **Everything in the hand-written scope is a name of the presentation.**  The
induction is the scope's own: an atomic part is a declared process, and a
coerced part is the drop of a name the induction has already placed. -/
theorem generatedScope_hasSort :
    ∀ name, generatedScope leftPart rightPart name →
      HasSort platform FreeTypeContext.empty [] name "Name" := by
  refine scope_induction (invariant := fun name =>
    HasSort platform FreeTypeContext.empty [] name "Name") ?_
  intro left right leftAdmitted rightAdmitted
  have leftProc : HasSort platform FreeTypeContext.empty [] left "Proc" := by
    rcases leftAdmitted with atomic | ⟨inner, shape, innerName⟩
    · rw [atomic]; exact stop_sorted [2]
    · rw [shape]; exact drop_hasSort [2] innerName
  have rightProc : HasSort platform FreeTypeContext.empty [] right "Proc" := by
    rcases rightAdmitted with atomic | ⟨inner, shape, innerName⟩
    · rw [atomic]; exact output_sorted [2]
    · rw [shape]; exact drop_hasSort [2] innerName
  exact quote_hasSort [2]
    (HasType.collectionConstructor (parDeclaration_mem [2]) rfl
      (.cons leftProc (.cons rightProc (.nil _ _))))

/-- **So the comparison's condition is met**, by the presentation's own derived
singleton law at a sorting judgement the induction above supplies. -/
theorem platform_singletonDrop (relEnv : RelationEnv) :
    ∀ name, generatedScope leftPart rightPart name →
      (langGSLTUsing relEnv platform).Equiv
        (Mettapedia.OSLF.Framework.ScopeComparison.part (drop name)) (drop name) :=
  fun name member =>
    platform_singleton [2] (engineBasePremises relEnv)
      (bag_sortedParts [2]
        (.cons (drop_hasSort [2] (generatedScope_hasSort name member)) (.nil _ _)))

/-- **And the whole hand-written scope is inside the formula's reading in the
generated logic**, with no condition left standing.  The two constructions of
the rho name scope are related outright on this presentation: the fixed point
of the hand-written transformer is contained in the extension of the formula,
coercion and all. -/
theorem generatedScope_le_formula (relEnv : RelationEnv) :
    ∀ name, generatedScope leftPart rightPart name →
      langSemUsing relEnv platform
        (Mettapedia.OSLF.Framework.ScopeComparison.equationPartAtoms
          relEnv platform leftPart rightPart)
        Mettapedia.OSLF.Framework.ScopeComparison.scopeFormula name :=
  fun name member =>
    Mettapedia.OSLF.Framework.ScopeComparison.generatedScope_le_langSemUsing
      relEnv platform leftPart rightPart (platform_singletonDrop relEnv) name member

/-- **A witness that the containment is not vacuous**, and that it reaches past
the atoms-only layer: a coerced name is in the hand-written scope. -/
theorem coerced_in_generatedScope :
    generatedScope leftPart rightPart
      (quote (par (drop (quote (par stop output))) output)) :=
  mem_of_drop_left (mem_of_atoms rfl rfl) rfl

/-- And it is therefore in the formula's reading in the generated logic. -/
theorem coerced_in_formula (relEnv : RelationEnv) :
    langSemUsing relEnv platform
      (Mettapedia.OSLF.Framework.ScopeComparison.equationPartAtoms
        relEnv platform leftPart rightPart)
      Mettapedia.OSLF.Framework.ScopeComparison.scopeFormula
      (quote (par (drop (quote (par stop output))) output)) :=
  generatedScope_le_formula relEnv _ coerced_in_generatedScope

/-! ## The same chain, in the frame whose instances read their type contexts

`PlatformEquationDiscipline` records that the permissive equation theory of this
presentation equates every term with a quote, so a bound stated up to those
equations rules nothing out.  The disciplined theory does not, and the chain
lives there too: the derived collection laws are generators of it unchanged, so
the singleton law the recursive step consumes is available without a second
argument. -/

section Sorted

variable (relEnv : RelationEnv)

/-- The same atoms, admitted to the disciplined logic. -/
def sortedAtoms : SortedEquationAtomSemUsing relEnv platform :=
  sortedEquationAtomSemUsing relEnv platform (atoms relEnv)

/-- **The singleton law, in the disciplined theory**, at every link of the
chain.  The derived laws carry their own sorting judgement, so the discipline
leaves them alone. -/
theorem chain_sorted_singleton (step : Nat) :
    (langSortedGSLTUsing relEnv platform).Equiv
      (.collection .hashBag [.apply dropLabel [chain step]] none)
      (.apply dropLabel [chain step]) :=
  sortedDerivedInstance_equivalent
    (DerivedInstance.singleton (parDeclaration_isAlgebra [2]) rfl
      (drop_chain_sortedParts [2] step))

/-- **And the whole chain is in the scope read in the disciplined frame.**  With
`PlatformEquationDiscipline.stop_not_in_sortedScope`, one frame now carries both
halves of the separation: a chain of names inside the scope and a process
outside it. -/
theorem chain_in_sorted_scope : ∀ step,
    langSortedSemUsing relEnv platform (sortedAtoms relEnv) scope (chain step)
  | 0 => by
      show semEnv (langSortedSemanticReducesUsing relEnv platform)
        (setoidFrame (langSortedGSLTUsing relEnv platform).equations)
        (fun atom => (sortedAtoms relEnv atom).1) ScopeEnv.empty scope (chain 0)
      rw [sourceScope_unfold_setoid (langSortedGSLTUsing relEnv platform).equations
        (langSortedSemanticReducesUsing relEnv platform)
        (fun atom => (sortedAtoms relEnv atom).1)
        (frameClosed_sortedEquationFrameUsing relEnv platform (sortedAtoms relEnv))
        ScopeEnv.empty (fun _ _ _ _ => Iff.rfl) quoteLabel dropLabel "Stopped" "Emitting"]
      refine (setoidFrame (langSortedGSLTUsing relEnv platform).equations).le_close _ _
        ⟨.collection .hashBag [stop, output] none, rfl, ?_⟩
      exact semEnv_cut_of_split_setoid (langSortedGSLTUsing relEnv platform).equations
        (langSortedSemanticReducesUsing relEnv platform)
        (fun atom => (sortedAtoms relEnv atom).1) ScopeEnv.empty .hashBag _ _
        [stop] [output] (Or.inl (atoms_stopped relEnv)) (Or.inl (atoms_emitting relEnv))
  | step + 1 =>
      sourceScope_step_setoid (langSortedGSLTUsing relEnv platform).equations
        (langSortedSemanticReducesUsing relEnv platform)
        (fun atom => (sortedAtoms relEnv atom).1)
        (frameClosed_sortedEquationFrameUsing relEnv platform (sortedAtoms relEnv))
        quoteLabel dropLabel "Stopped" "Emitting"
        (chain_sorted_singleton relEnv step) (chain_in_sorted_scope step)
        (atoms_emitting relEnv)

/-- **The separation, in one frame.**  In the frame whose instances read their
type contexts, every link of the chain is inside the source's scope and the
terminated process is outside it.  The ambient powerset has the second half and
not the first; the permissive equation reading has the first and cannot state
the second, because the bound it would rest on holds of every term there. -/
theorem sorted_frame_separates (step : Nat) :
    langSortedSemUsing relEnv platform (sortedAtoms relEnv) scope (chain step) ∧
      ¬ langSortedSemUsing relEnv platform (sortedAtoms relEnv) scope stop :=
  ⟨chain_in_sorted_scope relEnv step,
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquationDiscipline.stop_not_in_sortedScope
      relEnv (sortedAtoms relEnv) "Stopped" "Emitting"⟩

/-! ### The two constructions, related in the frame that carries both halves -/

/-- The part atoms, admitted to the disciplined logic. -/
def sortedPartAtoms : SortedEquationAtomSemUsing relEnv platform :=
  sortedEquationAtomSemUsing relEnv platform
    (Mettapedia.OSLF.Framework.ScopeComparison.equationPartAtoms
      relEnv platform leftPart rightPart)

/-- **The disciplined singleton law at every name of the hand-written scope.**
The sorting judgement is the induction on the grammar above; the law itself is
the presentation's, and the discipline leaves the derived laws alone. -/
theorem platform_sorted_singletonDrop :
    ∀ name, generatedScope leftPart rightPart name →
      (langSortedGSLTUsing relEnv platform).Equiv
        (Mettapedia.OSLF.Framework.ScopeComparison.part (drop name)) (drop name) :=
  fun name member =>
    sortedDerivedInstance_equivalent
      (DerivedInstance.singleton (parDeclaration_isAlgebra [2]) rfl
        (bag_sortedParts [2]
          (.cons (drop_hasSort [2] (generatedScope_hasSort name member)) (.nil _ _))))

/-- **And the hand-written fixed point is inside the formula's reading in the
disciplined frame.**  The tree had this containment only in the frame whose
bounds are vacuous; it now holds in the frame that carries both halves of the
scope separation. -/
theorem generatedScope_le_sorted_formula :
    ∀ name, generatedScope leftPart rightPart name →
      langSortedSemUsing relEnv platform (sortedPartAtoms relEnv)
        Mettapedia.OSLF.Framework.ScopeComparison.scopeFormula name :=
  fun name member =>
    Mettapedia.OSLF.Framework.ScopeComparison.generatedScope_le_semEnv_setoid
      (langSortedGSLTUsing relEnv platform).equations
      (langSortedSemanticReducesUsing relEnv platform)
      (fun atom => (sortedPartAtoms relEnv atom).1)
      (frameClosed_sortedEquationFrameUsing relEnv platform (sortedPartAtoms relEnv))
      leftPart rightPart
      (fun _ holds =>
        Mettapedia.OSLF.Framework.ScopeComparison.equationPartAtoms_left
          relEnv platform holds)
      (fun _ holds =>
        Mettapedia.OSLF.Framework.ScopeComparison.equationPartAtoms_right
          relEnv platform holds)
      (platform_sorted_singletonDrop relEnv) name member

end Sorted

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSourceScope
