import Mettapedia.GSLT.Core.StaticPart
import Mettapedia.GSLT.Compilation.SyntaxOnFrames
import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep

/-!
# Restricting root compilation to syntax

For the admitted root compiler, removing the authored operational part
leaves the same row encoding and an empty rule set. The two routes
agree as operational translations after comparison with the static parts.

The square is stated at the row observation. Concrete Transform states also
carry occurrence identities, and their relation to the row observation is
the existing root compiler correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.RootStaticPart

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (not_step_of_matchPatternForRule_eq_nil)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (Tm)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines
  (rootSystem rootRules stepSystem)
open RootRewritesOnTheStep (compile lowerRules sourceSystem encode rootStep_of_step)
open SyntaxOnFrames (syntaxPart)

abbrev Authored (relations : RelationEnv) (language : LanguageDef) : OperationalTheory :=
  ⟨sourceSystem relations language⟩
abbrev Compiled (schemas : List (Tm × Tm)) : OperationalTheory :=
  ⟨rootSystem schemas⟩

variable {language : LanguageDef} {schemas : List (Tm × Tm)}

/-- The syntax of every admitted root presentation compiles to the empty
operational program. The syntax itself is still read and stored as usual. -/
theorem compile_syntaxPart (compiled : compile language = .ok schemas) :
    compile (syntaxPart language) = .ok [] := by
  unfold compile at compiled
  split at compiled
  · rename_i admitted
    simp only [Bool.and_eq_true] at admitted
    change (if true && !language.hasAlgebraDeclarations then lowerRules [] else .error .staticEquations) = _
    simp [admitted.2, lowerRules]
  · cases compiled

def translate (relations : RelationEnv) (compiled : compile language = .ok schemas) :
    Authored relations language ⟶ Compiled schemas where
  mapTerm := encode
  mapEquiv := fun same => congrArg encode same
  mapStep := rootStep_of_step compiled

private theorem syntax_has_no_step (relations : RelationEnv) (language : LanguageDef) :
    StaticPart.StepFree (Authored relations (syntaxPart language)) := by
  intro s t
  exact not_step_of_matchPatternForRule_eq_nil fun _ member => (List.not_mem_nil member).elim

/-- The authored syntax-only theory is the static part at the root compiler's
chosen raw-syntax observation. -/
def sourceIso (relations : RelationEnv) (language : LanguageDef) :
    Authored relations (syntaxPart language) ≅ (StaticPart.erase (Authored relations language)).obj where
  hom :=
    { mapTerm := id, mapEquiv := fun h => h,
      mapStep := fun {s t} h => (syntax_has_no_step relations language s t h).elim }
  inv := { mapTerm := id, mapEquiv := fun h => h, mapStep := fun h => h.elim }
  hom_inv_id := by
    apply OperationalTranslation.ext
    rfl
  inv_hom_id := by
    apply OperationalTranslation.ext
    rfl

/-- An empty rule set is the static part of the row theory. -/
def targetIso (schemas : List (Tm × Tm)) :
    Compiled [] ≅ (StaticPart.erase (Compiled schemas)).obj where
  hom :=
    { mapTerm := id
      mapEquiv := fun h => h
      mapStep := by
        rintro _ _ ⟨_, member, _⟩
        exact (List.not_mem_nil member).elim }
  inv := { mapTerm := id, mapEquiv := fun h => h, mapStep := fun h => h.elim }
  hom_inv_id := by
    apply OperationalTranslation.ext
    rfl
  inv_hom_id := by
    apply OperationalTranslation.ext
    rfl

/-- Independently compiling the erased authored presentation gives the
restriction of the full program's term translation. -/
theorem square (relations : RelationEnv) (compiled : compile language = .ok schemas) :
    translate relations (compile_syntaxPart compiled) ≫ (targetIso schemas).hom =
      (sourceIso relations language).hom ≫ (StaticPart.forgetSteps.map (translate relations compiled)).hom := by
  apply OperationalTranslation.ext
  rfl

/-- The empty rule set also has no concrete firings of the general
Transform step. -/
theorem empty_transform_step (source target : (stepSystem ℕ (rootRules [])).Term) :
    ¬ (stepSystem ℕ (rootRules [])).Step source target := by
  rintro ⟨firing, _, _⟩
  exact List.not_mem_nil firing.member

namespace Controls

open Mettapedia.GSLT.Ultrainfinite (StepCover)
open RootRewritesOnTheStep.Controls (choice choice_compiles choice_step_iff)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-- Both constructor arguments are still available to the compiler when its
two competing rules are removed. The compiled rule set is empty. -/
theorem choice_syntax_compiles : compile (syntaxPart choice) = .ok [] := by
  obtain ⟨_, compiled⟩ := choice_compiles
  exact compile_syntaxPart compiled

theorem choice_extension_adds_a_step :
    ¬ Nonempty (StepCover (StaticPart.erase (Authored RelationEnv.empty choice)).obj.theory
      (Authored RelationEnv.empty choice).theory
      (StaticPart.inclusion (Authored RelationEnv.empty choice)).mapTerm) := by
  intro covers
  have quiet := (StaticPart.covers_iff (Authored RelationEnv.empty choice)).mp covers
  let first : Pattern := .bvar 0
  let second : Pattern := .bvar 1
  exact quiet (.apply "Choose" [first, second]) first
    ((choice_step_iff (relEnv := RelationEnv.empty) first second first).mpr (.inl rfl))

end Controls

#print axioms compile_syntaxPart
#print axioms square
#print axioms empty_transform_step
#print axioms Controls.choice_extension_adds_a_step

end Mettapedia.GSLT.Compilation.RootStaticPart
