import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationDefinitions

/-!
# Admission through the translation

Let `P` be a candidate step over the second-order frames whose guards and predicate queries are
equation guards (`Holds f g ↔ Models g (guards f)`). For a firing `f`:

* **`admission_transfer`**: if the firing's information has a second-order principal answer whose
  translation factors every dependent solution on translated terms, then `f` is admitted exactly
  when the dependent admission condition holds for the translated data: shapes, enabling, dependent
  solvability of the translated information, and the dependent ask of the translated guards.
* **`definition_admission_transfer`**: this holds whenever the information is a definition
  `m(x̄) ≐ t` with `m` not in `t`, the information a helper firing adds.

The hypothesis of `admission_transfer` is exactly what the translation must supply beyond the
definition fragment: image factorization of the principal answers the second-order solver returns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation

open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

variable {Head : Type} {S : Binding.Signature} (names : BindingSignatureEmbedding.Names S)
  {rules : Rules Head} (realization : BindingSignatureEmbedding.Realization names rules)
  {O : Type} [DecidableEq O] {State : Type} {Firing : State → Type}
  (P : Step (listFrames S) O State Firing)
  [P.Guarded]
  (guards : ∀ {s : State} (f : Firing s),
    EquationStore (Binding.ContextualFamily.Observation S (P.target f).get))

/-- **Admission is preserved and reflected** by the translation at a firing whose information has a
principal answer that the translation keeps principal on translated terms. -/
theorem admission_transfer
    (holds : ∀ {s : State} (f : Firing s) (N : List (Binding.MetaArity S))
      (g : Binding.ContextualFamily.Assignment (S := S) (P.target f).get N.get),
      P.Holds f N g ↔ (listFrames S).Models g (guards f))
    (reflects : (translation names realization).Reflects)
    {s : State} (f : Firing s) {m : List (Binding.MetaArity S)}
    {answer : Binding.ContextualFamily.Assignment (S := S) (P.target f).get m.get}
    (principal : (listFrames S).Principal (P.information f) answer)
    (factors : (translation names realization).FactorsOnImage (P.information f)
      ((translation names realization).hom answer)) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (Dependent.frames rules).Solvable ((translation names realization).store (P.information f)) ∧
      (Dependent.frames rules).Entails ((translation names realization).store (P.information f))
        (fun _ g => (Dependent.frames rules).Models g
          ((translation names realization).store (guards f))) := by
  have asks : (listFrames S).Entails (P.information f) (P.Holds f) ↔
      (listFrames S).Entails (P.information f) (fun _ g => (listFrames S).Models g (guards f)) :=
    ⟨fun asked N g solved => (holds f N g).mp (asked N g solved),
      fun asked N g solved => (holds f N g).mpr (asked N g solved)⟩
  rw [P.admits_iff f, asks,
    ← (translation names realization).entails_iff_of_factorsOnImage reflects principal factors]
  have solvable : (listFrames S).Solvable (P.information f) ↔
      (Dependent.frames rules).Solvable ((translation names realization).store (P.information f)) :=
    ⟨(translation names realization).solvable, fun _ => principal.solvable⟩
  rw [solvable]

/-- **Admission at definitions**: at a firing whose information is a definition `m(x̄) ≐ t` with `m`
not in `t`, admission is preserved and reflected by the translation. -/
theorem definition_admission_transfer (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) (sortInjective : Function.Injective names.sort)
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s)))
    (holds : ∀ {s : State} (f : Firing s) (N : List (Binding.MetaArity S))
      (g : Binding.ContextualFamily.Assignment (S := S) (P.target f).get N.get),
      P.Holds f N g ↔ (listFrames S).Models g (guards f))
    {s : State} (f : Firing s) (i : Fin (P.target f).length)
    (t : Binding.Term (Sig S (P.target f)) ((P.target f).get i).1 ((P.target f).get i).2)
    (absent : i ∉ Binding.ContextualFamily.support t)
    (defined : P.information f = definitionStore (P.target f) i t) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (Dependent.frames rules).Solvable ((translation names realization).store (P.information f)) ∧
      (Dependent.frames rules).Entails ((translation names realization).store (P.information f))
        (fun _ g => (Dependent.frames rules).Models g
          ((translation names realization).store (guards f))) := by
  have principal := definition_principal (P.target f) i t absent
  have factors := definition_factorsOnImage names realization (P.target f) i t
  rw [← defined] at principal factors
  exact admission_transfer names realization P guards holds
    (translation_reflects names realization empty symmetric sortInjective @operatorInjective)
    f principal factors

end Translation

#print axioms Translation.admission_transfer
#print axioms Translation.definition_admission_transfer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
