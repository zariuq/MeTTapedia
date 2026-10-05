import Mettapedia.GSLT.LanguageDef.DeterministicEquations.InstantiationExtraction

/-! # Complete source-derived theorem instantiation controls

These examples use the checked instantiation entry, including argument typing,
the entire dependency matrix, and ordered substitution. They concern encoded
source values; declaration admission and validation of external atoms remain
separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation.Controls

open Mettapedia.Languages.MM0
open Kernel
open Presentation.ComputationalContext

private def inputs (signature : List (Nat × TermDecl)) (target : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) : List Term :=
  [encodeList (encodePair natural encodeDeclaration) signature, encodeList encodeBinder target,
    encodeTheoremDecl declaration, encodeList Presentation.encode arguments]

private theorem accepted (signature : List (Nat × TermDecl)) (target : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (result : TheoremInstance)
    (source : declaration.instantiate? (Inference.termTable signature) target arguments = some result) :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs signature target declaration arguments) (encodeOption encodeTheoremInstance (some result)) :=
  (instantiate_accepts_iff signature target declaration arguments result).mpr
    ((TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp source)

private theorem refused (signature : List (Nat × TermDecl)) (target : Context)
    (declaration : TheoremDecl) (arguments : List Preterm)
    (source : declaration.instantiate? (Inference.termTable signature) target arguments = none) :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs signature target declaration arguments) (.sym "None") :=
  (instantiate_refuses_iff signature target declaration arguments).mpr
    ((TheoremDecl.instantiate_none_iff _ _ _ _).mp source)

private def target : Context := [.bound 0, .regular 0 ∅, .regular 0 {0}]
private def dependent : TheoremDecl :=
  ⟨[.bound 0, .regular 0 {0}], [.var 1, .var 0, .var 1], .var 1⟩
private def independent : TheoremDecl :=
  ⟨[.bound 0, .regular 0 ∅], [.var 1], .var 1⟩
private def submitted : List Preterm := [.var 0, .var 2]
private def orderedResult : TheoremInstance := ⟨[.var 2, .var 0, .var 2], .var 2⟩

theorem ordered_repeated_premises :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target dependent submitted)
      (encodeOption encodeTheoremInstance (some orderedResult)) :=
  accepted _ _ _ _ _ rfl

theorem typing_alone_does_not_establish_independence :
    List.Forall₂ (Preterm.FitsBinder (Inference.termTable []) target)
      submitted independent.arguments ∧
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target independent submitted) (.sym "None") := by
  constructor
  · exact (Substitution.checkArguments_iff _ _ _ _).mp rfl
  · exact refused _ _ _ _ rfl

theorem earlier_entry_dependency_is_checked :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target ⟨[.regular 0 ∅, .bound 0], [], .var 0⟩ [.var 2, .var 0])
      (.sym "None") :=
  refused _ _ _ _ rfl

theorem duplicate_bound_images_refused :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] [.bound 0] ⟨[.bound 0, .bound 0], [], .var 0⟩ [.var 0, .var 0])
      (.sym "None") :=
  refused _ _ _ _ rfl

theorem missing_argument_refused :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target dependent [.var 0]) (.sym "None") :=
  refused _ _ _ _ rfl

theorem surplus_argument_refused :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target dependent [.var 0, .var 2, .var 1]) (.sym "None") :=
  refused _ _ _ _ rfl

theorem regular_image_cannot_fill_bound_slot :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target ⟨[.bound 0], [], .var 0⟩ [.var 2]) (.sym "None") :=
  refused _ _ _ _ rfl

theorem wrong_argument_sort_refused :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] [.regular 1 ∅] ⟨[.regular 0 ∅], [], .var 0⟩ [.var 0]) (.sym "None") :=
  refused _ _ _ _ rfl

theorem missing_hypothesis_image_refused :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] [.bound 0] ⟨[.bound 0], [.var 1], .var 0⟩ [.var 0]) (.sym "None") :=
  refused _ _ _ _ rfl

theorem missing_conclusion_image_refused :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] [.bound 0] ⟨[.bound 0], [.var 0], .var 1⟩ [.var 0]) (.sym "None") :=
  refused _ _ _ _ rfl

theorem signature_first_key_controls_argument_typing :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [(7, ⟨[], 1, ∅⟩), (7, ⟨[], 0, ∅⟩)] []
        ⟨[.regular 0 ∅], [], .var 0⟩ [.term 7]) (.sym "None") :=
  refused _ _ _ _ rfl

theorem reordered_signature_changes_acceptance :
    Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [(7, ⟨[], 0, ∅⟩), (7, ⟨[], 1, ∅⟩)] []
        ⟨[.regular 0 ∅], [], .var 0⟩ [.term 7])
      (encodeOption encodeTheoremInstance (some ⟨[], .term 7⟩)) :=
  accepted _ _ _ _ _ rfl

theorem duplicate_premise_cannot_be_dropped :
    ¬ Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target dependent submitted)
      (encodeOption encodeTheoremInstance (some ⟨[.var 2, .var 0], .var 2⟩)) := by
  intro observed
  have same := encodeOption_injective encodeTheoremInstance_injective
    (observed.deterministic ordered_repeated_premises)
  cases same

theorem well_typed_operand_does_not_rescue_wrong_arity :
    Preterm.HasType (Inference.termTable []) target (.var 0) [] 0 ∧
    ¬ Applies instantiateProgram dataEqualityHost instantiateHead
      (inputs [] target dependent [.var 0])
      (encodeOption encodeTheoremInstance (some orderedResult)) := by
  constructor
  · exact .var (binder := .bound 0) rfl
  · intro observed
    have same := observed.deterministic missing_argument_refused
    cases same

theorem source_refusal_is_a_completed_value (fuel : Nat)
    (completed : apply instantiateProgram dataEqualityHost fuel instantiateHead
      (inputs [] target dependent [.var 0]) ≠ .exhausted) :
    apply instantiateProgram dataEqualityHost fuel instantiateHead
      (inputs [] target dependent [.var 0]) = .value (.sym "None") :=
  completed_exact missing_argument_refused fuel completed

theorem zero_fuel_is_exhaustion :
    apply instantiateProgram dataEqualityHost 0 instantiateHead
      (inputs [] target dependent [.var 0]) = .exhausted := by
  have atZero (first second third fourth : Term) :
      apply instantiateProgram dataEqualityHost 0 instantiateHead
        [first, second, third, fourth] = .exhausted := by
    have defined : instantiateProgram.definesAt instantiateHead 4 = true := by decide
    unfold apply applyWith
    simp only [List.length_cons, List.length_nil, defined, ↓reduceIte]
    unfold instantiateHead
    rw [instantiateProgram.selection_0]
    rfl
  exact atZero _ _ _ _

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation.Controls
