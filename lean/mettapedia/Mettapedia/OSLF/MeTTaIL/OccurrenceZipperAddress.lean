import Mettapedia.OSLF.MeTTaIL.RuleBinding
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Executable occurrence addresses and one-hole contexts

An authored occurrence address selects either an ordinary pattern variable or
a collection rest. An ordinary variable has an existing one-hole context; a
rest is metadata on a collection and is not a term hole. This decoder retains
the exact child address while using the established context representation.
-/

namespace Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

/-- Decode an ordinary metavariable address into the actual structural zipper.
The collection-rest slot has no zipper and returns `none`. -/
def termZipperAt? : Pattern → List Nat → Option (String × OneHoleContext)
  | .fvar name, [] => some (name, .hole)
  | .apply constructor arguments, index :: path => do
      let argument ← arguments[index]?
      let (name, inner) ← termZipperAt? argument path
      pure (name, .apply constructor (arguments.take index) inner
        (arguments.drop (index + 1)))
  | .lambda binder body, 0 :: path => do
      let (name, inner) ← termZipperAt? body path
      pure (name, .lambda binder inner)
  | .multiLambda arity binders body, 0 :: path => do
      let (name, inner) ← termZipperAt? body path
      pure (name, .multiLambda arity binders inner)
  | .subst body replacement, 0 :: path => do
      let (name, inner) ← termZipperAt? body path
      pure (name, .substBody inner replacement)
  | .subst body replacement, 1 :: path => do
      let (name, inner) ← termZipperAt? replacement path
      pure (name, .substReplacement body inner)
  | .collection kind elements rest, index :: path =>
      if index < elements.length then do
        let element ← elements[index]?
        let (name, inner) ← termZipperAt? element path
        pure (name, .collection kind (elements.take index) inner
          (elements.drop (index + 1)) rest)
      else none
  | _, _ => none
termination_by _ path => path.length

private theorem pairMap_name {β : Type}
    (source : Option (String × OneHoleContext))
    (wrap : OneHoleContext → β)
    {name : String} {value : β}
    (mapped : source.bind (fun pair => some (pair.1, wrap pair.2)) =
      some (name, value)) :
    ∃ inner, source = some (name, inner) := by
  cases source with
  | none => simp at mapped
  | some pair =>
      rcases pair with ⟨actualName, inner⟩
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at mapped
      rcases mapped with ⟨nameEq, _⟩
      subst actualName
      exact ⟨inner, rfl⟩

private theorem pairMap_value {β : Type}
    (source : Option (String × OneHoleContext))
    (wrap : OneHoleContext → β)
    {name : String} {value : β}
    (mapped : source.bind (fun pair => some (pair.1, wrap pair.2)) =
      some (name, value)) :
    ∃ inner, source = some (name, inner) ∧ value = wrap inner := by
  cases source with
  | none => simp at mapped
  | some pair =>
      rcases pair with ⟨actualName, inner⟩
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at mapped
      rcases mapped with ⟨nameEq, valueEq⟩
      subst actualName
      exact ⟨inner, rfl, valueEq.symm⟩

private theorem take_some_drop {α : Type} {elements : List α}
    {index : Nat} {element : α}
    (selected : elements[index]? = some element) :
    elements.take index ++ element :: elements.drop (index + 1) =
      elements := by
  have inBounds := (List.getElem?_eq_some_iff.mp selected).1
  have actual := List.getElem?_eq_getElem inBounds
  rw [selected] at actual
  have elementEq : element = elements[index] := Option.some.inj actual
  rw [elementEq, List.getElem_cons_drop inBounds]
  exact List.take_append_drop index elements

/-- Every decoded ordinary address agrees with the executable reader of that
same address. The converse needs to exclude collection-rest slots. -/
theorem termZipperAt?_occurrenceAt?
    {pattern : Pattern} {path : List Nat}
    {name : String} {context : OneHoleContext}
    (decoded : termZipperAt? pattern path = some (name, context)) :
    occurrenceAt? pattern path = some name := by
  induction path generalizing pattern name context with
  | nil =>
      cases pattern <;> simp [termZipperAt?, occurrenceAt?] at decoded ⊢
      case fvar name' => exact decoded.1
  | cons index path inductionHypothesis =>
      cases pattern with
      | bvar _ => simp [termZipperAt?] at decoded
      | fvar _ => simp [termZipperAt?] at decoded
      | apply constructor arguments =>
          simp [termZipperAt?, occurrenceAt?] at decoded ⊢
          obtain ⟨argument, selectedArgument, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp decoded
          obtain ⟨inner, innerDecoded⟩ := pairMap_name
            (termZipperAt? argument path)
            (fun inner => OneHoleContext.apply constructor
              (arguments.take index) inner (arguments.drop (index + 1)))
            selectedInner
          rw [selectedArgument]
          exact inductionHypothesis innerDecoded
      | lambda binder body =>
          cases index with
          | zero =>
              simp [termZipperAt?, occurrenceAt?] at decoded ⊢
              obtain ⟨inner, innerDecoded⟩ := pairMap_name
                (termZipperAt? body path)
                (OneHoleContext.lambda binder) decoded
              exact inductionHypothesis innerDecoded
          | succ _ => simp [termZipperAt?] at decoded
      | multiLambda arity binders body =>
          cases index with
          | zero =>
              simp [termZipperAt?, occurrenceAt?] at decoded ⊢
              obtain ⟨inner, innerDecoded⟩ := pairMap_name
                (termZipperAt? body path)
                (OneHoleContext.multiLambda arity binders) decoded
              exact inductionHypothesis innerDecoded
          | succ _ => simp [termZipperAt?] at decoded
      | subst body replacement =>
          cases index with
          | zero =>
              simp [termZipperAt?, occurrenceAt?] at decoded ⊢
              obtain ⟨inner, innerDecoded⟩ := pairMap_name
                (termZipperAt? body path)
                (fun inner => OneHoleContext.substBody inner replacement)
                decoded
              exact inductionHypothesis innerDecoded
          | succ index =>
              cases index with
              | zero =>
                  simp [termZipperAt?, occurrenceAt?] at decoded ⊢
                  obtain ⟨inner, innerDecoded⟩ := pairMap_name
                    (termZipperAt? replacement path)
                    (OneHoleContext.substReplacement body) decoded
                  exact inductionHypothesis innerDecoded
              | succ _ => simp [termZipperAt?] at decoded
      | collection kind elements rest =>
          simp [termZipperAt?] at decoded
          obtain ⟨inBounds, selected⟩ := decoded
          obtain ⟨element, selectedElement, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp selected
          obtain ⟨inner, innerDecoded⟩ := pairMap_name
            (termZipperAt? element path)
            (fun inner => OneHoleContext.collection kind
              (elements.take index) inner (elements.drop (index + 1)) rest)
            selectedInner
          simp only [occurrenceAt?, if_pos inBounds,
            selectedElement, Option.bind_some]
          exact inductionHypothesis innerDecoded

/-- The zipper reconstructed from an executable term address selects its
original free-variable occurrence in the original pattern. -/
theorem termZipperAt?_selects
    {pattern : Pattern} {path : List Nat}
    {name : String} {context : OneHoleContext}
    (decoded : termZipperAt? pattern path = some (name, context)) :
    Selects (.fvar name) context pattern := by
  suffices filled : context.fill (.fvar name) = pattern by
    rw [← filled]
    exact Selects.of_fill context (.fvar name)
  induction path generalizing pattern name context with
  | nil =>
      cases pattern <;> simp [termZipperAt?] at decoded ⊢
      case fvar _ =>
        rcases decoded with ⟨nameEq, contextEq⟩
        subst name
        subst context
        rfl
  | cons index path inductionHypothesis =>
      cases pattern with
      | bvar _ => simp [termZipperAt?] at decoded
      | fvar _ => simp [termZipperAt?] at decoded
      | apply constructor arguments =>
          simp only [termZipperAt?] at decoded
          obtain ⟨argument, selectedArgument, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp decoded
          obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
            (termZipperAt? argument path)
            (fun inner => OneHoleContext.apply constructor
              (arguments.take index) inner (arguments.drop (index + 1)))
            selectedInner
          subst context
          have innerFilled := inductionHypothesis innerDecoded
          simp only [OneHoleContext.fill, innerFilled]
          rw [take_some_drop selectedArgument]
      | lambda binder body =>
          cases index with
          | zero =>
              simp only [termZipperAt?] at decoded
              obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                (termZipperAt? body path)
                (OneHoleContext.lambda binder) decoded
              subst context
              simpa [OneHoleContext.fill] using
                congrArg (Pattern.lambda binder)
                  (inductionHypothesis innerDecoded)
          | succ _ => simp [termZipperAt?] at decoded
      | multiLambda arity binders body =>
          cases index with
          | zero =>
              simp only [termZipperAt?] at decoded
              obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                (termZipperAt? body path)
                (OneHoleContext.multiLambda arity binders) decoded
              subst context
              simpa [OneHoleContext.fill] using
                congrArg (Pattern.multiLambda arity binders)
                  (inductionHypothesis innerDecoded)
          | succ _ => simp [termZipperAt?] at decoded
      | subst body replacement =>
          cases index with
          | zero =>
              simp only [termZipperAt?] at decoded
              obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                (termZipperAt? body path)
                (fun inner => OneHoleContext.substBody inner replacement)
                decoded
              subst context
              simpa [OneHoleContext.fill] using
                congrArg (fun body => Pattern.subst body replacement)
                  (inductionHypothesis innerDecoded)
          | succ index =>
              cases index with
              | zero =>
                  simp [termZipperAt?] at decoded
                  obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                    (termZipperAt? replacement path)
                    (OneHoleContext.substReplacement body) decoded
                  subst context
                  simpa [OneHoleContext.fill] using
                    congrArg (Pattern.subst body)
                      (inductionHypothesis innerDecoded)
              | succ _ => simp [termZipperAt?] at decoded
      | collection kind elements rest =>
          simp [termZipperAt?] at decoded
          obtain ⟨_, selected⟩ := decoded
          obtain ⟨element, selectedElement, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp selected
          obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
            (termZipperAt? element path)
            (fun inner => OneHoleContext.collection kind
              (elements.take index) inner (elements.drop (index + 1)) rest)
            selectedInner
          subst context
          have innerFilled := inductionHypothesis innerDecoded
          simp only [OneHoleContext.fill, innerFilled]
          rw [take_some_drop selectedElement]

/-- Number of binders crossed on the unique path to a zipper hole. Explicit
substitution bodies cross the eliminated binder, while replacements do not. -/
def binderCount : OneHoleContext → Nat
  | .hole => 0
  | .apply _ _ inner _ => binderCount inner
  | .lambda _ inner => 1 + binderCount inner
  | .multiLambda arity _ inner => arity + binderCount inner
  | .substBody inner _ => 1 + binderCount inner
  | .substReplacement _ inner => binderCount inner
  | .collection _ _ inner _ _ => binderCount inner

/-- The executable depth reader and the decoded zipper count precisely the
same binder crossings. The starting ambient depth remains explicit. -/
theorem termZipperAt?_depth
    {pattern : Pattern} {path : List Nat}
    {name : String} {context : OneHoleContext}
    (decoded : termZipperAt? pattern path = some (name, context))
    (depth : Nat) :
    occurrenceDepthAt? pattern path depth =
      some (depth + binderCount context) := by
  induction path generalizing pattern name context depth with
  | nil =>
      cases pattern <;> simp [termZipperAt?] at decoded ⊢
      case fvar _ =>
        rcases decoded with ⟨_, contextEq⟩
        subst context
        simp [occurrenceDepthAt?, binderCount]
  | cons index path inductionHypothesis =>
      cases pattern with
      | bvar _ => simp [termZipperAt?] at decoded
      | fvar _ => simp [termZipperAt?] at decoded
      | apply constructor arguments =>
          simp only [termZipperAt?] at decoded
          obtain ⟨argument, selectedArgument, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp decoded
          obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
            (termZipperAt? argument path)
            (fun inner => OneHoleContext.apply constructor
              (arguments.take index) inner (arguments.drop (index + 1)))
            selectedInner
          subst context
          simp [occurrenceDepthAt?, binderCount, selectedArgument,
            inductionHypothesis innerDecoded depth]
      | lambda binder body =>
          cases index with
          | zero =>
              simp only [termZipperAt?] at decoded
              obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                (termZipperAt? body path)
                (OneHoleContext.lambda binder) decoded
              subst context
              simpa [occurrenceDepthAt?, binderCount, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                inductionHypothesis innerDecoded (depth + 1)
          | succ _ => simp [termZipperAt?] at decoded
      | multiLambda arity binders body =>
          cases index with
          | zero =>
              simp only [termZipperAt?] at decoded
              obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                (termZipperAt? body path)
                (OneHoleContext.multiLambda arity binders) decoded
              subst context
              simpa [occurrenceDepthAt?, binderCount, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                inductionHypothesis innerDecoded (depth + arity)
          | succ _ => simp [termZipperAt?] at decoded
      | subst body replacement =>
          cases index with
          | zero =>
              simp only [termZipperAt?] at decoded
              obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                (termZipperAt? body path)
                (fun inner => OneHoleContext.substBody inner replacement)
                decoded
              subst context
              simpa [occurrenceDepthAt?, binderCount, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                inductionHypothesis innerDecoded (depth + 1)
          | succ index =>
              cases index with
              | zero =>
                  simp [termZipperAt?] at decoded
                  obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
                    (termZipperAt? replacement path)
                    (OneHoleContext.substReplacement body) decoded
                  subst context
                  simpa [occurrenceDepthAt?, binderCount] using
                    inductionHypothesis innerDecoded depth
              | succ _ => simp [termZipperAt?] at decoded
      | collection kind elements rest =>
          simp [termZipperAt?] at decoded
          obtain ⟨inBounds, selected⟩ := decoded
          obtain ⟨element, selectedElement, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp selected
          obtain ⟨inner, innerDecoded, contextEq⟩ := pairMap_value
            (termZipperAt? element path)
            (fun inner => OneHoleContext.collection kind
              (elements.take index) inner (elements.drop (index + 1)) rest)
            selectedInner
          subst context
          simp only [occurrenceDepthAt?, if_pos inBounds,
            selectedElement, Option.bind_some, binderCount]
          exact inductionHypothesis innerDecoded depth

end Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
