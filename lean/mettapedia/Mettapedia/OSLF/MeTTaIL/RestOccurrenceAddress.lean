import Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress

/-!
# Executable addresses of collection rests

A rest slot is metadata on a collection node, not a pattern-variable term
hole. Its address selects the enclosing collection together with a one-hole
context for that collection. This representation keeps the existing zipper
calculus while distinguishing rest sites from ordinary term occurrences.
-/

namespace Mettapedia.OSLF.MeTTaIL.RestOccurrenceAddress

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress
open Mettapedia.OSLF.MeTTaIL.RuleBinding

set_option autoImplicit false

/-- A rest slot and the structural context of its enclosing collection. -/
structure RestSite where
  name : String
  kind : CollType
  elements : List Pattern
  context : OneHoleContext
deriving Repr, DecidableEq

def RestSite.focus (site : RestSite) : Pattern :=
  .collection site.kind site.elements (some site.name)

def RestSite.push (outer : OneHoleContext) (site : RestSite) : RestSite :=
  { site with context := outer.comp site.context }

/-- Decode exactly the collection-rest addresses accepted by the executable
occurrence reader, retaining the context of the enclosing collection. -/
def restSiteAt? : Pattern → List Nat → Option RestSite
  | .apply constructor arguments, index :: path => do
      let argument ← arguments[index]?
      let site ← restSiteAt? argument path
      pure (site.push
        (.apply constructor (arguments.take index) .hole
          (arguments.drop (index + 1))))
  | .lambda binder body, 0 :: path => do
      let site ← restSiteAt? body path
      pure (site.push (.lambda binder .hole))
  | .multiLambda arity binders body, 0 :: path => do
      let site ← restSiteAt? body path
      pure (site.push (.multiLambda arity binders .hole))
  | .subst body replacement, 0 :: path => do
      let site ← restSiteAt? body path
      pure (site.push (.substBody .hole replacement))
  | .subst body replacement, 1 :: path => do
      let site ← restSiteAt? replacement path
      pure (site.push (.substReplacement body .hole))
  | .collection kind elements rest, index :: path =>
      if index < elements.length then do
        let element ← elements[index]?
        let site ← restSiteAt? element path
        pure (site.push
          (.collection kind (elements.take index) .hole
            (elements.drop (index + 1)) rest))
      else if index == elements.length && path.isEmpty then
        rest.map fun name =>
          { name, kind, elements, context := .hole }
      else none
  | _, _ => none
termination_by _ path => path.length

private theorem pushed_some (source : Option RestSite)
    (outer : OneHoleContext) {site : RestSite}
    (mapped : source.bind (fun inner => some (inner.push outer)) = some site) :
    ∃ inner, source = some inner ∧ site = inner.push outer := by
  cases source with
  | none => simp at mapped
  | some inner =>
      simp only [Option.bind_some, Option.some.injEq] at mapped
      exact ⟨inner, rfl, mapped.symm⟩

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

/-- The selected rest's enclosing collection reconstructs the original
pattern when filled into its decoded outer context. -/
theorem restSiteAt?_fill
    {pattern : Pattern} {path : List Nat} {site : RestSite}
    (decoded : restSiteAt? pattern path = some site) :
    site.context.fill site.focus = pattern := by
  induction path generalizing pattern site with
  | nil =>
      cases pattern <;> simp [restSiteAt?] at decoded
  | cons index path inductionHypothesis =>
      cases pattern with
      | bvar _ => simp [restSiteAt?] at decoded
      | fvar _ => simp [restSiteAt?] at decoded
      | apply constructor arguments =>
          simp only [restSiteAt?] at decoded
          obtain ⟨argument, selectedArgument, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp decoded
          obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
            (restSiteAt? argument path)
            (.apply constructor (arguments.take index) .hole
              (arguments.drop (index + 1))) selectedInner
          subst site
          have innerFilled := inductionHypothesis innerDecoded
          change inner.context.fill
            (.collection inner.kind inner.elements (some inner.name)) =
              argument at innerFilled
          simp only [RestSite.push, RestSite.focus,
            OneHoleContext.fill_comp, OneHoleContext.fill]
          rw [innerFilled]
          rw [take_some_drop selectedArgument]
      | lambda binder body =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path) (.lambda binder .hole) decoded
              subst site
              simpa [RestSite.push, RestSite.focus,
                OneHoleContext.fill_comp, OneHoleContext.fill] using
                congrArg (Pattern.lambda binder)
                  (inductionHypothesis innerDecoded)
          | succ _ => simp [restSiteAt?] at decoded
      | multiLambda arity binders body =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path)
                (.multiLambda arity binders .hole) decoded
              subst site
              simpa [RestSite.push, RestSite.focus,
                OneHoleContext.fill_comp, OneHoleContext.fill] using
                congrArg (Pattern.multiLambda arity binders)
                  (inductionHypothesis innerDecoded)
          | succ _ => simp [restSiteAt?] at decoded
      | subst body replacement =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path) (.substBody .hole replacement) decoded
              subst site
              simpa [RestSite.push, RestSite.focus,
                OneHoleContext.fill_comp, OneHoleContext.fill] using
                congrArg (fun body => Pattern.subst body replacement)
                  (inductionHypothesis innerDecoded)
          | succ index =>
              cases index with
              | zero =>
                  simp [restSiteAt?] at decoded
                  obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                    (restSiteAt? replacement path)
                    (.substReplacement body .hole) decoded
                  subst site
                  simpa [RestSite.push, RestSite.focus,
                    OneHoleContext.fill_comp, OneHoleContext.fill] using
                    congrArg (Pattern.subst body)
                      (inductionHypothesis innerDecoded)
              | succ _ => simp [restSiteAt?] at decoded
      | collection kind elements rest =>
          by_cases inBounds : index < elements.length
          · simp only [restSiteAt?, if_pos inBounds] at decoded
            obtain ⟨element, selectedElement, selectedInner⟩ :=
              Option.bind_eq_some_iff.mp decoded
            obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
              (restSiteAt? element path)
              (.collection kind (elements.take index) .hole
                (elements.drop (index + 1)) rest) selectedInner
            subst site
            have innerFilled := inductionHypothesis innerDecoded
            change inner.context.fill
              (.collection inner.kind inner.elements (some inner.name)) =
                element at innerFilled
            simp only [RestSite.push, RestSite.focus,
              OneHoleContext.fill_comp, OneHoleContext.fill]
            rw [innerFilled]
            rw [take_some_drop selectedElement]
          · by_cases isRest : index == elements.length && path.isEmpty
            · simp only [restSiteAt?, if_neg inBounds,
                if_pos isRest] at decoded
              cases rest with
              | none => simp at decoded
              | some name =>
                  simp only [Option.map_some, Option.some.injEq] at decoded
                  subst site
                  rfl
            · simp [restSiteAt?, inBounds, isRest] at decoded

/-- A decoded rest site is exactly the rest name read by the executable
occurrence-address reader, including nested rests. -/
theorem restSiteAt?_occurrenceAt?
    {pattern : Pattern} {path : List Nat} {site : RestSite}
    (decoded : restSiteAt? pattern path = some site) :
    occurrenceAt? pattern path = some site.name := by
  induction path generalizing pattern site with
  | nil =>
      cases pattern <;> simp [restSiteAt?] at decoded
  | cons index path inductionHypothesis =>
      cases pattern with
      | bvar _ => simp [restSiteAt?] at decoded
      | fvar _ => simp [restSiteAt?] at decoded
      | apply constructor arguments =>
          simp only [restSiteAt?] at decoded
          obtain ⟨argument, selectedArgument, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp decoded
          obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
            (restSiteAt? argument path)
            (.apply constructor (arguments.take index) .hole
              (arguments.drop (index + 1))) selectedInner
          subst site
          simpa [occurrenceAt?, selectedArgument, RestSite.push] using
            inductionHypothesis innerDecoded
      | lambda binder body =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path) (.lambda binder .hole) decoded
              subst site
              simpa [occurrenceAt?, RestSite.push] using
                inductionHypothesis innerDecoded
          | succ _ => simp [restSiteAt?] at decoded
      | multiLambda arity binders body =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path)
                (.multiLambda arity binders .hole) decoded
              subst site
              simpa [occurrenceAt?, RestSite.push] using
                inductionHypothesis innerDecoded
          | succ _ => simp [restSiteAt?] at decoded
      | subst body replacement =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path) (.substBody .hole replacement) decoded
              subst site
              simpa [occurrenceAt?, RestSite.push] using
                inductionHypothesis innerDecoded
          | succ index =>
              cases index with
              | zero =>
                  simp [restSiteAt?] at decoded
                  obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                    (restSiteAt? replacement path)
                    (.substReplacement body .hole) decoded
                  subst site
                  simpa [occurrenceAt?, RestSite.push] using
                    inductionHypothesis innerDecoded
              | succ _ => simp [restSiteAt?] at decoded
      | collection kind elements rest =>
          by_cases inBounds : index < elements.length
          · simp only [restSiteAt?, if_pos inBounds] at decoded
            obtain ⟨element, selectedElement, selectedInner⟩ :=
              Option.bind_eq_some_iff.mp decoded
            obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
              (restSiteAt? element path)
              (.collection kind (elements.take index) .hole
                (elements.drop (index + 1)) rest) selectedInner
            subst site
            simp only [occurrenceAt?, if_pos inBounds,
              selectedElement, Option.bind_some, RestSite.push]
            exact inductionHypothesis innerDecoded
          · by_cases isRest : index == elements.length && path.isEmpty
            · simp only [restSiteAt?, if_neg inBounds,
                if_pos isRest] at decoded
              cases rest with
              | none => simp at decoded
              | some name =>
                  simp only [Option.map_some, Option.some.injEq] at decoded
                  subst site
                  simp only [Bool.and_eq_true, beq_iff_eq,
                    List.isEmpty_iff] at isRest
                  obtain ⟨indexEq, pathEmpty⟩ := isRest
                  subst path
                  simp [occurrenceAt?, indexEq]
            · simp [restSiteAt?, inBounds, isRest] at decoded

/-- The collection rest inherits precisely the binders crossed on the path
to its enclosing collection. This is the same depth used by rule execution. -/
theorem restSiteAt?_depth
    {pattern : Pattern} {path : List Nat} {site : RestSite}
    (decoded : restSiteAt? pattern path = some site) (depth : Nat) :
    occurrenceDepthAt? pattern path depth =
      some (depth + binderCount site.context) := by
  induction path generalizing pattern site depth with
  | nil =>
      cases pattern <;> simp [restSiteAt?] at decoded
  | cons index path inductionHypothesis =>
      cases pattern with
      | bvar _ => simp [restSiteAt?] at decoded
      | fvar _ => simp [restSiteAt?] at decoded
      | apply constructor arguments =>
          simp only [restSiteAt?] at decoded
          obtain ⟨argument, selectedArgument, selectedInner⟩ :=
            Option.bind_eq_some_iff.mp decoded
          obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
            (restSiteAt? argument path)
            (.apply constructor (arguments.take index) .hole
              (arguments.drop (index + 1))) selectedInner
          subst site
          simp [occurrenceDepthAt?, selectedArgument, RestSite.push,
            OneHoleContext.comp, binderCount,
            inductionHypothesis innerDecoded depth]
      | lambda binder body =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path) (.lambda binder .hole) decoded
              subst site
              simpa [occurrenceDepthAt?, RestSite.push,
                OneHoleContext.comp, binderCount, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                inductionHypothesis innerDecoded (depth + 1)
          | succ _ => simp [restSiteAt?] at decoded
      | multiLambda arity binders body =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path)
                (.multiLambda arity binders .hole) decoded
              subst site
              simpa [occurrenceDepthAt?, RestSite.push,
                OneHoleContext.comp, binderCount, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                inductionHypothesis innerDecoded (depth + arity)
          | succ _ => simp [restSiteAt?] at decoded
      | subst body replacement =>
          cases index with
          | zero =>
              simp only [restSiteAt?] at decoded
              obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                (restSiteAt? body path) (.substBody .hole replacement) decoded
              subst site
              simpa [occurrenceDepthAt?, RestSite.push,
                OneHoleContext.comp, binderCount, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                inductionHypothesis innerDecoded (depth + 1)
          | succ index =>
              cases index with
              | zero =>
                  simp [restSiteAt?] at decoded
                  obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
                    (restSiteAt? replacement path)
                    (.substReplacement body .hole) decoded
                  subst site
                  simpa [occurrenceDepthAt?, RestSite.push,
                    OneHoleContext.comp, binderCount] using
                    inductionHypothesis innerDecoded depth
              | succ _ => simp [restSiteAt?] at decoded
      | collection kind elements rest =>
          by_cases inBounds : index < elements.length
          · simp only [restSiteAt?, if_pos inBounds] at decoded
            obtain ⟨element, selectedElement, selectedInner⟩ :=
              Option.bind_eq_some_iff.mp decoded
            obtain ⟨inner, innerDecoded, siteEq⟩ := pushed_some
              (restSiteAt? element path)
              (.collection kind (elements.take index) .hole
                (elements.drop (index + 1)) rest) selectedInner
            subst site
            simp only [occurrenceDepthAt?, if_pos inBounds,
              selectedElement, Option.bind_some]
            simpa [RestSite.push, OneHoleContext.comp, binderCount] using
              inductionHypothesis innerDecoded depth
          · by_cases isRest : index == elements.length && path.isEmpty
            · simp only [restSiteAt?, if_neg inBounds,
                if_pos isRest] at decoded
              cases rest with
              | none => simp at decoded
              | some name =>
                  simp only [Option.map_some, Option.some.injEq] at decoded
                  subst site
                  simp only [Bool.and_eq_true, beq_iff_eq,
                    List.isEmpty_iff] at isRest
                  obtain ⟨indexEq, pathEmpty⟩ := isRest
                  subst path
                  simp [occurrenceDepthAt?, indexEq, binderCount]
            · simp [restSiteAt?, inBounds, isRest] at decoded

/-- The two address decoders cover every occurrence accepted by the actual
rule reader. Ordinary free variables become term zippers; collection rests
become rest sites. No address is silently dropped at binder or collection
frames. -/
theorem occurrenceAt?_covered
    {pattern : Pattern} {path : List Nat} {name : String}
    (observed : occurrenceAt? pattern path = some name) :
    (∃ context, termZipperAt? pattern path = some (name, context)) ∨
      (∃ site, restSiteAt? pattern path = some site ∧ site.name = name) := by
  induction path generalizing pattern name with
  | nil =>
      cases pattern with
      | fvar actual =>
          simp only [occurrenceAt?, Option.some.injEq] at observed
          subst actual
          exact Or.inl ⟨.hole, by simp [termZipperAt?]⟩
      | bvar _ => simp [occurrenceAt?] at observed
      | apply _ _ => simp [occurrenceAt?] at observed
      | lambda _ _ => simp [occurrenceAt?] at observed
      | multiLambda _ _ _ => simp [occurrenceAt?] at observed
      | subst _ _ => simp [occurrenceAt?] at observed
      | collection _ _ _ => simp [occurrenceAt?] at observed
  | cons index path inductionHypothesis =>
      cases pattern with
      | bvar _ => simp [occurrenceAt?] at observed
      | fvar _ => simp [occurrenceAt?] at observed
      | apply constructor arguments =>
          simp only [occurrenceAt?] at observed
          obtain ⟨argument, selectedArgument, innerObserved⟩ :=
            Option.bind_eq_some_iff.mp observed
          rcases inductionHypothesis innerObserved with
            ⟨context, termDecoded⟩ | ⟨site, restDecoded, nameEq⟩
          · refine Or.inl ⟨.apply constructor (arguments.take index)
              context (arguments.drop (index + 1)), ?_⟩
            simp [termZipperAt?, selectedArgument, termDecoded]
          · refine Or.inr ⟨site.push
              (.apply constructor (arguments.take index) .hole
                (arguments.drop (index + 1))), ?_, ?_⟩
            · simp [restSiteAt?, selectedArgument, restDecoded]
            · exact nameEq
      | lambda binder body =>
          cases index with
          | zero =>
              simp only [occurrenceAt?] at observed
              rcases inductionHypothesis observed with
                ⟨context, termDecoded⟩ | ⟨site, restDecoded, nameEq⟩
              · exact Or.inl ⟨.lambda binder context,
                  by simp [termZipperAt?, termDecoded]⟩
              · exact Or.inr ⟨site.push (.lambda binder .hole),
                  by simp [restSiteAt?, restDecoded], nameEq⟩
          | succ _ => simp [occurrenceAt?] at observed
      | multiLambda arity binders body =>
          cases index with
          | zero =>
              simp only [occurrenceAt?] at observed
              rcases inductionHypothesis observed with
                ⟨context, termDecoded⟩ | ⟨site, restDecoded, nameEq⟩
              · exact Or.inl ⟨.multiLambda arity binders context,
                  by simp [termZipperAt?, termDecoded]⟩
              · exact Or.inr ⟨site.push
                  (.multiLambda arity binders .hole),
                  by simp [restSiteAt?, restDecoded], nameEq⟩
          | succ _ => simp [occurrenceAt?] at observed
      | subst body replacement =>
          cases index with
          | zero =>
              simp only [occurrenceAt?] at observed
              rcases inductionHypothesis observed with
                ⟨context, termDecoded⟩ | ⟨site, restDecoded, nameEq⟩
              · exact Or.inl ⟨.substBody context replacement,
                  by simp [termZipperAt?, termDecoded]⟩
              · exact Or.inr ⟨site.push (.substBody .hole replacement),
                  by simp [restSiteAt?, restDecoded], nameEq⟩
          | succ index =>
              cases index with
              | zero =>
                  simp [occurrenceAt?] at observed
                  rcases inductionHypothesis observed with
                    ⟨context, termDecoded⟩ | ⟨site, restDecoded, nameEq⟩
                  · exact Or.inl ⟨.substReplacement body context,
                      by simp [termZipperAt?, termDecoded]⟩
                  · exact Or.inr ⟨site.push
                      (.substReplacement body .hole),
                      by simp [restSiteAt?, restDecoded], nameEq⟩
              | succ _ => simp [occurrenceAt?] at observed
      | collection kind elements rest =>
          by_cases inBounds : index < elements.length
          · simp only [occurrenceAt?, if_pos inBounds] at observed
            obtain ⟨element, selectedElement, innerObserved⟩ :=
              Option.bind_eq_some_iff.mp observed
            have elementEq : element = elements[index] := by
              have actual := List.getElem?_eq_getElem inBounds
              rw [selectedElement] at actual
              exact Option.some.inj actual
            rcases inductionHypothesis innerObserved with
              ⟨context, termDecoded⟩ | ⟨site, restDecoded, nameEq⟩
            · refine Or.inl ⟨.collection kind (elements.take index)
                context (elements.drop (index + 1)) rest, ?_⟩
              simp [termZipperAt?, inBounds, ← elementEq, termDecoded]
            · refine Or.inr ⟨site.push
                (.collection kind (elements.take index) .hole
                  (elements.drop (index + 1)) rest), ?_, ?_⟩
              · simp [restSiteAt?, inBounds, ← elementEq, restDecoded]
              · exact nameEq
          · by_cases isRest : index == elements.length && path.isEmpty
            · simp only [occurrenceAt?, if_neg inBounds,
                if_pos isRest] at observed
              refine Or.inr ⟨{ name, kind, elements, context := .hole },
                ?_, rfl⟩
              simp [restSiteAt?, inBounds, isRest, observed]
            · simp [occurrenceAt?, inBounds, isRest] at observed

end Mettapedia.OSLF.MeTTaIL.RestOccurrenceAddress
