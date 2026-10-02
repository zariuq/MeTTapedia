import Mettapedia.OSLF.Framework.RuleInstanceSteps

/-!
# Steps of a rule that rewrites two members of a bag

A rule whose left side is a bag pattern with two members and a rest variable
selects two members of a bag, wherever they stand, and keeps the others.  It
is how two things of one sort meet in a language definition: an input and an
output in a process calculus, a table row and a configuration in a universal
machine.

The matcher searches the bag and merges the bindings of the two members, so
a variable that occurs in both must be bound to the same term.  When the two
member patterns are matched exactly, this module turns that search into a
statement about instances.

* `bagPair_of_mem_matchPattern`: a match selects two positions, the two
  member patterns under the bindings are the members there, and the rest
  variable is bound to the bag of the others.
* `exists_mem_matchPattern_bagPair`: conversely, bindings under which the two
  member patterns are members at two positions give a match with the same
  three properties.
* `step_of_bagPair`: such bindings give a step to the bag whose first two
  members are the right-side patterns under those bindings.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.Framework.PredFiniteSufficient

/-- What the bindings of a bag match with two members satisfy. -/
private theorem pair_spec {first second : Pattern} {rest : String} {elements : List Pattern}
    {i j : Nat} {hi : i < elements.length} {hj : j < (elements.eraseIdx i).length}
    {firstBindings secondBindings merged bindings : Bindings}
    (firstExact : isMatchCorrectAux first = true) (secondExact : isMatchCorrectAux second = true)
    (firstMatch : MatchRel first elements[i] firstBindings)
    (secondMatch : MatchRel second (elements.eraseIdx i)[j] secondBindings)
    (mergeRest : mergeBindings secondBindings
      [(rest, .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none)] = some merged)
    (mergeFirst : mergeBindings firstBindings merged = some bindings) :
    applyBindings bindings first = elements[i] ∧
      applyBindings bindings second = (elements.eraseIdx i)[j] ∧
        bindings.find? (·.1 == rest) =
          some (rest, .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none) := by
  refine ⟨?_, ?_, ?_⟩
  · exact matchRel_correct_of_extends firstMatch firstExact fun _ _ found =>
      mergeBindings_subsumed_left mergeFirst found
  · exact matchRel_correct_of_extends secondMatch secondExact fun _ _ found =>
      mergeBindings_subsumed_right mergeFirst (mergeBindings_subsumed_left mergeRest found)
  · exact mergeBindings_subsumed_right mergeFirst
      (mergeBindings_subsumed_right mergeRest (by simp))

/-- **A match of a bag pattern with two members selects two positions.**  The
member patterns under the bindings are the members at those positions, and
the rest variable is bound to the bag of the others. -/
theorem bagPair_of_mem_matchPattern {first second : Pattern} {rest : String}
    {elements : List Pattern} {tail : Option String} {bindings : Bindings}
    (firstExact : isMatchCorrectAux first = true) (secondExact : isMatchCorrectAux second = true)
    (matched : bindings ∈ matchPattern (.collection .hashBag [first, second] (some rest))
      (.collection .hashBag elements tail)) :
    ∃ (i : Nat) (hi : i < elements.length) (j : Nat) (hj : j < (elements.eraseIdx i).length),
      applyBindings bindings first = elements[i] ∧
        applyBindings bindings second = (elements.eraseIdx i)[j] ∧
          bindings.find? (·.1 == rest) =
            some (rest, .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none) := by
  have relation := matchPattern_iff_matchRel.mp matched
  cases relation with
  | collection notVector bagRelation =>
      cases bagRelation with
      | cons i hi firstMatch restRelation mergeFirst =>
          cases restRelation with
          | cons j hj secondMatch lastRelation mergeRest =>
              cases lastRelation with
              | nilRest =>
                  exact ⟨i, hi, j, hj,
                    pair_spec firstExact secondExact firstMatch secondMatch mergeRest mergeFirst⟩

/-- **Bindings under which the two member patterns are members of the bag
give a match.**  The match need not be the given bindings; it has the same
members and the same rest. -/
theorem exists_mem_matchPattern_bagPair {first second : Pattern} {rest : String}
    (firstExact : isMatchCorrectAux first = true) (secondExact : isMatchCorrectAux second = true)
    (ambient : Bindings) {elements : List Pattern} {i j : Nat}
    (hi : i < elements.length) (hj : j < (elements.eraseIdx i).length)
    (atFirst : applyBindings ambient first = elements[i])
    (atSecond : applyBindings ambient second = (elements.eraseIdx i)[j])
    (restBound : lookupOrFvar ambient rest =
      .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none) :
    ∃ bindings ∈ matchPattern (.collection .hashBag [first, second] (some rest))
        (.collection .hashBag elements none),
      applyBindings bindings first = elements[i] ∧
        applyBindings bindings second = (elements.eraseIdx i)[j] ∧
          bindings.find? (·.1 == rest) =
            some (rest, .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none) := by
  obtain ⟨firstBindings, firstMember, firstValued⟩ :=
    matchPattern_applyBindings_complete (bs := ambient) firstExact
  obtain ⟨secondBindings, secondMember, secondValued⟩ :=
    matchPattern_applyBindings_complete (bs := ambient) secondExact
  rw [atFirst] at firstMember
  rw [atSecond] at secondMember
  have restValued : BindingsValued
      [(rest, Pattern.collection .hashBag ((elements.eraseIdx i).eraseIdx j) none)]
      (lookupOrFvar ambient) := by
    intro name value member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact restBound.symm
  obtain ⟨merged, mergeRest, mergedValued⟩ :=
    mergeBindings_some_of_valued secondBindings _ _ secondValued restValued
  obtain ⟨bindings, mergeFirst, -⟩ :=
    mergeBindings_some_of_valued firstBindings merged _ firstValued mergedValued
  have firstMatch := matchPattern_iff_matchRel.mp firstMember
  have secondMatch := matchPattern_iff_matchRel.mp secondMember
  exact ⟨bindings,
    matchPattern_iff_matchRel.mpr
      (.collection (by decide)
        (.cons i hi firstMatch (.cons j hj secondMatch .nilRest mergeRest) mergeFirst)),
    pair_spec firstExact secondExact firstMatch secondMatch mergeRest mergeFirst⟩

/-- A bag pattern with two members under bindings whose rest variable is bound
to a bag: the two members first, then the rest. -/
theorem applyBindings_bagPair {first second : Pattern} {rest : String} {bindings : Bindings}
    {others : List Pattern}
    (restBound : bindings.find? (·.1 == rest) = some (rest, .collection .hashBag others none)) :
    applyBindings bindings (.collection .hashBag [first, second] (some rest)) =
      .collection .hashBag (applyBindings bindings first :: applyBindings bindings second ::
        others) none := by
  simp [applyBindings, restBound]

/-- **Every instance of a rule that rewrites two members of a bag is a
step.**  The two members may stand anywhere in the bag; the reduct has the
rewritten members first and then the others. -/
theorem step_of_bagPair {relEnv : RelationEnv} {lang : LanguageDef} (plain : PlainRules lang)
    {rule : RewriteRule} (member : rule ∈ lang.rewrites)
    {first second newFirst newSecond : Pattern} {rest : String}
    (leftShape : rule.left = .collection .hashBag [first, second] (some rest))
    (rightShape : rule.right = .collection .hashBag [newFirst, newSecond] (some rest))
    (firstExact : isMatchCorrectAux first = true) (secondExact : isMatchCorrectAux second = true)
    (newFirstExact : isMatchCorrectAux newFirst = true)
    (newSecondExact : isMatchCorrectAux newSecond = true)
    (bound : ∀ name ∈ freeVars newFirst ++ freeVars newSecond,
      name ∈ freeVars first ++ freeVars second)
    (ambient : Bindings) {elements : List Pattern} {i j : Nat}
    (hi : i < elements.length) (hj : j < (elements.eraseIdx i).length)
    (atFirst : applyBindings ambient first = elements[i])
    (atSecond : applyBindings ambient second = (elements.eraseIdx i)[j])
    (restBound : lookupOrFvar ambient rest =
      .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none) :
    Step (engineBasePremises relEnv) lang (.collection .hashBag elements none)
      (.collection .hashBag (applyBindings ambient newFirst :: applyBindings ambient newSecond ::
        (elements.eraseIdx i).eraseIdx j) none) := by
  obtain ⟨bindings, matched, foundFirst, foundSecond, foundRest⟩ :=
    exists_mem_matchPattern_bagPair firstExact secondExact ambient hi hj atFirst atSecond
      restBound
  have agree : ∀ name ∈ freeVars first ++ freeVars second,
      lookupOrFvar bindings name = lookupOrFvar ambient name := by
    intro name inLeft
    rcases List.mem_append.mp inLeft with inFirst | inSecond
    · exact applyBindings_injective_isMatchCorrect firstExact (foundFirst.trans atFirst.symm)
        name inFirst
    · exact applyBindings_injective_isMatchCorrect secondExact
        (foundSecond.trans atSecond.symm) name inSecond
  refine (step_iff_exists_match plain).mpr
    ⟨rule, member, bindings, by rw [leftShape]; exact matched, ?_⟩
  rw [rightShape, applyBindings_bagPair foundRest,
    applyBindings_eq_of_agree_isMatchCorrect newFirstExact fun name inNew =>
      agree name (bound name (List.mem_append_left _ inNew)),
    applyBindings_eq_of_agree_isMatchCorrect newSecondExact fun name inNew =>
      agree name (bound name (List.mem_append_right _ inNew))]

end Mettapedia.OSLF.MeTTaIL.ContextualStep
