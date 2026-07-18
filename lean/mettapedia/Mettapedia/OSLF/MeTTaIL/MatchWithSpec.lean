import Mettapedia.OSLF.MeTTaIL.Match
import Mathlib.Data.List.Enum

/-!
# Relational specification of equivalence-parameterized matching

The executable matcher accepts a Boolean relation only when two partial
binding sets assign the same metavariable.  The relations below specify its
recursive search independently of list enumeration and prove both directions
of agreement with `matchPatternWith`, `matchArgsWith`, and `matchBagWith`.
-/

namespace Mettapedia.OSLF.MeTTaIL.MatchWithSpec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

mutual
  inductive MatchRelWith (equivalent : Pattern → Pattern → Bool) :
      Pattern → Pattern → Bindings → Prop where
    | fvar : MatchRelWith equivalent (.fvar name) term [(name, term)]
    | bvar : MatchRelWith equivalent (.bvar index) (.bvar index) []
    | apply :
        MatchArgsRelWith equivalent patternArguments termArguments bindings →
        patternArguments.length = termArguments.length →
        MatchRelWith equivalent
          (.apply constructor patternArguments) (.apply constructor termArguments) bindings
    | lambda :
        MatchRelWith equivalent patternBody termBody bindings →
        MatchRelWith equivalent
          (.lambda patternName patternBody) (.lambda termName termBody) bindings
    | multiLambda :
        MatchRelWith equivalent patternBody termBody bindings →
        MatchRelWith equivalent
          (.multiLambda arity patternNames patternBody)
          (.multiLambda arity termNames termBody) bindings
    | collection :
        MatchBagRelWith equivalent patternElements rest collectionType termElements bindings →
        MatchRelWith equivalent
          (.collection collectionType patternElements rest)
          (.collection collectionType termElements termRest) bindings
    | subst :
        MatchRelWith equivalent patternBody termBody bodyBindings →
        MatchRelWith equivalent patternReplacement termReplacement replacementBindings →
        mergeBindingsWith equivalent bodyBindings replacementBindings = some bindings →
        MatchRelWith equivalent
          (.subst patternBody patternReplacement)
          (.subst termBody termReplacement) bindings

  inductive MatchArgsRelWith (equivalent : Pattern → Pattern → Bool) :
      List Pattern → List Pattern → Bindings → Prop where
    | nil : MatchArgsRelWith equivalent [] [] []
    | cons :
        MatchRelWith equivalent pattern term headBindings →
        MatchArgsRelWith equivalent patterns terms tailBindings →
        mergeBindingsWith equivalent headBindings tailBindings = some bindings →
        MatchArgsRelWith equivalent
          (pattern :: patterns) (term :: terms) bindings

  inductive MatchBagRelWith (equivalent : Pattern → Pattern → Bool) :
      List Pattern → Option String → CollType → List Pattern → Bindings → Prop where
    | nilNoRest : MatchBagRelWith equivalent [] none collectionType [] []
    | nilRest :
        MatchBagRelWith equivalent [] (some restName) collectionType termElements
          [(restName, .collection collectionType termElements none)]
    | cons :
        (index : Nat) → (indexBound : index < termElements.length) →
        MatchRelWith equivalent pattern (termElements[index]) headBindings →
        MatchBagRelWith equivalent patterns rest collectionType
          (termElements.eraseIdx index) tailBindings →
        mergeBindingsWith equivalent headBindings tailBindings = some bindings →
        MatchBagRelWith equivalent (pattern :: patterns) rest collectionType
          termElements bindings
end

private theorem lt_length_of_mem_zipIdx {α : Type*} {values : List α}
    {value : α} {index : Nat} (membership : (value, index) ∈ values.zipIdx) :
    index < values.length := by
  have key := List.exists_mem_zipIdx'.mp
    (show ∃ entry ∈ values.zipIdx, entry = (value, index) from
      ⟨_, membership, rfl⟩)
  obtain ⟨foundIndex, foundBound, pairEquality⟩ := key
  have : foundIndex = index := (Prod.ext_iff.mp pairEquality).2
  subst this
  exact foundBound

private theorem eq_getElem_of_mem_zipIdx {α : Type*} {values : List α}
    {value : α} {index : Nat} (membership : (value, index) ∈ values.zipIdx)
    (indexBound : index < values.length) : value = values[index] := by
  have key := List.exists_mem_zipIdx'.mp
    (show ∃ entry ∈ values.zipIdx, entry = (value, index) from
      ⟨_, membership, rfl⟩)
  obtain ⟨foundIndex, _, pairEquality⟩ := key
  have indexEquality : foundIndex = index := (Prod.ext_iff.mp pairEquality).2
  subst indexEquality
  exact (Prod.ext_iff.mp pairEquality).1.symm

private theorem mem_zipIdx_of_lt {α : Type*} (values : List α)
    (index : Nat) (indexBound : index < values.length) :
    (values[index], index) ∈ values.zipIdx := by
  have zippedBound : index < values.zipIdx.length := by
    rw [List.length_zipIdx]
    exact indexBound
  have getEquality : values.zipIdx[index] = (values[index], index) := by
    simp [List.getElem_zipIdx]
  rw [← getEquality]
  exact List.getElem_mem zippedBound

private theorem eq_nil_of_isEmpty {α : Type*} {values : List α}
    (empty : values.isEmpty = true) : values = [] := by
  cases values with
  | nil => rfl
  | cons head tail => simp [List.isEmpty] at empty

private theorem sizeOf_pattern_pos (pattern : Pattern) : 0 < sizeOf pattern := by
  cases pattern <;> simp_wf

private theorem sizeOf_body_lt_lambda (name : Option String) (body : Pattern) :
    sizeOf body < sizeOf (Pattern.lambda name body) := by simp_wf

private theorem sizeOf_body_lt_multiLambda
    (arity : Nat) (names : List String) (body : Pattern) :
    sizeOf body < sizeOf (Pattern.multiLambda arity names body) := by simp_wf

private theorem sizeOf_args_lt_apply (constructor : String) (arguments : List Pattern) :
    sizeOf arguments < sizeOf (Pattern.apply constructor arguments) := by simp_wf

private theorem sizeOf_elems_lt_collection (collectionType : CollType)
    (elements : List Pattern) (rest : Option String) :
    sizeOf elements < sizeOf (Pattern.collection collectionType elements rest) := by
  simp_wf
  omega

private theorem sizeOf_body_lt_subst (body replacement : Pattern) :
    sizeOf body < sizeOf (Pattern.subst body replacement) := by
  simp_wf
  omega

private theorem sizeOf_replacement_lt_subst (body replacement : Pattern) :
    sizeOf replacement < sizeOf (Pattern.subst body replacement) := by simp_wf

private theorem sizeOf_head_lt_cons (pattern : Pattern) (patterns : List Pattern) :
    sizeOf pattern < sizeOf (pattern :: patterns) := by
  simp_wf
  omega

private theorem sizeOf_tail_lt_cons (pattern : Pattern) (patterns : List Pattern) :
    sizeOf patterns < sizeOf (pattern :: patterns) := by simp_wf

private theorem sizeOf_cons_pos (pattern : Pattern) (patterns : List Pattern) :
    0 < sizeOf (pattern :: patterns) := by
  have patternPositive := sizeOf_pattern_pos pattern
  have headSmaller := sizeOf_head_lt_cons pattern patterns
  omega

/-! ## Executable soundness -/

private theorem sound_all (equivalent : Pattern → Pattern → Bool) (bound : Nat) :
    (∀ pattern term bindings, sizeOf pattern ≤ bound →
      bindings ∈ matchPatternWith equivalent pattern term →
      MatchRelWith equivalent pattern term bindings) ∧
    (∀ patterns terms bindings, sizeOf patterns ≤ bound →
      bindings ∈ matchArgsWith equivalent patterns terms →
      MatchArgsRelWith equivalent patterns terms bindings) ∧
    (∀ patterns rest collectionType terms bindings, sizeOf patterns ≤ bound →
      bindings ∈ matchBagWith equivalent patterns rest collectionType terms →
      MatchBagRelWith equivalent patterns rest collectionType terms bindings) := by
  induction bound with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro pattern term bindings sizeBound membership
        exact absurd sizeBound (by have := sizeOf_pattern_pos pattern; omega)
      · intro patterns terms bindings sizeBound membership
        match patterns, terms with
        | [], [] =>
            simp only [matchArgsWith, List.mem_singleton] at membership
            subst membership
            exact .nil
        | [], _ :: _ => simp [matchArgsWith] at membership
        | _ :: _, [] => simp [matchArgsWith] at membership
        | pattern :: patterns, _ :: _ =>
            exact absurd sizeBound (by
              have positive := sizeOf_cons_pos pattern patterns
              omega)
      · intro patterns rest collectionType terms bindings sizeBound membership
        match patterns with
        | [] =>
            unfold matchBagWith at membership
            match rest with
            | none =>
                dsimp only at membership
                split at membership
                next empty =>
                  simp only [List.mem_singleton] at membership
                  subst membership
                  have termsEmpty := eq_nil_of_isEmpty empty
                  subst termsEmpty
                  exact .nilNoRest
                next => simp at membership
            | some restName =>
                simp only [List.mem_singleton] at membership
                subst membership
                exact .nilRest
        | pattern :: patterns =>
            exact absurd sizeBound (by
              have positive := sizeOf_cons_pos pattern patterns
              omega)
  | succ previousBound inductionHypothesis =>
      obtain ⟨patternInduction, argumentsInduction, bagInduction⟩ := inductionHypothesis
      refine ⟨?_, ?_, ?_⟩
      · intro pattern term bindings sizeBound membership
        match pattern, term with
        | .fvar name, term =>
            simp only [matchPatternWith, List.mem_singleton] at membership
            subst membership
            exact .fvar
        | .bvar left, .bvar right =>
            unfold matchPatternWith at membership
            split at membership
            next equality =>
              have indexEquality := beq_iff_eq.mp equality
              subst indexEquality
              simp only [List.mem_singleton] at membership
              subst membership
              exact .bvar
            next => simp at membership
        | .bvar _, .fvar _ | .bvar _, .apply _ _ | .bvar _, .lambda _ _
        | .bvar _, .multiLambda _ _ _ | .bvar _, .subst _ _
        | .bvar _, .collection _ _ _ => simp [matchPatternWith] at membership
        | .apply leftConstructor leftArguments,
            .apply rightConstructor rightArguments =>
            unfold matchPatternWith at membership
            split at membership
            next condition =>
              have ⟨constructorEquality, lengthEquality⟩ :=
                Bool.and_eq_true_iff.mp condition
              have constructorsEqual : leftConstructor = rightConstructor :=
                beq_iff_eq.mp constructorEquality
              have lengthsEqual : leftArguments.length = rightArguments.length :=
                beq_iff_eq.mp lengthEquality
              subst constructorsEqual
              exact .apply
                (argumentsInduction leftArguments rightArguments bindings
                  (by have := sizeOf_args_lt_apply leftConstructor leftArguments; omega)
                  membership)
                lengthsEqual
            next => simp at membership
        | .apply _ _, .bvar _ | .apply _ _, .fvar _ | .apply _ _, .lambda _ _
        | .apply _ _, .multiLambda _ _ _ | .apply _ _, .subst _ _
        | .apply _ _, .collection _ _ _ => simp [matchPatternWith] at membership
        | .lambda patternName patternBody, .lambda termName termBody =>
            unfold matchPatternWith at membership
            exact .lambda
              (patternInduction patternBody termBody bindings
                (by have := sizeOf_body_lt_lambda patternName patternBody; omega)
                membership)
        | .lambda _ _, .bvar _ | .lambda _ _, .fvar _ | .lambda _ _, .apply _ _
        | .lambda _ _, .multiLambda _ _ _ | .lambda _ _, .subst _ _
        | .lambda _ _, .collection _ _ _ => simp [matchPatternWith] at membership
        | .multiLambda patternArity patternNames patternBody,
            .multiLambda termArity termNames termBody =>
            unfold matchPatternWith at membership
            split at membership
            next equality =>
              have aritiesEqual := beq_iff_eq.mp equality
              subst aritiesEqual
              exact .multiLambda
                (patternInduction patternBody termBody bindings
                  (by
                    have := sizeOf_body_lt_multiLambda
                      patternArity patternNames patternBody
                    omega)
                  membership)
            next => simp at membership
        | .multiLambda _ _ _, .bvar _ | .multiLambda _ _ _, .fvar _
        | .multiLambda _ _ _, .apply _ _ | .multiLambda _ _ _, .lambda _ _
        | .multiLambda _ _ _, .subst _ _ | .multiLambda _ _ _, .collection _ _ _ =>
            simp [matchPatternWith] at membership
        | .collection leftType patternElements rest,
            .collection rightType termElements termRest =>
            unfold matchPatternWith at membership
            split at membership
            next equality =>
              have typesEqual := beq_iff_eq.mp equality
              subst typesEqual
              exact .collection
                (bagInduction patternElements rest leftType termElements bindings
                  (by
                    have := sizeOf_elems_lt_collection leftType patternElements rest
                    omega)
                  membership)
            next => simp at membership
        | .collection _ _ _, .bvar _ | .collection _ _ _, .fvar _
        | .collection _ _ _, .apply _ _ | .collection _ _ _, .lambda _ _
        | .collection _ _ _, .multiLambda _ _ _ | .collection _ _ _, .subst _ _ =>
            simp [matchPatternWith] at membership
        | .subst patternBody patternReplacement, .subst termBody termReplacement =>
            unfold matchPatternWith at membership
            rw [List.mem_flatMap] at membership
            obtain ⟨bodyBindings, bodyMembership, replacementSearch⟩ := membership
            rw [List.mem_filterMap] at replacementSearch
            obtain ⟨replacementBindings, replacementMembership, mergeEquality⟩ :=
              replacementSearch
            exact .subst
              (patternInduction patternBody termBody bodyBindings
                (by have := sizeOf_body_lt_subst patternBody patternReplacement; omega)
                bodyMembership)
              (patternInduction patternReplacement termReplacement replacementBindings
                (by
                  have := sizeOf_replacement_lt_subst patternBody patternReplacement
                  omega)
                replacementMembership)
              mergeEquality
        | .subst _ _, .bvar _ | .subst _ _, .fvar _ | .subst _ _, .apply _ _
        | .subst _ _, .lambda _ _ | .subst _ _, .multiLambda _ _ _
        | .subst _ _, .collection _ _ _ => simp [matchPatternWith] at membership
      · intro patterns terms bindings sizeBound membership
        match patterns, terms with
        | [], [] =>
            simp only [matchArgsWith, List.mem_singleton] at membership
            subst membership
            exact .nil
        | [], _ :: _ => simp [matchArgsWith] at membership
        | _ :: _, [] => simp [matchArgsWith] at membership
        | pattern :: patterns, term :: terms =>
            unfold matchArgsWith at membership
            rw [List.mem_flatMap] at membership
            obtain ⟨headBindings, headMembership, tailSearch⟩ := membership
            rw [List.mem_filterMap] at tailSearch
            obtain ⟨tailBindings, tailMembership, mergeEquality⟩ := tailSearch
            exact .cons
              (patternInduction pattern term headBindings
                (by have := sizeOf_head_lt_cons pattern patterns; omega)
                headMembership)
              (argumentsInduction patterns terms tailBindings
                (by have := sizeOf_tail_lt_cons pattern patterns; omega)
                tailMembership)
              mergeEquality
      · intro patterns rest collectionType terms bindings sizeBound membership
        match patterns with
        | [] =>
            unfold matchBagWith at membership
            match rest with
            | none =>
                dsimp only at membership
                split at membership
                next empty =>
                  simp only [List.mem_singleton] at membership
                  subst membership
                  have termsEmpty := eq_nil_of_isEmpty empty
                  subst termsEmpty
                  exact .nilNoRest
                next => simp at membership
            | some restName =>
                simp only [List.mem_singleton] at membership
                subst membership
                exact .nilRest
        | pattern :: patterns =>
            unfold matchBagWith at membership
            rw [List.mem_flatMap] at membership
            obtain ⟨⟨term, index⟩, zippedMembership, headSearch⟩ := membership
            rw [List.mem_flatMap] at headSearch
            obtain ⟨headBindings, headMembership, tailSearch⟩ := headSearch
            rw [List.mem_filterMap] at tailSearch
            obtain ⟨tailBindings, tailMembership, mergeEquality⟩ := tailSearch
            have indexBound := lt_length_of_mem_zipIdx zippedMembership
            have termEquality := eq_getElem_of_mem_zipIdx zippedMembership indexBound
            subst termEquality
            exact .cons index indexBound
              (patternInduction pattern terms[index] headBindings
                (by have := sizeOf_head_lt_cons pattern patterns; omega)
                headMembership)
              (bagInduction patterns rest collectionType (terms.eraseIdx index) tailBindings
                (by have := sizeOf_tail_lt_cons pattern patterns; omega)
                tailMembership)
              mergeEquality

theorem matchPatternWith_sound {equivalent : Pattern → Pattern → Bool}
    {pattern term : Pattern} {bindings : Bindings}
    (membership : bindings ∈ matchPatternWith equivalent pattern term) :
    MatchRelWith equivalent pattern term bindings :=
  (sound_all equivalent (sizeOf pattern)).1 pattern term bindings (Nat.le_refl _) membership

theorem matchArgsWith_sound {equivalent : Pattern → Pattern → Bool}
    {patterns terms : List Pattern} {bindings : Bindings}
    (membership : bindings ∈ matchArgsWith equivalent patterns terms) :
    MatchArgsRelWith equivalent patterns terms bindings :=
  (sound_all equivalent (sizeOf patterns)).2.1
    patterns terms bindings (Nat.le_refl _) membership

theorem matchBagWith_sound {equivalent : Pattern → Pattern → Bool}
    {patterns : List Pattern} {rest : Option String} {collectionType : CollType}
    {terms : List Pattern} {bindings : Bindings}
    (membership :
      bindings ∈ matchBagWith equivalent patterns rest collectionType terms) :
    MatchBagRelWith equivalent patterns rest collectionType terms bindings :=
  (sound_all equivalent (sizeOf patterns)).2.2
    patterns rest collectionType terms bindings (Nat.le_refl _) membership

/-! ## Relational completeness -/

private theorem complete_all (equivalent : Pattern → Pattern → Bool) (bound : Nat) :
    (∀ pattern term bindings, sizeOf pattern ≤ bound →
      MatchRelWith equivalent pattern term bindings →
      bindings ∈ matchPatternWith equivalent pattern term) ∧
    (∀ patterns terms bindings, sizeOf patterns ≤ bound →
      MatchArgsRelWith equivalent patterns terms bindings →
      bindings ∈ matchArgsWith equivalent patterns terms) ∧
    (∀ patterns rest collectionType terms bindings, sizeOf patterns ≤ bound →
      MatchBagRelWith equivalent patterns rest collectionType terms bindings →
      bindings ∈ matchBagWith equivalent patterns rest collectionType terms) := by
  induction bound with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro pattern term bindings sizeBound relation
        exact absurd sizeBound (by have := sizeOf_pattern_pos pattern; omega)
      · intro patterns terms bindings sizeBound relation
        cases relation with
        | nil => simp [matchArgsWith]
        | cons headRelation tailRelation mergeEquality =>
          rename_i pattern term headBindings patterns terms tailBindings
          exact absurd sizeBound (by
            have positive := sizeOf_cons_pos pattern patterns
            omega)
      · intro patterns rest collectionType terms bindings sizeBound relation
        cases relation with
        | nilNoRest => simp [matchBagWith, List.isEmpty]
        | nilRest => simp [matchBagWith]
        | cons index indexBound headRelation tailRelation mergeEquality =>
          rename_i pattern headBindings patterns tailBindings
          exact absurd sizeBound (by
            have positive := sizeOf_cons_pos pattern patterns
            omega)
  | succ previousBound inductionHypothesis =>
      obtain ⟨patternInduction, argumentsInduction, bagInduction⟩ := inductionHypothesis
      refine ⟨?_, ?_, ?_⟩
      · intro pattern term bindings sizeBound relation
        cases relation with
        | fvar => simp [matchPatternWith]
        | bvar => simp [matchPatternWith]
        | apply argumentsRelation lengthEquality =>
            rename_i patternArguments termArguments constructor
            unfold matchPatternWith
            simp only [beq_self_eq_true, beq_iff_eq.mpr lengthEquality,
              Bool.true_and, ↓reduceIte]
            exact argumentsInduction patternArguments termArguments _
              (by have := sizeOf_args_lt_apply constructor patternArguments; omega)
              argumentsRelation
        | lambda bodyRelation =>
            rename_i patternBody termBody patternName termName
            unfold matchPatternWith
            exact patternInduction patternBody termBody _
              (by have := sizeOf_body_lt_lambda patternName patternBody; omega)
              bodyRelation
        | multiLambda bodyRelation =>
            rename_i patternBody termBody arity patternNames termNames
            unfold matchPatternWith
            simp only [beq_self_eq_true, ↓reduceIte]
            exact patternInduction patternBody termBody _
              (by
                have := sizeOf_body_lt_multiLambda arity patternNames patternBody
                omega)
              bodyRelation
        | collection bagRelation =>
            rename_i patternElements rest collectionType termElements termRest
            unfold matchPatternWith
            simp only [beq_self_eq_true, ↓reduceIte]
            exact bagInduction patternElements rest collectionType termElements _
              (by
                have := sizeOf_elems_lt_collection collectionType patternElements rest
                omega)
              bagRelation
        | subst bodyRelation replacementRelation mergeEquality =>
            rename_i patternBody termBody bodyBindings patternReplacement
              termReplacement replacementBindings
            unfold matchPatternWith
            rw [List.mem_flatMap]
            exact ⟨bodyBindings,
              patternInduction patternBody termBody bodyBindings
                (by have := sizeOf_body_lt_subst patternBody patternReplacement; omega)
                bodyRelation,
              List.mem_filterMap.mpr
                ⟨replacementBindings,
                  patternInduction patternReplacement termReplacement replacementBindings
                    (by
                      have := sizeOf_replacement_lt_subst patternBody patternReplacement
                      omega)
                    replacementRelation,
                  mergeEquality⟩⟩
      · intro patterns terms bindings sizeBound relation
        cases relation with
        | nil => simp [matchArgsWith]
        | cons headRelation tailRelation mergeEquality =>
            rename_i pattern term headBindings patterns terms tailBindings
            unfold matchArgsWith
            rw [List.mem_flatMap]
            exact ⟨headBindings,
              patternInduction pattern term headBindings
                (by have := sizeOf_head_lt_cons pattern patterns; omega)
                headRelation,
              List.mem_filterMap.mpr
                ⟨tailBindings,
                  argumentsInduction patterns terms tailBindings
                    (by have := sizeOf_tail_lt_cons pattern patterns; omega)
                    tailRelation,
                  mergeEquality⟩⟩
      · intro patterns rest collectionType terms bindings sizeBound relation
        cases relation with
        | nilNoRest => simp [matchBagWith, List.isEmpty]
        | nilRest => simp [matchBagWith]
        | cons index indexBound headRelation tailRelation mergeEquality =>
            rename_i pattern headBindings patterns tailBindings
            unfold matchBagWith
            rw [List.mem_flatMap]
            refine ⟨(terms[index], index), mem_zipIdx_of_lt terms index indexBound, ?_⟩
            rw [List.mem_flatMap]
            exact ⟨headBindings,
              patternInduction pattern terms[index] headBindings
                (by have := sizeOf_head_lt_cons pattern patterns; omega)
                headRelation,
              List.mem_filterMap.mpr
                ⟨tailBindings,
                  bagInduction patterns rest collectionType (terms.eraseIdx index) tailBindings
                    (by have := sizeOf_tail_lt_cons pattern patterns; omega)
                    tailRelation,
                  mergeEquality⟩⟩

theorem matchRelWith_complete {equivalent : Pattern → Pattern → Bool}
    {pattern term : Pattern} {bindings : Bindings}
    (relation : MatchRelWith equivalent pattern term bindings) :
    bindings ∈ matchPatternWith equivalent pattern term :=
  (complete_all equivalent (sizeOf pattern)).1
    pattern term bindings (Nat.le_refl _) relation

theorem matchArgsRelWith_complete {equivalent : Pattern → Pattern → Bool}
    {patterns terms : List Pattern} {bindings : Bindings}
    (relation : MatchArgsRelWith equivalent patterns terms bindings) :
    bindings ∈ matchArgsWith equivalent patterns terms :=
  (complete_all equivalent (sizeOf patterns)).2.1
    patterns terms bindings (Nat.le_refl _) relation

theorem matchBagRelWith_complete {equivalent : Pattern → Pattern → Bool}
    {patterns : List Pattern} {rest : Option String} {collectionType : CollType}
    {terms : List Pattern} {bindings : Bindings}
    (relation :
      MatchBagRelWith equivalent patterns rest collectionType terms bindings) :
    bindings ∈ matchBagWith equivalent patterns rest collectionType terms :=
  (complete_all equivalent (sizeOf patterns)).2.2
    patterns rest collectionType terms bindings (Nat.le_refl _) relation

theorem matchPatternWith_iff_matchRelWith
    {equivalent : Pattern → Pattern → Bool} {pattern term : Pattern}
    {bindings : Bindings} :
    bindings ∈ matchPatternWith equivalent pattern term ↔
      MatchRelWith equivalent pattern term bindings :=
  ⟨matchPatternWith_sound, matchRelWith_complete⟩

theorem matchArgsWith_iff_matchArgsRelWith
    {equivalent : Pattern → Pattern → Bool} {patterns terms : List Pattern}
    {bindings : Bindings} :
    bindings ∈ matchArgsWith equivalent patterns terms ↔
      MatchArgsRelWith equivalent patterns terms bindings :=
  ⟨matchArgsWith_sound, matchArgsRelWith_complete⟩

theorem matchBagWith_iff_matchBagRelWith
    {equivalent : Pattern → Pattern → Bool} {patterns : List Pattern}
    {rest : Option String} {collectionType : CollType} {terms : List Pattern}
    {bindings : Bindings} :
    bindings ∈ matchBagWith equivalent patterns rest collectionType terms ↔
      MatchBagRelWith equivalent patterns rest collectionType terms bindings :=
  ⟨matchBagWith_sound, matchBagRelWith_complete⟩

end Mettapedia.OSLF.MeTTaIL.MatchWithSpec
