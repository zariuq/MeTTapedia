import Mettapedia.OSLF.MeTTaIL.EngineCoded.Substitution

/-!
# Matching computed on codes

Matching a pattern against a term (`matchPattern`) is a structural recursion on
the pattern whose calls are all pairs of a part of the pattern with a part of the
term. The values form a matrix, row by row: argument lists and vectors combine
its diagonal position by position (`argsCombine`), and a bag or set tries every
remaining term element for each pattern element in turn (`bagRun`). Each
combination is computable on codes, and so is matching.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'
open CodeComputable

/-! ## Argument lists -/

/-- Combine the matches of an argument list position by position. -/
def argsCombine (results : List (List Bindings)) : List Bindings :=
  results.foldr (fun found rest => found.flatMap fun head => rest.filterMap (mergeBindings head)) [[]]

theorem matchArgs_eq : ∀ patterns terms : List Pattern,
    matchArgs patterns terms =
      if patterns.length = terms.length then argsCombine (List.zipWith matchPattern patterns terms) else []
  | [], [] => by simp [matchArgs, argsCombine]
  | [], _ :: _ => by simp [matchArgs]
  | _ :: _, [] => by simp [matchArgs]
  | pattern :: patterns, term :: terms => by
      rw [matchArgs.eq_def]
      simp only [matchArgs_eq patterns terms, List.length_cons, Nat.add_right_cancel_iff]
      by_cases same : patterns.length = terms.length
      · simp [same, argsCombine]
      · simp [same]

theorem argsCombine_computable : CodeComputable argsCombine :=
  list_foldr id (const [[]])
    (list_flatMap (fst.comp snd)
      (list_filterMap (snd.comp (snd.comp fst)) (mergeBindings_computable.comp (pair (snd.comp fst) snd))))

/-! ## The matrix of calls -/

/-- Every part of the pattern paired with every part of the term, row by row. -/
def matchCalls (term pattern : Pattern) : List (Pattern × Pattern) :=
  (parts pattern).flatMap fun part => (parts term).map fun subterm => (subterm, part)

theorem matchCalls_computable : CodeComputable₂ matchCalls :=
  list_flatMap (parts_computable.comp snd)
    (list_map (parts_computable.comp (fst.comp fst)) (pair snd (snd.comp fst)))

theorem matchCalls_smaller (term pattern : Pattern) :
    ∀ call ∈ matchCalls term pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  simp only [matchCalls, List.mem_flatMap, List.mem_map] at member
  obtain ⟨part, inParts, subterm, _, rfl⟩ := member
  exact patternCode_lt_of_mem_parts inParts

/-- The entry of a matrix stored row by row. -/
def entry (values : List (List Bindings)) (width row column : ℕ) : List Bindings :=
  values.getD (row * width + column) []

theorem getD_flatMap_rows {α β : Type} (f : α → β → List Bindings) :
    ∀ (rows : List α) (columns : List β) (row column : ℕ) (inRow : row < rows.length)
      (inColumn : column < columns.length),
      ((rows.flatMap fun r => columns.map (f r)).getD (row * columns.length + column) []) =
        f rows[row] columns[column]
  | [], _, _, _, inRow, _ => absurd inRow (Nat.not_lt_zero _)
  | r :: rows, columns, 0, column, _, inColumn => by
      have inMap : column < (columns.map (f r)).length := by simpa using inColumn
      rw [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_append_left inMap, List.getElem?_map, List.getElem?_eq_getElem inColumn]
      rfl
  | r :: rows, columns, row + 1, column, inRow, inColumn => by
      have shifted : (row + 1) * columns.length + column = columns.length + (row * columns.length + column) := by
        rw [Nat.succ_mul]; omega
      rw [List.flatMap_cons, shifted, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left,
        ← List.getD_eq_getElem?_getD]
      exact getD_flatMap_rows f rows columns row column (Nat.lt_of_succ_lt_succ inRow) inColumn

theorem entry_matchCalls (term pattern : Pattern) (row column : ℕ) (inRow : row < (parts pattern).length)
    (inColumn : column < (parts term).length) :
    entry ((matchCalls term pattern).map fun call => matchPattern call.2 call.1) (parts term).length row column =
      matchPattern (parts pattern)[row] (parts term)[column] := by
  unfold entry matchCalls
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def]
  exact getD_flatMap_rows (fun part subterm => matchPattern part subterm) _ _ row column inRow inColumn

/-- The diagonal of a matrix stored row by row, with this many rows. -/
def diagonal (values : List (List Bindings)) (width count : ℕ) : List (List Bindings) :=
  (List.range count).map fun index => entry values width index index

theorem diagonal_computable :
    CodeComputable fun input : List (List Bindings) × ℕ × ℕ => diagonal input.1 input.2.1 input.2.2 :=
  list_map (list_range (snd.comp snd))
    (list_getD [] (fst.comp fst) (nat_add (CodeComputable.nat_mul snd (fst.comp (snd.comp fst))) snd))

theorem diagonal_eq_zipWith {patterns terms : List Pattern} (count : ℕ) (inPatterns : count ≤ patterns.length)
    (inTerms : count ≤ terms.length) (values : List (List Bindings))
    (stored : ∀ row column (inRow : row < patterns.length) (inColumn : column < terms.length),
      entry values terms.length row column = matchPattern patterns[row] terms[column]) :
    diagonal values terms.length count =
      List.zipWith matchPattern (patterns.take count) (terms.take count) := by
  apply List.ext_getElem
  · simp [diagonal, Nat.min_eq_left inPatterns, Nat.min_eq_left inTerms]
  · intro index inDiagonal _
    simp only [diagonal, List.length_map, List.length_range] at inDiagonal
    simp only [diagonal, List.getElem_map, List.getElem_range, List.getElem_zipWith, List.getElem_take]
    exact stored index index (by omega) (by omega)


/-! ## Bags and sets -/

/-- What a bag match reads: the matrix, its width, the term elements, the rest name and the kind. -/
abbrev BagContext := List (List Bindings) × ℕ × List Pattern × Option String × CollType

/-- The end of a bag match: no rest name needs every term element used; a rest name takes those left. -/
def bagBase (context : BagContext) (columns : List ℕ) : List Bindings :=
  Option.casesOn (motive := fun _ => List Bindings) context.2.2.2.1
    (if columns.length = 0 then [[]] else [])
    fun name => [[(name, .collection context.2.2.2.2
      (columns.map fun column => context.2.2.1.getD column (.bvar 0)) none)]]

/-- The calls of a bag match: place the next row on each free column in turn. -/
def bagCalls (_fuel : ℕ) (argument : BagContext × List ℕ × List ℕ) : List (BagContext × List ℕ × List ℕ) :=
  if argument.2.1.length = 0 then []
  else (List.range argument.2.2.length).map fun index =>
    (argument.1, argument.2.1.tail, argument.2.2.eraseIdx index)

/-- The combination of a bag match from the matches of the remaining rows. -/
def bagCombine (_fuel : ℕ) (argument : BagContext × List ℕ × List ℕ) (results : List (List Bindings)) :
    List Bindings :=
  if argument.2.1.length = 0 then bagBase argument.1 argument.2.2
  else (List.range argument.2.2.length).flatMap fun index =>
    (entry argument.1.1 argument.1.2.1 (argument.2.1.headD 0) (argument.2.2.getD index 0)).flatMap fun head =>
      (results.getD index []).filterMap (mergeBindings head)

/-- Bag matching within a fuel, on the rows still to place and the columns still free. -/
def bagRun : ℕ → BagContext × List ℕ × List ℕ → List Bindings
  | 0, argument => bagBase argument.1 argument.2.2
  | fuel + 1, argument => bagCombine fuel argument ((bagCalls fuel argument).map (bagRun fuel))

theorem zipIdx_flatMap {α β : Type} (fallback : α) (items : List α) (f : α × ℕ → List β) :
    items.zipIdx.flatMap f = (List.range items.length).flatMap fun index => f (items.getD index fallback, index) := by
  have same : items.zipIdx = (List.range items.length).map fun index => (items.getD index fallback, index) := by
    apply List.ext_getElem
    · simp
    · intro index inZip _
      simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using inZip)]
  rw [same, List.flatMap_map]

/-- **Bag matching is the fuel recursion on the matrix**, when the matrix holds the matches of
every pattern element against every term element. -/
theorem matchBag_eq_bagRun (elements terms : List Pattern) (values : List (List Bindings))
    (rest : Option String) (kind : CollType)
    (stored : ∀ row column, row < elements.length → column < terms.length →
      entry values terms.length row column =
        matchPattern (elements.getD row (.bvar 0)) (terms.getD column (.bvar 0))) :
    ∀ (rows columns : List ℕ), (∀ row ∈ rows, row < elements.length) → (∀ column ∈ columns, column < terms.length) →
      matchBag (rows.map fun row => elements.getD row (.bvar 0)) rest kind
          (columns.map fun column => terms.getD column (.bvar 0)) =
        bagRun rows.length ((values, terms.length, terms, rest, kind), rows, columns)
  | [], columns, _, _ => by
      cases rest with
      | none => simp [matchBag, bagRun, bagBase]
      | some name => simp [matchBag, bagRun, bagBase]
  | row :: rows, columns, inRows, inColumns => by
      rw [List.map_cons, matchBag.eq_def]
      simp only []
      rw [zipIdx_flatMap (.bvar 0)]
      simp only [List.length_map, List.length_cons, bagRun, bagCombine, bagCalls, List.length_cons,
        Nat.add_one_ne_zero, if_false, List.tail_cons, List.headD_cons]
      apply List.flatMap_congr
      intro index inRange
      have below : index < columns.length := List.mem_range.mp inRange
      have termAt : (columns.map fun column => terms.getD column (Pattern.bvar 0)).getD index (Pattern.bvar 0) =
          terms.getD columns[index] (Pattern.bvar 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem below]
        rfl
      have columnAt : columns.getD index 0 = columns[index] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem below]
        rfl
      have resultAt : ((List.map (bagRun rows.length) (List.map (fun index =>
          ((values, terms.length, terms, rest, kind), rows, columns.eraseIdx index)) (List.range columns.length))).getD
            index []) = bagRun rows.length ((values, terms.length, terms, rest, kind), rows, columns.eraseIdx index) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range below]
        rfl
      rw [termAt, columnAt, resultAt,
        stored row columns[index] (inRows row List.mem_cons_self) (inColumns _ (List.getElem_mem below)),
        List.eraseIdx_map, matchBag_eq_bagRun elements terms values rest kind stored rows (columns.eraseIdx index)
          (fun r member => inRows r (List.mem_cons_of_mem _ member))
          (fun c member => inColumns c (List.mem_of_mem_eraseIdx member))]


theorem bagBase_computable :
    CodeComputable fun argument : BagContext × List ℕ × List ℕ => bagBase argument.1 argument.2.2 := by
  have restName : CodeComputable fun argument : BagContext × List ℕ × List ℕ => argument.1.2.2.2.1 :=
    fst.comp (snd.comp (snd.comp (snd.comp fst)))
  have noneCase : CodeComputable fun argument : BagContext × List ℕ × List ℕ =>
      (if argument.2.2.length = 0 then [[]] else [] : List Bindings) :=
    (CodeComputable.ite (nat_eq (list_length (snd.comp snd)) (const 0)) (const [[]]) (const [])).of_eq
      fun argument => by by_cases empty : argument.2.2.length = 0 <;> simp [empty]
  have elements : CodeComputable fun input : (BagContext × List ℕ × List ℕ) × String =>
      input.1.2.2.map fun column => input.1.1.2.2.1.getD column (Pattern.bvar 0) :=
    list_map (snd.comp (snd.comp fst))
      (list_getD (Pattern.bvar 0) (fst.comp (snd.comp (snd.comp (fst.comp (fst.comp fst))))) snd)
  have someCase : CodeComputable₂ fun (argument : BagContext × List ℕ × List ℕ) (name : String) =>
      [[(name, Pattern.collection argument.1.2.2.2.2
        (argument.2.2.map fun column => argument.1.2.2.1.getD column (Pattern.bvar 0)) none)]] :=
    list_cons (list_cons (pair snd (collection (snd.comp (snd.comp (snd.comp (snd.comp (fst.comp fst)))))
      elements (const none))) (const [])) (const [])
  exact (optionString_casesOn restName noneCase someCase).of_eq fun _ => rfl

theorem eraseIdx_computable :
    CodeComputable fun input : List ℕ × ℕ => input.1.eraseIdx input.2 :=
  (list_append (list_take snd fst) (list_drop (nat_add snd (const 1)) fst)).of_eq fun _ =>
    (List.eraseIdx_eq_take_drop_succ ..).symm

theorem bagCalls_computable : CodeComputable₂ bagCalls := by
  have rows : CodeComputable fun input : ℕ × BagContext × List ℕ × List ℕ => input.2.2.1 := fst.comp (snd.comp snd)
  have columns : CodeComputable fun input : ℕ × BagContext × List ℕ × List ℕ => input.2.2.2 :=
    snd.comp (snd.comp snd)
  have image : CodeComputable₂ fun (input : ℕ × BagContext × List ℕ × List ℕ) (index : ℕ) =>
      (input.2.1, input.2.2.1.tail, input.2.2.2.eraseIdx index) :=
    pair (fst.comp (snd.comp fst)) (pair (list_tail (rows.comp fst))
      (eraseIdx_computable.comp (pair (columns.comp fst) snd)))
  refine (CodeComputable.ite (nat_eq (list_length rows) (const 0)) (const [])
    (list_map (list_range (list_length columns)) image)).of_eq fun input => ?_
  by_cases empty : input.2.2.1.length = 0 <;> simp [bagCalls, empty]

theorem bagCombine_computable :
    CodeComputable fun input : ℕ × (BagContext × List ℕ × List ℕ) × List (List Bindings) =>
      bagCombine input.1 input.2.1 input.2.2 := by
  have argument : CodeComputable fun input : ℕ × (BagContext × List ℕ × List ℕ) × List (List Bindings) =>
      input.2.1 := fst.comp snd
  have rows := fst.comp (snd.comp argument)
  have columns := snd.comp (snd.comp argument)
  have values := fst.comp (fst.comp argument)
  have width := fst.comp (snd.comp (fst.comp argument))
  have results : CodeComputable fun input : ℕ × (BagContext × List ℕ × List ℕ) × List (List Bindings) =>
      input.2.2 := snd.comp snd
  have firstRow : CodeComputable fun input : ℕ × (BagContext × List ℕ × List ℕ) × List (List Bindings) =>
      input.2.1.2.1.headD 0 := (list_headI rows).of_eq fun input => by cases input.2.1.2.1 <;> rfl
  have cell : CodeComputable fun input : (ℕ × (BagContext × List ℕ × List ℕ) × List (List Bindings)) × ℕ =>
      entry input.1.2.1.1.1 input.1.2.1.1.2.1 (input.1.2.1.2.1.headD 0) (input.1.2.1.2.2.getD input.2 0) :=
    list_getD [] (values.comp fst)
      (nat_add (CodeComputable.nat_mul (firstRow.comp fst) (width.comp fst)) (list_getD 0 (columns.comp fst) snd))
  have branch : CodeComputable₂ fun (input : ℕ × (BagContext × List ℕ × List ℕ) × List (List Bindings))
      (index : ℕ) => (entry input.2.1.1.1 input.2.1.1.2.1 (input.2.1.2.1.headD 0) (input.2.1.2.2.getD index 0)).flatMap
        fun head => (input.2.2.getD index []).filterMap (mergeBindings head) :=
    list_flatMap cell (list_filterMap (list_getD [] (results.comp (fst.comp fst)) (snd.comp fst))
      (mergeBindings_computable.comp (pair (snd.comp fst) snd)))
  refine (CodeComputable.ite (nat_eq (list_length rows) (const 0))
    (bagBase_computable.comp argument) (list_flatMap (list_range (list_length columns)) branch)).of_eq fun input => ?_
  by_cases empty : input.2.1.2.1.length = 0 <;> simp [bagCombine, empty]

/-- **Bag matching within a fuel is computable on codes.** -/
theorem bagRun_computable : CodeComputable₂ bagRun :=
  fuel (base := fun argument => bagBase argument.1 argument.2.2) (calls := bagCalls) (combine := bagCombine)
    (fun _ => rfl) (fun _ _ => rfl) bagBase_computable bagCalls_computable bagCombine_computable


/-! ## The value of a match at a node -/

/-- A bound variable matches the same bound variable. -/
def bvarCombine (term : Pattern) (index : ℕ) : List Bindings :=
  @Pattern.casesOn (fun _ => List Bindings) term (fun other => if index == other then [[]] else [])
    (fun _ => []) (fun _ _ => []) (fun _ _ => []) (fun _ _ _ => []) (fun _ _ => []) (fun _ _ _ => [])

/-- An application matches an application with the same label and as many arguments. -/
def applyCombine' (term : Pattern) (label : String) (arguments : List Pattern) (values : List (List Bindings)) :
    List Bindings :=
  @Pattern.casesOn (fun _ => List Bindings) term (fun _ => []) (fun _ => [])
    (fun otherLabel otherArguments =>
      if label == otherLabel && arguments.length == otherArguments.length then
        argsCombine (diagonal values otherArguments.length arguments.length)
      else [])
    (fun _ _ => []) (fun _ _ _ => []) (fun _ _ => []) (fun _ _ _ => [])

/-- A binder matches a binder by its body. -/
def lambdaCombine (term : Pattern) (values : List (List Bindings)) : List Bindings :=
  @Pattern.casesOn (fun _ => List Bindings) term (fun _ => []) (fun _ => []) (fun _ _ => [])
    (fun _ _ => values.getD 0 []) (fun _ _ _ => []) (fun _ _ => []) (fun _ _ _ => [])

/-- A binder of several variables matches one of the same arity by its body. -/
def multiLambdaCombine (term : Pattern) (arity : ℕ) (values : List (List Bindings)) : List Bindings :=
  @Pattern.casesOn (fun _ => List Bindings) term (fun _ => []) (fun _ => []) (fun _ _ => []) (fun _ _ => [])
    (fun otherArity _ _ => if arity == otherArity then values.getD 0 [] else []) (fun _ _ => [])
    (fun _ _ _ => [])

/-- A substitution matches a substitution part by part. -/
def substCombine (term : Pattern) (values : List (List Bindings)) : List Bindings :=
  @Pattern.casesOn (fun _ => List Bindings) term (fun _ => []) (fun _ => []) (fun _ _ => []) (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => (values.getD 0 []).flatMap fun first => (values.getD 3 []).filterMap (mergeBindings first))
    (fun _ _ _ => [])

/-- A vector matches its elements in order, and binds its rest name to the elements left. -/
def vecCombine (elements terms : List Pattern) (rest : Option String) (values : List (List Bindings)) :
    List Bindings :=
  Option.casesOn (motive := fun _ => List Bindings) rest
    (if elements.length = terms.length then argsCombine (diagonal values terms.length elements.length) else [])
    fun name =>
      if elements.length ≤ terms.length then
        (argsCombine (diagonal values terms.length elements.length)).filterMap fun bindings =>
          mergeBindings bindings [(name, .collection .vec (terms.drop elements.length) none)]
      else []

/-- A collection matches a collection of the same kind: a vector in order, a bag or set in any order. -/
def collectionCombine (term : Pattern) (kind : CollType) (elements : List Pattern) (rest : Option String)
    (values : List (List Bindings)) : List Bindings :=
  @Pattern.casesOn (fun _ => List Bindings) term (fun _ => []) (fun _ => []) (fun _ _ => []) (fun _ _ => [])
    (fun _ _ _ => []) (fun _ _ => [])
    (fun otherKind terms _ =>
      if kind == otherKind then
        if kind == .vec then vecCombine elements terms rest values
        else bagRun elements.length
          ((values, terms.length, terms, rest, kind), List.range elements.length, List.range terms.length)
      else [])

/-- The value of a match at a node, from the matrix of the matches of the parts. -/
def matchCombine (term pattern : Pattern) (values : List (List Bindings)) : List Bindings :=
  @Pattern.casesOn (fun _ => List Bindings) pattern (fun index => bvarCombine term index)
    (fun name => [[(name, term)]]) (fun label arguments => applyCombine' term label arguments values)
    (fun _ _ => lambdaCombine term values) (fun arity _ _ => multiLambdaCombine term arity values)
    (fun _ _ => substCombine term values)
    (fun kind elements rest => collectionCombine term kind elements rest values)

theorem map_getD_range {α : Type} (items : List α) (fallback : α) :
    (List.range items.length).map (fun index => items.getD index fallback) = items := by
  apply List.ext_getElem
  · simp
  · intro index inMap _
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using inMap)]

theorem match_node (term pattern : Pattern) :
    matchPattern pattern term =
      matchCombine term pattern ((matchCalls term pattern).map fun call => matchPattern call.2 call.1) := by
  have stored : ∀ row column (inRow : row < (parts pattern).length) (inColumn : column < (parts term).length),
      entry ((matchCalls term pattern).map fun call => matchPattern call.2 call.1) (parts term).length row column =
        matchPattern (parts pattern)[row] (parts term)[column] := entry_matchCalls term pattern
  cases pattern with
  | fvar name => rw [matchPattern.eq_def]; rfl
  | bvar index => cases term <;> (rw [matchPattern.eq_def]; rfl)
  | apply label arguments =>
      cases term with
      | apply otherLabel otherArguments =>
          rw [matchPattern.eq_def]
          simp only [matchCombine, applyCombine']
          by_cases agree : (label == otherLabel && arguments.length == otherArguments.length) = true
          · rw [if_pos agree, if_pos agree]
            have same : arguments.length = otherArguments.length := by
              simp only [Bool.and_eq_true, beq_iff_eq] at agree; exact agree.2
            rw [matchArgs_eq, if_pos same, diagonal_eq_zipWith arguments.length le_rfl same.le _ stored,
              List.take_length, same, List.take_length]
          · rw [if_neg agree, if_neg agree]
      | _ => rw [matchPattern.eq_def]; rfl
  | lambda binder body => cases term <;> (rw [matchPattern.eq_def]; rfl)
  | multiLambda arity binders body => cases term <;> (rw [matchPattern.eq_def]; rfl)
  | subst body replacement => cases term <;> (rw [matchPattern.eq_def]; rfl)
  | collection kind elements rest =>
      cases term with
      | collection otherKind terms otherRest =>
          rw [matchPattern.eq_def]
          simp only [matchCombine, collectionCombine]
          by_cases sameKind : (kind == otherKind) = true
          · rw [if_pos sameKind, if_pos sameKind]
            by_cases isVec : (kind == CollType.vec) = true
            · rw [if_pos isVec, if_pos isVec]
              unfold vecCombine
              cases rest with
              | none =>
                  simp only []
                  rw [matchArgs_eq]
                  by_cases same : elements.length = terms.length
                  · rw [if_pos same, if_pos same, diagonal_eq_zipWith elements.length le_rfl same.le _ stored,
                      List.take_length, same, List.take_length]
                  · rw [if_neg same, if_neg same]
              | some name =>
                  simp only []
                  rw [matchArgs_eq]
                  by_cases fits : elements.length ≤ terms.length
                  · have same : elements.length = (terms.take elements.length).length := by
                      rw [List.length_take, Nat.min_eq_left fits]
                    rw [if_pos same, if_pos fits, diagonal_eq_zipWith elements.length le_rfl fits _ stored,
                      List.take_length]
                  · have differ : ¬ elements.length = (terms.take elements.length).length := by
                      rw [List.length_take]; omega
                    rw [if_neg differ, if_neg fits]
                    rfl
            · rw [if_neg isVec, if_neg isVec]
              have bags := matchBag_eq_bagRun elements terms
                ((matchCalls (.collection otherKind terms otherRest) (.collection kind elements rest)).map
                  fun call => matchPattern call.2 call.1) rest kind
                (fun row column inRow inColumn => by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRow, Option.getD_some,
                    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inColumn, Option.getD_some]
                  exact stored row column inRow inColumn)
                (List.range elements.length) (List.range terms.length)
                (fun row member => List.mem_range.mp member) (fun column member => List.mem_range.mp member)
              rw [map_getD_range, map_getD_range, List.length_range] at bags
              exact bags
          · rw [if_neg sameKind, if_neg sameKind]
      | _ => rw [matchPattern.eq_def]; rfl


/-! ## The combinations are computable on codes -/

theorem natBEq : CodeComputable₂ fun left right : ℕ => left == right :=
  (nat_eq fst snd).of_eq fun _ => Bool.eq_iff_iff.mpr (by simp)

theorem collBEq : CodeComputable₂ fun left right : CollType => left == right :=
  (beq_of_injective collectionCode_injective).of_eq fun _ => rfl

theorem bvarCombine_computable : CodeComputable₂ bvarCombine :=
  (casesOn (pattern := fun input : Pattern × ℕ => input.1)
    (onBVar := fun input other => if input.2 == other then [[]] else ([] : List Bindings))
    (onFVar := fun _ _ => []) (onApply := fun _ _ _ => []) (onLambda := fun _ _ _ => [])
    (onMultiLambda := fun _ _ _ _ => []) (onSubst := fun _ _ _ => []) (onCollection := fun _ _ _ _ => []) fst
    (CodeComputable.ite (natBEq.comp (pair (snd.comp fst) snd)) (const [[]]) (const [])) (const []) (const [])
    (const []) (const []) (const []) (const [])).of_eq fun _ => rfl

theorem applyCombine'_computable :
    CodeComputable fun input : Pattern × String × List Pattern × List (List Bindings) =>
      applyCombine' input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have test : CodeComputable fun x : (Pattern × String × List Pattern × List (List Bindings)) × String × List Pattern =>
      x.1.2.1 == x.2.1 && x.1.2.2.1.length == x.2.2.length :=
    CodeComputable.and (stringBEq.comp (pair (fst.comp (snd.comp fst)) (fst.comp snd)))
      (natBEq.comp (pair (list_length (fst.comp (snd.comp (snd.comp fst)))) (list_length (snd.comp snd))))
  have value : CodeComputable fun x : (Pattern × String × List Pattern × List (List Bindings)) × String × List Pattern =>
      argsCombine (diagonal x.1.2.2.2 x.2.2.length x.1.2.2.1.length) :=
    argsCombine_computable.comp (diagonal_computable.comp (pair (snd.comp (snd.comp (snd.comp fst)))
      (pair (list_length (snd.comp snd)) (list_length (fst.comp (snd.comp (snd.comp fst)))))))
  exact (casesOn (pattern := fun input : Pattern × String × List Pattern × List (List Bindings) => input.1)
    (onBVar := fun _ _ => ([] : List Bindings)) (onFVar := fun _ _ => [])
    (onApply := fun input otherLabel otherArguments =>
      if input.2.1 == otherLabel && input.2.2.1.length == otherArguments.length then
        argsCombine (diagonal input.2.2.2 otherArguments.length input.2.2.1.length) else [])
    (onLambda := fun _ _ _ => []) (onMultiLambda := fun _ _ _ _ => []) (onSubst := fun _ _ _ => [])
    (onCollection := fun _ _ _ _ => []) fst (const []) (const []) (CodeComputable.ite test value (const []))
    (const []) (const []) (const []) (const [])).of_eq fun _ => rfl

theorem lambdaCombine_computable : CodeComputable₂ lambdaCombine :=
  (casesOn (pattern := fun input : Pattern × List (List Bindings) => input.1)
    (onBVar := fun _ _ => ([] : List Bindings)) (onFVar := fun _ _ => []) (onApply := fun _ _ _ => [])
    (onLambda := fun input _ _ => input.2.getD 0 []) (onMultiLambda := fun _ _ _ _ => [])
    (onSubst := fun _ _ _ => []) (onCollection := fun _ _ _ _ => []) fst (const []) (const []) (const [])
    (list_getD [] (snd.comp fst) (const 0)) (const []) (const []) (const [])).of_eq fun _ => rfl

theorem multiLambdaCombine_computable :
    CodeComputable fun input : Pattern × ℕ × List (List Bindings) => multiLambdaCombine input.1 input.2.1 input.2.2 :=
  (casesOn (pattern := fun input : Pattern × ℕ × List (List Bindings) => input.1)
    (onBVar := fun _ _ => ([] : List Bindings)) (onFVar := fun _ _ => []) (onApply := fun _ _ _ => [])
    (onLambda := fun _ _ _ => [])
    (onMultiLambda := fun input otherArity _ _ => if input.2.1 == otherArity then input.2.2.getD 0 [] else [])
    (onSubst := fun _ _ _ => []) (onCollection := fun _ _ _ _ => []) fst (const []) (const []) (const [])
    (const [])
    (CodeComputable.ite (natBEq.comp (pair (fst.comp (snd.comp fst)) (fst.comp snd)))
      (list_getD [] (snd.comp (snd.comp fst)) (const 0)) (const []))
    (const []) (const [])).of_eq fun _ => rfl

theorem substCombine_computable : CodeComputable₂ substCombine := by
  have value : CodeComputable fun x : (Pattern × List (List Bindings)) × Pattern × Pattern =>
      (x.1.2.getD 0 []).flatMap fun first => (x.1.2.getD 3 []).filterMap (mergeBindings first) :=
    list_flatMap (list_getD [] (snd.comp fst) (const 0))
      (list_filterMap (list_getD [] (snd.comp (fst.comp fst)) (const 3))
        (mergeBindings_computable.comp (pair (snd.comp fst) snd)))
  exact (casesOn (pattern := fun input : Pattern × List (List Bindings) => input.1)
    (onBVar := fun _ _ => ([] : List Bindings)) (onFVar := fun _ _ => []) (onApply := fun _ _ _ => [])
    (onLambda := fun _ _ _ => []) (onMultiLambda := fun _ _ _ _ => [])
    (onSubst := fun input _ _ => (input.2.getD 0 []).flatMap fun first =>
      (input.2.getD 3 []).filterMap (mergeBindings first))
    (onCollection := fun _ _ _ _ => []) fst (const []) (const []) (const []) (const []) (const []) value
    (const [])).of_eq fun _ => rfl

theorem vecCombine_computable :
    CodeComputable fun input : List Pattern × List Pattern × Option String × List (List Bindings) =>
      vecCombine input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have elements : CodeComputable fun input : List Pattern × List Pattern × Option String × List (List Bindings) =>
      input.1 := fst
  have terms : CodeComputable fun input : List Pattern × List Pattern × Option String × List (List Bindings) =>
      input.2.1 := fst.comp snd
  have values : CodeComputable fun input : List Pattern × List Pattern × Option String × List (List Bindings) =>
      input.2.2.2 := snd.comp (snd.comp snd)
  have combined : CodeComputable fun input : List Pattern × List Pattern × Option String × List (List Bindings) =>
      argsCombine (diagonal input.2.2.2 input.2.1.length input.1.length) :=
    argsCombine_computable.comp (diagonal_computable.comp (pair values (pair (list_length terms)
      (list_length elements))))
  have noneCase : CodeComputable fun input : List Pattern × List Pattern × Option String × List (List Bindings) =>
      (if input.1.length = input.2.1.length then argsCombine (diagonal input.2.2.2 input.2.1.length input.1.length)
        else [] : List Bindings) :=
    (CodeComputable.ite (nat_eq (list_length elements) (list_length terms)) combined (const [])).of_eq
      fun input => by by_cases same : input.1.length = input.2.1.length <;> simp [same]
  have restBinding : CodeComputable fun x : (List Pattern × List Pattern × Option String × List (List Bindings)) ×
      String => [(x.2, Pattern.collection CollType.vec (x.1.2.1.drop x.1.1.length) none)] :=
    list_cons (pair snd (collection (const CollType.vec) (list_drop (list_length (elements.comp fst))
      (terms.comp fst)) (const none))) (const [])
  have mergeRest : CodeComputable₂ fun (x : (List Pattern × List Pattern × Option String × List (List Bindings)) ×
      String) (bindings : Bindings) =>
      mergeBindings bindings [(x.2, Pattern.collection CollType.vec (x.1.2.1.drop x.1.1.length) none)] :=
    (mergeBindings_computable.comp (pair snd (restBinding.comp fst))).of_eq fun _ => rfl
  have someCase : CodeComputable₂ fun (input : List Pattern × List Pattern × Option String × List (List Bindings))
      (name : String) =>
      (if input.1.length ≤ input.2.1.length then
        (argsCombine (diagonal input.2.2.2 input.2.1.length input.1.length)).filterMap fun bindings =>
          mergeBindings bindings [(name, .collection .vec (input.2.1.drop input.1.length) none)]
      else [] : List Bindings) :=
    (CodeComputable.ite (CodeComputable.not (nat_lt (list_length (terms.comp fst)) (list_length (elements.comp fst))))
      (list_filterMap (combined.comp fst) mergeRest)
      (const [])).of_eq fun x => by
        by_cases fits : x.1.1.length ≤ x.1.2.1.length
        · simp [fits, Nat.not_lt.mpr fits]
        · simp [fits, Nat.lt_of_not_le fits]
  exact (optionString_casesOn (fst.comp (snd.comp snd)) noneCase someCase).of_eq fun _ => rfl

theorem collectionCombine_computable :
    CodeComputable fun input : Pattern × CollType × List Pattern × Option String × List (List Bindings) =>
      collectionCombine input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2 := by
  have kind : CodeComputable fun x : (Pattern × CollType × List Pattern × Option String × List (List Bindings)) ×
      CollType × List Pattern × Option String => x.1.2.1 := fst.comp (snd.comp fst)
  have elements : CodeComputable fun x : (Pattern × CollType × List Pattern × Option String × List (List Bindings)) ×
      CollType × List Pattern × Option String => x.1.2.2.1 := fst.comp (snd.comp (snd.comp fst))
  have rest : CodeComputable fun x : (Pattern × CollType × List Pattern × Option String × List (List Bindings)) ×
      CollType × List Pattern × Option String => x.1.2.2.2.1 := fst.comp (snd.comp (snd.comp (snd.comp fst)))
  have values : CodeComputable fun x : (Pattern × CollType × List Pattern × Option String × List (List Bindings)) ×
      CollType × List Pattern × Option String => x.1.2.2.2.2 := snd.comp (snd.comp (snd.comp (snd.comp fst)))
  have terms : CodeComputable fun x : (Pattern × CollType × List Pattern × Option String × List (List Bindings)) ×
      CollType × List Pattern × Option String => x.2.2.1 := fst.comp (snd.comp snd)
  have bags := bagRun_computable.comp (pair (list_length elements) (pair (pair values (pair (list_length terms)
    (pair terms (pair rest kind)))) (pair (list_range (list_length elements)) (list_range (list_length terms)))))
  have branch := CodeComputable.ite (collBEq.comp (pair kind (fst.comp snd)))
    (CodeComputable.ite (collBEq.comp (pair kind (const CollType.vec)))
      (vecCombine_computable.comp (pair elements (pair terms (pair rest values)))) bags) (const [])
  exact (casesOn (pattern := fun input : Pattern × CollType × List Pattern × Option String × List (List Bindings) =>
      input.1)
    (onBVar := fun _ _ => ([] : List Bindings)) (onFVar := fun _ _ => []) (onApply := fun _ _ _ => [])
    (onLambda := fun _ _ _ => []) (onMultiLambda := fun _ _ _ _ => []) (onSubst := fun _ _ _ => [])
    (onCollection := fun input otherKind terms _ =>
      if input.2.1 == otherKind then
        if input.2.1 == .vec then vecCombine input.2.2.1 terms input.2.2.2.1 input.2.2.2.2
        else bagRun input.2.2.1.length ((input.2.2.2.2, terms.length, terms, input.2.2.2.1, input.2.1),
          List.range input.2.2.1.length, List.range terms.length)
      else [])
    fst (const []) (const []) (const []) (const []) (const []) (const []) branch).of_eq fun _ => rfl

theorem matchCombine_computable :
    CodeComputable fun input : Pattern × Pattern × List (List Bindings) => matchCombine input.1 input.2.1 input.2.2 :=
  (casesOn (pattern := fun input : Pattern × Pattern × List (List Bindings) => input.2.1)
    (onBVar := fun input index => bvarCombine input.1 index)
    (onFVar := fun input name => [[(name, input.1)]])
    (onApply := fun input label arguments => applyCombine' input.1 label arguments input.2.2)
    (onLambda := fun input _ _ => lambdaCombine input.1 input.2.2)
    (onMultiLambda := fun input arity _ _ => multiLambdaCombine input.1 arity input.2.2)
    (onSubst := fun input _ _ => substCombine input.1 input.2.2)
    (onCollection := fun input kind elements rest => collectionCombine input.1 kind elements rest input.2.2)
    (fst.comp snd) (bvarCombine_computable.comp (pair (fst.comp fst) snd))
    (list_cons (list_cons (pair snd (fst.comp fst)) (const [])) (const []))
    (applyCombine'_computable.comp (pair (fst.comp fst) (pair (fst.comp snd) (pair (snd.comp snd)
      (snd.comp (snd.comp fst))))))
    (lambdaCombine_computable.comp (pair (fst.comp fst) (snd.comp (snd.comp fst))))
    (multiLambdaCombine_computable.comp (pair (fst.comp fst) (pair (fst.comp snd) (snd.comp (snd.comp fst)))))
    (substCombine_computable.comp (pair (fst.comp fst) (snd.comp (snd.comp fst))))
    (collectionCombine_computable.comp (pair (fst.comp fst) (pair (fst.comp snd) (pair (fst.comp (snd.comp snd))
      (pair (snd.comp (snd.comp snd)) (snd.comp (snd.comp fst)))))))).of_eq fun _ => rfl

/-- **Matching a pattern against a term is computable on codes.** -/
theorem matchPattern_computable : CodeComputable₂ matchPattern :=
  (structural (value := fun term pattern => matchPattern pattern term) (calls := matchCalls)
    (combine := matchCombine) match_node matchCalls_smaller matchCalls_computable
    matchCombine_computable).comp (pair snd fst)

end Mettapedia.OSLF.MeTTaIL.EngineCoded

#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.matchPattern_computable
