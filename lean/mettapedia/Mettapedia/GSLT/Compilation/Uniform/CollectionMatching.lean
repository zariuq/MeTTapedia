import Mettapedia.GSLT.Compilation.Uniform.DemandTransformation
import Mettapedia.GSLT.Compilation.Uniform.OrderedRows
import Mettapedia.GSLT.Compilation.Uniform.MatchesAndInstances
import Mettapedia.GSLT.Compilation.Uniform.PatternRows

/-!
# Matching bags and sets by clauses

A bag or set pattern matches a collection by picking, for each of its elements in turn, one element of the
collection by position, and binding its rest to the elements left, in their order (`MatchBagRel`). Two
fixed relations on rows say this:

* `pick`: an element of a list beside the list without it (`pick_sound`, `pick_complete`);
* `wrap`: the row of a bag or a set with a given list (`wrap_sound`, `wrap_complete`).

Read the other way, `insert` and `unwrap` turn a match into an instantiation of the same pattern (`invertGoals`);
`unwrap` also gives an instantiation the list of a bag or set rest (`Instantiation.buildRow`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.CollectionMatching

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.ComputedConditions (Relations)
open RootRewritesOnTheStep (symTerm appTerm encode encodeList numeralTerm numeral)
open DemandTransformation (Goal Clause goalHolds DerivesAt Derives derives_of_clause pick)

/-! ## Reading lists off their rows -/

open PatternRows (encodeList_cons_inv encodeList_nil_inv encode_closed_inv)


/-! ## An element of a list beside the list without it -/

/-- The relation that picks an element of a list. -/
def pickRelation : ℕ := 3

/-- Picking the first element. -/
def pickHeadClause : Clause :=
  { relation := pickRelation, input := appTerm (.var 0) (.var 1), output := appTerm (.var 0) (.var 1), body := [] }

/-- Picking a later element, and keeping the first. -/
def pickTailClause : Clause :=
  { relation := pickRelation, input := appTerm (.var 0) (.var 1),
    output := appTerm (.var 2) (appTerm (.var 0) (.var 3)),
    body := [.ask pickRelation (.var 1) (appTerm (.var 2) (.var 3))] }

/-- The clauses of picking. -/
def pickClauses : List Clause := [pickHeadClause, pickTailClause]

variable {R : Relations} {program : List Clause}

/-- **A derived pick is an element of the list beside the list without it.** -/
theorem pick_sound (onlyPicks : ∀ c ∈ program, c.relation = pickRelation → c ∈ pickClauses) :
    ∀ (depth : ℕ) {xs : List Pattern} {w : Expr}, DerivesAt R program depth pickRelation (encodeList xs) w →
      ∃ i, ∃ bound : i < xs.length, w = .app (encode xs[i]) (encodeList (xs.eraseIdx i))
  | 0, _, _, derived => derived.elim
  | depth + 1, xs, w, derived => by
      obtain ⟨c, member, isPick, θ, input, output, goals⟩ := derived
      have picked := onlyPicks c member isPick
      simp only [pickClauses, List.mem_cons, List.not_mem_nil, or_false] at picked
      rcases picked with rfl | rfl
      · simp only [pickHeadClause, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at input output
        obtain ⟨x, rest, rfl, first, second⟩ := encodeList_cons_inv input
        exact ⟨0, by simp, by rw [← output, first, second]; simp⟩
      · simp only [pickTailClause, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at input output
        obtain ⟨x, rest, rfl, first, second⟩ := encodeList_cons_inv input
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, second] at asked
        obtain ⟨j, bound, answered⟩ := pick_sound onlyPicks depth asked
        simp only [Expr.app.injEq] at answered
        refine ⟨j + 1, by simpa using bound, ?_⟩
        rw [← output, answered.1, answered.2, first]
        simp [encodeList]

/-- **Every element of a list beside the list without it is a derived pick.** -/
theorem pick_complete (included : ∀ c ∈ pickClauses, c ∈ program) :
    ∀ (xs : List Pattern) (i : ℕ) (bound : i < xs.length),
      Derives R program pickRelation (encodeList xs) (.app (encode xs[i]) (encodeList (xs.eraseIdx i)))
  | [], _, bound => absurd bound (by simp)
  | x :: rest, 0, _ => by
      have clause := derives_of_clause (R := R) (included pickHeadClause (by simp [pickClauses]))
        (pick [encode x, encodeList rest]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [pickHeadClause, pick, encodeList] using clause
  | x :: rest, j + 1, bound => by
      have jBound : j < rest.length := by simpa using bound
      have inner := pick_complete included rest j jBound
      have clause := derives_of_clause (R := R) (included pickTailClause (by simp [pickClauses]))
        (pick [encode x, encodeList rest, encode rest[j], encodeList (rest.eraseIdx j)]) (fun g inside => by
          simp only [pickTailClause, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, pick] using inner)
      simpa [pickTailClause, pick, encodeList] using clause

/-! ## A bag or a set with a given list -/

/-- The row pattern of a collection of a kind, with a list. -/
def collectionTerm (kind : CollType) (list : Tm) : Tm :=
  appTerm (symTerm 6) (appTerm (symTerm (collectionCode kind)) (appTerm list (symTerm 0)))

theorem inst_collectionTerm (θ : ℕ → Expr) (kind : CollType) (list : Tm) :
    inst θ (collectionTerm kind list) =
      .app (.sym 6) (.app (.sym (collectionCode kind)) (.app (inst θ list) (.sym 0))) := rfl

theorem encode_collection (kind : CollType) (items : List Pattern) :
    encode (.collection kind items none) =
      .app (.sym 6) (.app (.sym (collectionCode kind)) (.app (encodeList items) (.sym 0))) := by
  simp [encode, RootRewritesOnTheStep.optionRow]

/-- The relation that wraps a list as a bag or a set. -/
def wrapRelation : ℕ := 4

/-- Wrapping a list as a collection of the kind. -/
def wrapClause (kind : CollType) : Clause :=
  { relation := wrapRelation, input := appTerm (symTerm (collectionCode kind)) (.var 0),
    output := collectionTerm kind (.var 0), body := [] }

/-- The clauses of wrapping: a bag, a set. -/
def wrapClauses : List Clause := [wrapClause .hashBag, wrapClause .hashSet]

/-- **A derived wrap is the collection of the kind with the list.** -/
theorem wrap_sound (onlyWraps : ∀ c ∈ program, c.relation = wrapRelation → c ∈ wrapClauses)
    {kind : CollType} {xs : List Pattern} {w : Expr}
    (derived : Derives R program wrapRelation (.app (.sym (collectionCode kind)) (encodeList xs)) w) :
    w = encode (.collection kind xs none) := by
  obtain ⟨depth, derivedAt⟩ := derived
  cases depth with
  | zero => exact derivedAt.elim
  | succ depth =>
      obtain ⟨c, member, isWrap, θ, input, output, -⟩ := derivedAt
      have wrapped := onlyWraps c member isWrap
      simp only [wrapClauses, List.mem_cons, List.not_mem_nil, or_false] at wrapped
      rcases wrapped with rfl | rfl
      all_goals
        simp only [wrapClause, inst_collectionTerm, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq, Expr.sym.injEq]
          at input output
        obtain ⟨kindIs, listIs⟩ := input
        rw [← output, listIs, encode_collection, Mettapedia.OSLF.MeTTaIL.PatternCode.collectionCode_injective kindIs]

/-- **A bag or a set with a list is a derived wrap.** -/
theorem wrap_complete (included : ∀ c ∈ wrapClauses, c ∈ program) {kind : CollType} (unordered : kind ≠ .vec)
    (xs : List Pattern) :
    Derives R program wrapRelation (.app (.sym (collectionCode kind)) (encodeList xs))
      (encode (.collection kind xs none)) := by
  have member : wrapClause kind ∈ program := by
    cases kind with
    | vec => exact absurd rfl unordered
    | hashBag => exact included _ (by simp [wrapClauses])
    | hashSet => exact included _ (by simp [wrapClauses])
  have clause := derives_of_clause (R := R) member (pick [encodeList xs]) (fun _ inside => absurd inside List.not_mem_nil)
  simpa [wrapClause, pick, inst_collectionTerm, encode_collection] using clause

/-! ## Fresh lists -/

/-- The length of the longest of some names. -/
def widest (avoid : List String) : ℕ := avoid.foldr (fun name width => max name.length width) 0

theorem length_le_widest : ∀ {avoid : List String} {name : String}, name ∈ avoid → name.length ≤ widest avoid
  | [], _, inside => absurd inside List.not_mem_nil
  | first :: others, name, inside => by
      simp only [widest, List.foldr_cons]
      rcases List.mem_cons.mp inside with rfl | later
      · exact le_max_left _ _
      · exact le_trans (length_le_widest later) (le_max_right _ _)

/-- **A fresh name**: longer than every name it must differ from, one length per number. -/
def freshName (avoid : List String) (n : ℕ) : String :=
  String.ofList (List.replicate (widest avoid + 1 + n) '#')

theorem freshName_length (avoid : List String) (n : ℕ) : (freshName avoid n).length = widest avoid + 1 + n := by
  simp [freshName]

theorem freshName_not_mem (avoid : List String) (n : ℕ) : freshName avoid n ∉ avoid := by
  intro inside
  have := length_le_widest inside
  rw [freshName_length] at this
  omega

theorem freshName_injective (avoid : List String) : Function.Injective (freshName avoid) := by
  intro m n same
  have := congrArg String.length same
  rw [freshName_length, freshName_length] at this
  omega

/-- The unknown of the `n`-th fresh list. -/
def listUnknown (avoid : List String) (n : ℕ) : ℕ := RootRewritesOnTheStep.labelCode (freshName avoid n)

theorem listUnknown_ne {avoid : List String} {name : String} (inside : name ∈ avoid) (n : ℕ) :
    listUnknown avoid n ≠ RootRewritesOnTheStep.labelCode name := by
  intro same
  have named : freshName avoid n = name := RootRewritesOnTheStep.labelCode_injective same
  exact freshName_not_mem avoid n (named ▸ inside)

theorem listUnknown_injective (avoid : List String) : Function.Injective (listUnknown avoid) :=
  fun _ _ same => freshName_injective avoid (RootRewritesOnTheStep.labelCode_injective same)

/-! ## Patterns at matching positions -/

open OrderedRows (vectorTerm)
open OrderedMatching (names namesList)
open RootRewritesOnTheStep (labelCode)

/-- What a bag or a set leaves after its picked elements: its rest, or nothing. -/
def restRow (kind : CollType) : Option String → Tm
  | some rest => .var (labelCode rest)
  | none => collectionTerm kind (symTerm 0)

mutual
  /-- **A pattern at a matching position**: its row pattern, the goals that pick the elements of its bags and sets
  and wrap their rests, and the next fresh list. A name in `rests` is a vector rest. -/
  def matchRow (rests avoid : List String) : ℕ → Pattern → Option (Tm × List Goal × ℕ)
    | next, .fvar name =>
        some (if name ∈ rests then vectorTerm (.var (labelCode name)) else .var (labelCode name), [], next)
    | next, .bvar index => some (appTerm (symTerm 0) (numeralTerm index), [], next)
    | next, .apply label arguments => (matchRows rests avoid next arguments (symTerm 0)).map fun found =>
        (appTerm (symTerm 2) (appTerm (symTerm (labelCode label)) found.1), found.2.1, found.2.2)
    | next, .collection .vec elements none => (matchRows rests avoid next elements (symTerm 0)).map fun found =>
        (vectorTerm found.1, found.2.1, found.2.2)
    | next, .collection .vec elements (some rest) =>
        if rest ∈ rests then (matchRows rests avoid next elements (.var (labelCode rest))).map fun found =>
          (vectorTerm found.1, found.2.1, found.2.2)
        else none
    | next, .collection .hashBag elements rest =>
        if rest.all (fun name => !rests.contains name) then
          (pickGoals rests avoid (next + 1) .hashBag (.var (listUnknown avoid next)) elements rest).map fun found =>
            (collectionTerm .hashBag (.var (listUnknown avoid next)), found.1, found.2)
        else none
    | next, .collection .hashSet elements rest =>
        if rest.all (fun name => !rests.contains name) then
          (pickGoals rests avoid (next + 1) .hashSet (.var (listUnknown avoid next)) elements rest).map fun found =>
            (collectionTerm .hashSet (.var (listUnknown avoid next)), found.1, found.2)
        else none
    | next, .lambda _ body => (matchRow rests avoid next body).map fun found =>
        (appTerm (symTerm 3) (appTerm (symTerm 0) found.1), found.2.1, found.2.2)
    | next, .multiLambda arity _ body => (matchRow rests avoid next body).map fun found =>
        (appTerm (symTerm 4) (appTerm (numeralTerm arity) (appTerm (symTerm 0) found.1)), found.2.1, found.2.2)
    | next, .subst body value => (matchRow rests avoid next body).bind fun bodyFound =>
        (matchRow rests avoid bodyFound.2.2 value).map fun valueFound =>
          (appTerm (symTerm 5) (appTerm bodyFound.1 valueFound.1), bodyFound.2.1 ++ valueFound.2.1, valueFound.2.2)

  /-- Patterns as one list closed by a tail, at a matching position. -/
  def matchRows (rests avoid : List String) : ℕ → List Pattern → Tm → Option (Tm × List Goal × ℕ)
    | next, [], close => some (close, [], next)
    | next, pattern :: patterns, close => (matchRow rests avoid next pattern).bind fun head =>
        (matchRows rests avoid head.2.2 patterns close).map fun tail =>
          (appTerm head.1 tail.1, head.2.1 ++ tail.2.1, tail.2.2)

  /-- The goals that pick the elements of a bag or a set from a list, in turn, then wrap what is left: as the
  rest, or as the empty collection when there is no rest. -/
  def pickGoals (rests avoid : List String) : ℕ → CollType → Tm → List Pattern → Option String →
      Option (List Goal × ℕ)
    | next, kind, list, [], rest =>
        some ([.ask wrapRelation (appTerm (symTerm (collectionCode kind)) list)
          (restRow kind rest)], next)
    | next, kind, list, element :: elements, rest => (matchRow rests avoid next element).bind fun found =>
        (pickGoals rests avoid (found.2.2 + 1) kind (.var (listUnknown avoid found.2.2)) elements rest).map
          fun later => (.ask pickRelation list (appTerm found.1 (.var (listUnknown avoid found.2.2))) ::
            found.2.1 ++ later.1, later.2)
end

/-! ## Reading terms off their rows -/

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar BindingsValued mergeBindings_some_of_valued)
open OrderedRows (Holds Captured)
open OrderedMatching (Covers covers_extends)

theorem collection_of_row {θ : ℕ → Expr} {kind : CollType} {list : Tm} {s : Pattern}
    (met : inst θ (collectionTerm kind list) = encode s) :
    ∃ items, s = .collection kind items none ∧ inst θ list = encodeList items := by
  cases s with
  | collection kind' items rest =>
      simp only [inst_collectionTerm, encode, Expr.app.injEq, Expr.sym.injEq, true_and] at met
      obtain ⟨kindIs, listIs, restIs⟩ := met
      cases rest with
      | none =>
          rw [Mettapedia.OSLF.MeTTaIL.PatternCode.collectionCode_injective kindIs]
          exact ⟨items, rfl, listIs⟩
      | some name => simp [RootRewritesOnTheStep.optionRow] at restIs
  | _ => simp [inst_collectionTerm, encode] at met

theorem apply_of_row {θ : ℕ → Expr} {label : String} {list : Tm} {s : Pattern}
    (met : inst θ (appTerm (symTerm 2) (appTerm (symTerm (labelCode label)) list)) = encode s) :
    ∃ arguments, s = .apply label arguments ∧ inst θ list = encodeList arguments := by
  cases s with
  | apply label' arguments =>
      simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, encode, Expr.app.injEq,
        Expr.sym.injEq, true_and] at met
      rw [RootRewritesOnTheStep.labelCode_injective met.1]
      exact ⟨arguments, rfl, met.2⟩
  | _ => simp [encode] at met

theorem valued_single {name : String} {value : Pattern} {witness : Bindings}
    (same : lookupOrFvar witness name = value) : BindingsValued [(name, value)] (lookupOrFvar witness) := by
  intro key found member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨rfl, rfl⟩ := member
  exact same.symm

theorem covers_single (name : String) (value : Pattern) : Covers [(name, value)] [name] := by
  intro key member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨value, by simp⟩

theorem covers_merge {left right merged : Bindings} {leftNames rightNames : List String}
    (ok : mergeBindings left right = some merged) (leftCovered : Covers left leftNames)
    (rightCovered : Covers right rightNames) : Covers merged (leftNames ++ rightNames) := by
  intro name member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact covers_extends leftCovered (fun _ _ held => mergeBindings_subsumed_left ok held) name inLeft
  · exact covers_extends rightCovered (fun _ _ held => mergeBindings_subsumed_right ok held) name inRight

/-! ## Matching is sound -/

section Sound

variable {R : Relations} {program : List Clause} {rests avoid : List String}

/-- Every clause of picking is a pick clause, and every clause of wrapping a wrap clause. -/
structure CollectionClauses (program : List Clause) : Prop where
  onlyPicks : ∀ c ∈ program, c.relation = pickRelation → c ∈ pickClauses
  onlyWraps : ∀ c ∈ program, c.relation = wrapRelation → c ∈ wrapClauses

/-- The bag or set case of soundness, once its picks are sound. -/
theorem bag_of_picks {kind : CollType} (unordered : kind ≠ .vec) {elements : List Pattern} {rest : Option String}
    {θ : ℕ → Expr} {list : Tm} {s : Pattern} (met : inst θ (collectionTerm kind list) = encode s)
    (picks : ∀ {items : List Pattern}, inst θ list = encodeList items →
      (∀ name ∈ namesList elements ++ rest.toList, Captured rests θ name) ∧
        ∀ witness : Bindings, (∀ name ∈ namesList elements ++ rest.toList, Holds rests θ witness name) →
          ∃ found, MatchBagRel elements rest kind items found ∧ BindingsValued found (lookupOrFvar witness) ∧
            Covers found (namesList elements ++ rest.toList)) :
    (∀ name ∈ names (.collection kind elements rest), Captured rests θ name) ∧
      ∀ witness : Bindings, (∀ name ∈ names (.collection kind elements rest), Holds rests θ witness name) →
        ∃ found, MatchRel (.collection kind elements rest) s found ∧ BindingsValued found (lookupOrFvar witness) ∧
          Covers found (names (.collection kind elements rest)) := by
  obtain ⟨items, rfl, listed⟩ := collection_of_row met
  obtain ⟨captured, matching⟩ := picks listed
  refine ⟨by simpa only [names] using captured, fun witness holds => ?_⟩
  obtain ⟨bindings, matched, valued, covered⟩ := matching witness (by simpa only [names] using holds)
  exact ⟨bindings, .collection unordered matched, valued, by simpa only [names] using covered⟩

mutual
  /-- **A clause instance whose matching goals hold is a match**: it captures every name, and for any witness of
  the names, the matcher matches the term with bindings the witness values. -/
  theorem matchRow_sound (collections : CollectionClauses program) : ∀ (p : Pattern) {next next' : ℕ} {t : Tm}
      {goals : List Goal},
      matchRow rests avoid next p = some (t, goals, next') → ∀ {θ : ℕ → Expr} {s : Pattern},
      inst θ t = encode s → (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ name ∈ names p, Captured rests θ name) ∧
        ∀ witness : Bindings, (∀ name ∈ names p, Holds rests θ witness name) →
          ∃ found, MatchRel p s found ∧ BindingsValued found (lookupOrFvar witness) ∧ Covers found (names p)
    | .fvar name, _, _, _, _, lowered, θ, s, met, _ => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        refine ⟨fun other inside => ?_, fun witness holds => ?_⟩
        · simp only [names, List.mem_singleton] at inside
          subst inside
          unfold Captured
          split
          · rename_i inRests
            rw [if_pos inRests] at met
            exact OrderedRows.list_of_vectorTerm (list := .var _) met
          · rename_i outside
            rw [if_neg outside] at met
            exact ⟨s, met⟩
        · have held := holds name (by simp [names])
          have value : lookupOrFvar witness name = s := by
            unfold Holds at held
            split at held
            · rename_i inRests
              obtain ⟨tail, value, listed⟩ := held
              rw [if_pos inRests, OrderedRows.inst_vectorTerm (list := .var _) (items := tail) listed] at met
              rw [value]
              exact RootRewritesOnTheStep.encode_injective met
            · rename_i outside
              rw [if_neg outside] at met
              exact RootRewritesOnTheStep.encode_injective (held.symm.trans met)
          exact ⟨[(name, s)], .fvar, valued_single value, by simpa [names] using covers_single name s⟩
    | .bvar index, _, _, _, _, lowered, θ, s, met, _ => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        have same : s = .bvar index := by
          cases s <;> simp [encode] at met
          rw [met]
        subst same
        exact ⟨by simp [names], fun _ _ => ⟨[], .bvar, fun _ _ inside => absurd inside List.not_mem_nil,
          by simp [names, Covers]⟩⟩
    | .apply label arguments, _, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨items, rfl, listed⟩ := apply_of_row met
        obtain ⟨heads, tail, rfl, lengths, closed, captured, matching⟩ :=
          matchRows_sound collections arguments found listed goals
        have empty : tail = [] := encodeList_nil_inv closed
        subst empty
        rw [List.append_nil]
        refine ⟨by simpa only [names] using captured, fun witness holds => ?_⟩
        obtain ⟨bindings, matched, valued, covered⟩ := matching witness (by simpa only [names] using holds)
        exact ⟨bindings, .apply matched lengths.symm, valued, by simpa only [names] using covered⟩
    | .collection .vec elements none, _, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨items, rfl, listed⟩ := collection_of_row (kind := .vec) met
        obtain ⟨heads, tail, rfl, lengths, closed, captured, matching⟩ :=
          matchRows_sound collections elements found listed goals
        have empty : tail = [] := encodeList_nil_inv closed
        subst empty
        rw [List.append_nil]
        refine ⟨by simpa only [names, Option.toList_none, List.append_nil] using captured, fun witness holds => ?_⟩
        obtain ⟨bindings, matched, valued, covered⟩ :=
          matching witness (by simpa only [names, Option.toList_none, List.append_nil] using holds)
        exact ⟨bindings, .vector matched, valued, by simpa only [names, Option.toList_none, List.append_nil] using covered⟩
    | .collection .vec elements (some restName), _, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, rfl, listed⟩ := collection_of_row (kind := .vec) met
          obtain ⟨heads, tail, rfl, lengths, closed, captured, matching⟩ :=
            matchRows_sound collections elements found listed goals
          refine ⟨fun name inside => ?_, fun witness holds => ?_⟩
          · simp only [names, Option.toList_some, List.mem_append, List.mem_singleton] at inside
            rcases inside with inElements | rfl
            · exact captured name inElements
            · simp only [Captured, if_pos inRests]
              exact ⟨tail, closed⟩
          · obtain ⟨bindings, matched, valued, covered⟩ :=
              matching witness fun name inside => holds name (by simp [names, inside])
            have restHolds := holds restName (by simp [names])
            simp only [Holds, if_pos inRests] at restHolds
            obtain ⟨tail', restValue, restListed⟩ := restHolds
            have sameTail : tail' = tail := RootRewritesOnTheStep.encodeList_inj _ _ (restListed.symm.trans closed)
            subst sameTail
            obtain ⟨merged, mergedOk, mergedValued⟩ :=
              mergeBindings_some_of_valued bindings _ _ valued (valued_single restValue)
            have takeIs : (heads ++ tail').take elements.length = heads := by
              rw [← lengths, List.take_left]
            have dropIs : (heads ++ tail').drop elements.length = tail' := by
              rw [← lengths, List.drop_left]
            refine ⟨merged, .vectorRest (by rw [takeIs]; exact matched) (by rw [dropIs]; exact mergedOk),
              mergedValued, ?_⟩
            simpa only [names, Option.toList_some] using covers_merge mergedOk covered (covers_single restName _)
        · cases lowered
    | .collection .hashBag elements rest, next, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i restOutside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          exact bag_of_picks (by decide) met fun listed => pickGoals_sound collections elements picked restOutside listed goals
        · cases lowered
    | .collection .hashSet elements rest, next, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i restOutside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          exact bag_of_picks (by decide) met fun listed => pickGoals_sound collections elements picked restOutside listed goals
        · cases lowered
    | .lambda _ body, _, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at met
        obtain ⟨binder, body', rfl, -, bodyMet⟩ := PatternRows.encode_lambda_inv met
        obtain ⟨captured, matching⟩ := matchRow_sound collections body found bodyMet goals
        refine ⟨by simpa only [names] using captured, fun witness holds => ?_⟩
        obtain ⟨bindings, matched, valued, covered⟩ := matching witness (by simpa only [names] using holds)
        exact ⟨bindings, .lambda matched, valued, by simpa only [names] using covered⟩
    | .multiLambda arity _ body, _, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          RootRewritesOnTheStep.inst_numeralTerm] at met
        obtain ⟨arity', binders', body', rfl, arityIs, -, bodyMet⟩ := PatternRows.encode_multiLambda_inv met
        obtain rfl := RootRewritesOnTheStep.numeral_injective arityIs
        obtain ⟨captured, matching⟩ := matchRow_sound collections body found bodyMet goals
        refine ⟨by simpa only [names] using captured, fun witness holds => ?_⟩
        obtain ⟨bindings, matched, valued, covered⟩ := matching witness (by simpa only [names] using holds)
        exact ⟨bindings, .multiLambda matched, valued, by simpa only [names] using covered⟩
    | .subst body value, _, _, _, _, lowered, θ, s, met, goals => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at met
        obtain ⟨body', value', rfl, bodyMet, valueMet⟩ := PatternRows.encode_subst_inv met
        obtain ⟨bodyCaptured, bodyMatching⟩ := matchRow_sound collections body bodyFound bodyMet
          (fun g inside => goals g (List.mem_append_left _ inside))
        obtain ⟨valueCaptured, valueMatching⟩ := matchRow_sound collections value valueFound valueMet
          (fun g inside => goals g (List.mem_append_right _ inside))
        refine ⟨fun name inside => ?_, fun witness holds => ?_⟩
        · simp only [names, List.mem_append] at inside
          rcases inside with here | later
          · exact bodyCaptured name here
          · exact valueCaptured name later
        · obtain ⟨bodyBindings, bodyMatched, bodyValued, bodyCovered⟩ :=
            bodyMatching witness fun name inside => holds name (by simp [names, inside])
          obtain ⟨valueBindings, valueMatched, valueValued, valueCovered⟩ :=
            valueMatching witness fun name inside => holds name (by simp [names, inside])
          obtain ⟨merged, mergedOk, mergedValued⟩ :=
            mergeBindings_some_of_valued bodyBindings valueBindings _ bodyValued valueValued
          exact ⟨merged, .subst bodyMatched valueMatched mergedOk, mergedValued,
            by simpa only [names] using covers_merge mergedOk bodyCovered valueCovered⟩

  /-- **Patterns matched as one list**: a prefix of the list, the rest closing it. -/
  theorem matchRows_sound (collections : CollectionClauses program) : ∀ (patterns : List Pattern) {next next' : ℕ}
      {close list : Tm} {goals : List Goal},
      matchRows rests avoid next patterns close = some (list, goals, next') →
      ∀ {θ : ℕ → Expr} {items : List Pattern}, inst θ list = encodeList items →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      ∃ heads tail, items = heads ++ tail ∧ heads.length = patterns.length ∧ inst θ close = encodeList tail ∧
        (∀ name ∈ namesList patterns, Captured rests θ name) ∧
        ∀ witness : Bindings, (∀ name ∈ namesList patterns, Holds rests θ witness name) →
          ∃ found, MatchArgsRel patterns heads found ∧ BindingsValued found (lookupOrFvar witness) ∧
            Covers found (namesList patterns)
    | [], _, _, _, _, _, lowered, θ, items, met, _ => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨[], items, rfl, rfl, met, by simp [namesList], fun _ _ => ⟨[], .nil,
          fun _ _ inside => absurd inside List.not_mem_nil, by simp [namesList, Covers]⟩⟩
    | pattern :: patterns, _, _, _, _, _, lowered, θ, items, met, goals => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm] at met
        obtain ⟨x, others, rfl, headMet, tailMet⟩ := encodeList_cons_inv met
        obtain ⟨headCaptured, headMatching⟩ := matchRow_sound collections pattern headFound headMet
          (fun g inside => goals g (List.mem_append_left _ inside))
        obtain ⟨heads, rest, rfl, lengths, closed, tailCaptured, tailMatching⟩ := matchRows_sound collections patterns
          tailFound tailMet (fun g inside => goals g (List.mem_append_right _ inside))
        refine ⟨x :: heads, rest, rfl, by simp [lengths], closed, fun name inside => ?_, fun witness holds => ?_⟩
        · simp only [namesList, List.mem_append] at inside
          rcases inside with here | later
          · exact headCaptured name here
          · exact tailCaptured name later
        · obtain ⟨headBindings, headMatched, headValued, headCovered⟩ :=
            headMatching witness fun name inside => holds name (by simp [namesList, inside])
          obtain ⟨tailBindings, tailMatched, tailValued, tailCovered⟩ :=
            tailMatching witness fun name inside => holds name (by simp [namesList, inside])
          obtain ⟨merged, mergedOk, mergedValued⟩ :=
            mergeBindings_some_of_valued headBindings tailBindings _ headValued tailValued
          exact ⟨merged, .cons headMatched tailMatched mergedOk, mergedValued,
            by simpa only [namesList] using covers_merge mergedOk headCovered tailCovered⟩

  /-- **Picks that hold are a match of a bag or a set**: the picked elements, then what is left. -/
  theorem pickGoals_sound (collections : CollectionClauses program) : ∀ (elements : List Pattern) {next next' : ℕ}
      {kind : CollType} {list : Tm}
      {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') →
      rest.all (fun name => !rests.contains name) = true → ∀ {θ : ℕ → Expr} {items : List Pattern},
      inst θ list = encodeList items → (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ name ∈ namesList elements ++ rest.toList, Captured rests θ name) ∧
        ∀ witness : Bindings, (∀ name ∈ namesList elements ++ rest.toList, Holds rests θ witness name) →
          ∃ found, MatchBagRel elements rest kind items found ∧ BindingsValued found (lookupOrFvar witness) ∧
            Covers found (namesList elements ++ rest.toList)
    | [], _, _, kind, list, rest, _, lowered, outside, θ, items, met, goals => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl⟩ := lowered
        have wrapped := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, met] at wrapped
        have restIs := wrap_sound collections.onlyWraps wrapped
        cases rest with
        | none =>
            simp only [restRow, inst_collectionTerm, RootRewritesOnTheStep.inst_symTerm, encode_collection,
              Expr.app.injEq, true_and, and_true] at restIs
            have empty : items = [] := encodeList_nil_inv restIs
            subst empty
            exact ⟨by simp [namesList], fun _ _ => ⟨[], .nilNoRest, fun _ _ inside => absurd inside List.not_mem_nil,
              by simp [namesList, Covers]⟩⟩
        | some restName =>
            simp only [restRow, DemandTransformation.inst_unknown] at restIs
            have notRest : restName ∉ rests := by simpa using outside
            refine ⟨fun name inside => ?_, fun witness holds => ?_⟩
            · simp only [namesList, Option.toList_some, List.nil_append, List.mem_singleton] at inside
              subst inside
              simp only [Captured, if_neg notRest]
              exact ⟨_, restIs⟩
            · have held := holds restName (by simp [namesList])
              simp only [Holds, if_neg notRest] at held
              have value : lookupOrFvar witness restName = .collection kind items none :=
                RootRewritesOnTheStep.encode_injective (held.symm.trans restIs)
              exact ⟨_, .nilRest, valued_single value, by simpa [namesList] using covers_single restName _⟩
    | element :: elements, _, _, kind, list, rest, _, lowered, outside, θ, items, met, goals => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, found, ⟨laterGoals, last⟩, laterFound, rfl, rfl⟩ := lowered
        have picked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, met] at picked
        obtain ⟨depth, pickedAt⟩ := picked
        obtain ⟨i, bound, answered⟩ := pick_sound collections.onlyPicks depth pickedAt
        simp only [Expr.app.injEq] at answered
        obtain ⟨headCaptured, headMatching⟩ := matchRow_sound collections element found answered.1
          (fun g inside => goals g (List.mem_cons_of_mem _ (List.mem_append_left _ inside)))
        obtain ⟨tailCaptured, tailMatching⟩ := pickGoals_sound collections elements laterFound outside
          (by simpa using answered.2) (fun g inside => goals g (List.mem_cons_of_mem _ (List.mem_append_right _ inside)))
        refine ⟨fun name inside => ?_, fun witness holds => ?_⟩
        · simp only [namesList, List.append_assoc, List.mem_append] at inside
          rcases inside with here | later
          · exact headCaptured name here
          · exact tailCaptured name (List.mem_append.mpr later)
        · obtain ⟨headBindings, headMatched, headValued, headCovered⟩ :=
            headMatching witness fun name inside => holds name (by simp [namesList, inside])
          obtain ⟨tailBindings, tailMatched, tailValued, tailCovered⟩ :=
            tailMatching witness fun name inside => holds name (by
              rcases List.mem_append.mp inside with inElements | inRest
              · simp [namesList, inElements]
              · simp [namesList, inRest])
          obtain ⟨merged, mergedOk, mergedValued⟩ :=
            mergeBindings_some_of_valued headBindings tailBindings _ headValued tailValued
          refine ⟨merged, .cons i bound headMatched tailMatched mergedOk, mergedValued, ?_⟩
          simpa only [namesList, List.append_assoc] using covers_merge mergedOk headCovered tailCovered
end

end Sound

/-! ## What a matching lowering mentions -/

open RuleSyntax.Machines (unknowns)
open DemandTransformation (goalUnknowns)

variable {rests avoid : List String}

/-- **An unknown in scope**: the code of one of some names, or a fresh list from `first` to before `last`. -/
def InScope (avoid names : List String) (first last u : ℕ) : Prop :=
  (∃ name ∈ names, u = labelCode name) ∨ ∃ k, first ≤ k ∧ k < last ∧ u = listUnknown avoid k

theorem InScope.widen {avoid names names' : List String} {first last first' last' u : ℕ}
    (within : InScope avoid names first last u) (sub : ∀ name ∈ names, name ∈ names') (below : first' ≤ first)
    (above : last ≤ last') : InScope avoid names' first' last' u := by
  rcases within with ⟨name, inside, rfl⟩ | ⟨k, low, high, rfl⟩
  · exact .inl ⟨name, sub name inside, rfl⟩
  · exact .inr ⟨k, le_trans below low, lt_of_lt_of_le high above, rfl⟩

@[simp] theorem unknowns_vectorTerm (list : Tm) : unknowns (vectorTerm list) = unknowns list := by
  simp [vectorTerm]

@[simp] theorem unknowns_collectionTerm (kind : CollType) (list : Tm) :
    unknowns (collectionTerm kind list) = unknowns list := by
  simp [collectionTerm]

mutual
  /-- **A matching lowering mentions the pattern's names and its own fresh lists.** -/
  theorem matchRow_scope : ∀ (p : Pattern) {next next' : ℕ} {t : Tm} {goals : List Goal},
      matchRow rests avoid next p = some (t, goals, next') →
      next ≤ next' ∧ ∀ u ∈ unknowns t ++ goals.flatMap goalUnknowns, InScope avoid (names p) next next' u
    | .fvar name, _, _, _, _, lowered => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        refine ⟨le_rfl, fun u inside => .inl ⟨name, by simp [names], ?_⟩⟩
        split at inside <;> simpa using inside
    | .bvar _, _, _, _, _, lowered => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨le_rfl, fun u inside => by simp at inside⟩
    | .apply label arguments, _, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := matchRows_scope arguments found
        refine ⟨ordered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append]
          at inside
        rcases within u inside with inClose | inScope
        · simp at inClose
        · exact inScope.widen (fun name member => by simpa [names] using member) le_rfl le_rfl
    | .collection .vec elements none, _, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := matchRows_scope elements found
        refine ⟨ordered, fun u inside => ?_⟩
        rw [unknowns_vectorTerm] at inside
        rcases within u inside with inClose | inScope
        · simp at inClose
        · exact inScope.widen (fun name member => by simpa [names] using member) le_rfl le_rfl
    | .collection .vec elements (some restName), _, _, _, _, lowered => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨ordered, within⟩ := matchRows_scope elements found
          refine ⟨ordered, fun u inside => ?_⟩
          rw [unknowns_vectorTerm] at inside
          rcases within u inside with inClose | inScope
          · simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inClose
            exact .inl ⟨restName, by simp [names], inClose⟩
          · exact inScope.widen (fun name member => by simp [names, member]) le_rfl le_rfl
        · cases lowered
    | .collection .hashBag elements rest, next, _, _, _, lowered => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨ordered, within⟩ := pickGoals_scope elements picked
          refine ⟨by omega, fun u inside => ?_⟩
          rcases List.mem_append.mp inside with inRow | inGoals
          · simp only [unknowns_collectionTerm, DemandTransformation.unknowns_unknown, List.mem_singleton] at inRow
            exact .inr ⟨next, le_rfl, by omega, inRow⟩
          · rcases within u inGoals with inList | inScope
            · simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inList
              exact .inr ⟨next, le_rfl, by omega, inList⟩
            · exact inScope.widen (fun name member => by simpa [names] using member) (by omega) le_rfl
        · cases lowered
    | .collection .hashSet elements rest, next, _, _, _, lowered => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨ordered, within⟩ := pickGoals_scope elements picked
          refine ⟨by omega, fun u inside => ?_⟩
          rcases List.mem_append.mp inside with inRow | inGoals
          · simp only [unknowns_collectionTerm, DemandTransformation.unknowns_unknown, List.mem_singleton] at inRow
            exact .inr ⟨next, le_rfl, by omega, inRow⟩
          · rcases within u inGoals with inList | inScope
            · simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inList
              exact .inr ⟨next, le_rfl, by omega, inList⟩
            · exact inScope.widen (fun name member => by simpa [names] using member) (by omega) le_rfl
        · cases lowered
    | .lambda _ body, next, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := matchRow_scope body found
        refine ⟨ordered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
          List.nil_append] at inside
        exact (within u inside).widen (fun name member => by simpa [names] using member) le_rfl le_rfl
    | .multiLambda _ _ body, next, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨ordered, within⟩ := matchRow_scope body found
        refine ⟨ordered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
          RootRewritesOnTheStep.unknowns_numeralTerm, List.nil_append] at inside
        exact (within u inside).widen (fun name member => by simpa [names] using member) le_rfl le_rfl
    | .subst body value, next, _, _, _, lowered => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        obtain ⟨bodyOrdered, bodyScoped⟩ := matchRow_scope body bodyFound
        obtain ⟨valueOrdered, valueScoped⟩ := matchRow_scope value valueFound
        refine ⟨le_trans bodyOrdered valueOrdered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append,
          List.flatMap_append, List.mem_append] at inside
        have bodySide : ∀ v, InScope avoid (names body) next middle v →
            InScope avoid (names (.subst body value)) next last v := fun v within =>
          within.widen (fun name member => by simp [names, member]) le_rfl valueOrdered
        have valueSide : ∀ v, InScope avoid (names value) middle last v →
            InScope avoid (names (.subst body value)) next last v := fun v within =>
          within.widen (fun name member => by simp [names, member]) bodyOrdered le_rfl
        rcases inside with (inBody | inValue) | inBodyGoals | inValueGoals
        · exact bodySide u (bodyScoped u (List.mem_append_left _ inBody))
        · exact valueSide u (valueScoped u (List.mem_append_left _ inValue))
        · exact bodySide u (bodyScoped u (List.mem_append_right _ inBodyGoals))
        · exact valueSide u (valueScoped u (List.mem_append_right _ inValueGoals))

  theorem matchRows_scope : ∀ (patterns : List Pattern) {next next' : ℕ} {close list : Tm} {goals : List Goal},
      matchRows rests avoid next patterns close = some (list, goals, next') →
      next ≤ next' ∧ ∀ u ∈ unknowns list ++ goals.flatMap goalUnknowns,
        u ∈ unknowns close ∨ InScope avoid (namesList patterns) next next' u
    | [], _, _, _, _, _, lowered => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨le_rfl, fun u inside => .inl (by simpa using inside)⟩
    | pattern :: patterns, next, _, _, _, _, lowered => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        obtain ⟨headOrdered, headScoped⟩ := matchRow_scope pattern headFound
        obtain ⟨tailOrdered, tailScoped⟩ := matchRows_scope patterns tailFound
        refine ⟨le_trans headOrdered tailOrdered, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, List.flatMap_append, List.mem_append] at inside
        have headSide : ∀ v, InScope avoid (names pattern) next middle v →
            InScope avoid (namesList (pattern :: patterns)) next last v := fun v within =>
          within.widen (fun name member => by simp [namesList, member]) le_rfl tailOrdered
        have tailSide : ∀ v, InScope avoid (namesList patterns) middle last v →
            InScope avoid (namesList (pattern :: patterns)) next last v := fun v within =>
          within.widen (fun name member => by simp [namesList, member]) headOrdered le_rfl
        rcases inside with (inHead | inTail) | inHeadGoals | inTailGoals
        · exact .inr (headSide u (headScoped u (List.mem_append_left _ inHead)))
        · rcases tailScoped u (List.mem_append_left _ inTail) with inClose | within
          · exact .inl inClose
          · exact .inr (tailSide u within)
        · exact .inr (headSide u (headScoped u (List.mem_append_right _ inHeadGoals)))
        · rcases tailScoped u (List.mem_append_right _ inTailGoals) with inClose | within
          · exact .inl inClose
          · exact .inr (tailSide u within)

  theorem pickGoals_scope : ∀ (elements : List Pattern) {next next' : ℕ} {kind : CollType} {list : Tm}
      {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') →
      next ≤ next' ∧ ∀ u ∈ goals.flatMap goalUnknowns,
        u ∈ unknowns list ∨ InScope avoid (namesList elements ++ rest.toList) next next' u
    | [], _, _, kind, list, rest, _, lowered => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl⟩ := lowered
        refine ⟨le_rfl, fun u inside => ?_⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, goalUnknowns,
          RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append,
          List.mem_append] at inside
        rcases inside with inList | inRest
        · exact .inl inList
        · cases rest with
          | none => simp [restRow] at inRest
          | some restName =>
              simp only [restRow, DemandTransformation.unknowns_unknown, List.mem_singleton] at inRest
              exact .inr (.inl ⟨restName, by simp [namesList], inRest⟩)
    | element :: elements, next, _, kind, list, rest, _, lowered => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, found, ⟨laterGoals, last⟩, laterFound, rfl, rfl⟩ := lowered
        dsimp only at laterFound
        obtain ⟨rowOrdered, rowScoped⟩ := matchRow_scope element found
        obtain ⟨laterOrdered, laterScoped⟩ := pickGoals_scope elements laterFound
        refine ⟨by omega, fun u inside => ?_⟩
        have listed : u = listUnknown avoid middle →
            InScope avoid (namesList (element :: elements) ++ rest.toList) next last u :=
          fun same => .inr ⟨middle, rowOrdered, by omega, same⟩
        have rowSide : ∀ v, InScope avoid (names element) next middle v →
            InScope avoid (namesList (element :: elements) ++ rest.toList) next last v := fun v within =>
          within.widen (fun name member => by simp [namesList, member]) le_rfl (by omega)
        dsimp only at inside
        rw [List.flatMap_append, List.flatMap_cons] at inside
        rcases List.mem_append.mp inside with inFirst | inLater
        · rcases List.mem_append.mp inFirst with inPick | inElementGoals
          · simp only [goalUnknowns, RootRewritesOnTheStep.unknowns_appTerm, DemandTransformation.unknowns_unknown]
              at inPick
            rcases List.mem_append.mp inPick with inList | inRowTail
            · exact .inl inList
            rcases List.mem_append.mp inRowTail with inRow | same
            · exact .inr (rowSide u (rowScoped u (List.mem_append_left _ inRow)))
            · exact .inr (listed (List.mem_singleton.mp same))
          · exact .inr (rowSide u (rowScoped u (List.mem_append_right _ inElementGoals)))
        · rcases laterScoped u inLater with inTail | within
          · simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inTail
            exact .inr (listed inTail)
          · exact .inr (within.widen (fun name member => by
              rcases List.mem_append.mp member with inElements | inRest
              · simp [namesList, inElements]
              · simp [inRest]) (by omega) le_rfl)
end

/-! ## Matching is complete at data -/

/-- An unknown that no fresh list from `first` to before `last` is. -/
def Untouched (avoid : List String) (first last u : ℕ) : Prop :=
  ∀ k, first ≤ k → k < last → u ≠ listUnknown avoid k

/-- **Two instantiations agree outside the fresh lists** from `first` to before `last`. -/
def AgreeOutside (avoid : List String) (first last : ℕ) (θ θ' : ℕ → Expr) : Prop :=
  ∀ u, Untouched avoid first last u → θ' u = θ u

theorem AgreeOutside.refl {first last : ℕ} (θ : ℕ → Expr) : AgreeOutside avoid first last θ θ := fun _ _ => rfl

theorem AgreeOutside.trans {a b c d : ℕ} {θ θ₁ θ₂ : ℕ → Expr} (one : AgreeOutside avoid a b θ θ₁)
    (two : AgreeOutside avoid c d θ₁ θ₂) (lower : a ≤ c) (upper : b ≤ d) : AgreeOutside avoid a d θ θ₂ :=
  fun u untouched => (two u fun k low high => untouched k (le_trans lower low) high).trans
    (one u fun k low high => untouched k low (lt_of_lt_of_le high upper))

theorem untouched_name {name : String} (inside : name ∈ avoid) (first last : ℕ) :
    Untouched avoid first last (labelCode name) := fun k _ _ same => listUnknown_ne inside k same.symm

theorem InScope.untouched {names : List String} {a b c d u : ℕ} (within : InScope avoid names a b u)
    (named : ∀ name ∈ names, name ∈ avoid) (apart : b ≤ c ∨ d ≤ a) : Untouched avoid c d u := by
  rcases within with ⟨name, inside, rfl⟩ | ⟨k, low, high, rfl⟩
  · exact untouched_name (named name inside) c d
  · intro k' low' high' same
    have := listUnknown_injective avoid same
    omega

theorem holds_congr {θ θ' : ℕ → Expr} {witness : Bindings} {name : String}
    (same : θ' (labelCode name) = θ (labelCode name)) (holds : Holds rests θ witness name) :
    Holds rests θ' witness name := by
  unfold Holds at holds ⊢
  by_cases inRests : name ∈ rests
  · rw [if_pos inRests] at holds ⊢
    obtain ⟨tail, value, listed⟩ := holds
    exact ⟨tail, value, same.trans listed⟩
  · rw [if_neg inRests] at holds ⊢
    exact same.trans holds

theorem lookup_of_extends_single {name : String} {value : Pattern} {witness : Bindings}
    (above : BindingsExtends [(name, value)] witness) : lookupOrFvar witness name = value := by
  have found := above name value (by simp)
  simp [lookupOrFvar, applyBindings, found]

theorem extends_of_merge_left {left right merged witness : Bindings} (ok : mergeBindings left right = some merged)
    (above : BindingsExtends merged witness) : BindingsExtends left witness :=
  OrderedMatching.extends_trans (fun _ _ held => mergeBindings_subsumed_left ok held) above

theorem extends_of_merge_right {left right merged witness : Bindings} (ok : mergeBindings left right = some merged)
    (above : BindingsExtends merged witness) : BindingsExtends right witness :=
  OrderedMatching.extends_trans (fun _ _ held => mergeBindings_subsumed_right ok held) above

/-- The pick and wrap clauses are clauses of the program. -/
structure CollectionClausesIn (program : List Clause) : Prop where
  picks : ∀ c ∈ pickClauses, c ∈ program
  wraps : ∀ c ∈ wrapClauses, c ∈ program

section Complete

open OrderedMatching (isData)

variable {R : Relations} {program : List Clause}

theorem goals_agree {θ θ' : ℕ → Expr} {goals : List Goal}
    (agree : ∀ u ∈ goals.flatMap goalUnknowns, θ' u = θ u)
    (holds : ∀ g ∈ goals, goalHolds R (Derives R program) θ g) : ∀ g ∈ goals, goalHolds R (Derives R program) θ' g :=
  fun g inside => DemandTransformation.goalHolds_congr g
    (fun u inU => (agree u (List.mem_flatMap.mpr ⟨g, inside, inU⟩)).symm) (holds g inside)

/-- The bag or set case of completeness, once its picks are complete: the list unknown is set to the list. -/
theorem bag_complete {kind : CollType} {elements : List Pattern} {rest : Option String} {next last : ℕ}
    {picks : List Goal} (ordered : next + 1 ≤ last)
    (named : ∀ name ∈ names (.collection kind elements rest), name ∈ avoid) {items : List Pattern}
    {witness : Bindings} {θ : ℕ → Expr}
    (holds : ∀ name ∈ names (.collection kind elements rest), Holds rests θ witness name)
    (picksComplete : ∀ θ₁ : ℕ → Expr,
      (∀ name ∈ namesList elements ++ rest.toList, Holds rests θ₁ witness name) →
      inst θ₁ (.var (listUnknown avoid next) : Tm) = encodeList items →
      (∀ u ∈ unknowns (.var (listUnknown avoid next) : Tm), Untouched avoid (next + 1) last u) →
      ∃ θ', AgreeOutside avoid (next + 1) last θ₁ θ' ∧ ∀ g ∈ picks, goalHolds R (Derives R program) θ' g) :
    ∃ θ', AgreeOutside avoid next last θ θ' ∧
      inst θ' (collectionTerm kind (.var (listUnknown avoid next))) = encode (.collection kind items none) ∧
      ∀ g ∈ picks, goalHolds R (Derives R program) θ' g := by
  obtain ⟨θ₁, θ₁Is⟩ : ∃ θ₁ : ℕ → Expr, θ₁ = Function.update θ (listUnknown avoid next) (encodeList items) :=
    ⟨_, rfl⟩
  have onNames : ∀ name ∈ names (.collection kind elements rest), θ₁ (labelCode name) = θ (labelCode name) :=
    fun name inside => by
      rw [θ₁Is]
      exact Function.update_of_ne (listUnknown_ne (named name inside) next).symm _ _
  have freshList : ∀ k, next + 1 ≤ k → listUnknown avoid next ≠ listUnknown avoid k := fun k low same => by
    have := listUnknown_injective avoid same
    omega
  obtain ⟨θ', agree, goalsHold⟩ := picksComplete θ₁
    (fun name inside => holds_congr (onNames name (by simpa [names] using inside))
      (holds name (by simpa [names] using inside)))
    (by simp [θ₁Is])
    (fun u inside => by
      simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inside
      subst inside
      exact fun k low _ => freshList k low)
  refine ⟨θ', fun u untouched => ?_, ?_, goalsHold⟩
  · rw [agree u fun k low high => untouched k (by omega) high, θ₁Is]
    exact Function.update_of_ne (untouched next le_rfl (by omega)) _ _
  · have kept : θ' (listUnknown avoid next) = encodeList items := by
      rw [agree _ fun k low _ => freshList k low]
      simp [θ₁Is]
    rw [inst_collectionTerm, DemandTransformation.inst_unknown, kept, encode_collection]

mutual
  /-- **A match at data is a clause instance whose matching goals hold**, changed only at its own fresh lists. -/
  theorem matchRow_complete (included : CollectionClausesIn program) : ∀ (p : Pattern) {next next' : ℕ} {t : Tm}
      {goals : List Goal}, matchRow rests avoid next p = some (t, goals, next') → (∀ name ∈ names p, name ∈ avoid) →
      ∀ {s : Pattern} {found : Bindings}, MatchRel p s found → isData s = true → ∀ {witness : Bindings},
      BindingsExtends found witness → ∀ {θ : ℕ → Expr}, (∀ name ∈ names p, Holds rests θ witness name) →
      ∃ θ', AgreeOutside avoid next next' θ θ' ∧ inst θ' t = encode s ∧
        ∀ g ∈ goals, goalHolds R (Derives R program) θ' g
    | .fvar name, _, _, _, _, lowered, _, s, found, matched, _, witness, above, θ, holds => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        cases matched
        have value := lookup_of_extends_single above
        have held := holds name (by simp [names])
        refine ⟨θ, AgreeOutside.refl θ, ?_, fun _ inside => absurd inside List.not_mem_nil⟩
        unfold Holds at held
        split at held
        · rename_i inRests
          obtain ⟨tail, restValue, listed⟩ := held
          rw [if_pos inRests, OrderedRows.inst_vectorTerm (list := .var _) (items := tail) listed, ← restValue, value]
        · rename_i outside
          rw [if_neg outside, DemandTransformation.inst_unknown, held, value]
    | .bvar _, _, _, _, _, lowered, _, s, found, matched, _, _, _, θ, _ => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        cases matched
        exact ⟨θ, AgreeOutside.refl θ, by simp [encode], fun _ inside => absurd inside List.not_mem_nil⟩
    | .apply label arguments, _, _, _, _, lowered, named, s, found, matched, data, witness, above, θ, holds => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, rowFound, rfl, rfl, rfl⟩ := lowered
        cases s with
        | apply label' items =>
            cases matched with
            | apply argumentsMatched _ =>
              simp only [OrderedMatching.isData] at data
              obtain ⟨θ', agree, listed, goalsHold⟩ := matchRows_complete included arguments rowFound
                (fun name inside => named name (by simpa [names] using inside)) argumentsMatched data above
                (fun name inside => holds name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
                (fun u inside => by simp at inside)
              refine ⟨θ', agree, ?_, goalsHold⟩
              rw [List.append_nil] at listed
              simp [encode, listed]
        | _ => cases matched
    | .collection .vec elements none, _, _, _, _, lowered, named, s, found, matched, data, witness, above, θ,
        holds => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, rowFound, rfl, rfl, rfl⟩ := lowered
        cases s with
        | collection kind' items termRest =>
            cases matched with
            | collection notVector _ => exact absurd rfl notVector
            | vector elementsMatched =>
              simp only [OrderedMatching.isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
              obtain ⟨rfl, data⟩ := data
              obtain ⟨θ', agree, listed, goalsHold⟩ := matchRows_complete included elements rowFound
                (fun name inside => named name (by simpa [names] using inside)) elementsMatched data above
                (fun name inside => holds name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
                (fun u inside => by simp at inside)
              refine ⟨θ', agree, ?_, goalsHold⟩
              rw [List.append_nil] at listed
              exact OrderedRows.inst_vectorTerm listed
        | _ => cases matched
    | .collection .vec elements (some restName), _, _, _, _, lowered, named, s, found, matched, data, witness, above,
        θ, holds => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, rowFound, rfl, rfl, rfl⟩ := lowered
          cases s with
          | collection kind' items termRest =>
              cases matched with
              | collection notVector _ => exact absurd rfl notVector
              | vectorRest prefixMatched merged =>
                simp only [OrderedMatching.isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
                obtain ⟨rfl, data⟩ := data
                have restValue := lookup_of_extends_single (extends_of_merge_right merged above)
                have restHolds := holds restName (by simp [names])
                simp only [Holds, if_pos inRests] at restHolds
                obtain ⟨tail, restIs, restListed⟩ := restHolds
                rw [restValue] at restIs
                cases restIs
                have prefixData : OrderedMatching.isDataList (items.take elements.length) = true :=
                  OrderedMatching.isDataList_iff.mpr fun term member =>
                    OrderedMatching.isDataList_iff.mp data term (List.mem_of_mem_take member)
                obtain ⟨θ', agree, listed, goalsHold⟩ := matchRows_complete included elements rowFound
                  (fun name inside => named name (by simp [names, inside])) prefixMatched prefixData
                  (extends_of_merge_left merged above) (fun name inside => holds name (by simp [names, inside]))
                  (tail := items.drop elements.length) (by simpa using restListed)
                  (fun u inside => by
                    simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inside
                    subst inside
                    exact untouched_name (named restName (by simp [names])) _ _)
                refine ⟨θ', agree, ?_, goalsHold⟩
                rw [List.take_append_drop] at listed
                exact OrderedRows.inst_vectorTerm listed
          | _ => cases matched
        · cases lowered
    | .collection .hashBag elements rest, next, _, _, _, lowered, named, s, found, matched, data, witness, above,
        θ, holds => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i restOutside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          cases s with
          | collection kind' items termRest =>
              cases matched with
              | collection _ bagMatched =>
                simp only [OrderedMatching.isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
                obtain ⟨rfl, data⟩ := data
                exact bag_complete (pickGoals_scope elements picked).1 named holds fun θ₁ holds₁ listed untouched =>
                  pickGoals_complete included elements picked (by decide) restOutside
                    (fun name inside => named name (by simpa [names] using inside)) bagMatched data above holds₁ listed
                    untouched
          | _ => cases matched
        · cases lowered
    | .collection .hashSet elements rest, next, _, _, _, lowered, named, s, found, matched, data, witness, above,
        θ, holds => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i restOutside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          cases s with
          | collection kind' items termRest =>
              cases matched with
              | collection _ bagMatched =>
                simp only [OrderedMatching.isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
                obtain ⟨rfl, data⟩ := data
                exact bag_complete (pickGoals_scope elements picked).1 named holds fun θ₁ holds₁ listed untouched =>
                  pickGoals_complete included elements picked (by decide) restOutside
                    (fun name inside => named name (by simpa [names] using inside)) bagMatched data above holds₁ listed
                    untouched
          | _ => cases matched
        · cases lowered
    | .lambda _ body, next, _, _, _, lowered, named, s, found, matched, data, witness, above, θ, holds => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, rowFound, rfl, rfl, rfl⟩ := lowered
        cases s with
        | lambda binder' body' =>
            cases matched with
            | lambda bodyMatched =>
              simp only [OrderedMatching.isData, Bool.and_eq_true, Option.isNone_iff_eq_none] at data
              obtain ⟨rfl, bodyData⟩ := data
              obtain ⟨θ', agree, bodyIs, goalsHold⟩ := matchRow_complete included body rowFound
                (fun name inside => named name (by simpa [names] using inside)) bodyMatched bodyData above
                (fun name inside => holds name (by simpa [names] using inside))
              exact ⟨θ', agree, by simp [encode, bodyIs, RootRewritesOnTheStep.optionRow], goalsHold⟩
        | _ => cases matched
    | .multiLambda arity _ body, next, _, _, _, lowered, named, s, found, matched, data, witness, above, θ,
        holds => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, rowFound, rfl, rfl, rfl⟩ := lowered
        cases s with
        | multiLambda arity' binders' body' =>
            cases matched with
            | multiLambda bodyMatched =>
              simp only [OrderedMatching.isData, Bool.and_eq_true, List.isEmpty_iff] at data
              obtain ⟨rfl, bodyData⟩ := data
              obtain ⟨θ', agree, bodyIs, goalsHold⟩ := matchRow_complete included body rowFound
                (fun name inside => named name (by simpa [names] using inside)) bodyMatched bodyData above
                (fun name inside => holds name (by simpa [names] using inside))
              exact ⟨θ', agree, by simp [encode, bodyIs, RootRewritesOnTheStep.namesRow], goalsHold⟩
        | _ => cases matched
    | .subst body value, next, _, _, _, lowered, named, s, found, matched, data, witness, above, θ, holds => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        cases s with
        | subst body' value' =>
            cases matched with
            | subst bodyMatched valueMatched merged =>
              simp only [OrderedMatching.isData, Bool.and_eq_true] at data
              obtain ⟨bodyOrdered, bodyScope⟩ := matchRow_scope body bodyFound
              obtain ⟨valueOrdered, -⟩ := matchRow_scope value valueFound
              have bodyNamed : ∀ name ∈ names body, name ∈ avoid :=
                fun name inside => named name (by simp [names, inside])
              have valueNamed : ∀ name ∈ names value, name ∈ avoid :=
                fun name inside => named name (by simp [names, inside])
              obtain ⟨θ₁, agree₁, bodyIs, bodyHolds⟩ := matchRow_complete included body bodyFound bodyNamed
                bodyMatched data.1 (extends_of_merge_left merged above)
                fun name inside => holds name (by simp [names, inside])
              have onValueNames : ∀ name ∈ names value, θ₁ (labelCode name) = θ (labelCode name) :=
                fun name inside => agree₁ _ (untouched_name (valueNamed name inside) _ _)
              obtain ⟨θ₂, agree₂, valueIs, valueHolds⟩ := matchRow_complete included value valueFound valueNamed
                valueMatched data.2 (extends_of_merge_right merged above)
                (fun name inside => holds_congr (onValueNames name inside) (holds name (by simp [names, inside])))
              have bodyStays : ∀ u ∈ unknowns bodyRow ++ bodyGoals.flatMap goalUnknowns, θ₂ u = θ₁ u :=
                fun u inside => agree₂ u ((bodyScope u inside).untouched bodyNamed (.inl le_rfl))
              refine ⟨θ₂, agree₁.trans agree₂ bodyOrdered valueOrdered, ?_, fun g inside => ?_⟩
              · simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, encode, valueIs]
                rw [DemandTransformation.inst_agree bodyRow fun u inside => bodyStays u (List.mem_append_left _ inside),
                  bodyIs]
              · rcases List.mem_append.mp inside with inBody | inValue
                · exact goals_agree (fun u inU => bodyStays u (List.mem_append_right _ inU)) bodyHolds g inBody
                · exact valueHolds g inValue
        | _ => cases matched

  theorem matchRows_complete (included : CollectionClausesIn program) : ∀ (patterns : List Pattern) {next next' : ℕ}
      {close list : Tm} {goals : List Goal}, matchRows rests avoid next patterns close = some (list, goals, next') →
      (∀ name ∈ namesList patterns, name ∈ avoid) → ∀ {heads : List Pattern} {found : Bindings},
      MatchArgsRel patterns heads found → OrderedMatching.isDataList heads = true → ∀ {witness : Bindings},
      BindingsExtends found witness → ∀ {θ : ℕ → Expr}, (∀ name ∈ namesList patterns, Holds rests θ witness name) →
      ∀ {tail : List Pattern}, inst θ close = encodeList tail → (∀ u ∈ unknowns close, Untouched avoid next next' u) →
      ∃ θ', AgreeOutside avoid next next' θ θ' ∧ inst θ' list = encodeList (heads ++ tail) ∧
        ∀ g ∈ goals, goalHolds R (Derives R program) θ' g
    | [], _, _, _, _, _, lowered, _, heads, found, matched, _, _, _, θ, _, tail, closed, _ => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        cases matched
        exact ⟨θ, AgreeOutside.refl θ, closed, fun _ inside => absurd inside List.not_mem_nil⟩
    | pattern :: patterns, next, _, close, _, _, lowered, named, heads, _, matched, data, witness, above, θ, holds,
        tail, closed, closeUntouched => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tailRow, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        dsimp only at tailFound closeUntouched ⊢
        cases heads with
        | nil => cases matched
        | cons h hs =>
          cases matched with
          | cons headMatched tailMatched merged =>
            simp only [OrderedMatching.isDataList, Bool.and_eq_true] at data
            obtain ⟨headOrdered, headScope⟩ := matchRow_scope pattern headFound
            obtain ⟨tailOrdered, -⟩ := matchRows_scope patterns tailFound
            have headNamed : ∀ name ∈ names pattern, name ∈ avoid :=
              fun name inside => named name (by simp [namesList, inside])
            have tailNamed : ∀ name ∈ namesList patterns, name ∈ avoid :=
              fun name inside => named name (by simp [namesList, inside])
            obtain ⟨θ₁, agree₁, headIs, headHolds⟩ := matchRow_complete included pattern headFound headNamed
              headMatched data.1 (extends_of_merge_left merged above)
              fun name inside => holds name (by simp [namesList, inside])
            have onTailNames : ∀ name ∈ namesList patterns, θ₁ (labelCode name) = θ (labelCode name) :=
              fun name inside => agree₁ _ (untouched_name (tailNamed name inside) _ _)
            obtain ⟨θ₂, agree₂, tailIs, tailHolds⟩ := matchRows_complete included patterns tailFound tailNamed
              tailMatched data.2 (extends_of_merge_right merged above)
              (fun name inside => holds_congr (onTailNames name inside) (holds name (by simp [namesList, inside])))
              (tail := tail)
              (by rw [← closed]; exact DemandTransformation.inst_agree close fun u inside =>
                agree₁ u fun k low high => closeUntouched u inside k low (by omega))
              (fun u inside k low high => closeUntouched u inside k (by omega) high)
            have headStays : ∀ u ∈ unknowns head ++ headGoals.flatMap goalUnknowns, θ₂ u = θ₁ u := fun u inside =>
              agree₂ u ((headScope u inside).untouched headNamed (.inl le_rfl))
            refine ⟨θ₂, agree₁.trans agree₂ headOrdered tailOrdered, ?_, fun g inside => ?_⟩
            · simp only [RootRewritesOnTheStep.inst_appTerm, List.cons_append, encodeList, tailIs]
              rw [DemandTransformation.inst_agree head fun u inside => headStays u (List.mem_append_left _ inside),
                headIs]
            · rcases List.mem_append.mp inside with inHead | inTail
              · exact goals_agree (fun u inU => headStays u (List.mem_append_right _ inU)) headHolds g inHead
              · exact tailHolds g inTail

  theorem pickGoals_complete (included : CollectionClausesIn program) : ∀ (elements : List Pattern) {next next' : ℕ}
      {kind : CollType} {list : Tm} {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') → kind ≠ .vec →
      rest.all (fun name => !rests.contains name) = true →
      (∀ name ∈ namesList elements ++ rest.toList, name ∈ avoid) → ∀ {items : List Pattern} {found : Bindings},
      MatchBagRel elements rest kind items found → OrderedMatching.isDataList items = true → ∀ {witness : Bindings},
      BindingsExtends found witness → ∀ {θ : ℕ → Expr},
      (∀ name ∈ namesList elements ++ rest.toList, Holds rests θ witness name) → inst θ list = encodeList items →
      (∀ u ∈ unknowns list, Untouched avoid next next' u) →
      ∃ θ', AgreeOutside avoid next next' θ θ' ∧ ∀ g ∈ goals, goalHolds R (Derives R program) θ' g
    | [], _, _, kind, list, rest, _, lowered, unordered, outside, _, items, found, matched, _, witness, above, θ,
        holds, listed, _ => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl⟩ := lowered
        refine ⟨θ, AgreeOutside.refl θ, fun g inside => ?_⟩
        rw [List.mem_singleton] at inside
        subst inside
        have wrapped := wrap_complete (R := R) included.wraps unordered items
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, listed]
        cases rest with
        | none =>
            cases matched
            simpa [restRow, inst_collectionTerm, encode_collection, encodeList] using wrapped
        | some restName =>
            cases matched
            have notRest : restName ∉ rests := by simpa using outside
            have held := holds restName (by simp [namesList])
            simp only [Holds, if_neg notRest] at held
            rw [lookup_of_extends_single above] at held
            simpa [restRow, held] using wrapped
    | element :: elements, next, _, kind, list, rest, _, lowered, unordered, outside, named, items, found, matched,
        data, witness, above, θ, holds, listed, listUntouched => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, rowFound, ⟨laterGoals, last⟩, laterFound, rfl, rfl⟩ := lowered
        dsimp only at laterFound listUntouched ⊢
        cases matched with
        | cons index bound elementMatched laterMatched merged =>
          obtain ⟨rowOrdered, rowScope⟩ := matchRow_scope element rowFound
          obtain ⟨laterOrdered, -⟩ := pickGoals_scope elements laterFound
          have elementNamed : ∀ name ∈ names element, name ∈ avoid :=
            fun name inside => named name (by simp [namesList, inside])
          have laterNamed : ∀ name ∈ namesList elements ++ rest.toList, name ∈ avoid := fun name inside => by
            rcases List.mem_append.mp inside with inElements | inRest
            · exact named name (by simp [namesList, inElements])
            · exact named name (by simp [inRest])
          have elementData : isData items[index] = true :=
            OrderedMatching.isDataList_iff.mp data _ (List.getElem_mem bound)
          obtain ⟨θ₁, agree₁, rowIs, elementHolds⟩ := matchRow_complete included element rowFound elementNamed
            elementMatched elementData (extends_of_merge_left merged above)
            fun name inside => holds name (by simp [namesList, inside])
          obtain ⟨θ₂, θ₂Is⟩ : ∃ θ₂ : ℕ → Expr,
              θ₂ = Function.update θ₁ (listUnknown avoid middle) (encodeList (items.eraseIdx index)) := ⟨_, rfl⟩
          have middleFresh : ∀ k, middle + 1 ≤ k → listUnknown avoid middle ≠ listUnknown avoid k := fun k low same => by
            have := listUnknown_injective avoid same
            omega
          have onLaterNames : ∀ name ∈ namesList elements ++ rest.toList, θ₂ (labelCode name) = θ (labelCode name) :=
            fun name inside => by
              rw [θ₂Is, Function.update_of_ne (listUnknown_ne (laterNamed name inside) middle).symm]
              exact agree₁ _ (untouched_name (laterNamed name inside) _ _)
          have laterData : OrderedMatching.isDataList (items.eraseIdx index) = true :=
            OrderedMatching.isDataList_iff.mpr fun term member =>
              OrderedMatching.isDataList_iff.mp data term (List.mem_of_mem_eraseIdx member)
          obtain ⟨θ₃, agree₃, laterHolds⟩ := pickGoals_complete included elements laterFound unordered outside
            laterNamed laterMatched laterData (extends_of_merge_right merged above)
            (fun name inside => holds_congr (onLaterNames name inside) (holds name (by
              rcases List.mem_append.mp inside with inElements | inRest
              · simp [namesList, inElements]
              · simp [inRest])))
            (by simp [θ₂Is])
            (fun u inside => by
              simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inside
              subst inside
              exact fun k low _ => middleFresh k low)
          have tailKept : θ₃ (listUnknown avoid middle) = encodeList (items.eraseIdx index) := by
            rw [agree₃ _ fun k low _ => middleFresh k low]
            simp [θ₂Is]
          have rowStays : ∀ u ∈ unknowns row ++ elementGoals.flatMap goalUnknowns, θ₃ u = θ₁ u := fun u inside => by
            have within := rowScope u inside
            rw [agree₃ u (within.untouched elementNamed (.inl (by omega))), θ₂Is]
            exact Function.update_of_ne (fun same =>
              (within.untouched (c := middle) (d := middle + 1) elementNamed (.inl le_rfl)) middle le_rfl
                (by omega) same) _ _
          have listStays : inst θ₃ list = encodeList items := by
            rw [← listed]
            exact DemandTransformation.inst_agree list fun u inside => by
              rw [agree₃ u fun k low high => listUntouched u inside k (by omega) high, θ₂Is]
              rw [Function.update_of_ne (fun same => listUntouched u inside middle rowOrdered (by omega) same)]
              exact agree₁ u fun k low high => listUntouched u inside k low (by omega)
          refine ⟨θ₃, fun u untouched => ?_, fun g inside => ?_⟩
          · rw [agree₃ u fun k low high => untouched k (by omega) high, θ₂Is]
            rw [Function.update_of_ne (fun same => untouched middle rowOrdered (by omega) same)]
            exact agree₁ u fun k low high => untouched k low (by omega)
          · rcases List.mem_append.mp inside with inFirst | inLater
            · rcases List.mem_cons.mp inFirst with rfl | inElement
              · simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
                  listStays, tailKept]
                rw [DemandTransformation.inst_agree row fun u inside => rowStays u (List.mem_append_left _ inside),
                  rowIs]
                exact pick_complete included.picks items index bound
              · exact goals_agree (fun u inU => rowStays u (List.mem_append_right _ inU)) elementHolds g inElement
            · exact laterHolds g inLater
end

end Complete

/-! ## Unwrapping a bag or a set into its list -/

/-- The relation that unwraps a bag or a set into its kind and list. -/
def unwrapRelation : ℕ := 5

/-- Unwrapping a collection of the kind. -/
def unwrapClause (kind : CollType) : Clause :=
  { relation := unwrapRelation, input := collectionTerm kind (.var 0),
    output := appTerm (symTerm (collectionCode kind)) (.var 0), body := [] }

/-- The clauses of unwrapping: a bag, a set. -/
def unwrapClauses : List Clause := [unwrapClause .hashBag, unwrapClause .hashSet]

section Unwrap

variable {R : Relations} {program : List Clause}

/-- **A derived unwrap reads a collection of the kind off its list.** -/
theorem unwrap_sound (onlyUnwraps : ∀ c ∈ program, c.relation = unwrapRelation → c ∈ unwrapClauses)
    {kind : CollType} {x list : Expr}
    (derived : Derives R program unwrapRelation x (.app (.sym (collectionCode kind)) list)) :
    x = .app (.sym 6) (.app (.sym (collectionCode kind)) (.app list (.sym 0))) := by
  obtain ⟨depth, derivedAt⟩ := derived
  cases depth with
  | zero => exact derivedAt.elim
  | succ depth =>
      obtain ⟨c, member, isUnwrap, θ, input, output, -⟩ := derivedAt
      have unwrapped := onlyUnwraps c member isUnwrap
      simp only [unwrapClauses, List.mem_cons, List.not_mem_nil, or_false] at unwrapped
      rcases unwrapped with rfl | rfl
      all_goals
        simp only [unwrapClause, inst_collectionTerm, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq, Expr.sym.injEq]
          at input output
        obtain ⟨kindIs, listIs⟩ := output
        rw [← input, listIs, ← kindIs]

/-- **A collection of the kind is unwrapped into its list.** -/
theorem unwrap_complete (included : ∀ c ∈ unwrapClauses, c ∈ program) {kind : CollType} (unordered : kind ≠ .vec)
    (list : Expr) :
    Derives R program unwrapRelation (.app (.sym 6) (.app (.sym (collectionCode kind)) (.app list (.sym 0))))
      (.app (.sym (collectionCode kind)) list) := by
  have member : unwrapClause kind ∈ program := by
    cases kind with
    | vec => exact absurd rfl unordered
    | hashBag => exact included _ (by simp [unwrapClauses])
    | hashSet => exact included _ (by simp [unwrapClauses])
  have clause := derives_of_clause (R := R) member (pick [list]) (fun _ inside => absurd inside List.not_mem_nil)
  simpa [unwrapClause, pick, inst_collectionTerm] using clause

end Unwrap

theorem find_of_lookup_collection {witness : Bindings} {name : String} {kind : CollType} {items : List Pattern}
    (same : lookupOrFvar witness name = .collection kind items none) :
    witness.find? (·.1 == name) = some (name, .collection kind items none) := by
  cases found : witness.find? (·.1 == name) with
  | none => simp [lookupOrFvar, applyBindings, found] at same
  | some entry =>
      have named := OrderedMatching.find_named found
      rw [named] at found ⊢
      simp only [lookupOrFvar, applyBindings, found] at same
      rw [same]

/-! ## Matching read back -/

/-- The relation that inserts an element into a list: picking read back. -/
def insertRelation : ℕ := 6

/-- Inserting first. -/
def insertHeadClause : Clause :=
  { relation := insertRelation, input := appTerm (.var 0) (.var 1), output := appTerm (.var 0) (.var 1), body := [] }

/-- Inserting later, and keeping the first. -/
def insertTailClause : Clause :=
  { relation := insertRelation, input := appTerm (.var 2) (appTerm (.var 0) (.var 3)),
    output := appTerm (.var 0) (.var 1), body := [.ask insertRelation (appTerm (.var 2) (.var 3)) (.var 1)] }

/-- The clauses of inserting. -/
def insertClauses : List Clause := [insertHeadClause, insertTailClause]

/-- **The collection clauses of a program**: picking, wrapping, inserting and unwrapping each have exactly their
own clauses. -/
structure CollectionProgram (program : List Clause) : Prop where
  picks : ∀ c ∈ pickClauses, c ∈ program
  wraps : ∀ c ∈ wrapClauses, c ∈ program
  inserts : ∀ c ∈ insertClauses, c ∈ program
  unwraps : ∀ c ∈ unwrapClauses, c ∈ program
  onlyPicks : ∀ c ∈ program, c.relation = pickRelation → c ∈ pickClauses
  onlyWraps : ∀ c ∈ program, c.relation = wrapRelation → c ∈ wrapClauses
  onlyInserts : ∀ c ∈ program, c.relation = insertRelation → c ∈ insertClauses
  onlyUnwraps : ∀ c ∈ program, c.relation = unwrapRelation → c ∈ unwrapClauses

theorem CollectionProgram.sound {program : List Clause} (collections : CollectionProgram program) :
    CollectionClauses program :=
  ⟨collections.onlyPicks, collections.onlyWraps⟩

theorem CollectionProgram.included {program : List Clause} (collections : CollectionProgram program) :
    CollectionClausesIn program :=
  ⟨collections.picks, collections.wraps⟩

section ReadBack

variable {R : Relations} {program : List Clause}

/-- **A derived insertion is a pick read back.** -/
theorem pick_of_insert (collections : CollectionProgram program) :
    ∀ (depth : ℕ) {x y : Expr}, DerivesAt R program depth insertRelation x y → Derives R program pickRelation y x
  | 0, _, _, derived => derived.elim
  | depth + 1, x, y, derived => by
      obtain ⟨c, member, isInsert, θ, input, output, goals⟩ := derived
      have inserted := collections.onlyInserts c member isInsert
      simp only [insertClauses, List.mem_cons, List.not_mem_nil, or_false] at inserted
      rcases inserted with rfl | rfl
      · have clause := derives_of_clause (R := R) (collections.picks pickHeadClause (by simp [pickClauses])) θ
          (fun _ inside => absurd inside List.not_mem_nil)
        simp only [insertHeadClause, pickHeadClause, RootRewritesOnTheStep.inst_appTerm,
          DemandTransformation.inst_unknown] at input output clause
        rw [← input, ← output]
        exact clause
      · have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at asked
        have inner := pick_of_insert collections depth asked
        have clause := derives_of_clause (R := R) (collections.picks pickTailClause (by simp [pickClauses])) θ
          (fun g inside => by
            simp only [pickTailClause, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds] using inner)
        simp only [insertTailClause, pickTailClause, RootRewritesOnTheStep.inst_appTerm,
          DemandTransformation.inst_unknown] at input output clause
        rw [← input, ← output]
        exact clause

/-- **A derived pick is an insertion read back.** -/
theorem insert_of_pick (collections : CollectionProgram program) :
    ∀ (depth : ℕ) {x y : Expr}, DerivesAt R program depth pickRelation x y → Derives R program insertRelation y x
  | 0, _, _, derived => derived.elim
  | depth + 1, x, y, derived => by
      obtain ⟨c, member, isPick, θ, input, output, goals⟩ := derived
      have picked := collections.onlyPicks c member isPick
      simp only [pickClauses, List.mem_cons, List.not_mem_nil, or_false] at picked
      rcases picked with rfl | rfl
      · have clause := derives_of_clause (R := R) (collections.inserts insertHeadClause (by simp [insertClauses])) θ
          (fun _ inside => absurd inside List.not_mem_nil)
        simp only [insertHeadClause, pickHeadClause, RootRewritesOnTheStep.inst_appTerm,
          DemandTransformation.inst_unknown] at input output clause
        rw [← input, ← output]
        exact clause
      · have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at asked
        have inner := insert_of_pick collections depth asked
        have clause := derives_of_clause (R := R) (collections.inserts insertTailClause (by simp [insertClauses])) θ
          (fun g inside => by
            simp only [insertTailClause, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds] using inner)
        simp only [insertTailClause, pickTailClause, RootRewritesOnTheStep.inst_appTerm,
          DemandTransformation.inst_unknown] at input output clause
        rw [← input, ← output]
        exact clause

/-- **A derived unwrap is a wrap read back.** -/
theorem wrap_of_unwrap (collections : CollectionProgram program) {x y : Expr}
    (derived : Derives R program unwrapRelation x y) : Derives R program wrapRelation y x := by
  obtain ⟨depth, derivedAt⟩ := derived
  cases depth with
  | zero => exact derivedAt.elim
  | succ depth =>
      obtain ⟨c, member, isUnwrap, θ, input, output, -⟩ := derivedAt
      have unwrapped := collections.onlyUnwraps c member isUnwrap
      simp only [unwrapClauses, List.mem_cons, List.not_mem_nil, or_false] at unwrapped
      rcases unwrapped with rfl | rfl
      · have clause := derives_of_clause (R := R) (collections.wraps (wrapClause .hashBag) (by simp [wrapClauses])) θ
          (fun _ inside => absurd inside List.not_mem_nil)
        simp only [unwrapClause, wrapClause] at input output clause
        rw [← input, ← output]
        exact clause
      · have clause := derives_of_clause (R := R) (collections.wraps (wrapClause .hashSet) (by simp [wrapClauses])) θ
          (fun _ inside => absurd inside List.not_mem_nil)
        simp only [unwrapClause, wrapClause] at input output clause
        rw [← input, ← output]
        exact clause

/-- **A derived wrap is an unwrap read back.** -/
theorem unwrap_of_wrap (collections : CollectionProgram program) {x y : Expr}
    (derived : Derives R program wrapRelation x y) : Derives R program unwrapRelation y x := by
  obtain ⟨depth, derivedAt⟩ := derived
  cases depth with
  | zero => exact derivedAt.elim
  | succ depth =>
      obtain ⟨c, member, isWrap, θ, input, output, -⟩ := derivedAt
      have wrapped := collections.onlyWraps c member isWrap
      simp only [wrapClauses, List.mem_cons, List.not_mem_nil, or_false] at wrapped
      rcases wrapped with rfl | rfl
      · have clause := derives_of_clause (R := R)
          (collections.unwraps (unwrapClause .hashBag) (by simp [unwrapClauses])) θ
          (fun _ inside => absurd inside List.not_mem_nil)
        simp only [unwrapClause, wrapClause] at input output clause
        rw [← input, ← output]
        exact clause
      · have clause := derives_of_clause (R := R)
          (collections.unwraps (unwrapClause .hashSet) (by simp [unwrapClauses])) θ
          (fun _ inside => absurd inside List.not_mem_nil)
        simp only [unwrapClause, wrapClause] at input output clause
        rw [← input, ← output]
        exact clause

end ReadBack

/-- The relation that reads a matching relation back: inserting reads picking back, unwrapping reads wrapping back. -/
def readBack (relation : ℕ) : ℕ := if relation = pickRelation then insertRelation else unwrapRelation

/-- A goal read back: its relation read back, its input and output exchanged. -/
def invertGoal : Goal → Goal
  | .ask relation input output => .ask (readBack relation) output input
  | .query condition => .query condition

/-- **Goals read back**, in the opposite order. -/
def invertGoals (goals : List Goal) : List Goal := (goals.map invertGoal).reverse

@[simp] theorem invertGoals_nil : invertGoals [] = [] := rfl

theorem invertGoals_append (first second : List Goal) :
    invertGoals (first ++ second) = invertGoals second ++ invertGoals first := by
  simp [invertGoals]

theorem invertGoals_cons (g : Goal) (goals : List Goal) :
    invertGoals (g :: goals) = invertGoals goals ++ [invertGoal g] := by
  simp [invertGoals]

theorem goalUnknowns_invertGoal (g : Goal) (u : ℕ) :
    u ∈ goalUnknowns (invertGoal g) ↔ u ∈ goalUnknowns g := by
  cases g with
  | query condition => rfl
  | ask relation input output =>
      simp only [invertGoal, goalUnknowns, List.mem_append]
      exact Or.comm

theorem mem_invertGoals_unknowns {goals : List Goal} {u : ℕ} :
    u ∈ (invertGoals goals).flatMap goalUnknowns ↔ u ∈ goals.flatMap goalUnknowns := by
  simp only [invertGoals, List.mem_flatMap, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨_, ⟨g, inside, rfl⟩, inU⟩
    exact ⟨g, inside, (goalUnknowns_invertGoal g u).mp inU⟩
  · rintro ⟨g, inside, inU⟩
    exact ⟨_, ⟨g, inside, rfl⟩, (goalUnknowns_invertGoal g u).mpr inU⟩

/-- A goal of matching: a pick or a wrap. -/
def MatchingGoal : Goal → Prop
  | .ask relation _ _ => relation = pickRelation ∨ relation = wrapRelation
  | .query _ => False

theorem invertGoal_holds {R : Relations} {program : List Clause} (collections : CollectionProgram program)
    {θ : ℕ → Expr} {g : Goal} (matching : MatchingGoal g) :
    goalHolds R (Derives R program) θ (invertGoal g) ↔ goalHolds R (Derives R program) θ g := by
  cases g with
  | query condition => exact matching.elim
  | ask relation input output =>
      simp only [MatchingGoal] at matching
      rcases matching with rfl | rfl
      · simp only [invertGoal, readBack, goalHolds]
        constructor
        · rintro ⟨depth, derived⟩
          exact pick_of_insert collections depth derived
        · rintro ⟨depth, derived⟩
          exact insert_of_pick collections depth derived
      · simp only [invertGoal, readBack, show wrapRelation ≠ pickRelation by decide, if_false, goalHolds]
        exact ⟨wrap_of_unwrap collections, unwrap_of_wrap collections⟩

/-- **Goals of matching read back hold exactly when they hold.** -/
theorem invertGoals_hold {R : Relations} {program : List Clause} (collections : CollectionProgram program)
    {θ : ℕ → Expr} {goals : List Goal} (matching : ∀ g ∈ goals, MatchingGoal g) :
    (∀ g ∈ invertGoals goals, goalHolds R (Derives R program) θ g) ↔
      ∀ g ∈ goals, goalHolds R (Derives R program) θ g := by
  simp only [invertGoals, List.mem_reverse, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun holds g inside => (invertGoal_holds collections (matching g inside)).mp (holds g inside),
    fun holds g inside => (invertGoal_holds collections (matching g inside)).mpr (holds g inside)⟩

mutual
  theorem matchRow_matching : ∀ (p : Pattern) {next next' : ℕ} {t : Tm} {goals : List Goal},
      matchRow rests avoid next p = some (t, goals, next') → ∀ g ∈ goals, MatchingGoal g
    | .fvar _, _, _, _, _, lowered => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        exact fun _ inside => absurd inside List.not_mem_nil
    | .bvar _, _, _, _, _, lowered => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        exact fun _ inside => absurd inside List.not_mem_nil
    | .apply _ arguments, _, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, -, rfl, -⟩ := lowered
        exact matchRows_matching arguments found
    | .collection .vec elements none, _, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, -, rfl, -⟩ := lowered
        exact matchRows_matching elements found
    | .collection .vec elements (some _), _, _, _, _, lowered => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, -, rfl, -⟩ := lowered
          exact matchRows_matching elements found
        · cases lowered
    | .collection .hashBag elements rest, _, _, _, _, lowered => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, -, rfl, -⟩ := lowered
          exact pickGoals_matching elements picked
        · cases lowered
    | .collection .hashSet elements rest, _, _, _, _, lowered => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, -, rfl, -⟩ := lowered
          exact pickGoals_matching elements picked
        · cases lowered
    | .lambda _ body, _, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, -, rfl, -⟩ := lowered
        exact matchRow_matching body found
    | .multiLambda _ _ body, _, _, _, _, lowered => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, -, rfl, -⟩ := lowered
        exact matchRow_matching body found
    | .subst body value, _, _, _, _, lowered => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, -, rfl, -⟩ :=
          lowered
        intro g inside
        rcases List.mem_append.mp inside with inBody | inValue
        · exact matchRow_matching body bodyFound g inBody
        · exact matchRow_matching value valueFound g inValue

  theorem matchRows_matching : ∀ (patterns : List Pattern) {next next' : ℕ} {close list : Tm} {goals : List Goal},
      matchRows rests avoid next patterns close = some (list, goals, next') → ∀ g ∈ goals, MatchingGoal g
    | [], _, _, _, _, _, lowered => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨-, rfl, -⟩ := lowered
        exact fun _ inside => absurd inside List.not_mem_nil
    | pattern :: patterns, _, _, _, _, _, lowered => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, -, rfl, -⟩ := lowered
        intro g inside
        rcases List.mem_append.mp inside with inHead | inTail
        · exact matchRow_matching pattern headFound g inHead
        · exact matchRows_matching patterns tailFound g inTail

  theorem pickGoals_matching : ∀ (elements : List Pattern) {next next' : ℕ} {kind : CollType} {list : Tm}
      {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') → ∀ g ∈ goals, MatchingGoal g
    | [], _, _, _, _, _, _, lowered => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, -⟩ := lowered
        intro g inside
        simp only [List.mem_singleton] at inside
        subst inside
        exact .inr rfl
    | element :: elements, _, _, _, _, _, _, lowered => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, found, ⟨laterGoals, last⟩, laterFound, rfl, -⟩ := lowered
        dsimp only at laterFound
        intro g inside
        rcases List.mem_append.mp inside with inFirst | inLater
        · rcases List.mem_cons.mp inFirst with rfl | inElement
          · exact .inl rfl
          · exact matchRow_matching element found g inElement
        · exact pickGoals_matching elements laterFound g inLater
end

/-! ## Terms read back off their rows -/

section Decode

variable {R : Relations} {program : List Clause}

/-- **A pick of an element beside a list is a pick from a list.** -/
theorem pick_decodes (onlyPicks : ∀ c ∈ program, c.relation = pickRelation → c ∈ pickClauses) :
    ∀ (depth : ℕ) {list : Expr} {x : Pattern} {ys : List Pattern},
      DerivesAt R program depth pickRelation list (.app (encode x) (encodeList ys)) → ∃ items, list = encodeList items
  | 0, _, _, _, derived => derived.elim
  | depth + 1, list, x, ys, derived => by
      obtain ⟨c, member, isPick, θ, input, output, goals⟩ := derived
      have picked := onlyPicks c member isPick
      simp only [pickClauses, List.mem_cons, List.not_mem_nil, or_false] at picked
      rcases picked with rfl | rfl
      · simp only [pickHeadClause, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at input output
        exact ⟨x :: ys, by rw [← input, output]; rfl⟩
      · simp only [pickTailClause, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input output
        obtain ⟨elementIs, restIs⟩ := output
        obtain ⟨y, ys', rfl, firstIs, laterIs⟩ := encodeList_cons_inv restIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, elementIs,
          laterIs] at asked
        obtain ⟨items, itemsIs⟩ := pick_decodes onlyPicks depth asked
        exact ⟨y :: items, by rw [← input, firstIs, itemsIs]; rfl⟩

/-- **A wrap into a collection is a wrap of a list.** -/
theorem wrap_decodes (onlyWraps : ∀ c ∈ program, c.relation = wrapRelation → c ∈ wrapClauses) {kind : CollType}
    {list : Expr} {value : Pattern}
    (derived : Derives R program wrapRelation (.app (.sym (collectionCode kind)) list) (encode value)) :
    ∃ items, list = encodeList items := by
  obtain ⟨depth, derivedAt⟩ := derived
  cases depth with
  | zero => exact derivedAt.elim
  | succ depth =>
      obtain ⟨c, member, isWrap, θ, input, output, -⟩ := derivedAt
      have wrapped := onlyWraps c member isWrap
      simp only [wrapClauses, List.mem_cons, List.not_mem_nil, or_false] at wrapped
      rcases wrapped with rfl | rfl
      all_goals
        simp only [wrapClause, inst_collectionTerm, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨-, listIs⟩ := input
        rw [listIs] at output
        obtain ⟨items, -, itemsIs⟩ := encode_closed_inv output
        exact ⟨items, itemsIs⟩

mutual
  /-- **A matching lowering whose goals hold, at names that are terms, is a term.** -/
  theorem matchRow_decodes (collections : CollectionClauses program) : ∀ (p : Pattern) {next next' : ℕ} {t : Tm}
      {goals : List Goal}, matchRow rests avoid next p = some (t, goals, next') → ∀ {θ : ℕ → Expr},
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) → (∀ name ∈ names p, Captured rests θ name) →
      ∃ s, inst θ t = encode s
    | .fvar name, _, _, _, _, lowered, θ, _, captured => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        have held := captured name (by simp [names])
        unfold Captured at held
        split at held
        · rename_i inRests
          obtain ⟨tail, listed⟩ := held
          exact ⟨.collection .vec tail none, by
            rw [if_pos inRests, OrderedRows.inst_vectorTerm (list := .var (labelCode name)) (items := tail) listed]⟩
        · rename_i outside
          obtain ⟨value, valued⟩ := held
          exact ⟨value, by rw [if_neg outside, DemandTransformation.inst_unknown, valued]⟩
    | .bvar index, _, _, _, _, lowered, θ, _, _ => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨.bvar index, by simp [encode]⟩
    | .apply label arguments, _, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨heads, listed⟩ := matchRows_decodes collections arguments found goals
          (fun name inside => captured name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
        rw [List.append_nil] at listed
        exact ⟨.apply label heads, by simp [encode, listed]⟩
    | .collection .vec elements none, _, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨heads, listed⟩ := matchRows_decodes collections elements found goals
          (fun name inside => captured name (by simpa [names] using inside)) (tail := []) (by simp [encodeList])
        rw [List.append_nil] at listed
        exact ⟨.collection .vec heads none, OrderedRows.inst_vectorTerm listed⟩
    | .collection .vec elements (some restName), _, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          have restCaptured := captured restName (by simp [names])
          simp only [Captured, if_pos inRests] at restCaptured
          obtain ⟨tail, listed⟩ := restCaptured
          obtain ⟨heads, headsListed⟩ := matchRows_decodes collections elements found goals
            (fun name inside => captured name (by simp [names, inside])) (tail := tail) (by simpa using listed)
          exact ⟨.collection .vec (heads ++ tail) none, OrderedRows.inst_vectorTerm headsListed⟩
        · cases lowered
    | .collection .hashBag elements rest, next, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, listed⟩ := pickGoals_decodes collections elements picked outside goals
            (fun name inside => captured name (by simpa [names] using inside))
          refine ⟨.collection .hashBag items none, ?_⟩
          rw [inst_collectionTerm, encode_collection, ← listed]
        · cases lowered
    | .collection .hashSet elements rest, next, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, listed⟩ := pickGoals_decodes collections elements picked outside goals
            (fun name inside => captured name (by simpa [names] using inside))
          refine ⟨.collection .hashSet items none, ?_⟩
          rw [inst_collectionTerm, encode_collection, ← listed]
        · cases lowered
    | .lambda _ body, _, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨s, bodyIs⟩ := matchRow_decodes collections body found goals
          (fun name inside => captured name (by simpa [names] using inside))
        exact ⟨.lambda none s, by simp [encode, bodyIs, RootRewritesOnTheStep.optionRow]⟩
    | .multiLambda arity _ body, _, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨s, bodyIs⟩ := matchRow_decodes collections body found goals
          (fun name inside => captured name (by simpa [names] using inside))
        exact ⟨.multiLambda arity [] s, by simp [encode, bodyIs, RootRewritesOnTheStep.namesRow]⟩
    | .subst body value, _, _, _, _, lowered, θ, goals, captured => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        obtain ⟨s₁, bodyIs⟩ := matchRow_decodes collections body bodyFound
          (fun g inside => goals g (List.mem_append_left _ inside))
          (fun name inside => captured name (by simp [names, inside]))
        obtain ⟨s₂, valueIs⟩ := matchRow_decodes collections value valueFound
          (fun g inside => goals g (List.mem_append_right _ inside))
          (fun name inside => captured name (by simp [names, inside]))
        exact ⟨.subst s₁ s₂, by simp [encode, bodyIs, valueIs]⟩

  theorem matchRows_decodes (collections : CollectionClauses program) : ∀ (patterns : List Pattern) {next next' : ℕ}
      {close list : Tm} {goals : List Goal}, matchRows rests avoid next patterns close = some (list, goals, next') →
      ∀ {θ : ℕ → Expr}, (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ name ∈ namesList patterns, Captured rests θ name) → ∀ {tail : List Pattern}, inst θ close = encodeList tail →
      ∃ heads, inst θ list = encodeList (heads ++ tail)
    | [], _, _, _, _, _, lowered, θ, _, _, tail, closed => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨[], by simpa using closed⟩
    | pattern :: patterns, _, _, _, _, _, lowered, θ, goals, captured, tail, closed => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tailRow, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        obtain ⟨s, headIs⟩ := matchRow_decodes collections pattern headFound
          (fun g inside => goals g (List.mem_append_left _ inside))
          (fun name inside => captured name (by simp [namesList, inside]))
        obtain ⟨heads, tailIs⟩ := matchRows_decodes collections patterns tailFound
          (fun g inside => goals g (List.mem_append_right _ inside))
          (fun name inside => captured name (by simp [namesList, inside])) closed
        exact ⟨s :: heads, by simp [RootRewritesOnTheStep.inst_appTerm, headIs, tailIs, encodeList]⟩

  theorem pickGoals_decodes (collections : CollectionClauses program) : ∀ (elements : List Pattern) {next next' : ℕ}
      {kind : CollType} {list : Tm} {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') →
      rest.all (fun name => !rests.contains name) = true → ∀ {θ : ℕ → Expr},
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ name ∈ namesList elements ++ rest.toList, Captured rests θ name) → ∃ items, inst θ list = encodeList items
    | [], _, _, kind, list, rest, _, lowered, outside, θ, goals, captured => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl⟩ := lowered
        have wrapped := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at wrapped
        cases rest with
        | none =>
            have emptyIs : inst θ (collectionTerm kind (symTerm 0)) = encode (.collection kind [] none) := by
              rw [encode_collection]
              rfl
            simp only [restRow] at wrapped
            rw [emptyIs] at wrapped
            exact wrap_decodes collections.onlyWraps wrapped
        | some restName =>
            have restCaptured := captured restName (by simp)
            have notRest : restName ∉ rests := by simpa using outside
            simp only [Captured, if_neg notRest] at restCaptured
            obtain ⟨value, valued⟩ := restCaptured
            simp only [restRow, DemandTransformation.inst_unknown, valued] at wrapped
            exact wrap_decodes collections.onlyWraps wrapped
    | element :: elements, _, _, kind, list, rest, _, lowered, outside, θ, goals, captured => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, found, ⟨laterGoals, last⟩, laterFound, rfl, rfl⟩ := lowered
        dsimp only at laterFound goals
        obtain ⟨s, rowIs⟩ := matchRow_decodes collections element found
          (fun g inside => goals g (List.mem_append_left _ (List.mem_cons_of_mem _ inside)))
          (fun name inside => captured name (by simp [namesList, inside]))
        obtain ⟨items, laterIs⟩ := pickGoals_decodes collections elements laterFound outside
          (fun g inside => goals g (List.mem_append_right _ inside))
          (fun name inside => captured name (by
            rcases List.mem_append.mp inside with inElements | inRest
            · simp [namesList, inElements]
            · simp [inRest]))
        have picked := goals _ (List.mem_append_left _ List.mem_cons_self)
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, rowIs] at picked
        rw [DemandTransformation.inst_unknown] at laterIs
        rw [laterIs] at picked
        obtain ⟨depth, pickedAt⟩ := picked
        exact pick_decodes collections.onlyPicks depth pickedAt
end

end Decode

/-! ## The goals of a lowering in order -/

open DemandTransformation (InputsBound goalInputs)

theorem matchRows_close : ∀ (patterns : List Pattern) {next next' : ℕ} {close list : Tm} {goals : List Goal},
    matchRows rests avoid next patterns close = some (list, goals, next') → ∀ u ∈ unknowns close, u ∈ unknowns list
  | [], _, _, _, _, _, lowered => by
      simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
      obtain ⟨rfl, -, -⟩ := lowered
      exact fun _ inside => inside
  | pattern :: patterns, _, _, _, _, _, lowered => by
      simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
      obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, -, -⟩ := lowered
      intro u inside
      simp only [RootRewritesOnTheStep.unknowns_appTerm, List.mem_append]
      exact .inr (matchRows_close patterns tailFound u inside)

mutual
  /-- **A matching lowering's goals are bound in order from its row, and bind every name of the pattern.** -/
  theorem matchRow_moded : ∀ (p : Pattern) {next next' : ℕ} {t : Tm} {goals : List Goal},
      matchRow rests avoid next p = some (t, goals, next') → ∀ {bound : List ℕ}, (∀ u ∈ unknowns t, u ∈ bound) →
      InputsBound bound goals ∧ ∀ name ∈ names p, labelCode name ∈ bound ++ goals.flatMap goalUnknowns
    | .fvar name, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        refine ⟨.nil bound, fun other inside => ?_⟩
        simp only [names, List.mem_singleton] at inside
        subst inside
        refine List.mem_append_left _ (rowBound _ ?_)
        split <;> simp
    | .bvar _, _, _, _, _, lowered, bound, _ => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨.nil bound, fun _ inside => by simp [names] at inside⟩
    | .apply _ arguments, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, named⟩ := matchRows_moded arguments found fun u inside => rowBound u (by simpa using inside)
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .collection .vec elements none, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, named⟩ := matchRows_moded elements found fun u inside => rowBound u (by simpa using inside)
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .collection .vec elements (some restName), _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨flows, named⟩ := matchRows_moded elements found fun u inside => rowBound u (by simpa using inside)
          refine ⟨flows, fun name inside => ?_⟩
          simp only [names, Option.toList_some, List.mem_append, List.mem_singleton] at inside
          rcases inside with inElements | rfl
          · exact named name inElements
          · refine List.mem_append_left _ (rowBound _ ?_)
            rw [unknowns_vectorTerm]
            exact matchRows_close elements found _ (by simp)
        · cases lowered
    | .collection .hashBag elements rest, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨flows, named⟩ := pickGoals_moded elements picked fun u inside => rowBound u (by simpa using inside)
          exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
        · cases lowered
    | .collection .hashSet elements rest, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨flows, named⟩ := pickGoals_moded elements picked fun u inside => rowBound u (by simpa using inside)
          exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
        · cases lowered
    | .lambda _ body, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, named⟩ := matchRow_moded body found fun u inside => rowBound u (by simp [inside])
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .multiLambda _ _ body, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, named⟩ := matchRow_moded body found fun u inside => rowBound u (by simp [inside])
        exact ⟨flows, fun name inside => named name (by simpa [names] using inside)⟩
    | .subst body value, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        obtain ⟨bodyFlows, bodyNamed⟩ := matchRow_moded body bodyFound fun u inside => rowBound u (by simp [inside])
        obtain ⟨valueFlows, valueNamed⟩ := matchRow_moded value valueFound
          (bound := bound ++ bodyGoals.flatMap goalUnknowns) fun u inside =>
            List.mem_append_left _ (rowBound u (by simp [inside]))
        refine ⟨bodyFlows.append valueFlows, fun name inside => ?_⟩
        simp only [names, List.mem_append] at inside
        rcases inside with inBody | inValue
        · have here := bodyNamed name inBody
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
        · have here := valueNamed name inValue
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto

  theorem matchRows_moded : ∀ (patterns : List Pattern) {next next' : ℕ} {close list : Tm} {goals : List Goal},
      matchRows rests avoid next patterns close = some (list, goals, next') → ∀ {bound : List ℕ},
      (∀ u ∈ unknowns list, u ∈ bound) →
      InputsBound bound goals ∧ ∀ name ∈ namesList patterns, labelCode name ∈ bound ++ goals.flatMap goalUnknowns
    | [], _, _, _, _, _, lowered, bound, _ => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨.nil bound, fun _ inside => by simp [namesList] at inside⟩
    | pattern :: patterns, _, _, _, _, _, lowered, bound, rowBound => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        simp only [RootRewritesOnTheStep.unknowns_appTerm, List.mem_append] at rowBound
        obtain ⟨headFlows, headNamed⟩ := matchRow_moded pattern headFound fun u inside => rowBound u (.inl inside)
        obtain ⟨tailFlows, tailNamed⟩ := matchRows_moded patterns tailFound
          (bound := bound ++ headGoals.flatMap goalUnknowns) fun u inside =>
            List.mem_append_left _ (rowBound u (.inr inside))
        refine ⟨headFlows.append tailFlows, fun name inside => ?_⟩
        simp only [namesList, List.mem_append] at inside
        rcases inside with inHead | inTail
        · have here := headNamed name inHead
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto
        · have here := tailNamed name inTail
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto

  theorem pickGoals_moded : ∀ (elements : List Pattern) {next next' : ℕ} {kind : CollType} {list : Tm}
      {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') → ∀ {bound : List ℕ},
      (∀ u ∈ unknowns list, u ∈ bound) → InputsBound bound goals ∧
        ∀ name ∈ namesList elements ++ rest.toList, labelCode name ∈ bound ++ goals.flatMap goalUnknowns
    | [], _, _, kind, list, rest, _, lowered, bound, listBound => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl⟩ := lowered
        refine ⟨.cons (fun x inside => listBound x (by simpa [goalInputs] using inside)) (.nil _),
          fun name inside => ?_⟩
        simp only [namesList, List.nil_append] at inside
        cases rest with
        | none => simp at inside
        | some restName =>
            simp only [Option.toList_some, List.mem_singleton] at inside
            subst inside
            simp [goalUnknowns, restRow]
    | element :: elements, next, _, kind, list, rest, _, lowered, bound, listBound => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, found, ⟨laterGoals, last⟩, laterFound, rfl, rfl⟩ := lowered
        dsimp only at laterFound ⊢
        obtain ⟨elementFlows, elementNamed⟩ := matchRow_moded element found
          (bound := bound ++ goalUnknowns (.ask pickRelation list (appTerm row (.var (listUnknown avoid middle)))))
          fun u inside => List.mem_append_right _ (by simp [goalUnknowns, inside])
        obtain ⟨laterFlows, laterNamed⟩ := pickGoals_moded elements laterFound
          (bound := bound ++ goalUnknowns (.ask pickRelation list (appTerm row (.var (listUnknown avoid middle)))) ++
            elementGoals.flatMap goalUnknowns)
          fun u inside => by
            simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inside
            subst inside
            simp [goalUnknowns]
        refine ⟨InputsBound.append (.cons (fun x inside => listBound x (by simpa [goalInputs] using inside))
          elementFlows) (by simpa [List.flatMap_cons, List.append_assoc] using laterFlows), fun name inside => ?_⟩
        simp only [namesList, List.append_assoc, List.mem_append] at inside
        rcases inside with inElement | inLater
        · have here := elementNamed name inElement
          simp only [List.flatMap_append, List.flatMap_cons, List.mem_append] at here ⊢
          tauto
        · have here := laterNamed name (List.mem_append.mpr inLater)
          simp only [List.flatMap_append, List.flatMap_cons, List.mem_append] at here ⊢
          tauto
end

mutual
  /-- **A matching lowering read back is bound in order from the pattern's names, and binds its row.** -/
  theorem matchRow_readBack : ∀ (p : Pattern) {next next' : ℕ} {t : Tm} {goals : List Goal},
      matchRow rests avoid next p = some (t, goals, next') → ∀ {bound : List ℕ},
      (∀ name ∈ names p, labelCode name ∈ bound) →
      InputsBound bound (invertGoals goals) ∧ ∀ u ∈ unknowns t, u ∈ bound ++ goals.flatMap goalUnknowns
    | .fvar name, _, _, _, _, lowered, bound, named => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        refine ⟨.nil bound, fun u inside => List.mem_append_left _ ?_⟩
        have isName : u = labelCode name := by split at inside <;> simpa using inside
        subst isName
        exact named name (by simp [names])
    | .bvar _, _, _, _, _, lowered, bound, _ => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨.nil bound, fun _ inside => by simp at inside⟩
    | .apply _ arguments, _, _, _, _, lowered, bound, named => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := matchRows_readBack arguments found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append]
          at inside
        rcases rowBound u inside with inClose | inBound
        · simp at inClose
        · exact inBound
    | .collection .vec elements none, _, _, _, _, lowered, bound, named => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := matchRows_readBack elements found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        rw [unknowns_vectorTerm] at inside
        rcases rowBound u inside with inClose | inBound
        · simp at inClose
        · exact inBound
    | .collection .vec elements (some restName), _, _, _, _, lowered, bound, named => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨flows, rowBound⟩ := matchRows_readBack elements found
            fun name inside => named name (by simp [names, inside])
          refine ⟨flows, fun u inside => ?_⟩
          rw [unknowns_vectorTerm] at inside
          rcases rowBound u inside with inClose | inBound
          · simp only [DemandTransformation.unknowns_unknown, List.mem_singleton] at inClose
            subst inClose
            exact List.mem_append_left _ (named restName (by simp [names]))
          · exact inBound
        · cases lowered
    | .collection .hashBag elements rest, _, _, _, _, lowered, bound, named => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨flows, listBound⟩ := pickGoals_readBack elements picked
            fun name inside => named name (by simpa [names] using inside)
          exact ⟨flows, fun u inside => List.mem_append_right _ (listBound u (by simpa using inside))⟩
        · cases lowered
    | .collection .hashSet elements rest, _, _, _, _, lowered, bound, named => by
        simp only [matchRow] at lowered
        split at lowered
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨flows, listBound⟩ := pickGoals_readBack elements picked
            fun name inside => named name (by simpa [names] using inside)
          exact ⟨flows, fun u inside => List.mem_append_right _ (listBound u (by simpa using inside))⟩
        · cases lowered
    | .lambda _ body, _, _, _, _, lowered, bound, named => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := matchRow_readBack body found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append]
          at inside
        exact rowBound u inside
    | .multiLambda _ _ body, _, _, _, _, lowered, bound, named => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨flows, rowBound⟩ := matchRow_readBack body found
          fun name inside => named name (by simpa [names] using inside)
        refine ⟨flows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm,
          RootRewritesOnTheStep.unknowns_numeralTerm, List.nil_append] at inside
        exact rowBound u inside
    | .subst body value, _, _, _, _, lowered, bound, named => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        obtain ⟨valueFlows, valueBound⟩ := matchRow_readBack value valueFound
          fun name inside => named name (by simp [names, inside])
        obtain ⟨bodyFlows, bodyBound⟩ := matchRow_readBack body bodyFound
          (bound := bound ++ (invertGoals valueGoals).flatMap goalUnknowns)
          fun name inside => List.mem_append_left _ (named name (by simp [names, inside]))
        refine ⟨by rw [invertGoals_append]; exact valueFlows.append bodyFlows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, RootRewritesOnTheStep.unknowns_symTerm, List.nil_append,
          List.mem_append] at inside
        rcases inside with inBody | inValue
        · have here := bodyBound u inBody
          simp only [List.flatMap_append, List.mem_append, mem_invertGoals_unknowns] at here ⊢
          tauto
        · have here := valueBound u inValue
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto

  theorem matchRows_readBack : ∀ (patterns : List Pattern) {next next' : ℕ} {close list : Tm} {goals : List Goal},
      matchRows rests avoid next patterns close = some (list, goals, next') → ∀ {bound : List ℕ},
      (∀ name ∈ namesList patterns, labelCode name ∈ bound) →
      InputsBound bound (invertGoals goals) ∧
        ∀ u ∈ unknowns list, u ∈ unknowns close ∨ u ∈ bound ++ goals.flatMap goalUnknowns
    | [], _, _, _, _, _, lowered, bound, _ => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact ⟨.nil bound, fun _ inside => .inl inside⟩
    | pattern :: patterns, _, _, _, _, _, lowered, bound, named => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tail, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        obtain ⟨tailFlows, tailBound⟩ := matchRows_readBack patterns tailFound
          fun name inside => named name (by simp [namesList, inside])
        obtain ⟨headFlows, headBound⟩ := matchRow_readBack pattern headFound
          (bound := bound ++ (invertGoals tailGoals).flatMap goalUnknowns)
          fun name inside => List.mem_append_left _ (named name (by simp [namesList, inside]))
        refine ⟨by rw [invertGoals_append]; exact tailFlows.append headFlows, fun u inside => ?_⟩
        simp only [RootRewritesOnTheStep.unknowns_appTerm, List.mem_append] at inside
        rcases inside with inHead | inTail
        · have here := headBound u inHead
          simp only [List.flatMap_append, List.mem_append, mem_invertGoals_unknowns] at here ⊢
          tauto
        · have here := tailBound u inTail
          simp only [List.flatMap_append, List.mem_append] at here ⊢
          tauto

  theorem pickGoals_readBack : ∀ (elements : List Pattern) {next next' : ℕ} {kind : CollType} {list : Tm}
      {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') → ∀ {bound : List ℕ},
      (∀ name ∈ namesList elements ++ rest.toList, labelCode name ∈ bound) →
      InputsBound bound (invertGoals goals) ∧ ∀ u ∈ unknowns list, u ∈ goals.flatMap goalUnknowns
    | [], _, _, kind, list, rest, _, lowered, bound, named => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl⟩ := lowered
        refine ⟨?_, fun u inside => by simp [goalUnknowns, inside]⟩
        simp only [invertGoals, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append]
        refine .cons (fun x inside => ?_) (.nil _)
        simp only [invertGoal, goalInputs] at inside
        cases rest with
        | none => simp [restRow] at inside
        | some restName =>
            simp only [restRow, DemandTransformation.unknowns_unknown, List.mem_singleton] at inside
            subst inside
            exact named restName (by simp)
    | element :: elements, next, _, kind, list, rest, _, lowered, bound, named => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, found, ⟨laterGoals, last⟩, laterFound, rfl, rfl⟩ := lowered
        dsimp only at laterFound ⊢
        obtain ⟨laterFlows, laterBound⟩ := pickGoals_readBack elements laterFound fun name inside => named name (by
          rcases List.mem_append.mp inside with inElements | inRest
          · simp [namesList, inElements]
          · simp [inRest])
        obtain ⟨elementFlows, rowBound⟩ := matchRow_readBack element found
          (bound := bound ++ (invertGoals laterGoals).flatMap goalUnknowns)
          fun name inside => List.mem_append_left _ (named name (by simp [namesList, inside]))
        refine ⟨?_, fun u inside => by simp [goalUnknowns, inside]⟩
        rw [invertGoals_append, invertGoals_cons]
        refine laterFlows.append (InputsBound.append elementFlows (.cons (fun x inside => ?_) (.nil _)))
        simp only [invertGoal, goalInputs, RootRewritesOnTheStep.unknowns_appTerm, DemandTransformation.unknowns_unknown,
          List.mem_append, List.mem_singleton] at inside
        rcases inside with inRow | isList
        · have here := rowBound x inRow
          simp only [List.mem_append, mem_invertGoals_unknowns] at here ⊢
          tauto
        · subst isList
          have here := laterBound (listUnknown avoid middle) (by simp)
          simp only [List.mem_append, mem_invertGoals_unknowns] at here ⊢
          tauto
end

/-! ## Matching rows of data read data -/

theorem mem_eraseIdx_or {α : Type} : ∀ (items : List α) (i : ℕ) (bound : i < items.length) {x : α}, x ∈ items →
    x = items[i] ∨ x ∈ items.eraseIdx i
  | [], _, bound, _, _ => absurd bound (by simp)
  | y :: ys, 0, _, x, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact .inl rfl
      · exact .inr (by simpa using later)
  | y :: ys, j + 1, bound, x, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact .inr (by simp)
      · rcases mem_eraseIdx_or ys j (by simpa using bound) later with same | inRest
        · exact .inl (by simpa using same)
        · exact .inr (by simp [inRest])

section Data

variable {R : Relations} {program : List Clause}

mutual
  /-- **A matching lowering whose goals hold reads data, at names of data.** -/
  theorem matchRow_data (collections : CollectionClauses program) : ∀ (p : Pattern) {next next' : ℕ} {t : Tm}
      {goals : List Goal}, matchRow rests avoid next p = some (t, goals, next') → ∀ {θ : ℕ → Expr} {s : Pattern}
      {witness : Bindings}, inst θ t = encode s → (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ name ∈ names p, Holds rests θ witness name) →
      (∀ name ∈ names p, OrderedMatching.isData (lookupOrFvar witness name) = true) →
      OrderedMatching.isData s = true
    | .fvar name, _, _, _, _, lowered, θ, s, witness, met, _, holds, data => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        have held := holds name (by simp [names])
        have valueData := data name (by simp [names])
        unfold Holds at held
        split at held
        · rename_i inRests
          obtain ⟨tail, value, listed⟩ := held
          rw [if_pos inRests, OrderedRows.inst_vectorTerm (list := .var (labelCode name)) (items := tail) listed] at met
          rw [← RootRewritesOnTheStep.encode_injective met, ← value]
          exact valueData
        · rename_i outside
          rw [if_neg outside, DemandTransformation.inst_unknown, held] at met
          rw [← RootRewritesOnTheStep.encode_injective met]
          exact valueData
    | .bvar index, _, _, _, _, lowered, θ, s, _, met, _, _, _ => by
        simp only [matchRow, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        rw [← RootRewritesOnTheStep.encode_injective (show encode (.bvar index) = encode s by simpa [encode] using met)]
        rfl
    | .apply label arguments, _, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, argumentGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨items, rfl, listed⟩ := apply_of_row met
        have itemsData := matchRows_data collections arguments found listed goals
          (fun name inside => holds name (by simpa [names] using inside))
          (fun name inside => data name (by simpa [names] using inside))
          fun tail closed => by rw [encodeList_nil_inv (xs := tail) (Eq.symm (by simpa using closed.symm))]; rfl
        simpa [OrderedMatching.isData] using itemsData
    | .collection .vec elements none, _, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        obtain ⟨items, rfl, listed⟩ := collection_of_row (kind := .vec) met
        have itemsData := matchRows_data collections elements found listed goals
          (fun name inside => holds name (by simpa [names] using inside))
          (fun name inside => data name (by simpa [names] using inside))
          fun tail closed => by rw [encodeList_nil_inv (xs := tail) (Eq.symm (by simpa using closed.symm))]; rfl
        simpa [OrderedMatching.isData] using itemsData
    | .collection .vec elements (some restName), _, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i inRests
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨list, elementGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, rfl, listed⟩ := collection_of_row (kind := .vec) met
          have restHolds := holds restName (by simp [names])
          have restData := data restName (by simp [names])
          simp only [Holds, if_pos inRests] at restHolds
          obtain ⟨tail', restValue, restListed⟩ := restHolds
          rw [restValue] at restData
          have itemsData := matchRows_data collections elements found listed goals
            (fun name inside => holds name (by simp [names, inside]))
            (fun name inside => data name (by simp [names, inside]))
            fun tail closed => by
              rw [DemandTransformation.inst_unknown, restListed] at closed
              rw [← RootRewritesOnTheStep.encodeList_inj _ _ closed]
              simpa [OrderedMatching.isData] using restData
          simpa [OrderedMatching.isData] using itemsData
        · cases lowered
    | .collection .hashBag elements rest, next, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, rfl, listed⟩ := collection_of_row met
          have itemsData := pickGoals_data collections elements picked outside listed goals
            (fun name inside => holds name (by simpa [names] using inside))
            (fun name inside => data name (by simpa [names] using inside))
          simpa [OrderedMatching.isData] using itemsData
        · cases lowered
    | .collection .hashSet elements rest, next, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow] at lowered
        split at lowered
        · rename_i outside
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at lowered
          obtain ⟨⟨picks, last⟩, picked, rfl, rfl, rfl⟩ := lowered
          obtain ⟨items, rfl, listed⟩ := collection_of_row met
          have itemsData := pickGoals_data collections elements picked outside listed goals
            (fun name inside => holds name (by simpa [names] using inside))
            (fun name inside => data name (by simpa [names] using inside))
          simpa [OrderedMatching.isData] using itemsData
        · cases lowered
    | .lambda _ body, _, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at met
        obtain ⟨binder, body', rfl, binderIs, bodyMet⟩ := PatternRows.encode_lambda_inv met
        have noName : binder = none := by
          cases binder with
          | none => rfl
          | some _ => simp [RootRewritesOnTheStep.optionRow] at binderIs
        subst noName
        simpa [OrderedMatching.isData] using matchRow_data collections body found bodyMet goals
          (fun name inside => holds name (by simpa [names] using inside))
          (fun name inside => data name (by simpa [names] using inside))
    | .multiLambda _ _ body, _, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, last⟩, found, rfl, rfl, rfl⟩ := lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          RootRewritesOnTheStep.inst_numeralTerm] at met
        obtain ⟨arity', binders', body', rfl, -, bindersIs, bodyMet⟩ := PatternRows.encode_multiLambda_inv met
        have noNames : binders' = [] := by
          cases binders' with
          | nil => rfl
          | cons _ _ => simp [RootRewritesOnTheStep.namesRow] at bindersIs
        subst noNames
        simpa [OrderedMatching.isData] using matchRow_data collections body found bodyMet goals
          (fun name inside => holds name (by simpa [names] using inside))
          (fun name inside => data name (by simpa [names] using inside))
    | .subst body value, _, _, _, _, lowered, θ, s, witness, met, goals, holds, data => by
        simp only [matchRow, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨bodyRow, bodyGoals, middle⟩, bodyFound, ⟨valueRow, valueGoals, last⟩, valueFound, rfl, rfl, rfl⟩ :=
          lowered
        simp only [RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm] at met
        obtain ⟨body', value', rfl, bodyMet, valueMet⟩ := PatternRows.encode_subst_inv met
        have bodyData := matchRow_data collections body bodyFound bodyMet
          (fun g inside => goals g (List.mem_append_left _ inside))
          (fun name inside => holds name (by simp [names, inside]))
          (fun name inside => data name (by simp [names, inside]))
        have valueData := matchRow_data collections value valueFound valueMet
          (fun g inside => goals g (List.mem_append_right _ inside))
          (fun name inside => holds name (by simp [names, inside]))
          (fun name inside => data name (by simp [names, inside]))
        simp [OrderedMatching.isData, bodyData, valueData]

  theorem matchRows_data (collections : CollectionClauses program) : ∀ (patterns : List Pattern) {next next' : ℕ}
      {close list : Tm} {goals : List Goal}, matchRows rests avoid next patterns close = some (list, goals, next') →
      ∀ {θ : ℕ → Expr} {items : List Pattern} {witness : Bindings}, inst θ list = encodeList items →
      (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ name ∈ namesList patterns, Holds rests θ witness name) →
      (∀ name ∈ namesList patterns, OrderedMatching.isData (lookupOrFvar witness name) = true) →
      (∀ tail : List Pattern, inst θ close = encodeList tail → OrderedMatching.isDataList tail = true) →
      OrderedMatching.isDataList items = true
    | [], _, _, _, _, _, lowered, θ, items, _, listed, _, _, _, closeData => by
        simp only [matchRows, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl, rfl⟩ := lowered
        exact closeData items listed
    | pattern :: patterns, _, _, _, _, _, lowered, θ, items, witness, listed, goals, holds, data, closeData => by
        simp only [matchRows, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨head, headGoals, middle⟩, headFound, ⟨tailRow, tailGoals, last⟩, tailFound, rfl, rfl, rfl⟩ := lowered
        rw [RootRewritesOnTheStep.inst_appTerm] at listed
        obtain ⟨x, rest, rfl, headIs, tailIs⟩ := encodeList_cons_inv listed
        have headData := matchRow_data collections pattern headFound headIs
          (fun g inside => goals g (List.mem_append_left _ inside))
          (fun name inside => holds name (by simp [namesList, inside]))
          (fun name inside => data name (by simp [namesList, inside]))
        have tailData := matchRows_data collections patterns tailFound tailIs
          (fun g inside => goals g (List.mem_append_right _ inside))
          (fun name inside => holds name (by simp [namesList, inside]))
          (fun name inside => data name (by simp [namesList, inside])) closeData
        simp [OrderedMatching.isDataList, headData, tailData]

  theorem pickGoals_data (collections : CollectionClauses program) : ∀ (elements : List Pattern) {next next' : ℕ}
      {kind : CollType} {list : Tm} {rest : Option String} {goals : List Goal},
      pickGoals rests avoid next kind list elements rest = some (goals, next') →
      rest.all (fun name => !rests.contains name) = true → ∀ {θ : ℕ → Expr} {items : List Pattern}
      {witness : Bindings}, inst θ list = encodeList items → (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      (∀ name ∈ namesList elements ++ rest.toList, Holds rests θ witness name) →
      (∀ name ∈ namesList elements ++ rest.toList, OrderedMatching.isData (lookupOrFvar witness name) = true) →
      OrderedMatching.isDataList items = true
    | [], _, _, kind, list, rest, _, lowered, outside, θ, items, witness, listed, goals, holds, data => by
        simp only [pickGoals, Option.some.injEq, Prod.mk.injEq] at lowered
        obtain ⟨rfl, rfl⟩ := lowered
        have wrapped := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, listed]
          at wrapped
        have restIs := wrap_sound collections.onlyWraps wrapped
        cases rest with
        | none =>
            have emptyIs : inst θ (collectionTerm kind (symTerm 0)) = encode (.collection kind [] none) := by
              rw [encode_collection]
              rfl
            simp only [restRow] at restIs
            rw [emptyIs] at restIs
            have same := RootRewritesOnTheStep.encode_injective restIs
            simp only [Pattern.collection.injEq] at same
            rw [← same.2.1]
            rfl
        | some restName =>
            have notRest : restName ∉ rests := by simpa using outside
            have held := holds restName (by simp)
            have restData := data restName (by simp)
            simp only [Holds, if_neg notRest] at held
            simp only [restRow, DemandTransformation.inst_unknown, held] at restIs
            rw [RootRewritesOnTheStep.encode_injective restIs] at restData
            simpa [OrderedMatching.isData] using restData
    | element :: elements, next, _, kind, list, rest, _, lowered, outside, θ, items, witness, listed, goals, holds,
        data => by
        simp only [pickGoals, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at lowered
        obtain ⟨⟨row, elementGoals, middle⟩, found, ⟨laterGoals, last⟩, laterFound, rfl, rfl⟩ := lowered
        dsimp only at laterFound goals
        have picked := goals _ (List.mem_append_left _ List.mem_cons_self)
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, listed] at picked
        obtain ⟨depth, pickedAt⟩ := picked
        obtain ⟨i, bound, pickIs⟩ := pick_sound collections.onlyPicks depth pickedAt
        simp only [Expr.app.injEq] at pickIs
        obtain ⟨rowIs, laterIs⟩ := pickIs
        have elementData := matchRow_data collections element found rowIs
          (fun g inside => goals g (List.mem_append_left _ (List.mem_cons_of_mem _ inside)))
          (fun name inside => holds name (by simp [namesList, inside]))
          (fun name inside => data name (by simp [namesList, inside]))
        have laterData := pickGoals_data collections elements laterFound outside
          (by rw [DemandTransformation.inst_unknown]; exact laterIs)
          (fun g inside => goals g (List.mem_append_right _ inside))
          (fun name inside => holds name (by
            rcases List.mem_append.mp inside with inElements | inRest
            · simp [namesList, inElements]
            · simp [inRest]))
          (fun name inside => data name (by
            rcases List.mem_append.mp inside with inElements | inRest
            · simp [namesList, inElements]
            · simp [inRest]))
        refine OrderedMatching.isDataList_iff.mpr fun x inside => ?_
        rcases mem_eraseIdx_or items i bound inside with rfl | inRest
        · exact elementData
        · exact OrderedMatching.isDataList_iff.mp laterData x inRest
end

end Data

end Mettapedia.GSLT.Compilation.Uniform.CollectionMatching

#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionMatching.pick_sound
#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionMatching.pick_complete
#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionMatching.wrap_sound
#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionMatching.wrap_complete
#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionMatching.matchRow_sound
#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionMatching.matchRow_complete
#print axioms Mettapedia.GSLT.Compilation.Uniform.CollectionMatching.matchRow_scope
