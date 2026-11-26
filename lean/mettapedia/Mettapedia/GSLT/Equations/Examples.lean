import Mettapedia.GSLT.Equations
import Mettapedia.InformationTheory.RelationStoreRentOrBuy

/-! # Examples for choosing an equation-aware layout

Each example uses the same operations as the proofs, not a second model of
the examples. The numeric examples count postings, tuples, or encoded bits;
they are not measurements in a particular runtime.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.Examples

namespace AtomicRead

open Atomic
open Contracts.ScopedAliasSections (GTerm)

inductive Symbol where
  | cold | warm | humid | pair | other
  deriving DecidableEq

private def key : Symbol → Nat
  | .cold | .warm => 0
  | .humid => 1
  | .pair => 2
  | .other => 3

private def pattern : Atomic.Pattern Symbol Nat :=
  .app (.app (.sym (.inl .pair)) (.sym (.inr 0))) (.sym (.inr 0))

private def row (a b : Symbol) : GTerm Symbol :=
  .app (.app (.sym .pair) (.sym a)) (.sym b)

private def readBack (a b : Symbol) : Option (GTerm Symbol) :=
  (matchFrom key pattern (row a b) (fun _ => none)).bind (fun env => env 0)

/-- Cold and Warm match the same variable, but the first actual spelling
of that binding stays Cold. Reverse their order and the returned raw value
is Warm. The quotient result itself did not change. -/
theorem weather_alias_preserves_raw :
    readBack .cold .warm = some (.sym .cold) ∧ readBack .warm .cold = some (.sym .warm) :=
  ⟨rfl, rfl⟩

theorem structural_mismatch_is_not_an_alias :
    readBack .cold .humid = none :=
  rfl

theorem plain_matching_does_not_assume_theory :
    (matchFrom id pattern (row .cold .warm) (fun _ => none)).isNone = true :=
  rfl

private def seen (rs : List (GTerm Symbol)) : Nat :=
  (rs.filter fun r => (matchFrom key pattern r (fun _ => none)).isSome).length

/-- An occurrence count is not a count of classes or distinct payloads. -/
theorem equal_rows_still_have_two_occurrences :
    seen [row .cold .warm, row .cold .humid, row .cold .warm] = 2 := rfl

/-- The index selector cannot use the raw repeated-variable equality.
It admits the shape; only the final matcher checks quotient equality. -/
theorem candidate_wildcards_do_not_split_an_alias :
    CandidateSelection.shapeFits id pattern (row .cold .warm) = true ∧
      (matchFrom id pattern (row .cold .warm) (fun _ => none)).isNone = true ∧
      (matchFrom key pattern (row .cold .warm) (fun _ => none)).isSome = true :=
  ⟨rfl, rfl, rfl⟩

private def nestedLiterals : Nat → Atomic.Pattern Bool Unit
  | 0 => .sym (.inr ())
  | n + 1 => .app (.sym (.inl false)) (nestedLiterals n)

/-- Even a two-member alias class can give exponentially many literal
expansions. A bound on class fanout alone cannot guard this route. -/
theorem two_spellings_per_coordinate (n : Nat) :
    (CandidateSelection.expansions (fun _ : Unit => [false, true]) (fun _ => ())
      (nestedLiterals n)).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nestedLiterals, CandidateSelection.expansion_product, ih, pow_succ]
    exact Nat.mul_comm _ _

end AtomicRead

namespace Schema

open UniversalAlgebra RecipeMatching

inductive Head where
  | schema | range | alias | float | zero | one | other
  deriving DecidableEq

def sig : Signature where
  Operation := Head
  arity
    | .schema => 1
    | .range => 3
    | _ => 0

abbrev Id := Fin 7

/-- Root class 0 contains (Schema AI:UnitRange); class 1 contains both the
alias and (Range Float 0 1). Class 5 is another row with the same outer
head and an unrelated child. -/
def index : Catalogue sig Id where
  rows
    | .schema => [(0, fun _ => 1), (5, fun _ => 6)]
    | .range => [(1, fun i => if i.val = 0 then 2 else if i.val = 1 then 3 else 4)]
    | .alias => [(1, Fin.elim0)]
    | .float => [(2, Fin.elim0)]
    | .zero => [(3, Fin.elim0)]
    | .one => [(4, Fin.elim0)]
    | .other => [(6, Fin.elim0)]

def pattern : Term sig := .op .schema (fun _ => .op .range (fun i => .var i.val))

private def supplied (i : Nat) : Id := if i = 0 then 2 else if i = 1 then 3 else 4

theorem inner_recipe_finds_the_aliased_row :
    index.roots supplied pattern = {0} := by decide +kernel

theorem inner_recipe_plan_has_two_atoms :
    (RelationalPlan.compile pattern).map RelationalPlan.Atom.operation = [.schema, .range] ∧
      RelationalPlan.query index supplied pattern 0 := by
  refine ⟨rfl, (RelationalPlan.query_iff index supplied pattern 0).mpr ?_⟩
  exact (index.mem_roots_iff supplied pattern 0).mp (by decide +kernel)

/-- A conservative collided bit cannot confirm a recipe. One bit may cover
several heads, while class 6 still has no Range construction. -/
theorem a_head_bit_may_be_a_false_positive :
    index.HeadSummary (fun _ => ()) (fun _ => {()}) ∧
      ¬ index.Matches supplied (.op .range (fun i => .var i.val)) 6 := by
  refine ⟨fun _ _ _ _ => by simp, ?_⟩
  intro fake
  have missing : (6 : Id) ∉ index.roots supplied (.op .range (fun i => .var i.val)) := by
    decide +kernel
  exact missing ((index.mem_roots_iff _ _ _).mpr fake)

private def withoutRange : Catalogue sig Id where
  rows
    | .range => []
    | f => index.rows f

/-- An identical list of outer heads does not establish an atomic fast
path. A missed child recipe changes an observable match. -/
theorem head_only_fast_path_loses_the_row :
    withoutRange.rows .schema = index.rows .schema ∧
    withoutRange.roots supplied pattern = ∅ := by
  refine ⟨rfl, ?_⟩
  decide +kernel

def groundArgument (v : Nat) : Term sig :=
  if v = 0 then .op .float Fin.elim0
  else if v = 1 then .op .zero Fin.elim0 else .op .one Fin.elim0

def aliasTerm : Term sig := .op .alias Fin.elim0
def compound : Term sig := .op .range (fun i => groundArgument i.val)
def theory : EquationSystem sig := ⟨[(aliasTerm, compound)]⟩

/-- Same positive instance checked by the authored equation's independent
consequence relation, without consulting the recipe table. -/
theorem source_equation_allows_the_open_instance :
    EquationalConsequence theory (pattern.subst groundArgument, .op .schema (fun _ => aliasTerm)) := by
  change EquationalConsequence theory
    (.op .schema (fun _ => compound), .op .schema (fun _ => aliasTerm))
  apply EquationalConsequence.operation
  intro _
  exact EquationalConsequence.symm (EquationalConsequence.of_mem (by
    change (aliasTerm, compound) ∈ [(aliasTerm, compound)]
    simp))

/-- Sparse inner demand needs one posting request regardless of how many
outer rows were considered plausible by head alone. This holds on an actual
ordered occurrence query, with the reverse posting as the input. -/
theorem sparse_inner_seek (noise : Nat) :
    SelectiveCursor.requests ([1] : List Id) = 1 ∧
      SelectiveCursor.read (fun _ : Id => [noise]) [1] =
        (List.range (noise + 1)).filter
          (fun r => decide ((if r = noise then 1 else 6 : Id) ∈
            index.roots supplied (.op .range (fun i => .var i.val)))) := by
  refine ⟨rfl, ?_⟩
  have yes : (1 : Id) ∈ index.roots supplied (.op .range (fun i => .var i.val)) := by
    decide +kernel
  have no : (6 : Id) ∉ index.roots supplied (.op .range (fun i => .var i.val)) := by
    decide +kernel
  simp only [SelectiveCursor.read, List.map_cons, List.map_nil, OccurrenceRuns.merge,
    List.foldr_cons, List.foldr_nil, List.merge_right]
  rw [List.range_succ, List.filter_append]
  have empt : (List.range noise).filter
      (fun r => decide ((if r = noise then 1 else 6 : Id) ∈
        index.roots supplied (.op .range (fun i => .var i.val)))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro r present
    have diff : r ≠ noise := Nat.ne_of_lt (List.mem_range.mp present)
    simp [diff, no]
  simp [empt, yes]

end Schema

namespace CyclicRecipes

open UniversalAlgebra RecipeMatching

private def sig : Signature where
  Operation := Bool
  arity h := if h then 1 else 0

private def a : Term sig := .op false Fin.elim0
private def f (t : Term sig) : Term sig := .op true (fun _ => t)
private def iter : Nat → Term sig
  | 0 => a
  | n + 1 => f (iter n)

private def graph : Catalogue sig (Fin 1) where
  rows _ := [(0, fun _ => 0)]

private def equations : EquationSystem sig := ⟨[(f a, a)]⟩

/-- The cycle is finite storage for arbitrarily deep requested patterns.
Recursion is on the request; it never enumerates the members of the class. -/
theorem cyclic_matches_every_depth (n : Nat) :
    graph.Matches (fun _ => 0) (iter n) 0 := by
  induction n with
  | zero =>
    refine ⟨(fun _ => 0), by simp [graph], ?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih => exact ⟨(fun _ => 0), by simp [graph], fun _ => ih⟩

theorem every_depth_is_an_authored_consequence (n : Nat) :
    EquationalConsequence equations (iter n, a) := by
  induction n with
  | zero => exact EquationalConsequence.refl _ _
  | succ n ih =>
    change EquationalConsequence equations (f (iter n), a)
    have first : EquationalConsequence equations (f (iter n), f a) :=
      EquationalConsequence.operation (S := sig) true _ _ (fun _ => ih)
    exact first.trans (EquationalConsequence.of_mem (by
      change (f a, a) ∈ [(f a, a)]
      simp))

end CyclicRecipes

namespace Reconciliation

open UniversalAlgebra RecipeMatching ClassChange

private def sig : Signature where
  Operation := Unit
  arity _ := 1

private def graph : Catalogue sig (Fin 4) where
  rows _ := [(2, fun _ => 0), (3, fun _ => 1)]

private def collapseInputs (old : Fin 4) : Fin 4 :=
  if old = 1 then 0 else old

/-- Before the merge, f(0) and f(1) may have different parents. After
0=1, merely relabelling the children doesn't finish congruence closure. -/
theorem merging_children_requires_reconciling_parents :
    graph.Functional ∧ ¬ (relabel collapseInputs graph).Functional := by
  constructor
  · intro op args a b first second
    change (a, args) ∈ [(2, fun _ => (0 : Fin 4)), (3, fun _ => (1 : Fin 4))] at first
    change (b, args) ∈ [(2, fun _ => (0 : Fin 4)), (3, fun _ => (1 : Fin 4))] at second
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at first second
    rcases first with ⟨rfl, x⟩ | ⟨rfl, x⟩ <;> rcases second with ⟨rfl, y⟩ | ⟨rfl, y⟩
    · rfl
    · exact False.elim ((by decide : (0 : Fin 4) ≠ 1) (congrFun (x.symm.trans y) (0 : Fin 1)))
    · exact False.elim ((by decide : (1 : Fin 4) ≠ 0) (congrFun (x.symm.trans y) (0 : Fin 1)))
    · rfl
  · intro good
    have same := (functional_after_iff collapseInputs graph).mp good () 2 3
      (fun _ => 0) (fun _ => 1) (by simp [graph]) (by simp [graph]) (fun _ => rfl)
    exact (by decide : (2 : Fin 4) ≠ 3) same

end Reconciliation

namespace Presentation

open Preference

/-- The last 0 is an actual third member, not a preference flag. -/
theorem numeric_aliases_are_values :
    Relation.EqvGen (Edge (consecutive ([-1, 1, 0] : List Int))) (-1) 0 := by
  apply (consecutive_eq_clique _ _ _).mpr
  exact Relation.EqvGen.rel _ _ (by decide)

private def separate : Bool → Bool → Prop := Eq
private def terminal : Unit → Unit → Prop := Eq

private theorem no_bool_cross {x y : Bool} (p : Reach separate x y) : x = y := by
  induction p with
  | refl => rfl
  | tail _ step arrived => exact arrived.trans step

/-- Two eligible spellings can share an equality class without preferring
each other. One bridge removes only the spelling in its source SCC. -/
theorem preference_bridge_keeps_the_other_sink :
    let edge := bridge separate terminal false ()
    ¬ Eligible edge (.inl false) ∧ Eligible edge (.inl true) ∧ Eligible edge (.inr ()) := by
  dsimp only
  rw [eligible_left, eligible_left, eligible_right]
  refine ⟨fun h => h.2 .refl, ⟨?_, fun h => Bool.noConfusion (no_bool_cross h)⟩, ?_⟩
  · intro y p
    cases no_bool_cross p
    exact .refl
  · intro y _
    cases y
    exact .refl

end Presentation

namespace Demand

open FactorizedRead UniversalAlgebra RecipeMatching

/-- The independent substitution domain has two alternatives per position.
Its factorized count is the product of the local counts. Any explicitly
emitted ordered enumeration has exponentially many elements. -/
theorem binary_dimensions (n : Nat) :
    (products (List.replicate n ([[false], [true]] : List (List Bool)))).length = 2^n := by
  rw [length_products]
  simp

private def sig : Signature where
  Operation := Unit
  arity _ := 2

private def pair (x y : Fin 3) : Fin 2 → Fin 3 := fun i => if i.val = 0 then x else y

private def diagonalTrap : Catalogue sig (Fin 3) where
  rows _ := [(2, pair 0 1), (2, pair 1 0)]

private def query (v : Nat) : Term sig := .op () (fun i => .var (if i.val = 0 then 0 else v))

/-- Two unequal choices satisfy the linear pattern. Dropping the repeated
variable equality wrongly counts two derivations of the diagonal pattern,
for which no assignment actually exists. -/
theorem repeated_variable_is_a_join_not_a_product :
    (messages diagonalTrap (fun _ => (1 : Nat)) (query 0))[2] = 2 ∧
      (∃ ρ, diagonalTrap.Matches ρ (query 1) 2) ∧
      ¬ ∃ ρ, diagonalTrap.Matches ρ (query 0) 2 := by
  refine ⟨rfl, ⟨(fun i => if i = 0 then 0 else 1), ?_⟩, ?_⟩
  · refine ⟨pair 0 1, by simp [diagonalTrap], ?_⟩
    intro i
    change (if (if i.val = 0 then 0 else 1) = 0 then (0 : Fin 3) else 1) = pair 0 1 i
    by_cases e : i.val = 0 <;> simp [pair, e]
  · rintro ⟨ρ, args, member, ok⟩
    change (2, args) ∈ [(2, pair 0 1), (2, pair 1 0)] at member
    have selected : args = pair 0 1 ∨ args = pair 1 0 := by
      rcases List.mem_cons.mp member with first | rest
      · exact Or.inl (congrArg Prod.snd first)
      · rcases List.mem_cons.mp rest with last | impossible
        · exact Or.inr (congrArg Prod.snd last)
        · exact (List.not_mem_nil impossible).elim
    have fst : ρ 0 = args (0 : Fin 2) := ok (0 : Fin 2)
    have snd : ρ 0 = args (1 : Fin 2) := ok (1 : Fin 2)
    have same := fst.symm.trans snd
    rcases selected with rfl | rfl
    · exact (by decide : (0 : Fin 3) ≠ 1) same
    · exact (by decide : (1 : Fin 3) ≠ 0) same

end Demand

namespace Layout

open SelectiveCursor PostingInformation OccurrenceRuns
open scoped BigOperators

private def alternating (n : Nat) (second : Bool) : List Nat :=
  List.range' (if second then 1 else 0) n 2

/-- Exactly two key requests for two raw labels, even if there are many
equal-payload occurrences. Count and ordered emission do not cost the
same: the former can read two lengths, the latter still emits 2n positions. -/
theorem two_labels_many_rows (n : Nat) :
    requests [false, true] = 2 ∧ count (fun _ => n) [false, true] = 2 * n ∧
      (read (alternating n) [false, true]).length = 2 * n := by
  have countEq : count (fun _ => n) [false, true] = 2 * n := by simp [count, two_mul]
  refine ⟨rfl, countEq, ?_⟩
  rw [← count_eq_read (alternating n) (fun _ => n) [false, true] (by simp [alternating])]
  exact countEq

theorem ordered_output_does_not_group_by_alias :
    read (alternating 3) [true, false] = [0, 1, 2, 3, 4, 5] ∧
    first (fun k => (alternating 3 k).head?) [true, false] = some 0 := by
  simp [SelectiveCursor.read, merge, first, alternating, List.range'_succ]

/-- Two independent matches assigned position zero by their own cursors
lose a result if those offsets pass through an occurrence union. They
remain different with shared occurrence IDs, even with equal payloads. -/
theorem cursor_local_offsets_are_not_global_addresses :
    ((merge ([[0], [0]] : List (List Nat))).dedup).length = 1 ∧
      ((merge ([[1], [0], [1]] : List (List Nat))).dedup) = [0, 1] := by
  simp [merge]

/-- The one-distinct-label-per-row case is not the two-label case.
Gathering on demand requests one posting per label and has that many
outputs; re-filing can remove a repeated lookup overhead, not the output. -/
theorem distinct_label_churn (n : Nat) :
    requests (List.range (2*n)) = 2*n ∧
    (read (fun i => [i]) (List.range (2*n))).length = 2*n := by
  refine ⟨by simp [requests], ?_⟩
  rw [← count_eq_read (fun i => [i]) (fun _ => 1) (List.range (2*n)) (by simp)]
  simp [count]

private def extraWork (materialize : Bool) (perRead setup reads : Nat) : Nat :=
  if materialize then setup else reads * perRead

/-- Same fanout and setup cost; changing how long the class lasts changes
which plan is cheaper. The costs here exclude the unavoidable output,
which is common to the two routes in the fixed-snapshot model. -/
theorem constant_fanout_cannot_choose_in_both_epochs :
    extraWork false 2 24 1 < extraWork true 2 24 1 ∧
      extraWork true 2 24 20 < extraWork false 2 24 20 := by decide

open InformationTheory.RelationStoreFloors in
theorem adaptive_materialization_prices_the_reads (overhead : Nat → Nat)
    (setup reads largest : Nat) (perRead : ∀ i < reads, overhead i ≤ largest) :
    rentOrBuyVar overhead setup reads ≤ 2 * min (paid overhead reads) setup + largest :=
  rentOrBuyVar_le_two_mul_opt_add overhead setup reads largest perRead

/-- An arbitrary mix of two spellings for n known class occurrences needs
n fixed-width bits, even with the complete quotient tape for free. -/
theorem binary_spellings_need_one_bit_each (n bits : Nat) :
    Nonempty ((Fin n → Bool) ↪ Fin (2^bits)) ↔ n ≤ bits := by
  constructor
  · rintro ⟨enc⟩
    have fits : (2 : Nat) ^ n ≤ 2 ^ bits := by simpa using Fintype.card_le_of_embedding enc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : Nat))).mp fits
  · intro fits
    have card : Fintype.card (Fin n → Bool) ≤ 2 ^ bits := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      exact Nat.pow_le_pow_right (by decide) fits
    exact ⟨(Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb card)⟩

/-- Three positions whose dictionaries each have three spellings need five
bits together, not two bits per position. The remainders give back the
original choice, rather than a class representative. -/
theorem three_ternary_spellings_use_five_bits :
    MixedRadix.width [3, 3, 3] = 5 ∧
      MixedRadix.decode [3, 3, 3] (MixedRadix.encode [3, 3, 3] (2, 1, 2, ())) =
        some (2, 1, 2, ()) := by
  refine ⟨by decide +kernel, MixedRadix.decode_encode _ _⟩

open InformationTheory.RelationStoreFloors in
/-- A sparse four-position posting in a 1024-row range fits in 41 bits
before rank/select metadata. A full bitmap uses 1024 bits. -/
theorem sparse_layout_bit_budget :
    efBits 8 (efEncode 8 5 ({3, 127, 513, 1019} : Finset Nat)) = 41 ∧ 41 < 1024 := by
  have inRange : ∀ x ∈ ({3, 127, 513, 1019} : Finset Nat), x < 5 * 2 ^ 8 := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  exact ⟨(efBits_efEncode 8 inRange).trans (by decide), by decide⟩

open InformationTheory.RelationStoreFloors in
/-- The dense bitmap wins this half-full block against that Elias–Fano
layout. Format selection needs more than one sparse-data recommendation. -/
theorem dense_layout_bit_budget :
    efBits 1 (efEncode 1 513 (Finset.range 512)) = 1537 ∧ 1024 < 1537 := by
  refine ⟨?_, by decide⟩
  have inRange : ∀ x ∈ Finset.range 512, x < 513 * 2 ^ 1 := by
    intro x mem
    have smaller := Finset.mem_range.mp mem
    omega
  rw [efBits_efEncode 1 inRange, Finset.card_range]

end Layout

end Mettapedia.GSLT.Equations.Examples
