import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Finset.Lattice.Fold

/-!
# A call with several fitting declarations

In HE an operation may have several declared function types. When more than one of them fits a
call, HE's interpreter (its specification and its implementation, since July 2024) uses the first
one in the order its type query lists them. Before July 2024 it ran the call once for each
declaration, which repeated answers. Elsewhere the interpreter keeps every alternative.

This module states the possible rules side by side over an abstract call.

* A fitting declaration (`Fitting`) has a *way* of running the call (which arguments are
  evaluated before the call, and whether the result is evaluated) and a check on results
  (`accepts`). `run w` is the bag of results of running the call that way.
* `firstFit`: the first fitting declaration decides (HE since July 2024).
* `perDeclaration`: one run for each declaration (HE before July 2024).
* `alternatives`: one run for each distinct way; a result is kept when some declaration of its way
  accepts it; the runs are combined as a union of bags, which adds no copies.
* `promises`: the same runs; a result is kept only when every declaration of its way accepts it.

Laws:

* `alternatives_congr`, `promises_congr`, `alternatives_perm`: the answers depend only on which
  declarations fit, not on their order or on repeated declarations.
* `alternatives_le_runs`: declarations never add an answer, or a copy of one, beyond what the runs
  give.
* `alternatives_eq_firstFit_of_agree`, `promises_eq_firstFit_of_agree`,
  `firstFit_eq_alternatives_of_agree`: when the fitting declarations run the call the same way and
  accept the same results, every rule answers as the first declaration does, in every order.
* `alternatives_mono`: adding a fitting declaration never removes an answer under `alternatives`.
  `promises_antitone`: adding one of a way already present never adds an answer under `promises`.

Controls (`Controls`), each the bag of one small HE program, as measured: `firstFit` changes with
declaration order for `pick`, `q2`, `f` and the program with `(:< Nat Number)`; `alternatives` and
`promises` do not; `perDeclaration` repeats an answer that `alternatives` gives once (`g`, `e`);
under `promises` a narrower declaration narrows the answers, under `alternatives` it does not
(`numberAndNat_refinement`).

Scope: the evaluator is a parameter, and `run w` is one run for each way. That this equals running
the call under each declaration separately, for HE's evaluator, needs its answers at a more general
expected type to include those at a more specific one; that is not proved here. The rule is not yet
stated on the HE specification of this tree, whose `Spec.Eval.FunctionCandidateScanRel` transcribes
`firstFit`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.SeveralDeclarations

section General

variable {Way Ans : Type} [DecidableEq Way]

/-- A declaration that fits a call: the way it has the call run, and the results it accepts. -/
structure Fitting (Way Ans : Type) where
  way : Way
  accepts : Ans → Bool

/-- The ways of running among the fitting declarations. -/
def ways (ds : List (Fitting Way Ans)) : Finset Way := (ds.map Fitting.way).toFinset

/-- Some fitting declaration of way `w` accepts `a`. -/
def someAccepts (ds : List (Fitting Way Ans)) (w : Way) (a : Ans) : Bool :=
  ds.any fun d => decide (d.way = w) && d.accepts a

/-- Every fitting declaration of way `w` accepts `a`. -/
def allAccept (ds : List (Fitting Way Ans)) (w : Way) (a : Ans) : Bool :=
  ds.all fun d => !decide (d.way = w) || d.accepts a

variable [DecidableEq Ans]

/-- **Declarations as alternatives**: one run for each way; a result is kept when some
declaration of its way accepts it; the runs are combined as a union of bags, which adds no copies. -/
def alternatives (run : Way → Multiset Ans) (ds : List (Fitting Way Ans)) : Multiset Ans :=
  (ways ds).sup fun w => (run w).filter fun a => someAccepts ds w a = true

/-- **Declarations as promises**: one run for each way; a result is kept only when every
declaration of its way accepts it. -/
def promises (run : Way → Multiset Ans) (ds : List (Fitting Way Ans)) : Multiset Ans :=
  (ways ds).sup fun w => (run w).filter fun a => allAccept ds w a = true

/-- **HE since July 2024**: the first fitting declaration decides. -/
def firstFit (run : Way → Multiset Ans) : List (Fitting Way Ans) → Multiset Ans
  | [] => 0
  | d :: _ => (run d.way).filter fun a => d.accepts a = true

/-- **HE before July 2024**: one run for each declaration, every result kept. -/
def perDeclaration (run : Way → Multiset Ans) (ds : List (Fitting Way Ans)) : Multiset Ans :=
  (ds.map fun d => (run d.way).filter fun a => d.accepts a = true).sum

omit [DecidableEq Ans] in
theorem ways_congr {ds ds' : List (Fitting Way Ans)} (same : ∀ d, d ∈ ds ↔ d ∈ ds') :
    ways ds = ways ds' := by
  ext w
  simp only [ways, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨d, member, rfl⟩
    exact ⟨d, (same d).mp member, rfl⟩
  · rintro ⟨d, member, rfl⟩
    exact ⟨d, (same d).mpr member, rfl⟩

omit [DecidableEq Ans] in
theorem someAccepts_eq_true {ds : List (Fitting Way Ans)} {w : Way} {a : Ans} :
    someAccepts ds w a = true ↔ ∃ d ∈ ds, d.way = w ∧ d.accepts a = true := by
  simp [someAccepts]

omit [DecidableEq Ans] in
theorem allAccept_eq_true {ds : List (Fitting Way Ans)} {w : Way} {a : Ans} :
    allAccept ds w a = true ↔ ∀ d ∈ ds, d.way = w → d.accepts a = true := by
  simp only [allAccept, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro h d member same
    rcases h d member with different | accepted
    · exact absurd same different
    · exact accepted
  · intro h d member
    by_cases same : d.way = w
    · exact Or.inr (h d member same)
    · exact Or.inl same

/-- The answers depend only on which declarations fit. -/
theorem alternatives_congr (run : Way → Multiset Ans) {ds ds' : List (Fitting Way Ans)}
    (same : ∀ d, d ∈ ds ↔ d ∈ ds') : alternatives run ds = alternatives run ds' := by
  unfold alternatives
  rw [ways_congr same]
  refine Finset.sup_congr rfl fun w _ => Multiset.filter_congr fun a _ => ?_
  simp only [someAccepts_eq_true]
  constructor
  · rintro ⟨d, member, rest⟩
    exact ⟨d, (same d).mp member, rest⟩
  · rintro ⟨d, member, rest⟩
    exact ⟨d, (same d).mpr member, rest⟩

/-- The same for `promises`. -/
theorem promises_congr (run : Way → Multiset Ans) {ds ds' : List (Fitting Way Ans)}
    (same : ∀ d, d ∈ ds ↔ d ∈ ds') : promises run ds = promises run ds' := by
  unfold promises
  rw [ways_congr same]
  refine Finset.sup_congr rfl fun w _ => Multiset.filter_congr fun a _ => ?_
  simp only [allAccept_eq_true]
  constructor
  · intro h d member
    exact h d ((same d).mpr member)
  · intro h d member
    exact h d ((same d).mp member)

/-- In particular the order of the declarations does not matter. -/
theorem alternatives_perm (run : Way → Multiset Ans) {ds ds' : List (Fitting Way Ans)}
    (h : ds.Perm ds') : alternatives run ds = alternatives run ds' :=
  alternatives_congr run fun _ => h.mem_iff

/-- **Declarations add no answers**: every answer, with its copies, is one of a run's. -/
theorem alternatives_le_runs (run : Way → Multiset Ans) (ds : List (Fitting Way Ans)) :
    alternatives run ds ≤ (ways ds).sup run :=
  Finset.sup_mono_fun fun _ _ => Multiset.filter_le _ _

omit [DecidableEq Ans] in
theorem ways_subset {ds ds' : List (Fitting Way Ans)} (sub : ∀ d ∈ ds, d ∈ ds') :
    ways ds ⊆ ways ds' := by
  intro w member
  simp only [ways, List.mem_toFinset, List.mem_map] at member ⊢
  obtain ⟨d, inside, rfl⟩ := member
  exact ⟨d, sub d inside, rfl⟩

/-- **Monotone**: a further fitting declaration never removes an answer of `alternatives`. -/
theorem alternatives_mono (run : Way → Multiset Ans) {ds ds' : List (Fitting Way Ans)}
    (sub : ∀ d ∈ ds, d ∈ ds') : alternatives run ds ≤ alternatives run ds' := by
  unfold alternatives
  calc (ways ds).sup (fun w => (run w).filter fun a => someAccepts ds w a = true)
      ≤ (ways ds).sup (fun w => (run w).filter fun a => someAccepts ds' w a = true) :=
        Finset.sup_mono_fun fun w _ => Multiset.monotone_filter_right _ fun a h => by
          obtain ⟨d, member, rest⟩ := someAccepts_eq_true.mp h
          exact someAccepts_eq_true.mpr ⟨d, sub d member, rest⟩
    _ ≤ (ways ds').sup (fun w => (run w).filter fun a => someAccepts ds' w a = true) :=
        Finset.sup_mono (ways_subset sub)

/-- **Antitone**: a further declaration of a way already present never adds an answer of
`promises`. -/
theorem promises_antitone (run : Way → Multiset Ans) {ds ds' : List (Fitting Way Ans)}
    (sub : ∀ d ∈ ds, d ∈ ds') (sameWays : ways ds' = ways ds) :
    promises run ds' ≤ promises run ds := by
  unfold promises
  rw [sameWays]
  exact Finset.sup_mono_fun fun w _ => Multiset.monotone_filter_right _ fun a h =>
    allAccept_eq_true.mpr fun d member => allAccept_eq_true.mp h d (sub d member)

omit [DecidableEq Ans] in
theorem ways_of_oneWay {d₀ : Fitting Way Ans} {rest : List (Fitting Way Ans)}
    (oneWay : ∀ d ∈ d₀ :: rest, d.way = d₀.way) : ways (d₀ :: rest) = {d₀.way} := by
  ext w
  simp only [ways, List.mem_toFinset, List.mem_map, Finset.mem_singleton]
  constructor
  · rintro ⟨d, member, rfl⟩
    exact oneWay d member
  · rintro rfl
    exact ⟨d₀, List.mem_cons_self .., rfl⟩

/-- **Agreement**: declarations that run the call one way and accept the same results answer
under `alternatives` as the first does. -/
theorem alternatives_eq_firstFit_of_agree (run : Way → Multiset Ans) (d₀ : Fitting Way Ans)
    (rest : List (Fitting Way Ans)) (oneWay : ∀ d ∈ d₀ :: rest, d.way = d₀.way)
    (agree : ∀ d ∈ d₀ :: rest, ∀ a ∈ run d₀.way, d.accepts a = d₀.accepts a) :
    alternatives run (d₀ :: rest) = firstFit run (d₀ :: rest) := by
  unfold alternatives firstFit
  rw [ways_of_oneWay oneWay, Finset.sup_singleton]
  refine Multiset.filter_congr fun a inRun => ?_
  rw [someAccepts_eq_true]
  constructor
  · rintro ⟨d, member, _, accepted⟩
    rw [← agree d member a inRun]
    exact accepted
  · intro accepted
    exact ⟨d₀, List.mem_cons_self .., rfl, accepted⟩

/-- The same for `promises`. -/
theorem promises_eq_firstFit_of_agree (run : Way → Multiset Ans) (d₀ : Fitting Way Ans)
    (rest : List (Fitting Way Ans)) (oneWay : ∀ d ∈ d₀ :: rest, d.way = d₀.way)
    (agree : ∀ d ∈ d₀ :: rest, ∀ a ∈ run d₀.way, d.accepts a = d₀.accepts a) :
    promises run (d₀ :: rest) = firstFit run (d₀ :: rest) := by
  unfold promises firstFit
  rw [ways_of_oneWay oneWay, Finset.sup_singleton]
  refine Multiset.filter_congr fun a inRun => ?_
  rw [allAccept_eq_true]
  constructor
  · intro h
    exact h d₀ (List.mem_cons_self ..) rfl
  · intro accepted d member _
    rw [agree d member a inRun]
    exact accepted


/-- **When the fitting declarations agree, the first one answers alike in every order**: any
arrangement of them gives, under `firstFit`, what `alternatives` gives. -/
theorem firstFit_eq_alternatives_of_agree (run : Way → Multiset Ans) (d₀ : Fitting Way Ans)
    (rest : List (Fitting Way Ans)) (oneWay : ∀ d ∈ d₀ :: rest, d.way = d₀.way)
    (agree : ∀ d ∈ d₀ :: rest, ∀ a ∈ run d₀.way, d.accepts a = d₀.accepts a)
    {d₁ : Fitting Way Ans} {rest' : List (Fitting Way Ans)}
    (perm : (d₁ :: rest').Perm (d₀ :: rest)) :
    firstFit run (d₁ :: rest') = alternatives run (d₀ :: rest) := by
  rw [alternatives_eq_firstFit_of_agree run d₀ rest oneWay agree]
  have member : d₁ ∈ d₀ :: rest := perm.mem_iff.mp (List.mem_cons_self ..)
  have sameWay : d₁.way = d₀.way := oneWay d₁ member
  show (run d₁.way).filter (fun a => d₁.accepts a = true) =
    (run d₀.way).filter (fun a => d₀.accepts a = true)
  rw [sameWay]
  exact Multiset.filter_congr fun a inRun => by rw [agree d₁ member a inRun]

end General

namespace Controls

/-- How a call is run: its arguments evaluated first, or held as written. -/
inductive HowRun where
  | evaluated
  | held
  deriving DecidableEq, Repr

/-- The results that occur in the measured programs. -/
inductive Result where
  | zero
  | z
  | three
  | onePlusTwo
  | one
  | two
  | done
  deriving DecidableEq, Repr

/-- `(= (pick) 0)`, `(= (pick) Z)`, with `(: pick (-> Number))` and `(: pick (-> Nat))`; `Z` is a
`Nat` only. -/
def pickRun : HowRun → Multiset Result := fun _ => {.zero, .z}
def pickNumber : Fitting HowRun Result := ⟨.evaluated, fun r => decide (r = .zero)⟩
def pickNat : Fitting HowRun Result := ⟨.evaluated, fun r => decide (r = .z)⟩

theorem pick_today_depends_on_order :
    firstFit pickRun [pickNumber, pickNat] = {.zero} ∧
      firstFit pickRun [pickNat, pickNumber] = {.z} := by
  decide

theorem pick_alternatives : alternatives pickRun [pickNumber, pickNat] = {.zero, .z} := by
  decide

theorem pick_promises : promises pickRun [pickNumber, pickNat] = 0 := by
  decide

/-- With `(:< Nat Number)`: `f` typed `(-> Number Number)` and `(-> Nat Nat)`, body `(pick)`, call
`(f Z)`. `Z` is a Number through the subtype. -/
def subRun : HowRun → Multiset Result := fun _ => {.zero, .z}
def subNumber : Fitting HowRun Result := ⟨.evaluated, fun r => decide (r = .zero ∨ r = .z)⟩
def subNat : Fitting HowRun Result := ⟨.evaluated, fun r => decide (r = .z)⟩

theorem numberAndNat_today_depends_on_order :
    firstFit subRun [subNumber, subNat] = {.zero, .z} ∧
      firstFit subRun [subNat, subNumber] = {.z} := by
  decide

theorem numberAndNat_alternatives : alternatives subRun [subNumber, subNat] = {.zero, .z} := by
  decide

theorem numberAndNat_promises : promises subRun [subNumber, subNat] = {.z} := by
  decide

/-- Under `alternatives` the Nat declaration changes nothing here; under `promises` it removes `0`. -/
theorem numberAndNat_refinement :
    alternatives subRun [subNumber, subNat] = alternatives subRun [subNumber] ∧
      promises subRun [subNumber, subNat] ≠ promises subRun [subNumber] := by
  decide

/-- `(= (q2 $x) $x)` typed `(-> Atom Atom)` and `(-> Number Number)`, call `(q2 (+ 1 2))`: the held
way gives `(+ 1 2)`, the evaluated way `3`. -/
def q2Run : HowRun → Multiset Result
  | .held => {.onePlusTwo}
  | .evaluated => {.three}
def q2Atom : Fitting HowRun Result := ⟨.held, fun _ => true⟩
def q2Number : Fitting HowRun Result := ⟨.evaluated, fun r => decide (r = .three)⟩

theorem q2_today_depends_on_order :
    firstFit q2Run [q2Atom, q2Number] = {.onePlusTwo} ∧
      firstFit q2Run [q2Number, q2Atom] = {.three} := by
  decide

theorem q2_alternatives : alternatives q2Run [q2Atom, q2Number] = {.onePlusTwo, .three} := by
  decide

/-- `(= (f $x) $x)` typed `(-> Number String)` and `(-> Number Number)`, call `(f 1)`. -/
def fRun : HowRun → Multiset Result := fun _ => {.one}
def fString : Fitting HowRun Result := ⟨.evaluated, fun _ => false⟩
def fNumber : Fitting HowRun Result := ⟨.evaluated, fun r => decide (r = .one)⟩

theorem f_today_depends_on_order :
    firstFit fRun [fString, fNumber] = 0 ∧ firstFit fRun [fNumber, fString] = {.one} := by
  decide

theorem f_alternatives : alternatives fRun [fString, fNumber] = {.one} := by
  decide

theorem f_promises : promises fRun [fString, fNumber] = 0 := by
  decide

/-- `(= (g $x) (+ $x 1))` typed `(-> Number Number)` and `(-> $t $t)`, call `(g 1)`. -/
def gRun : HowRun → Multiset Result := fun _ => {.two}
def gNumber : Fitting HowRun Result := ⟨.evaluated, fun r => decide (r = .two)⟩
def gVariable : Fitting HowRun Result := ⟨.evaluated, fun _ => true⟩

theorem g_perDeclaration_duplicates :
    perDeclaration gRun [gNumber, gVariable] = {.two, .two} ∧
      alternatives gRun [gNumber, gVariable] = {.two} := by
  decide

/-- `(= (e $x) done)` typed `(-> Atom Atom)` and `(-> %Undefined% %Undefined%)`: two ways that give
the same answer. -/
def eRun : HowRun → Multiset Result := fun _ => {.done}
def eAtom : Fitting HowRun Result := ⟨.held, fun _ => true⟩
def eUndefined : Fitting HowRun Result := ⟨.evaluated, fun _ => true⟩

theorem e_two_ways_one_copy :
    alternatives eRun [eAtom, eUndefined] = {.done} ∧
      perDeclaration eRun [eAtom, eUndefined] = {.done, .done} := by
  decide

end Controls

#print axioms alternatives_congr
#print axioms alternatives_le_runs
#print axioms alternatives_mono
#print axioms promises_antitone
#print axioms alternatives_eq_firstFit_of_agree
#print axioms firstFit_eq_alternatives_of_agree
#print axioms Controls.numberAndNat_refinement
#print axioms Controls.e_two_ways_one_copy

end Mettapedia.Languages.MeTTa.HE.SeveralDeclarations
