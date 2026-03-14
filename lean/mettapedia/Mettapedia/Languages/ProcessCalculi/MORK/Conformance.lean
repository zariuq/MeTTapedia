import Mettapedia.Languages.ProcessCalculi.MORK.Space

/-!
# MORK Conformance Tests

Kernel-checked conformance tests for the MORK formalization.  Each fixture
documents the `.mm2` source, the `mork run` output (ground truth), and a
Lean theorem proving that the computable reference evaluator produces the
same result.

## Computable Reference Evaluator

The formalization's `Space = Finset Atom` makes `fireRule` noncomputable
(`Finset.toList`).  The computable reference evaluator mirrors these operations
over `List Atom` so that conformance theorems reduce by `rfl` in the kernel.

The spec-level `matchAtom` (Space.lean) handles all atom constructors including
expression patterns.  The computable evaluator's `cmatchAtom` provides the same
semantics over `List Atom` for kernel-checked `rfl` tests.

## MORK Ground Truth

All expected outputs are verified against `mork run` (MORK CLI).
The `.mm2` source for each test is included in the fixture's docstring.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## Spec-level expression matching -/

/-- The spec-level `matchAtom` now handles expression patterns (matches `cmatchAtom`). -/
theorem matchAtom_expression_works :
    matchAtom [] (.expression [.symbol "start"]) (.expression [.symbol "start"])
      = some [] := rfl

/-! ## Computable Reference Evaluator -/

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- A computable space is `List Atom` (bag semantics). -/
abbrev CSpace := List Atom

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

mutual
/-- Match a pattern atom against a concrete atom, threading substitution.
    Handles `.expression` patterns by recursive element-wise matching. -/
def Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchAtom
    (σ : Subst) (pat conc : Atom) : Option Subst :=
  match pat, conc with
  | .var v, a =>
    match σ.lookup v with
    | some a' => if a == a' then some σ else none
    | none    => some ((v, a) :: σ)
  | .symbol s, .symbol t     => if s == t then some σ else none
  | .grounded g, .grounded h => if g == h then some σ else none
  | .expression ps, .expression cs =>
    Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchAtomList σ ps cs
  | _, _ => none

/-- Match lists of atoms element-wise (mutual helper for `cmatchAtom`). -/
def Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchAtomList
    (σ : Subst) (pats concs : List Atom) : Option Subst :=
  match pats, concs with
  | [], [] => some σ
  | p :: ps, c :: cs =>
    match Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchAtom σ p c with
    | some σ' =>
      Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchAtomList σ' ps cs
    | none => none
  | _, _ => none
end

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

namespace Computable

/-- Computable: match all pattern atoms against a list space. -/
def cmatchPattern (σ : Subst) (s : CSpace) (p : Pattern) :
    List (Subst × List Atom) :=
  let rec go : List Atom → Subst → List Atom → List (Subst × List Atom)
    | [], σ', consumed => [(σ', consumed)]
    | pat :: rest, σ', consumed =>
        let available := s.filter (!consumed.contains ·)
        let found := available.filterMap fun a =>
          (cmatchAtom σ' pat a).map (·, a)
        found.flatMap fun (σ'', a) =>
          go rest σ'' (a :: consumed)
  go p.atoms σ []

/-- Computable: apply sinks to a list space. -/
def capplySinks (s : CSpace) (σ : Subst) (tmpl : Template) : CSpace :=
  tmpl.sinks.foldl (fun s' sink =>
    match sink with
    | .add a =>
      let a' := applySubst σ a
      if isGroundAtom a' then s' ++ [a'] else s'
    | .remove a =>
      s'.erase (applySubst σ a)
    | .head a =>
      let a' := applySubst σ a
      if isGroundAtom a' then
        if s'.contains a' then s' else s' ++ [a']
      else s'
  ) s

/-- Computable: fire a rule once in a list space.
    Returns all possible one-step successor spaces. -/
def cfireRule (s : CSpace) (r : ExecRule) : List CSpace :=
  (cmatchPattern [] s r.pat).map fun (σ, _consumed) =>
    capplySinks s σ r.tmpl

/-- Fire a rule to fixpoint: keep applying until no matches remain.
    Uses fuel to guarantee termination.  MORK's `mork run` executes
    a rule exhaustively within a priority step; this mirrors that. -/
def cfireToFixpoint (fuel : Nat) (s : CSpace) (r : ExecRule) : CSpace :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match cfireRule s r with
    | [] => s  -- no match: fixpoint reached
    | s' :: _ => cfireToFixpoint fuel' s' r  -- take first result, continue

/-- Computable: match a single source factor against a list space. -/
def cmatchSourceFactor (σ : Subst) (s : CSpace) (src : SourceFactor) :
    List (Subst × Atom) :=
  match src with
  | .btm pat =>
    s.filterMap fun a => (cmatchAtom σ pat a).map (·, a)
  | .eqConstraint pat witness =>
    let target := applySubst σ pat
    if s.contains target then
      match cmatchAtom σ witness target with
      | some σ' => [(σ', target)]
      | none => []
    else []
  | .neqConstraint pat witness =>
    let target := applySubst σ pat
    let remaining := s.erase target
    remaining.filterMap fun a => (cmatchAtom σ witness a).map (·, a)

/-- Computable: match a list of source factors against a list space. -/
def cmatchSourceFactors (σ : Subst) (s : CSpace) (factors : List SourceFactor) :
    List (Subst × List Atom) :=
  let rec go : List SourceFactor → Subst → List Atom →
      List (Subst × List Atom)
    | [], σ', consumed => [(σ', consumed)]
    | src :: rest, σ', consumed =>
        let available := s.filter (!consumed.contains ·)
        let found := cmatchSourceFactor σ' available src
        found.flatMap fun (σ'', a) =>
          go rest σ'' (a :: consumed)
  go factors σ []

/-- Computable: match an `InputSpec` against a list space. -/
def cmatchInputSpec (σ : Subst) (s : CSpace) (input : InputSpec) :
    List (Subst × List Atom) :=
  match input with
  | .compat pat => cmatchPattern σ s pat
  | .explicit factors => cmatchSourceFactors σ s factors

/-- Computable: fire a `SourceExecRule` in a list space. -/
def cfireSourceRule (s : CSpace) (r : SourceExecRule) : List CSpace :=
  ((cmatchInputSpec [] s r.input).filter fun (σ, _) =>
    matchSourceGuards σ r.guards).map fun (σ, _consumed) =>
    capplySinks s σ r.tmpl

end Computable

open Computable

/-! ## MORK-Verified Conformance Fixtures

Each fixture includes:
- The `.mm2` source (as a comment)
- The `mork run` output (ground truth)
- A Lean `rfl` theorem matching the evaluator output
-/

/-! ### Test 1: Simple add + remove

```mm2
(start)
(exec (0 create-facts)
  (, (start))
  (O (+ (color apple red))
     (+ (color banana yellow))
     (+ (color grape purple))
     (- (start))))
```

`mork run` output: `(color apple red)`, `(color grape purple)`, `(color banana yellow)`
-/

private def test1_rule : ExecRule :=
  mkExecRule 0 "create-facts"
    (mkPattern [.expression [.symbol "start"]])
    (mkTemplate [mkAdd (.expression [.symbol "color", .symbol "apple", .symbol "red"]),
                 mkAdd (.expression [.symbol "color", .symbol "banana", .symbol "yellow"]),
                 mkAdd (.expression [.symbol "color", .symbol "grape", .symbol "purple"]),
                 mkRemove (.expression [.symbol "start"])])

/-- test_add_simple: verified against `mork run`. -/
theorem conformance_test1_add_simple :
    cfireRule [.expression [.symbol "start"]] test1_rule =
      [[.expression [.symbol "color", .symbol "apple", .symbol "red"],
        .expression [.symbol "color", .symbol "banana", .symbol "yellow"],
        .expression [.symbol "color", .symbol "grape", .symbol "purple"]]] := rfl

/-! ### Test 2: Constant add (flat symbol)

```mm2
(trigger-ready)
(exec 0
  (, (trigger-ready))
  (O (+ MATCHED)
     (- (trigger-ready))))
```

`mork run` output: `MATCHED`
-/

private def test2_rule : ExecRule :=
  mkExecRule 0 "add-constant"
    (mkPattern [.expression [.symbol "trigger-ready"]])
    (mkTemplate [mkAdd (.symbol "MATCHED"),
                 mkRemove (.expression [.symbol "trigger-ready"])])

/-- test_add_constant: verified against `mork run`. -/
theorem conformance_test2_add_constant :
    cfireRule [.expression [.symbol "trigger-ready"]] test2_rule =
      [[.symbol "MATCHED"]] := rfl

/-! ### Test 3: Variable binding inside expressions

Source: `examples/lean_conformance/test3_var_binding.mm2`

```mm2
(edge a b)
(exec (0 edge-to-path)
  (, (edge $x $y))
  (O (+ (path $x $y))
     (- (edge $x $y))))
```

`mork run` output: `(path a b)`
-/

private def test3_rule : ExecRule :=
  mkExecRule 0 "edge-to-path"
    (mkPattern [.expression [.symbol "edge", .var "x", .var "y"]])
    (mkTemplate [mkAdd (.expression [.symbol "path", .var "x", .var "y"]),
                 mkRemove (.expression [.symbol "edge", .var "x", .var "y"])])

/-- Variable binding: `(edge a b)` → `(path a b)`. Verified against `mork run`. -/
theorem conformance_test3_var_binding :
    cfireRule [.expression [.symbol "edge", .symbol "a", .symbol "b"]] test3_rule =
      [[.expression [.symbol "path", .symbol "a", .symbol "b"]]] := rfl

/-! ### Test 4: Conjunctive pattern with shared variable

Source: `examples/lean_conformance/test4_conjunctive.mm2`

```mm2
(person alice)
(age alice 30)
(exec (0 join)
  (, (person $name) (age $name $years))
  (O (+ (profile $name $years))
     (- (person $name))
     (- (age $name $years))))
```

`mork run` output: `(profile alice 30)`
-/

private def test4_rule : ExecRule :=
  mkExecRule 0 "join"
    (mkPattern [.expression [.symbol "person", .var "name"],
                .expression [.symbol "age", .var "name", .var "years"]])
    (mkTemplate [mkAdd (.expression [.symbol "profile", .var "name", .var "years"]),
                 mkRemove (.expression [.symbol "person", .var "name"]),
                 mkRemove (.expression [.symbol "age", .var "name", .var "years"])])

/-- Conjunctive match with shared variable: verified against `mork run`. -/
theorem conformance_test4_conjunctive :
    cfireRule [.expression [.symbol "person", .symbol "alice"],
              .expression [.symbol "age", .symbol "alice", .symbol "30"]]
             test4_rule =
      [[.expression [.symbol "profile", .symbol "alice", .symbol "30"]]] := rfl

/-! ### Test 5: Equality constraint via repeated variable

Source: `examples/lean_conformance/test5_equal_pair.mm2`

```mm2
(pair 5 5)
(pair 3 7)
(exec (0 find-equal)
  (, (pair $x $x))
  (O (+ (equal-pair $x))
     (- (pair $x $x))))
```

`mork run` output: `(equal-pair 5)`, `(pair 3 7)`
-/

private def test5_rule : ExecRule :=
  mkExecRule 0 "find-equal"
    (mkPattern [.expression [.symbol "pair", .var "x", .var "x"]])
    (mkTemplate [mkAdd (.expression [.symbol "equal-pair", .var "x"]),
                 mkRemove (.expression [.symbol "pair", .var "x", .var "x"])])

/-- Equality constraint: `(pair 5 5)` matches `(pair $x $x)`, `(pair 3 7)` does not.
    Verified against `mork run`. -/
theorem conformance_test5_equal_pair :
    cfireRule [.expression [.symbol "pair", .symbol "5", .symbol "5"],
              .expression [.symbol "pair", .symbol "3", .symbol "7"]]
             test5_rule =
      [[.expression [.symbol "pair", .symbol "3", .symbol "7"],
        .expression [.symbol "equal-pair", .symbol "5"]]] := rfl

/-! ### Test 6: Pattern mismatch (negative test)

Source: `examples/lean_conformance/test6_no_match.mm2`

```mm2
(foo a)
(exec (0 try-match)
  (, (bar $x))
  (O (+ (matched $x))))
```

`mork run` output: `(foo a)` (rule does not fire)
-/

/-- Mismatch: `(bar $x)` pattern does not match `(foo a)` atom.
    Verified against `mork run`. -/
theorem conformance_test6_no_match :
    cfireRule [.expression [.symbol "foo", .symbol "a"]]
      (mkExecRule 0 "try-match"
        (mkPattern [.expression [.symbol "bar", .var "x"]])
        (mkTemplate [mkAdd (.expression [.symbol "matched", .var "x"])])) = [] := rfl

/-! ### Test 7: Nested expression with variable

Source: `examples/lean_conformance/test7_nested.mm2`

```mm2
(f (g a))
(exec (0 nested)
  (, (f (g $x)))
  (O (+ (found $x))
     (- (f (g $x)))))
```

`mork run` output: `(found a)`
-/

private def test7_rule : ExecRule :=
  mkExecRule 0 "nested"
    (mkPattern [.expression [.symbol "f",
                 .expression [.symbol "g", .var "x"]]])
    (mkTemplate [mkAdd (.expression [.symbol "found", .var "x"]),
                 mkRemove (.expression [.symbol "f",
                            .expression [.symbol "g", .var "x"]])])

/-- Nested expression: `(f (g a))` matches `(f (g $x))`, binds `x=a`.
    Verified against `mork run`. -/
theorem conformance_test7_nested :
    cfireRule [.expression [.symbol "f",
               .expression [.symbol "g", .symbol "a"]]]
             test7_rule =
      [[.expression [.symbol "found", .symbol "a"]]] := rfl

/-! ### Test 8: Multi-step exhaustive execution

Source: `examples/lean_conformance/test8_multi_step.mm2`

```mm2
(task a) (task b) (task c)
(exec (0 process)
  (, (task $x))
  (O (+ (done $x)) (- (task $x))))
```

`mork run` output: `(done a)`, `(done b)`, `(done c)`

MORK runs the rule exhaustively. We test both:
- One-step: `cfireRule` returns 3 possible successor spaces
- Fixpoint: `cfireToFixpoint` runs all 3 steps
-/

private def test8_rule : ExecRule :=
  mkExecRule 0 "process"
    (mkPattern [.expression [.symbol "task", .var "x"]])
    (mkTemplate [mkAdd (.expression [.symbol "done", .var "x"]),
                 mkRemove (.expression [.symbol "task", .var "x"])])

private def test8_space : CSpace :=
  [.expression [.symbol "task", .symbol "a"],
   .expression [.symbol "task", .symbol "b"],
   .expression [.symbol "task", .symbol "c"]]

/-- One-step: 3 possible firings (one per task atom). -/
theorem conformance_test8_one_step :
    (cfireRule test8_space test8_rule).length = 3 := rfl

-- Multi-step chain: each step reduces by `rfl`.
-- cfireToFixpoint doesn't reduce definitionally, so we chain steps explicitly.

private def test8_s1 : CSpace := (cfireRule test8_space test8_rule).head!
private def test8_s2 : CSpace := (cfireRule test8_s1 test8_rule).head!
private def test8_s3 : CSpace := (cfireRule test8_s2 test8_rule).head!

/-- Step 1: process task a. -/
theorem conformance_test8_step1 :
    test8_s1 = [.expression [.symbol "task", .symbol "b"],
                .expression [.symbol "task", .symbol "c"],
                .expression [.symbol "done", .symbol "a"]] := rfl

/-- Step 2: process task b. -/
theorem conformance_test8_step2 :
    test8_s2 = [.expression [.symbol "task", .symbol "c"],
                .expression [.symbol "done", .symbol "a"],
                .expression [.symbol "done", .symbol "b"]] := rfl

/-- Step 3 (fixpoint): all tasks done. Verified against `mork run`. -/
theorem conformance_test8_step3 :
    test8_s3 = [.expression [.symbol "done", .symbol "a"],
                .expression [.symbol "done", .symbol "b"],
                .expression [.symbol "done", .symbol "c"]] := rfl

/-- No further matches at fixpoint. -/
theorem conformance_test8_fixpoint :
    cfireRule test8_s3 test8_rule = [] := rfl

/-! ### Test 9: Arity mismatch (negative test)

`(f a b)` pattern does not match `(f a)` (different arity). -/

/-- Arity mismatch: 3-element pattern vs 2-element expression. -/
theorem conformance_test9_arity_mismatch :
    cfireRule [.expression [.symbol "f", .symbol "a"]]
      (mkExecRule 0 "arity"
        (mkPattern [.expression [.symbol "f", .symbol "a", .symbol "b"]])
        (mkTemplate [mkAdd (.symbol "matched")])) = [] := rfl

/-! ## Computable ↔ Spec Correspondence

The computable evaluator (`cmatchAtom`, `capplySinks`, `cfireRule`) mirrors
the spec-level semantics (`matchAtom`, `applySinks`, `fireRule`) but uses
`List Atom` instead of `Finset Atom` for kernel-computability.

This section proves that they agree on the covered fragment:

1. `cmatchAtom = matchAtom` (exact, unconditional)
2. `capplySink_toFinset` (per-sink, List → Finset under `Nodup`)
3. `capplySinks_toFinset` (full template, List → Finset under `Nodup`)

The `Nodup` hypothesis is needed because `List.erase` removes only the first
occurrence while `Finset.erase` removes the element entirely. The conformance
tests all start from duplicate-free lists, so this restriction is benign.

End-to-end `cfireRule ↔ fireRule` is blocked by `Finset.toList` being
noncomputable in the spec-level `matchPattern`.  The correspondence is:
- Matching: `cmatchAtom = matchAtom` (proven, exact)
- Sinks: `capplySinks` agrees with `applySinks` modulo `toFinset` (proven, under `Nodup`)
- Full firing: the gap is `matchPattern` (noncomputable iteration over `Finset.toList`)
-/

section Correspondence

open Computable

mutual
/-- `cmatchAtom` is identical to `matchAtom` on all inputs.
    Both perform first-order pattern matching with the same case structure.
    Proven by mutual structural recursion. -/
theorem cmatchAtom_eq_matchAtom (σ : Subst) (pat conc : Atom) :
    cmatchAtom σ pat conc = matchAtom σ pat conc := by
  unfold cmatchAtom matchAtom
  match pat, conc with
  | .var _, _ => rfl
  | .symbol _, .symbol _ => rfl
  | .symbol _, .var _ => rfl
  | .symbol _, .grounded _ => rfl
  | .symbol _, .expression _ => rfl
  | .grounded _, .grounded _ => rfl
  | .grounded _, .var _ => rfl
  | .grounded _, .symbol _ => rfl
  | .grounded _, .expression _ => rfl
  | .expression ps, .expression cs =>
    exact cmatchAtomList_eq_matchAtomList σ ps cs
  | .expression _, .var _ => rfl
  | .expression _, .symbol _ => rfl
  | .expression _, .grounded _ => rfl

/-- Mutual companion: `cmatchAtomList` = `matchAtom.matchAtomList`. -/
theorem cmatchAtomList_eq_matchAtomList (σ : Subst) (pats concs : List Atom) :
    cmatchAtomList σ pats concs = matchAtom.matchAtomList σ pats concs := by
  match pats, concs with
  | [], [] => simp [cmatchAtomList, matchAtom.matchAtomList]
  | [], _ :: _ => simp [cmatchAtomList, matchAtom.matchAtomList]
  | _ :: _, [] => simp [cmatchAtomList, matchAtom.matchAtomList]
  | p :: ps, c :: cs =>
    simp only [cmatchAtomList, matchAtom.matchAtomList]
    rw [cmatchAtom_eq_matchAtom σ p c]
    cases matchAtom σ p c with
    | none => rfl
    | some σ' => exact cmatchAtomList_eq_matchAtomList σ' ps cs
end

/-- Applying a single `add` sink on a list and projecting to `Finset` equals
    the spec-level `applySink` on the `Finset` projection.
    No preconditions needed: `(l ++ [a]).toFinset = l.toFinset ∪ {a}`. -/
theorem capplySink_add_toFinset (s : List Atom) (σ : Subst) (a : Atom) :
    (if isGroundAtom (applySubst σ a) then s ++ [applySubst σ a] else s).toFinset =
    applySink s.toFinset σ (.add a) := by
  simp only [applySink]
  split_ifs with hg
  · simp [List.toFinset_append]
  · rfl

/-- Applying a single `head` sink on a list and projecting to `Finset` equals
    the spec-level `applySink` on the `Finset` projection.
    No preconditions needed: `head` is idempotent on lists, and `∪` is
    idempotent on `Finset`. -/
theorem capplySink_head_toFinset (s : List Atom) (σ : Subst) (a : Atom) :
    (if isGroundAtom (applySubst σ a) then
       if s.contains (applySubst σ a) then s else s ++ [applySubst σ a]
     else s).toFinset = applySink s.toFinset σ (.head a) := by
  simp only [applySink]
  split_ifs with hg hc
  · -- ground, already contains: s.toFinset = s.toFinset ∪ {a'}
    symm; rw [Finset.union_eq_left]
    exact Finset.singleton_subset_iff.mpr
      (List.mem_toFinset.mpr (List.contains_iff_mem.mp hc))
  · -- ground, not contains: (s ++ [a']).toFinset = s.toFinset ∪ {a'}
    rw [List.toFinset_append]; simp
  · rfl

/-- For `remove` sinks, the `Nodup` hypothesis guarantees that `List.erase`
    (removing first occurrence) agrees with `Finset.erase` (removing the element).
    Without `Nodup`, a list like `[a, a]` would have `(l.erase a).toFinset = {a}`
    but `l.toFinset.erase a = ∅`. -/
theorem capplySink_remove_toFinset (s : List Atom) (hnd : s.Nodup) (σ : Subst) (a : Atom) :
    (s.erase (applySubst σ a)).toFinset = applySink s.toFinset σ (.remove a) := by
  simp only [applySink]
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase]
  constructor
  · intro hx
    exact ⟨fun heq => absurd (heq ▸ hx) (List.Nodup.not_mem_erase hnd),
           List.mem_of_mem_erase hx⟩
  · intro ⟨hne, hx_mem⟩
    exact (List.mem_erase_of_ne hne).mpr hx_mem

/-! ### Single computable sink step -/

/-- Apply a single sink to a list space (factored out for stating NodupSafe). -/
def capplySinkStep (σ : Subst) (s' : CSpace) (sink : Sink) : CSpace :=
  match sink with
  | .add a =>
    let a' := applySubst σ a
    if isGroundAtom a' then s' ++ [a'] else s'
  | .remove a =>
    s'.erase (applySubst σ a)
  | .head a =>
    let a' := applySubst σ a
    if isGroundAtom a' then
      if s'.contains a' then s' else s' ++ [a']
    else s'

/-- `capplySinks` is `foldl capplySinkStep`. -/
theorem capplySinks_eq_foldl (s : CSpace) (σ : Subst) (tmpl : Template) :
    capplySinks s σ tmpl = tmpl.sinks.foldl (capplySinkStep σ) s := rfl

/-- `NodupSafe s σ sinks` means the accumulator is `Nodup` at every
    remove-sink step during `foldl (capplySinkStep σ) s sinks`. -/
def NodupSafe (s : CSpace) (σ : Subst) (sinks : List Sink) : Prop :=
  ∀ (i : Fin sinks.length), sinks[i].isRemove = true →
    (sinks.take i |>.foldl (capplySinkStep σ) s).Nodup

/-- `NodupSafe` at every step of the outer foldl over match results.
    At step `i`, the accumulator (result of folding the first `i` match results
    through `capplySinks`) must satisfy `NodupSafe` for the next substitution. -/
def FoldNodupSafe (acc : CSpace) (ms : List (Subst × List Atom)) (tmpl : Template) : Prop :=
  ∀ (i : Fin ms.length),
    NodupSafe
      (ms.take i |>.foldl (fun a (σ, _) => capplySinks a σ tmpl) acc)
      ms[i].1
      tmpl.sinks

/-! ### Per-sink step correspondence -/

/-- `capplySinkStep` on add/head corresponds to spec `applySink` via toFinset
    (unconditionally). -/
theorem capplySinkStep_toFinset_add (s : List Atom) (σ : Subst) (a : Atom) :
    (capplySinkStep σ s (.add a)).toFinset = applySink s.toFinset σ (.add a) :=
  capplySink_add_toFinset s σ a

theorem capplySinkStep_toFinset_head (s : List Atom) (σ : Subst) (a : Atom) :
    (capplySinkStep σ s (.head a)).toFinset = applySink s.toFinset σ (.head a) :=
  capplySink_head_toFinset s σ a

theorem capplySinkStep_toFinset_remove (s : List Atom) (hnd : s.Nodup) (σ : Subst) (a : Atom) :
    (capplySinkStep σ s (.remove a)).toFinset = applySink s.toFinset σ (.remove a) :=
  capplySink_remove_toFinset s hnd σ a

/-! ### Sinks composition correspondence -/

/-- For templates without `remove` sinks, the computable `capplySinks` on a list
    corresponds to spec-level `applySinks` via `toFinset`, unconditionally.
    No `Nodup` hypothesis needed because `add` and `head` sinks don't need it. -/
theorem capplySinks_toFinset_no_remove (s : List Atom) (σ : Subst) (tmpl : Template)
    (hno_rm : ∀ sink ∈ tmpl.sinks, sink.isRemove = false) :
    (capplySinks s σ tmpl).toFinset = applySinks s.toFinset σ tmpl := by
  simp only [capplySinks, applySinks]
  -- Both are foldl over tmpl.sinks; prove by induction on the sink list
  suffices h : ∀ (sinks : List Sink) (acc : List Atom),
      (∀ sink ∈ sinks, sink.isRemove = false) →
      (sinks.foldl (fun s' sink =>
        match sink with
        | .add a => let a' := applySubst σ a
                    if isGroundAtom a' then s' ++ [a'] else s'
        | .remove a => s'.erase (applySubst σ a)
        | .head a => let a' := applySubst σ a
                     if isGroundAtom a' then
                       if s'.contains a' then s' else s' ++ [a']
                     else s'
      ) acc).toFinset = sinks.foldl (applySink · σ) acc.toFinset by
    exact h tmpl.sinks s hno_rm
  intro sinks
  induction sinks with
  | nil => intro _ _; rfl
  | cons sink rest ih =>
    intro acc hno_rm'
    simp only [List.foldl]
    have hsink : sink.isRemove = false := hno_rm' sink List.mem_cons_self
    have hrest : ∀ s ∈ rest, s.isRemove = false :=
      fun s hs => hno_rm' s (List.mem_cons_of_mem _ hs)
    cases sink with
    | add a =>
      have hstep := capplySink_add_toFinset acc σ a
      conv_rhs => rw [← hstep]
      exact ih _ hrest
    | head a =>
      have hstep := capplySink_head_toFinset acc σ a
      conv_rhs => rw [← hstep]
      exact ih _ hrest
    | remove _ => simp [Sink.isRemove] at hsink

/-- For templates with `NodupSafe`, the computable `capplySinks` on a list
    corresponds to spec-level `applySinks` via `toFinset`.
    Subsumes `capplySinks_toFinset_no_remove` (trivially satisfied when
    no sinks are removes). -/
theorem capplySinks_toFinset_safe (s : List Atom) (σ : Subst) (tmpl : Template)
    (hsafe : NodupSafe s σ tmpl.sinks) :
    (capplySinks s σ tmpl).toFinset = applySinks s.toFinset σ tmpl := by
  simp only [capplySinks_eq_foldl, applySinks]
  -- Generalize: induction on sinks with a local NodupSafe
  suffices h : ∀ (sinks : List Sink) (acc : List Atom),
      (∀ (i : Fin sinks.length), sinks[i].isRemove = true →
        (sinks.take i |>.foldl (capplySinkStep σ) acc).Nodup) →
      (sinks.foldl (capplySinkStep σ) acc).toFinset =
        sinks.foldl (applySink · σ) acc.toFinset by
    exact h tmpl.sinks s hsafe
  intro sinks
  induction sinks with
  | nil => intro _ _; rfl
  | cons sink rest ih =>
    intro acc hsafe_local
    simp only [List.foldl, capplySinkStep]
    -- Per-sink step correspondence
    have hacc_step : (capplySinkStep σ acc sink).toFinset =
        applySink acc.toFinset σ sink := by
      cases sink with
      | add a => exact capplySink_add_toFinset acc σ a
      | head a => exact capplySink_head_toFinset acc σ a
      | remove a =>
        have hnd : acc.Nodup := by
          have := hsafe_local ⟨0, by simp [List.length]⟩
          simp [Sink.isRemove, List.take] at this
          exact this
        exact capplySink_remove_toFinset acc hnd σ a
    -- Apply IH with shifted NodupSafe
    rw [← hacc_step]
    -- The foldl body matches capplySinkStep; show the goal reduces
    change (rest.foldl (capplySinkStep σ) (capplySinkStep σ acc sink)).toFinset =
      rest.foldl (applySink · σ) (capplySinkStep σ acc sink).toFinset
    exact ih (capplySinkStep σ acc sink) fun ⟨i, hi⟩ hrem => by
      have hlt : i + 1 < (sink :: rest).length := by simp [List.length]; omega
      have := hsafe_local ⟨i + 1, hlt⟩
      specialize this (by simpa using hrem)
      simp only [List.take_succ_cons, List.foldl] at this
      exact this

/-! ### Foldl correspondence for multi-match firing -/

/-- `FoldNodupSafe` for the tail of a match-result list follows from
    `FoldNodupSafe` for the full list. -/
theorem FoldNodupSafe_tail (acc : CSpace) (hd : Subst × List Atom)
    (tl : List (Subst × List Atom)) (tmpl : Template)
    (hsafe : FoldNodupSafe acc (hd :: tl) tmpl) :
    FoldNodupSafe (capplySinks acc hd.1 tmpl) tl tmpl := by
  intro ⟨i, hi⟩
  have hi' : i + 1 < (hd :: tl).length := by simp; omega
  have := hsafe ⟨i + 1, hi'⟩
  convert this using 1

/-- Core foldl correspondence: if computable and spec match results have
    the same substitutions in the same order, and `FoldNodupSafe` holds
    for the computable accumulator, then the foldls produce corresponding
    results at the `Finset` level. -/
theorem foldl_capplySinks_toFinset
    (acc : CSpace) (acc_s : Space) (tmpl : Template)
    (cms : List (Subst × List Atom))
    (sms : List (Subst × Finset Atom))
    (hacc : acc.toFinset = acc_s)
    (hlen : cms.length = sms.length)
    (hσ : ∀ (i : ℕ) (hi_c : i < cms.length) (hi_s : i < sms.length),
      cms[i].1 = sms[i].1)
    (hsafe : FoldNodupSafe acc cms tmpl) :
    (cms.foldl (fun a (σ, _) => capplySinks a σ tmpl) acc).toFinset =
     sms.foldl (fun a (σ, _) => applySinks a σ tmpl) acc_s := by
  induction cms generalizing sms acc acc_s with
  | nil =>
    cases sms with
    | nil => simpa using hacc
    | cons _ _ => simp at hlen
  | cons chd ctl ih =>
    cases sms with
    | nil => simp at hlen
    | cons shd stl =>
      simp only [List.foldl_cons]
      have hσ0 : chd.1 = shd.1 := hσ 0 (by simp) (by simp)
      have hns : NodupSafe acc chd.1 tmpl.sinks := by
        have := hsafe ⟨0, by simp⟩
        simp [List.take] at this
        exact this
      have hstep : (capplySinks acc chd.1 tmpl).toFinset =
          applySinks acc_s shd.1 tmpl := by
        rw [← hσ0, ← hacc]
        exact capplySinks_toFinset_safe acc chd.1 tmpl hns
      exact ih (capplySinks acc chd.1 tmpl) (applySinks acc_s shd.1 tmpl) stl
        hstep
        (by simp at hlen ⊢; omega)
        (fun i hi_c hi_s => hσ (i + 1) (by simp; omega) (by simp; omega))
        (FoldNodupSafe_tail acc chd ctl tmpl hsafe)

/-! ### Match-pattern consumed membership -/

/-- Every atom in the consumed list returned by `cmatchPattern` belongs to
    the input space `s`.  This is a soundness property: consumed atoms
    always come from the space being searched. -/
theorem cmatchPattern_consumed_subset (σ₀ : Subst) (s : CSpace) (p : Pattern)
    (σ : Subst) (consumed : List Atom)
    (hmatch : (σ, consumed) ∈ cmatchPattern σ₀ s p) :
    ∀ a ∈ consumed, a ∈ s := by
  -- cmatchPattern unfolds to cmatchPattern.go p.atoms σ₀ []
  simp only [cmatchPattern] at hmatch
  -- Prove the generalized statement about go
  suffices h : ∀ (pats : List Atom) (σ_in : Subst) (consumed_in : List Atom)
      (σ_out : Subst) (consumed_out : List Atom),
      (σ_out, consumed_out) ∈ cmatchPattern.go s pats σ_in consumed_in →
      (∀ a ∈ consumed_in, a ∈ s) →
      ∀ a ∈ consumed_out, a ∈ s by
    exact h p.atoms σ₀ [] σ consumed hmatch (fun _ h => absurd h List.not_mem_nil)
  intro pats
  induction pats with
  | nil =>
    intro σ_in consumed_in σ_out consumed_out hmem hprev
    simp only [cmatchPattern.go, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨_, rfl⟩ := hmem
    exact hprev
  | cons pat rest ih =>
    intro σ_in consumed_in σ_out consumed_out hmem hprev
    simp only [cmatchPattern.go] at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨σ'', a_matched⟩, hmem_found, hmem_go⟩ := hmem
    apply ih σ'' (a_matched :: consumed_in) σ_out consumed_out hmem_go
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · -- a_matched came from available.filterMap
      rw [List.mem_filterMap] at hmem_found
      obtain ⟨a', ha'_mem, ha'_map⟩ := hmem_found
      simp only [List.mem_filter] at ha'_mem
      simp only [Option.map_eq_some_iff] at ha'_map
      obtain ⟨_, _, heq⟩ := ha'_map
      exact (Prod.mk.inj heq).2 ▸ ha'_mem.1
    · exact hprev a ha

/-! ### Match-pattern substitution extension -/

/-- The substitution returned by `cmatchPattern` extends the input substitution.
    `matchAtom` only prepends new bindings; it never removes existing ones.
    This is a structural invariant of first-order matching. -/
theorem cmatchPattern_subst_extends (σ₀ : Subst) (s : CSpace) (p : Pattern)
    (σ : Subst) (consumed : List Atom)
    (hmatch : (σ, consumed) ∈ cmatchPattern σ₀ s p) :
    ∀ v a, (v, a) ∈ σ₀ → (v, a) ∈ σ := by
  simp only [cmatchPattern] at hmatch
  -- Generalize over go, with the property that matchAtom extends substitutions
  suffices h : ∀ (pats : List Atom) (σ_in : Subst) (consumed_in : List Atom)
      (σ_out : Subst) (consumed_out : List Atom),
      (σ_out, consumed_out) ∈ cmatchPattern.go s pats σ_in consumed_in →
      ∀ v a, (v, a) ∈ σ_in → (v, a) ∈ σ_out by
    exact h p.atoms σ₀ [] σ consumed hmatch
  intro pats
  induction pats with
  | nil =>
    intro σ_in consumed_in σ_out consumed_out hmem
    simp only [cmatchPattern.go, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, _⟩ := hmem
    intro _ _ h; exact h
  | cons pat rest ih =>
    intro σ_in consumed_in σ_out consumed_out hmem
    simp only [cmatchPattern.go] at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨σ'', a_matched⟩, hmem_found, hmem_go⟩ := hmem
    intro v a hva_in
    -- Need: (v, a) ∈ σ_out
    -- Step 1: (v, a) ∈ σ_in → (v, a) ∈ σ'' (matchAtom extends)
    -- Step 2: (v, a) ∈ σ'' → (v, a) ∈ σ_out (IH on rest)
    apply ih σ'' (a_matched :: consumed_in) σ_out consumed_out hmem_go
    -- Need: (v, a) ∈ σ''
    rw [List.mem_filterMap] at hmem_found
    obtain ⟨conc, _, hmap⟩ := hmem_found
    simp only [Option.map_eq_some_iff] at hmap
    obtain ⟨σ_mid, hmatch_atom, heq⟩ := hmap
    -- heq : (σ_mid, conc) = (σ'', a_matched)
    have hσ : σ_mid = σ'' := by exact (Prod.mk.inj heq).1
    rw [cmatchAtom_eq_matchAtom] at hmatch_atom
    rw [← hσ]
    exact Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_extends σ_in pat conc σ_mid hmatch_atom v a hva_in

/-! ### Forward soundness: cmatchPattern → matchPattern -/

/-- Forward soundness: every `(σ, consumed)` returned by the computable
    `cmatchPattern` has a spec-level counterpart `(σ, consumed.toFinset)` in
    `matchPattern`.  The `s.Nodup` hypothesis is NOT needed: only set-level
    membership is required. -/
theorem cmatchPattern_toFinset_sound (σ₀ : Subst) (s : CSpace) (p : Pattern)
    (σ : Subst) (consumed : List Atom)
    (hmatch : (σ, consumed) ∈ cmatchPattern σ₀ s p) :
    (σ, consumed.toFinset) ∈ matchPattern σ₀ s.toFinset p := by
  simp only [cmatchPattern] at hmatch
  simp only [matchPattern]
  -- Generalize over go, relating list-consumed to Finset-consumed
  suffices h : ∀ (pats : List Atom) (σ_in : Subst)
      (consumed_in : List Atom) (consumed_fs : Finset Atom)
      (σ_out : Subst) (consumed_out : List Atom),
      consumed_fs = consumed_in.toFinset →
      (σ_out, consumed_out) ∈ cmatchPattern.go s pats σ_in consumed_in →
      (σ_out, consumed_out.toFinset) ∈ matchPattern.go s.toFinset pats σ_in consumed_fs by
    exact h p.atoms σ₀ [] ∅ σ consumed (by simp) hmatch
  intro pats
  induction pats with
  | nil =>
    intro σ_in consumed_in consumed_fs σ_out consumed_out hfs hmem
    simp only [cmatchPattern.go, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    simp only [matchPattern.go, List.mem_singleton, Prod.mk.injEq]
    exact ⟨trivial, hfs.symm⟩
  | cons pat rest ih =>
    intro σ_in consumed_in consumed_fs σ_out consumed_out hfs hmem
    simp only [cmatchPattern.go] at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨σ_mid, a⟩, hmem_found, hmem_go⟩ := hmem
    -- Extract: a came from the available list, cmatchAtom matched
    rw [List.mem_filterMap] at hmem_found
    obtain ⟨a', ha'_avail, ha'_match⟩ := hmem_found
    simp only [Option.map_eq_some_iff] at ha'_match
    obtain ⟨σ_mid', hcmatch, heq⟩ := ha'_match
    -- heq : (σ_mid', a') = (σ_mid, a)
    cases heq
    -- Now a' = a and σ_mid' = σ_mid in the context
    -- a ∈ s.filter (not in consumed_in) → a ∈ s.toFinset \ consumed_fs
    rw [List.mem_filter] at ha'_avail
    have ha_in_sdiff : a ∈ s.toFinset \ consumed_fs := by
      rw [Finset.mem_sdiff]
      refine ⟨List.mem_toFinset.mpr ha'_avail.1, ?_⟩
      rw [hfs]; intro h
      simp at ha'_avail
      exact ha'_avail.2 (List.mem_toFinset.mp h)
    -- matchAtom correspondence
    rw [cmatchAtom_eq_matchAtom] at hcmatch
    -- (σ_mid, a) ∈ matchOneInSpace σ_in pat (s.toFinset \ consumed_fs)
    have hmatch_spec := Mettapedia.Languages.ProcessCalculi.MORK.matchOneInSpace_mem
      σ_in pat (s.toFinset \ consumed_fs) a ha_in_sdiff σ_mid hcmatch
    -- Consumed correspondence: (a :: consumed_in).toFinset = consumed_fs ∪ {a}
    have hcons_fs : consumed_fs ∪ {a} = (a :: consumed_in).toFinset := by
      simp [List.toFinset_cons, hfs]
    -- hmem_go has (σ_mid, a).1 and (σ_mid, a).2; simplify
    simp only at hmem_go
    -- Goal: (σ_out, consumed_out.toFinset) ∈ matchPattern.go ...
    simp only [matchPattern.go]
    rw [List.mem_flatMap]
    exact ⟨(σ_mid, a), hmatch_spec,
           ih σ_mid (a :: consumed_in) (consumed_fs ∪ {a})
             σ_out consumed_out hcons_fs hmem_go⟩

/-! ### Forward soundness: cfireRule → fireRule -/

/-- Forward soundness: every space `s'` returned by the computable `cfireRule`
    has a spec-level counterpart `s'.toFinset` in `fireRule`.
    Requires `NodupSafe` on the template's sinks for the substitutions
    produced by matching. -/
theorem cfireRule_toFinset_sound (s : CSpace) (r : ExecRule) (s' : CSpace)
    (hs' : s' ∈ cfireRule s r)
    (hsafe : ∀ σ : Subst, NodupSafe s σ r.tmpl.sinks) :
    s'.toFinset ∈ fireRule s.toFinset r := by
  simp only [cfireRule, List.mem_map] at hs'
  obtain ⟨⟨σ, consumed⟩, hmatch, rfl⟩ := hs'
  simp only [fireRule, List.mem_map]
  have hmatch_spec := cmatchPattern_toFinset_sound [] s r.pat σ consumed hmatch
  exact ⟨(σ, consumed.toFinset), hmatch_spec,
         (capplySinks_toFinset_safe s σ r.tmpl (hsafe σ)).symm⟩

/-! ### Backward soundness: matchPattern → cmatchPattern -/

/-- Backward soundness: every spec-level `matchPattern` result has a
    computable counterpart in `cmatchPattern`.  Combined with the forward
    direction (`cmatchPattern_toFinset_sound`), this gives set-level
    equivalence: the reachable `(σ, consumed-as-set)` pairs are exactly
    the same.

    No `s.Nodup` hypothesis needed — the proof is about existence of a
    matching consumed list, not about order preservation. -/
theorem matchPattern_toFinset_complete (σ₀ : Subst) (s : CSpace) (p : Pattern)
    (σ : Subst) (consumed_fs : Finset Atom)
    (hmatch : (σ, consumed_fs) ∈ matchPattern σ₀ s.toFinset p) :
    ∃ consumed : List Atom, (σ, consumed) ∈ cmatchPattern σ₀ s p ∧
      consumed.toFinset = consumed_fs := by
  simp only [cmatchPattern, matchPattern] at *
  -- Generalize over go, relating Finset-consumed back to list-consumed
  suffices h : ∀ (pats : List Atom) (σ_in : Subst)
      (consumed_in : List Atom) (consumed_fs_in : Finset Atom)
      (σ_out : Subst) (consumed_fs_out : Finset Atom),
      consumed_fs_in = consumed_in.toFinset →
      (σ_out, consumed_fs_out) ∈ matchPattern.go s.toFinset pats σ_in consumed_fs_in →
      ∃ consumed_out : List Atom,
        (σ_out, consumed_out) ∈ cmatchPattern.go s pats σ_in consumed_in ∧
        consumed_out.toFinset = consumed_fs_out by
    exact h p.atoms σ₀ [] ∅ σ consumed_fs (by simp) hmatch
  intro pats
  induction pats with
  | nil =>
    intro σ_in consumed_in consumed_fs_in σ_out consumed_fs_out hfs hmem
    simp only [matchPattern.go, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨consumed_in, by simp [cmatchPattern.go], hfs.symm⟩
  | cons pat rest ih =>
    intro σ_in consumed_in consumed_fs_in σ_out consumed_fs_out hfs hmem
    simp only [matchPattern.go] at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨σ_mid, a⟩, hmatch_one, hmem_go⟩ := hmem
    -- Extract: a ∈ s.toFinset \ consumed_fs_in, matchAtom σ_in pat a = some σ_mid
    have ⟨ha_avail, hm⟩ := Mettapedia.Languages.ProcessCalculi.MORK.matchOneInSpace_spec
      σ_in pat (s.toFinset \ consumed_fs_in) σ_mid a hmatch_one
    rw [Finset.mem_sdiff] at ha_avail
    -- a ∈ s (via toFinset)
    have ha_in_s : a ∈ s := List.mem_toFinset.mp ha_avail.1
    -- a ∉ consumed_in (via toFinset bridge)
    have ha_not_consumed : a ∉ consumed_in := by
      intro h_in
      exact ha_avail.2 (hfs ▸ List.mem_toFinset.mpr h_in)
    -- So a appears in the computable available list
    have ha_filter : a ∈ s.filter (!consumed_in.contains ·) := by
      rw [List.mem_filter]
      exact ⟨ha_in_s, by simp [ha_not_consumed]⟩
    -- cmatchAtom = matchAtom, so match succeeds
    rw [← cmatchAtom_eq_matchAtom] at hm
    -- (σ_mid, a) is found by computable filterMap
    have hfound : (σ_mid, a) ∈ (s.filter (!consumed_in.contains ·)).filterMap
        (fun a' => (cmatchAtom σ_in pat a').map (·, a')) := by
      rw [List.mem_filterMap]
      exact ⟨a, ha_filter, by simp [hm]⟩
    -- Consumed correspondence for IH
    have hcons_fs : consumed_fs_in ∪ {a} = (a :: consumed_in).toFinset := by
      simp [List.toFinset_cons, hfs]
    -- Apply IH
    obtain ⟨consumed_out, hgo, hfs_out⟩ := ih σ_mid (a :: consumed_in)
      (consumed_fs_in ∪ {a}) σ_out consumed_fs_out hcons_fs hmem_go
    exact ⟨consumed_out, by
      simp only [cmatchPattern.go]
      rw [List.mem_flatMap]
      exact ⟨(σ_mid, a), hfound, hgo⟩, hfs_out⟩

/-! ### Backward soundness: fireRule → cfireRule -/

/-- Backward soundness: every spec-level `fireRule` result has a computable
    counterpart in `cfireRule`.  Combined with `cfireRule_toFinset_sound`,
    this gives set-level equivalence for rule firing. -/
theorem fireRule_toFinset_complete (s : CSpace) (r : ExecRule)
    (s'_fs : Space) (hs' : s'_fs ∈ fireRule s.toFinset r)
    (hsafe : ∀ σ : Subst, NodupSafe s σ r.tmpl.sinks) :
    ∃ s' : CSpace, s' ∈ cfireRule s r ∧ s'.toFinset = s'_fs := by
  simp only [fireRule, List.mem_map] at hs'
  obtain ⟨⟨σ, consumed_fs⟩, hmatch, rfl⟩ := hs'
  -- Backward soundness gives a computable match
  obtain ⟨consumed, hcmatch, _hfs⟩ :=
    matchPattern_toFinset_complete [] s r.pat σ consumed_fs hmatch
  -- capplySinks correspondence
  have hsinks := capplySinks_toFinset_safe s σ r.tmpl (hsafe σ)
  exact ⟨capplySinks s σ r.tmpl, by
    simp only [cfireRule, List.mem_map]
    exact ⟨(σ, consumed), hcmatch, rfl⟩, hsinks⟩

/-! ### Source-side correspondence: cmatchSourceFactor → matchSourceFactor -/

/-- Forward soundness: every `cmatchSourceFactor` result has a spec-level
    counterpart in `matchSourceFactor`.
    The `Nodup` hypothesis is needed for `neqConstraint` where `List.erase`
    removes only the first occurrence while `Finset.erase` removes entirely. -/
theorem cmatchSourceFactor_sound (σ : Subst) (s : CSpace) (src : SourceFactor)
    (hnd : s.Nodup)
    (σ' : Subst) (a : Atom)
    (h : (σ', a) ∈ cmatchSourceFactor σ s src) :
    (σ', a) ∈ matchSourceFactor σ s.toFinset src := by
  match src with
  | .btm pat =>
    simp only [cmatchSourceFactor, matchSourceFactor, matchOneInSpace] at h ⊢
    rw [List.mem_filterMap] at h ⊢
    obtain ⟨a', ha'_mem, ha'_match⟩ := h
    simp only [Option.map_eq_some_iff] at ha'_match
    obtain ⟨σ'', hcmatch, heq⟩ := ha'_match
    cases heq
    rw [cmatchAtom_eq_matchAtom] at hcmatch
    exact ⟨a, Finset.mem_toList.mpr (List.mem_toFinset.mpr ha'_mem),
           by simp [hcmatch]⟩
  | .eqConstraint pat witness =>
    simp only [cmatchSourceFactor, matchSourceFactor] at h ⊢
    split at h
    · rename_i hcontains
      have htarget_mem : applySubst σ pat ∈ s.toFinset :=
        List.mem_toFinset.mpr (List.mem_of_elem_eq_true hcontains)
      simp only [htarget_mem, ↓reduceIte]
      match hm : cmatchAtom σ witness (applySubst σ pat) with
      | some σ'' =>
        rw [hm] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [cmatchAtom_eq_matchAtom] at hm
        simp [hm]
      | none =>
        rw [hm] at h; simp at h
    · simp at h
  | .neqConstraint pat witness =>
    simp only [cmatchSourceFactor, matchSourceFactor, matchOneInSpace] at h ⊢
    rw [List.mem_filterMap] at h
    obtain ⟨a', ha'_mem, ha'_match⟩ := h
    simp only [Option.map_eq_some_iff] at ha'_match
    obtain ⟨σ'', hcmatch, heq⟩ := ha'_match
    cases heq
    rw [cmatchAtom_eq_matchAtom] at hcmatch
    rw [List.mem_filterMap]
    have ha_ne : a ≠ applySubst σ pat := by
      intro heq; rw [heq] at ha'_mem; exact hnd.not_mem_erase ha'_mem
    have ha_mem_s : a ∈ s := List.mem_of_mem_erase ha'_mem
    have ha_in_erase : a ∈ (s.toFinset.erase (applySubst σ pat)).toList := by
      rw [Finset.mem_toList, Finset.mem_erase]
      exact ⟨ha_ne, List.mem_toFinset.mpr ha_mem_s⟩
    exact ⟨a, ha_in_erase, by simp [hcmatch]⟩

/-- Forward soundness: cmatchSourceFactors results have spec-level
    counterparts in matchSourceFactors. -/
theorem cmatchSourceFactors_toFinset_sound (σ₀ : Subst) (s : CSpace)
    (hnd : s.Nodup)
    (factors : List SourceFactor) (σ : Subst) (consumed : List Atom)
    (hmatch : (σ, consumed) ∈ cmatchSourceFactors σ₀ s factors) :
    (σ, consumed.toFinset) ∈ matchSourceFactors σ₀ s.toFinset factors := by
  simp only [cmatchSourceFactors] at hmatch
  simp only [matchSourceFactors]
  suffices h : ∀ (fs : List SourceFactor) (σ_in : Subst)
      (consumed_in : List Atom) (consumed_fs : Finset Atom)
      (σ_out : Subst) (consumed_out : List Atom),
      consumed_fs = consumed_in.toFinset →
      (σ_out, consumed_out) ∈ cmatchSourceFactors.go s fs σ_in consumed_in →
      (σ_out, consumed_out.toFinset) ∈ matchSourceFactors.go s.toFinset fs σ_in consumed_fs by
    exact h factors σ₀ [] ∅ σ consumed (by simp) hmatch
  intro fs
  induction fs with
  | nil =>
    intro σ_in ci cf σ_out co hfs hmem
    simp only [cmatchSourceFactors.go, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    simp only [matchSourceFactors.go, List.mem_singleton, Prod.mk.injEq]
    exact ⟨trivial, hfs.symm⟩
  | cons src rest ih =>
    intro σ_in ci cf σ_out co hfs hmem
    simp only [cmatchSourceFactors.go] at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨σ_mid, a⟩, hmem_found, hmem_go⟩ := hmem
    -- cmatchSourceFactor on the filtered list
    have ha_in_avail := hmem_found
    -- The available list is s.filter (!ci.contains ·)
    -- We need: a ∈ matchSourceFactor σ_in (s.toFinset \ cf) src
    -- From cmatchSourceFactor σ_in (available) src
    -- available = s.filter (!ci.contains ·) whose toFinset = s.toFinset \ ci.toFinset = s.toFinset \ cf
    have hfilt_nd : (s.filter (!ci.contains ·)).Nodup := hnd.filter _
    have havail_sound : ∀ (σ' : Subst) (b : Atom),
        (σ', b) ∈ cmatchSourceFactor σ_in (s.filter (!ci.contains ·)) src →
        (σ', b) ∈ matchSourceFactor σ_in (s.toFinset \ cf) src := by
      intro σ' b hm
      have hsub := cmatchSourceFactor_sound σ_in (s.filter (!ci.contains ·)) src
        hfilt_nd σ' b hm
      have hfilt_eq : (s.filter (!ci.contains ·)).toFinset = s.toFinset \ cf := by
        subst hfs; ext x
        simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset,
          Finset.mem_sdiff, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
      rw [hfilt_eq] at hsub; exact hsub
    have hspec := havail_sound σ_mid a ha_in_avail
    simp only at hmem_go
    have hcons_fs : cf ∪ {a} = (a :: ci).toFinset := by
      simp [List.toFinset_cons, hfs]
    simp only [matchSourceFactors.go]
    rw [List.mem_flatMap]
    exact ⟨(σ_mid, a), hspec,
           ih σ_mid (a :: ci) (cf ∪ {a}) σ_out co hcons_fs hmem_go⟩

/-- Forward soundness: cmatchInputSpec results have spec-level counterparts. -/
theorem cmatchInputSpec_toFinset_sound (σ₀ : Subst) (s : CSpace)
    (hnd : s.Nodup)
    (input : InputSpec) (σ : Subst) (consumed : List Atom)
    (hmatch : (σ, consumed) ∈ cmatchInputSpec σ₀ s input) :
    (σ, consumed.toFinset) ∈ matchInputSpec σ₀ s.toFinset input := by
  match input with
  | .compat pat =>
    simp only [cmatchInputSpec, matchInputSpec] at hmatch ⊢
    exact cmatchPattern_toFinset_sound σ₀ s pat σ consumed hmatch
  | .explicit factors =>
    simp only [cmatchInputSpec, matchInputSpec] at hmatch ⊢
    exact cmatchSourceFactors_toFinset_sound σ₀ s hnd factors σ consumed hmatch

/-- Forward soundness: every space returned by `cfireSourceRule` has a
    spec-level counterpart in `fireSourceRule`.
    Requires `NodupSafe` for the substitutions produced by matching. -/
theorem cfireSourceRule_toFinset_sound (s : CSpace) (r : SourceExecRule) (s' : CSpace)
    (hnd : s.Nodup)
    (hs' : s' ∈ cfireSourceRule s r)
    (hsafe : ∀ σ : Subst, NodupSafe s σ r.tmpl.sinks) :
    s'.toFinset ∈ fireSourceRule s.toFinset r := by
  simp only [cfireSourceRule, List.mem_map, List.mem_filter] at hs'
  obtain ⟨⟨σ, consumed⟩, ⟨hmatch, hguards⟩, rfl⟩ := hs'
  simp only [fireSourceRule, List.mem_map, List.mem_filter]
  have hmatch_spec := cmatchInputSpec_toFinset_sound [] s hnd r.input σ consumed hmatch
  exact ⟨(σ, consumed.toFinset), ⟨hmatch_spec, hguards⟩,
         (capplySinks_toFinset_safe s σ r.tmpl (hsafe σ)).symm⟩

/-! ### Backward completeness: matchSourceFactor → cmatchSourceFactor -/

/-- Backward completeness: every `matchSourceFactor` result has a computable
    counterpart in `cmatchSourceFactor`. Combined with `cmatchSourceFactor_sound`,
    this gives set-level equivalence for source-factor matching. -/
theorem cmatchSourceFactor_complete (σ : Subst) (s : CSpace) (src : SourceFactor)
    (σ' : Subst) (a : Atom)
    (h : (σ', a) ∈ matchSourceFactor σ s.toFinset src) :
    (σ', a) ∈ cmatchSourceFactor σ s src := by
  match src with
  | .btm pat =>
    simp only [cmatchSourceFactor, matchSourceFactor, matchOneInSpace] at h ⊢
    rw [List.mem_filterMap] at h ⊢
    obtain ⟨a', ha'_mem, ha'_match⟩ := h
    have ha'_in_s : a' ∈ s := List.mem_toFinset.mp (Finset.mem_toList.mp ha'_mem)
    simp only [Option.map_eq_some_iff] at ha'_match
    obtain ⟨σ'', hmatch, heq⟩ := ha'_match
    cases heq
    rw [← cmatchAtom_eq_matchAtom] at hmatch
    exact ⟨a, ha'_in_s, by simp [hmatch]⟩
  | .eqConstraint pat witness =>
    simp only [cmatchSourceFactor, matchSourceFactor] at h ⊢
    split at h
    · rename_i htarget_mem
      have hcontains : s.contains (applySubst σ pat) = true := by
        rw [List.contains_eq_mem]; exact decide_eq_true (List.mem_toFinset.mp htarget_mem)
      rw [hcontains]
      match hm : matchAtom σ witness (applySubst σ pat) with
      | some σ'' =>
        rw [hm] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [← cmatchAtom_eq_matchAtom] at hm; simp [hm]
      | none =>
        rw [hm] at h; simp at h
    · simp at h
  | .neqConstraint pat witness =>
    simp only [cmatchSourceFactor, matchSourceFactor, matchOneInSpace] at h ⊢
    rw [List.mem_filterMap] at h ⊢
    obtain ⟨a', ha'_mem, ha'_match⟩ := h
    simp only [Option.map_eq_some_iff] at ha'_match
    obtain ⟨σ'', hmatch, heq⟩ := ha'_match
    cases heq
    rw [← cmatchAtom_eq_matchAtom] at hmatch
    -- a ∈ (s.toFinset.erase target).toList → a ∈ s.erase target
    have ha_fs : a ∈ s.toFinset.erase (applySubst σ pat) :=
      Finset.mem_toList.mp ha'_mem
    rw [Finset.mem_erase] at ha_fs
    have ha_in_s : a ∈ s := List.mem_toFinset.mp ha_fs.2
    have ha_ne : a ≠ applySubst σ pat := ha_fs.1
    have ha_in_erase : a ∈ s.erase (applySubst σ pat) :=
      (List.mem_erase_of_ne ha_ne).mpr ha_in_s
    exact ⟨a, ha_in_erase, by simp [hmatch]⟩

/-- Backward completeness for source factors: every `matchSourceFactors` result
    has a computable counterpart in `cmatchSourceFactors`. -/
theorem cmatchSourceFactors_toFinset_complete (σ₀ : Subst) (s : CSpace)
    (hnd : s.Nodup)
    (factors : List SourceFactor) (σ : Subst) (consumed_fs : Finset Atom)
    (hmatch : (σ, consumed_fs) ∈ matchSourceFactors σ₀ s.toFinset factors) :
    ∃ consumed : List Atom, (σ, consumed) ∈ cmatchSourceFactors σ₀ s factors ∧
      consumed.toFinset = consumed_fs := by
  simp only [cmatchSourceFactors, matchSourceFactors] at *
  suffices h : ∀ (fs : List SourceFactor) (σ_in : Subst)
      (consumed_in : List Atom) (consumed_fs_in : Finset Atom)
      (σ_out : Subst) (consumed_fs_out : Finset Atom),
      consumed_fs_in = consumed_in.toFinset →
      (σ_out, consumed_fs_out) ∈ matchSourceFactors.go s.toFinset fs σ_in consumed_fs_in →
      ∃ consumed_out : List Atom,
        (σ_out, consumed_out) ∈ cmatchSourceFactors.go s fs σ_in consumed_in ∧
        consumed_out.toFinset = consumed_fs_out by
    exact h factors σ₀ [] ∅ σ consumed_fs (by simp) hmatch
  intro fs
  induction fs with
  | nil =>
    intro σ_in ci cf σ_out cf_out hfs hmem
    simp only [matchSourceFactors.go, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨ci, by simp [cmatchSourceFactors.go], hfs.symm⟩
  | cons src rest ih =>
    intro σ_in ci cf σ_out cf_out hfs hmem
    simp only [matchSourceFactors.go] at hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨σ_mid, a⟩, hmatch_one, hmem_go⟩ := hmem
    -- a ∈ matchSourceFactor σ_in (s.toFinset \ cf) src
    -- Need: a ∈ cmatchSourceFactor σ_in (s.filter (!ci.contains ·)) src
    have hfilt_eq : (s.filter (!ci.contains ·)).toFinset = s.toFinset \ cf := by
      subst hfs; ext x
      simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset,
        Finset.mem_sdiff, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    have hfilt_nd : (s.filter (!ci.contains ·)).Nodup := hnd.filter _
    have hmatch_comp : (σ_mid, a) ∈ cmatchSourceFactor σ_in (s.filter (!ci.contains ·)) src := by
      have hsound := cmatchSourceFactor_complete σ_in (s.filter (!ci.contains ·)) src
        σ_mid a
      rw [hfilt_eq] at hsound
      exact hsound hmatch_one
    -- Consumed correspondence for IH
    have hcons_fs : cf ∪ {a} = (a :: ci).toFinset := by
      simp [List.toFinset_cons, hfs]
    obtain ⟨consumed_out, hgo, hfs_out⟩ := ih σ_mid (a :: ci)
      (cf ∪ {a}) σ_out cf_out hcons_fs hmem_go
    exact ⟨consumed_out, by
      simp only [cmatchSourceFactors.go]
      rw [List.mem_flatMap]
      exact ⟨(σ_mid, a), hmatch_comp, hgo⟩, hfs_out⟩

/-- Backward completeness for input spec: every `matchInputSpec` result
    has a computable counterpart in `cmatchInputSpec`. -/
theorem cmatchInputSpec_toFinset_complete (σ₀ : Subst) (s : CSpace)
    (hnd : s.Nodup)
    (input : InputSpec) (σ : Subst) (consumed_fs : Finset Atom)
    (hmatch : (σ, consumed_fs) ∈ matchInputSpec σ₀ s.toFinset input) :
    ∃ consumed : List Atom, (σ, consumed) ∈ cmatchInputSpec σ₀ s input ∧
      consumed.toFinset = consumed_fs := by
  match input with
  | .compat pat =>
    simp only [cmatchInputSpec, matchInputSpec] at hmatch ⊢
    exact matchPattern_toFinset_complete σ₀ s pat σ consumed_fs hmatch
  | .explicit factors =>
    simp only [cmatchInputSpec, matchInputSpec] at hmatch ⊢
    exact cmatchSourceFactors_toFinset_complete σ₀ s hnd factors σ consumed_fs hmatch

/-- Backward completeness for source rule firing: every spec-level
    `fireSourceRule` result has a computable counterpart in `cfireSourceRule`. -/
theorem fireSourceRule_toFinset_complete (s : CSpace) (r : SourceExecRule)
    (hnd : s.Nodup)
    (s'_fs : Space) (hs' : s'_fs ∈ fireSourceRule s.toFinset r)
    (hsafe : ∀ σ : Subst, NodupSafe s σ r.tmpl.sinks) :
    ∃ s' : CSpace, s' ∈ cfireSourceRule s r ∧ s'.toFinset = s'_fs := by
  simp only [fireSourceRule, List.mem_map, List.mem_filter] at hs'
  obtain ⟨⟨σ, consumed_fs⟩, ⟨hmatch, hguards⟩, rfl⟩ := hs'
  obtain ⟨consumed, hcmatch, _hfs⟩ :=
    cmatchInputSpec_toFinset_complete [] s hnd r.input σ consumed_fs hmatch
  refine ⟨capplySinks s σ r.tmpl, ?_, ?_⟩
  · simp only [cfireSourceRule, List.mem_map, List.mem_filter]
    exact ⟨(σ, consumed), ⟨hcmatch, hguards⟩, rfl⟩
  · exact (capplySinks_toFinset_safe s σ r.tmpl (hsafe σ))

end Correspondence

/-! ## Approach B: Equational proofs against `Finset Space`

Partial results using the existing noncomputable spec definitions.
End-to-end `fireRule` is blocked by `Finset.toList` (noncomputable).
-/

private def aStart  : Atom := .symbol "start"
private def aRed    : Atom := .symbol "color_apple_red"
private def aYellow : Atom := .symbol "color_banana_yellow"
private def aPurple : Atom := .symbol "color_grape_purple"

private def flatAddSimpleRule : ExecRule :=
  mkExecRule 0 "create-facts"
    (mkPattern [aStart])
    (mkTemplate [mkAdd aRed, mkAdd aYellow, mkAdd aPurple, mkRemove aStart])

/-- `matchAtom` on flat symbols reduces by `rfl`. -/
theorem matchAtom_symbol_rfl :
    matchAtom [] (.symbol "start") (.symbol "start") = some [] := rfl

/-- `matchAtom` variable binding reduces by `rfl`. -/
theorem matchAtom_var_rfl :
    matchAtom [] (.var "x") (.symbol "hello") = some [("x", .symbol "hello")] := rfl

/-- `applySinks` on the flat add-simple template (Finset version). -/
theorem applySinks_flat_template :
    applySinks {aStart} ([] : Subst) flatAddSimpleRule.tmpl =
      ({aRed, aYellow, aPurple} : Space) := by
  simp only [applySinks, flatAddSimpleRule, mkTemplate, mkExecRule,
             List.foldl, applySink, mkAdd, mkRemove,
             applySubst, isGroundAtom, ite_true,
             aStart, aRed, aYellow, aPurple]
  ext a
  simp [Finset.mem_singleton, Finset.mem_insert]

/-! ## Aggregator conformance

These tests verify `applyAggregator` matches MORK's `finalize()` semantics
from `sinks.rs`. They duplicate the canaries in `ThreePhaseExec.lean` but
live here as conformance artifacts. -/

/-- count aggregator: 3 sub-results → 3. -/
theorem conformance_aggregator_count_3 :
    applyAggregator .count [.symbol "a", .symbol "b", .symbol "c"] =
      some (.grounded (.int 3)) := rfl

/-- sum aggregator: 10 + 20 + 5 = 35. -/
theorem conformance_aggregator_sum_ints :
    applyAggregator .sum
      [.grounded (.int 10), .grounded (.int 20), .grounded (.int 5)] =
      some (.grounded (.int 35)) := rfl

/-- selectFirst picks head. -/
theorem conformance_aggregator_selectFirst :
    applyAggregator .selectFirst [.symbol "first", .symbol "second"] =
      some (.symbol "first") := rfl

/-! ## Head-sink conformance

The `head` sink performs idempotent add: if the atom is already present,
no duplicate is introduced. This matches MORK's Finset-model semantics. -/

private def head_rule : ExecRule :=
  mkExecRule 0 "head-test"
    (mkPattern [.expression [.symbol "trigger"]])
    (mkTemplate [mkHead (.symbol "result")])

/-- Head sink: first fire adds the atom. -/
theorem conformance_head_first_add :
    cfireRule [.expression [.symbol "trigger"]] head_rule =
      [[.expression [.symbol "trigger"], .symbol "result"]] := rfl

/-- Head sink: second fire is idempotent (atom already present). -/
theorem conformance_head_idempotent :
    cfireRule [.expression [.symbol "trigger"], .symbol "result"] head_rule =
      [[.expression [.symbol "trigger"], .symbol "result"]] := rfl

/-! ## Summary

| Feature | Conformance Tests | Verified Against |
|---|---|---|
| Expression matching | Tests 1-5, 7 | `mork run` |
| Variable binding (fresh) | Tests 3, 4, 5, 7, 8 | `mork run` |
| Equality constraint (`$x $x`) | Test 5 | `mork run` |
| Conjunctive match (shared var) | Test 4 | `mork run` |
| Nested expressions | Test 7 | `mork run` |
| Pattern mismatch (negative) | Tests 6, 9 | `mork run` |
| Multi-step fixpoint | Test 8 | `mork run` |
| Flat symbol matching | Approach B | spec-level |
| `applySinks` (Finset) | `applySinks_flat_template` | spec-level |
| Fold aggregators (count/sum/first) | 3 tests | `sinks.rs finalize()` |
| Head sink idempotence | 2 tests | MORK Finset model |
| `cmatchAtom = matchAtom` | 2 mutual thms | exact correspondence |
| `capplySink` ↔ `applySink` | 3 thms (add/head/remove) | via `toFinset` |
| `capplySinks` ↔ `applySinks` | 2 thms (no-remove + NodupSafe) | via `toFinset` |
| `cmatchPattern` soundness | 3 thms (consumed/subst/toFinset) | structural |
| `cfireRule` ↔ `fireRule` | 1 thm (forward soundness) | via `toFinset` |
| `matchAtom_extends` | 1 thm (Space.lean) | structural |
| `matchOneInSpace_mem` | 1 thm (Space.lean) | structural |
| `capplySinkStep` helpers | 4 defs/thms | factored sink step |

34 theorems (18 conformance + 16 correspondence), 0 sorries.
All `cfireRule`/`cfireToFixpoint` conformance theorems proved by `rfl` (kernel-checked).
Forward soundness chain: `cmatchPattern_toFinset_sound` + `capplySinks_toFinset_safe`
→ `cfireRule_toFinset_sound`: every computable firing result has a spec counterpart.
-/

/-! ## Source-aware conformance tests

These test the `cfireSourceRule` function against `mork run` ground truth.
Each fixture documents the `.mm2` source and expected output. -/

section SourceConformance

open Computable

/-! ### Test S1: BTM source (compat equivalence)

```mm2
(edge a b)
(exec (0 edge-to-path)
  (I (BTM (edge $x $y)))
  (O (+ (path $x $y)) (- (edge $x $y))))
```
Expected output: `(path a b)`
Verified: `mork run` produces `(path a b)`. -/

private def source_test1_rule : SourceExecRule :=
  ⟨0, "edge-to-path",
    .explicit [.btm (.expression [.symbol "edge", .var "x", .var "y"])],
    [],
    mkTemplate [mkAdd (.expression [.symbol "path", .var "x", .var "y"]),
                mkRemove (.expression [.symbol "edge", .var "x", .var "y"])]⟩

/-- BTM source: single factor matches the space. -/
theorem source_test1_btm :
    cfireSourceRule [.expression [.symbol "edge", .symbol "a", .symbol "b"]]
      source_test1_rule =
      [[.expression [.symbol "path", .symbol "a", .symbol "b"]]] := rfl

/-! ### Test S2: == source (equality constraint, success)

```mm2
(LHS (foo bar))
(RHS (foo bar))
(exec (0 eq-test)
  (I (BTM (LHS $p)) (== (RHS $p) $o))
  (O (+ (RES $p)) (- $o) (- (LHS $p))))
```
Expected output: `(RES (foo bar))`
Verified: `mork run` produces `(RES (foo bar))`. -/

private def source_test2_space : CSpace :=
  [.expression [.symbol "LHS", .expression [.symbol "foo", .symbol "bar"]],
   .expression [.symbol "RHS", .expression [.symbol "foo", .symbol "bar"]]]

private def source_test2_rule : SourceExecRule :=
  ⟨0, "eq-test",
    .explicit [
      .btm (.expression [.symbol "LHS", .var "p"]),
      .eqConstraint (.expression [.symbol "RHS", .var "p"]) (.var "o")],
    [],
    mkTemplate [
      mkAdd (.expression [.symbol "RES", .var "p"]),
      mkRemove (.var "o"),
      mkRemove (.expression [.symbol "LHS", .var "p"])]⟩

/-- == source: constraint succeeds, binds $o to (RHS (foo bar)). -/
theorem source_test2_eq :
    cfireSourceRule source_test2_space source_test2_rule =
      [[.expression [.symbol "RES",
          .expression [.symbol "foo", .symbol "bar"]]]] := rfl

/-! ### Test S3: == source (no match — RHS absent)

```mm2
(LHS key1)
(exec (0 eq-nm)
  (I (BTM (LHS $p)) (== (RHS $p) $o))
  (O (+ (found $o))))
```
Expected output: `(LHS key1)` (rule does not fire)
Verified: `mork run` produces `(LHS key1)`. -/

private def source_test3_space : CSpace :=
  [.expression [.symbol "LHS", .symbol "key1"]]

private def source_test3_rule : SourceExecRule :=
  ⟨0, "eq-nm",
    .explicit [
      .btm (.expression [.symbol "LHS", .var "p"]),
      .eqConstraint (.expression [.symbol "RHS", .var "p"]) (.var "o")],
    [],
    mkTemplate [mkAdd (.expression [.symbol "found", .var "o"])]⟩

/-- == source: no match (RHS absent), rule does not fire. -/
theorem source_test3_eq_nomatch :
    cfireSourceRule source_test3_space source_test3_rule = [] := rfl

/-! ### Test S4: Multi-BTM source (conjunctive, same as compat)

```mm2
(left a)
(right b)
(exec (0 join)
  (I (BTM (left $x)) (BTM (right $y)))
  (O (+ (pair $x $y)) (- (left $x)) (- (right $y))))
```
Expected output: `(pair a b)`
Verified: `mork run` produces `(pair a b)`. -/

private def source_test4_space : CSpace :=
  [.expression [.symbol "left", .symbol "a"],
   .expression [.symbol "right", .symbol "b"]]

private def source_test4_rule : SourceExecRule :=
  ⟨0, "join",
    .explicit [
      .btm (.expression [.symbol "left", .var "x"]),
      .btm (.expression [.symbol "right", .var "y"])],
    [],
    mkTemplate [
      mkAdd (.expression [.symbol "pair", .var "x", .var "y"]),
      mkRemove (.expression [.symbol "left", .var "x"]),
      mkRemove (.expression [.symbol "right", .var "y"])]⟩

/-- Multi-BTM source: conjunctive match over two atoms. -/
theorem source_test4_multi_btm :
    cfireSourceRule source_test4_space source_test4_rule =
      [[.expression [.symbol "pair", .symbol "a", .symbol "b"]]] := rfl

/-! ### Test S5: == with shared variable propagation

```mm2
(color car red)
(color house blue)
(wants car)
(exec (0 paint)
  (I (BTM (color $obj $c)) (== (wants $obj) $w))
  (O (+ (paint $obj $c)) (- $w) (- (color $obj $c))))
```
Expected output: `(color house blue)`, `(paint car red)`
Verified: `mork run` produces `(color house blue) (paint car red)`. -/

private def source_test5_space : CSpace :=
  [.expression [.symbol "color", .symbol "car", .symbol "red"],
   .expression [.symbol "color", .symbol "house", .symbol "blue"],
   .expression [.symbol "wants", .symbol "car"]]

private def source_test5_rule : SourceExecRule :=
  ⟨0, "paint",
    .explicit [
      .btm (.expression [.symbol "color", .var "obj", .var "c"]),
      .eqConstraint (.expression [.symbol "wants", .var "obj"]) (.var "w")],
    [],
    mkTemplate [
      mkAdd (.expression [.symbol "paint", .var "obj", .var "c"]),
      mkRemove (.var "w"),
      mkRemove (.expression [.symbol "color", .var "obj", .var "c"])]⟩

/-- == with shared variable: only `(color car red)` fires (wants car exists). -/
theorem source_test5_eq_shared :
    cfireSourceRule source_test5_space source_test5_rule =
      [[.expression [.symbol "color", .symbol "house", .symbol "blue"],
        .expression [.symbol "paint", .symbol "car", .symbol "red"]]] := rfl

/-! ### Test S6: != source (inequality constraint, basic)

```mm2
(item a)
(item b)
(exclude a)
(exec (0 neq-test)
  (I (BTM (exclude $x)) (!= (item $x) $other))
  (O (+ (keep $other)) (- $other) (- (exclude $x))))
```
Expected: binds `x=a`, removes `(item a)` from candidates, matches `(item b)` as `$other`.
Output: `(keep (item b))`.
Verified: mirrors Rust `CmpSource` with `cmp=1`. -/

private def source_test6_space : CSpace :=
  [.expression [.symbol "item", .symbol "a"],
   .expression [.symbol "item", .symbol "b"],
   .expression [.symbol "exclude", .symbol "a"]]

private def source_test6_rule : SourceExecRule :=
  ⟨0, "neq-test",
    .explicit [
      .btm (.expression [.symbol "exclude", .var "x"]),
      .neqConstraint (.expression [.symbol "item", .var "x"])
                     (.var "other")],
    [],
    mkTemplate [
      mkAdd (.expression [.symbol "keep", .var "other"]),
      mkRemove (.var "other"),
      mkRemove (.expression [.symbol "exclude", .var "x"])]⟩

/-- != source: exclude `(item a)`, match `(item b)` as `$other`. -/
theorem source_test6_neq :
    cfireSourceRule source_test6_space source_test6_rule =
      [[.expression [.symbol "item", .symbol "a"],
        .expression [.symbol "keep",
          .expression [.symbol "item", .symbol "b"]]]] := rfl

/-! ### Test S7: != source (no remaining matches)

```mm2
(item a)
(exclude a)
(exec (0 neq-empty)
  (I (BTM (exclude $x)) (!= (item $x) (item $y)))
  (O (+ (found $y))))
```
Expected: binds `x=a`, removes `(item a)`, no remaining `(item ?)` atoms → no match. -/

private def source_test7_space : CSpace :=
  [.expression [.symbol "item", .symbol "a"],
   .expression [.symbol "exclude", .symbol "a"]]

private def source_test7_rule : SourceExecRule :=
  ⟨0, "neq-empty",
    .explicit [
      .btm (.expression [.symbol "exclude", .var "x"]),
      .neqConstraint (.expression [.symbol "item", .var "x"])
                     (.expression [.symbol "item", .var "y"])],
    [],
    mkTemplate [mkAdd (.expression [.symbol "found", .var "y"])]⟩

/-- != source: after removing `(item a)`, no `(item ?)` remains → no fire. -/
theorem source_test7_neq_nomatch :
    cfireSourceRule source_test7_space source_test7_rule = [] := rfl

/-! ### Test S8: != source (multiple remaining matches)

```mm2
(item a)
(item b)
(item c)
(exclude a)
(exec (0 neq-multi)
  (I (BTM (exclude $x)) (!= (item $x) (item $y)))
  (O (+ (found $y)) (- (item $y))))
```
Expected: binds `x=a`, removes `(item a)`, matches `(item b)` AND `(item c)`. -/

private def source_test8_space : CSpace :=
  [.expression [.symbol "item", .symbol "a"],
   .expression [.symbol "item", .symbol "b"],
   .expression [.symbol "item", .symbol "c"],
   .expression [.symbol "exclude", .symbol "a"]]

private def source_test8_rule : SourceExecRule :=
  ⟨0, "neq-multi",
    .explicit [
      .btm (.expression [.symbol "exclude", .var "x"]),
      .neqConstraint (.expression [.symbol "item", .var "x"])
                     (.expression [.symbol "item", .var "y"])],
    [],
    mkTemplate [
      mkAdd (.expression [.symbol "found", .var "y"]),
      mkRemove (.expression [.symbol "item", .var "y"])]⟩

/-- != source: two non-excluded matches produce two results.
    Uses `decide` because the 4-atom space + multi-match exceeds the kernel's
    definitional reduction budget for `rfl`. -/
theorem source_test8_neq_multi :
    cfireSourceRule source_test8_space source_test8_rule =
      [[.expression [.symbol "item", .symbol "a"],
        .expression [.symbol "item", .symbol "c"],
        .expression [.symbol "exclude", .symbol "a"],
        .expression [.symbol "found", .symbol "b"]],
       [.expression [.symbol "item", .symbol "a"],
        .expression [.symbol "item", .symbol "b"],
        .expression [.symbol "exclude", .symbol "a"],
        .expression [.symbol "found", .symbol "c"]]] := by decide

end SourceConformance

/-! ### Compat equivalence theorem

For compat-mode rules, `cfireSourceRule` agrees with `cfireRule`. -/

/-- `cfireSourceRule` on a compat-mode rule is `cfireRule`. -/
theorem cfireSourceRule_compat_eq (s : CSpace) (r : ExecRule) :
    Computable.cfireSourceRule s r.toSourceRule = Computable.cfireRule s r := by
  simp [Computable.cfireSourceRule, Computable.cfireRule,
        Computable.cmatchInputSpec, ExecRule.toSourceRule,
        matchSourceGuards, List.all_nil, List.filter_true]

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance
