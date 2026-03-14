import Mettapedia.Languages.MeTTa.PeTTa.StageIndex
import Mettapedia.Languages.MeTTa.PeTTa.ContractCatalog
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract

/-!
# PeTTa OSLF Package — Per-Stage Semantic Bundles

Each `PeTTaStage` carries a coherent package of
`(lang, relEnv, execContracts, scopeContracts)`. All 4 stages share the
**same** `LanguageDef` (`pettaSpaceToLangDef s`). Stages differ in:
- **`relEnv`** — empty → query-aware
- **`execEntries`** — slices of `ContractCatalog.lean` entries per stage
- **`scopeEntries`** — slices of `ScopeContract.lean` entries per stage

## Stage Layout

| Stage | relEnv | execEntries | scopeEntries |
|-------|--------|-------------|--------------|
| `sourceCore` | `empty` | `[]` | `[]` |
| `queryCore` | `pettaQueryRelEnv s` | spaceMatch, getAtoms, premise | matchScope |
| `statefulCore` | `pettaQueryRelEnv s` | + addAtom*, removeAtom*, payloads, let/chain/progn, collapse/min/max | + let, chain, letStar, case, addAtom/removeAtom scope |
| `boundaryAware` | `pettaQueryRelEnv s` | + mm2Intrinsics, comparisons, reflection, println!, test, quote, get-type, is-var, float, tuple | + lambda |

## References

- Plan: `cosmic-scribbling-thacker.md` Step 3
- `Mettapedia.Languages.MeTTa.PeTTa.StageIndex` — `PeTTaStage`
- `Mettapedia.Languages.MeTTa.PeTTa.ContractCatalog` — execution contract entries
- `Mettapedia.Languages.MeTTa.PeTTa.ScopeContract` — scope contract entries
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings matchPattern applyBindings)
open Mettapedia.Languages.MeTTa.ExecutionContract
open Mettapedia.Languages.MeTTa.ScopeContract
open Mettapedia.Languages.MeTTa.PeTTa.StageIndex
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
open Mettapedia.Languages.MeTTa.PeTTa.ScopeContract

/-! ## §1 Package Structure -/

/-- A per-stage semantic package for PeTTa.

    All stages share the same `LanguageDef` (user rewrite rules). Stages differ
    in the semantic enrichment carried alongside:
    - `relEnv`: which premise relations are available
    - `execEntries`: which execution contracts are active
    - `scopeEntries`: which scope contracts are active -/
structure PeTTaOSLFPackage where
  lang : LanguageDef
  relEnv : RelationEnv
  execEntries : List ExecutionContractEntry
  scopeEntries : List ScopeContractEntry

/-! ## §2 Query Relation Environment

The `queryCore` stage (and above) augments `RelationEnv.empty` with a
`spaceMatch` relation derived from the PeTTa space's stored atoms.

For each stored atom `a`, the `spaceMatch` relation produces tuples
`[pattern, template, result]` where `result = applyBindings bs template`
for bindings `bs` from matching `pattern` against `a`. -/

/-- Compute all spaceMatch result rows from a list of stored atoms.

    For each stored atom, tries matching `pat` against it. For every
    successful match with bindings `bs`, produces the row
    `[applyBindings bs pat, applyBindings bs tmpl, applyBindings bs tmpl]`.

    Returns ALL matches (not just the first), since spaceMatch is
    nondeterministic. The 3rd element is the result (template with
    matched bindings applied). The caller's `matchArgs` will unify
    this against the `$out` fvar to produce the output binding.

    This helper is factored out so both the semantic layer and runtime
    lowering can reference the same row-generation logic. -/
def spaceMatchRows (atoms : List Pattern) (pat tmpl : Pattern) :
    List (List Pattern) :=
  atoms.flatMap fun atom =>
    (matchPattern pat atom).map fun bs =>
      [applyBindings bs pat, applyBindings bs tmpl, applyBindings bs tmpl]

/-- Query-aware relation environment for a PeTTa space.

    Adds `spaceMatch(pattern, template, result)` 3-arg tuples derived from
    `s.storedAtoms` to the empty environment.

    This is the relEnv that enables premise-aware query rules to fire in
    the OSLF type system. The 3-arg shape matches
    `spaceMatchRelationPremiseContract` (arity 3, argRoles =
    `[.pattern, .template, .resultVar]`).

    The `relationQueryStep` in Engine.lean substitutes bindings into the
    3 args before calling `relEnv.tuples`. Typically the first two args
    are ground and the third is a free variable (`$out`). `matchArgs`
    then unifies each returned row against the arg patterns, binding
    `$out` to the result. -/
def pettaQueryRelEnv (s : PeTTaSpace) : RelationEnv where
  tuples := fun name args =>
    if name = "spaceMatch" then
      match args with
      | [pat, tmpl, _] => spaceMatchRows s.storedAtoms pat tmpl
      | _ => []
    else RelationEnv.empty.tuples name args

/-- The query relation environment agrees with `empty` on all non-`spaceMatch`
    relation names. -/
theorem pettaQueryRelEnv_non_spaceMatch (s : PeTTaSpace) (name : String)
    (args : List Pattern) (h : name ≠ "spaceMatch") :
    (pettaQueryRelEnv s).tuples name args = RelationEnv.empty.tuples name args := by
  simp [pettaQueryRelEnv, h]

/-- Every row in `spaceMatchRows` has length 3. -/
theorem spaceMatchRows_row_length {atoms : List Pattern} {pat tmpl : Pattern}
    {row : List Pattern} (h : row ∈ spaceMatchRows atoms pat tmpl) :
    row.length = 3 := by
  simp [spaceMatchRows, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

/-- Every row in `spaceMatchRows` comes from a successful match. -/
theorem spaceMatchRows_sound {atoms : List Pattern} {pat tmpl : Pattern}
    {row : List Pattern} (h : row ∈ spaceMatchRows atoms pat tmpl) :
    ∃ atom ∈ atoms, ∃ bs ∈ matchPattern pat atom,
      row = [applyBindings bs pat, applyBindings bs tmpl, applyBindings bs tmpl] := by
  simp [spaceMatchRows, List.mem_flatMap, List.mem_map] at h
  obtain ⟨atom, hatom, bs, hbs, rfl⟩ := h
  exact ⟨atom, hatom, bs, hbs, rfl⟩

/-- Every successful match against a stored atom produces a row. -/
theorem spaceMatchRows_complete {atoms : List Pattern} {pat tmpl : Pattern}
    {atom : Pattern} {bs : Bindings}
    (hatom : atom ∈ atoms) (hbs : bs ∈ matchPattern pat atom) :
    [applyBindings bs pat, applyBindings bs tmpl, applyBindings bs tmpl] ∈
      spaceMatchRows atoms pat tmpl := by
  simp [spaceMatchRows, List.mem_flatMap, List.mem_map]
  exact ⟨atom, hatom, bs, hbs, rfl, rfl⟩

/-! ## §3 Stage-Tagged Entry Classification

Each contract entry is tagged with its minimum stage via `execStage` / `scopeStage`.
Filtering the full artifact by `≤ stage` gives the correct per-stage slice.
This replaces hand-written per-stage lists and ensures stage monotonicity by
construction. -/

/-- Minimum stage at which an execution contract entry becomes active.
    Classification by constructor variant (exhaustive, no string matching). -/
def execStage : ExecutionContractEntry → PeTTaStage
  | .lookupQuery _        => .queryCore
  | .relationPremise _    => .queryCore      -- semantically query-level (reads space)
  | .spaceEffect _        => .statefulCore
  | .spaceEffectPayload _ => .statefulCore
  | .controlBuiltin _     => .statefulCore
  | .aggregationBuiltin _ => .statefulCore
  | .intrinsicBuiltin _   => .boundaryAware
  | .groundedBuiltin _    => .boundaryAware

/-- Minimum stage at which a scope contract entry becomes active. -/
def scopeStage (e : ScopeContractEntry) : PeTTaStage :=
  match e.head with
  | "match" => .queryCore
  | "let" | "chain" | "let*" | "case" => .statefulCore
  | "add-atom" | "add-atom!" | "remove-atom" | "remove-atom!" => .statefulCore
  | _ => .boundaryAware  -- lambda

/-- Stage-filtered execution entries from the canonical artifact. -/
def stageExecEntries (st : PeTTaStage) : List ExecutionContractEntry :=
  pettaExecutionContractArtifact.entries.filter (fun e => decide (execStage e ≤ st))

/-- Stage-filtered scope entries from the canonical artifact. -/
def stageScopeEntries (st : PeTTaStage) : List ScopeContractEntry :=
  pettaScopeContractArtifact.entries.filter (fun e => decide (scopeStage e ≤ st))

/-- Every execution entry has `execStage e ≤ .boundaryAware`. -/
theorem execStage_le_boundaryAware (e : ExecutionContractEntry) :
    execStage e ≤ .boundaryAware := by
  cases e <;> simp only [execStage] <;> decide

/-- Every scope entry has `scopeStage e ≤ .boundaryAware`. -/
theorem scopeStage_le_boundaryAware (e : ScopeContractEntry) :
    scopeStage e ≤ .boundaryAware := by
  simp only [scopeStage]
  split <;> decide

/-- Execution entries grow monotonically with stage. -/
theorem stageExecEntries_mono {s₁ s₂ : PeTTaStage} (h : s₁ ≤ s₂) :
    ∀ e ∈ stageExecEntries s₁, e ∈ stageExecEntries s₂ := by
  intro e he
  simp only [stageExecEntries, List.mem_filter, decide_eq_true_eq] at he ⊢
  exact ⟨he.1, Nat.le_trans he.2 h⟩

/-- Scope entries grow monotonically with stage. -/
theorem stageScopeEntries_mono {s₁ s₂ : PeTTaStage} (h : s₁ ≤ s₂) :
    ∀ e ∈ stageScopeEntries s₁, e ∈ stageScopeEntries s₂ := by
  intro e he
  simp only [stageScopeEntries, List.mem_filter, decide_eq_true_eq] at he ⊢
  exact ⟨he.1, Nat.le_trans he.2 h⟩

/-! ## §4 Package Constructors -/

/-- Build the per-stage OSLF package for a given PeTTa space and stage. -/
def pettaPkg (stage : PeTTaStage) (s : PeTTaSpace) : PeTTaOSLFPackage :=
  { lang := pettaSpaceToLangDef s
  , relEnv := match stage with
      | .sourceCore => RelationEnv.empty
      | _ => pettaQueryRelEnv s
  , execEntries := stageExecEntries stage
  , scopeEntries := stageScopeEntries stage
  }

/-! ## §5 Package Properties -/

/-- All stages share the same `LanguageDef`. -/
theorem pettaPkg_lang_constant (s : PeTTaSpace) (stage : PeTTaStage) :
    (pettaPkg stage s).lang = pettaSpaceToLangDef s := by
  simp [pettaPkg]

/-- The `sourceCore` stage uses empty `relEnv`. -/
theorem pettaPkg_sourceCore_relEnv (s : PeTTaSpace) :
    (pettaPkg .sourceCore s).relEnv = RelationEnv.empty := rfl

/-- The `boundaryAware` stage's execution entries match the existing
    `pettaExecutionContractArtifact`. -/
theorem pettaPkg_boundaryAware_exec_eq_artifact (s : PeTTaSpace) :
    (pettaPkg .boundaryAware s).execEntries =
    pettaExecutionContractArtifact.entries := by
  simp only [pettaPkg, stageExecEntries]
  rw [List.filter_eq_self]
  intro e _
  simp only [decide_eq_true_eq]
  exact execStage_le_boundaryAware e

/-- The `boundaryAware` stage's scope entries match the existing
    `pettaScopeContractArtifact`. -/
theorem pettaPkg_boundaryAware_scope_eq_artifact (s : PeTTaSpace) :
    (pettaPkg .boundaryAware s).scopeEntries =
    pettaScopeContractArtifact.entries := by
  simp only [pettaPkg, stageScopeEntries]
  rw [List.filter_eq_self]
  intro e _
  simp only [decide_eq_true_eq]
  exact scopeStage_le_boundaryAware e

end Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage
