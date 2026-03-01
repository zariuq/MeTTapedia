import Mettapedia.Logic.LP.Unification
import Mettapedia.Logic.LP.SLD
import Mettapedia.Logic.LP.SLDCompute

/-!
# Logic Programming Kernel: All-Solutions SLD Resolution

Fuel-bounded DFS SLD resolution that collects **all** answer substitutions
(rather than stopping at the first). This models Prolog's `findall/3` or
MeTTa's `collapse` operator.

## Design

- `sldSearchAll prog fuel goals` — DFS over the SLD tree, returning every
  computed answer substitution reachable within the fuel bound.
- `sldSearchAll_yields_SLDTree` — every answer comes from an `SLDTree` witness,
  providing the bridge to the least Herbrand model.
- `sldSearchAll_sound` — corollary: every answer is semantically sound.
- `sldSearch_mem_sldSearchAll` — the first-answer search is subsumed:
  if `sldSearch` succeeds, that answer appears in `sldSearchAll`.

## Relationship to sldSearch

`sldSearch` uses `findSome?` (stops at first success).
`sldSearchAll` uses `flatMap` (collects all successes).
When `sldSearch prog fuel goals = some θ`,
then `θ ∈ sldSearchAll prog fuel goals`.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed., Ch. 3
- Sterling & Shapiro, *The Art of Prolog*, Ch. 5 (Prolog's findall)
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: All-solutions SLD search -/

/-- Fuel-bounded DFS SLD resolution returning all answer substitutions.

    Mirrors `sldSearch` exactly but uses `flatMap` instead of `findSome?`,
    collecting every successful branch instead of stopping at the first.

    - `fuel = 0`: fuel exhausted, return empty list
    - `goals = []`: refutation found, return singleton `[id]`
    - `goals = a :: rest`: try every clause; for each successful unification,
      recurse and map results by right-composing the unifier. -/
def sldSearchAll {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) : ℕ → List (Atom σ) → List (Subst σ)
  | 0, _ => []
  | _, [] => [Subst.id σ]
  | fuel + 1, a :: goals =>
    prog.flatMap fun c =>
      match unifyAtoms a c.head fuel with
      | none => []
      | some θ =>
        (sldSearchAll prog fuel (θ.applyAtoms (c.body ++ goals))).map (· ∘ₛ θ)

/-- All-answers single-query convenience wrapper. -/
def sldQueryAll {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (a : Atom σ) (fuel : ℕ := 1000) : List (Subst σ) :=
  sldSearchAll prog fuel [a]

/-! ## Section 2: Soundness bridge -/

/-- **Bridge theorem**: every answer in `sldSearchAll` has a corresponding `SLDTree`.

    This connects the all-solutions DFS to the abstract SLD specification,
    enabling `SLDTree_sound` (and hence least Herbrand model membership) to be
    transferred to `sldSearchAll`. -/
theorem sldSearchAll_yields_SLDTree {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ)) (θ : Subst σ)
    (h : θ ∈ sldSearchAll prog fuel goals) :
    SLDTree prog goals θ := by
  induction fuel generalizing goals θ with
  | zero => simp [sldSearchAll] at h
  | succ n ih =>
    match goals with
    | [] =>
      simp only [sldSearchAll, List.mem_singleton] at h
      subst h; exact SLDTree.nil
    | a :: rest =>
      simp only [sldSearchAll, List.mem_flatMap] at h
      obtain ⟨c, hc, hmem⟩ := h
      -- Extract the unifier from the match on `unifyAtoms`
      cases hunif : unifyAtoms a c.head n with
      | none =>
        -- In the none branch, the map produces [], so hmem : θ ∈ []
        simp only [hunif] at hmem
        exact absurd hmem (by simp)
      | some θu =>
        simp only [hunif, List.mem_map] at hmem
        obtain ⟨θ_rec, hrec, heq⟩ := hmem
        subst heq
        exact SLDTree.cons a rest c θu θ_rec hc
          (unifyAtoms_sound a c.head n θu hunif)
          (ih _ _ hrec)

/-- **Soundness of all-solutions SLD**: every answer in `sldSearchAll` is in
    the least Herbrand model (for every goal atom, under every further grounding). -/
theorem sldSearchAll_sound {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (fuel : ℕ) (goals : List (Atom σ)) (θ : Subst σ)
    (h : θ ∈ sldSearchAll kb.prog fuel goals) :
    ∀ g : Grounding σ, ∀ a ∈ goals,
      (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb :=
  SLDTree_sound kb goals θ (sldSearchAll_yields_SLDTree kb.prog fuel goals θ h)

/-- Soundness for single-atom all-solutions queries. -/
theorem sldQueryAll_sound {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (a : Atom σ) (fuel : ℕ) (θ : Subst σ)
    (h : θ ∈ sldQueryAll kb.prog a fuel) (g : Grounding σ) :
    (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb :=
  sldSearchAll_sound kb fuel [a] θ h g a (List.mem_cons_self ..)

/-! ## Section 3: Subsumption of sldSearch -/

/-- **sldSearch is subsumed by sldSearchAll**: if `sldSearch` returns a first
    answer `θ`, then `θ` appears in `sldSearchAll`.

    This means all properties proven via `sldSearch_sound` also hold for
    the element found first by the single-answer search. -/
theorem sldSearch_mem_sldSearchAll {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ)) (θ : Subst σ)
    (h : sldSearch prog fuel goals = some θ) :
    θ ∈ sldSearchAll prog fuel goals := by
  induction fuel generalizing goals θ with
  | zero => simp [sldSearch] at h
  | succ n ih =>
    match goals with
    | [] =>
      simp only [sldSearch] at h
      have : θ = Subst.id σ := Option.some.inj h.symm
      subst this
      simp [sldSearchAll]
    | a :: rest =>
      simp only [sldSearch] at h
      -- Extract the successful clause from findSome?
      obtain ⟨c, hc, hfc⟩ := mem_of_findSome?_some h
      obtain ⟨θ_unif, θ_rec, hunify, hrec, heq⟩ := extract_clause_result hfc
      subst heq
      -- Show the same answer is in sldSearchAll
      simp only [sldSearchAll, List.mem_flatMap]
      refine ⟨c, hc, ?_⟩
      simp only [hunify, List.mem_map]
      exact ⟨θ_rec, ih _ _ hrec, rfl⟩

/-- **Corollary**: `sldQueryAll` subsumes `sldQuery`. -/
theorem sldQuery_mem_sldQueryAll {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (a : Atom σ) (fuel : ℕ) (θ : Subst σ)
    (h : sldQuery prog a fuel = some θ) :
    θ ∈ sldQueryAll prog a fuel :=
  sldSearch_mem_sldSearchAll prog fuel [a] θ h

/-! ## Section 4: Witness-based completeness -/

/-- **Completeness from SLDWitness**: if a witness tree exists at fuel `f`,
    then the corresponding answer appears in `sldSearchAll prog f goals`.

    This extends `sldSearch_complete_bounded` to the all-solutions setting:
    every witnessable answer is captured. -/
theorem sldSearchAll_complete_of_witness {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ))
    (hw : SLDWitness prog fuel goals) :
    ∃ θ ∈ sldSearchAll prog fuel goals, SLDTree prog goals θ := by
  -- Extract the sldSearch answer (which by sldSearch_complete_bounded exists)
  obtain ⟨θ, hθ⟩ := sldSearch_complete_bounded prog fuel goals hw
  exact ⟨θ, sldSearch_mem_sldSearchAll prog fuel goals θ hθ,
         sldSearch_yields_SLDTree prog fuel goals θ hθ⟩

/-! ## Summary

**0 sorries. 0 axioms.**

### All-solutions search
- `sldSearchAll`: DFS collecting all answer substitutions (uses `flatMap`)
- `sldQueryAll`: single-atom convenience wrapper

### Soundness
- `sldSearchAll_yields_SLDTree`: every answer → `SLDTree` witness
- `sldSearchAll_sound`: every answer → in least Herbrand model
- `sldQueryAll_sound`: single-atom variant

### Subsumption
- `sldSearch_mem_sldSearchAll`: first-answer ⊆ all-answers (backward compat)
- `sldQuery_mem_sldQueryAll`: single-query variant

### Completeness
- `sldSearchAll_complete_of_witness`: witness tree → answer in `sldSearchAll`
-/

end Mettapedia.Logic.LP
