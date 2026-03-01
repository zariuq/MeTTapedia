import Mettapedia.Logic.LP.Unification
import Mettapedia.Logic.LP.SLD
import Mettapedia.Logic.LP.FunctionFreeEvaluation

/-!
# Logic Programming Kernel: Computational SLD Resolution

Fuel-bounded DFS SLD resolution using `unifyAtoms`, with a soundness
bridge to `SLDTree` (and thereby to the least Herbrand model).

## Design

- `sldSearch prog fuel goals` — DFS search over the SLD tree using
  `unifyAtoms` for unification, leftmost selection, clauses tried in order.
- `sldSearch_yields_SLDTree` — if `sldSearch` succeeds, an `SLDTree` witness
  exists. This bridges the computational algorithm to the specification.
- `sldSearch_sound` — corollary: `sldSearch` results are in the least model.

## References

- Lloyd, *Foundations of Logic Programming*, Ch. 3 (SLD resolution)
- Sterling & Shapiro, *The Art of Prolog*, Ch. 5 (search strategy)
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Computational SLD search -/

/-- Fuel-bounded DFS SLD resolution.

    Tries each clause in program order against the leftmost goal.
    Returns the composed answer substitution on success, `none` on
    failure or fuel exhaustion.

    This implements Prolog's default search strategy:
    leftmost selection × top-down clause order × depth-first. -/
def sldSearch {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) : ℕ → List (Atom σ) → Option (Subst σ)
  | 0, _ => none
  | _, [] => some (Subst.id σ)
  | fuel + 1, a :: goals =>
    prog.findSome? fun c =>
      match unifyAtoms a c.head fuel with
      | none => none
      | some θ =>
        match sldSearch prog fuel (θ.applyAtoms (c.body ++ goals)) with
        | none => none
        | some θ' => some (θ' ∘ₛ θ)

/-- Single-query convenience wrapper. -/
def sldQuery {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (a : Atom σ) (fuel : ℕ := 1000) : Option (Subst σ) :=
  sldSearch prog fuel [a]

/-! ## Section 2: Proof helpers -/

/-- Extract element membership from `findSome?` success. -/
theorem mem_of_findSome?_some {α β : Type*}
    {f : α → Option β} {l : List α} {b : β}
    (h : l.findSome? f = some b) : ∃ a ∈ l, f a = some b := by
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨l₁, a, _, heq, hfa, _⟩ := h
  exact ⟨a, heq ▸ List.mem_append_right l₁ (List.mem_cons_self ..), hfa⟩

/-- Extract the unifier and recursive result from a successful clause try. -/
theorem extract_clause_result {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    {a : Atom σ} {c : Clause σ} {goals : List (Atom σ)}
    {prog : Program σ} {fuel : ℕ} {θ_result : Subst σ}
    (h : (match unifyAtoms a c.head fuel with
      | none => none
      | some θ =>
        match sldSearch prog fuel (θ.applyAtoms (c.body ++ goals)) with
        | none => none
        | some θ' => some (θ' ∘ₛ θ)) = some θ_result) :
    ∃ θ θ', unifyAtoms a c.head fuel = some θ ∧
            sldSearch prog fuel (θ.applyAtoms (c.body ++ goals)) = some θ' ∧
            θ_result = θ' ∘ₛ θ := by
  split at h
  · contradiction
  · rename_i θ hθ
    split at h
    · contradiction
    · rename_i θ' hθ'
      simp at h
      exact ⟨θ, θ', hθ, hθ', h.symm⟩

/-! ## Section 3: Soundness bridge -/

/-- **Bridge theorem**: if `sldSearch` succeeds, there is an `SLDTree` witness.

    This connects the computational DFS search to the abstract specification,
    enabling all `SLDTree` properties (particularly soundness w.r.t. the
    least Herbrand model) to be transferred to `sldSearch`. -/
theorem sldSearch_yields_SLDTree {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ)) (θ : Subst σ)
    (h : sldSearch prog fuel goals = some θ) :
    SLDTree prog goals θ := by
  induction fuel generalizing goals θ with
  | zero => simp [sldSearch] at h
  | succ n ih =>
    match goals with
    | [] =>
      simp [sldSearch] at h; subst h; exact SLDTree.nil
    | a :: rest =>
      simp only [sldSearch] at h
      obtain ⟨c, hc, hfc⟩ := mem_of_findSome?_some h
      obtain ⟨θ_unif, θ_rec, hunify, hrec, heq⟩ := extract_clause_result hfc
      subst heq
      exact SLDTree.cons a rest c θ_unif θ_rec hc
        (unifyAtoms_sound a c.head n θ_unif hunify) (ih _ _ hrec)

/-- **Soundness of computational SLD**: if `sldSearch` succeeds, every goal atom
    (grounded via the computed answer and any further grounding) is in the
    least Herbrand model. -/
theorem sldSearch_sound {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (fuel : ℕ) (goals : List (Atom σ)) (θ : Subst σ)
    (h : sldSearch kb.prog fuel goals = some θ) :
    ∀ g : Grounding σ, ∀ a ∈ goals,
      (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb :=
  SLDTree_sound kb goals θ (sldSearch_yields_SLDTree kb.prog fuel goals θ h)

/-- Soundness for single-atom queries via `sldQuery`. -/
theorem sldQuery_sound {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (a : Atom σ) (fuel : ℕ) (θ : Subst σ)
    (h : sldQuery kb.prog a fuel = some θ) (g : Grounding σ) :
    (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb :=
  sldSearch_sound kb fuel [a] θ h g a (List.mem_cons_self ..)

/-! ## Section 4: Bounded operational completeness -/

/-- A constructive witness that a successful SLD branch exists within a given fuel.

This relation is declarative (inductive) and independent from the implementation
of `findSome?`: it only records that some clause in the program can be used at each
step, together with a successful recursive witness for the resulting goals. -/
inductive SLDWitness {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) : ℕ → List (Atom σ) → Prop where
  | nil (fuel : ℕ) : SLDWitness prog (fuel + 1) []
  | cons (fuel : ℕ) (a : Atom σ) (goals : List (Atom σ))
      (c : Clause σ) (θ : Subst σ) :
      c ∈ prog →
      unifyAtoms a c.head fuel = some θ →
      SLDWitness prog fuel (θ.applyAtoms (c.body ++ goals)) →
      SLDWitness prog (fuel + 1) (a :: goals)

/-- If some member of a list maps to `some _`, then `findSome?` returns `some _`. -/
private theorem exists_findSome?_some_of_exists_mem
    {α β : Type*} (l : List α) (f : α → Option β)
    (h : ∃ a ∈ l, ∃ b, f a = some b) :
    ∃ b, l.findSome? f = some b := by
  induction l with
  | nil =>
      rcases h with ⟨a, ha, _⟩
      cases ha
  | cons x xs ih =>
      rcases h with ⟨a, ha, hb⟩
      rcases List.mem_cons.mp ha with hax | ha_tail
      · subst hax
        rcases hb with ⟨b, hfb⟩
        exact ⟨b, by simp [List.findSome?, hfb]⟩
      · by_cases hx : ∃ b, f x = some b
        · rcases hx with ⟨b, hxb⟩
          exact ⟨b, by simp [List.findSome?, hxb]⟩
        · have hnone : f x = none := by
            cases hfx : f x with
            | none => simp
            | some b =>
                exfalso
                exact hx ⟨b, hfx⟩
          rcases ih ⟨a, ha_tail, hb⟩ with ⟨b, hbfind⟩
          exact ⟨b, by simp [List.findSome?, hnone, hbfind]⟩

/-- **Bounded completeness of `sldSearch`**:
if there exists a finite SLD witness at a given fuel, the executable search succeeds. -/
theorem sldSearch_complete_bounded {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ))
    (h : SLDWitness prog fuel goals) :
    ∃ θ : Subst σ, sldSearch prog fuel goals = some θ := by
  induction h with
  | nil fuel =>
      exact ⟨Subst.id σ, by simp [sldSearch]⟩
  | cons fuel a goals c θ hc hunif hw ih =>
      rcases ih with ⟨θ', hrec⟩
      let tryClause : Clause σ → Option (Subst σ) := fun c' =>
        match unifyAtoms a c'.head fuel with
        | none => none
        | some θu =>
          match sldSearch prog fuel (θu.applyAtoms (c'.body ++ goals)) with
          | none => none
          | some θr => some (θr ∘ₛ θu)
      have hclauseSome : ∃ θres, tryClause c = some θres := by
        refine ⟨θ' ∘ₛ θ, ?_⟩
        simp [tryClause, hunif, hrec]
      have hexistsSome :
          ∃ c' ∈ prog, ∃ θres, tryClause c' = some θres :=
        ⟨c, hc, hclauseSome⟩
      rcases exists_findSome?_some_of_exists_mem prog tryClause hexistsSome with ⟨θres, hfind⟩
      exact ⟨θres, by simpa [sldSearch] using hfind⟩

/-- If `sldSearch` succeeds, we can reconstruct a bounded witness tree. -/
theorem sldSearch_some_implies_witness {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ)) (θ : Subst σ)
    (h : sldSearch prog fuel goals = some θ) :
    SLDWitness prog fuel goals := by
  induction fuel generalizing goals θ with
  | zero =>
      simp [sldSearch] at h
  | succ n ih =>
      match goals with
      | [] =>
          simp [sldSearch] at h
          subst h
          exact SLDWitness.nil n
      | a :: rest =>
          simp only [sldSearch] at h
          obtain ⟨c, hc, hfc⟩ := mem_of_findSome?_some h
          obtain ⟨θ_unif, θ_rec, hunify, hrec, heq⟩ := extract_clause_result hfc
          subst heq
          exact SLDWitness.cons n a rest c θ_unif hc hunify (ih _ _ hrec)

/-- Executable success is equivalent to existence of a bounded witness tree. -/
theorem sldSearch_some_iff_witness {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ)) :
    (∃ θ : Subst σ, sldSearch prog fuel goals = some θ) ↔
      SLDWitness prog fuel goals := by
  constructor
  · intro h
    rcases h with ⟨θ, hθ⟩
    exact sldSearch_some_implies_witness prog fuel goals θ hθ
  · exact sldSearch_complete_bounded prog fuel goals

/-- A bounded witness induces an abstract `SLDTree` derivation. -/
theorem SLDWitness_yields_SLDTree {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (fuel : ℕ) (goals : List (Atom σ))
    (h : SLDWitness prog fuel goals) :
    ∃ θ : Subst σ, SLDTree prog goals θ := by
  induction h with
  | nil fuel =>
      exact ⟨Subst.id σ, SLDTree.nil⟩
  | cons fuel a goals c θu hc hunif hw ih =>
      rcases ih with ⟨θ', htree⟩
      refine ⟨θ' ∘ₛ θu, ?_⟩
      exact SLDTree.cons a goals c θu θ' hc (unifyAtoms_sound a c.head fuel θu hunif) htree

/-- Soundness corollary for bounded witnesses via the existing `SLDTree_sound` theorem. -/
theorem SLDWitness_sound {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (fuel : ℕ) (goals : List (Atom σ))
    (h : SLDWitness kb.prog fuel goals) :
    ∃ θ : Subst σ, ∀ g : Grounding σ, ∀ a ∈ goals,
      (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb := by
  rcases SLDWitness_yields_SLDTree kb.prog fuel goals h with ⟨θ, htree⟩
  exact ⟨θ, SLDTree_sound kb goals θ htree⟩

/-- Single-query bounded completeness via `sldQuery`. -/
theorem sldQuery_complete_bounded {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (prog : Program σ) (a : Atom σ) (fuel : ℕ)
    (h : SLDWitness prog fuel [a]) :
    ∃ θ : Subst σ, sldQuery prog a fuel = some θ := by
  simpa [sldQuery] using sldSearch_complete_bounded prog fuel [a] h

/-- End-to-end completeness composition:
semantic lifting (`leastHerbrandModel` → `SLDWitness`) implies executable success. -/
theorem sldQuery_complete_of_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hLift : ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, sldQuery kb.prog ga.toAtom fuel = some θ := by
  rcases hLift ga ha with ⟨fuel, hw⟩
  rcases sldQuery_complete_bounded kb.prog ga.toAtom fuel hw with ⟨θ, hθ⟩
  exact ⟨fuel, θ, hθ⟩

/-- Lift an iterate-level witness constructor to full least-model witness coverage. -/
theorem sldWitness_lift_of_iter_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hIterLift : ∀ n : ℕ, ∀ ga : GroundAtom σ, ga ∈ T_P_LP_iter kb n →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom]) :
    ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom] := by
  intro ga hga
  have hIter : ga ∈ ⋃ n, T_P_LP_iter kb n := by
    rw [← leastHerbrandModel_eq_iter_sup (kb := kb)]
    exact hga
  rcases Set.mem_iUnion.mp hIter with ⟨n, hn⟩
  exact hIterLift n ga hn

/-- Constructive iterate-level lifting from base (`db`) and rule-step witness constructors. -/
theorem sldWitness_iter_lift_of_db_and_rule {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hBase : ∀ ga : GroundAtom σ, ga ∈ kb.db →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    (hRule : ∀ c : Clause σ, ∀ γ : Grounding σ, c ∈ kb.prog →
      (∀ b ∈ c.body, ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom]) →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom c.head).toAtom]) :
    ∀ n : ℕ, ∀ ga : GroundAtom σ, ga ∈ T_P_LP_iter kb n →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom] := by
  intro n
  induction n with
  | zero =>
      intro ga hga
      simpa [T_P_LP_iter] using hBase ga hga
  | succ n ih =>
      intro ga hga
      simp [T_P_LP_iter, T_P_LP] at hga
      rcases hga with hdb | hclause
      · exact hBase ga hdb
      · rcases hclause with ⟨c, hclause⟩
        rcases hclause with ⟨hc, hclause⟩
        rcases hclause with ⟨γ, hhead, hbody⟩
        subst hhead
        refine hRule c γ hc ?_
        intro b hb
        exact ih (γ.groundAtom b) (hbody b hb)

/-- Lift least-model membership to witness coverage from base+rule lifting data. -/
theorem sldWitness_lift_of_db_and_rule {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hBase : ∀ ga : GroundAtom σ, ga ∈ kb.db →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    (hRule : ∀ c : Clause σ, ∀ γ : Grounding σ, c ∈ kb.prog →
      (∀ b ∈ c.body, ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom]) →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom c.head).toAtom]) :
    ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom] := by
  refine sldWitness_lift_of_iter_lift kb ?_
  exact sldWitness_iter_lift_of_db_and_rule kb hBase hRule

/-- Completeness endpoint using iterate-level lifting data. -/
theorem sldQuery_complete_of_iter_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hIterLift : ∀ n : ℕ, ∀ ga : GroundAtom σ, ga ∈ T_P_LP_iter kb n →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, sldQuery kb.prog ga.toAtom fuel = some θ := by
  have hLift :
      ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
        ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom] :=
    sldWitness_lift_of_iter_lift kb hIterLift
  exact sldQuery_complete_of_lift kb hLift ha

/-- End-to-end completeness using proved least-model witness lifting
from iterative characterization. -/
theorem sldQuery_complete_of_semantic_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hBase : ∀ ga : GroundAtom σ, ga ∈ kb.db →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    (hRule : ∀ c : Clause σ, ∀ γ : Grounding σ, c ∈ kb.prog →
      (∀ b ∈ c.body, ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom]) →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom c.head).toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, sldQuery kb.prog ga.toAtom fuel = some θ := by
  have hLift :
      ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
        ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom] :=
    sldWitness_lift_of_db_and_rule kb hBase hRule
  exact sldQuery_complete_of_lift kb hLift ha

/-- Compatibility alias: completeness endpoint where lifting data is provided
explicitly in base+rule form. -/
theorem sldQuery_complete_of_db_and_rule_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hBase : ∀ ga : GroundAtom σ, ga ∈ kb.db →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    (hRule : ∀ c : Clause σ, ∀ γ : Grounding σ, c ∈ kb.prog →
      (∀ b ∈ c.body, ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom]) →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom c.head).toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, sldQuery kb.prog ga.toAtom fuel = some θ :=
  sldQuery_complete_of_semantic_lift kb hBase hRule ha

/-- Stronger end-to-end bundle:
semantic lifting gives executable success and least-model soundness in one theorem. -/
theorem sldQuery_complete_sound_bundle_of_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hLift : ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      sldQuery kb.prog ga.toAtom fuel = some θ ∧
      ∀ g : Grounding σ,
        (g.compSubst θ).groundAtom ga.toAtom ∈ leastHerbrandModel kb := by
  rcases sldQuery_complete_of_lift kb hLift ha with ⟨fuel, θ, hθ⟩
  refine ⟨fuel, θ, hθ, ?_⟩
  intro g
  exact sldQuery_sound kb ga.toAtom fuel θ hθ g

/-- Soundness+completeness bundle using iterate-level lifting data. -/
theorem sldQuery_complete_sound_bundle_of_iter_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hIterLift : ∀ n : ℕ, ∀ ga : GroundAtom σ, ga ∈ T_P_LP_iter kb n →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      sldQuery kb.prog ga.toAtom fuel = some θ ∧
      ∀ g : Grounding σ,
        (g.compSubst θ).groundAtom ga.toAtom ∈ leastHerbrandModel kb := by
  have hLift :
      ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
        ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom] :=
    sldWitness_lift_of_iter_lift kb hIterLift
  exact sldQuery_complete_sound_bundle_of_lift kb hLift ha

/-- Soundness+completeness bundle using proved least-model witness lifting
from iterative characterization. -/
theorem sldQuery_complete_sound_bundle_of_semantic_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hBase : ∀ ga : GroundAtom σ, ga ∈ kb.db →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    (hRule : ∀ c : Clause σ, ∀ γ : Grounding σ, c ∈ kb.prog →
      (∀ b ∈ c.body, ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom]) →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom c.head).toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      sldQuery kb.prog ga.toAtom fuel = some θ ∧
      ∀ g : Grounding σ,
        (g.compSubst θ).groundAtom ga.toAtom ∈ leastHerbrandModel kb := by
  have hLift :
      ∀ ga : GroundAtom σ, ga ∈ leastHerbrandModel kb →
        ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom] :=
    sldWitness_lift_of_db_and_rule kb hBase hRule
  exact sldQuery_complete_sound_bundle_of_lift kb hLift ha

/-- Compatibility alias: soundness+completeness bundle where lifting data is
provided explicitly in base+rule form. -/
theorem sldQuery_complete_sound_bundle_of_db_and_rule_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ)
    (hBase : ∀ ga : GroundAtom σ, ga ∈ kb.db →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom])
    (hRule : ∀ c : Clause σ, ∀ γ : Grounding σ, c ∈ kb.prog →
      (∀ b ∈ c.body, ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom]) →
      ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom c.head).toAtom])
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      sldQuery kb.prog ga.toAtom fuel = some θ ∧
      ∀ g : Grounding σ,
        (g.compSubst θ).groundAtom ga.toAtom ∈ leastHerbrandModel kb :=
  sldQuery_complete_sound_bundle_of_semantic_lift kb hBase hRule ha

end Mettapedia.Logic.LP
