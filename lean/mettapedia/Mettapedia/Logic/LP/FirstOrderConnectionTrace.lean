import Mettapedia.Logic.LP.FirstOrderConnectionSearch
import Mettapedia.Logic.LP.FirstOrderConnectionSoundness
import Mettapedia.Logic.LP.FirstOrderConnectionScopedSearch
import Mettapedia.Logic.LP.FirstOrderConnectionScopeBounds
import Mettapedia.Logic.LP.UnificationComplete
import Mathlib.Data.List.TakeDrop

/-!
# First-order connection trace objects, search and ranked collection

Each pending goal retains its own ancestor path, and substitutions propagate
through all pending frames. The `proof_fo` step/object format is unchanged.
The operational theorems concern the supplied fixed-variable clause matrix.
Independent arbitrary-structure soundness is imported from
`FirstOrderConnectionSoundness`. The scoped checker and DFS entry points use
per-use clause copies, with actual-unifier scope preservation from
`FirstOrderConnectionScopeBounds`. Full first-order refutational completeness
remains separate from accepted-trace witness completeness.
-/

namespace Mettapedia.Logic.LP

noncomputable section

section FirstOrderConnection

variable {σ : LPSignature}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
variable [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

def connProveFODFS (clauses : ConnFOCNF σ) (uFuel : Nat) (goals path : ConnFOClause σ) (fuel : Nat) :
    Option (FOProofTrace σ) := connProveFOAgendaDFS clauses uFuel (connectionGoals goals path) fuel

def connProveAllFO (clauses : ConnFOCNF σ) (uFuel : Nat) (goals path : ConnFOClause σ) (fuel : Nat) :
    List (FOProofTrace σ) := connProveFOAgendaAll clauses uFuel (connectionGoals goals path) fuel

theorem connProveFODFS_some_mem_connProveAllFO (clauses : ConnFOCNF σ) (uFuel : Nat)
    (fuel : Nat) (goals path : ConnFOClause σ) (trace : FOProofTrace σ)
    (computed : connProveFODFS clauses uFuel goals path fuel = some trace) :
    trace ∈ connProveAllFO clauses uFuel goals path fuel :=
  connProveFOAgendaDFS_some_mem_connProveFOAgendaAll clauses uFuel fuel _ trace computed

theorem connProveAllFO_sound_of_mem (clauses : ConnFOCNF σ) (uFuel : Nat)
    (fuel : Nat) (goals path : ConnFOClause σ) (trace : FOProofTrace σ)
    (member : trace ∈ connProveAllFO clauses uFuel goals path fuel) :
    TraceDerivableFO clauses uFuel goals path trace :=
  connProveFOAgendaAll_sound_of_mem clauses uFuel fuel _ trace member

theorem connProveAllFO_sound {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {goals path : ConnFOClause σ} {trace : FOProofTrace σ}
    (member : trace ∈ connProveAllFO clauses uFuel goals path fuel) : TraceDerivableFO clauses uFuel goals path trace :=
  connProveAllFO_sound_of_mem clauses uFuel fuel goals path trace member

theorem connProveFODFS_sound_of_some (clauses : ConnFOCNF σ) (uFuel : Nat)
    (fuel : Nat) (goals path : ConnFOClause σ) (trace : FOProofTrace σ)
    (computed : connProveFODFS clauses uFuel goals path fuel = some trace) :
    TraceDerivableFO clauses uFuel goals path trace :=
  connProveFOAgendaDFS_sound_of_some clauses uFuel fuel _ trace computed

theorem connProveFODFS_sound {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {goals path : ConnFOClause σ} {trace : FOProofTrace σ}
    (computed : connProveFODFS clauses uFuel goals path fuel = some trace) : TraceDerivableFO clauses uFuel goals path trace :=
  connProveFODFS_sound_of_some clauses uFuel fuel goals path trace computed

theorem connProveFODFS_some_refines_connProveAllFO {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {goals path : ConnFOClause σ} {trace : FOProofTrace σ}
    (computed : connProveFODFS clauses uFuel goals path fuel = some trace) :
    trace ∈ connProveAllFO clauses uFuel goals path fuel ∧ TraceDerivableFO clauses uFuel goals path trace :=
  ⟨connProveFODFS_some_mem_connProveAllFO clauses uFuel fuel goals path trace computed, connProveFODFS_sound computed⟩

theorem connProveFODFS_complete_of_trace {clauses : ConnFOCNF σ} {uFuel : Nat}
    {goals path : ConnFOClause σ} {trace : FOProofTrace σ} {fuel : Nat}
    (derived : TraceDerivableFO clauses uFuel goals path trace) (budget : trace.length ≤ fuel) :
    ∃ result, connProveFODFS clauses uFuel goals path fuel = some result :=
  connProveFOAgendaDFS_complete_of_trace derived budget

theorem connProveFODFS_witness_complete {clauses : ConnFOCNF σ} {uFuel : Nat} {goals path : ConnFOClause σ}
    (derived : ∃ trace, TraceDerivableFO clauses uFuel goals path trace) :
    ∃ fuel trace, connProveFODFS clauses uFuel goals path fuel = some trace := by
  obtain ⟨trace, traced⟩ := derived
  obtain ⟨result, computed⟩ := connProveFODFS_complete_of_trace traced (Nat.le_refl trace.length)
  exact ⟨trace.length, result, computed⟩

/-! ## FO collection + ranking contracts (PeTTa parity layer) -/

/-- Wrap FO traces as `FOProofObj` values for a fixed root/fuel. -/
def wrapFOTracesAsProofs (fuel : Nat) (root : ConnFOClause σ)
    (traces : List (FOProofTrace σ)) : List (FOProofObj σ) :=
  traces.map (fun tr => { fuel := fuel, root := root, trace := tr })

/-- Branch-complete proof objects for one root clause. -/
def rootProofsAllFO (clauses : ConnFOCNF σ) (uFuel fuel : Nat)
    (root : ConnFOClause σ) : List (FOProofObj σ) :=
  wrapFOTracesAsProofs (σ := σ) fuel root (connProveAllFO clauses uFuel root [] fuel)

/-- Branch-complete proof objects collected over a root list. -/
def collectRootProofsAllFO (clauses : ConnFOCNF σ) (uFuel fuel : Nat)
    (roots : ConnFOCNF σ) : List (FOProofObj σ) :=
  match roots with
  | [] => []
  | root :: tail =>
      rootProofsAllFO (σ := σ) clauses uFuel fuel root
        ++ collectRootProofsAllFO clauses uFuel fuel tail

/-- Branch-complete proof objects collected over matrix roots. -/
def collectProofsAllFO (clauses : ConnFOCNF σ) (uFuel fuel : Nat) : List (FOProofObj σ) :=
  collectRootProofsAllFO clauses uFuel fuel clauses

/-- Default FO ranking score used for deterministic topK extraction. -/
def foProofRankScore (p : FOProofObj σ) : Nat :=
  p.fuel + p.trace.length

/-- Insert one FO proof in descending score order. -/
def insertFOProofByScore (score : FOProofObj σ → Nat)
    (p : FOProofObj σ) : List (FOProofObj σ) → List (FOProofObj σ)
  | [] => [p]
  | q :: qs =>
      if score p ≥ score q then
        p :: q :: qs
      else
        q :: insertFOProofByScore score p qs

/-- Stable insertion-sort by descending score. -/
def sortFOProofsDescByScore (score : FOProofObj σ → Nat)
    (proofs : List (FOProofObj σ)) : List (FOProofObj σ) :=
  proofs.foldr (insertFOProofByScore score) []

/-- Top-K projection over sorted FO proofs. -/
def topKFOProofsByScore (score : FOProofObj σ → Nat)
    (proofs : List (FOProofObj σ)) (topK : Nat) : List (FOProofObj σ) :=
  (sortFOProofsDescByScore score proofs).take topK

/-- Top-K over branch-complete FO proofs. -/
def topKCollectProofsAllFO (score : FOProofObj σ → Nat)
    (clauses : ConnFOCNF σ) (uFuel fuel topK : Nat) : List (FOProofObj σ) :=
  topKFOProofsByScore score (collectProofsAllFO (σ := σ) clauses uFuel fuel) topK

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_insertFOProofByScore_iff
    (score : FOProofObj σ → Nat) (p : FOProofObj σ)
    {ps : List (FOProofObj σ)} {x : FOProofObj σ} :
    x ∈ insertFOProofByScore score p ps ↔ x = p ∨ x ∈ ps := by
  induction ps with
  | nil =>
      simp [insertFOProofByScore]
  | cons q qs ih =>
      by_cases hcmp : score p ≥ score q
      · simp [insertFOProofByScore, hcmp]
      · simp [insertFOProofByScore, hcmp, ih]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_sortFOProofsDescByScore_iff
    (score : FOProofObj σ → Nat) {proofs : List (FOProofObj σ)} {x : FOProofObj σ} :
    x ∈ sortFOProofsDescByScore score proofs ↔ x ∈ proofs := by
  induction proofs with
  | nil =>
      simp [sortFOProofsDescByScore]
  | cons p ps ih =>
      have ih' : x ∈ List.foldr (insertFOProofByScore score) [] ps ↔ x ∈ ps := by
        simpa [sortFOProofsDescByScore] using ih
      simp [sortFOProofsDescByScore, ih', mem_insertFOProofByScore_iff]

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_topKFOProofsByScore_implies_mem
    (score : FOProofObj σ → Nat) {proofs : List (FOProofObj σ)} {topK : Nat}
    {p : FOProofObj σ}
    (h : p ∈ topKFOProofsByScore score proofs topK) :
    p ∈ proofs := by
  have hMemSorted : p ∈ sortFOProofsDescByScore score proofs :=
    List.mem_of_mem_take h
  exact (mem_sortFOProofsDescByScore_iff (σ := σ) score).1 hMemSorted

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem length_topKFOProofsByScore_le
    (score : FOProofObj σ → Nat) (proofs : List (FOProofObj σ)) (topK : Nat) :
    (topKFOProofsByScore score proofs topK).length ≤ topK := by
  simp [topKFOProofsByScore]

theorem mem_topKCollectProofsAllFO_implies_mem_collectProofsAllFO
    (score : FOProofObj σ → Nat) {clauses : ConnFOCNF σ} {uFuel fuel topK : Nat}
    {p : FOProofObj σ}
    (h : p ∈ topKCollectProofsAllFO (σ := σ) score clauses uFuel fuel topK) :
    p ∈ collectProofsAllFO (σ := σ) clauses uFuel fuel := by
  exact mem_topKFOProofsByScore_implies_mem (σ := σ) score h

theorem length_topKCollectProofsAllFO_le
    (score : FOProofObj σ → Nat) (clauses : ConnFOCNF σ)
    (uFuel fuel topK : Nat) :
    (topKCollectProofsAllFO (σ := σ) score clauses uFuel fuel topK).length ≤ topK := by
  exact length_topKFOProofsByScore_le
    (σ := σ) score (collectProofsAllFO (σ := σ) clauses uFuel fuel) topK

/-- Contract alias: topK-over-all is definitionally topK over `collectProofsAllFO`. -/
theorem topKCollectProofsAllFO_contract
    (score : FOProofObj σ → Nat) (clauses : ConnFOCNF σ)
    (uFuel fuel topK : Nat) :
    topKCollectProofsAllFO (σ := σ) score clauses uFuel fuel topK =
      topKFOProofsByScore score (collectProofsAllFO (σ := σ) clauses uFuel fuel) topK := rfl

/-! ## FO `collectProofsAll` root-membership family (PeTTa parity layer) -/

omit [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] in
theorem mem_wrapFOTracesAsProofs_of_mem
    {fuel : Nat} {root : ConnFOClause σ}
    {tr : FOProofTrace σ} {trs : List (FOProofTrace σ)}
    (h : tr ∈ trs) :
    ({ fuel := fuel, root := root, trace := tr } : FOProofObj σ) ∈
      wrapFOTracesAsProofs (σ := σ) fuel root trs := by
  unfold wrapFOTracesAsProofs
  exact List.mem_map.mpr ⟨tr, h, rfl⟩

theorem rootProofsAllFO_mem_collectRootProofsAllFO_of_mem_root
    {clauses roots : ConnFOCNF σ} {uFuel fuel : Nat}
    {root : ConnFOClause σ} {p : FOProofObj σ}
    (hRoot : root ∈ roots)
    (hp : p ∈ rootProofsAllFO (σ := σ) clauses uFuel fuel root) :
    p ∈ collectRootProofsAllFO (σ := σ) clauses uFuel fuel roots := by
  induction roots generalizing root p with
  | nil =>
      cases hRoot
  | cons r rs ih =>
      simp [collectRootProofsAllFO] at hRoot ⊢
      cases hRoot with
      | inl hr =>
          subst hr
          exact Or.inl hp
      | inr hTail =>
          exact Or.inr (ih hTail hp)

theorem proof_mem_collectProofsAllFO_of_root_mem_trace_mem
    {clauses : ConnFOCNF σ} {uFuel fuel : Nat}
    {root : ConnFOClause σ} {tr : FOProofTrace σ}
    (hRoot : root ∈ clauses)
    (hTr : tr ∈ connProveAllFO (σ := σ) clauses uFuel root [] fuel) :
    ({ fuel := fuel, root := root, trace := tr } : FOProofObj σ) ∈
      collectProofsAllFO (σ := σ) clauses uFuel fuel := by
  unfold collectProofsAllFO
  exact rootProofsAllFO_mem_collectRootProofsAllFO_of_mem_root
    (σ := σ) (clauses := clauses) (roots := clauses)
    (uFuel := uFuel) (fuel := fuel) (root := root)
    hRoot
    (mem_wrapFOTracesAsProofs_of_mem (σ := σ) hTr)

/-! ## PeTTaFixtureMapFO (`test_leancop_*` parity names) -/

section PeTTaFixtureMapFO

inductive FOFixVar where
  | x
  deriving DecidableEq, Repr

inductive FOFixConst where
  | a
  deriving DecidableEq, Repr

inductive FOFixRel where
  | p
  deriving DecidableEq, Repr

inductive FOFixFun where
  | f
  deriving DecidableEq, Repr

def foFixtureSig : LPSignature where
  constants := FOFixConst
  vars := FOFixVar
  relationSymbols := FOFixRel
  relationArity
    | .p => 1
  functionSymbols := FOFixFun
  functionArity
    | .f => 1

local instance : DecidableEq foFixtureSig.vars := inferInstanceAs (DecidableEq FOFixVar)
local instance : DecidableEq foFixtureSig.constants := inferInstanceAs (DecidableEq FOFixConst)
local instance : DecidableEq foFixtureSig.relationSymbols := inferInstanceAs (DecidableEq FOFixRel)
local instance : DecidableEq foFixtureSig.functionSymbols := inferInstanceAs (DecidableEq FOFixFun)

def fo_tA : Term foFixtureSig := .const .a
def fo_tX : Term foFixtureSig := .var .x
def fo_tFa : Term foFixtureSig := .app .f (fun _ => fo_tA)

def fo_atomP (t : Term foFixtureSig) : Atom foFixtureSig where
  symbol := .p
  args := fun _ => t

def fo_lit_pos_a : ConnFOLit foFixtureSig := .pos (fo_atomP fo_tA)
def fo_lit_neg_a : ConnFOLit foFixtureSig := .neg (fo_atomP fo_tA)
def fo_lit_pos_x : ConnFOLit foFixtureSig := .pos (fo_atomP fo_tX)
def fo_lit_neg_fa : ConnFOLit foFixtureSig := .neg (fo_atomP fo_tFa)

def fo_unsat_ground_c1 : ConnFOClause foFixtureSig := [fo_lit_pos_a]
def fo_unsat_ground_c2 : ConnFOClause foFixtureSig := [fo_lit_neg_a]
def fo_unsat_ground_clauses : ConnFOCNF foFixtureSig := [fo_unsat_ground_c1, fo_unsat_ground_c2]
def fo_unsat_ground_root : ConnFOClause foFixtureSig := fo_unsat_ground_c1

def fo_unsat_unify_c1 : ConnFOClause foFixtureSig := [fo_lit_pos_x]
def fo_unsat_unify_c2 : ConnFOClause foFixtureSig := [fo_lit_neg_fa]
def fo_unsat_unify_clauses : ConnFOCNF foFixtureSig := [fo_unsat_unify_c1, fo_unsat_unify_c2]
def fo_unsat_unify_root : ConnFOClause foFixtureSig := fo_unsat_unify_c1

def fo_sat_singleton_clauses : ConnFOCNF foFixtureSig := [fo_unsat_ground_c1]
def fo_sat_singleton_root : ConnFOClause foFixtureSig := fo_unsat_ground_c1

/-- Named FO fixture lemma: ground contradiction has an executable FO proof witness. -/
theorem fo_unsat_ground :
    ∃ uFuel tr, connProveFODFS (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel fo_unsat_ground_root [] 2 = some tr := by
  have hUnifies : Unifies (Subst.id (σ := foFixtureSig))
      (finPairsToList (fun _ : Fin 1 => fo_tA) (fun _ : Fin 1 => fo_tA)) := by
    intro p hp
    have hp' : p = (fo_tA, fo_tA) := by
      simpa [finPairsToList, fo_tA] using hp
    subst hp'
    simp [Subst.id, fo_tA]
  rcases unifyFuel_exists_of_unifies
      (eqs := finPairsToList (fun _ : Fin 1 => fo_tA) (fun _ : Fin 1 => fo_tA))
      ⟨Subst.id (σ := foFixtureSig), hUnifies⟩ with ⟨uFuel, θ, hU⟩
  have hUnify :
      unifyComplementLit? (σ := foFixtureSig) uFuel fo_lit_pos_a fo_lit_neg_a = some θ := by
    unfold unifyComplementLit? unifyAtoms
    simp [fo_lit_pos_a, fo_lit_neg_a, fo_atomP]
    exact ⟨rfl, hU⟩
  have hDer : TraceDerivableFO fo_unsat_ground_clauses uFuel
      fo_unsat_ground_root [] [.step_extend fo_unsat_ground_c2 fo_lit_neg_a] := by
    have hErase : fo_unsat_ground_c2.erase fo_lit_neg_a = [] := by
      simp [fo_unsat_ground_c2, fo_lit_neg_a]
    refine AgendaTraceDerivableFO.extend
      fo_lit_pos_a [] [] fo_unsat_ground_c2 fo_lit_neg_a [] θ
      (by simp [fo_unsat_ground_clauses, fo_unsat_ground_c2, fo_unsat_ground_c1])
      (by simp [fo_unsat_ground_c2, fo_lit_neg_a]) hUnify ?_
    simpa only [hErase, connectionGoals_nil, List.nil_append, Subst.applyConnFOAgenda_nil]
      using (AgendaTraceDerivableFO.done (clauses := fo_unsat_ground_clauses) (uFuel := uFuel))
  rcases connProveFODFS_complete_of_trace
      (σ := foFixtureSig) (clauses := fo_unsat_ground_clauses) (uFuel := uFuel)
      (goals := fo_unsat_ground_root) (path := [])
      (trace := [.step_extend fo_unsat_ground_c2 fo_lit_neg_a]) (fuel := 2)
      hDer (by decide) with ⟨tr, hRun⟩
  exact ⟨uFuel, tr, hRun⟩

/-- Named FO fixture lemma: unification contradiction has an executable FO proof witness. -/
theorem fo_unsat_unify :
    ∃ uFuel tr, connProveFODFS (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel fo_unsat_unify_root [] 2 = some tr := by
  let δ : Subst foFixtureSig := Subst.single .x fo_tFa
  have hUnifies : Unifies δ
      (finPairsToList (fun _ : Fin 1 => fo_tX) (fun _ : Fin 1 => fo_tFa)) := by
    intro p hp
    have hp' : p = (fo_tX, fo_tFa) := by
      simpa [finPairsToList, fo_tX, fo_tFa, fo_tA] using hp
    subst hp'
    simp [δ, Subst.single, Subst.applyTerm, fo_tX, fo_tFa, fo_tA]
    rfl
  rcases unifyFuel_exists_of_unifies
      (eqs := finPairsToList (fun _ : Fin 1 => fo_tX) (fun _ : Fin 1 => fo_tFa))
      ⟨δ, hUnifies⟩ with ⟨uFuel, θ, hU⟩
  have hUnify :
      unifyComplementLit? (σ := foFixtureSig) uFuel fo_lit_pos_x fo_lit_neg_fa = some θ := by
    unfold unifyComplementLit? unifyAtoms
    simp [fo_lit_pos_x, fo_lit_neg_fa, fo_atomP]
    exact ⟨rfl, hU⟩
  have hDer : TraceDerivableFO fo_unsat_unify_clauses uFuel
      fo_unsat_unify_root [] [.step_extend fo_unsat_unify_c2 fo_lit_neg_fa] := by
    have hErase : fo_unsat_unify_c2.erase fo_lit_neg_fa = [] := by
      simp [fo_unsat_unify_c2, fo_lit_neg_fa]
    refine AgendaTraceDerivableFO.extend
      fo_lit_pos_x [] [] fo_unsat_unify_c2 fo_lit_neg_fa [] θ
      (by simp [fo_unsat_unify_clauses, fo_unsat_unify_c2, fo_unsat_unify_c1])
      (by simp [fo_unsat_unify_c2, fo_lit_neg_fa]) hUnify ?_
    simpa only [hErase, connectionGoals_nil, List.nil_append, Subst.applyConnFOAgenda_nil]
      using (AgendaTraceDerivableFO.done (clauses := fo_unsat_unify_clauses) (uFuel := uFuel))
  rcases connProveFODFS_complete_of_trace
      (σ := foFixtureSig) (clauses := fo_unsat_unify_clauses) (uFuel := uFuel)
      (goals := fo_unsat_unify_root) (path := [])
      (trace := [.step_extend fo_unsat_unify_c2 fo_lit_neg_fa]) (fuel := 2)
      hDer (by decide) with ⟨tr, hRun⟩
  exact ⟨uFuel, tr, hRun⟩

/-- Named FO fixture lemma: singleton positive clause remains unsolved for all fuels. -/
theorem fo_sat_singleton :
    ∀ uFuel fuel, connProveFODFS (σ := foFixtureSig)
      fo_sat_singleton_clauses uFuel fo_sat_singleton_root [] fuel = none := by
  intro uFuel fuel
  cases fuel with
  | zero =>
      simp [connProveFODFS, connProveFOAgendaDFS, connectionGoals, fo_sat_singleton_root, fo_unsat_ground_c1]
  | succ n =>
      simp [connProveFODFS, connProveFOAgendaDFS, connectionGoals, fo_sat_singleton_clauses, fo_sat_singleton_root, fo_unsat_ground_c1,
        tryExtendFO, tryExtendClauseFO, tryReducePathFO, unifyComplementLit?, fo_lit_pos_a]

/-- FO fixture-parity: root-wise proof witnesses are members of branch-complete proof collection (ground). -/
theorem fo_unsat_ground_proof_mem_collectProofsAllFO :
    ∃ uFuel : Nat, ∃ p : FOProofObj foFixtureSig, p ∈ collectProofsAllFO (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel 2 := by
  rcases fo_unsat_ground with ⟨uFuel, tr, hRun⟩
  let p : FOProofObj foFixtureSig :=
    { fuel := 2, root := fo_unsat_ground_root, trace := tr }
  refine ⟨uFuel, p, ?_⟩
  have hTrMem : tr ∈ connProveAllFO (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel fo_unsat_ground_root [] 2 :=
    connProveFODFS_some_mem_connProveAllFO (σ := foFixtureSig)
      fo_unsat_ground_clauses uFuel 2 fo_unsat_ground_root [] tr hRun
  simpa [p] using
    (proof_mem_collectProofsAllFO_of_root_mem_trace_mem
      (clauses := fo_unsat_ground_clauses) (uFuel := uFuel) (fuel := 2)
      (root := fo_unsat_ground_root) (tr := tr)
      (by simp [fo_unsat_ground_root, fo_unsat_ground_clauses, fo_unsat_ground_c1]) hTrMem)

/-- FO fixture-parity: root-wise proof witnesses are members of branch-complete proof collection (unify). -/
theorem fo_unsat_unify_proof_mem_collectProofsAllFO :
    ∃ uFuel : Nat, ∃ p : FOProofObj foFixtureSig, p ∈ collectProofsAllFO (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel 2 := by
  rcases fo_unsat_unify with ⟨uFuel, tr, hRun⟩
  let p : FOProofObj foFixtureSig :=
    { fuel := 2, root := fo_unsat_unify_root, trace := tr }
  refine ⟨uFuel, p, ?_⟩
  have hTrMem : tr ∈ connProveAllFO (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel fo_unsat_unify_root [] 2 :=
    connProveFODFS_some_mem_connProveAllFO (σ := foFixtureSig)
      fo_unsat_unify_clauses uFuel 2 fo_unsat_unify_root [] tr hRun
  simpa [p] using
    (proof_mem_collectProofsAllFO_of_root_mem_trace_mem
      (clauses := fo_unsat_unify_clauses) (uFuel := uFuel) (fuel := 2)
      (root := fo_unsat_unify_root) (tr := tr)
      (by simp [fo_unsat_unify_root, fo_unsat_unify_clauses, fo_unsat_unify_c1]) hTrMem)

end PeTTaFixtureMapFO

end FirstOrderConnection

end

end Mettapedia.Logic.LP
