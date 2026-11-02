import Mettapedia.Logic.LP.PropositionalConnectionSearch

/-!
# Propositional connection tableau proof objects, search and collection

Replay and both searches use branch-local goal agendas. The reduction and
extension proof-step format is unchanged. Operational correspondence is
separate from the independent Boolean semantic theorem
`checkProof_unsatisfiable` imported from the checked replay core.
-/

namespace Mettapedia.Logic.LP

section PropositionalConnection

variable {α : Type*} [DecidableEq α]


/-! ## Operator-style refinement aliases (concrete API layer) -/

def op_replay_proof (clauses : ConnCNF α) (goals path : ConnClause α) (trace : ProofTrace α) : Bool :=
  replay clauses goals path trace

def op_check_proof (clauses : ConnCNF α) (p : ProofObj α) : Bool :=
  checkProof clauses p

def op_provable (clauses : ConnCNF α) (goals path : ConnClause α) : Prop :=
  ConnDerivable clauses goals path

theorem op_replay_refines
    (clauses : ConnCNF α) (goals path : ConnClause α) (trace : ProofTrace α) :
    op_replay_proof (α := α) clauses goals path trace = true →
      op_provable clauses goals path := by
  intro h
  exact replay_sound (α := α) h

theorem op_replay_complete
    (clauses : ConnCNF α) (goals path : ConnClause α)
    (h : op_provable (α := α) clauses goals path) :
    ∃ trace, op_replay_proof clauses goals path trace = true := by
  exact replay_complete (α := α) h

/-- Concrete checker implies abstract provability at root. -/
theorem op_check_proof_sound
    (clauses : ConnCNF α) (p : ProofObj α) :
    op_check_proof clauses p = true → p.root ∈ clauses ∧ op_provable clauses p.root [] := by
  intro h
  simpa [op_check_proof, op_provable] using
    (checkProof_sound (α := α) clauses p h)


/-- Root-wise proof object, aligned with PeTTa `root-proof`. -/
def rootProof (clauses : ConnCNF α) (root : ConnClause α) (fuel : Nat) : Option (ProofObj α) :=
  match connProveDFS clauses root [] fuel with
  | some tr => some { fuel := fuel, root := root, trace := tr }
  | none => none

/-- Root-wise collection helper over an explicit root list. -/
def collectRootProofs (clauses : ConnCNF α) (fuel : Nat) : ConnCNF α → List (ProofObj α)
  | [] => []
  | root :: tail =>
      match rootProof clauses root fuel with
      | some p => p :: collectRootProofs clauses fuel tail
      | none => collectRootProofs clauses fuel tail

/-- Root-wise collection, aligned with PeTTa `collect-proofs`. -/
def collectProofs (clauses : ConnCNF α) (fuel : Nat) : List (ProofObj α) :=
  collectRootProofs clauses fuel clauses


/-- Wrap traces as `(proof fuel root trace)` objects. -/
def wrapTracesAsProofs (fuel : Nat) (root : ConnClause α)
    (trs : List (ProofTrace α)) : List (ProofObj α) :=
  trs.map (fun tr => ({ fuel := fuel, root := root, trace := tr } : ProofObj α))

/-- All proofs for a fixed root, aligned with PeTTa `root-proofs-all`. -/
def rootProofsAll (clauses : ConnCNF α) (root : ConnClause α) (fuel : Nat) : List (ProofObj α) :=
  wrapTracesAsProofs fuel root (connProveAll clauses root [] fuel)

/-- Helper over root lists for branch-complete collection. -/
def collectRootProofsAll (clauses : ConnCNF α) (fuel : Nat) : ConnCNF α → List (ProofObj α)
  | [] => []
  | root :: tail =>
      rootProofsAll clauses root fuel ++ collectRootProofsAll clauses fuel tail

/-- Branch-complete collection, aligned with PeTTa `collect-proofs-all`. -/
def collectProofsAll (clauses : ConnCNF α) (fuel : Nat) : List (ProofObj α) :=
  collectRootProofsAll clauses fuel clauses


/-! ## Ranking and topK correctness over collected proofs -/

/-- Default deterministic ranking score (longer trace = higher score). -/
def proofRankScore (p : ProofObj α) : Nat :=
  p.trace.length

/-- Insert one proof into a descending-by-score list. -/
def insertProofByScore (score : ProofObj α → Nat)
    (p : ProofObj α) : List (ProofObj α) → List (ProofObj α)
  | [] => [p]
  | h :: t =>
      if score p >= score h then
        p :: h :: t
      else
        h :: insertProofByScore score p t

/-- Insertion sort descending by score. -/
def sortProofsDescByScore (score : ProofObj α → Nat) : List (ProofObj α) → List (ProofObj α)
  | [] => []
  | h :: t => insertProofByScore score h (sortProofsDescByScore score t)

/-- Top-k selection after descending score sort. -/
def topKProofsByScore (score : ProofObj α → Nat) (proofs : List (ProofObj α))
    (topK : Nat) : List (ProofObj α) :=
  (sortProofsDescByScore score proofs).take topK

/-- Top-k over root-wise collection. -/
def topKCollectProofs (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : List (ProofObj α) :=
  topKProofsByScore score (collectProofs clauses fuel) topK

/-- Top-k over branch-complete collection. -/
def topKCollectProofsAll (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : List (ProofObj α) :=
  topKProofsByScore score (collectProofsAll clauses fuel) topK

/-- Collected connection proofs together with their score-selected projection. -/
structure ProofCollectionBundle (α : Type u) where
  proofs : List (ProofObj α)
  topKProofs : List (ProofObj α)

/-- Bundle of fuel-bounded root-wise proof collection and its top-k projection. -/
def rootProofBundle (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : ProofCollectionBundle α :=
  { proofs := collectProofs clauses fuel
  , topKProofs := topKCollectProofs score clauses fuel topK
  }

/-- Bundle of fuel-bounded branch-complete proof collection and its top-k projection. -/
def branchProofBundle (score : ProofObj α → Nat) (clauses : ConnCNF α)
    (fuel topK : Nat) : ProofCollectionBundle α :=
  { proofs := collectProofsAll clauses fuel
  , topKProofs := topKCollectProofsAll score clauses fuel topK
  }

omit [DecidableEq α] in
theorem mem_insertProofByScore_iff
    (score : ProofObj α → Nat) (p x : ProofObj α) (ps : List (ProofObj α)) :
    x ∈ insertProofByScore score p ps ↔ x = p ∨ x ∈ ps := by
  induction ps with
  | nil =>
      simp [insertProofByScore]
  | cons h t ih =>
      by_cases hge : score p >= score h
      · simp [insertProofByScore, hge]
      · simp [insertProofByScore, hge, ih]
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

omit [DecidableEq α] in
theorem mem_sortProofsDescByScore_iff
    (score : ProofObj α → Nat) (x : ProofObj α) (ps : List (ProofObj α)) :
    x ∈ sortProofsDescByScore score ps ↔ x ∈ ps := by
  induction ps with
  | nil =>
      simp [sortProofsDescByScore]
  | cons h t ih =>
      simp [sortProofsDescByScore, mem_insertProofByScore_iff, ih]

omit [DecidableEq α] in
theorem mem_topKProofsByScore_implies_mem
    (score : ProofObj α → Nat) {proofs : List (ProofObj α)} {topK : Nat}
    {p : ProofObj α}
    (h : p ∈ topKProofsByScore score proofs topK) :
    p ∈ proofs := by
  have hSort : p ∈ sortProofsDescByScore score proofs := List.mem_of_mem_take h
  exact (mem_sortProofsDescByScore_iff score p proofs).1 hSort

omit [DecidableEq α] in
theorem length_topKProofsByScore_le
    (score : ProofObj α → Nat) (proofs : List (ProofObj α)) (topK : Nat) :
    (topKProofsByScore score proofs topK).length ≤ topK := by
  simp [topKProofsByScore]

omit [DecidableEq α] in
theorem topKProofsByScore_eq_sorted_of_len_le
    (score : ProofObj α → Nat) {proofs : List (ProofObj α)} {topK : Nat}
    (hLen : (sortProofsDescByScore score proofs).length ≤ topK) :
    topKProofsByScore score proofs topK = sortProofsDescByScore score proofs := by
  simpa [topKProofsByScore] using
    (List.take_eq_self_iff (sortProofsDescByScore score proofs)).2 hLen

theorem mem_topKCollectProofs_implies_mem_collectProofs
    (score : ProofObj α → Nat) {clauses : ConnCNF α} {fuel topK : Nat}
    {p : ProofObj α}
    (h : p ∈ topKCollectProofs score clauses fuel topK) :
    p ∈ collectProofs clauses fuel := by
  exact mem_topKProofsByScore_implies_mem score h

theorem mem_topKCollectProofsAll_implies_mem_collectProofsAll
    (score : ProofObj α → Nat) {clauses : ConnCNF α} {fuel topK : Nat}
    {p : ProofObj α}
    (h : p ∈ topKCollectProofsAll score clauses fuel topK) :
    p ∈ collectProofsAll clauses fuel := by
  exact mem_topKProofsByScore_implies_mem score h

theorem length_topKCollectProofsAll_le
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (topKCollectProofsAll score clauses fuel topK).length ≤ topK := by
  exact length_topKProofsByScore_le score (collectProofsAll clauses fuel) topK

/-- Contract parity: bundle proofs field is exactly root-wise proof collection. -/
theorem rootProofBundle_proofs_eq_collectProofs
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (rootProofBundle score clauses fuel topK).proofs = collectProofs clauses fuel := rfl

/-- Contract parity: bundle topK field is exactly root-wise topK projection. -/
theorem rootProofBundle_topK_eq_topKCollectProofs
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (rootProofBundle score clauses fuel topK).topKProofs =
      topKCollectProofs score clauses fuel topK := rfl

/-- Contract parity: branch-complete bundle proofs field matches `collectProofsAll`. -/
theorem branchProofBundle_proofs_eq_collectProofsAll
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (branchProofBundle score clauses fuel topK).proofs = collectProofsAll clauses fuel := rfl

/-- Contract parity: branch-complete bundle topK field matches `topKCollectProofsAll`. -/
theorem branchProofBundle_topK_eq_topKCollectProofsAll
    (score : ProofObj α → Nat) (clauses : ConnCNF α) (fuel topK : Nat) :
    (branchProofBundle score clauses fuel topK).topKProofs =
      topKCollectProofsAll score clauses fuel topK := rfl

/-- Bundle-level topK membership always comes from bundle-level branch-complete proofs. -/
theorem mem_branchProofBundle_topK_implies_mem_branchProofBundle_proofs
    (score : ProofObj α → Nat) {clauses : ConnCNF α} {fuel topK : Nat}
    {p : ProofObj α}
    (h : p ∈ (branchProofBundle score clauses fuel topK).topKProofs) :
    p ∈ (branchProofBundle score clauses fuel topK).proofs := by
  simpa [branchProofBundle] using
    (mem_topKCollectProofsAll_implies_mem_collectProofsAll
      (score := score) (clauses := clauses) (fuel := fuel) (topK := topK) (p := p) h)

omit [DecidableEq α] in

theorem mem_wrapTracesAsProofs_of_mem
    {fuel : Nat} {root : ConnClause α}
    {tr : ProofTrace α} {trs : List (ProofTrace α)}
    (h : tr ∈ trs) :
    ({ fuel := fuel, root := root, trace := tr } : ProofObj α) ∈ wrapTracesAsProofs fuel root trs := by
  unfold wrapTracesAsProofs
  exact List.mem_map.mpr ⟨tr, h, rfl⟩


theorem rootProof_mem_rootProofsAll_of_some
    {clauses : ConnCNF α} {root : ConnClause α} {fuel : Nat} {p : ProofObj α}
    (h : rootProof clauses root fuel = some p) :
    p ∈ rootProofsAll clauses root fuel := by
  unfold rootProof at h
  cases hConn : connProveDFS clauses root [] fuel with
  | none =>
      simp [hConn] at h
  | some tr =>
      have hp : ({ fuel := fuel, root := root, trace := tr } : ProofObj α) = p := by
        simpa [hConn] using h
      subst hp
      unfold rootProofsAll
      exact mem_wrapTracesAsProofs_of_mem
        (connProveDFS_some_mem_connProveAll
          (clauses := clauses) fuel root [] tr hConn)

theorem rootProofsAll_mem_collectRootProofsAll_of_mem_root
    {clauses roots : ConnCNF α} {fuel : Nat}
    {root : ConnClause α} {p : ProofObj α}
    (hRoot : root ∈ roots)
    (hp : p ∈ rootProofsAll clauses root fuel) :
    p ∈ collectRootProofsAll clauses fuel roots := by
  induction roots generalizing root p with
  | nil =>
      cases hRoot
  | cons r rs ih =>
      simp [collectRootProofsAll] at hRoot ⊢
      cases hRoot with
      | inl hr =>
          subst hr
          exact Or.inl hp
      | inr hTail =>
          exact Or.inr (ih hTail hp)

theorem proof_mem_collectProofsAll_of_root_mem_trace_mem
    {clauses : ConnCNF α} {root : ConnClause α}
    {fuel : Nat} {tr : ProofTrace α}
    (hRoot : root ∈ clauses)
    (hTr : tr ∈ connProveAll clauses root [] fuel) :
    ({ fuel := fuel, root := root, trace := tr } : ProofObj α) ∈ collectProofsAll clauses fuel := by
  unfold collectProofsAll
  exact rootProofsAll_mem_collectRootProofsAll_of_mem_root
    (clauses := clauses) (roots := clauses) (fuel := fuel)
    (root := root)
    hRoot
    (mem_wrapTracesAsProofs_of_mem hTr)

/--
Mode monotonicity (PeTTa parity):
root-wise collection is included in branch-complete collection at the same fuel.
-/
theorem collectRootProofs_subset_collectRootProofsAll
    (clauses : ConnCNF α) (fuel : Nat) :
    ∀ roots p,
      p ∈ collectRootProofs clauses fuel roots →
      p ∈ collectRootProofsAll clauses fuel roots := by
  intro roots
  induction roots with
  | nil =>
      intro p hp
      simp [collectRootProofs] at hp
  | cons root tail ih =>
      intro p hp
      unfold collectRootProofs at hp
      cases hRoot : rootProof clauses root fuel with
      | none =>
          have hpTail : p ∈ collectRootProofs clauses fuel tail := by
            simpa [hRoot] using hp
          have hTailAll := ih p hpTail
          exact List.mem_append.mpr <| Or.inr (by simpa [collectRootProofsAll] using hTailAll)
      | some pr =>
          have hsplit : p = pr ∨ p ∈ collectRootProofs clauses fuel tail := by
            simpa [hRoot] using hp
          cases hsplit with
          | inl hpEq =>
              subst hpEq
              have hInRoot : p ∈ rootProofsAll clauses root fuel :=
                rootProof_mem_rootProofsAll_of_some (clauses := clauses) (root := root) (fuel := fuel)
                  (p := p) hRoot
              exact List.mem_append.mpr <| Or.inl (by simpa [collectRootProofsAll] using hInRoot)
          | inr hpTail =>
              have hTailAll := ih p hpTail
              exact List.mem_append.mpr <| Or.inr (by simpa [collectRootProofsAll] using hTailAll)

theorem collectProofs_subset_collectProofsAll
    (clauses : ConnCNF α) (fuel : Nat) :
    ∀ p, p ∈ collectProofs clauses fuel → p ∈ collectProofsAll clauses fuel := by
  intro p hp
  simpa [collectProofs, collectProofsAll] using
    (collectRootProofs_subset_collectRootProofsAll
      (clauses := clauses) (fuel := fuel) (roots := clauses) p hp)

theorem collectRootProofsAll_checked (clauses roots : ConnCNF α) (fuel : Nat)
    (subset : ∀ root ∈ roots, root ∈ clauses) :
    ∀ proof ∈ collectRootProofsAll clauses fuel roots, checkProof clauses proof = true := by
  induction roots with
  | nil => exact fun _ member => False.elim (List.not_mem_nil member)
  | cons root rest earlier =>
      intro proof member
      rcases List.mem_append.mp member with atRoot | later
      · obtain ⟨trace, traceMember, rfl⟩ := List.mem_map.mp atRoot
        have replayed := replay_true_of_traceDerivable clauses root [] trace (connProveAll_sound_of_mem traceMember)
        simp only [checkProof, subset root List.mem_cons_self, decide_true, replayed, Bool.and_self]
      · exact earlier (fun other selected => subset other (List.mem_cons_of_mem _ selected)) proof later

theorem mem_collectProofsAll_checkProof_true {clauses : ConnCNF α} {fuel : Nat} {proof : ProofObj α}
    (member : proof ∈ collectProofsAll clauses fuel) : checkProof clauses proof = true :=
  collectRootProofsAll_checked clauses clauses fuel (fun _ selected => selected) proof member

theorem mem_collectProofs_checkProof_true {clauses : ConnCNF α} {fuel : Nat} {proof : ProofObj α}
    (member : proof ∈ collectProofs clauses fuel) : checkProof clauses proof = true :=
  mem_collectProofsAll_checkProof_true (collectProofs_subset_collectProofsAll clauses fuel proof member)

theorem mem_collectProofsAll_unsatisfiable {clauses : ConnCNF α} {fuel : Nat} {proof : ProofObj α}
    (member : proof ∈ collectProofsAll clauses fuel) : ∀ valuation : α → Bool, ¬ ConnSatisfies valuation clauses :=
  checkProof_unsatisfiable clauses proof (mem_collectProofsAll_checkProof_true member)

theorem mem_topKCollectProofs_checkProof_true (score : ProofObj α → Nat)
    {clauses : ConnCNF α} {fuel topK : Nat} {proof : ProofObj α}
    (member : proof ∈ topKCollectProofs score clauses fuel topK) : checkProof clauses proof = true :=
  mem_collectProofs_checkProof_true (mem_topKCollectProofs_implies_mem_collectProofs score member)

theorem mem_topKCollectProofsAll_checkProof_true (score : ProofObj α → Nat)
    {clauses : ConnCNF α} {fuel topK : Nat} {proof : ProofObj α}
    (member : proof ∈ topKCollectProofsAll score clauses fuel topK) : checkProof clauses proof = true :=
  mem_collectProofsAll_checkProof_true (mem_topKCollectProofsAll_implies_mem_collectProofsAll score member)

/-! ## Canary fixtures matching PeTTa-style proof objects -/

section Canary

abbrev cPos (a : α) : ConnClause α := [Lit.pos a]
abbrev cNeg (a : α) : ConnClause α := [Lit.neg a]

variable (pAtom : α)

def unsatClauses : ConnCNF α := [cPos pAtom, cNeg pAtom]

def unsatWitnessTrace : ProofTrace α :=
  [.step_extend (Lit.pos pAtom) (cNeg pAtom)]

def unsatWitnessProof : ProofObj α :=
  { fuel := 1, root := cPos pAtom, trace := unsatWitnessTrace pAtom }

theorem canary_unsat_ground_checkProof_true :
    checkProof (clauses := unsatClauses pAtom) (unsatWitnessProof pAtom) = true := by
  unfold checkProof unsatWitnessProof unsatWitnessTrace unsatClauses cPos cNeg replay replayAgenda connectionGoals
  simp [Lit.complement]
  simp [replayAgenda]

theorem canary_forged_reduce_rejected :
    checkProof
      (clauses := unsatClauses pAtom)
      ({ fuel := 1
       , root := cPos pAtom
       , trace := [.step_reduce (Lit.pos pAtom)] } : ProofObj α)
      = false := by
  unfold checkProof unsatClauses cPos cNeg replay replayAgenda connectionGoals
  simp [Lit.complement]

theorem canary_singleton_not_checkable :
    ¬ ∃ p : ProofObj α, checkProof ([cPos pAtom] : ConnCNF α) p = true := by
  rintro ⟨proof, checked⟩
  apply checkProof_unsatisfiable [cPos pAtom] proof checked (fun _ => true)
  intro clause member
  have same := List.mem_singleton.mp member
  subst clause
  exact ⟨Lit.pos pAtom, List.mem_singleton_self _, rfl⟩

end Canary

/-! ## PeTTa Fixture Map (test_leancop_* parity names) -/

section PeTTaFixtureMap

inductive FixtureAtom where
  | p | q
  deriving DecidableEq, Repr

open FixtureAtom

def ic_unsat_c1 : ConnClause FixtureAtom := [Lit.pos p]
def ic_unsat_c2 : ConnClause FixtureAtom := [Lit.neg p]
def ic_unsat_clauses : ConnCNF FixtureAtom := [ic_unsat_c1, ic_unsat_c2]
def ic_unsat_root : ConnClause FixtureAtom := ic_unsat_c1

def ic_sat_clauses : ConnCNF FixtureAtom := [ic_unsat_c1]
def ic_sat_root : ConnClause FixtureAtom := ic_unsat_c1

def ic_branching_c1 : ConnClause FixtureAtom := [Lit.pos p, Lit.pos q]
def ic_branching_c2 : ConnClause FixtureAtom := [Lit.neg p]
def ic_branching_c3 : ConnClause FixtureAtom := [Lit.neg q]
def ic_branching_clauses : ConnCNF FixtureAtom :=
  [ic_branching_c1, ic_branching_c2, ic_branching_c3]

def ic_branching_root_negp : ConnClause FixtureAtom := ic_branching_c2
def ic_branching_root_negq : ConnClause FixtureAtom := ic_branching_c3

def ic_unsat_proof : ProofObj FixtureAtom where
  fuel := 2
  root := ic_unsat_root
  trace := [.step_extend (Lit.pos p) ic_unsat_c2]

def ic_branching_negp_proof : ProofObj FixtureAtom where
  fuel := 3
  root := ic_branching_root_negp
  trace := [.step_extend (Lit.neg p) ic_branching_c1,
            .step_extend (Lit.pos q) ic_branching_c3]

def ic_branching_negq_proof : ProofObj FixtureAtom where
  fuel := 3
  root := ic_branching_root_negq
  trace := [.step_extend (Lit.neg q) ic_branching_c1,
            .step_extend (Lit.pos p) ic_branching_c2]

theorem ic_unsat_checkProof_true :
    checkProof ic_unsat_clauses ic_unsat_proof = true := by
  decide

theorem ic_sat_connProve_none :
    ∀ fuel, connProveDFS ic_sat_clauses ic_sat_root [] fuel = none := by
  intro fuel
  cases fuel with
  | zero =>
      simp [connProveDFS, connProveAgendaDFS, connectionGoals, ic_sat_root, ic_unsat_c1]
  | succ n =>
      simp [connProveDFS, connProveAgendaDFS, connectionGoals, ic_sat_root, ic_sat_clauses, ic_unsat_c1, tryExtendWith, Lit.complement]

theorem ic_unsat_connProve_has_proof :
    ∃ tr, connProveDFS ic_unsat_clauses ic_unsat_root [] 2 = some tr := by
  refine ⟨ic_unsat_proof.trace, ?_⟩
  decide

theorem ic_branching_negp_checkProof_true :
    checkProof ic_branching_clauses ic_branching_negp_proof = true := by
  decide

theorem ic_branching_negq_checkProof_true :
    checkProof ic_branching_clauses ic_branching_negq_proof = true := by
  decide

theorem ic_branching_two_distinct_root_proofs :
    ic_branching_root_negp ≠ ic_branching_root_negq
      ∧ checkProof ic_branching_clauses ic_branching_negp_proof = true
      ∧ checkProof ic_branching_clauses ic_branching_negq_proof = true := by
  decide

theorem ic_branching_negp_connProve_has_proof :
    ∃ tr, connProveDFS ic_branching_clauses ic_branching_root_negp [] 3 = some tr := by
  have hChk : checkProof ic_branching_clauses ic_branching_negp_proof = true := by
    decide
  have hTrace : TraceDerivable ic_branching_clauses ic_branching_root_negp [] ic_branching_negp_proof.trace :=
    (checkProof_true_iff_root_mem_and_traceDerivable
      (clauses := ic_branching_clauses) (p := ic_branching_negp_proof)).1 hChk |>.2
  simpa [ic_branching_negp_proof] using
    connProveDFS_complete_of_trace
      (clauses := ic_branching_clauses)
      (goals := ic_branching_root_negp) (path := [])
      (trace := ic_branching_negp_proof.trace) (fuel := 3)
      hTrace (by decide)

theorem ic_branching_negq_connProve_has_proof :
    ∃ tr, connProveDFS ic_branching_clauses ic_branching_root_negq [] 3 = some tr := by
  have hChk : checkProof ic_branching_clauses ic_branching_negq_proof = true := by
    decide
  have hTrace : TraceDerivable ic_branching_clauses ic_branching_root_negq [] ic_branching_negq_proof.trace :=
    (checkProof_true_iff_root_mem_and_traceDerivable
      (clauses := ic_branching_clauses) (p := ic_branching_negq_proof)).1 hChk |>.2
  simpa [ic_branching_negq_proof] using
    connProveDFS_complete_of_trace
      (clauses := ic_branching_clauses)
      (goals := ic_branching_root_negq) (path := [])
      (trace := ic_branching_negq_proof.trace) (fuel := 3)
      hTrace (by decide)

/-- Fixture-level parity: root-wise proofs are included in branch-complete proofs (unsat case). -/
theorem ic_unsat_collectProofs_subset_collectProofsAll :
    ∀ p, p ∈ collectProofs ic_unsat_clauses 2 → p ∈ collectProofsAll ic_unsat_clauses 2 := by
  intro p hp
  exact collectProofs_subset_collectProofsAll (clauses := ic_unsat_clauses) (fuel := 2) p hp

/-- Fixture-level parity: root-wise proofs are included in branch-complete proofs (branching case). -/
theorem ic_branching_collectProofs_subset_collectProofsAll :
    ∀ p, p ∈ collectProofs ic_branching_clauses 3 → p ∈ collectProofsAll ic_branching_clauses 3 := by
  intro p hp
  exact collectProofs_subset_collectProofsAll (clauses := ic_branching_clauses) (fuel := 3) p hp

/--
Branch-complete fixture parity:
`collectProofsAll` contains proofs for both distinct branching roots.
-/
theorem ic_branching_collectProofsAll_two_distinct_roots :
    ∃ p1 p2 : ProofObj FixtureAtom,
      p1.root ≠ p2.root
        ∧ p1 ∈ collectProofsAll ic_branching_clauses 3
        ∧ p2 ∈ collectProofsAll ic_branching_clauses 3 := by
  rcases ic_branching_negp_connProve_has_proof with ⟨tr1, h1⟩
  rcases ic_branching_negq_connProve_has_proof with ⟨tr2, h2⟩
  let p1 : ProofObj FixtureAtom := { fuel := 3, root := ic_branching_root_negp, trace := tr1 }
  let p2 : ProofObj FixtureAtom := { fuel := 3, root := ic_branching_root_negq, trace := tr2 }
  refine ⟨p1, p2, ?_, ?_, ?_⟩
  · intro hEq
    have hRootEq : ic_branching_root_negp = ic_branching_root_negq := by
      simpa [p1, p2] using hEq
    exact (by decide : ic_branching_root_negp ≠ ic_branching_root_negq) hRootEq
  · have hTr1 : tr1 ∈ connProveAll ic_branching_clauses ic_branching_root_negp [] 3 :=
      connProveDFS_some_mem_connProveAll
        (clauses := ic_branching_clauses) 3 ic_branching_root_negp [] tr1 h1
    simpa [p1] using
      (proof_mem_collectProofsAll_of_root_mem_trace_mem
        (clauses := ic_branching_clauses)
        (root := ic_branching_root_negp) (fuel := 3) (tr := tr1)
        (by decide) hTr1)
  · have hTr2 : tr2 ∈ connProveAll ic_branching_clauses ic_branching_root_negq [] 3 :=
      connProveDFS_some_mem_connProveAll
        (clauses := ic_branching_clauses) 3 ic_branching_root_negq [] tr2 h2
    simpa [p2] using
      (proof_mem_collectProofsAll_of_root_mem_trace_mem
        (clauses := ic_branching_clauses)
        (root := ic_branching_root_negq) (fuel := 3) (tr := tr2)
        (by decide) hTr2)

end PeTTaFixtureMap

end PropositionalConnection

end Mettapedia.Logic.LP
