import Mettapedia.Logic.LP.SLDCompletenessKit

/-!
# Logic Programming Kernel: Completeness Canaries

Concrete finite fixtures exercising the semantic completeness endpoint
`sldQuery_complete_of_semantic_lift` through `NullaryFactOnlyKB`.
-/

namespace Mettapedia.Logic.LP

namespace Canaries

/-! ## Fixture signature -/

inductive CConst where
  | c0
  deriving DecidableEq

inductive CVar where
  | x
  deriving DecidableEq

inductive CRel where
  | p
  | q
  deriving DecidableEq

inductive CFun where
  deriving DecidableEq

instance : IsEmpty CFun := ⟨by intro f; cases f⟩

def cSig : LPSignature where
  constants := CConst
  vars := CVar
  relationSymbols := CRel
  relationArity := fun _ => 0
  functionSymbols := CFun
  functionArity := fun f => nomatch f

instance : DecidableEq cSig.vars := by
  intro a b
  cases a
  cases b
  exact isTrue rfl

instance : DecidableEq cSig.constants := by
  intro a b
  cases a
  cases b
  exact isTrue rfl

instance : DecidableEq cSig.functionSymbols := by
  intro a
  cases a

instance : DecidableEq cSig.relationSymbols := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

def atomP : Atom cSig where
  symbol := .p
  args := fun i => nomatch i

def atomQ : Atom cSig where
  symbol := .q
  args := fun i => nomatch i

def factP : Clause cSig where
  head := atomP
  body := []

def factQ : Clause cSig where
  head := atomQ
  body := []

def rulePfromQ : Clause cSig where
  head := atomP
  body := [atomQ]

def kbP : KnowledgeBase cSig where
  prog := [factP]
  db := ∅

def kbPQ : KnowledgeBase cSig where
  prog := [rulePfromQ, factQ]
  db := ∅

def defaultGrounding : Grounding cSig := fun _ => .const .c0

def gaP : GroundAtom cSig := defaultGrounding.groundAtom factP.head

def gaQ : GroundAtom cSig := defaultGrounding.groundAtom factQ.head

theorem kbP_nullaryFactOnly : NullaryFactOnlyKB kbP := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    cases r <;> rfl
  · rfl
  · intro c hc
    simp [kbP, factP] at hc
    rcases hc with rfl
    rfl

theorem gaP_in_leastHerbrandModel_kbP : gaP ∈ leastHerbrandModel kbP := by
  refine leastHerbrandModel_clause kbP factP ?_ defaultGrounding ?_
  · simp [kbP]
  · intro b hb
    simp [factP] at hb

theorem kbPQ_nullaryUnaryBody : NullaryUnaryBodyKB kbPQ := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    cases r <;> rfl
  · rfl
  · intro c hc
    simp [kbPQ, rulePfromQ, factQ] at hc
    rcases hc with rfl | rfl
    · exact Or.inr ⟨atomQ, rfl⟩
    · exact Or.inl rfl

theorem gaQ_in_leastHerbrandModel_kbPQ : gaQ ∈ leastHerbrandModel kbPQ := by
  refine leastHerbrandModel_clause kbPQ factQ ?_ defaultGrounding ?_
  · simp [kbPQ]
  · intro b hb
    simp [factQ] at hb

theorem gaP_in_leastHerbrandModel_kbPQ : gaP ∈ leastHerbrandModel kbPQ := by
  refine leastHerbrandModel_clause kbPQ rulePfromQ ?_ defaultGrounding ?_
  · simp [kbPQ]
  · intro b hb
    simp [rulePfromQ] at hb
    rcases hb with rfl
    simpa [gaQ] using gaQ_in_leastHerbrandModel_kbPQ

/-- Positive canary: semantic completeness endpoint derives executable success
for the ground fact present in the least Herbrand model. -/
theorem canary_complete_queryP :
    ∃ fuel : ℕ, ∃ θ : Subst cSig, sldQuery kbP.prog gaP.toAtom fuel = some θ := by
  exact sldQuery_complete_of_nullaryFactOnly kbP kbP_nullaryFactOnly gaP_in_leastHerbrandModel_kbP

/-- Bundle canary: completeness+soundness endpoint for the same fixture. -/
theorem canary_complete_sound_queryP :
    ∃ fuel : ℕ, ∃ θ : Subst cSig,
      sldQuery kbP.prog gaP.toAtom fuel = some θ ∧
      ∀ g : Grounding cSig,
        (g.compSubst θ).groundAtom gaP.toAtom ∈ leastHerbrandModel kbP := by
  exact sldQuery_complete_sound_bundle_of_nullaryFactOnly
    kbP kbP_nullaryFactOnly gaP_in_leastHerbrandModel_kbP

/-- Negative canary: with only `p` facts/rules, querying `q` always fails
for executable search (completeness boundary sanity check). -/
theorem canary_negative_queryQ_fails (fuel : ℕ) :
    sldQuery kbP.prog atomQ fuel = none := by
  cases fuel with
  | zero =>
      simp [sldQuery, sldSearch]
  | succ n =>
      simp [sldQuery, sldSearch, kbP, factP, atomP, atomQ, unifyAtoms]

/-- Positive canary for the non-empty-body kit (`p :- q`, `q.`): completeness
finds executable success for `p` through a unary-body rule chain. -/
theorem canary_complete_queryP_via_unaryBody :
    ∃ fuel : ℕ, ∃ θ : Subst cSig, sldQuery kbPQ.prog gaP.toAtom fuel = some θ := by
  exact sldQuery_complete_of_nullaryUnaryBody
    kbPQ kbPQ_nullaryUnaryBody gaP_in_leastHerbrandModel_kbPQ

/-- Negative boundary canary for the unary-body fixture: insufficient fuel
prevents success even though the query is semantically derivable. -/
theorem canary_negative_unaryBody_insufficientFuel :
    sldQuery kbPQ.prog gaP.toAtom 1 = none := by
  simp [sldQuery, sldSearch, kbPQ, gaP,
    factP, factQ, rulePfromQ, atomP, atomQ, unifyAtoms, unifyFuel]

end Canaries

end Mettapedia.Logic.LP
