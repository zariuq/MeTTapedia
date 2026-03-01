import Mettapedia.Logic.LP.SLDCompute
import Mettapedia.Logic.LP.UnificationComplete

/-!
# Logic Programming Kernel: Completeness Lift Kits

Reusable packaging for the `hBase` / `hRule` obligations used by
`sldQuery_complete_of_semantic_lift`, plus a concrete canonical kit for a
simple concrete KB class (nullary fact-only programs).
-/

namespace Mettapedia.Logic.LP

/-- Bundle of witness-lifting obligations for a fixed knowledge base. -/
structure SLDWitnessLiftKit {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) where
  hBase : ∀ ga : GroundAtom σ, ga ∈ kb.db →
    ∃ fuel : ℕ, SLDWitness kb.prog fuel [ga.toAtom]
  hRule : ∀ c : Clause σ, ∀ γ : Grounding σ, c ∈ kb.prog →
    (∀ b ∈ c.body, ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom]) →
    ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom c.head).toAtom]

/-- Canonical one-call completeness endpoint from a lift kit. -/
theorem sldQuery_complete_of_kit {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    {kb : KnowledgeBase σ} (kit : SLDWitnessLiftKit kb)
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, sldQuery kb.prog ga.toAtom fuel = some θ :=
  sldQuery_complete_of_semantic_lift kb kit.hBase kit.hRule ha

/-- Canonical one-call soundness+completeness endpoint from a lift kit. -/
theorem sldQuery_complete_sound_bundle_of_kit {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    {kb : KnowledgeBase σ} (kit : SLDWitnessLiftKit kb)
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      sldQuery kb.prog ga.toAtom fuel = some θ ∧
      ∀ g : Grounding σ,
        (g.compSubst θ).groundAtom ga.toAtom ∈ leastHerbrandModel kb :=
  sldQuery_complete_sound_bundle_of_semantic_lift kb kit.hBase kit.hRule ha

/-- Concrete KB class: nullary predicates only, no EDB facts, and program
clauses are facts (`body = []`). -/
structure NullaryFactOnlyKB {σ : LPSignature} (kb : KnowledgeBase σ) : Prop where
  relationArity_zero : ∀ r : σ.relationSymbols, σ.relationArity r = 0
  db_empty : kb.db = ∅
  facts_only : ∀ c : Clause σ, c ∈ kb.prog → c.body = []

private theorem groundAtom_toAtom_eq_of_nullary {σ : LPSignature}
    (hNull : ∀ r : σ.relationSymbols, σ.relationArity r = 0)
    (γ : Grounding σ) (a : Atom σ) :
    (γ.groundAtom a).toAtom = a := by
  cases a with
  | mk sym args =>
      have h0 : σ.relationArity sym = 0 := hNull sym
      simp [Grounding.groundAtom, GroundAtom.toAtom]
      have hEmpty : IsEmpty (Fin (σ.relationArity sym)) := by
        refine ⟨?_⟩
        intro i
        have hi : i.1 < 0 := by
          simpa [h0] using i.2
        exact (Nat.not_lt_zero _ hi).elim
      funext i
      exact (hEmpty.false i).elim

private theorem unifyAtoms_groundHead_self_of_nullary_succ {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (hNull : ∀ r : σ.relationSymbols, σ.relationArity r = 0)
    (c : Clause σ) (γ : Grounding σ) (n : ℕ) :
    unifyAtoms (γ.groundAtom c.head).toAtom c.head (n + 1) = some (Subst.id σ) := by
  have hArity : σ.relationArity c.head.symbol = 0 := hNull c.head.symbol
  have hsym : (γ.groundAtom c.head).toAtom.symbol = c.head.symbol := rfl
  have hPairs :
      finPairsToList (γ.groundAtom c.head).toAtom.args (hsym ▸ c.head.args) = [] := by
    simpa [finPairsToList, hArity]
  simp [unifyAtoms, hsym, hPairs, unifyFuel]

private theorem sldWitness_nil_of_pos {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    {prog : Program σ} {fuel : ℕ} (hpos : 0 < fuel) :
    SLDWitness prog fuel [] := by
  cases fuel with
  | zero =>
      exact (Nat.not_lt_zero _ hpos).elim
  | succ n =>
      simpa using (SLDWitness.nil (prog := prog) n)

private theorem fuel_pos_of_unifyAtoms_some {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    {a b : Atom σ} {fuel : ℕ} {θ : Subst σ}
    (h : unifyAtoms a b fuel = some θ) :
    0 < fuel := by
  cases fuel with
  | zero =>
      simp [unifyAtoms, unifyFuel] at h
  | succ n =>
      simp

/-- Semantic-unifiability threaded through global unification completeness:
for nullary heads, executable `unifyAtoms` success exists. -/
private theorem unifyAtoms_groundHead_exists_of_nullary {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (hNull : ∀ r : σ.relationSymbols, σ.relationArity r = 0)
    (c : Clause σ) (γ : Grounding σ) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      unifyAtoms (γ.groundAtom c.head).toAtom c.head fuel = some θ := by
  have hArity : σ.relationArity c.head.symbol = 0 := hNull c.head.symbol
  have hsym : (γ.groundAtom c.head).toAtom.symbol = c.head.symbol := rfl
  let eqs : List (Term σ × Term σ) :=
    finPairsToList (γ.groundAtom c.head).toAtom.args (hsym ▸ c.head.args)
  have hPairs : eqs = [] := by
    simpa [eqs, finPairsToList, hArity]
  have hunif : ∃ δ : Subst σ, Unifies δ eqs := by
    refine ⟨Subst.id σ, ?_⟩
    intro p hp
    simp [hPairs] at hp
  rcases unifyFuel_exists_of_unifies (eqs := eqs) hunif with ⟨fuel, θ, hθ⟩
  refine ⟨fuel, θ, ?_⟩
  simp [unifyAtoms, hsym, eqs, hθ]

/-- Canonical lift kit for nullary fact-only KBs. -/
def nullaryFactOnlyKit {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (hNF : NullaryFactOnlyKB kb) :
    SLDWitnessLiftKit kb where
  hBase := by
    intro ga hga
    exfalso
    simp [hNF.db_empty] at hga
  hRule := by
    intro c γ hc _
    have hBodyNil : c.body = [] := hNF.facts_only c hc
    rcases unifyAtoms_groundHead_exists_of_nullary hNF.relationArity_zero c γ with
      ⟨fuelU, θu, hunif⟩
    have hnext :
        SLDWitness kb.prog fuelU (θu.applyAtoms (c.body ++ [])) := by
      have hpos : 0 < fuelU := fuel_pos_of_unifyAtoms_some hunif
      simpa [hBodyNil, Subst.applyAtoms] using
        (sldWitness_nil_of_pos (prog := kb.prog) hpos)
    refine ⟨fuelU + 1, ?_⟩
    have hw :
        SLDWitness kb.prog (fuelU + 1) ((γ.groundAtom c.head).toAtom :: []) :=
      SLDWitness.cons fuelU ((γ.groundAtom c.head).toAtom) [] c θu hc hunif hnext
    simpa using hw

/-- Concrete KB class: nullary predicates, no EDB facts, and each clause body
has at most one atom. -/
structure NullaryUnaryBodyKB {σ : LPSignature} (kb : KnowledgeBase σ) : Prop where
  relationArity_zero : ∀ r : σ.relationSymbols, σ.relationArity r = 0
  db_empty : kb.db = ∅
  body_nil_or_singleton : ∀ c : Clause σ, c ∈ kb.prog →
    c.body = [] ∨ ∃ b : Atom σ, c.body = [b]

/-- Canonical lift kit for nullary unary-body KBs (includes non-empty-body clauses). -/
def nullaryUnaryBodyKit {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (hNU : NullaryUnaryBodyKB kb) :
    SLDWitnessLiftKit kb where
  hBase := by
    intro ga hga
    exfalso
    simp [hNU.db_empty] at hga
  hRule := by
    intro c γ hc hBodies
    rcases hNU.body_nil_or_singleton c hc with hnil | ⟨b, hsingle⟩
    · have hunif :
          ∃ fuel : ℕ, ∃ θ : Subst σ,
            unifyAtoms (γ.groundAtom c.head).toAtom c.head fuel = some θ := by
        exact unifyAtoms_groundHead_exists_of_nullary hNU.relationArity_zero c γ
      rcases hunif with ⟨fuelU, θu, hunif⟩
      have hnext :
          SLDWitness kb.prog fuelU (θu.applyAtoms (c.body ++ [])) := by
        have hpos : 0 < fuelU := fuel_pos_of_unifyAtoms_some hunif
        simpa [hnil, Subst.applyAtoms] using
          (sldWitness_nil_of_pos (prog := kb.prog) hpos)
      refine ⟨fuelU + 1, ?_⟩
      have hw :
          SLDWitness kb.prog (fuelU + 1) ((γ.groundAtom c.head).toAtom :: []) :=
        SLDWitness.cons fuelU ((γ.groundAtom c.head).toAtom) [] c θu hc hunif hnext
      simpa using hw
    · have hbodyWitness :
          ∃ fuel : ℕ, SLDWitness kb.prog fuel [(γ.groundAtom b).toAtom] := by
        have hbmem : b ∈ c.body := by simp [hsingle]
        exact hBodies b hbmem
      rcases hbodyWitness with ⟨fuelB, hwB⟩
      cases fuelB with
      | zero =>
          cases hwB
      | succ n =>
          have hbEq : (γ.groundAtom b).toAtom = b :=
            groundAtom_toAtom_eq_of_nullary hNU.relationArity_zero γ b
          have hunif :
              unifyAtoms (γ.groundAtom c.head).toAtom c.head (n + 1) =
                some (Subst.id σ) := by
            exact unifyAtoms_groundHead_self_of_nullary_succ
              hNU.relationArity_zero c γ n
          have hnext :
              SLDWitness kb.prog (n + 1)
                ((Subst.id σ).applyAtoms (c.body ++ [])) := by
            simpa [hsingle, Subst.applyAtoms, hbEq] using hwB
          refine ⟨(n + 1) + 1, ?_⟩
          have hw :
              SLDWitness kb.prog ((n + 1) + 1)
                ((γ.groundAtom c.head).toAtom :: []) :=
            SLDWitness.cons (n + 1) ((γ.groundAtom c.head).toAtom) [] c
              (Subst.id σ) hc hunif hnext
          simpa using hw

/-- Completeness endpoint specialized to nullary unary-body KBs. -/
theorem sldQuery_complete_of_nullaryUnaryBody {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (hNU : NullaryUnaryBodyKB kb)
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, sldQuery kb.prog ga.toAtom fuel = some θ :=
  sldQuery_complete_of_kit (nullaryUnaryBodyKit kb hNU) ha

/-- Soundness+completeness endpoint specialized to nullary unary-body KBs. -/
theorem sldQuery_complete_sound_bundle_of_nullaryUnaryBody {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (hNU : NullaryUnaryBodyKB kb)
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      sldQuery kb.prog ga.toAtom fuel = some θ ∧
      ∀ g : Grounding σ,
        (g.compSubst θ).groundAtom ga.toAtom ∈ leastHerbrandModel kb :=
  sldQuery_complete_sound_bundle_of_kit (nullaryUnaryBodyKit kb hNU) ha

/-- Completeness endpoint specialized to nullary fact-only KBs. -/
theorem sldQuery_complete_of_nullaryFactOnly {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (hNF : NullaryFactOnlyKB kb)
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, sldQuery kb.prog ga.toAtom fuel = some θ :=
  sldQuery_complete_of_kit (nullaryFactOnlyKit kb hNF) ha

/-- Soundness+completeness endpoint specialized to nullary fact-only KBs. -/
theorem sldQuery_complete_sound_bundle_of_nullaryFactOnly {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) (hNF : NullaryFactOnlyKB kb)
    {ga : GroundAtom σ} (ha : ga ∈ leastHerbrandModel kb) :
    ∃ fuel : ℕ, ∃ θ : Subst σ,
      sldQuery kb.prog ga.toAtom fuel = some θ ∧
      ∀ g : Grounding σ,
        (g.compSubst θ).groundAtom ga.toAtom ∈ leastHerbrandModel kb :=
  sldQuery_complete_sound_bundle_of_kit (nullaryFactOnlyKit kb hNF) ha

end Mettapedia.Logic.LP
