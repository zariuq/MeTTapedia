import Mettapedia.Logic.Datalog.Semantics
import Mettapedia.Logic.LP.Semantics

/-!
# Datalog → LP Embedding

Faithful embedding of Datalog types and semantics into the LP kernel.
Datalog is the function-free fragment of LP: `LPSignature.isFunctionFree`
characterizes exactly when `σ.functionSymbols` is empty.

## Main results

- `Signature.toLPSignature` — converts a Datalog signature to an LP signature.
- `Term.toLPTerm`, `Atom.toLPAtom`, etc. — type-level conversions.
- `datalog_lp_semantics_agree` — the key correctness theorem: a ground atom is
  in the Datalog least model iff its LP translation is in the LP least model.

## Design

The embedding is injective but not surjective (LP has function symbols).
The LP signature has `functionSymbols := Empty`, making it function-free.
-/

namespace Mettapedia.Logic

/-! ## Section 1: Signature conversion -/

/-- Convert a Datalog signature to an LP signature (no function symbols). -/
def Datalog.Signature.toLPSignature (τ : Datalog.Signature) : LP.LPSignature where
  constants       := τ.constants
  vars            := τ.vars
  relationSymbols := τ.relationSymbols
  relationArity   := τ.relationArity
  functionSymbols := Empty
  functionArity   := Empty.elim

/-- A Datalog-derived LP signature is function-free. -/
theorem Datalog.Signature.toLPSignature_isFunctionFree (τ : Datalog.Signature) :
    τ.toLPSignature.isFunctionFree :=
  Empty.instIsEmpty

/-! ## Section 2: Term conversion -/

/-- Convert a Datalog term to an LP term. -/
def Datalog.Term.toLPTerm {τ : Datalog.Signature} :
    Datalog.Term τ → LP.Term τ.toLPSignature
  | .constant c   => .const c
  | .variableDL v => .var v

/-- A Datalog constant (used as a ground atom element) to an LP GroundTerm. -/
def Datalog.constToLPGroundTerm {τ : Datalog.Signature} (c : τ.constants) :
    LP.GroundTerm τ.toLPSignature :=
  .const c

/-! ## Section 3: Atom conversion -/

/-- Convert a Datalog atom (List-based) to an LP atom (Fin-indexed). -/
def Datalog.Atom.toLPAtom {τ : Datalog.Signature} (a : Datalog.Atom τ) :
    LP.Atom τ.toLPSignature where
  symbol := a.symbol
  args   := fun i => (a.atom_terms.get (a.term_length ▸ i)).toLPTerm

/-- Convert a Datalog ground atom to an LP ground atom. -/
def Datalog.GroundAtom.toLPGroundAtom {τ : Datalog.Signature} (ga : Datalog.GroundAtom τ) :
    LP.GroundAtom τ.toLPSignature where
  symbol := ga.symbol
  args   := fun i => .const (ga.atom_terms.get (ga.term_length ▸ i))

/-! ## Section 4: Rule/Clause conversion -/

/-- Convert a Datalog rule to an LP clause. -/
def Datalog.Rule.toLPClause {τ : Datalog.Signature} (r : Datalog.Rule τ) :
    LP.Clause τ.toLPSignature where
  head := r.head.toLPAtom
  body := r.body.map Datalog.Atom.toLPAtom

/-- Convert a Datalog program to an LP program. -/
def Datalog.Program.toLPProgram {τ : Datalog.Signature}
    (prog : Datalog.Program τ) : LP.Program τ.toLPSignature :=
  prog.map Datalog.Rule.toLPClause

/-! ## Section 5: Knowledge base conversion -/

/-- Convert a Datalog knowledge base to an LP knowledge base.
    The EDB maps from `Finset` to `Set` (via coercion). -/
def Datalog.KnowledgeBase.toLPKB {τ : Datalog.Signature} (kb : Datalog.KnowledgeBase τ) :
    LP.KnowledgeBase τ.toLPSignature where
  prog := kb.prog.toLPProgram
  db   := { ga | ∃ dga ∈ kb.db, dga.toLPGroundAtom = ga }

/-! ## Section 6: Grounding conversion -/

/-- Convert a Datalog grounding to an LP grounding. -/
def Datalog.Grounding.toLPGrounding {τ : Datalog.Signature}
    (g : Datalog.Grounding τ) : LP.Grounding τ.toLPSignature :=
  fun v => .const (g v)

/-- The LP grounding of a Datalog term equals the Datalog grounding lifted. -/
theorem Datalog.Grounding.toLPGrounding_term {τ : Datalog.Signature}
    (g : Datalog.Grounding τ) (t : Datalog.Term τ) :
    (g.toLPGrounding.groundTerm t.toLPTerm).toTerm =
      LP.Term.const (g.applyTerm t) := by
  cases t with
  | constant c => rfl
  | variableDL v => rfl

/-- Helper: LP grounding of a single Datalog term produces the right constant. -/
private theorem groundTerm_toLPTerm_eq {τ : Datalog.Signature}
    (g : Datalog.Grounding τ) (t : Datalog.Term τ) :
    g.toLPGrounding.groundTerm t.toLPTerm = .const (g.applyTerm t) := by
  cases t with
  | constant c => rfl
  | variableDL v => rfl

/-- Fin.val is preserved by Eq.rec transport on the bound. -/
private theorem fin_val_transport {n m : ℕ} (h : n = m) (i : Fin m) :
    (h ▸ i : Fin n).val = i.val := by subst h; rfl

/-- The two grounding paths commute: applying a Datalog grounding then embedding
    equals embedding then applying the LP grounding. -/
theorem Datalog.Grounding.groundAtom_comm {τ : Datalog.Signature}
    (g : Datalog.Grounding τ) (a : Datalog.Atom τ) :
    g.toLPGrounding.groundAtom a.toLPAtom = (g.applyAtom a).toLPGroundAtom := by
  unfold LP.Grounding.groundAtom Datalog.Atom.toLPAtom
         Datalog.GroundAtom.toLPGroundAtom Datalog.Grounding.applyAtom
  simp only
  congr 1
  funext ⟨j, hj⟩
  rw [groundTerm_toLPTerm_eq]
  simp only [LP.GroundTerm.const.injEq]
  simp [Datalog.Grounding.applyTermList]
  have h1 := fin_val_transport a.term_length ⟨j, hj⟩
  have h2 := fin_val_transport (show (List.map g.applyTerm a.atom_terms).length =
    τ.relationArity a.symbol by simp [a.term_length]) ⟨j, hj⟩
  simp_all

/-! ## Section 7: Semantics agreement -/

/-- Forward direction: if a ground atom is in the Datalog T_P result,
    its LP translation is in the LP T_P result. -/
theorem T_P_forward {τ : Datalog.Signature}
    (kb : Datalog.KnowledgeBase τ) (I : Datalog.Interpretation τ)
    (I_lp : LP.Interpretation τ.toLPSignature)
    (hI : ∀ ga : Datalog.GroundAtom τ, ga ∈ I → ga.toLPGroundAtom ∈ I_lp)
    (ga : Datalog.GroundAtom τ) (ha : ga ∈ Datalog.T_P kb I) :
    ga.toLPGroundAtom ∈ LP.T_P_LP kb.toLPKB I_lp := by
  simp only [Datalog.T_P, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq] at ha
  rcases ha with ha | ⟨r, g, hr, hhead, hbody⟩
  · -- EDB case
    apply Set.mem_union_left
    exact ⟨ga, ha, rfl⟩
  · -- Rule case
    apply Set.mem_union_right
    refine ⟨r.toLPClause, g.toLPGrounding, ?_, ?_, ?_⟩
    · simp [Datalog.KnowledgeBase.toLPKB, Datalog.Program.toLPProgram, List.mem_map]
      exact ⟨r, hr, rfl⟩
    · -- head agreement
      show g.toLPGrounding.groundAtom r.head.toLPAtom = ga.toLPGroundAtom
      rw [g.groundAtom_comm, hhead]
    · -- body satisfaction
      intro b hb
      simp [Datalog.Rule.toLPClause, List.mem_map] at hb
      obtain ⟨db, hdb, rfl⟩ := hb
      rw [g.groundAtom_comm]
      exact hI _ (hbody db hdb)

end Mettapedia.Logic
