import Mettapedia.Logic.LP.Core
import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.FunctionFree
import GFCore
import Mettapedia.Logic.EvidenceKind

/-!
# GFCoreLPBridge — Bridge from GFCore.Atom to LP Herbrand Model

Maps GF-parsed English (GFCore.Atom) to the LP kernel's ground atoms,
giving parsed text **model-theoretic semantics** via the least Herbrand model.

## Architecture

```
GF ParseEng → GFCore.Atom → atomToLP → LP.GroundAtom gfSig
                                              ↓
                                    KnowledgeBase gfSig
                                              ↓
                                    leastHerbrandModel
                                              ↓
                              Entailment = set membership
```

## Key properties

- **Function-free** (Datalog fragment): GroundTerm ≃ constants, decidable
- **Soundness**: EDB facts ∈ leastHerbrandModel (proven in LP/Semantics.lean)
- **Completeness**: leastHerbrandModel is the SMALLEST model (Tarski fixpoint)

## References

- van Emden & Kowalski, 1976 (T_P operator)
- Lloyd, Foundations of Logic Programming, Ch. 2 (least Herbrand model)
- Council session 2026-03-22 (GFCore→LP bridge design)
-/

namespace Mettapedia.Languages.GF

open Mettapedia.Logic.LP
open GFCore

-- ═══════════════════════════════════════════════════════════════════
-- Phase 1: LP Signature for GFCore
-- ═══════════════════════════════════════════════════════════════════

/-- Relation symbols for the GFCore LP signature.
    Each GFCore.Atom constructor maps to one or more relation symbols.
    Predicates are stratified by arity (standard Datalog practice). -/
inductive GFRelSym where
  | isa                                  -- arity 2: IsA(sub, sup)
  | pred (p : ConceptId) (arity : Nat)   -- arity n: Rel(p, [arg₁,...,argₙ])
  deriving Repr, BEq, Inhabited

instance : DecidableEq GFRelSym := by
  intro a b
  cases a with
  | isa =>
    cases b with
    | isa => exact isTrue rfl
    | pred _ _ => exact isFalse (fun h => GFRelSym.noConfusion h)
  | pred p1 n1 =>
    cases b with
    | isa => exact isFalse (fun h => GFRelSym.noConfusion h)
    | pred p2 n2 =>
      by_cases hp : p1 = p2
      · by_cases hn : n1 = n2
        · exact isTrue (by subst hp; subst hn; rfl)
        · exact isFalse (fun h => hn (by cases h; rfl))
      · exact isFalse (fun h => hp (by cases h; rfl))

/-- Arity of each GFCore relation symbol. -/
def gfRelArity : GFRelSym → Nat
  | .isa => 2
  | .pred _ n => n

/-- The LP signature for GFCore ground atoms.
    Function-free (Datalog fragment): no compound terms, only constants. -/
def gfSig : LPSignature where
  constants       := ConceptId
  vars            := String
  relationSymbols := GFRelSym
  relationArity   := gfRelArity
  functionSymbols := Empty
  functionArity   := Empty.elim

instance : IsEmpty gfSig.functionSymbols := Empty.instIsEmpty
instance : DecidableEq gfSig.vars := inferInstanceAs (DecidableEq String)
instance : DecidableEq gfSig.constants := inferInstanceAs (DecidableEq ConceptId)

-- ═══════════════════════════════════════════════════════════════════
-- Phase 2: Flatten GFCore.Term → LP Constant
-- ═══════════════════════════════════════════════════════════════════

/-- Flatten a structured GFCore.Term to its head ConceptId.
    Loses modifier/role information but preserves core semantic content.
    Modifiers can be extracted as separate atoms if needed. -/
def flattenTerm : Term → ConceptId
  | .entity head _ _ _ => head
  | .event pred _ => pred
  | .var name => ConceptId.fromGF name "Var"
  | .opaque desc => ConceptId.fromGF desc "?"

-- ═══════════════════════════════════════════════════════════════════
-- Phase 3: Translate GFCore.Atom → LP.GroundAtom
-- ═══════════════════════════════════════════════════════════════════

/-- Helper: build a 2-argument ground atom for IsA. -/
def mkIsA (sub sup : ConceptId) : GroundAtom gfSig :=
  GroundAtom.ofFinArgs .isa (fun i => match i with
    | ⟨0, _⟩ => sub
    | ⟨1, _⟩ => sup)

/-- Helper: build an n-argument ground atom for Rel. -/
def mkRel (pred : ConceptId) (args : List ConceptId) : GroundAtom gfSig :=
  let n := args.length
  ⟨.pred pred n, fun i =>
    .const (args.getD i.val (ConceptId.fromGF "?" "?"))⟩

/-- Translate a GFCore.Atom to an LP ground atom.
    Returns `none` for higher-order atoms (causes, implies, conj, neg, forAll)
    which don't have a direct first-order ground representation.
    These stay in the GFCore proof search layer. -/
def atomToLP : GFCore.Atom → Option (GroundAtom gfSig)
  | .isa sub sup => some (mkIsA (flattenTerm sub) (flattenTerm sup))
  | .rel pred args => some (mkRel pred (args.map flattenTerm))
  | .compare _ _ _ _ => none   -- TODO: comparative encoding
  | .causes _ _ => none        -- higher-order
  | .implies _ _ => none       -- higher-order
  | .conj _ => none            -- higher-order
  | .neg _ => none             -- higher-order (negation-as-failure)
  | .forAll _ _ => none        -- higher-order (universal quantification)
  | .opaque _ => none          -- no semantic content

/-- Translate a list of GFCore.Atoms to LP ground atoms, dropping untranslatable ones. -/
def atomsToLP (atoms : List GFCore.Atom) : List (GroundAtom gfSig) :=
  atoms.filterMap atomToLP

-- ═══════════════════════════════════════════════════════════════════
-- Phase 4: Build Knowledge Base from premises
-- ═══════════════════════════════════════════════════════════════════

/-- Build an LP KnowledgeBase from GFCore atoms.
    Translatable atoms become EDB (extensional database) facts.
    No intensional rules yet — pure ground fact base. -/
noncomputable def kbFromAtoms (atoms : List GFCore.Atom) : KnowledgeBase gfSig where
  prog := []  -- no rules yet (just facts)
  db := { a | a ∈ atomsToLP atoms }

/-- Build an LP KnowledgeBase with IsA transitivity rule.
    EDB = ground facts from atoms.
    IDB = IsA transitivity: isa(X, Z) :- isa(X, Y), isa(Y, Z). -/
noncomputable def kbWithTransitivity (atoms : List GFCore.Atom) : KnowledgeBase gfSig where
  prog := [isaTransRule]
  db := { a | a ∈ atomsToLP atoms }
where
  /-- The IsA transitivity clause: isa(X, Z) :- isa(X, Y), isa(Y, Z).
      Uses LP variables "X", "Y", "Z". -/
  isaTransRule : Clause gfSig := {
    head := ⟨.isa, fun i => match i with
      | ⟨0, _⟩ => .var "X"
      | ⟨1, _⟩ => .var "Z"⟩
    body := [
      ⟨.isa, fun i => match i with
        | ⟨0, _⟩ => .var "X"
        | ⟨1, _⟩ => .var "Y"⟩,
      ⟨.isa, fun i => match i with
        | ⟨0, _⟩ => .var "Y"
        | ⟨1, _⟩ => .var "Z"⟩
    ]
  }

-- ═══════════════════════════════════════════════════════════════════
-- Phase 5: Soundness — facts and derived atoms in the Herbrand Model
-- ═══════════════════════════════════════════════════════════════════

/-- Every ground atom in the EDB is in the least Herbrand model (trivial). -/
theorem edb_in_lhm (atoms : List GFCore.Atom) (ga : GroundAtom gfSig)
    (h : ga ∈ atomsToLP atoms) :
    ga ∈ leastHerbrandModel (kbFromAtoms atoms) :=
  leastHerbrandModel_db (kbFromAtoms atoms) ga h

/-- EDB facts are also in the transitivity-augmented LHM. -/
theorem edb_in_trans_lhm (atoms : List GFCore.Atom) (ga : GroundAtom gfSig)
    (h : ga ∈ atomsToLP atoms) :
    ga ∈ leastHerbrandModel (kbWithTransitivity atoms) :=
  leastHerbrandModel_db (kbWithTransitivity atoms) ga h

/-- Helper: ground a 2-ary isa atom from two constants. -/
private def groundIsaAtom (x y : ConceptId) : GroundAtom gfSig :=
  ⟨.isa, fun i => match i with | ⟨0, _⟩ => .const x | ⟨1, _⟩ => .const y⟩

private theorem groundIsaAtom_eq_mkIsA (x y : ConceptId) :
    groundIsaAtom x y = mkIsA x y := by
  unfold groundIsaAtom mkIsA GroundAtom.ofFinArgs
  congr 1; funext ⟨i, hi⟩; match i with | 0 => rfl | 1 => rfl

/-- IsA transitivity via the Herbrand model.

    Proof: construct a grounding mapping X→a, Y→b, Z→c.
    The transitivity clause `isa(X,Z) :- isa(X,Y), isa(Y,Z)` with this grounding
    produces head `isa(a,c)` with body `[isa(a,b), isa(b,c)]`.
    Body atoms are in the LHM (from EDB), so head is in T_P(LHM) = LHM. -/
theorem isa_trans_in_lhm (atoms : List GFCore.Atom)
    (a b c : ConceptId)
    (hab : mkIsA a b ∈ atomsToLP atoms)
    (hbc : mkIsA b c ∈ atomsToLP atoms) :
    mkIsA a c ∈ leastHerbrandModel (kbWithTransitivity atoms) := by
  let kb := kbWithTransitivity atoms
  rw [← groundIsaAtom_eq_mkIsA]
  have hab' : groundIsaAtom a b ∈ leastHerbrandModel kb := by
    rw [groundIsaAtom_eq_mkIsA]; exact edb_in_trans_lhm atoms _ hab
  have hbc' : groundIsaAtom b c ∈ leastHerbrandModel kb := by
    rw [groundIsaAtom_eq_mkIsA]; exact edb_in_trans_lhm atoms _ hbc
  -- Grounding: all variables map to the same constant, then we override.
  -- We use a list-lookup grounding to avoid if-then-else reduction issues.
  let lookup : List (String × ConceptId) := [("X", a), ("Y", b), ("Z", c)]
  let g : Grounding gfSig := fun v =>
    .const ((lookup.find? (·.1 == v)).map (·.2) |>.getD a)
  -- Show g "X" = .const a, g "Y" = .const b, g "Z" = .const c by rfl
  have gX : g "X" = .const a := rfl
  have gY : g "Y" = .const b := rfl
  have gZ : g "Z" = .const c := rfl
  -- Apply fixpoint: groundIsaAtom a c ∈ T_P(LHM) = LHM
  rw [← leastHerbrandModel_fixpoint kb]
  apply Set.mem_union_right
  refine ⟨kbWithTransitivity.isaTransRule, g, List.mem_cons_self, ?_, ?_⟩
  · -- grounded head = groundIsaAtom a c
    simp only [Grounding.groundAtom, kbWithTransitivity.isaTransRule, groundIsaAtom]
    congr 1; funext ⟨i, hi⟩
    match i with
    | 0 => exact gX
    | 1 => exact gZ
  · -- body atoms in LHM
    intro bodyAtom hbody
    simp only [kbWithTransitivity.isaTransRule, List.mem_cons,
               List.mem_nil_iff, or_false] at hbody
    rcases hbody with rfl | rfl
    · -- isa(X,Y) grounded → groundIsaAtom a b
      convert hab' using 1
      simp only [Grounding.groundAtom, groundIsaAtom]
      congr 1; funext ⟨i, hi⟩
      match i with
      | 0 => exact gX
      | 1 => exact gY
    · -- isa(Y,Z) grounded → groundIsaAtom b c
      convert hbc' using 1
      simp only [Grounding.groundAtom, groundIsaAtom]
      congr 1; funext ⟨i, hi⟩
      match i with
      | 0 => exact gY
      | 1 => exact gZ

-- ═══════════════════════════════════════════════════════════════════
-- Phase 6: Evidence-tagged atoms (PLN foundation)
-- ═══════════════════════════════════════════════════════════════════

open Mettapedia.Logic

/-- A ground atom tagged with its epistemic provenance.
    This is the PLN foundation: each fact carries evidence about
    HOW it was established, enabling confidence propagation. -/
structure TaggedAtom where
  atom : GroundAtom gfSig
  kind : EvidenceKind
  source : String          -- provenance: "GF:ParseEng", "WordNet:taxonomy", "DBpedia:SPARQL", "LLM:repair"

/-- Tag a GFCore atom as text-interpreted (parsed from natural language). -/
def tagFromGF (a : GFCore.Atom) (source : String := "GF:ParseEng") : Option TaggedAtom :=
  match atomToLP a with
  | some ga => some { atom := ga, kind := EvidenceKind.textInterpreted, source }
  | none => none

/-- Tag a background IsA fact as empirical (from WordNet taxonomy). -/
def tagFromWordNet (sub sup : ConceptId) : TaggedAtom :=
  { atom := mkIsA sub sup, kind := EvidenceKind.empirical, source := "WordNet:taxonomy" }

/-- Tag an LLM-repaired atom as model-derived (reduced confidence). -/
def tagFromLLM (a : GFCore.Atom) (source : String := "LLM:repair") : Option TaggedAtom :=
  match atomToLP a with
  | some ga => some { atom := ga, kind := EvidenceKind.modelDerived, source }
  | none => none

/-- Tag a derived atom as logical derivation (from proof search). -/
def tagFromDerivation (ga : GroundAtom gfSig) (rule : String) : TaggedAtom :=
  { atom := ga, kind := EvidenceKind.logicalDerivation, source := s!"derived:{rule}" }

/-- Build a tagged knowledge base: atoms with provenance. -/
def taggedKB (tagged : List TaggedAtom) : KnowledgeBase gfSig where
  prog := []
  db := { a | ∃ t ∈ tagged, t.atom = a }

/-- Tagged EDB facts are in the least Herbrand model. -/
theorem tagged_in_lhm (tagged : List TaggedAtom) (t : TaggedAtom)
    (ht : t ∈ tagged) :
    t.atom ∈ leastHerbrandModel (taggedKB tagged) := by
  apply leastHerbrandModel_db
  exact ⟨t, ht, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- Phase 7: LLM Oracle Interface + Provenance
-- ═══════════════════════════════════════════════════════════════════

/-- Full provenance chain for a derived fact.
    Tracks the epistemic origin of every atom in the KB. -/
inductive Provenance where
  | gfParse (sentence : String) (gfFun : String)
  | wordnet (synsetId : String)
  | dbpedia (uri : String)
  | llmSuggestion (model : String) (prompt : String) (response : String)
  | derivation (rule : String) (from_ : List Provenance)
  deriving Repr

/-- A request to an LLM oracle to fill a gap in the proof. -/
structure GapQuery where
  hypothesis : String       -- the goal (English)
  premises : List String    -- existing premises (English)
  gapDescription : String   -- what's missing (from ProveResult.gap)
  neededAtoms : List String -- pretty-printed atoms that would help

/-- An LLM's suggested premise to fill the gap. -/
structure LLMSuggestion where
  text : String             -- natural language: "cooling starch forms resistant starch"
  confidence : Float        -- LLM self-assessed confidence (0.0-1.0)
  model : String            -- "gpt-4o:2026-03-22"

/-- A tagged atom with full provenance chain (not just EvidenceKind). -/
structure ProvenancedAtom where
  atom : GroundAtom gfSig
  kind : EvidenceKind
  provenance : Provenance

/-- Tag a GF-parsed atom with full provenance. -/
def provenanceFromGF (a : GFCore.Atom) (sentence : String) (gfFun : String := "ParseEng")
    : Option ProvenancedAtom :=
  match atomToLP a with
  | some ga => some {
      atom := ga
      kind := EvidenceKind.textInterpreted
      provenance := .gfParse sentence gfFun
    }
  | none => none

/-- Tag an LLM-suggested atom with full provenance. -/
def provenanceFromLLM (a : GFCore.Atom) (suggestion : LLMSuggestion)
    (gapDesc : String) : Option ProvenancedAtom :=
  match atomToLP a with
  | some ga => some {
      atom := ga
      kind := EvidenceKind.modelDerived
      provenance := .llmSuggestion suggestion.model gapDesc suggestion.text
    }
  | none => none

/-- Tag a derived atom with derivation provenance. -/
def provenanceFromDerivation (ga : GroundAtom gfSig) (rule : String)
    (sources : List Provenance) : ProvenancedAtom := {
  atom := ga
  kind := EvidenceKind.logicalDerivation
  provenance := .derivation rule sources
}

end Mettapedia.Languages.GF
