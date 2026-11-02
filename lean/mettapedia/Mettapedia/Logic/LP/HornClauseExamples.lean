import Mettapedia.Logic.LP.Semantics

/-!
# First-order Horn-clause examples with Prolog-style syntax

A concrete `LPSignature` for function symbols, compound terms and recursive
Horn clauses. This supplies examples for the least-Herbrand-model semantics;
it does not specify an ISO source reader, ordered execution, cut or effects.

## Historical Context

Prolog and its theoretical foundation were developed by:

- **Colmerauer & Roussel** (1973): Prolog language design (Marseille)
- **Kowalski** (1974): procedural interpretation of Horn clauses
- **van Emden & Kowalski** (1976): model-theoretic semantics (`T_P` operator,
  least Herbrand model) — formalized in `LP/Semantics.lean`
- **Lloyd** (1987): *Foundations of Logic Programming* — SLD resolution,
  soundness, completeness — formalized in `LP/SLD.lean`

## Design Note

Our `LPSignature` separates relation and function symbols at the type level.
This is an organizational choice for first-order Horn logic. The separate
`Logic.Prolog` source signature and control semantics represent operational
Prolog programs; their reader and dialect qualifications are separate.

## Example Programs

### Family Relations (Datalog fragment)

```prolog
parent(alice, bob).
parent(bob, charlie).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
```

### Successor Arithmetic (requires function symbols)

```prolog
nat(0).
nat(s(X)) :- nat(X).
```

The `s` in `nat(s(X))` is a function symbol — `s(X)` is a compound term.
Compound function symbols are outside function-free Datalog. These examples
exercise first-order LP without asserting complete Prolog-language coverage.

0 sorry.
-/

namespace Mettapedia.Logic.LP.HornClauseExamples

open Mettapedia.Logic.LP

/-! ## §1 Signature -/

inductive PConst | alice | bob | charlie | zero deriving DecidableEq
inductive PVar  | X | Y | Z                    deriving DecidableEq
inductive PRel  | parent | ancestor | nat       deriving DecidableEq
inductive PFun  | succ                          deriving DecidableEq

@[reducible] def signature : LPSignature where
  constants := PConst
  vars := PVar
  relationSymbols := PRel
  relationArity := fun | .parent => 2 | .ancestor => 2 | .nat => 1
  functionSymbols := PFun
  functionArity := fun | .succ => 1

/-! ## §2 Term Builders -/

def con (x : PConst) : Term signature := .const x
def var' (x : PVar) : Term signature := .var x
def suc (t : Term signature) : Term signature :=
  .app PFun.succ (fun _ => t)

/-- Build a binary atom (parent, ancestor). -/
def bin (r : PRel) (a b : Term signature) (_h : signature.relationArity r = 2 := by decide) :
    Atom signature :=
  ⟨r, fun i => if i.val = 0 then a else b⟩

/-- Build a unary atom (nat). -/
def una (r : PRel) (a : Term signature) (_h : signature.relationArity r = 1 := by decide) :
    Atom signature :=
  ⟨r, fun _ => a⟩

/-! ## §3 Program -/

/-- `parent(alice, bob).` -/
def cl_parentAB : Clause signature :=
  ⟨bin .parent (con .alice) (con .bob), []⟩

/-- `parent(bob, charlie).` -/
def cl_parentBC : Clause signature :=
  ⟨bin .parent (con .bob) (con .charlie), []⟩

/-- `ancestor(X, Y) :- parent(X, Y).` -/
def cl_ancBase : Clause signature :=
  ⟨bin .ancestor (var' .X) (var' .Y),
   [bin .parent (var' .X) (var' .Y)]⟩

/-- `ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).` -/
def cl_ancStep : Clause signature :=
  ⟨bin .ancestor (var' .X) (var' .Y),
   [bin .parent (var' .X) (var' .Z),
    bin .ancestor (var' .Z) (var' .Y)]⟩

/-- `nat(0).` -/
def cl_natZ : Clause signature :=
  ⟨una .nat (con .zero), []⟩

/-- `nat(s(X)) :- nat(X).` — uses the function symbol `s`. -/
def cl_natS : Clause signature :=
  ⟨una .nat (suc (var' .X)),
   [una .nat (var' .X)]⟩

def program : Program signature :=
  [cl_parentAB, cl_parentBC, cl_ancBase, cl_ancStep, cl_natZ, cl_natS]

def knowledgeBase : KnowledgeBase signature where
  prog := program
  db := ∅

/-! ## §4 Ground Terms with Function Symbols

`GroundTerm signature` includes compound terms like `s(s(0))`.
This is NOT possible in Datalog. -/

def gcon (x : PConst) : GroundTerm signature := .const x
def gsuc (t : GroundTerm signature) : GroundTerm signature :=
  .app PFun.succ (fun _ => t)

/-- Ground binary atom. -/
def gbin (r : PRel) (a b : GroundTerm signature) : GroundAtom signature :=
  ⟨r, fun i => if i.val = 0 then a else b⟩

/-- Ground unary atom. -/
def guna (r : PRel) (a : GroundTerm signature) : GroundAtom signature :=
  ⟨r, fun _ => a⟩

/-- `nat(0)` -/
def gNatZero := guna .nat (gcon .zero)

/-- `nat(s(0))` — compound term with function symbol -/
def gNatS0 := guna .nat (gsuc (gcon .zero))

/-- `nat(s(s(0)))` — nested function symbol application -/
def gNatSS0 := guna .nat (gsuc (gsuc (gcon .zero)))

/-! ## §5 Semantic Proofs

We prove ground atoms are in the least Herbrand model.
`T_P_LP` and `leastHerbrandModel` have NO function-free restriction. -/

/-- Grounding that maps all variables to `0`. -/
private def g0 : Grounding signature := fun _ => gcon .zero

/-- `nat(0) ∈ LHM` — base fact. -/
theorem nat_zero_in_lhm : gNatZero ∈ leastHerbrandModel knowledgeBase := by
  -- nat(0) = g0.groundAtom cl_natZ.head
  have : g0.groundAtom cl_natZ.head = gNatZero := by
    simp [Grounding.groundAtom, guna, gNatZero, gcon, una, con, Grounding.groundTerm, cl_natZ]
  rw [← this]
  exact leastHerbrandModel_clause knowledgeBase cl_natZ
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) g0
    (fun b hb => by simp [cl_natZ] at hb)

/-- **`nat(s(0)) ∈ LHM`** — uses function symbol `s`.

    This proof is the key demonstration: `s(0)` is a compound ground term
    built with the function symbol `succ`. This is impossible in Datalog.
    The clause `nat(s(X)) :- nat(X)` with grounding `X ↦ 0` derives it. -/
theorem nat_s0_in_lhm : gNatS0 ∈ leastHerbrandModel knowledgeBase := by
  -- nat(s(0)) = g0.groundAtom cl_natS.head  (since g0 maps X to 0, s(X) becomes s(0))
  have hhead : g0.groundAtom cl_natS.head = gNatS0 := by
    simp [Grounding.groundAtom, guna, gNatS0, gcon, gsuc, una, suc, var', g0,
          Grounding.groundTerm, cl_natS]
  rw [← hhead]
  apply leastHerbrandModel_clause knowledgeBase cl_natS
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) g0
  -- body: nat(X) grounded by g0 gives nat(0), which is in LHM
  intro b hb
  simp only [cl_natS, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  have : g0.groundAtom (una .nat (var' .X)) = gNatZero := by
    simp [Grounding.groundAtom, guna, gNatZero, gcon, una, var', g0, Grounding.groundTerm]
  rw [this]
  exact nat_zero_in_lhm

end Mettapedia.Logic.LP.HornClauseExamples
