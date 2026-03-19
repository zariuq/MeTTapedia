import Mettapedia.Logic.LP.Semantics

/-!
# Standard Prolog Instance

A concrete `LPSignature` demonstrating that our LP formalization fully models
standard Prolog with function symbols, compound terms, and recursive clauses.

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
This is an organizational choice, not a semantic restriction: any standard
Prolog program is directly representable, as this module demonstrates.

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
This is impossible in Datalog and demonstrates our formalization handles
full first-order LP.

0 sorry.
-/

namespace Mettapedia.Logic.LP.PrologInstance

open Mettapedia.Logic.LP

/-! ## §1 Signature -/

inductive PConst | alice | bob | charlie | zero deriving DecidableEq
inductive PVar  | X | Y | Z                    deriving DecidableEq
inductive PRel  | parent | ancestor | nat       deriving DecidableEq
inductive PFun  | succ                          deriving DecidableEq

@[reducible] def prologSig : LPSignature where
  constants := PConst
  vars := PVar
  relationSymbols := PRel
  relationArity := fun | .parent => 2 | .ancestor => 2 | .nat => 1
  functionSymbols := PFun
  functionArity := fun | .succ => 1

/-! ## §2 Term Builders -/

def con (x : PConst) : Term prologSig := .const x
def var' (x : PVar) : Term prologSig := .var x
def suc (t : Term prologSig) : Term prologSig :=
  .app PFun.succ (fun _ => t)

/-- Build a binary atom (parent, ancestor). -/
def bin (r : PRel) (a b : Term prologSig) (h : prologSig.relationArity r = 2 := by decide) :
    Atom prologSig :=
  ⟨r, fun i => if i.val = 0 then a else b⟩

/-- Build a unary atom (nat). -/
def una (r : PRel) (a : Term prologSig) (h : prologSig.relationArity r = 1 := by decide) :
    Atom prologSig :=
  ⟨r, fun _ => a⟩

/-! ## §3 Program -/

/-- `parent(alice, bob).` -/
def cl_parentAB : Clause prologSig :=
  ⟨bin .parent (con .alice) (con .bob), []⟩

/-- `parent(bob, charlie).` -/
def cl_parentBC : Clause prologSig :=
  ⟨bin .parent (con .bob) (con .charlie), []⟩

/-- `ancestor(X, Y) :- parent(X, Y).` -/
def cl_ancBase : Clause prologSig :=
  ⟨bin .ancestor (var' .X) (var' .Y),
   [bin .parent (var' .X) (var' .Y)]⟩

/-- `ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).` -/
def cl_ancStep : Clause prologSig :=
  ⟨bin .ancestor (var' .X) (var' .Y),
   [bin .parent (var' .X) (var' .Z),
    bin .ancestor (var' .Z) (var' .Y)]⟩

/-- `nat(0).` -/
def cl_natZ : Clause prologSig :=
  ⟨una .nat (con .zero), []⟩

/-- `nat(s(X)) :- nat(X).` — uses the function symbol `s`. -/
def cl_natS : Clause prologSig :=
  ⟨una .nat (suc (var' .X)),
   [una .nat (var' .X)]⟩

def prologProg : Program prologSig :=
  [cl_parentAB, cl_parentBC, cl_ancBase, cl_ancStep, cl_natZ, cl_natS]

def prologKB : KnowledgeBase prologSig where
  prog := prologProg
  db := ∅

/-! ## §4 Ground Terms with Function Symbols

`GroundTerm prologSig` includes compound terms like `s(s(0))`.
This is NOT possible in Datalog. -/

def gcon (x : PConst) : GroundTerm prologSig := .const x
def gsuc (t : GroundTerm prologSig) : GroundTerm prologSig :=
  .app PFun.succ (fun _ => t)

/-- Ground binary atom. -/
def gbin (r : PRel) (a b : GroundTerm prologSig) : GroundAtom prologSig :=
  ⟨r, fun i => if i.val = 0 then a else b⟩

/-- Ground unary atom. -/
def guna (r : PRel) (a : GroundTerm prologSig) : GroundAtom prologSig :=
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
private def g0 : Grounding prologSig := fun _ => gcon .zero

/-- `nat(0) ∈ LHM` — base fact. -/
theorem nat_zero_in_lhm : gNatZero ∈ leastHerbrandModel prologKB := by
  -- nat(0) = g0.groundAtom cl_natZ.head
  have : g0.groundAtom cl_natZ.head = gNatZero := by
    simp [Grounding.groundAtom, guna, gNatZero, gcon, una, con, var', g0, Grounding.groundTerm, cl_natZ]
  rw [← this]
  exact leastHerbrandModel_clause prologKB cl_natZ
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) g0
    (fun b hb => by simp [cl_natZ] at hb)

/-- **`nat(s(0)) ∈ LHM`** — uses function symbol `s`.

    This proof is the key demonstration: `s(0)` is a compound ground term
    built with the function symbol `succ`. This is impossible in Datalog.
    The clause `nat(s(X)) :- nat(X)` with grounding `X ↦ 0` derives it. -/
theorem nat_s0_in_lhm : gNatS0 ∈ leastHerbrandModel prologKB := by
  -- nat(s(0)) = g0.groundAtom cl_natS.head  (since g0 maps X to 0, s(X) becomes s(0))
  have hhead : g0.groundAtom cl_natS.head = gNatS0 := by
    simp [Grounding.groundAtom, guna, gNatS0, gcon, gsuc, una, con, suc, var', g0,
          Grounding.groundTerm, cl_natS]
  rw [← hhead]
  apply leastHerbrandModel_clause prologKB cl_natS
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) g0
  -- body: nat(X) grounded by g0 gives nat(0), which is in LHM
  intro b hb
  simp only [cl_natS, Clause.body, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  have : g0.groundAtom (una .nat (var' .X)) = gNatZero := by
    simp [Grounding.groundAtom, guna, gNatZero, gcon, una, var', g0, Grounding.groundTerm]
  rw [this]
  exact nat_zero_in_lhm

end Mettapedia.Logic.LP.PrologInstance
