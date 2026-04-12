/-
# Pi-Calculus Formalization

The π-calculus (pi-calculus) is a process algebra for modeling concurrent computation.
Key feature: names can be passed as values, enabling dynamic reconfiguration.

## Core Constructs

- **Names**: Communication channels
- **Processes**: Parallel composition, input/output prefixing, restriction, replication
- **Reduction**: Synchronization via input-output on shared names

## References

- Milner (1999): Communicating and Mobile Systems: The π-Calculus
- Sangiorgi & Walker (2001): The π-calculus: A Theory of Mobile Processes
- Caires & Pfenning (2010): Session Types as Intuitionistic Linear Propositions
- Wadler (2012): Propositions as Sessions
-/

import Mathlib.Data.Finset.Basic

namespace Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi

/-! ## Names

Names (channels) in the pi-calculus. We use De Bruijn indices for bound names.
-/

/-- A name is either free (named) or bound (de Bruijn index) -/
inductive Name where
  | free : String → Name
  | bound : Nat → Name
  deriving DecidableEq, Repr, Inhabited

instance : ToString Name where
  toString
    | .free s => s
    | .bound n => s!"#{n}"

/-! ## Pi-Calculus Processes

The grammar of processes:
  P, Q ::= 0           (nil/inaction)
         | P | Q       (parallel composition)
         | x(y).P      (input: receive y on x, bind in P)
         | x̄⟨y⟩.P      (output: send y on x, continue with P)
         | (νx)P       (restriction: create fresh name x)
         | !P          (replication: unbounded copies of P)
         | [x=y]P      (match: conditional on name equality)
-/

/-- Pi-calculus process syntax -/
inductive Process where
  /-- Nil process (inaction) -/
  | nil : Process
  /-- Parallel composition -/
  | par : Process → Process → Process
  /-- Input prefix: x(y).P - receive on x, bind to y in P -/
  | input : Name → Process → Process
  /-- Output prefix: x̄⟨y⟩.P - send y on x, continue with P -/
  | output : Name → Name → Process → Process
  /-- Restriction: (νx)P - create fresh name x -/
  | restriction : Process → Process
  /-- Replication: !P - unbounded copies -/
  | replication : Process → Process
  /-- Match: [x=y]P - guard by name equality -/
  | match : Name → Name → Process → Process
  deriving Repr, Inhabited

/-- Notation helpers -/
notation "𝟎" => Process.nil
infixl:60 " ∥ " => Process.par
prefix:80 "ν." => Process.restriction
prefix:80 "!" => Process.replication

instance : ToString Process where
  toString p := go p
where
  go : Process → String
    | .nil => "0"
    | .par p q => s!"({go p} | {go q})"
    | .input x p => s!"{x}?.{go p}"
    | .output x y p => s!"{x}!⟨{y}⟩.{go p}"
    | .restriction p => s!"(ν.{go p})"
    | .replication p => s!"!{go p}"
    | .match x y p => s!"[{x}={y}]{go p}"

/-! ## Free Names

The set of free names in a process.
-/

/-- Get free names in a process -/
def Process.freeNames : Process → List String
  | .nil => []
  | .par p q => p.freeNames ++ q.freeNames
  | .input x p =>
    match x with
    | .free s => s :: p.freeNames
    | .bound _ => p.freeNames
  | .output x y p =>
    let xFree := match x with | .free s => [s] | .bound _ => []
    let yFree := match y with | .free s => [s] | .bound _ => []
    xFree ++ yFree ++ p.freeNames
  | .restriction p => p.freeNames  -- Bound name removed
  | .replication p => p.freeNames
  | .match x y p =>
    let xFree := match x with | .free s => [s] | .bound _ => []
    let yFree := match y with | .free s => [s] | .bound _ => []
    xFree ++ yFree ++ p.freeNames

/-! ## Structural Congruence

Processes are considered equivalent up to structural congruence:
- P | 0 ≡ P
- P | Q ≡ Q | P
- P | (Q | R) ≡ (P | Q) | R
- (νx)0 ≡ 0
- (νx)(νy)P ≡ (νy)(νx)P
- (νx)(P | Q) ≡ P | (νx)Q  if x ∉ fn(P)
- !P ≡ P | !P
-/

/-- Structural congruence between processes -/
inductive StructCong : Process → Process → Prop where
  /-- Reflexivity -/
  | refl (p : Process) : StructCong p p
  /-- Symmetry -/
  | symm : StructCong p q → StructCong q p
  /-- Transitivity -/
  | trans : StructCong p q → StructCong q r → StructCong p r
  /-- Par with nil -/
  | par_nil : StructCong (.par p .nil) p
  /-- Par commutativity -/
  | par_comm : StructCong (.par p q) (.par q p)
  /-- Par associativity -/
  | par_assoc : StructCong (.par (.par p q) r) (.par p (.par q r))
  /-- Restriction of nil -/
  | nu_nil : StructCong (.restriction .nil) .nil
  /-- Restriction swap -/
  | nu_swap : StructCong (.restriction (.restriction p)) (.restriction (.restriction p))
  /-- Replication unfolding -/
  | repl_unfold : StructCong (.replication p) (.par p (.replication p))
  /-- Congruence under parallel -/
  | cong_par : StructCong p p' → StructCong q q' → StructCong (.par p q) (.par p' q')
  /-- Congruence under restriction -/
  | cong_nu : StructCong p p' → StructCong (.restriction p) (.restriction p')

notation:50 p " ≡ " q => StructCong p q

/-! ## Reduction Semantics

The reduction relation captures synchronization:
  x̄⟨z⟩.P | x(y).Q  →  P | Q[z/y]

Plus congruence rules for reduction under parallel and restriction.
-/

/-- Substitution of names in a process -/
def Process.subst (p : Process) (target : Nat) (replacement : Name) : Process :=
  match p with
  | .nil => .nil
  | .par p q => .par (p.subst target replacement) (q.subst target replacement)
  | .input x p =>
    let x' := match x with
      | .bound n => if n == target then replacement else x
      | _ => x
    -- Under input, the bound variable index shifts
    .input x' (p.subst (target + 1) replacement)
  | .output x y p =>
    let x' := match x with
      | .bound n => if n == target then replacement else x
      | _ => x
    let y' := match y with
      | .bound n => if n == target then replacement else y
      | _ => y
    .output x' y' (p.subst target replacement)
  | .restriction p =>
    -- Under restriction, the bound variable index shifts
    .restriction (p.subst (target + 1) replacement)
  | .replication p => .replication (p.subst target replacement)
  | .match x y p =>
    let x' := match x with
      | .bound n => if n == target then replacement else x
      | _ => x
    let y' := match y with
      | .bound n => if n == target then replacement else y
      | _ => y
    .match x' y' (p.subst target replacement)

/-- One-step reduction relation -/
inductive Reduce : Process → Process → Prop where
  /-- Communication: output and input on same channel synchronize -/
  | comm (x : Name) (z : Name) (p q : Process) :
      Reduce (.par (.output x z p) (.input x q)) (.par p (q.subst 0 z))
  /-- Match succeeds when names are equal -/
  | match_eq (n : Name) (p : Process) :
      Reduce (.match n n p) p
  /-- Reduce under parallel (left) -/
  | par_left : Reduce p p' → Reduce (.par p q) (.par p' q)
  /-- Reduce under parallel (right) -/
  | par_right : Reduce q q' → Reduce (.par p q) (.par p q')
  /-- Reduce under restriction -/
  | res : Reduce p p' → Reduce (.restriction p) (.restriction p')
  /-- Reduce up to structural congruence -/
  | struct : StructCong p p' → Reduce p' q' → StructCong q' q → Reduce p q

notation:50 p " ⟶ " q => Reduce p q

/-! ## Examples -/

/-- Example: Simple communication on channel a -/
def exampleComm : Process :=
  .par
    (.output (.free "a") (.free "v") .nil)  -- a!⟨v⟩.0
    (.input (.free "a") .nil)                -- a?.0

/-- Example: Restricted channel -/
def exampleRestricted : Process :=
  .restriction (
    .par
      (.output (.bound 0) (.free "v") .nil)
      (.input (.bound 0) .nil)
  )

#check (exampleComm : Process)
#check (exampleRestricted : Process)

/-! ## Properties -/

/-- Structural congruence is an equivalence relation -/
theorem structCong_equiv : Equivalence StructCong :=
  ⟨StructCong.refl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Parallel composition with nil is identity (up to congruence) -/
theorem par_nil_id (p : Process) : (p ∥ 𝟎) ≡ p :=
  StructCong.par_nil

/-- Parallel composition is commutative -/
theorem par_comm (p q : Process) : (p ∥ q) ≡ (q ∥ p) :=
  StructCong.par_comm

end Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi
