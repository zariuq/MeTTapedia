import Mettapedia.OSLF.PiCalculus.Reduction
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Correct Encoding π → ρ (Lybech 2022)

This encoding fixes the errors in Meredith & Radestock (2005).

## Key Innovation: Name Server

Instead of parametrized name generation, use a dedicated process:
```
!N(x,z,v,s) = D(x) | x⟨z(a).v(r).(D(x) | r⟨↓a⟩ | z⟨a⟨|0|⟩⟩)⟩
```

This generates namespace N⁺[s] = {s, ⌜s⌜|0|⌝⌝, ⌜⌜s⌜|0|⌝⌝⌜|0|⌝⌝, ...}

## Challenge

The π-calculus uses **atomic names** (strings like "x", "y"), while the
ρ-calculus uses **structured names** (quoted processes like @(P)).

**Meredith & Radestock (2005) errors:**
1. Parameters lost access to "most recently replicated names"
2. Static name increments weren't updated at runtime

**Lybech's solution:** Name server generates fresh names dynamically.

## References
- Lybech (2022), Section 6, pages 104-107
- Meredith & Radestock (2005) - INCORRECT encoding
-/

namespace Mettapedia.OSLF.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.OSLF.RhoCalculus.Reduction

/-! ## Name Mapping

π-calculus names (atomic strings) map to ρ-calculus channels.
We use `.fvar x` as the channel for π-name x. Output sends `PDrop(.fvar z)` as
payload so that COMM's NQuote wrapping produces `NQuote(PDrop(.fvar z)) ≡ .fvar z`
by the QuoteDrop structural equation. This avoids the double-quoting problem.
-/

/-- Map a π-calculus atomic name to a ρ-calculus channel.

    A π-name x maps to the free variable `.fvar x` in the ρ-calculus encoding.
    After COMM, the bound variable receives `NQuote(payload)`. Since output
    sends `PDrop(.fvar z)` as payload, COMM produces `NQuote(PDrop(.fvar z))`,
    which simplifies to `.fvar z` by the QuoteDrop structural equation.
-/
def piNameToRhoName (n : Name) : Pattern :=
  .fvar n

/-- The nil process in ρ-calculus -/
def rhoNil : Pattern :=
  .collection .hashBag [] none

/-- Parallel composition in ρ-calculus -/
def rhoPar (P Q : Pattern) : Pattern :=
  match P, Q with
  | .collection .hashBag ps none, .collection .hashBag qs none =>
      .collection .hashBag (ps ++ qs) none
  | .collection .hashBag ps none, q =>
      .collection .hashBag (ps ++ [q]) none
  | p, .collection .hashBag qs none =>
      .collection .hashBag (p :: qs) none
  | p, q => .collection .hashBag [p, q] none

/-- Input in ρ-calculus: for(x <- n){P}

    In locally nameless, `closeFVar 0 x P` replaces free occurrences of `x`
    in `P` with `BVar 0`, then wraps in `.lambda`. -/
def rhoInput (n : Pattern) (x : String) (P : Pattern) : Pattern :=
  .apply "PInput" [n, .lambda (closeFVar 0 x P)]

/-- Output in ρ-calculus: n!(q) -/
def rhoOutput (n q : Pattern) : Pattern :=
  .apply "POutput" [n, q]

/-- Restriction in ρ-calculus: (νx)P (via new channel pattern) -/
def rhoNu (x : String) (P : Pattern) : Pattern :=
  -- In ρ-calculus, restriction is typically encoded using input on a fresh channel
  -- For now, represent as a direct restriction pattern (may need refinement)
  .apply "PNu" [.lambda (closeFVar 0 x P)]

/-- Replication in ρ-calculus: !P -/
def rhoReplicate (P : Pattern) : Pattern :=
  .apply "PReplicate" [P]

/-- Drop in ρ-calculus: *n (dereference a name to get its process) -/
def rhoDrop (n : Pattern) : Pattern :=
  .apply "PDrop" [n]

/-! ## Name Server (Lybech's Innovation)

The name server generates fresh names on demand. This is the key to fixing
the Meredith & Radestock bugs.

The name server is defined as:
```
!N(x,z,v,s) = D(x) | x⟨z(a).v(r).(D(x) | r⟨↓a⟩ | z⟨a⟨|0|⟩⟩)⟩ | z⟨↓s⟩
```

Where D(x) is a "drop" operation that repeatedly offers `x` for communication.
-/

/-- Drop operation: D(x) - repeatedly offers x for communication

    In ρ-calculus, this is represented as a replicated input that
    continuously makes x available.
-/
def dropOperation (x : String) : Pattern :=
  rhoReplicate (rhoInput (.fvar x) "_drop" rhoNil)

/-- The name server process that generates fresh names on demand.

    Parameters:
    - x: server channel (where to request names)
    - z: response channel (where fresh names are sent)
    - v: continuation channel
    - s: seed name (starting point for namespace generation)

    Following Lybech (2022), page 104:
    ```
    !N(x,z,v,s) = D(x) | x⟨z(a).v(r).(D(x) | r⟨↓a⟩ | z⟨a⟨|0|⟩⟩)⟩ | z⟨↓s⟩
    ```

    This generates namespace N⁺[s] = {s, ⌜s⌜|0|⌝⌝, ⌜⌜s⌜|0|⌝⌝⌜|0|⌝⌝, ...}
-/
def nameServer (x z v s : String) : Pattern :=
  let dropX := dropOperation x
  -- x⟨z(a).v(r).(D(x) | r⟨↓a⟩ | z⟨a⟨|0|⟩⟩)⟩
  let serverBody :=
    rhoInput (.fvar x) z
      (rhoInput (.fvar z) "a"
        (rhoInput (.fvar v) "r"
          (rhoPar dropX
            (rhoPar
              (rhoOutput (.fvar "r") (.apply "Drop" [.fvar "a"]))
              (rhoOutput (.fvar z)
                (.apply "Quote" [.apply "Quote" [rhoNil]]))))))
  -- z⟨↓s⟩
  let initialSeed :=
    rhoOutput (.fvar z) (.apply "Drop" [.fvar s])
  -- Replicate the server and add initial seed
  rhoPar (rhoReplicate serverBody) (rhoPar dropX initialSeed)

/-! ## Encoding Function ⟦P⟧

The encoding maps π-calculus processes to ρ-calculus patterns.

Following Lybech, the encoding is parametrized by:
- n: a namespace parameter (for generating fresh names)
- v: a value parameter (for passing computed values)
-/

/-- Encoding function ⟦P⟧_{n,v}

    Maps a π-calculus process P to a ρ-calculus pattern,
    parametrized by namespace n and value v.
-/
def encode (P : Process) (n v : String) : Pattern :=
  match P with
  | .nil => rhoNil
  | .par P Q =>
      rhoPar (encode P (n ++ "_L") v) (encode Q (n ++ "_R") v)
  | .input x y P =>
      rhoInput (piNameToRhoName x) y (encode P n v)
  | .output x z =>
      -- Send PDrop(z) as the process payload. After COMM, the bound variable
      -- receives NQuote(PDrop(.var z)) which ≡ .var z by QuoteDrop.
      -- This correctly implements ρ-calculus: output sends a PROCESS,
      -- COMM quotes it to create a NAME for the receiver.
      rhoOutput (piNameToRhoName x) (rhoDrop (piNameToRhoName z))
  | .nu x P =>
      -- Request fresh name from name server and use it in encoding
      -- Following Lybech: (νx)P ↦ v⟨n⟩ | n(x).⟦P⟧_{n∘n,v}
      rhoPar
        (rhoOutput (.fvar v) (.fvar n))
        (rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v))
  | .replicate x y P =>
      rhoReplicate (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v))

/-- Full encoding: ⟦P⟧ = ⟦P⟧_{n,v} | !N(x,z,v,s)

    The full encoding includes the name server running in parallel.
-/
def fullEncode (P : Process) : Pattern :=
  let n := "n_init"
  let v := "v_init"
  let x := "ns_x"
  let z := "ns_z"
  let s := "ns_seed"
  rhoPar (encode P n v) (nameServer x z v s)

/-! ## Namespace Renaming Environment

For proving parameter independence (Prop 1), we need a finite substitution
that maps namespace variables generated from parameter `n` to those from `n'`.

The encoding generates namespace variables as follows:
- `par P Q` → left uses `n ++ "_L"`, right uses `n ++ "_R"`
- `nu x P` → uses `n` as a channel, body uses `n ++ "_" ++ n`
- `replicate x y P` → body uses `n ++ "_rep"`
- `nil`, `output`, `input` → no namespace variables generated

The `nsEnv` function builds the finite renaming mapping these generated
namespace variables from one parameter to another.

Reference: Lybech (2022), Proposition 1, page 106.
-/

open Mettapedia.OSLF.MeTTaIL.Substitution

/-- Namespace renaming environment: maps namespace variables generated from `n`
    to corresponding ones generated from `n'`.

    For each `nu` in the process, the encoding uses `.fvar n` as a channel.
    This env maps `n ↦ .fvar n'` so that `applySubst (nsEnv P n n') (encode P n v) = encode P n' v`.
-/
def nsEnv : Process → String → String → SubstEnv
  | .nil, _, _ => []
  | .output _ _, _, _ => []
  | .input _ _ P, n, n' => nsEnv P n n'
  | .par P Q, n, n' =>
      nsEnv P (n ++ "_L") (n' ++ "_L") ++ nsEnv Q (n ++ "_R") (n' ++ "_R")
  | .nu _ P, n, n' =>
      (n, .fvar n') :: nsEnv P (n ++ "_" ++ n) (n' ++ "_" ++ n')
  | .replicate _ _ P, n, n' =>
      nsEnv P (n ++ "_rep") (n' ++ "_rep")

end Mettapedia.OSLF.PiCalculus
