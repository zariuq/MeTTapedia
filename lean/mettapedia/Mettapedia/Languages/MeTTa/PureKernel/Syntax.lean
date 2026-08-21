import Lean

namespace Mettapedia.Languages.MeTTa.PureKernel.Syntax

/-- Kernel-level global declaration name. -/
abbrev DeclName := Lean.Name

/-- Core MeTTa-Pure term syntax, scoped by de Bruijn depth.

**Universe status (2026-08-18, sequestration notice).**  The `u0`/`u1`
pair is a *sealed two-sort fragment* — one distinguished ground type with
`u0 : u1`, and `u1` itself untyped.  It is **not** Prime's universe design:
it cannot quantify over types, hosts no hierarchy, and must not be extended
(`u2`, `El`, level arithmetic, compatibility aliases are all out of scope
for this fragment).  It is retained unchanged because it underwrites the
proved regular fragment (~940 downstream uses); its theorems are valid on
their actual fragment even though the names suggest more.

The eventual replacement is adjudicated under the Russell-unified-Tarski
lane (`PureKernel/Universe/`): a two-tier design (`LevelData` homoiconic,
`FormationLevel` admission, canonical level algebra) with a single chosen
calculus promoted into Prime and these constructors then removed.  Until
that promotion, treat any proof parameterized over `u0`/`u1` as a theorem
of the sealed fragment only.  Do not describe `u0` as "Type 0" or `u1` as
"Type 1" in new documentation; the first is a ground type, the second an
untyped formation marker. -/
inductive PureTm : Nat → Type where
  | var : Fin n → PureTm n
  | const : DeclName → PureTm n
  /-- Sealed fragment: the distinguished ground type (see module notice
  above; not a Russell `Type 0`). -/
  | u0 : PureTm n
  /-- Sealed fragment: the untyped formation marker with `u0 : u1`
  (see module notice above; not a Russell `Type 1`). -/
  | u1 : PureTm n
  | pi : PureTm n → PureTm (n + 1) → PureTm n
  | sigma : PureTm n → PureTm (n + 1) → PureTm n
  | id : PureTm n → PureTm n → PureTm n → PureTm n
  | lam : PureTm (n + 1) → PureTm n
  | app : PureTm n → PureTm n → PureTm n
  | pair : PureTm n → PureTm n → PureTm n
  | fst : PureTm n → PureTm n
  | snd : PureTm n → PureTm n
  | refl : PureTm n → PureTm n
deriving DecidableEq, Repr

end Mettapedia.Languages.MeTTa.PureKernel.Syntax
