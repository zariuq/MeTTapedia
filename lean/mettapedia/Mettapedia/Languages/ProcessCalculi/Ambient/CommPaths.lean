import Mettapedia.Languages.ProcessCalculi.Ambient.Comm

/-!
# The path normal form

The laws of paths read a prefix by a capability as the prefixes of the pure calculus: `ε.P = P`,
`(M.M').P = M.(M'.P)` and `(in n).P = in n.P`, and so for `out` and `open`. Read from left to right they terminate,
and they meet only at the prefix they rewrite, so a term has one normal form under them (`pathNF`): every prefix by
a capability is read as the prefixes it makes (`prefixes`), and a prefix by a capability variable, which no law reads,
stays.

- **A path normal form has no prefix by a capability but by a variable** (`pathNormal`); the normal form of a term
  without capability prefixes is the term itself (`pathNF_of_capFree`).
- **The normal form is idempotent** (`pathNF_pathNF`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Prefixes made by a capability -/

/-- **The prefixes a capability makes** in front of a process: `in n`, `out n` and `open n` as the pure calculus's
prefixes, the empty path as nothing, a path as its first capability's prefixes in front of the rest's; anything else,
a capability variable above all, as a prefix no law reads. -/
def prefixes : Pattern → Pattern → Pattern
  | .apply "CapIn" [name], process => .apply "AIn" [name, process]
  | .apply "CapOut" [name], process => .apply "AOut" [name, process]
  | .apply "CapOpen" [name], process => .apply "AOpen" [name, process]
  | .apply "CapEps" [], process => process
  | .apply "CapPath" [first, rest], process => prefixes first (prefixes rest process)
  | capability, process => .apply "ACap" [capability, process]

mutual
  /-- **The path normal form**: every prefix by a capability read as the prefixes it makes, everywhere. -/
  def pathNF : Pattern → Pattern
    | .apply "ACap" [capability, process] => prefixes capability (pathNF process)
    | .apply label arguments => .apply label (pathNFList arguments)
    | .lambda binder body => .lambda binder (pathNF body)
    | .multiLambda arity binders body => .multiLambda arity binders (pathNF body)
    | .subst body replacement => .subst (pathNF body) (pathNF replacement)
    | .collection kind elements rest => .collection kind (pathNFList elements) rest
    | other => other

  /-- The path normal forms of a list of terms. -/
  def pathNFList : List Pattern → List Pattern
    | [] => []
    | first :: rest => pathNF first :: pathNFList rest
end

theorem pathNFList_eq_map : ∀ patterns : List Pattern, pathNFList patterns = patterns.map pathNF
  | [] => rfl
  | first :: rest => by rw [pathNFList, pathNFList_eq_map rest, List.map_cons]

/-- Off the capability prefix, the normal form reads the arguments. -/
theorem pathNF_apply_of_ne {label : String} (different : label ≠ "ACap") (arguments : List Pattern) :
    pathNF (.apply label arguments) = .apply label (arguments.map pathNF) := by
  rw [← pathNFList_eq_map]
  unfold pathNF
  split <;> simp_all

/-! ## Controls -/

section Controls

private def n : Pattern := .fvar "n"
private def m : Pattern := .fvar "m"
private def zero : Pattern := .apply "AZero" []

/-- `(in n.out m).0` reads as `in n.out m.0`. -/
example : pathNF (.apply "ACap" [.apply "CapPath" [.apply "CapIn" [n], .apply "CapOut" [m]], zero]) =
    .apply "AIn" [n, .apply "AOut" [m, zero]] := by decide +kernel

/-- `ε.(in n).0` reads as `in n.0`. -/
example : pathNF (.apply "ACap" [.apply "CapEps" [], .apply "ACap" [.apply "CapIn" [n], zero]]) =
    .apply "AIn" [n, zero] := by decide +kernel

/-- A prefix by a capability variable stays, the rest of its path read: `(x.in n).0` reads as `x.(in n.0)`. -/
example : pathNF (.apply "ACap" [.apply "CapPath" [.bvar 0, .apply "CapIn" [n]], zero]) =
    .apply "ACap" [.bvar 0, .apply "AIn" [n, zero]] := by decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
