import Mettapedia.Logic.TierZero.Kernel2.Spaces

/-!
# MeTTa source of the kernel's messages

`renderWorld` prints a world's mailboxes as a MeTTa kernel-v2 program: the boot lines, one
`admit` command per admission, one `submit` command per claim, and the final query of the accepted
board. A claim's formals and dummies are the MeTTa variables `$x0, $x1, …`, written with their
kinds: `$x3` (a name), `(scope $x3)` (a scope variable), `(dep $x3 (0 2))` (a name over the scope
variables at positions `0` and `2`); a stored term `k` is `tk`; node `n` is `n`.

Example: the rule `ax-mp` renders as
`(admit-rule ax-mp ($x0 $x1) (prem (wff $x0) (prem (wff $x1) (prem (|- $x0) (prem (|- (wi $x0 $x1)) no-prem)))) (|- $x1))`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

/-- A list of sources in parentheses. -/
def parens (xs : List String) : String := "(" ++ " ".intercalate xs ++ ")"

/-- The formals `$x0 … $x(n-1)`. -/
def formalsSrc (from_ n : ℕ) : String := parens ((List.range n).map fun i => s!"$x{from_ + i}")

/-- A premise as MeTTa source. -/
def Premise.render : Premise → String
  | .judg p => renderPat p
  | .given p => s!"(given {renderPat p})"
  | .differ a b => s!"(differ {renderPat a} {renderPat b})"
  | .absent x b => s!"(absent-from {renderPat x} {renderPat b})"
  | .dv x y => s!"(dv {renderPat x} {renderPat y})"
  | .isOpen r b v => s!"(is {renderPat r} (open {renderPat b} {renderPat v}))"
  | .isAbstract r x b => s!"(is {renderPat r} (abstract {renderPat x} {renderPat b}))"
  | .isSubst r s b => s!"(is {renderPat r} (subst {renderPat s} {renderPat b}))"
  | .unionOf u g d => s!"(union-of {renderPat u} {renderPat g} {renderPat d})"
  | .removeOf r x g => s!"(remove-of {renderPat r} {renderPat x} {renderPat g})"
  | .singletonOf s x => s!"(singleton-of {renderPat s} {renderPat x})"
  | .imageOf h' s h => s!"(image-of {renderPat h'} {renderPat s} {renderPat h})"
  | .atomKind x k => s!"(atom-kind {renderPat x} {renderPat k})"
  | .each x l p => s!"(each $x{x} {renderPat l} {renderPat p})"

/-- A premise chain. -/
def premsSrc (ps : List Premise) : String :=
  ps.foldr (fun p acc => s!"(prem {p.render} {acc})") "no-prem"

/-- The list premises' local variables of a rule, each once (kernel-v2 lists them among the
formals). -/
def Rule.locals (ru : Rule) : List ℕ :=
  (ru.prems.filterMap fun p => match p with
    | .each x _ _ => some x
    | _ => none).dedup

/-- `(admit-rule NAME FORMALS PREMISES CONCLUSION)`. -/
def Rule.render (name : String) (ru : Rule) : String :=
  let formals := parens ((List.range ru.nformals ++ ru.locals).map fun i => s!"$x{i}")
  s!"(admit-rule {name} {formals} {premsSrc ru.prems} {renderPat ru.concl})"

/-- A child. -/
def CKid.render : CKid → String
  | .hyp i => s!"(hyp {i})"
  | .loc i => s!"(local {i})"
  | .term tid => s!"(term t{tid})"
  | .node n => toString n

/-- The proof chain. -/
def proofSrc (pf : List (CProofNode String)) : String :=
  pf.foldr (fun nd acc => s!"(node {nd.name} {nd.rule} {parens (nd.kids.map CKid.render)} {acc})") "no-node"

/-- A claim's variable `$x{i}` with its kind. -/
def FormalKind.render (i : ℕ) : FormalKind → String
  | .name => s!"$x{i}"
  | .scope => s!"(scope $x{i})"
  | .dep ds => s!"(dep $x{i} {parens (ds.map toString)})"

/-- The variables from position `from_`, with their kinds. -/
def kindsSrc (from_ : ℕ) (ks : List FormalKind) : String :=
  parens (ks.mapIdx fun i κ => κ.render (from_ + i))

/-- `(claim ID ROOT FORMALS DUMMIES HYPS LOCALS DVL CONCLUSION TERMS PROOF)`. -/
def Claim.render (c : Claim String) : String :=
  let n := c.formals.length
  let locals := parens (c.locals.map fun l => s!"({l.1} $x{l.2})")
  let dvl := parens (c.dvl.map fun pq => s!"({renderPat pq.1} {renderPat pq.2})")
  let terms := parens (c.terms.map fun x => s!"(t{x.1} {renderPat x.2})")
  s!"(claim {c.id} {c.root.render} {kindsSrc 0 c.formals} {kindsSrc n c.dummies} " ++
    s!"{premsSrc c.hyps} {locals} {dvl} {renderPat c.concl} {terms} {proofSrc c.proof})"

/-- An admission. -/
def Admission.render : Admission String → String
  | .judgment h n => s!"(admit-judgment {h} {n})"
  | .sort s => s!"(admit-sort {s})"
  | .rule r ru => ru.render r

/-- The boot lines of a kernel-v2 test, importing the kernel from `kernelPath`. -/
def bootSrc (kernelPath : String) : List String :=
  [ s!"!(import! &self {kernelPath})",
    "!(bind! &L (new-region board))", "!(bind! &T (new-region board))",
    "!(bind! &A (new-region mailbox))", "!(bind! &W (new-region mailbox))",
    "!(t0:boot &L &T &A &W)",
    "!(bind! &admit (facet &A (send)))", "!(bind! &submit (facet &W (send)))",
    "!(bind! &theorems (facet &T (peek)))", "!(bind! &rules (facet &L (peek)))" ]

/-- **A world's mailboxes as a MeTTa kernel-v2 program**, ending with the accepted board. -/
def renderWorld (kernelPath : String) (w : World String) : String :=
  "\n".intercalate (bootSrc kernelPath ++
    w.A.map (fun m => s!"!(transform &admit () (add-atom &admit {m.render}))") ++
    w.W.map (fun c => s!"!(transform &submit () (add-atom &submit {c.render}))") ++
    ["!(sort-atom (collapse (transform &theorems (every (read (accepted $x))) $x)))"]) ++ "\n"

end Mettapedia.Logic.TierZero.Kernel2
