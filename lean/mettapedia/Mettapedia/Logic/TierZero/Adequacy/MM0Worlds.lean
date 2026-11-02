import Mettapedia.Logic.TierZero.Adequacy.MM0
import Mettapedia.Logic.TierZero.Kernel2.Render

/-!
# MM0 claims as kernel-v2 worlds

The MM0 presentation of a finite environment and MM0 claims, as a world of admissions and claims
with string names (`Name.str`), so that the Lean kernel and the MeTTa kernel-v2 run on identical
inputs with bound variables: the claims' formals carry their kinds, `(scope X)` for a bound variable
and `(dep X (I …))` for a regular one (`Claim.render`).

`Controls.nfWorld`: the rules of the control environment `MM0.Controls.E` and the claims of
`nf_accepted` (as `thm1`), `nf_refused` (as `thm2`), and `thm3`, `nf` at the compound formula
`(imp ψ χ)`. An MM0 claim declares its binders' independence conditions and its bound variables as
names, so `thm1` and `thm3` are accepted and become rules: `thm3`'s proof decides
`(absent-from x (imp ψ χ))`, which the declared `(absent-from x ψ)` and `(absent-from x χ)` give by
structure. `thm2` is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0

open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.MM0.Kernel

/-- A rule name as a string. -/
def Name.str : Name → String
  | .con c => s!"con{c}"
  | .thm t => s!"thm{t}"
  | .cvRefl s => s!"cv-refl{s}"
  | .cvSymm => "cv-symm"
  | .cvTrans => "cv-trans"
  | .cvCong c => s!"cv-cong{c}"
  | .unfold c => s!"unfold{c}"
  | .conv => "conv"

/-- The judgments of the MM0 presentation: `(bv s X)`, `(ty s E)`, `(cv s E F)`, `(pf E)`. -/
def mm0Judgments : List (Admission String) :=
  [.judgment "bv" 2, .judgment "ty" 2, .judgment "cv" 3, .judgment "pf" 1]

/-- The rules of an environment at the given names, as admissions. -/
def admissionsOf (E : MM0Env) (names : List Name) : List (Admission String) :=
  names.filterMap fun r => (rules E r).map fun ru => .rule r.str ru

/-- A claim with its id and its proof's rule names as strings. -/
def strClaim (c : Claim Name) : Claim String :=
  ⟨c.id.str, c.formals, c.dummies, c.hyps, c.locals, c.dvl, c.concl, c.terms,
    c.proof.map fun nd => ⟨nd.name, nd.rule.str, nd.kids⟩, c.root⟩

namespace Controls

/-- The rule names of the control environment. -/
def nfNames : List Name :=
  [.con 0, .con 1, .thm 0, .cvRefl 0, .cvRefl 1, .cvSymm, .cvTrans, .cvCong 0, .cvCong 1, .conv]

/-- `x` bound; `ψ`, `χ` regular, independent of `x`. -/
def ctx₃ : Context := [.bound 1, .regular 0 ∅, .regular 0 ∅]

/-- `(imp ψ χ) → ∀x (imp ψ χ)`. -/
def goal₃ : Preterm := imp (imp (.var 1) (.var 2)) (all (.var 0) (imp (.var 1) (.var 2)))

/-- `imp` from the formulas' sorts (hypotheses 2 and 3), then `nf` at `x` (hypothesis 0) and it. -/
def nfImpProof : List (CProofNode Name) := [⟨0, .con 0, [.hyp 2, .hyp 3]⟩, ⟨1, .thm 0, [.hyp 0, .node 0]⟩]

/-- **`nf_accepted`, `nf_refused` and `nf` at a compound formula as one world.** -/
def nfWorld : World String :=
  ⟨⟨[], [], []⟩, [], mm0Judgments ++ admissionsOf E nfNames,
    [strClaim (mm0Claim (.thm 1) ctx₁ [] goal nfProof (.node 0)),
     strClaim (mm0Claim (.thm 2) ctx₂ [] goal nfProof (.node 0)),
     strClaim (mm0Claim (.thm 3) ctx₃ [] goal₃ nfImpProof (.node 1))], []⟩

/-- `thm1` (`ψ` independent of `x`) and `thm3` are accepted; `thm2` (`φ` over `x`) is refused. -/
theorem nfWorld_accepted : (runWorld 100 nfWorld).T = ["thm1", "thm3"] := by decide +kernel

/-- `thm1` and `thm3` become rules: their proofs decide independence only as the claims declare it,
directly or by structure. -/
theorem nfWorld_rules :
    ((runWorld 100 nfWorld).L.rules.map Prod.fst) = nfNames.map Name.str ++ ["thm1", "thm3"] := by
  decide +kernel

end Controls

end Mettapedia.Logic.TierZero.Adequacy.MM0
