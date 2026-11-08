import Mettapedia.Logic.ASP.Certificate
import Mettapedia.Logic.ASP.Checker

/-!
# Controls for Hall steps in certificates

Values are computed by the kernel (`decide +kernel`).

`pigeonholes n m` puts `n` pigeons into `m` holes: each placement is chosen freely by an even
loop, each pigeon has an at-least-one rule over its placements, and each hole has an exclusion
rule for every two pigeons. Its at-least-one rules come first, so the groups of a Hall step over
all pigeons are the rule numbers `0, …, n - 1`; the cliques are the holes.

* **More pigeons than holes**: the certificate of one Hall step, deriving the empty clause from
  all pigeons against all holes (`hallCertificate`), is accepted for three pigeons in two holes
  (`php32_certificate`), so that program has no stable model (`php32_no_stable_by_certificate`),
  and for four pigeons in three holes (`php43_certificate`).
* Refused Hall steps, each next to an accepted one:
  - two pigeons and two holes, as many cliques as groups (`php22_as_many_cliques_refused`). Two
    pigeons fit into two holes (`php22_stable`), and no certificate is accepted for the program
    at all (`php22_certificates_refused`). With one clique fewer and its atoms in the clause, the
    step is accepted (`php22_covered_step`);
  - two pigeons against the clique of hole `0` with the clause `in 0 1`: the group atom `in 1 1` is
    neither in the clause nor in a clique (`php22_uncovered_refused`), and the clause is false in a
    stable model (`php22_uncovered_unsound`). With `in 1 1` added to the clause the step is
    accepted (`php22_covered_step`);
  - three pigeons and two holes without the exclusion of pigeons `1` and `2` in hole `0`: the
    clique of hole `0` has a pair without an exclusion rule (`php32Gap_clique_refused`), and the
    program has a stable model (`php32Gap_stable`). With that exclusion rule the same certificate
    is accepted (`php32_certificate`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.HallStepControls

open Program Mettapedia.GSLT.Logic PropositionalFormula

/-- The atom `m * p + h`: pigeon `p` sits in hole `h`. -/
def inAtom (m p h : ℕ) : ℕ := m * p + h

/-- `n` pigeons in `m` holes, over `N = n * m` placements. The placement `x` is chosen against
`N + x`; the at-least-one rule of pigeon `p` has the head `2N + p`; the exclusion of pigeons
`p < q` in hole `h` has the head `2N + n + (h * n + p) * n + q`. -/
def pigeonholes (n m : ℕ) : Program ℕ :=
  (List.range n).map (fun p =>
      ⟨2 * (n * m) + p, [], (List.range m).map (inAtom m p) ++ [2 * (n * m) + p]⟩) ++
    (List.range m).flatMap (fun h => (List.range n).flatMap fun p =>
      ((List.range n).filter (p < ·)).map fun q =>
        ⟨2 * (n * m) + n + (h * n + p) * n + q, [inAtom m p h, inAtom m q h],
          [2 * (n * m) + n + (h * n + p) * n + q]⟩) ++
    (List.range (n * m)).flatMap fun x => [⟨x, [], [n * m + x]⟩, ⟨n * m + x, [], [x]⟩]

/-- The variable number of an atom of `P`. -/
def num (P : Program ℕ) (a : ℕ) : ℕ := P.index (.atom a)

/-- The holes as cliques of `n` pigeons, in the variable numbers of `P`. -/
def holeCliques (P : Program ℕ) (n m : ℕ) : List (List ℕ) :=
  (List.range m).map fun h => (List.range n).map fun p => num P (inAtom m p h)

/-- One Hall step: the empty clause, from all `n` pigeons against the `m` holes. -/
def hallCertificate (n m : ℕ) : List CertStep :=
  [.hall 1000 [] (List.range n) (holeCliques (pigeonholes n m) n m)]

/-! ## More pigeons than holes -/

theorem php32_certificate : (pigeonholes 3 2).checkCert (hallCertificate 3 2) = true := by
  decide +kernel

theorem php32_no_stable_by_certificate (M : Set ℕ) : ¬ (pigeonholes 3 2).Stable M :=
  (pigeonholes 3 2).checkCert_sound php32_certificate M

theorem php43_certificate : (pigeonholes 4 3).checkCert (hallCertificate 4 3) = true := by
  decide +kernel

/-! ## Refused Hall steps -/

/-- Two pigeons fit into two holes: pigeon `0` in hole `0`, pigeon `1` in hole `1`. -/
theorem php22_stable : (pigeonholes 2 2).Stable ↑({0, 3, 5, 6} : Finset ℕ) :=
  ((pigeonholes 2 2).isStable_iff _).mp (by decide +kernel)

/-- As many cliques as groups. -/
theorem php22_as_many_cliques_refused : (pigeonholes 2 2).checkCert (hallCertificate 2 2) = false := by
  decide +kernel

/-- No certificate is accepted for a program with a stable model. -/
theorem php22_certificates_refused (steps : List CertStep) : (pigeonholes 2 2).checkCert steps = false := by
  cases accepted : (pigeonholes 2 2).checkCert steps with
  | false => rfl
  | true => exact absurd php22_stable ((pigeonholes 2 2).checkCert_sound accepted _)

/-- The clause `in 1 1 ∨ in 0 1` over the clique of hole `0` is accepted as a step. -/
theorem php22_covered_step :
    ((pigeonholes 2 2).certStep (pigeonholes 2 2).inputs
      (.hall 1000 [.pos (num (pigeonholes 2 2) (inAtom 2 1 1)), .pos (num (pigeonholes 2 2) (inAtom 2 0 1))]
        (List.range 2) ((holeCliques (pigeonholes 2 2) 2 2).take 1))).isSome = true := by
  decide +kernel

/-- The clause `in 0 1` alone leaves the group atom `in 1 1` uncovered. -/
theorem php22_uncovered_refused :
    (pigeonholes 2 2).certStep (pigeonholes 2 2).inputs
      (.hall 1000 [.pos (num (pigeonholes 2 2) (inAtom 2 0 1))] (List.range 2)
        ((holeCliques (pigeonholes 2 2) 2 2).take 1)) = none := by
  decide +kernel

/-- The clause `in 0 1` is false in the stable model with pigeon `0` in hole `0`. -/
theorem php22_uncovered_unsound :
    Clause.sat ((pigeonholes 2 2).encode (canonical ↑({0, 3, 5, 6} : Finset ℕ)))
      [.pos (num (pigeonholes 2 2) (inAtom 2 0 1))] = false := by
  rw [← finValuation_eq_canonical]
  decide +kernel

/-- Three pigeons in two holes without the exclusion of pigeons `1` and `2` in hole `0`. -/
def php32Gap : Program ℕ :=
  (pigeonholes 3 2).erase ⟨20, [inAtom 2 1 0, inAtom 2 2 0], [20]⟩

/-- Pigeon `0` in hole `1`, pigeons `1` and `2` in hole `0`. -/
theorem php32Gap_stable : php32Gap.Stable ↑({1, 2, 4, 6, 9, 11} : Finset ℕ) :=
  (php32Gap.isStable_iff _).mp (by decide +kernel)

/-- The clique of hole `0` has the pair of pigeons `1` and `2`, without an exclusion rule. -/
theorem php32Gap_clique_refused :
    php32Gap.checkCert [.hall 1000 [] (List.range 3) (holeCliques php32Gap 3 2)] = false := by
  decide +kernel

/-- The atom numbers shift with the erased rule; the cliques are those of the same atoms. -/
theorem php32Gap_cliques :
    (holeCliques php32Gap 3 2).map (List.filterMap php32Gap.atomOf) =
      (holeCliques (pigeonholes 3 2) 3 2).map (List.filterMap (pigeonholes 3 2).atomOf) := by
  decide +kernel

/-! ## A Hall step in the C driver's numbering

Three pigeons in two holes in the C driver's rule order: placement `x` is chosen against
`x + 1` (for even `x`), pigeon `p` has the at-least-one rule with head `12 + p`, and each hole
an exclusion rule for every two pigeons. Each of these heads is a falsum atom, so their rules
have no body variables in the completion, and the bodies of the choice rules are unit bodies, so
the variables are the atoms alone. The C
solver's literals `±(n + 1)` are the literals of variable `n` here, and its groups and cliques carry
over unchanged: the Hall step from all pigeons against both holes is accepted
(`cPig32_certificate`), and with the clique of hole `1` dropped it is refused
(`cPig32_without_hole_refused`). -/

/-- The C driver's program for three pigeons in two holes. -/
def cPig32 : Program ℕ :=
  [⟨0, [], [1]⟩, ⟨1, [], [0]⟩, ⟨2, [], [3]⟩, ⟨3, [], [2]⟩, ⟨4, [], [5]⟩, ⟨5, [], [4]⟩,
   ⟨6, [], [7]⟩, ⟨7, [], [6]⟩, ⟨8, [], [9]⟩, ⟨9, [], [8]⟩, ⟨10, [], [11]⟩, ⟨11, [], [10]⟩,
   ⟨12, [], [0, 2, 12]⟩, ⟨13, [], [4, 6, 13]⟩, ⟨14, [], [8, 10, 14]⟩,
   ⟨15, [0, 4], [15]⟩, ⟨16, [0, 8], [16]⟩, ⟨17, [4, 8], [17]⟩,
   ⟨18, [2, 6], [18]⟩, ⟨19, [2, 10], [19]⟩, ⟨20, [6, 10], [20]⟩]

/-- The variables are the 21 atoms; the placements in the holes have the numbers of the cliques. -/
theorem cPig32_numbering : cPig32.varList.length = 21 ∧
    [0, 2, 4, 6, 8, 10].map (fun a => num cPig32 a) = [10, 16, 12, 18, 13, 19] := by
  decide +kernel

theorem cPig32_certificate :
    cPig32.checkCert [.hall 112 [] [12, 13, 14] [[10, 12, 13], [16, 18, 19]]] = true := by
  decide +kernel

theorem cPig32_without_hole_refused :
    cPig32.checkCert [.hall 112 [] [12, 13, 14] [[10, 12, 13]]] = false := by
  decide +kernel

end Mettapedia.Logic.ASP.HallStepControls
