import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRefined

/-!
# Located ambients

A flat calculus of located atoms, in which the tree of ambients is a link structure over names. A location is a name:

- `LAmb[p, ℓ, m]`: the ambient named `m`, standing at location `p`, whose content stands at location `ℓ`;
- `LOpened[p, ℓ, m]`: the ambient named `m` at `p`, opened: what stands at its location `ℓ` stands at `p`;
- `LIn[ℓ, n, K]`, `LOut[ℓ, n, K]`, `LOpen[ℓ, n, K]`: a capability standing at location `ℓ`, its continuation `K`
  released at `ℓ`;
- inaction, parallel composition as a bare bag, restriction of a name and replication of any process;
- for communication: capabilities as terms of their own sort (`in n`, `out n`, `open n`, `ε` and paths), a prefix by
  a capability variable standing at a location `LCap[ℓ, x, K]`, and the inputs and outputs of names and
  capabilities standing at a location (`LInName[ℓ, λx.K]`, `LOutName[ℓ, n]`, `LInCap[ℓ, λx.K]`, `LOutCap[ℓ, M]`), an
  input's body released at its location.

Its declared laws are exactly those of restriction and of replication (`locatedLanguage`), so the restriction-block
theory decides its static theory, with the refined labelling. The ambients' own law, that a restriction crosses an
ambient boundary it does not name, needs no law here: an ambient's content stands at a location bound by a restriction
around the ambient's marker and its content, and moving another restriction across that boundary is scope extrusion
and exchange of restrictions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Located

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext parameterType? UsesBareCollection
  isObjectPattern)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (BagPresentation)

/-- The blocks of located ambients: inaction, restriction, processes and names. -/
abbrev locatedBlock : Block := ⟨"LZero", "LNu", "Proc", "Name", [], []⟩

/-- Its blocks with replication, read by the refined labelling. -/
abbrev locatedRepBlock : ReplicationBlock := ⟨locatedBlock, "LRep", true⟩

/-- A capability standing at a location, with a continuation released there. -/
def capabilityRule (label keyword : String) : GrammarRule :=
  { label := label, category := "Proc",
    params := [.simple "l" (.base "Name"), .simple "n" (.base "Name"), .simple "k" (.base "Proc")],
    syntaxPattern := [.nonTerminal "l", .terminal "@", .terminal keyword, .nonTerminal "n", .terminal ".",
      .nonTerminal "k"] }

/-- A capability over a name. -/
def capTermRule (label keyword : String) : GrammarRule :=
  { label := label, category := "Cap", params := [.simple "n" (.base "Name")],
    syntaxPattern := [.terminal keyword, .nonTerminal "n"] }

/-- An input standing at a location, binding a variable of a sort in its body. -/
def inputRule (label : String) (sort : String) : GrammarRule :=
  { label := label, category := "Proc",
    params := [.simple "l" (.base "Name"),
      .abstraction "body" (TypeExpr.arrow (TypeExpr.base sort) (TypeExpr.base "Proc"))],
    syntaxPattern := [.nonTerminal "l", .terminal "@", .terminal "(", .terminal sort, .terminal ")",
      .nonTerminal "body"] }

/-- An output standing at a location, of a term of a sort. -/
def outputRule (label : String) (sort : String) : GrammarRule :=
  { label := label, category := "Proc",
    params := [.simple "l" (.base "Name"), .simple "m" (.base sort)],
    syntaxPattern := [.nonTerminal "l", .terminal "@", .terminal "<", .nonTerminal "m", .terminal ">"] }

/-- **Located ambients.** -/
def locatedCalc : LanguageDef := {
  name := "LocatedAmbients",
  types := ["Proc", "Name", "Cap"],
  terms := [
    { label := "LZero", category := "Proc", params := [], syntaxPattern := [.terminal "0"] },
    { label := "LPar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
      algebra? := some { flatten := true, unit := some "LZero" } },
    { label := "LNu", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "ν", .nonTerminal "body"] },
    { label := "LRep", category := "Proc",
      params := [.simple "p" (TypeExpr.base "Proc")],
      syntaxPattern := [.terminal "!", .nonTerminal "p"] },
    { label := "LAmb", category := "Proc",
      params := [.simple "p" (.base "Name"), .simple "l" (.base "Name"), .simple "m" (.base "Name")],
      syntaxPattern := [.nonTerminal "p", .terminal "@", .nonTerminal "m", .terminal "[", .nonTerminal "l",
        .terminal "]"] },
    capabilityRule "LIn" "in",
    capabilityRule "LOut" "out",
    capabilityRule "LOpen" "open",
    { label := "LOpened", category := "Proc",
      params := [.simple "p" (.base "Name"), .simple "l" (.base "Name"), .simple "m" (.base "Name")],
      syntaxPattern := [.nonTerminal "p", .terminal "@", .terminal "opened", .nonTerminal "m", .terminal "[",
        .nonTerminal "l", .terminal "]"] },
    capTermRule "CapIn" "in",
    capTermRule "CapOut" "out",
    capTermRule "CapOpen" "open",
    { label := "CapEps", category := "Cap", params := [], syntaxPattern := [.terminal "ε"] },
    { label := "CapPath", category := "Cap", params := [.simple "m" (.base "Cap"), .simple "k" (.base "Cap")],
      syntaxPattern := [.nonTerminal "m", .terminal ".", .nonTerminal "k"] },
    { label := "LCap", category := "Proc",
      params := [.simple "l" (.base "Name"), .simple "m" (.base "Cap"), .simple "k" (.base "Proc")],
      syntaxPattern := [.nonTerminal "l", .terminal "@", .nonTerminal "m", .terminal ":", .nonTerminal "k"] },
    inputRule "LInName" "Name",
    outputRule "LOutName" "Name",
    inputRule "LInCap" "Cap",
    outputRule "LOutCap" "Cap"
  ],
  equations := replicationBlockLaws locatedRepBlock,
  rewrites := [] }

/-- The parallel constructor declares the bag monoid with inaction as its unit. -/
theorem locatedBagPresentation : BagPresentation locatedCalc locatedCalc.terms[1] (some "LZero") where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  otherParameters := by
    intro rule member different parameter present
    simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simp at present
    · exact False.elim (different rfl)
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl | rfl <;> rfl
  unitAuthored := by
    intro unit same
    cases Option.some.inj same
    exact ⟨locatedCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩

/-- **Located ambients are a calculus with restriction and replication.** -/
instance locatedLanguage : ReplicationLanguage locatedCalc locatedRepBlock where
  bag := ⟨locatedCalc.terms[1], ParallelBag.ofBare (locatedBagPresentation.asBare rfl), rfl⟩
  equations := rfl
  restrictAuthored := ⟨locatedCalc.terms[2], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp_all
  unitShape := by
    intro rule member labelIs
    simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp_all
  multisetShape := by
    intro rule member listed
    simp at listed
  emptyUnitShape := by
    intro label listed
    simp at listed
  emptyUnitAuthored := by
    intro label listed
    simp at listed
  labelsUnique := by decide
  params := by
    intro rule member notBare _ parameter present
    simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare _ parameter present domain sort found
    simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl | rfl <;> simp_all [parameterType?]
  replicateAuthored := ⟨locatedCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp_all
  replicateFresh := by decide

end Mettapedia.Languages.ProcessCalculi.Ambient.Located
