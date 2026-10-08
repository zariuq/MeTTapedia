import Mettapedia.PLN.TruthValues.PLNClassicTruthFunctions
import Mettapedia.PLN.WorldModel.Provenance.PLNProvenanceInference
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Space

/-!
# Classic PLN v0.9 Examples — Formalized with Provenance

Conformance-style verification of PLN v0.9's three flagship examples
(`hyperon/PLN/examples/`), following the pattern of
`Mettapedia.Languages.MeTTa.PeTTa.Unit`.

Each example:
1. Encodes the PLN knowledge base as a `PeTTaSpace`
2. Verifies queries find correct atoms via `#eval`-checked Bool (like PeTTa.Unit)
3. Models provenance as `Finset (Fin n)` (stamp sets)
4. Proves stamp disjointness and forgetting properties via `decide` (kernel-checked)
-/

namespace Mettapedia.Examples.PLN.ClassicExamples

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Pattern constructors -/

private def sym (s : String) : Pattern := .apply s []
private def app (f : String) (args : List Pattern) : Pattern := .apply f args
private def inh (a b : String) : Pattern := app "Inheritance" [sym a, sym b]

-- ═══════════════════════════════════════════════════════════════════
/-! ## Example 1: DeductionRevision

PLN v0.9 (`DeductionRevision.metta`):
  KB: A→B (obs 0), A→C (obs 1), B→D (obs 2), C→D (obs 3)
  Query: A→D via two deduction paths, then revision.
  Path 1: A→B→D (stamps {0,2}),  Path 2: A→C→D (stamps {1,3})
  Stamps disjoint → revision safe → combined {0,1,2,3}
-/
section DeductionRevision

private def drKB : PeTTaSpace where
  facts := [inh "A" "B", inh "A" "C", inh "B" "D", inh "C" "D"]
  rules := []

-- PeTTa conformance: KB membership (kernel-checked by decide)
theorem dr_AB_found : inh "A" "B" ∈ drKB.storedAtoms := by decide
theorem dr_AC_found : inh "A" "C" ∈ drKB.storedAtoms := by decide
theorem dr_BD_found : inh "B" "D" ∈ drKB.storedAtoms := by decide
theorem dr_CD_found : inh "C" "D" ∈ drKB.storedAtoms := by decide

-- PeTTa conformance: variable query (eval-checked, like PeTTa.Unit)
def dr_var_query : Bool :=
  drKB.spaceMatch (app "Inheritance" [sym "A", .fvar "x"]) (.fvar "x")
    == [sym "B", sym "C"]

def dr_AD_not_in_kb : Bool :=
  drKB.spaceMatch (inh "A" "D") (sym "found") == []

#eval ("dr_var_query", dr_var_query)       -- should be true
#eval ("dr_AD_not_in_kb", dr_AD_not_in_kb) -- should be true

/-! ### Provenance stamps (4 observations) -/

private def dr_stamp1 : Finset (Fin 4) := {⟨0, by omega⟩, ⟨2, by omega⟩}
private def dr_stamp2 : Finset (Fin 4) := {⟨1, by omega⟩, ⟨3, by omega⟩}
private def dr_stampAll : Finset (Fin 4) :=
  {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩}

/-- StampDisjoint: two paths have disjoint provenance (kernel-checked). -/
theorem dr_stamps_disjoint : Disjoint dr_stamp1 dr_stamp2 := by decide

/-- StampConcat: combined stamp = union. -/
theorem dr_stamps_union : dr_stamp1 ∪ dr_stamp2 = dr_stampAll := by decide

/-- All 4 observations used. -/
theorem dr_stampAll_card : dr_stampAll.card = 4 := by decide

/-! ### Forgetting (WM calculus value-add — PLN v0.9 has none) -/

/-- Obs 0 is in path 1's stamp. -/
theorem dr_obs0_in_path1 : (⟨0, by omega⟩ : Fin 4) ∈ dr_stamp1 := by decide

/-- Obs 0 is NOT in path 2's stamp → forgetting obs 0 preserves path 2. -/
theorem dr_obs0_disjoint_path2 :
    Disjoint ({⟨0, by omega⟩} : Finset (Fin 4)) dr_stamp2 := by decide

/-- After forgetting obs 0, path 1 retains only obs 2. -/
theorem dr_path1_after_forget :
    dr_stamp1 \ {⟨0, by omega⟩} = ({⟨2, by omega⟩} : Finset (Fin 4)) := by decide

end DeductionRevision

-- ═══════════════════════════════════════════════════════════════════
/-! ## Example 2: RavenInduction

PLN v0.9 (`RavenInduction.metta`):
  KB: rv1→raven (obs 0), rv2→raven (obs 1), rv1→black (obs 2), rv2→black (obs 3)
  Query: raven→black (by induction from two ravens)
  rv1 data: stamps {0,2},  rv2 data: stamps {1,3}
-/
section RavenInduction

private def riKB : PeTTaSpace where
  facts := [inh "rv1" "raven", inh "rv2" "raven",
            app "Inheritance" [sym "rv1", app "IntSet" [sym "black"]],
            app "Inheritance" [sym "rv2", app "IntSet" [sym "black"]]]
  rules := []

-- PeTTa conformance: KB membership
theorem ri_rv1_raven : inh "rv1" "raven" ∈ riKB.storedAtoms := by decide
theorem ri_rv2_raven : inh "rv2" "raven" ∈ riKB.storedAtoms := by decide

-- PeTTa conformance: variable query (eval-checked)
-- rv1 has TWO inheritance links: raven and (IntSet black)
def ri_rv1_isa : Bool :=
  riKB.spaceMatch (app "Inheritance" [sym "rv1", .fvar "x"]) (.fvar "x")
    == [sym "raven", app "IntSet" [sym "black"]]
#eval ("ri_rv1_isa", ri_rv1_isa)

/-! ### Provenance: rv1 vs rv2 -/

private def ri_rv1_stamp : Finset (Fin 4) := {⟨0, by omega⟩, ⟨2, by omega⟩}
private def ri_rv2_stamp : Finset (Fin 4) := {⟨1, by omega⟩, ⟨3, by omega⟩}

/-- Two ravens' data is independent. -/
theorem ri_rv1_rv2_disjoint : Disjoint ri_rv1_stamp ri_rv2_stamp := by decide

/-- Forgetting rv2 leaves rv1 intact. -/
theorem ri_forget_rv2_preserves_rv1 :
    Disjoint ri_rv1_stamp ri_rv2_stamp := by decide

/-- After forgetting rv2, only rv1's data remains. -/
theorem ri_after_forget_rv2 :
    (ri_rv1_stamp ∪ ri_rv2_stamp) \ ri_rv2_stamp = ri_rv1_stamp := by decide

end RavenInduction

-- ═══════════════════════════════════════════════════════════════════
/-! ## Example 3: FlyingRaven

PLN v0.9 (`FlyingRaven.metta`):
  KB: Sam→Raven (0), Pingu→Penguin (1), Penguin→¬flies (2),
      Raven→Bird (3), Bird→flies (4)
  Sam's chain: Sam→Raven→Bird→flies (stamps {0,3,4})
  Pingu's chain: Pingu→Penguin→¬flies (stamps {1,2})
-/
section FlyingRaven

private def frKB : PeTTaSpace where
  facts := [inh "Sam" "Raven", inh "Pingu" "Penguin",
            inh "Raven" "Bird",
            app "Inheritance" [sym "Bird", app "IntSet" [sym "flies"]]]
  rules := []

-- PeTTa conformance: KB membership
theorem fr_sam_raven : inh "Sam" "Raven" ∈ frKB.storedAtoms := by decide
theorem fr_pingu_penguin : inh "Pingu" "Penguin" ∈ frKB.storedAtoms := by decide
theorem fr_raven_bird : inh "Raven" "Bird" ∈ frKB.storedAtoms := by decide

-- PeTTa conformance: chain lookups (eval-checked)
def fr_sam_to_raven : Bool :=
  frKB.spaceMatch (app "Inheritance" [sym "Sam", .fvar "x"]) (.fvar "x")
    == [sym "Raven"]

def fr_raven_to_bird : Bool :=
  frKB.spaceMatch (app "Inheritance" [sym "Raven", .fvar "x"]) (.fvar "x")
    == [sym "Bird"]

#eval ("fr_sam_to_raven", fr_sam_to_raven)
#eval ("fr_raven_to_bird", fr_raven_to_bird)

/-! ### Provenance stamps (5 observations) -/

private def fr_sam_stamp : Finset (Fin 5) :=
  {⟨0, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩}
private def fr_pingu_stamp : Finset (Fin 5) :=
  {⟨1, by omega⟩, ⟨2, by omega⟩}

/-- Sam's and Pingu's chains are provenance-independent. -/
theorem fr_sam_pingu_disjoint : Disjoint fr_sam_stamp fr_pingu_stamp := by decide

/-- Forgetting Sam→Raven (obs 0) breaks Sam's chain but not Pingu's. -/
theorem fr_forget_sam_preserves_pingu :
    Disjoint ({⟨0, by omega⟩} : Finset (Fin 5)) fr_pingu_stamp := by decide

/-- Bird→flies (obs 4) is in Sam's chain but NOT in Pingu's. -/
theorem fr_obs4_in_sam : (⟨4, by omega⟩ : Fin 5) ∈ fr_sam_stamp := by decide
theorem fr_obs4_not_in_pingu : (⟨4, by omega⟩ : Fin 5) ∉ fr_pingu_stamp := by decide

/-- After forgetting obs 0, Sam's chain retains {3,4} (Raven→Bird, Bird→flies). -/
theorem fr_sam_after_forget_obs0 :
    fr_sam_stamp \ {⟨0, by omega⟩} =
      ({⟨3, by omega⟩, ⟨4, by omega⟩} : Finset (Fin 5)) := by decide

end FlyingRaven

-- ═══════════════════════════════════════════════════════════════════
/-! ## All Checks (PeTTa.Unit style)

Aggregate all conformance checks into a single list for batch evaluation. -/

def plnExampleChecks : List (String × Bool) :=
  [ ("dr_AB_found", decide (inh "A" "B" ∈ (drKB).storedAtoms))
  , ("dr_AC_found", decide (inh "A" "C" ∈ (drKB).storedAtoms))
  , ("dr_BD_found", decide (inh "B" "D" ∈ (drKB).storedAtoms))
  , ("dr_CD_found", decide (inh "C" "D" ∈ (drKB).storedAtoms))
  , ("dr_var_query", dr_var_query)
  , ("dr_AD_not_in_kb", dr_AD_not_in_kb)
  , ("dr_stamps_disjoint", decide (Disjoint dr_stamp1 dr_stamp2))
  , ("dr_stamps_union", decide (dr_stamp1 ∪ dr_stamp2 = dr_stampAll))
  , ("ri_rv1_raven", decide (inh "rv1" "raven" ∈ (riKB).storedAtoms))
  , ("ri_rv2_raven", decide (inh "rv2" "raven" ∈ (riKB).storedAtoms))
  , ("ri_rv1_isa", ri_rv1_isa)
  , ("ri_disjoint", decide (Disjoint ri_rv1_stamp ri_rv2_stamp))
  , ("ri_forget_rv2", decide ((ri_rv1_stamp ∪ ri_rv2_stamp) \ ri_rv2_stamp = ri_rv1_stamp))
  , ("fr_sam_raven", decide (inh "Sam" "Raven" ∈ (frKB).storedAtoms))
  , ("fr_pingu_penguin", decide (inh "Pingu" "Penguin" ∈ (frKB).storedAtoms))
  , ("fr_sam_to_raven", fr_sam_to_raven)
  , ("fr_raven_to_bird", fr_raven_to_bird)
  , ("fr_disjoint", decide (Disjoint fr_sam_stamp fr_pingu_stamp))
  , ("fr_obs4_in_sam", decide ((⟨4, by omega⟩ : Fin 5) ∈ fr_sam_stamp))
  , ("fr_obs4_not_in_pingu", decide ((⟨4, by omega⟩ : Fin 5) ∉ fr_pingu_stamp))
  ]

def plnExampleAllPass : Bool := plnExampleChecks.all (·.2)
def plnExampleFailingCases : List String :=
  plnExampleChecks.filterMap fun c => if c.2 then none else some c.1

#eval ("pln_example_count", plnExampleChecks.length)
#eval ("pln_example_all_pass", plnExampleAllPass)
#eval ("pln_example_failing", plnExampleFailingCases)

end Mettapedia.Examples.PLN.ClassicExamples
