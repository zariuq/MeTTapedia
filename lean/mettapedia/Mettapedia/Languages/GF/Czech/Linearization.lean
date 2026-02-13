/-
# Czech Linearization: Abstract Syntax → Czech Concrete Syntax

Bridges GF abstract syntax trees to Czech morphological forms.

In GF, the abstract/concrete separation means:
- Abstract: language-independent tree structure (CN, NP, Det, VP, S)
- Concrete: language-specific linearization (CzechNoun, case forms, etc.)

This module:
1. Defines Czech concrete types for each abstract category
2. Provides linearization functions from abstract to concrete
3. Proves that abstract equivalence implies linguistic equivalence
-/

import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.Czech.Declensions
import Mettapedia.Languages.GF.Czech.Adjectives
import Mettapedia.Languages.GF.Czech.Verbs
import Mettapedia.Languages.GF.Czech.Pronouns
import Mettapedia.Languages.GF.Czech.Numerals
import Mettapedia.Languages.GF.Czech.Agreement
import Mettapedia.Languages.GF.Czech.Properties

namespace Mettapedia.Languages.GF.Czech.Linearization

open Mettapedia.Languages.GF
open Core Abstract
open Czech Declensions Adjectives Verbs Pronouns Numerals Agreement

/-! ## Czech Concrete Types

In GF, each abstract category maps to a concrete type:
- **CN** (common noun) → `CzechNoun` (inflection table)
- **NP** (noun phrase) → `Case → String` (case-selected form)
- **Det** (determiner) → `Number` (Czech has no articles; Det carries number)
-/

/-- A Czech common noun in concrete syntax is a CzechNoun (paradigm + lemma) -/
abbrev CzechCN := CzechNoun

/-- A Czech NP in concrete syntax: a function from case to surface form.
    "Once a determiner fixes the number, the NP just needs case from context." -/
abbrev CzechNP := Case → String

/-- Czech determiner: carries number (Czech has no articles).
    "ten pán" (sg) vs "ti páni" (pl) -/
abbrev CzechDet := Number

/-! ## Linearization Functions

These implement the GF abstract→concrete mapping for Czech.
-/

/-- Linearize DetCN: combine determiner (number) with CN to produce NP.
    This is the core operation: fixes number, leaves case free. -/
def linDetCN (cn : CzechCN) (det : CzechDet) : CzechNP :=
  fun c => declineFull cn ⟨c, det⟩

/-- Linearize an NP to a surface string by providing case from context -/
def linNP (np : CzechNP) (c : Case) : String := np c

/-- Linearize a CN directly to a specific case×number form -/
def linCN (cn : CzechCN) (c : Case) (n : Number) : String :=
  declineFull cn ⟨c, n⟩

/-- Linearize UseN: a bare noun (N) used as a common noun (CN).
    In Czech, N and CN are the same thing (no articles). -/
def linUseN (noun : CzechCN) : CzechCN := noun

/-! ## Linearization of Abstract Trees

A linearization function that turns abstract trees into Czech strings.
This connects `Abstract.NodeEquiv` to concrete Czech output.
-/

/-- A Czech linearization environment maps leaf names to Czech nouns -/
structure CzechLinEnv where
  lookupCN : String → Option CzechCN

/-- Linearize a leaf node to Czech in a given case context.
    Returns the surface form string, or the leaf name if not in environment. -/
def linearizeLeaf (env : CzechLinEnv) (name : String) (c : Case) (n : Number) : String :=
  match env.lookupCN name with
  | some cn => linCN cn c n
  | none => name

/-- Linearize an abstract tree to Czech.
    For leaves: looks up the noun and declines it.
    For applications: finds the first CN/N leaf among arguments (one level). -/
def linearizeTree (env : CzechLinEnv) (node : AbstractNode) (c : Case) (n : Number) : String :=
  match node with
  | .leaf name _ => linearizeLeaf env name c n
  | .apply _ args =>
    -- Find the first leaf that resolves to a known CN
    match args.findSome? fun arg =>
      match arg with
      | .leaf name _ => env.lookupCN name |>.map fun _ => name
      | _ => none
    with
    | some name => linearizeLeaf env name c n
    | none => "∅"

/-! ## Equivalence Theorems

Connect the three levels of equivalence:
1. `Abstract.NodeEquiv` — same linearization for all parameters
2. `Properties.LinguisticallyEquivalent` — same inflection for all params
3. Concrete string equality
-/

/-- Two CNs produce identical NPs for all determiners iff they are
    linguistically equivalent (same inflection in all case×number slots) -/
theorem cn_equiv_iff_linguistically_equiv (cn₁ cn₂ : CzechCN) :
    Properties.LinguisticallyEquivalent cn₁ cn₂ ↔
    ∀ (det : CzechDet) (c : Case), linDetCN cn₁ det c = linDetCN cn₂ det c := by
  constructor
  · intro h det c
    exact h ⟨c, det⟩
  · intro h ⟨c, n⟩
    exact h n c

/-- linDetCN is a homomorphism: same noun, same number → same NP -/
theorem linDetCN_deterministic (cn : CzechCN) (det : CzechDet) (c : Case) :
    linDetCN cn det c = declineFull cn ⟨c, det⟩ := rfl

/-- linUseN is the identity (Czech N = CN) -/
theorem linUseN_id (cn : CzechCN) : linUseN cn = cn := rfl

/-- Compositionality: linNP ∘ linDetCN = direct decline -/
theorem linNP_linDetCN (cn : CzechCN) (det : CzechDet) (c : Case) :
    linNP (linDetCN cn det) c = declineFull cn ⟨c, det⟩ := rfl

/-! ## Building a Czech Linearization for NodeEquiv

Construct a concrete `NodeLinearize CzechParams` so that
`Abstract.NodeEquiv` becomes meaningful for Czech.
-/

/-- Build a Czech linearization function from an environment.
    This bridges Abstract.NodeLinearize to Czech concrete syntax. -/
def czechLinearize (env : CzechLinEnv) : Abstract.NodeLinearize CzechParams :=
  fun node params => linearizeTree env node params.case params.number

/-- NodeEquiv under Czech linearization implies: for all case×number,
    two trees produce the same Czech string -/
theorem nodeEquiv_implies_string_eq (env : CzechLinEnv) (n₁ n₂ : AbstractNode) :
    Abstract.NodeEquiv (czechLinearize env) n₁ n₂ →
    ∀ (c : Case) (num : Number),
      linearizeTree env n₁ c num = linearizeTree env n₂ c num := by
  intro h c num
  exact h ⟨c, num⟩

/-! ## Extended Concrete Types

Concrete types for adjectives, verbs, pronouns, and numerals.
-/

/-- A Czech adjective in concrete syntax: dispatches AdjParams to surface form -/
abbrev CzechAdj := AdjParams → String

/-- A Czech verb phrase: dispatches agreement + polarity to surface form -/
abbrev CzechVP := Agr → Bool → String

/-- A Czech pronoun in concrete syntax: dispatches case to surface form -/
abbrev CzechPron := Case → String

/-! ## Extended Linearization Functions -/

/-- Linearize ModCN: adjective modifying a common noun.
    The adjective agrees with the noun in gender, number, and case.
    Returns "adj noun" string. -/
def linModCN (adj : CzechAdj) (cn : CzechCN) (c : Case) (n : Number) : String :=
  let adjStr := adj ⟨cn.gender, n, c⟩
  let nounStr := declineFull cn ⟨c, n⟩
  adjStr ++ " " ++ nounStr

/-- Linearize PredVP: subject NP + verb phrase.
    Subject in nominative, verb agrees with subject. -/
def linPredVP (subj : CzechNP) (vp : CzechVP) (agr : Agr) (pol : Bool) : String :=
  subj .Nom ++ " " ++ vp agr pol

/-- Linearize a numeral-governed NP using NumSize agreement.
    The numeral size determines whether the noun is Sg, Pl, or Pl Gen. -/
def linDetCNNum (cn : CzechCN) (det : Numerals.Determiner) (c : Case) : String :=
  let nounForm := numSizeForm
    (fun n cas => declineFull cn ⟨cas, n⟩)
    det.size c
  let detStr := det.s cn.gender c
  detStr ++ " " ++ nounForm

/-- Linearize a personal pronoun to a surface form given case context -/
def linPron (pf : PronForms) (c : Case) : String :=
  match c with
  | .Nom => pf.nom
  | .Gen => pf.gen
  | .Dat => pf.dat
  | .Acc => pf.acc
  | .Voc => pf.nom  -- vocative = nominative for pronouns
  | .Loc => pf.loc
  | .Ins => pf.ins

/-! ## Extended Theorems -/

/-- linModCN produces "adj noun" for any case and number -/
theorem linModCN_format (adj : CzechAdj) (cn : CzechCN) (c : Case) (n : Number) :
    linModCN adj cn c n = adj ⟨cn.gender, n, c⟩ ++ " " ++ declineFull cn ⟨c, n⟩ := rfl

/-- linPredVP produces "subj verb" -/
theorem linPredVP_format (subj : CzechNP) (vp : CzechVP) (agr : Agr) (pol : Bool) :
    linPredVP subj vp agr pol = subj .Nom ++ " " ++ vp agr pol := rfl

end Mettapedia.Languages.GF.Czech.Linearization
