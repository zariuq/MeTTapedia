/-
# English Linearization: Abstract Syntax to English Concrete Syntax

Bridges GF abstract syntax trees to English morphological forms,
following the same pattern as Czech/Linearization.lean.

Provides:
1. EnglishLinEnv: maps leaf names to English nouns
2. linearizeTree: abstract tree to English string
3. englishLinearize: NodeLinearize instance for OSLF bridge
4. Bridge theorems connecting NodeEquiv to English strings

## References
- Czech/Linearization.lean: pattern followed
- GF Abstract.lean: AbstractNode, NodeEquiv, NodeLinearize
-/

import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.English.Syntax
import Mettapedia.Languages.GF.English.Properties

namespace Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Core Abstract
open English Syntax

/-! ## English Linearization Environment -/

/-- An English linearization environment maps leaf names to English nouns -/
structure EnglishLinEnv where
  lookupCN : String → Option EnglishNoun

/-- Linearize a leaf node to English in a given case and number context -/
def linearizeLeaf (env : EnglishLinEnv) (name : String) (c : Case) (n : Number) : String :=
  match env.lookupCN name with
  | some cn => cn.s n c
  | none => name

/-- Linearize an abstract tree to English.
    For leaves: looks up the noun and declines it.
    For applications: finds the first CN/N leaf among arguments. -/
def linearizeTree (env : EnglishLinEnv) (node : AbstractNode) (c : Case) (n : Number) : String :=
  match node with
  | .leaf name _ => linearizeLeaf env name c n
  | .apply _ args =>
    match args.findSome? fun arg =>
      match arg with
      | .leaf name _ => env.lookupCN name |>.map fun _ => name
      | _ => none
    with
    | some name => linearizeLeaf env name c n
    | none => "∅"

/-! ## NodeLinearize Instance -/

/-- Build an English linearization function from an environment.
    Bridges Abstract.NodeLinearize to English concrete syntax. -/
def englishLinearize (env : EnglishLinEnv) : Abstract.NodeLinearize EnglishParams :=
  fun node params => linearizeTree env node params.case params.number

/-! ## Bridge Theorems -/

/-- NodeEquiv under English linearization implies: for all case x number,
    two trees produce the same English string -/
theorem nodeEquiv_implies_string_eq (env : EnglishLinEnv) (n1 n2 : AbstractNode) :
    Abstract.NodeEquiv (englishLinearize env) n1 n2 →
    ∀ (c : Case) (num : Number),
      linearizeTree env n1 c num = linearizeTree env n2 c num := by
  intro h c num
  exact h ⟨c, num⟩

/-- Leaf linearization respects the environment -/
theorem linearizeLeaf_found (env : EnglishLinEnv) (name : String) (cn : EnglishNoun)
    (h : env.lookupCN name = some cn) (c : Case) (n : Number) :
    linearizeLeaf env name c n = cn.s n c := by
  simp [linearizeLeaf, h]

/-- Leaf linearization falls back to name when not in environment -/
theorem linearizeLeaf_notFound (env : EnglishLinEnv) (name : String)
    (h : env.lookupCN name = none) (c : Case) (n : Number) :
    linearizeLeaf env name c n = name := by
  simp [linearizeLeaf, h]

/-! ## Extended Concrete Types

Concrete types for full sentence linearization with tense/polarity.
-/

/-- Extended English parameters for full sentence linearization -/
structure EnglishSentenceParams where
  tense : Tense
  anteriority : Anteriority
  polarity : CPolarity
  order : Order
  deriving DecidableEq, Repr, Inhabited

/-- Full English linearization with sentence-level parameters -/
def englishSentenceLinearize (env : EnglishLinEnv)
    (mkVP : String → EnglishVP)
    (node : AbstractNode) (sp : EnglishSentenceParams) : String :=
  match node with
  | .leaf name _ =>
    match env.lookupCN name with
    | some cn =>
      let np := linDetCN theDefArt cn
      let vp := mkVP name
      let cl := linPredVP np vp
      cl.s sp.tense sp.anteriority sp.polarity sp.order
    | none => name
  | _ => "∅"

end Mettapedia.Languages.GF.English.Linearization
