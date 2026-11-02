import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationInstance

/-!
# The refined labelling

The canonical form reads a block under orders of its restrictions and keeps the least reading. Read under every
order, a block of `n` restrictions has `n!` readings. A refined block (`ReplicationBlock.refined`) is read only under
the orders that sort its restrictions by their signatures (`readingOrders`, `signatureOf`): the profiles of the
components that mention a restriction (how many of the restrictions such a component mentions, and whether it is a
replication). Restrictions of one signature are read in every order among themselves, so a block whose restrictions
have distinct signatures has one reading.

- **The laws do not read how a block is read**, so a calculus with restriction and replication is one for its refined
  block too (`ReplicationLanguage.withRefined`), and every theorem of the replication theory holds for it.
- **The refined labelling decides the same equivalence as the least reading over every order** (`canonR_refined_iff`):
  on object terms of a sort, the refined canonical forms agree exactly when the canonical forms do, since both decide
  the static theory.
- **Controls** on the minimal calculus with replication: a block of five restrictions with distinct signatures has one
  reading order where every order gives 120 (`refined_orders_one`), and the refined canonical form tells two
  arrangements of it equivalent and a variant apart (`refined_same`, `refined_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

variable {language : LanguageDef} {block : ReplicationBlock}

/-- **A calculus with restriction and replication is one for its block read either way**: its laws do not read how a
block is read. -/
theorem ReplicationLanguage.withRefined (laws : ReplicationLanguage language block) (refined : Bool) :
    ReplicationLanguage language { block with refined := refined } where
  toBlockSignature := laws.toBlockSignature
  equations := laws.equations
  replicateAuthored := laws.replicateAuthored
  replicateShape := laws.replicateShape
  replicateFresh := laws.replicateFresh

/-- **The refined labelling decides the same equivalence as the least reading over every order**: on object terms
of a sort, the canonical forms read either way agree exactly when the other's do. -/
theorem canonR_refined_iff [laws : ReplicationLanguage language block] {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {first second : Pattern} {sort : String}
    (firstTyped : HasType language free bound first (.base sort))
    (secondTyped : HasType language free bound second (.base sort)) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) (refined : Bool) :
    canonR { block with refined := refined } first = canonR { block with refined := refined } second ↔
      canonR block first = canonR block second := by
  have refinedLaws := laws.withRefined refined
  rw [← equationEquiv_iff_canonR_eq (block := { block with refined := refined }) context firstTyped secondTyped
    firstObject secondObject, equationEquiv_iff_canonR_eq (block := block) context firstTyped secondTyped
    firstObject secondObject]

/-! ## Controls -/

namespace ReplicationInstance

/-- The minimal calculus's block, read only under the orders sorting its restrictions by their signatures. -/
abbrev refinedBlock : ReplicationBlock := { repBlock with refined := true }

instance refinedLanguage : ReplicationLanguage repCalc refinedBlock := repLanguage.withRefined true

private def out (channel datum : Pattern) : Pattern := .apply "ROut" [channel, datum]
private def bang (process : Pattern) : Pattern := .apply "RRep" [process]
private def a : Pattern := .fvar "a"
private def b : Pattern := .fvar "b"

/-- Five restrictions with distinct signatures: `r₁⟨a⟩ | !r₂⟨a⟩ | r₃⟨r₄⟩ | !r₄⟨a⟩ | !r₅⟨r₃⟩` under `(νr₁…r₅)`, the
innermost restriction `r₁` being the bound variable `0`. -/
def fiveComponents : List Pattern :=
  [out (.bvar 0) a, bang (out (.bvar 1) a), out (.bvar 2) (.bvar 3), bang (out (.bvar 3) a),
    bang (out (.bvar 4) (.bvar 2))]

/-- **One reading order where every order gives 120.** -/
theorem refined_orders_one :
    (readingOrders refinedBlock ⟨5, fiveComponents⟩).length = 1 ∧
      (readingOrders repBlock ⟨5, fiveComponents⟩).length = 120 := by
  decide +kernel

/-- The block read as a process. -/
def five : Pattern := Prenex.toPattern repBlock.toBlock ⟨5, fiveComponents⟩

/-- The same process with its restrictions bound in the opposite order and its components in another order. -/
def fiveRearranged : Pattern := Prenex.toPattern repBlock.toBlock
  ⟨5, [bang (out (.bvar 0) (.bvar 2)), out (.bvar 4) a, bang (out (.bvar 1) a), out (.bvar 2) (.bvar 1),
    bang (out (.bvar 3) a)]⟩

/-- A variant sending on `b` where the process sends on `a`. -/
def fiveVariant : Pattern := Prenex.toPattern repBlock.toBlock
  ⟨5, [out (.bvar 0) b, bang (out (.bvar 1) a), out (.bvar 2) (.bvar 3), bang (out (.bvar 3) a),
    bang (out (.bvar 4) (.bvar 2))]⟩

/-- **The refined canonical form tells the two arrangements equivalent.** -/
theorem refined_same : canonR refinedBlock five = canonR refinedBlock fiveRearranged := by
  decide +kernel

/-- **The refined canonical form tells the variant apart.** -/
theorem refined_apart : canonR refinedBlock five ≠ canonR refinedBlock fiveVariant := by
  decide +kernel

end ReplicationInstance

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
