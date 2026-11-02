import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Signature

/-!
# The laws of replication, over any calculus with restriction

A calculus with replication `!` declares, besides the laws of its parallel bag and of restriction, the laws of
replication in the form spatial logics read processes by:

- `!P = {P, !P}`, unfolding (`replicationUnfoldOf`);
- `!0 = 0` (`replicationNilOf`);
- `!!P = !P` (`replicationTwiceOf`);
- `!{P, Q} = {!P, !Q}` (`replicationParOf`);
- `{!P, !P} = !P` (`replicationIdempotentOf`).

Every law relates strongly bisimilar processes. Read with them, a replicated process stands for unboundedly many
copies, and the static theory is equality of multisets whose multiplicities may be infinite. Restriction does not
commute with replication: `!(νx) P` gives every copy its own name, while `(νx) !P` shares one.

`ReplicationLanguage` says what the theory needs of a language: the restriction-block signature with these laws
besides those of restriction, and a replication constructor taking one process to a process.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The signature of a calculus's blocks with replication**: a block signature and the replication
constructor. -/
structure ReplicationBlock extends Block where
  replicate : String
  /-- Whether the canonical form reads a block only under the orders of its restrictions that sort them by their
  signatures (`readingOrders`), rather than under every order. Both decide the same static theory. -/
  refined : Bool
  deriving DecidableEq, Repr

/-- `!P = {P, !P}` -/
def replicationUnfoldOf (block : ReplicationBlock) : Equation where
  name := "ReplicationUnfold"
  typeContext := [("P", .base block.proc)]
  premises := []
  left := .apply block.replicate [.fvar "P"]
  right := .collection .hashBag [.fvar "P", .apply block.replicate [.fvar "P"]] none

/-- `!0 = 0` -/
def replicationNilOf (block : ReplicationBlock) : Equation where
  name := "ReplicationNil"
  typeContext := []
  premises := []
  left := .apply block.replicate [.apply block.unit []]
  right := .apply block.unit []

/-- `!!P = !P` -/
def replicationTwiceOf (block : ReplicationBlock) : Equation where
  name := "ReplicationTwice"
  typeContext := [("P", .base block.proc)]
  premises := []
  left := .apply block.replicate [.apply block.replicate [.fvar "P"]]
  right := .apply block.replicate [.fvar "P"]

/-- `!{P, Q} = {!P, !Q}` -/
def replicationParOf (block : ReplicationBlock) : Equation where
  name := "ReplicationPar"
  typeContext := [("P", .base block.proc), ("Q", .base block.proc)]
  premises := []
  left := .apply block.replicate [.collection .hashBag [.fvar "P", .fvar "Q"] none]
  right := .collection .hashBag [.apply block.replicate [.fvar "P"], .apply block.replicate [.fvar "Q"]] none

/-- `{!P, !P} = !P` -/
def replicationIdempotentOf (block : ReplicationBlock) : Equation where
  name := "ReplicationIdempotent"
  typeContext := [("P", .base block.proc)]
  premises := []
  left := .collection .hashBag [.apply block.replicate [.fvar "P"], .apply block.replicate [.fvar "P"]] none
  right := .apply block.replicate [.fvar "P"]

/-- The laws of replication, in the order a calculus declares them. -/
def replicationLaws (block : ReplicationBlock) : List Equation :=
  [replicationUnfoldOf block, replicationNilOf block, replicationTwiceOf block, replicationParOf block,
    replicationIdempotentOf block]

/-- The laws of a calculus with restriction and replication: those of its blocks, then those of replication. -/
def replicationBlockLaws (block : ReplicationBlock) : List Equation :=
  blockLaws block.toBlock ++ replicationLaws block

/-- **What the laws of replication need of a language**: the restriction-block signature with the laws of replication
among its declared laws, and a replication constructor from processes to processes. A calculus may declare more laws
than these; the equivalences the laws of replication give hold for it. -/
class ReplicationSignature (language : LanguageDef) (block : ReplicationBlock) : Prop
    extends BlockSignature language block.toBlock where
  /-- The laws of replication are declared. -/
  replicationDeclared : ∀ law ∈ replicationLaws block, law ∈ language.equations
  /-- The replication is declared. -/
  replicateAuthored : ∃ rule ∈ language.terms, rule.label = block.replicate
  /-- Replication takes one process to a process. -/
  replicateShape : ∀ rule ∈ language.terms, rule.label = block.replicate → rule.category = block.proc ∧
    ∃ parameter, rule.params = [.simple parameter (.base block.proc)]
  /-- Replication is neither the unit, nor the restriction, nor a named multiset. -/
  replicateFresh : block.replicate ≠ block.unit ∧ block.replicate ≠ block.restrict ∧
    block.replicate ∉ block.multisets

/-- **What the replication theory needs of a language**: the replication signature, with exactly the laws of
restriction, of its empty named multisets and of replication declared. Every result of the block theory that reads
only the signature holds for it. -/
class ReplicationLanguage (language : LanguageDef) (block : ReplicationBlock) : Prop
    extends ReplicationSignature language block where
  /-- Its declared laws are exactly those of restriction, of its empty named multisets and of replication. -/
  equations : language.equations = replicationBlockLaws block
  lawsDeclared := fun _ member => by
    rw [equations]; exact List.mem_append_left _ member
  replicationDeclared := fun _ member => by
    rw [equations]; exact List.mem_append_right _ member

/-- The replication laws bind no name: each is read raw. -/
theorem replicationLaws_raw (block : ReplicationBlock) :
    ∀ law ∈ replicationLaws block, law.bindings = none := by
  intro law member
  simp only [replicationLaws, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A law of a calculus with restriction and replication is a law of its blocks or of replication. -/
theorem mem_replicationBlockLaws {block : ReplicationBlock} {law : Equation} :
    law ∈ replicationBlockLaws block ↔ law ∈ blockLaws block.toBlock ∨ law ∈ replicationLaws block := by
  simp [replicationBlockLaws]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
