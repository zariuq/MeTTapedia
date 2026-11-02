import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationForm
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Soundness

/-!
# The laws of replication as equivalences

For a calculus with replication (`ReplicationSignature`), each law of replication relates processes by a chain of
laws through processes, and replication carries such chains:

- `unfold_equivalent`: `!P ≡ {P, !P}`;
- `replicate_nil_equivalent`: `!0 ≡ 0`;
- `replicate_twice_equivalent`: `!!P ≡ !P`;
- `replicate_par_equivalent`: `!{P, Q} ≡ {!P, !Q}`;
- `replicate_idempotent_equivalent`: `{!P, !P} ≡ !P`;
- `replicate_fill`: equivalent processes have equivalent replications.

A calculus with replication has the restriction-block signature, so every equivalence of the block theory that reads
only the signature (`Soundness`) holds for it as well.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext UsesBareCollection)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (readsRaw_of_none)

variable {language : LanguageDef} {block : ReplicationBlock} [laws : ReplicationSignature language block]

namespace ReplicationSignature

include laws

theorem unfold_mem : List.Mem (replicationUnfoldOf block) language.equations := by
  exact laws.replicationDeclared _ (by simp [replicationLaws])

theorem nil_mem : List.Mem (replicationNilOf block) language.equations := by
  exact laws.replicationDeclared _ (by simp [replicationLaws])

theorem twice_mem : List.Mem (replicationTwiceOf block) language.equations := by
  exact laws.replicationDeclared _ (by simp [replicationLaws])

theorem par_mem : List.Mem (replicationParOf block) language.equations := by
  exact laws.replicationDeclared _ (by simp [replicationLaws])

theorem idempotent_mem : List.Mem (replicationIdempotentOf block) language.equations := by
  exact laws.replicationDeclared _ (by simp [replicationLaws])

end ReplicationSignature

/-- **A replication of a process is a process.** -/
theorem replicate_typed {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType language free bound process (.base block.proc)) :
    HasType language free bound (.apply block.replicate [process]) (.base block.proc) := by
  obtain ⟨rule, member, labelIs⟩ := laws.replicateAuthored
  obtain ⟨category, parameter, params⟩ := laws.replicateShape rule member labelIs
  have built : HasType language free bound (.apply rule.label [process]) (.base rule.category) :=
    .constructor member (by
        simp only [UsesBareCollection, GrammarRule.bareParams, params]
        split <;> simp)
      (by rw [params]; exact .cons trivial rfl typed .nil)
  rwa [labelIs, category] at built

/-- A bag of two processes is a process. -/
theorem pair_typed {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (firstTyped : HasType language free bound first (.base block.proc))
    (secondTyped : HasType language free bound second (.base block.proc)) :
    HasType language free bound (.collection .hashBag [first, second] none) (.base block.proc) :=
  bag_typed (block := block.toBlock) (Members.cons firstTyped (Members.cons secondTyped Members.nil))

/-- **`!P ≡ {P, !P}`.** -/
theorem unfold_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType language free bound process (.base block.proc)) :
    ProcEquiv language block.toBlock free bound (.apply block.replicate [process])
      (.collection .hashBag [process, .apply block.replicate [process]] none) :=
  SortedEquiv.ofInstance ⟨0, .forward (initialBindings := [("P", process)]) (finalBindings := [("P", process)])
    (ReplicationSignature.unfold_mem (block := block)) (readsRaw_of_none rfl)
    (by simp [replicationUnfoldOf, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]) (.nil _)
    (by simp [replicationUnfoldOf, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
    (replicate_typed typed) (pair_typed typed (replicate_typed typed))


/-- **`!0 ≡ 0`.** -/
theorem replicate_nil_equivalent {free : FreeTypeContext} {bound : List TypeExpr} :
    ProcEquiv language block.toBlock free bound (.apply block.replicate [.apply block.unit []])
      (.apply block.unit []) :=
  SortedEquiv.ofInstance ⟨0, .forward (initialBindings := []) (finalBindings := [])
    (ReplicationSignature.nil_mem (block := block)) (readsRaw_of_none rfl)
    (by simp [replicationNilOf, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]) (.nil _)
    (by simp [replicationNilOf, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
    (replicate_typed laws.unit_typed) laws.unit_typed

/-- **`!!P ≡ !P`.** -/
theorem replicate_twice_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType language free bound process (.base block.proc)) :
    ProcEquiv language block.toBlock free bound (.apply block.replicate [.apply block.replicate [process]])
      (.apply block.replicate [process]) :=
  SortedEquiv.ofInstance ⟨0, .forward (initialBindings := [("P", process)]) (finalBindings := [("P", process)])
    (ReplicationSignature.twice_mem (block := block)) (readsRaw_of_none rfl)
    (by simp [replicationTwiceOf, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]) (.nil _)
    (by simp [replicationTwiceOf, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
    (replicate_typed (replicate_typed typed)) (replicate_typed typed)

/-- **Replication carries chains through processes.** -/
theorem replicate_fill {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (equivalent : ProcEquiv language block.toBlock free bound first second) :
    ProcEquiv language block.toBlock free bound (.apply block.replicate [first]) (.apply block.replicate [second]) :=
  SortedEquiv.fill (.apply block.replicate [] .hole []) (fun _ typed => replicate_typed typed) equivalent


/-- **`!{P, Q} ≡ {!P, !Q}`.** -/
theorem replicate_par_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (firstTyped : HasType language free bound first (.base block.proc))
    (secondTyped : HasType language free bound second (.base block.proc)) :
    ProcEquiv language block.toBlock free bound (.apply block.replicate [.collection .hashBag [first, second] none])
      (.collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]] none) :=
  SortedEquiv.ofInstance ⟨0, .forward (initialBindings := [("Q", second), ("P", first)])
    (finalBindings := [("Q", second), ("P", first)])
    (ReplicationSignature.par_mem (block := block)) (readsRaw_of_none rfl)
    (by simp [replicationParOf, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
      Mettapedia.OSLF.MeTTaIL.Match.matchBag]) (.nil _)
    (by simp [replicationParOf, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
    (replicate_typed (pair_typed firstTyped secondTyped))
    (pair_typed (replicate_typed firstTyped) (replicate_typed secondTyped))

/-- **`{!P, !P} ≡ !P`.** -/
theorem replicate_idempotent_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType language free bound process (.base block.proc)) :
    ProcEquiv language block.toBlock free bound
      (.collection .hashBag [.apply block.replicate [process], .apply block.replicate [process]] none)
      (.apply block.replicate [process]) :=
  SortedEquiv.ofInstance ⟨0, .forward (initialBindings := [("P", process)]) (finalBindings := [("P", process)])
    (ReplicationSignature.idempotent_mem (block := block)) (readsRaw_of_none rfl)
    (by simp [replicationIdempotentOf, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
      Mettapedia.OSLF.MeTTaIL.Match.matchBag]) (.nil _)
    (by simp [replicationIdempotentOf, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
    (pair_typed (replicate_typed typed) (replicate_typed typed)) (replicate_typed typed)

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
