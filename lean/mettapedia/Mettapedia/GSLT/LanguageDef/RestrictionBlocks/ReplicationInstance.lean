import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCompleteness
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping

/-!
# A calculus with replication

`repCalc` is a minimal calculus with restriction and replication: inaction, parallel composition as a bare bag,
outputs `x⟨z⟩` on names, restriction binding a name over a process, and replication `!P` of any process, with the laws
of restriction and of replication as its declared laws (`repLanguage`). So its static theory is decided by the
canonical form with replication on object processes, and kernel controls read equivalences off canonical forms:
a copy beside a replication, `!!P`, `!0`, a replicated pair, and, apart, `!(νx)P` from `(νx)!P`, `!P` from `P`, a
private name from a shared one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext parameterType? UsesBareCollection
  isObjectPattern)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (BagPresentation)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- The blocks of the calculus: inaction, restriction, processes, names, and replication. -/
abbrev repBlock : ReplicationBlock := ⟨⟨"RNil", "RNu", "Proc", "Name", [], []⟩, "RRep", false⟩

/-- **A minimal calculus with restriction and replication.** -/
def repCalc : LanguageDef := {
  name := "RepCalc",
  types := ["Proc", "Name"],
  terms := [
    { label := "RNil", category := "Proc", params := [], syntaxPattern := [.terminal "0"] },
    { label := "RPar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
      algebra? := some { flatten := true, unit := some "RNil" } },
    { label := "ROut", category := "Proc",
      params := [.simple "x" (TypeExpr.base "Name"), .simple "z" (TypeExpr.base "Name")],
      syntaxPattern := [.nonTerminal "x", .terminal "<", .nonTerminal "z", .terminal ">"] },
    { label := "RNu", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "ν", .nonTerminal "body"] },
    { label := "RRep", category := "Proc",
      params := [.simple "p" (TypeExpr.base "Proc")],
      syntaxPattern := [.terminal "!", .nonTerminal "p"] }
  ],
  equations := replicationBlockLaws repBlock,
  rewrites := [] }

/-- The parallel constructor declares the bag monoid with inaction as its unit. -/
theorem repBagPresentation : BagPresentation repCalc repCalc.terms[1] (some "RNil") where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  otherParameters := by
    intro rule member different parameter present
    simp only [repCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact False.elim (different rfl)
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> rfl
  unitAuthored := by
    intro unit same
    cases Option.some.inj same
    exact ⟨repCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩

/-- **The calculus is a calculus with restriction and replication.** -/
instance repLanguage : ReplicationLanguage repCalc repBlock where
  bag := ⟨repCalc.terms[1], ParallelBag.ofBare (repBagPresentation.asBare rfl), rfl⟩
  equations := rfl
  restrictAuthored := ⟨repCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [repCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp_all
  unitShape := by
    intro rule member labelIs
    simp only [repCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp_all
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
    simp only [repCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare _ parameter present domain sort found
    simp only [repCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp_all [parameterType?]
  replicateAuthored := ⟨repCalc.terms[4], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [repCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp_all
  replicateFresh := by decide

/-! ## Controls -/

/-- Free names are names. -/
def names : FreeTypeContext := fun _ => some (.base "Name")

theorem names_base : BaseContext names [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [names] using found.symm⟩, fun _ member => by simp at member⟩

private def a : Pattern := .fvar "a"
private def b : Pattern := .fvar "b"
private def out (channel datum : Pattern) : Pattern := .apply "ROut" [channel, datum]
private def bang (process : Pattern) : Pattern := .apply "RRep" [process]
private def par (processes : List Pattern) : Pattern := .collection .hashBag processes none
private def nu (body : Pattern) : Pattern := .apply "RNu" [.lambda none body]
private def nil : Pattern := .apply "RNil" []

theorem name_typed {bound : List TypeExpr} (name : String) :
    HasType repCalc names bound (.fvar name) (.base "Name") :=
  .fvar rfl

theorem out_typed {bound : List TypeExpr} {channel datum : Pattern}
    (channelTyped : HasType repCalc names bound channel (.base "Name"))
    (datumTyped : HasType repCalc names bound datum (.base "Name")) :
    HasType repCalc names bound (out channel datum) (.base "Proc") :=
  .constructor (rule := repCalc.terms[2]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, repCalc])
    (.cons trivial rfl channelTyped (.cons trivial rfl datumTyped .nil))

theorem bound_typed {bound : List TypeExpr} : HasType repCalc names (.base "Name" :: bound) (.bvar 0) (.base "Name") :=
  .bvar rfl

/-- The equivalence of two object processes, read off their canonical forms. -/
theorem equivalent_iff {first second : Pattern} (firstTyped : HasType repCalc names [] first (.base "Proc"))
    (secondTyped : HasType repCalc names [] second (.base "Proc")) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) :
    EquationEquiv (engineBasePremises RelationEnv.empty) repCalc first second ↔
      canonR repBlock first = canonR repBlock second :=
  equationEquiv_iff_canonR_eq (block := repBlock) names_base firstTyped secondTyped firstObject secondObject

theorem out_ab_typed : HasType repCalc names [] (out a b) (.base "Proc") := out_typed (name_typed "a") (name_typed "b")

theorem bang_typed {bound : List TypeExpr} {process : Pattern}
    (typed : HasType repCalc names bound process (.base "Proc")) :
    HasType repCalc names bound (bang process) (.base "Proc") :=
  replicate_typed (block := repBlock) typed

theorem par_typed {bound : List TypeExpr} {processes : List Pattern}
    (typed : ∀ process ∈ processes, HasType repCalc names bound process (.base "Proc")) :
    HasType repCalc names bound (par processes) (.base "Proc") :=
  repLanguage.toBlockSignature.bag_typed (Mettapedia.GSLT.LanguageDef.BagNormalForm.elementsHaveType_iff.mpr typed)

theorem nu_typed {body : Pattern} (typed : HasType repCalc names [.base "Name"] body (.base "Proc")) :
    HasType repCalc names [] (nu body) (.base "Proc") :=
  repLanguage.toBlockSignature.restrict_typed typed

/-- `!a⟨b⟩ | a⟨b⟩` is `!a⟨b⟩`: a copy beside a replication is absorbed. -/
theorem copy_absorbed : EquationEquiv (engineBasePremises RelationEnv.empty) repCalc
    (par [bang (out a b), out a b]) (bang (out a b)) :=
  (equivalent_iff (par_typed (by simp; exact ⟨bang_typed out_ab_typed, out_ab_typed⟩)) (bang_typed out_ab_typed)
    (by decide) (by decide)).mpr (by decide +kernel)

/-- `!!a⟨b⟩` is `!a⟨b⟩`. -/
theorem twice_absorbed : EquationEquiv (engineBasePremises RelationEnv.empty) repCalc
    (bang (bang (out a b))) (bang (out a b)) :=
  (equivalent_iff (bang_typed (bang_typed out_ab_typed)) (bang_typed out_ab_typed) (by decide) (by decide)).mpr
    (by decide +kernel)

/-- A replicated pair is a pair of replications, in either order. -/
theorem pair_split : EquationEquiv (engineBasePremises RelationEnv.empty) repCalc
    (bang (par [out a b, out b a])) (par [bang (out b a), bang (out a b)]) :=
  (equivalent_iff (bang_typed (par_typed (by simp; exact ⟨out_ab_typed, out_typed (name_typed "b") (name_typed "a")⟩)))
    (par_typed (by simp; exact ⟨bang_typed (out_typed (name_typed "b") (name_typed "a")), bang_typed out_ab_typed⟩))
    (by decide) (by decide)).mpr (by decide +kernel)

/-- **Apart**: `!(νx)x⟨a⟩` gives every copy its own name, `(νx)!x⟨a⟩` shares one. -/
theorem private_names_apart : ¬ EquationEquiv (engineBasePremises RelationEnv.empty) repCalc
    (bang (nu (out (.bvar 0) a))) (nu (bang (out (.bvar 0) a))) := fun equivalent =>
  absurd ((equivalent_iff (bang_typed (nu_typed (out_typed bound_typed (name_typed "a"))))
    (nu_typed (bang_typed (out_typed bound_typed (name_typed "a")))) (by decide) (by decide)).mp equivalent)
    (by decide +kernel)

/-- **Apart**: a replication is not one copy. -/
theorem replication_not_copy : ¬ EquationEquiv (engineBasePremises RelationEnv.empty) repCalc
    (bang (out a b)) (out a b) := fun equivalent =>
  absurd ((equivalent_iff (bang_typed out_ab_typed) out_ab_typed (by decide) (by decide)).mp equivalent)
    (by decide +kernel)

/-- **Apart**: two copies under one private name are not the replication under it. -/
theorem shared_copies_not_replication : ¬ EquationEquiv (engineBasePremises RelationEnv.empty) repCalc
    (nu (par [out (.bvar 0) a, out (.bvar 0) a])) (nu (bang (out (.bvar 0) a))) := fun equivalent =>
  absurd ((equivalent_iff (nu_typed (par_typed (by
      intro process member
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      subst member
      exact out_typed bound_typed (name_typed "a"))))
    (nu_typed (bang_typed (out_typed bound_typed (name_typed "a")))) (by decide) (by decide)).mp equivalent)
    (by decide +kernel)

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationInstance
