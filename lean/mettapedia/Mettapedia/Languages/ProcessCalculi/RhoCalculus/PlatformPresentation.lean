import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.Framework.GeneratedHypercube
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# A platform presentation: N-ary joins, persistence, and guarded firing

The rho presentation the rest of the development runs on has one binary
interaction.  A platform — something a language is actually deployed on — wants
more: a receiver that waits on several channels at once, a receiver that stays
after it fires, and a firing condition consulted from outside the term.

All three are presentation data rather than new machinery.  This module builds
them as an ordinary `LanguageDef`:

* **N-ary joins.**  The join of arity `n` is *generated* from `n`, not written
  out per arity: `joinRule` computes its channel and value variables, its bag of
  participants, and its continuation from the arity alone.  There is no table of
  rules, which is what the anti-goal about hand-written rules asks for.
* **Persistence.**  A persistent join keeps itself on the right-hand side.  The
  two families differ in exactly that, and `persistentJoinRule_retains_receiver`
  together with `joinRule_consumes_receiver` proves the difference is real
  rather than a naming convention.
* **Where-guards.**  Firing is conditioned on a `relationQuery` premise, so the
  condition is answered by the relation environment rather than by the term.
  Because that environment answers with a *list of rows* rather than a yes or
  no, a guard is many-valued: the rows are the admissible instantiations, and
  the number of successors is the number of rows.  That is what makes the guard
  Ω-valued rather than Boolean, and it is checked below on a guard with two rows
  and on one with none.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedHypercube

/-! ## The generated vocabulary -/

/-- The label of the join former of a given arity. -/
def joinLabel (arity : Nat) : String := "Join" ++ toString arity

/-- The label of the persistent join former of a given arity. -/
def persistentJoinLabel (arity : Nat) : String := "PJoin" ++ toString arity

/-- The output former. -/
def outLabel : String := "Out"

/-- The former bundling the values a join received.  It is indexed by the
arity, because a presentation declaring two formers of one name declares an
ambiguous grammar: `rhoPlatform_validate` below is the check that would
otherwise fail. -/
def tupleLabel (arity : Nat) : String := "Tuple" ++ toString arity

/-- The quote: this presentation's name former, under rho's own constructor
name, because this presentation *is* rho. -/
def quoteLabel : String := "NQuote"

/-- The drop: the coercion from a name back to the process it codes. -/
def dropLabel : String := "PDrop"

/-- The variable standing for the parallel remainder a rule leaves alone.
Without it a rule matches only a process that is exactly its participants, so
the presentation would have no contextual reading at all. -/
def restVar : String := "rest"

/-- The relation a where-guard consults. -/
def guardRelation : String := "joinGuard"

/-- The channel variables of a join of the given arity. -/
def channelVars (arity : Nat) : List String :=
  (List.range arity).map fun index => "chan" ++ toString index

/-- The value variables of a join of the given arity. -/
def valueVars (arity : Nat) : List String :=
  (List.range arity).map fun index => "val" ++ toString index

/-- The continuation variable. -/
def continuationVar : String := "cont"

/-- Channels as patterns. -/
def channelPatterns (arity : Nat) : List Pattern :=
  (channelVars arity).map Pattern.fvar

/-- Values as patterns. -/
def valuePatterns (arity : Nat) : List Pattern :=
  (valueVars arity).map Pattern.fvar

/-- The receiver of a join: it names its channels and carries one continuation
under a binder. -/
def receiver (label : String) (arity : Nat) : Pattern :=
  .apply label (channelPatterns arity ++ [.lambda none (.fvar continuationVar)])

/-- The outputs a join of the given arity consumes. -/
def outputs (arity : Nat) : List Pattern :=
  (List.range arity).map fun index =>
    .apply outLabel
      [.fvar ("chan" ++ toString index), .fvar ("val" ++ toString index)]

/-- The values a join received, bundled into one process. -/
def deliveredTuple (arity : Nat) : Pattern :=
  .apply (tupleLabel arity) (valuePatterns arity)

/-- **What the continuation actually receives: the bundle's *name*.**  A join
binds a name, as an input of the reflective calculus does, so what reduction
substitutes is the quote of the bundle.  Delivering the bundle itself would
make the receiver bind a process, and the `Name` sort would be vestigial. -/
def deliveredName (arity : Nat) : Pattern :=
  .apply quoteLabel [deliveredTuple arity]

/-- The continuation, fed the name of the values it waited for. -/
def firedContinuation (arity : Nat) : Pattern :=
  .subst (.fvar continuationVar) (deliveredName arity)

/-! ## The generated rules -/

/-- **The join of arity `n`, generated from `n`.**  A receiver naming `n`
channels, beside one output on each, fires its continuation on the bundle of
values — when the guard relation admits the channels. -/
def joinRule (arity : Nat) : RewriteRule where
  name := "join-" ++ toString arity
  typeContext :=
    (channelVars arity).map (fun name => (name, TypeExpr.name)) ++
      (valueVars arity).map (fun name => (name, TypeExpr.proc)) ++
      [(continuationVar, TypeExpr.proc), (restVar, TypeExpr.proc)]
  premises := [.relationQuery guardRelation (channelPatterns arity)]
  left := .collection .hashBag
    (receiver (joinLabel arity) arity :: outputs arity) (some restVar)
  right := .collection .hashBag [firedContinuation arity] (some restVar)

/-- **The persistent join of arity `n`.**  The same interaction, except that the
receiver is kept: it is available again immediately. -/
def persistentJoinRule (arity : Nat) : RewriteRule where
  name := "pjoin-" ++ toString arity
  typeContext :=
    (channelVars arity).map (fun name => (name, TypeExpr.name)) ++
      (valueVars arity).map (fun name => (name, TypeExpr.proc)) ++
      [(continuationVar, TypeExpr.proc), (restVar, TypeExpr.proc)]
  premises := [.relationQuery guardRelation (channelPatterns arity)]
  left := .collection .hashBag
    (receiver (persistentJoinLabel arity) arity :: outputs arity) (some restVar)
  right := .collection .hashBag
    [firedContinuation arity, receiver (persistentJoinLabel arity) arity]
    (some restVar)

/-! ## What the generated rules say -/

/-- A join of arity `n` has `n` channel variables. -/
theorem channelVars_length (arity : Nat) : (channelVars arity).length = arity := by
  simp [channelVars]

/-- And `n` value variables. -/
theorem valueVars_length (arity : Nat) : (valueVars arity).length = arity := by
  simp [valueVars]

/-- Its left-hand side has the receiver and one output per channel. -/
theorem joinRule_participants (arity : Nat) :
    (joinRule arity).left =
      .collection .hashBag (receiver (joinLabel arity) arity :: outputs arity)
        (some restVar) := rfl

/-- **The arity is read off the rule**: the number of participants a join of
arity `n` consumes is `n + 1`, the receiver together with one output each. -/
theorem joinRule_participant_count (arity : Nat) :
    (outputs arity).length + 1 = arity + 1 := by
  simp [outputs]

/-- The where-guard is a relation query on the channels, so the firing condition
is answered outside the term. -/
theorem joinRule_guard (arity : Nat) :
    (joinRule arity).premises =
      [.relationQuery guardRelation (channelPatterns arity)] := rfl

/-- The persistent join carries the same guard. -/
theorem persistentJoinRule_guard (arity : Nat) :
    (persistentJoinRule arity).premises =
      [.relationQuery guardRelation (channelPatterns arity)] := rfl

/-- **The plain join consumes its receiver**: the receiver does not appear on
the right. -/
theorem joinRule_consumes_receiver (arity : Nat) :
    (joinRule arity).right =
      .collection .hashBag [firedContinuation arity] (some restVar) := rfl

/-- **The persistent join retains it**: the receiver is on the right, so it is
available again. -/
theorem persistentJoinRule_retains_receiver (arity : Nat) :
    receiver (persistentJoinLabel arity) arity ∈
      (match (persistentJoinRule arity).right with
       | .collection _ elements _ => elements
       | _ => []) := by
  simp [persistentJoinRule]

/-- The two families are genuinely different rules, not one rule named twice. -/
theorem joinRule_ne_persistentJoinRule (arity : Nat) :
    joinRule arity ≠ persistentJoinRule arity := by
  intro equal
  have names : (joinRule arity).name = (persistentJoinRule arity).name :=
    congrArg RewriteRule.name equal
  simp [joinRule, persistentJoinRule] at names

/-! ## The presentation -/

/-- The declaration of the join former of a given arity: it names its channels
and takes one continuation under a binder. -/
def joinDeclaration (label : String) (arity : Nat) : GrammarRule where
  label := label
  category := "Proc"
  params :=
    (channelVars arity).map (fun name => TermParam.simple name TypeExpr.name) ++
      [TermParam.abstraction continuationVar
        (TypeExpr.funType TypeExpr.name TypeExpr.proc)]
  syntaxPattern := [.terminal label]

/-- The output former's declaration. -/
def outDeclaration : GrammarRule where
  label := outLabel
  category := "Proc"
  params := [.simple "chan" TypeExpr.name, .simple "val" TypeExpr.proc]
  syntaxPattern := [.terminal outLabel]

/-- The value-bundle former's declaration, at a given arity. -/
def tupleDeclaration (arity : Nat) : GrammarRule where
  label := tupleLabel arity
  category := "Proc"
  params := (valueVars arity).map (fun name => TermParam.simple name TypeExpr.proc)
  syntaxPattern := [.terminal (tupleLabel arity)]

/-- The terminated process: a nullary process former.  Without one the
presentation has no closed process at all, so nothing it declares can be
exhibited as well sorted. -/
def stopDeclaration : GrammarRule where
  label := "Stop"
  category := "Proc"
  params := []
  syntaxPattern := [.terminal "Stop"]

/-- The quote: a name is a quoted process, as in rho. -/
def quoteDeclaration : GrammarRule where
  label := quoteLabel
  category := "Name"
  params := [.simple "quoted" (.base "Proc")]
  syntaxPattern := [.terminal quoteLabel]

/-- The drop's declaration: a name, read as the process it codes.  Without it
the name sort is inhabited but never eliminated, and the presentation has a
quote with nothing to undo it. -/
def dropDeclaration : GrammarRule where
  label := dropLabel
  category := "Proc"
  params := [.simple "name" (.base "Name")]
  syntaxPattern := [.terminal dropLabel]

/-- **Reflection.**  The quote of a drop is the name it dropped: the equation
that makes names codes of processes rather than a separate sort beside them. -/
def quoteDropEquation : Equation where
  name := "QuoteDrop"
  typeContext := [("N", TypeExpr.name)]
  premises := []
  left := .apply quoteLabel [.apply dropLabel [.fvar "N"]]
  right := .fvar "N"

/-- The parallel carrier: a bag of processes, declared as the presentation's
collection carrier so that the bag laws are *derived* from the declaration
rather than authored as equations. -/
def parDeclaration : GrammarRule where
  label := "Par"
  category := "Proc"
  params := [.simple "parts" (.collection .hashBag (.base "Proc"))]
  syntaxPattern := [.terminal "Par"]
  -- Parallel composition is associative with unit `Stop`; commutativity and
  -- multiplicity come from the bag tag.  Declaring the algebra is what makes
  -- flattening, the singleton law and the unit law *derived* rather than
  -- separately authored.
  algebra? := some { flatten := true, unit := some stopDeclaration.label }

/-- **The platform presentation**, generated from the arities it supports.  Both
join families at every supported arity, each with its guard, together with the
formers they mention. -/
def rhoPlatform (arities : List Nat) : LanguageDef where
  name := "RhoPlatform"
  types := [TypeDecl.plain "Proc", TypeDecl.plain "Name"]
  terms :=
    stopDeclaration :: quoteDeclaration :: dropDeclaration :: parDeclaration ::
      outDeclaration ::
      arities.flatMap fun arity =>
        [joinDeclaration (joinLabel arity) arity,
          joinDeclaration (persistentJoinLabel arity) arity,
          tupleDeclaration arity]
  equations := [quoteDropEquation]
  rewrites :=
    arities.flatMap fun arity => [joinRule arity, persistentJoinRule arity]

/-- Every supported arity contributes its two rules, and nothing else does. -/
theorem rhoPlatform_rewrites (arities : List Nat) :
    (rhoPlatform arities).rewrites =
      arities.flatMap fun arity =>
        [joinRule arity, persistentJoinRule arity] := rfl

/-- **Distinct arities declare distinct constructors.**  This is what indexing
the bundle former by its arity buys: an unindexed bundle would declare one
constructor per supported arity under a single name, and a presentation with two
constructors of one name declares an ambiguous grammar that its own
well-formedness check rejects. -/
theorem rhoPlatform_labels_nodup_pair :
    ((rhoPlatform [2]).terms.map GrammarRule.label).Nodup := by decide

theorem rhoPlatform_labels_nodup_three :
    ((rhoPlatform [1, 2, 3]).terms.map GrammarRule.label).Nodup := by decide

/-- The bundle formers of two arities are two constructors, not one. -/
theorem tupleDeclaration_label_distinct :
    (tupleDeclaration 1).label ≠ (tupleDeclaration 2).label := by decide

/-- The rule of a supported arity is in the presentation. -/
theorem joinRule_mem {arities : List Nat} {arity : Nat}
    (supported : arity ∈ arities) :
    joinRule arity ∈ (rhoPlatform arities).rewrites := by
  simp only [rhoPlatform, List.mem_flatMap]
  exact ⟨arity, supported, by simp⟩

/-- And so is the persistent one. -/
theorem persistentJoinRule_mem {arities : List Nat} {arity : Nat}
    (supported : arity ∈ arities) :
    persistentJoinRule arity ∈ (rhoPlatform arities).rewrites := by
  simp only [rhoPlatform, List.mem_flatMap]
  exact ⟨arity, supported, by simp⟩

/-! ## Item 1 run on this presentation

The redex-position generator is applied to the generated join rules with nothing
hand-written.  The redex position is the continuation's binder inside the
receiver, and what comes out is the arity: a join of arity `n` relies on `n`
channels and `n` values, so it carries `2n + 1` slots. -/

/-- The redex position of a join: the continuation, inside the receiver. -/
def joinPos (arity : Nat) : Position := [0, arity]

/-- At that position the focus is the continuation's binder, at each of the
three arities the specimen below uses. -/
theorem joinRule_focus_one :
    subtermAt (joinRule 1).left (joinPos 1) =
      some (.lambda none (.fvar continuationVar)) := by rfl

theorem joinRule_focus_two :
    subtermAt (joinRule 2).left (joinPos 2) =
      some (.lambda none (.fvar continuationVar)) := by rfl

theorem joinRule_focus_three :
    subtermAt (joinRule 3).left (joinPos 3) =
      some (.lambda none (.fvar continuationVar)) := by rfl

/-- The channel-and-value parameters a join of arity `n` relies on. -/
def participantVars (arity : Nat) : List String :=
  (List.range arity).flatMap fun index =>
    ["chan" ++ toString index, "val" ++ toString index]

/-- **Arity one**: the remainder, one channel, one value; four slots. -/
theorem joinRule_one_relyVars :
    relyVars (joinRule 1).left (joinPos 1) = restVar :: participantVars 1 := by rfl

theorem joinRule_one_slotCount :
    slotCount (joinRule 1).left (joinPos 1) = 4 := by rfl

/-- **Arity two**: two channels, two values; six slots. -/
theorem joinRule_two_relyVars :
    relyVars (joinRule 2).left (joinPos 2) = restVar :: participantVars 2 := by rfl

theorem joinRule_two_slotCount :
    slotCount (joinRule 2).left (joinPos 2) = 6 := by rfl

/-- **Arity three**: three channels, three values; eight slots. -/
theorem joinRule_three_relyVars :
    relyVars (joinRule 3).left (joinPos 3) = restVar :: participantVars 3 := by rfl

theorem joinRule_three_slotCount :
    slotCount (joinRule 3).left (joinPos 3) = 8 := by rfl

/-- **The remainder is a rely parameter, and it is the one the contextual
reading adds.**  A rule that matched only its own participants would have `2n`
of them; matching in a parallel context makes the remainder something the firing
relies on, and the slot family counts it. -/
theorem joinRule_relyVars_head :
    (relyVars (joinRule 1).left (joinPos 1)).head? = some restVar ∧
      (relyVars (joinRule 2).left (joinPos 2)).head? = some restVar ∧
        (relyVars (joinRule 3).left (joinPos 3)).head? = some restVar :=
  ⟨rfl, rfl, rfl⟩

/-- The participant parameters are two per arity, so the slot counts above are
`2n + 2` rather than a table. -/
theorem participantVars_length (arity : Nat) :
    (participantVars arity).length = 2 * arity := by
  induction arity with
  | zero => rfl
  | succ n ih =>
      simp [participantVars, List.range_succ, List.flatMap_append] at ih ⊢
      omega

/-- **And no slot is minted for an undeclared variable**, at any of the three:
the generated rules declare every metavariable they use, which is the defect the
tree's own communication rule has. -/
theorem joinRule_relyVars_declared :
    RelyVarsDeclared (joinRule 1) (joinPos 1) = true ∧
      RelyVarsDeclared (joinRule 2) (joinPos 2) = true ∧
        RelyVarsDeclared (joinRule 3) (joinPos 3) = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## The guard is Ω-valued, not Boolean

The relation environment answers a where-guard with a list of rows, and the rows
are the admissible instantiations.  So a guard does not merely permit or forbid:
it says *how many ways*, and the successors count them.  The three environments
below differ only in that count. -/

namespace Guard

/-- Two channels and two values. -/
def channelA : Pattern := .apply "A" []
def channelB : Pattern := .apply "B" []
def valueP : Pattern := .apply "P" []
def valueQ : Pattern := .apply "Q" []

/-- The supported presentation. -/
def platform : LanguageDef := rhoPlatform [2]

/-- A receiver on both channels, with one output on each. -/
def board : Pattern := .collection .hashBag
  [ .apply (joinLabel 2) [channelA, channelB, .lambda none (.bvar 0)]
  , .apply outLabel [channelA, valueP]
  , .apply outLabel [channelB, valueQ] ] none

/-- The same board, beside an idle process the rule must leave alone. -/
def boardInContext : Pattern := .collection .hashBag
  [ .apply (joinLabel 2) [channelA, channelB, .lambda none (.bvar 0)]
  , .apply outLabel [channelA, valueP]
  , .apply outLabel [channelB, valueQ]
  , .apply stopDeclaration.label [] ] none

/-- A plain receiver with two rounds of outputs. -/
def plainBoard : Pattern := .collection .hashBag
  [ .apply (joinLabel 2) [channelA, channelB, .lambda none (.bvar 0)]
  , .apply outLabel [channelA, valueP]
  , .apply outLabel [channelB, valueQ]
  , .apply outLabel [channelA, valueP]
  , .apply outLabel [channelB, valueQ] ] none

/-- A persistent receiver with two rounds of outputs. -/
def persistentBoard : Pattern := .collection .hashBag
  [ .apply (persistentJoinLabel 2) [channelA, channelB, .lambda none (.bvar 0)]
  , .apply outLabel [channelA, valueP]
  , .apply outLabel [channelB, valueQ]
  , .apply outLabel [channelA, valueP]
  , .apply outLabel [channelB, valueQ] ] none

/-- A guard that admits the pair once. -/
def admitsOnce : RelationEnv where
  tuples := fun relation _ =>
    if relation = guardRelation then [[channelA, channelB]] else []

/-- A guard that admits nothing. -/
def admitsNone : RelationEnv where
  tuples := fun _ _ => []

/-- A guard that admits the pair twice. -/
def admitsTwice : RelationEnv where
  tuples := fun relation _ =>
    if relation = guardRelation then [[channelA, channelB], [channelA, channelB]]
    else []


/-- **One row, one successor** — and the successor is the continuation fed the
bundle of values it waited for. -/
theorem admitsOnce_fires :
    rewriteAt (engineBasePremises admitsOnce) platform 6 board =
      [.collection .hashBag
        [.apply quoteLabel [.apply (tupleLabel 2) [valueP, valueQ]]] none] := by
  decide +kernel

/-- **And it fires in a context.**  The same interaction beside an idle process
fires and leaves that process alone — which is what a rule with a parallel
remainder means, and what a rule without one cannot do. -/
theorem admitsOnce_fires_in_context :
    rewriteAt (engineBasePremises admitsOnce) platform 6 boardInContext =
      [.collection .hashBag
        [.apply quoteLabel [.apply (tupleLabel 2) [valueP, valueQ]],
          .apply stopDeclaration.label []] none] := by
  decide +kernel

/-- **No rows, no successor.**  The guard blocks a join whose participants are
all present, which is what makes it a condition rather than a decoration. -/
theorem admitsNone_blocks :
    rewriteAt (engineBasePremises admitsNone) platform 6 board = [] := by
  decide +kernel

/-- **Two rows, two successors.**  The guard's value is its number of rows, so it
is many-valued rather than Boolean. -/
theorem admitsTwice_fires_twice :
    (rewriteAt (engineBasePremises admitsTwice) platform 6 board).length = 2 := by
  decide +kernel

/-! ### Persistence, operationally

The right-hand side of the persistent rule keeps its receiver.  That is a fact
about syntax; what makes it persistence is that the kept receiver fires again,
and the plain one does not. -/

/-- **The persistent family fires twice.**  Every successor of the first firing
still carries the receiver and still has an output pair, so every one of them
fires again. -/
theorem persistent_fires_twice :
    ((rewriteAt (engineBasePremises admitsOnce) platform 6 persistentBoard).map
      fun successor =>
        (rewriteAt (engineBasePremises admitsOnce) platform 6 successor).length)
      = [1, 1, 1, 1] := by
  decide +kernel

/-- **The plain family does not.**  The same board with a plain receiver has no
second firing anywhere: the receiver was consumed, and the second round of
outputs has nothing to synchronise with. -/
theorem plain_does_not_fire_twice :
    ((rewriteAt (engineBasePremises admitsOnce) platform 6 plainBoard).map
      fun successor =>
        (rewriteAt (engineBasePremises admitsOnce) platform 6 successor).length)
      = [0, 0, 0, 0] := by
  decide +kernel

end Guard

/-! ## The specimen: a chess ply, and its taxonomy

A ply is classified by how many pieces of state must agree for it to happen, and
that number is the arity of the join that performs it.  The taxonomy is not
imposed on the rules: it is read off them. -/

namespace Chess

/-- The kinds of ply. -/
inductive Ply where
  /-- One piece moves to an empty square. -/
  | quiet
  /-- A piece moves onto an occupied square; the occupant is removed. -/
  | capture
  /-- King and rook move together. -/
  | castle
  /-- A pawn captures a pawn that is not on the destination square, consuming
  the right that made it legal. -/
  | enPassant
  deriving DecidableEq, Repr

/-- **The taxonomy.**  How many pieces of state must agree for the ply to
happen. -/
def Ply.arity : Ply → Nat
  | .quiet => 1
  | .capture => 2
  | .castle => 2
  | .enPassant => 3

/-- The join that performs a ply is the join of its arity. -/
def Ply.rule (ply : Ply) : RewriteRule := joinRule ply.arity

/-- The presentation supporting every ply. -/
def platform : LanguageDef := rhoPlatform [1, 2, 3]

/-- Every ply's join is in the presentation. -/
theorem Ply.rule_mem (ply : Ply) : ply.rule ∈ platform.rewrites := by
  cases ply <;> exact joinRule_mem (by decide)

/-- **Move taxonomy is join arity.**  Two plies are performed by the same join
exactly when they have the same arity, so the arity is the classification and
not a label attached to one. -/
theorem Ply.rule_eq_iff_arity_eq (first second : Ply) :
    first.rule = second.rule ↔ first.arity = second.arity := by
  constructor
  · intro equal
    have names : first.rule.name = second.rule.name := congrArg RewriteRule.name equal
    simp only [Ply.rule, joinRule] at names
    cases first <;> cases second <;> simp only [Ply.arity] <;>
      first
        | rfl
        | exact absurd names (by decide)
  · intro equal
    simp only [Ply.rule, equal]

/-- The arities the taxonomy realises are exactly the three the presentation
supports. -/
theorem Ply.arities_realised :
    ([Ply.quiet, .capture, .castle, .enPassant].map Ply.arity).eraseDups = [1, 2, 3] := by
  decide

/-- Castling and a capture are different plies with the same arity, so the
taxonomy classifies by arity and does not separate within a class. -/
theorem castle_and_capture_share_arity :
    Ply.castle ≠ Ply.capture ∧ Ply.castle.arity = Ply.capture.arity :=
  ⟨by decide, rfl⟩

/-- En passant is the only ply of arity three. -/
theorem enPassant_unique_arity_three (ply : Ply) :
    ply.arity = 3 ↔ ply = .enPassant := by
  cases ply <;> simp [Ply.arity]

end Chess

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
