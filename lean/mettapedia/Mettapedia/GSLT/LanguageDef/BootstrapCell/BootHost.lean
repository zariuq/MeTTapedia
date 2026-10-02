import Mettapedia.GSLT.LanguageDef.BootstrapCell.Replay
import Mettapedia.Logic.FinitaryRuleSystem.ListBranchedDerivation
import Mettapedia.Logic.HOL.ReplayCore

/-!
# `BootHost`: certificates as the initial algebra, replay as the unique fold

Hosts of NIK's raw certificates are algebras of the polynomial endofunctor
`F X = Unit × RuleInstance × List X`, the category
`ListNodeAlgebra Unit RuleInstance`.  A raw certificate records no
conclusions, which is why the conclusion component is `Unit`.

**Certificates are the initial algebra.**
* `rawProofEquiv : RawProof ≃ ListBranchedDerivation Unit RuleInstance`.
* `rawProofIso`: the equivalence is an isomorphism of algebras between the
  list-branched syntax algebra and the host of raw certificates
  (`rawProofHost`), so `rawProofHost_isInitial` follows from
  `ListNodeAlgebra.syntaxAlgebra_isInitial`.

**Replay is the unique fold.**  Goal-directed replay is the algebra
`replayHost σ` on `σ.Goal → Bool`: a node asks its label for premises and
conclusion, compares the conclusion with the goal, and replays the child
results against the premises, rejecting on a length mismatch.
* `replayFold σ` is the algebra map `certificate ↦ (goal ↦ σ.replay goal
  certificate)`.
* `replayFold_unique`: every algebra map from the certificate host is
  `replayFold σ`, by initiality; `replayFold_unique_direct` proves the same
  by structural induction on certificates.
* `fold_replayHost`: the structural fold of `syntaxAlgebra` into
  `replayHost σ` is replay.
* For a validated calculus, the unique fold is the generic inference
  checker (`checkRawFold_unique`).

**Controls: non-well-founded hosts.**
* `cyclicHost`, over the loop signature in which every rule instance
  concludes the one goal from itself: `true` is a cyclic certificate, the
  node whose only child is itself.  Two different folds exist
  (`rejectingFold ≠ acceptingFold`), so the host is not initial
  (`cyclicHost_not_initial`).  The accepting fold accepts the cycle, although
  the goal has no derivation (`loop_not_derivable`), and the unique fold of
  the initial host rejects every certificate (`loop_replay_rejects`).  The
  cyclic host is the certificate carrier of the junk model of
  `Logic.HOL.ReplayCore`, and the accepting fold is that model's acceptance
  (`junkModel_node_eq`, `junkModel_acc_iff`).
* `pointHost`, the one-point algebra in which every node is the same
  certificate: over a signature with an axiom and a rejected rule instance,
  no fold exists at all (`pointHost_no_fold`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell.BootHost

open CategoryTheory CategoryTheory.Limits
open Mettapedia.Logic.FinitaryRuleSystem
open Mettapedia.Logic.FinitaryRuleSystem.ListBranchedDerivation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Hosts of raw certificates: algebras of `F X = Unit × RuleInstance × List X`. -/
abbrev Host := ListNodeAlgebra.{0, 0, 0} Unit RuleInstance

/-- List-branched certificate trees with no recorded conclusions. -/
abbrev CertificateTree := ListBranchedDerivation Unit RuleInstance

/-! ## Raw certificates are list-branched derivations -/

mutual

/-- A raw certificate as a list-branched tree. -/
def toTree : RawProof → CertificateTree
  | .node label children => .node () label (toTrees children)
termination_by structural certificate => certificate

/-- Pointwise conversion of children. -/
def toTrees : List RawProof → List CertificateTree
  | [] => []
  | child :: children => toTree child :: toTrees children
termination_by structural children => children

end

mutual

/-- A list-branched tree as a raw certificate. -/
def ofTree : CertificateTree → RawProof
  | .node _ label children => .node label (ofTrees children)
termination_by structural tree => tree

/-- Pointwise conversion of children. -/
def ofTrees : List CertificateTree → List RawProof
  | [] => []
  | child :: children => ofTree child :: ofTrees children
termination_by structural children => children

end

theorem toTrees_eq_map : ∀ children : List RawProof, toTrees children = children.map toTree
  | [] => by rw [toTrees, List.map_nil]
  | child :: children => by rw [toTrees, List.map_cons, toTrees_eq_map children]

theorem ofTrees_eq_map : ∀ children : List CertificateTree, ofTrees children = children.map ofTree
  | [] => by rw [ofTrees, List.map_nil]
  | child :: children => by rw [ofTrees, List.map_cons, ofTrees_eq_map children]

mutual

theorem ofTree_toTree : ∀ certificate : RawProof, ofTree (toTree certificate) = certificate
  | .node label children => by rw [toTree, ofTree, ofTrees_toTrees children]

theorem ofTrees_toTrees : ∀ children : List RawProof, ofTrees (toTrees children) = children
  | [] => by rw [toTrees, ofTrees]
  | child :: children => by
      rw [toTrees, ofTrees, ofTree_toTree child, ofTrees_toTrees children]

end

mutual

theorem toTree_ofTree : ∀ tree : CertificateTree, toTree (ofTree tree) = tree
  | .node () label children => by rw [ofTree, toTree, toTrees_ofTrees children]

theorem toTrees_ofTrees : ∀ children : List CertificateTree, toTrees (ofTrees children) = children
  | [] => by rw [ofTrees, toTrees]
  | child :: children => by
      rw [ofTrees, toTrees, toTree_ofTree child, toTrees_ofTrees children]

end

/-- **Raw certificates are list-branched derivations** with unit
conclusions. -/
def rawProofEquiv : RawProof ≃ CertificateTree where
  toFun := toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

/-! ## The certificate host is initial -/

/-- The host whose carrier is the raw certificates themselves. -/
def rawProofHost : Host where
  Carrier := RawProof
  node := fun _ label children => .node label children

theorem toTree_node (label : RuleInstance) (children : List RawProof) :
    toTree (.node label children) = .node () label (children.map toTree) := by
  rw [toTree, toTrees_eq_map]

theorem ofTree_node (conclusion : Unit) (label : RuleInstance)
    (children : List CertificateTree) :
    ofTree (.node conclusion label children) = .node label (children.map ofTree) := by
  rw [ofTree, ofTrees_eq_map]

/-- Conversion to trees preserves node formation. -/
def toTreeHom : rawProofHost ⟶ ListNodeAlgebra.syntaxAlgebra where
  toFun := toTree
  map_node := fun _ label children => toTree_node label children

/-- Conversion from trees preserves node formation. -/
def ofTreeHom : ListNodeAlgebra.syntaxAlgebra ⟶ rawProofHost where
  toFun := ofTree
  map_node := fun conclusion label children => ofTree_node conclusion label children

/-- The list-branched syntax algebra and the certificate host are
isomorphic algebras. -/
def rawProofIso : ListNodeAlgebra.syntaxAlgebra ≅ rawProofHost where
  hom := ofTreeHom
  inv := toTreeHom
  hom_inv_id := ListNodeAlgebra.Hom.ext' _ _ fun tree => toTree_ofTree tree
  inv_hom_id := ListNodeAlgebra.Hom.ext' _ _ fun certificate => ofTree_toTree certificate

/-- **Raw certificates are the initial algebra.** -/
def rawProofHost_isInitial : IsInitial rawProofHost :=
  ListNodeAlgebra.syntaxAlgebra_isInitial.ofIso rawProofIso

/-! ## Replay as an algebra -/

/-- Replay of ordered child results against ordered premises; a length
mismatch rejects. -/
def replayResults {Goal : Type} : List Goal → List (Goal → Bool) → Bool
  | [], [] => true
  | goal :: goals, result :: results => result goal && replayResults goals results
  | _, _ => false

/-- The replay algebra of a signature: a node asks its label for premises and
conclusion, compares the conclusion with the goal, and replays the child
results against the premises. -/
def replayHost (σ : ReplaySignature.{0}) : Host where
  Carrier := σ.Goal → Bool
  node := fun _ label results goal =>
    match σ.step label with
    | none => false
    | some (premises, conclusion) =>
        decide (conclusion = goal) && replayResults premises results

variable (σ : ReplaySignature.{0})

theorem replayAll_eq_replayResults : ∀ (premises : List σ.Goal) (children : List RawProof),
    σ.replayAll premises children =
      replayResults premises (children.map fun child goal => σ.replay goal child)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | goal :: goals, child :: children => by
      rw [ReplaySignature.replayAll_cons_cons, List.map_cons, replayResults,
        replayAll_eq_replayResults goals children]

/-- The node clause of replay, in the form of the replay algebra. -/
theorem replay_node_eq (label : RuleInstance) (children : List RawProof) :
    (fun goal => σ.replay goal (.node label children)) =
      (replayHost σ).node () label (children.map fun child goal => σ.replay goal child) := by
  funext goal
  rw [ReplaySignature.replay_node]
  unfold replayHost
  dsimp only
  cases σ.step label with
  | none => rfl
  | some result =>
      rcases result with ⟨premises, conclusion⟩
      exact congrArg (decide (conclusion = goal) && ·)
        (replayAll_eq_replayResults σ premises children)

/-- **Replay is an algebra map** from the certificate host. -/
def replayFold : rawProofHost ⟶ replayHost σ where
  toFun := fun certificate goal => σ.replay goal certificate
  map_node := fun _ label children => replay_node_eq σ label children

@[simp] theorem replayFold_apply (certificate : RawProof) (goal : σ.Goal) :
    (replayFold σ).toFun certificate goal = σ.replay goal certificate := rfl

/-- **Replay is the unique algebra map** out of the initial certificate
host. -/
theorem replayFold_unique (fold : rawProofHost ⟶ replayHost σ) : fold = replayFold σ :=
  rawProofHost_isInitial.hom_ext fold (replayFold σ)

/-- The same uniqueness by structural induction on certificates, without the
categorical packaging. -/
theorem replayFold_unique_direct (fold : rawProofHost ⟶ replayHost σ)
    (certificate : RawProof) :
    fold.toFun certificate = (replayFold σ).toFun certificate :=
  RawProof.rec
    (motive_1 := fun certificate => fold.toFun certificate = (replayFold σ).toFun certificate)
    (motive_2 := fun children =>
      children.map fold.toFun = children.map (replayFold σ).toFun)
    (fun label children agree =>
      (fold.map_node () label children).trans
        ((congrArg ((replayHost σ).node () label) agree).trans
          ((replayFold σ).map_node () label children).symm))
    rfl
    (fun _child _children headAgrees tailAgrees => congrArg₂ List.cons headAgrees tailAgrees)
    certificate

/-- The algebra maps from the certificate host to the replay algebra form a
singleton. -/
instance : Subsingleton (rawProofHost ⟶ replayHost σ) :=
  ⟨fun first second => (replayFold_unique σ first).trans (replayFold_unique σ second).symm⟩

/-- **Replay is the structural fold** of the list-branched syntax algebra
into the replay algebra. -/
theorem fold_replayHost (certificate : RawProof) :
    ListNodeAlgebra.fold (replayHost σ) (toTree certificate) =
      fun goal => σ.replay goal certificate := by
  have folded := ListNodeAlgebra.hom_eq_fold (replayHost σ) (ofTreeHom ≫ replayFold σ)
  have atTree := congrArg (fun fold => ListNodeAlgebra.Hom.toFun fold (toTree certificate)) folded
  change (fun goal => σ.replay goal (ofTree (toTree certificate))) =
    ListNodeAlgebra.fold (replayHost σ) (toTree certificate) at atTree
  rw [ofTree_toTree] at atTree
  exact atTree.symm

/-- For a validated calculus, the unique fold out of the certificate host is
the generic inference checker. -/
theorem checkRawFold_unique (definition : ValidatedCalculusLanguageDef)
    (fold : rawProofHost ⟶ replayHost (nikSignature definition)) (certificate : RawProof)
    (goal : Pattern) :
    fold.toFun certificate goal = checkRaw definition goal certificate := by
  rw [replayFold_unique (nikSignature definition) fold, replayFold_apply,
    checkRaw_eq_replay]

/-! ## Controls: non-well-founded hosts -/

/-- The loop signature: one goal, and every rule instance concludes it from
itself. -/
def loopSignature : ReplaySignature.{0} where
  Goal := Unit
  decEq := inferInstance
  step := fun _ => some ([()], ())

/-- The loop goal has no derivation: every derivation would need a strictly
smaller derivation of the same goal. -/
theorem loop_not_derivable (goal : Unit) : IsEmpty (loopSignature.Deriv goal) :=
  ⟨fun derivation =>
    ReplaySignature.Deriv.rec
      (motive_1 := fun _ _ => False)
      (motive_2 := fun goals _ => goals = [()] → False)
      (fun _label {premises} {conclusion} step _children childrenAbsurd =>
        childrenAbsurd
          (Prod.mk.inj (Option.some.inj
            (step : some (([()] : List Unit), ()) = some (premises, conclusion)))).1.symm)
      (fun empty => by cases empty)
      (fun _head _tail headAbsurd _tailAbsurd _ => headAbsurd)
      derivation⟩

/-- On the initial host the unique fold of the loop signature rejects every
certificate. -/
theorem loop_replay_rejects (certificate : RawProof) :
    loopSignature.replay () certificate = false := by
  cases accepted : loopSignature.replay () certificate with
  | false => rfl
  | true =>
      obtain ⟨derivation, _⟩ :=
        (ReplaySignature.replay_iff (σ := loopSignature) () certificate).mp accepted
      exact ((loop_not_derivable ()).false derivation).elim

/-- A host with a cyclic certificate: `true` is the node of every label whose
only child is `true` itself, and `false` is every other node. -/
def cyclicHost : Host where
  Carrier := Bool
  node := fun _ _ children => decide (children = [true])

/-- The cycle: the node whose only child is the cycle is the cycle. -/
theorem cyclicHost_cycle (label : RuleInstance) : cyclicHost.node () label [true] = true := rfl

/-- The fold rejecting every certificate of the cyclic host. -/
def rejectingFold : cyclicHost ⟶ replayHost loopSignature where
  toFun := fun _ _ => false
  map_node := by
    intro _ label children
    funext goal
    cases goal
    rcases children with _ | ⟨child, children⟩
    · rfl
    · rfl

/-- The fold accepting exactly the cycle. -/
def acceptingFold : cyclicHost ⟶ replayHost loopSignature where
  toFun := fun certificate _ => certificate
  map_node := by
    intro _ label children
    funext goal
    cases goal
    rcases children with _ | ⟨child, _ | ⟨next, rest⟩⟩
    · rfl
    · cases child <;> rfl
    · cases child <;> rfl

/-- The accepting fold accepts the cycle for the loop goal. -/
theorem acceptingFold_accepts_cycle : acceptingFold.toFun true () = true := rfl

/-- **The fold out of the cyclic host is not unique.** -/
theorem rejectingFold_ne_acceptingFold : rejectingFold ≠ acceptingFold := by
  intro same
  have atCycle := congrArg
    (fun fold : cyclicHost ⟶ replayHost loopSignature => fold.toFun true ()) same
  exact Bool.noConfusion atCycle

/-- The cyclic host is not initial. -/
theorem cyclicHost_not_initial : IsInitial cyclicHost → False := fun initial =>
  rejectingFold_ne_acceptingFold (initial.hom_ext rejectingFold acceptingFold)

/-- The cyclic host is the certificate carrier of the higher-order junk
model: its node operation is the junk model's `node`. -/
theorem junkModel_node_eq (label : Unit) (children : List Bool) (instance_ : RuleInstance) :
    (Mettapedia.Logic.HOL.ReplayCore.JunkModel.constant
        Mettapedia.Logic.HOL.ReplayCore.Symbol.node ⟨label⟩ ⟨children⟩).down =
      cyclicHost.node () instance_ children := rfl

/-- The junk model's acceptance is the accepting fold. -/
theorem junkModel_acc_iff (goal : Unit) (certificate : Bool) :
    (Mettapedia.Logic.HOL.ReplayCore.JunkModel.constant
        Mettapedia.Logic.HOL.ReplayCore.Symbol.acc ⟨goal⟩ ⟨certificate⟩).down ↔
      acceptingFold.toFun certificate goal = true := Iff.rfl

/-- The one-point host: every node is the same certificate. -/
def pointHost : Host where
  Carrier := Unit
  node := fun _ _ _ => ()

/-- One goal; the rule instance without arguments is an axiom for it, and
every rule instance with arguments is rejected. -/
def axiomSignature : ReplaySignature.{0} where
  Goal := Unit
  decEq := inferInstance
  step := fun label => if label.arguments.isEmpty then some ([], ()) else none

/-- An axiom instance and a rejected instance of the same rule. -/
def axiomInstance : RuleInstance := ⟨⟨"axiom"⟩, []⟩
def rejectedInstance : RuleInstance := ⟨⟨"axiom"⟩, [.bvar 0]⟩

/-- **No fold exists out of the one-point host**: it would have to accept and
reject the same certificate. -/
theorem pointHost_no_fold : IsEmpty (pointHost ⟶ replayHost axiomSignature) := by
  constructor
  intro fold
  have accepts := fold.map_node () axiomInstance []
  have rejects := fold.map_node () rejectedInstance []
  have disagree := congrFun (accepts.symm.trans rejects) ()
  change (replayHost axiomSignature).node () axiomInstance [] () =
    (replayHost axiomSignature).node () rejectedInstance [] () at disagree
  exact absurd disagree (by decide)

end Mettapedia.GSLT.LanguageDef.BootstrapCell.BootHost
