import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Pair reconstruction from membership proofs

The reconstruction algorithm uses membership, binary pairing, and retained
equality transport. It does not inspect a set representation. Concrete set
constructions and abstract operation parameters can supply the same interface.
All inputs and outputs remain actual retained proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.PairingReconstruction
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {object : Ty Base}

def orderedBy (pair : Term Const Γ object → Term Const Γ object → Term Const Γ object)
    (left right : Term Const Γ object) : Term Const Γ object :=
  pair (pair left left) (pair left right)

structure Operations (Const : Ty Base → Type v) (Γ : Ctx Base) (object : Ty Base) where
  member : Term Const Γ object → Term Const Γ object → Formula Const Γ
  pair : Term Const Γ object → Term Const Γ object → Term Const Γ object
  transportBound : ∀ {assumptions : List (Formula Const Γ)} {first second : Term Const Γ object}
    (point : Term Const Γ object), ProofSyntax Const assumptions (.eq first second) →
    ProofSyntax Const assumptions (member point first) → ProofSyntax Const assumptions (member point second)
  orderedCongrFirst : ∀ {assumptions : List (Formula Const Γ)} {first second : Term Const Γ object}
    (right : Term Const Γ object), ProofSyntax Const assumptions (.eq first second) →
    ProofSyntax Const assumptions (.eq (orderedBy pair first right) (orderedBy pair second right))

variable (ops : Operations Const Γ object) {Δ : List (Formula Const Γ)}

structure Rules (assumptions : List (Formula Const Γ)) where
  left : ∀ left right, ProofSyntax Const assumptions (ops.member left (ops.pair left right))
  right : ∀ left right, ProofSyntax Const assumptions (ops.member right (ops.pair left right))
  elimination : ∀ left right point, ProofSyntax Const assumptions
    (.imp (ops.member point (ops.pair left right)) (.or (.eq point left) (.eq point right)))

def Rules.prepend {ops : Operations Const Γ object}
    (rules : Rules ops Δ) (formula : Formula Const Γ) : Rules ops (formula :: Δ) where
  left left right := (rules.left left right).prepend formula
  right left right := (rules.right left right).prepend formula
  elimination left right point := (rules.elimination left right point).prepend formula

def Rules.elim (left right point : Term Const Γ object) (rules : Rules ops Δ)
    (admitted : ProofSyntax Const Δ (ops.member point (ops.pair left right))) :
    ProofSyntax Const Δ (.or (.eq point left) (.eq point right)) :=
  .impE (rules.elimination left right point) admitted

def anchoredInjective (anchor left right : Term Const Γ object) (rules : Rules ops Δ)
    (equal : ProofSyntax Const Δ (.eq (ops.pair anchor left) (ops.pair anchor right))) :
    ProofSyntax Const Δ (.eq left right) := by
  have leftCases := Rules.elim ops anchor right left rules
    (ops.transportBound left equal (rules.right anchor left))
  have rightCases := Rules.elim ops anchor left right rules
    (ops.transportBound right (.eqSymm equal) (rules.right anchor right))
  refine .orE leftCases ?_ ?_
  · have same : ProofSyntax Const (.eq left anchor :: Δ) (.eq left anchor) := .hyp 0
    refine .orE (rightCases.prepend _) ?_ ?_
    · exact .eqTrans (same.prepend _) (.eqSymm (.hyp 0))
    · exact .eqSymm (.hyp 0)
  · exact .hyp 0

def firstCoordinate (left right first second : Term Const Γ object) (rules : Rules ops Δ)
    (equal : ProofSyntax Const Δ (.eq (orderedBy ops.pair left right) (orderedBy ops.pair first second))) :
    ProofSyntax Const Δ (.eq left first) := by
  let singletonLeft := ops.pair left left
  let singletonFirst := ops.pair first first
  let pairFirst := ops.pair first second
  have possibilities := Rules.elim ops singletonFirst pairFirst singletonLeft rules
    (ops.transportBound singletonLeft equal (rules.left singletonLeft (ops.pair left right)))
  refine .orE possibilities ?_ ?_
  · let raised := rules.prepend (.eq singletonLeft singletonFirst)
    have inFirst : ProofSyntax Const (.eq singletonLeft singletonFirst :: Δ)
        (ops.member left singletonFirst) :=
      ops.transportBound left (.hyp 0) ((rules.left left left).prepend _)
    have cases := Rules.elim ops first first left raised inFirst
    exact .orE cases (.hyp 0) (.hyp 0)
  · let raised := rules.prepend (.eq singletonLeft pairFirst)
    have inLeft : ProofSyntax Const (.eq singletonLeft pairFirst :: Δ)
        (ops.member first singletonLeft) :=
      ops.transportBound first (.eqSymm (.hyp 0)) ((rules.left first second).prepend _)
    have cases := Rules.elim ops left left first raised inLeft
    exact .orE cases (.eqSymm (.hyp 0)) (.eqSymm (.hyp 0))

def orderedInjective (left right first second : Term Const Γ object) (rules : Rules ops Δ)
    (equal : ProofSyntax Const Δ (.eq (orderedBy ops.pair left right) (orderedBy ops.pair first second))) :
    ProofSyntax Const Δ (.and (.eq left first) (.eq right second)) := by
  have firstEqual := firstCoordinate ops left right first second rules equal
  have fixedFirst := ProofSyntax.eqTrans equal (ops.orderedCongrFirst second (.eqSymm firstEqual))
  have innerEqual := anchoredInjective ops (ops.pair left left)
    (ops.pair left right) (ops.pair left second) rules fixedFirst
  exact .andI firstEqual (anchoredInjective ops left right second rules innerEqual)

structure Operations.Free : Prop where
  transportBound : ∀ {assumptions : List (Formula Const Γ)} {first second : Term Const Γ object}
    (point : Term Const Γ object) (equal : ProofSyntax Const assumptions (.eq first second))
    (admitted : ProofSyntax Const assumptions (ops.member point first)),
    equal.FunctionExtensionalityFree → admitted.FunctionExtensionalityFree →
      (ops.transportBound point equal admitted).FunctionExtensionalityFree
  orderedCongrFirst : ∀ {assumptions : List (Formula Const Γ)} {first second : Term Const Γ object}
    (right : Term Const Γ object) (equal : ProofSyntax Const assumptions (.eq first second)),
    equal.FunctionExtensionalityFree → (ops.orderedCongrFirst right equal).FunctionExtensionalityFree

structure Rules.Free (rules : Rules ops Δ) : Prop where
  left : ∀ left right, (rules.left left right).FunctionExtensionalityFree
  right : ∀ left right, (rules.right left right).FunctionExtensionalityFree
  elimination : ∀ left right point, (rules.elimination left right point).FunctionExtensionalityFree

theorem anchoredInjective_free (anchor left right : Term Const Γ object) (rules : Rules ops Δ)
    (equal : ProofSyntax Const Δ (.eq (ops.pair anchor left) (ops.pair anchor right)))
    (opsFree : ops.Free) (rulesFree : rules.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (anchoredInjective ops anchor left right rules equal).FunctionExtensionalityFree := by
  simp [anchoredInjective, Rules.elim, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
    rulesFree.elimination, rulesFree.right, opsFree.transportBound, proofFree]

theorem firstCoordinate_free (left right first second : Term Const Γ object) (rules : Rules ops Δ)
    (equal : ProofSyntax Const Δ (.eq (orderedBy ops.pair left right) (orderedBy ops.pair first second)))
    (opsFree : ops.Free) (rulesFree : rules.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (firstCoordinate ops left right first second rules equal).FunctionExtensionalityFree := by
  simp [firstCoordinate, Rules.elim, Rules.prepend, ProofSyntax.FunctionExtensionalityFree,
    ProofSyntax.prepend, rulesFree.elimination, rulesFree.left, opsFree.transportBound, proofFree]

theorem orderedInjective_free (left right first second : Term Const Γ object) (rules : Rules ops Δ)
    (equal : ProofSyntax Const Δ (.eq (orderedBy ops.pair left right) (orderedBy ops.pair first second)))
    (opsFree : ops.Free) (rulesFree : rules.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (orderedInjective ops left right first second rules equal).FunctionExtensionalityFree := by
  have firstFree := firstCoordinate_free ops left right first second rules equal opsFree rulesFree proofFree
  simp only [orderedInjective, ProofSyntax.FunctionExtensionalityFree]
  refine ⟨firstFree, ?_⟩
  apply anchoredInjective_free ops left right second rules _ opsFree rulesFree
  apply anchoredInjective_free ops (ops.pair left left) (ops.pair left right) (ops.pair left second)
    rules _ opsFree rulesFree
  exact ⟨proofFree, opsFree.orderedCongrFirst second _ firstFree⟩

/-- A concrete implementation using ordinary typed binary operation terms. -/
def termOperations (membership : Term Const Γ (object ⇒ object ⇒ .prop))
    (pairing : Term Const Γ (object ⇒ object ⇒ object)) : Operations Const Γ object where
  member point bound := .app (.app membership point) bound
  pair left right := .app (.app pairing left) right
  transportBound point equal admitted := .impE (.eqPropEL (.eqAppArg (.app membership point) equal)) admitted
  orderedCongrFirst right equal :=
    let pairCongr := fun {Δ : List (Formula Const Γ)} {a b c d : Term Const Γ object}
      (first : ProofSyntax Const Δ (.eq a b)) (second : ProofSyntax Const Δ (.eq c d)) =>
        ProofSyntax.eqTrans (.eqApp c (.eqAppArg pairing first)) (.eqAppArg (.app pairing b) second)
    pairCongr (pairCongr equal equal) (pairCongr equal (.eqRefl right))

theorem termOperations_free (membership : Term Const Γ (object ⇒ object ⇒ .prop))
    (pairing : Term Const Γ (object ⇒ object ⇒ object)) : (termOperations membership pairing).Free where
  transportBound _ _ _ first second := ⟨first,second⟩
  orderedCongrFirst _ _ free := ⟨⟨free,free⟩,⟨free,trivial⟩⟩

end Mettapedia.Logic.HOL.PairingReconstruction

