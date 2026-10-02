import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeIndexedFamilies

/-!
# The full universe-polymorphic identity eliminator as a set-coded function

All six arguments are elements of actual set codes: the carrier, left endpoint,
trace-coded motive, method, right endpoint and equality witness. Carrier and
motive levels are independent. The construction uses the existing based J and
trace products, not an assumed interpretation of an elimination constant.

This supplies a model value and its computation law. Sound interpretation of
every native typing derivation is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceIdentityDeclaration

open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (Elements)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetTraceProducts (traceApp)
open ZFSetTraceUniverseInterpretation
open Mettapedia.TypeTheory.Models

universe u

variable {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}

def declarationLevel (i j : Nat) : Nat := max (i + 1) (j + 1)

/-- The enclosing set universe has exactly the level of the existing native
declaration's formation derivation, with its two parameters kept independent. -/
theorem declarationLevel_agrees (valuation : Nat → Nat) :
    NativeIndexedFamilies.Intrinsic.identityEliminateDeclarationLevel.eval valuation =
      declarationLevel (valuation 0) (valuation 1) := by
  simp only [NativeIndexedFamilies.Intrinsic.identityEliminateDeclarationLevel,
    NativeIndexedFamilies.Intrinsic.identityAfterPointLevel,
    NativeIndexedFamilies.Intrinsic.identityAfterMotiveLevel,
    NativeIndexedFamilies.Intrinsic.identityAfterReflLevel,
    NativeIndexedFamilies.Intrinsic.identityEliminateResultLevel,
    NativeIndexedFamilies.Intrinsic.identityMotiveLevel,
    NativeIndexedFamilies.Intrinsic.identityMotiveInnerLevel,
    NativeIndexedFamilies.Intrinsic.elementLevel,
    NativeIndexedFamilies.Intrinsic.motiveLevel,
    Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval,
    Mettapedia.TypeTheory.UniverseLevel.nat_succ, declarationLevel]
  omega

theorem carrier_below (i j : Nat) : i ≤ declarationLevel i j :=
  (Nat.le_succ i).trans (Nat.le_max_left _ _)

theorem motive_below (i j : Nat) : j ≤ declarationLevel i j :=
  (Nat.le_succ j).trans (Nat.le_max_right _ _)

noncomputable def pathCode (a : Code h seed i) (x y : El a) : Code h seed i :=
  proofCode h seed i (x = y)

noncomputable def reflValue (a : Code h seed i) (x : El a) : El (pathCode a x x) :=
  ⟨∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩

noncomputable def motiveRightCode (j : Nat) (a : Code h seed i) (x y : El a) :
    Code h seed (declarationLevel i j) :=
  piCodeWithin (carrier_below i j) (pathCode a x y)
    (fun _ => liftCode (Nat.le_max_right (i + 1) (j + 1)) (universeCode h seed j))

noncomputable def motiveCode (j : Nat) (a : Code h seed i) (x : El a) :
    Code h seed (declarationLevel i j) :=
  piCodeWithin (carrier_below i j) a (motiveRightCode j a x)

/-- Applying the supplied motive twice returns a code at its own level. -/
noncomputable def motiveAt (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (y : El a) (q : El (pathCode a x y)) : Code h seed j :=
  decodePiWithin (carrier_below i j) (pathCode a x y) _
    (decodePiWithin (carrier_below i j) a (motiveRightCode j a x) p y) q

noncomputable def encodeMotive (a : Code h seed i) (x : El a)
    (p : (y : El a) → El (pathCode a x y) → Code h seed j) : El (motiveCode j a x) :=
  (decodePiWithin (carrier_below i j) a (motiveRightCode j a x)).symm
    (fun y => (decodePiWithin (carrier_below i j) (pathCode a x y) _).symm (p y))

theorem motiveAt_encode (a : Code h seed i) (x : El a)
    (p : (y : El a) → El (pathCode a x y) → Code h seed j)
    (y : El a) (q : El (pathCode a x y)) :
    motiveAt a x (encodeMotive a x p) y q = p y q := by
  have first := congrFun
    ((decodePiWithin (carrier_below i j) a (motiveRightCode j a x)).apply_symm_apply
      (fun y => (decodePiWithin (carrier_below i j) (pathCode a x y)
        (fun _ => liftCode (Nat.le_max_right (i + 1) (j + 1))
          (universeCode h seed j))).symm (p y))) y
  exact (congrArg (fun f => decodePiWithin (carrier_below i j) (pathCode a x y)
    (fun _ => liftCode (Nat.le_max_right (i + 1) (j + 1))
      (universeCode h seed j)) f q) first).trans
    (congrFun ((decodePiWithin (carrier_below i j) (pathCode a x y)
      (fun _ => liftCode (Nat.le_max_right (i + 1) (j + 1))
        (universeCode h seed j))).apply_symm_apply (p y)) q)

theorem motiveAt_value (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (y : El a) (q : El (pathCode a x y)) :
    (motiveAt a x p y q).1 = traceApp (traceApp p.1 y.1) q.1 := by
  exact (decodePi_value (pathCode a x y) _
    (decodePiWithin (carrier_below i j) a (motiveRightCode j a x) p y) q).trans
    (congrArg (fun f => traceApp f q.1)
      (decodePi_value a (motiveRightCode j a x) p y))

noncomputable def resultRightCode (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (y : El a) : Code h seed (declarationLevel i j) :=
  piCodeWithin (carrier_below i j) (pathCode a x y)
    (fun q => liftCode (motive_below i j) (motiveAt a x p y q))

noncomputable def resultCode (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) : Code h seed (declarationLevel i j) :=
  piCodeWithin (carrier_below i j) a (resultRightCode a x p)

/-- The already constructed contextual J consumes the decoded motive.
No new endpoint-reflection rule is added to native syntax. -/
noncomputable def eliminate (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (d : El (motiveAt a x p x (reflValue a x)))
    (y : El a) (q : El (pathCode a x y)) : El (motiveAt a x p y q) :=
  SetCodedTypeOperations.Based.elimination.j
    (type := fun _ : PUnit.{u + 2} => a.1) (fun _ => x)
    (fun point => (motiveAt a x p point.1.2 point.2).1)
    (fun _ => d) ⟨⟨PUnit.unit, y⟩, q⟩

theorem eliminate_refl (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (d : El (motiveAt a x p x (reflValue a x))) :
    eliminate a x p d x (reflValue a x) = d := rfl

noncomputable def resultValue (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (d : El (motiveAt a x p x (reflValue a x))) :
    El (resultCode a x p) :=
  (decodePiWithin (carrier_below i j) a (resultRightCode a x p)).symm
    (fun y => (decodePiWithin (carrier_below i j) (pathCode a x y) _).symm
      (fun q => eliminate a x p d y q))

noncomputable def methodFunctionCode (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) : Code h seed (declarationLevel i j) :=
  piCodeWithin (motive_below i j) (motiveAt a x p x (reflValue a x))
    (fun _ => resultCode a x p)

noncomputable def methodFunctionValue (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) : El (methodFunctionCode a x p) :=
  (decodePiWithin (motive_below i j) (motiveAt a x p x (reflValue a x))
    (fun _ => resultCode a x p)).symm (resultValue a x p)

noncomputable def motiveFunctionCode (j : Nat) (a : Code h seed i) (x : El a) :
    Code h seed (declarationLevel i j) :=
  piCodeWithin (Nat.le_refl _) (motiveCode j a x) (methodFunctionCode a x)

noncomputable def motiveFunctionValue (j : Nat) (a : Code h seed i) (x : El a) :
    El (motiveFunctionCode j a x) :=
  (decodePiWithin (Nat.le_refl _) (motiveCode j a x) (methodFunctionCode a x)).symm
    (methodFunctionValue a x)

noncomputable def pointFunctionCode (j : Nat) (a : Code h seed i) :
    Code h seed (declarationLevel i j) :=
  piCodeWithin (carrier_below i j) a (motiveFunctionCode j a)

noncomputable def pointFunctionValue (j : Nat) (a : Code h seed i) :
    El (pointFunctionCode j a) :=
  (decodePiWithin (carrier_below i j) a (motiveFunctionCode j a)).symm
    (motiveFunctionValue j a)

/-- The complete six-argument type lives above both independently chosen
universes. The first argument ranges over the carrier universe, not over
the ambient collection of all set codes. -/
noncomputable def declarationCode (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (i j : Nat) : Code h seed (declarationLevel i j) :=
  piCodeWithin (Nat.le_max_left (i + 1) (j + 1)) (universeCode h seed i)
    (pointFunctionCode j)

noncomputable def declarationValue (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (i j : Nat) : El (declarationCode h seed i j) :=
  (decodePiWithin (Nat.le_max_left (i + 1) (j + 1)) (universeCode h seed i)
    (pointFunctionCode j)).symm (pointFunctionValue j)

theorem carrier_application (j : Nat) (a : Code h seed i) :
    traceApp (declarationValue h seed i j).1 a.1 = (pointFunctionValue j a).1 :=
  traceApp_encodePiWithin (Nat.le_max_left (i + 1) (j + 1))
    (universeCode h seed i) (pointFunctionCode j) (pointFunctionValue j) a

theorem point_application (j : Nat) (a : Code h seed i) (x : El a) :
    traceApp (pointFunctionValue j a).1 x.1 = (motiveFunctionValue j a x).1 :=
  traceApp_encodePiWithin (carrier_below i j) a
    (motiveFunctionCode j a) (motiveFunctionValue j a) x

theorem motive_application (a : Code h seed i) (x : El a) (p : El (motiveCode j a x)) :
    traceApp (motiveFunctionValue j a x).1 p.1 = (methodFunctionValue a x p).1 :=
  traceApp_encodePiWithin (Nat.le_refl _) (motiveCode j a x)
    (methodFunctionCode a x) (methodFunctionValue a x) p

theorem method_application (a : Code h seed i) (x : El a) (p : El (motiveCode j a x))
    (d : El (motiveAt a x p x (reflValue a x))) :
    traceApp (methodFunctionValue a x p).1 d.1 = (resultValue a x p d).1 :=
  traceApp_encodePiWithin (motive_below i j) (motiveAt a x p x (reflValue a x))
    (fun _ => resultCode a x p) (resultValue a x p) d

theorem result_application (a : Code h seed i) (x : El a) (p : El (motiveCode j a x))
    (d : El (motiveAt a x p x (reflValue a x))) (y : El a) (q : El (pathCode a x y)) :
    traceApp (traceApp (resultValue a x p d).1 y.1) q.1 = (eliminate a x p d y q).1 := by
  have first := traceApp_encodePiWithin (carrier_below i j) a (resultRightCode a x p)
    (fun y => (decodePiWithin (carrier_below i j) (pathCode a x y)
      (fun q => liftCode (motive_below i j) (motiveAt a x p y q))).symm
        (fun q => eliminate a x p d y q)) y
  exact (congrArg (fun f => traceApp f q.1) first).trans
    (traceApp_encodePiWithin (carrier_below i j) (pathCode a x y)
      (fun q => liftCode (motive_below i j) (motiveAt a x p y q))
        (fun q => eliminate a x p d y q) q)

theorem six_applications (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (d : El (motiveAt a x p x (reflValue a x)))
    (y : El a) (q : El (pathCode a x y)) :
    traceApp (traceApp (traceApp (traceApp (traceApp (traceApp
      (declarationValue h seed i j).1 a.1) x.1) p.1) d.1) y.1) q.1 =
      (eliminate a x p d y q).1 := by
  rw [carrier_application j a, point_application j a x, motive_application a x p,
    method_application a x p d, result_application a x p d y q]

/-- Six genuine set applications compute the supplied method at reflexivity. -/
theorem declaration_beta (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (d : El (motiveAt a x p x (reflValue a x))) :
    traceApp (traceApp (traceApp (traceApp (traceApp (traceApp
      (declarationValue h seed i j).1 a.1) x.1) p.1) d.1) x.1) ∅ = d.1 :=
  six_applications a x p d x (reflValue a x)

/-- The raw six-application result belongs to the code returned by the
actual supplied motive, rather than merely to an isomorphic output type. -/
theorem six_applications_mem (a : Code h seed i) (x : El a)
    (p : El (motiveCode j a x)) (d : El (motiveAt a x p x (reflValue a x)))
    (y : El a) (q : El (pathCode a x y)) :
    traceApp (traceApp (traceApp (traceApp (traceApp (traceApp
      (declarationValue h seed i j).1 a.1) x.1) p.1) d.1) y.1) q.1 ∈
      traceApp (traceApp p.1 y.1) q.1 := by
  rw [six_applications a x p d y q, ← motiveAt_value a x p y q]
  exact (eliminate a x p d y q).2

/-- Encoding and decoding do not restrict motives to constant families. -/
noncomputable def motiveEquiv (j : Nat) (a : Code h seed i) (x : El a) :
    El (motiveCode j a x) ≃ ((y : El a) → El (pathCode a x y) → Code h seed j) :=
  (decodePiWithin (carrier_below i j) a (motiveRightCode j a x)).trans
    (Equiv.piCongrRight (fun y => decodePiWithin (carrier_below i j) (pathCode a x y) _))

theorem encodeMotive_decode (a : Code h seed i) (x : El a) (p : El (motiveCode j a x)) :
    encodeMotive a x (motiveAt a x p) = p := (motiveEquiv j a x).symm_apply_apply p

theorem distinct_endpoints_rejected (a : Code h seed i) (x y : El a) (different : x ≠ y) :
    ¬ Nonempty (El (pathCode a x y)) := by
  rintro ⟨q⟩
  exact different ((mem_truthCode _ _).mp q.2).2

namespace Controls

open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls (twoCode)
open ZFSetDependentProducts.Controls (empty_mem_two power_empty_mem_two)

noncomputable def zeroPoint (h : CofinalInaccessibles.{u}) : El (twoCode h) :=
  ⟨∅, empty_mem_two⟩

noncomputable def onePoint (h : CofinalInaccessibles.{u}) : El (twoCode h) :=
  ⟨ZFSet.powerset ∅, power_empty_mem_two⟩

theorem points_differ (h : CofinalInaccessibles.{u}) : zeroPoint h ≠ onePoint h := by
  intro equal
  have values := congrArg Subtype.val equal
  change (∅ : ZFSet.{u}) = ZFSet.powerset ∅ at values
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (fun _ hp => hp)
  rw [← values] at member
  exact ZFSet.notMem_empty _ member

/-- A motive may return a universe above the carrier's level. Here its
method is itself a type code, so J computes data, not merely a truth witness. -/
noncomputable def universeMotive (h : CofinalInaccessibles.{u}) :
    El (motiveCode 1 (twoCode h) (zeroPoint h)) :=
  encodeMotive (twoCode h) (zeroPoint h) (fun _ _ => universeCode h ∅ 0)

theorem universeMotive_at (h : CofinalInaccessibles.{u}) (y : El (twoCode h))
    (q : El (pathCode (twoCode h) (zeroPoint h) y)) :
    motiveAt (twoCode h) (zeroPoint h) (universeMotive h) y q = universeCode h ∅ 0 :=
  motiveAt_encode (twoCode h) (zeroPoint h) (fun _ _ => universeCode h ∅ 0) y q

noncomputable def universeMethod (h : CofinalInaccessibles.{u}) :
    El (motiveAt (twoCode h) (zeroPoint h) (universeMotive h)
      (zeroPoint h) (reflValue (twoCode h) (zeroPoint h))) :=
  ⟨(twoCode h).1, by rw [universeMotive_at]; exact (twoCode h).2⟩

theorem universe_method_returned (h : CofinalInaccessibles.{u}) :
    traceApp (traceApp (traceApp (traceApp (traceApp (traceApp
      (declarationValue h ∅ 0 1).1 (twoCode h).1) ∅) (universeMotive h).1)
      (twoCode h).1) ∅) ∅ = (twoCode h).1 :=
  declaration_beta (twoCode h) (zeroPoint h) (universeMotive h) (universeMethod h)

theorem wrong_universe_result_rejected (h : CofinalInaccessibles.{u}) :
    traceApp (traceApp (traceApp (traceApp (traceApp (traceApp
      (declarationValue h ∅ 0 1).1 (twoCode h).1) ∅) (universeMotive h).1)
      (twoCode h).1) ∅) ∅ ≠ ∅ := by
  rw [universe_method_returned]
  intro empty
  have member : (∅ : ZFSet.{u}) ∈ (twoCode h).1 := empty_mem_two
  rw [empty] at member
  exact ZFSet.notMem_empty _ member

theorem wrong_endpoint_rejected (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (El (pathCode (twoCode h) (zeroPoint h) (onePoint h))) :=
  distinct_endpoints_rejected _ _ _ (points_differ h)

theorem universe_cannot_be_its_own_code (h : CofinalInaccessibles.{u}) :
    universeSet h ∅ 0 ∉ universeSet h ∅ 0 := universeSet_no_self_membership h ∅ 0

end Controls

#print axioms declarationValue
#print axioms declarationLevel_agrees
#print axioms motiveAt_value
#print axioms six_applications
#print axioms declaration_beta
#print axioms six_applications_mem
#print axioms encodeMotive_decode
#print axioms Controls.universe_method_returned
#print axioms Controls.wrong_universe_result_rejected
#print axioms Controls.wrong_endpoint_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceIdentityDeclaration
