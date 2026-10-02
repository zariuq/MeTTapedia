import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetValues
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Controls

/-!
# The root steps of the object package at their typed instances in the set tower

With the values of its constants in the seeded tower (`objectSetConsts`), every rewrite schema
of the object package (`objectSchemas`) is **valid at its typed instances**
(`TowerInterpretation.SchemaValid`): wherever the values of the metavariables lie in the values
of the types the positions of its left side require, and the point of a reflexivity position
has the value of its endpoints, the elaborated left and right sides have one value.

The validity theorems of the schemas are in the namespace `CodeModel.SetTower`:

* **The iota steps of `num-rec`** (`SetTower.numRecZero_valid`, `SetTower.numRecSuc_valid`): at
  zero the value at zero, at a successor the step at the predecessor applied to the recursive
  value.
* **Addition, the iterated power set and the iterator** (`SetTower.addZero_valid`,
  `SetTower.addSuc_valid`, `SetTower.powZero_valid`, `SetTower.powSuc_valid`,
  `SetTower.iterZero_valid`, `SetTower.iterSuc_valid`): their equations by recursion on the
  naturals.
* **Identity elimination** (`SetTower.j_valid`): its linear rule, at the instances whose
  reflexivity point has the value of both endpoints; the path then has the value of
  reflexivity.
* **The definitions by one equation** (`SetTower.eqAt_valid`, …, `SetTower.sucStep_valid`), by
  the generic theorem for definitions (`TowerInterpretation.definition_valid`).
* **The decoding of the codes** (`SetTower.imp_valid`, `SetTower.all_valid`,
  `SetTower.eq_valid`): implication decodes to the trace functions between truth values, which
  form the truth value of the implication, the quantifier at every simple type to the trace
  product over its set, and the equation to the identity value.

**The package** (`SetTower.objectSchemas_valid`, `objectChurch_step_valid`): every root step of
the object package's annotation is an instance of a schema valid at its typed instances. The
premises the package requires of a step give exactly those typed instances, so the object
package has a set model in the seeded tower (`objectSetModel`) and every derivation of its
annotated judgment holds there (`objectChurch_sound_tower`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph sigmaSet mem_sigmaSet)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta tracePiSet_congr)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open FormationSensitiveHOLInterface (typeAt typeAt_rename)
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName eqAtTelescope transportTelescope composeTelescope)
open Mettapedia.Logic
open Mettapedia.SetTheory

universe u

namespace CodeModel

/-! ## Helpers -/

/-- The natural of a successor. -/
theorem natOf_insert {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) : natOf (insert n n) = natOf n + 1 := by
  have e : insert n n = numeral (natOf n + 1) := by rw [numeral_succ, numeral_natOf hn]
  rw [e, natOf_numeral]

/-- **The trace functions between two truth values form the truth value of the
implication.** -/
theorem tracePiSet_truth_values {p q : ZFSet.{u}} (hp : p ∈ Square.omega) (hq : q ∈ Square.omega) :
    tracePiSet p (fun _ => q) = truthCode ((∅ : ZFSet.{u}) ∈ p → (∅ : ZFSet.{u}) ∈ q) := by
  have hq' : truthCode ((∅ : ZFSet.{u}) ∈ q) = q :=
    Square.truthCode_empty_mem (ZFSet.mem_powerset.mp hq)
  have fibres : tracePiSet p (fun _ => q) = tracePiSet p fun _ => truthCode ((∅ : ZFSet.{u}) ∈ q) :=
    tracePiSet_congr fun _ _ => hq'.symm
  rw [fibres, Controls.tracePiSet_truthCode]
  apply congrArg truthCode
  apply propext
  constructor
  · intro all hpe
    exact all ∅ hpe
  · intro implication x hx
    have hx' : x = ∅ := ZFSet.mem_singleton.mp (ZFSet.mem_powerset.mp hp hx)
    subst hx'
    exact implication hx

section Steps

variable (h : CofinalInaccessibles.{u})

/-! ## The recursor -/

/-- **The iota step at zero is valid at typed instances.** -/
theorem SetTower.numRecZero_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (iotaLeft numRecName zeroN 2 0) (iotaRight numRecName 2 0 ([] : List CtorField)) := by
  intro η typed
  have sat : Sat (objHeads h) (objectSetConsts h) cRecTele η := typed.sat numRecZero_knowledge
  rw [numRecZero_elabLeft, numRecZero_elabRight]
  have hz : objectSetConsts h zeroN ∈ objectSetConsts h numN := by
    rw [setConst_zero h, setConst_num h]
    exact numeral_mem_omega 0
  have satN : Sat (objHeads h) (objectSetConsts h) (nrTele numNames)
      (extend η (objectSetConsts h zeroN)) :=
    (sat_snoc _ _).mpr ⟨sat, hz⟩
  have key := numRecValue_zero satN (setConst_zero h)
  rw [← numRec_value h] at key
  exact key

/-- **The iota step at a successor is valid at typed instances.** -/
theorem SetTower.numRecSuc_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (iotaLeft numRecName sucN 2 1) (iotaRight numRecName 2 1 [(.recursive : CtorField)]) := by
  intro η typed
  have sat : Sat (objHeads h) (objectSetConsts h) (CCtx.snoc cRecTele cnum) η :=
    typed.sat numRecSuc_knowledge
  obtain ⟨satRec, hn⟩ := sat_tail _ _ sat
  have hn' : η 0 ∈ ZFSet.omega := by
    have number : η 0 ∈ objectSetConsts h numN := hn
    rwa [setConst_num h] at number
  rw [numRecSuc_elabLeft, numRecSuc_elabRight]
  have hs : traceApp (objectSetConsts h sucN) (η 0) ∈ objectSetConsts h numN := by
    rw [suc_apply h hn', setConst_num h]
    exact insert_mem_omega hn'
  have satL : Sat (objHeads h) (objectSetConsts h) (nrTele numNames)
      (extend (η ∘ Fin.succ) (traceApp (objectSetConsts h sucN) (η 0))) :=
    (sat_snoc _ _).mpr ⟨satRec, hs⟩
  have succ : traceApp (objectSetConsts h sucN) (η 0) = numeral (natOf (η 0) + 1) := by
    rw [suc_apply h hn', numeral_succ, numeral_natOf hn']
  have left := numRecValue_succ satL succ
  have right := numRecValue_apply (N := numNames) sat
  rw [← numRec_value h] at left right
  change applyValues (objectSetConsts h numRecName) 4
      (extend (η ∘ Fin.succ) (traceApp (objectSetConsts h sucN) (η 0))) =
    traceApp (traceApp (η 1) (η 0)) (applyValues (objectSetConsts h numRecName) 4 η)
  rw [left, right, numeral_natOf hn']
  rfl

/-! ## Addition, the iterated power set and the iterator -/

theorem SetTower.addZero_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN [])) := by
  intro η typed
  have sat := typed.sat addZero_knowledge
  have hn : η 0 ∈ objectSetConsts h numN := sat 0
  rw [setConst_num h] at hn
  rw [addZero_elabLeft, addZero_elabRight]
  show traceApp (traceApp (objectSetConsts h addN) (η 0)) (objectSetConsts h zeroN) = η 0
  rw [setConst_zero h, add_apply h hn (numeral_mem_omega 0), natOf_numeral, Nat.add_zero,
    numeral_natOf hn]

theorem SetTower.addSuc_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 [.recursive]) (addBody sucN [.recursive])) := by
  intro η typed
  have sat := typed.sat addSuc_knowledge
  have ha : η 1 ∈ objectSetConsts h numN := sat 1
  have hb : η 0 ∈ objectSetConsts h numN := sat 0
  rw [setConst_num h] at ha hb
  rw [addSuc_elabLeft, addSuc_elabRight]
  show traceApp (traceApp (objectSetConsts h addN) (η 1)) (traceApp (objectSetConsts h sucN) (η 0)) =
    traceApp (objectSetConsts h sucN) (traceApp (traceApp (objectSetConsts h addN) (η 1)) (η 0))
  have hs : traceApp (objectSetConsts h sucN) (η 0) ∈ ZFSet.omega := by
    rw [suc_apply h hb]
    exact insert_mem_omega hb
  rw [add_apply h ha hs, add_apply h ha hb, suc_apply h (numeral_mem_omega _), suc_apply h hb,
    natOf_insert hb]
  rfl

theorem SetTower.powZero_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 []) (powBody zeroN [])) := by
  intro η typed
  have sat := typed.sat powZero_knowledge
  have hX : η 0 ∈ objectSetConsts h setN := sat 0
  rw [setConst_set h] at hX
  rw [powZero_elabLeft, powZero_elabRight]
  show traceApp (traceApp (objectSetConsts h powN) (objectSetConsts h zeroN)) (η 0) = η 0
  rw [setConst_zero h, pow_apply h (numeral_mem_omega 0) hX, natOf_numeral]
  rfl

theorem SetTower.powSuc_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 [.recursive]) (powBody sucN [.recursive])) := by
  intro η typed
  have sat := typed.sat powSuc_knowledge
  have hn : η 1 ∈ objectSetConsts h numN := sat 1
  have hX : η 0 ∈ objectSetConsts h setN := sat 0
  rw [setConst_num h] at hn
  rw [setConst_set h] at hX
  rw [powSuc_elabLeft, powSuc_elabRight]
  show traceApp (traceApp (objectSetConsts h powN) (traceApp (objectSetConsts h sucN) (η 1))) (η 0) =
    traceApp (objectSetConsts h powerN) (traceApp (traceApp (objectSetConsts h powN) (η 1)) (η 0))
  have hs : traceApp (objectSetConsts h sucN) (η 1) ∈ ZFSet.omega := by
    rw [suc_apply h hn]
    exact insert_mem_omega hn
  rw [pow_apply h hs hX, pow_apply h hn hX, power_apply h (powIter_mem hX _), suc_apply h hn,
    natOf_insert hn]
  rfl

theorem SetTower.iterZero_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN [])) := by
  intro η typed
  have sat : Sat (objHeads h) (objectSetConsts h) cIterTele η := typed.sat iterZero_knowledge
  rw [iterZero_elabLeft, iterZero_elabRight]
  have hz : objectSetConsts h zeroN ∈ objectSetConsts h numN := by
    rw [setConst_zero h, setConst_num h]
    exact numeral_mem_omega 0
  -- the count zero, then the instance's carrier, family, step, value and evidence
  have hA : η 4 ∈ lowest h := sat 4
  have hP : η 3 ∈ tracePiSet (η 4) fun _ => lowest h := sat 3
  have hstep : η 2 ∈ stepSet (η 4) (η 3) := sat 2
  have hx : η 1 ∈ η 4 := sat 1
  have he : η 0 ∈ traceApp (η 3) (η 1) := sat 0
  have satI : Sat (objHeads h) (objectSetConsts h) cIterSucTele
      (extend (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h zeroN)) (η 4))
        (η 3)) (η 2)) (η 1)) (η 0)) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hz⟩, hA⟩, hP⟩, hstep⟩,
        hx⟩, he⟩
  have key := iter_apply h satI
  change applyValues (objectSetConsts h iterName) 6
      (extend (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h zeroN)) (η 4))
        (η 3)) (η 2)) (η 1)) (η 0)) = ZFSet.pair (η 1) (η 0)
  rw [key]
  change iterPair (η 2) (natOf (objectSetConsts h zeroN)) (ZFSet.pair (η 1) (η 0)) = _
  rw [setConst_zero h, natOf_numeral]
  rfl

theorem SetTower.iterSuc_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) := by
  intro η typed
  have sat : Sat (objHeads h) (objectSetConsts h) cIterSucTele η := typed.sat iterSuc_knowledge
  rw [iterSuc_elabLeft, iterSuc_elabRight]
  obtain ⟨hn, hstep, hx, he⟩ := iterTele_sat h sat
  have hA : η 4 ∈ lowest h := sat 4
  have hP : η 3 ∈ tracePiSet (η 4) fun _ => lowest h := sat 3
  have hs : traceApp (objectSetConsts h sucN) (η 5) ∈ objectSetConsts h numN := by
    rw [suc_apply h hn, setConst_num h]
    exact insert_mem_omega hn
  have hn' : η 5 ∈ objectSetConsts h numN := by
    rw [setConst_num h]
    exact hn
  -- the left side: the iterator at the successor of the count
  have satL : Sat (objHeads h) (objectSetConsts h) cIterSucTele
      (extend (extend (extend (extend (extend (extend Fin.elim0
        (traceApp (objectSetConsts h sucN) (η 5))) (η 4)) (η 3)) (η 2)) (η 1)) (η 0)) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hs⟩, hA⟩, hP⟩, hstep⟩,
        hx⟩, he⟩
  -- the right side: one use of the step, then the iterator at the count
  have hqPair : traceApp (traceApp (η 2) (η 1)) (η 0) ∈ sigmaSet (η 4) fun y => traceApp (η 3) y := by
    have atX := traceApp_mem_fibre hstep hx
    exact traceApp_mem_fibre atX he
  have satR : Sat (objHeads h) (objectSetConsts h) cIterSucTele
      (extend (extend (extend (extend (extend (extend Fin.elim0 (η 5)) (η 4)) (η 3)) (η 2))
        (ZFSetOrderedPair.first (traceApp (traceApp (η 2) (η 1)) (η 0))))
        (ZFSetOrderedPair.second (traceApp (traceApp (η 2) (η 1)) (η 0)))) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hn'⟩, hA⟩, hP⟩, hstep⟩,
        first_mem_sigmaSet hqPair⟩, second_mem_sigmaSet hqPair⟩
  have left := iter_apply h satL
  have right := iter_apply h satR
  change applyValues (objectSetConsts h iterName) 6
      (extend (extend (extend (extend (extend (extend Fin.elim0
        (traceApp (objectSetConsts h sucN) (η 5))) (η 4)) (η 3)) (η 2)) (η 1)) (η 0)) =
    traceApp (traceLam (graph (sigmaSet (η 4) fun y => traceApp (η 3) y) fun pack =>
      applyValues (objectSetConsts h iterName) 6
        (extend (extend (extend (extend (extend (extend Fin.elim0 (η 5)) (η 4)) (η 3)) (η 2))
          (ZFSetOrderedPair.first pack)) (ZFSetOrderedPair.second pack))))
      (traceApp (traceApp (η 2) (η 1)) (η 0))
  rw [traceApp_graph_beta _ hqPair, left, right]
  change iterPair (η 2) (natOf (traceApp (objectSetConsts h sucN) (η 5)))
      (ZFSet.pair (η 1) (η 0)) =
    iterPair (η 2) (natOf (η 5))
      (ZFSet.pair (ZFSetOrderedPair.first (traceApp (traceApp (η 2) (η 1)) (η 0)))
        (ZFSetOrderedPair.second (traceApp (traceApp (η 2) (η 1)) (η 0))))
  rw [suc_apply h hn, natOf_insert hn, pair_first_second hqPair]
  show iterPair (η 2) (natOf (η 5))
      (traceApp (traceApp (η 2) (ZFSetOrderedPair.first (ZFSet.pair (η 1) (η 0))))
        (ZFSetOrderedPair.second (ZFSet.pair (η 1) (η 0)))) = _
  rw [ZFSetOrderedPair.first_pair, ZFSetOrderedPair.second_pair]

/-! ## Identity elimination -/

/-- **The linear rule of identity elimination is valid at typed instances**: at an instance
whose reflexivity point has the value of the base point and of the endpoint, the path has the
value of reflexivity and the eliminator returns the method. -/
theorem SetTower.j_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls (eliminatorLeft jName) (.var 2) := by
  intro η typed
  have sat : Sat (objHeads h) (objectSetConsts h) cJTele η := typed.sat j_knowledge
  have equations := typed.2
  rw [j_equations] at equations
  have toBase : η 0 = η 4 := equations _ List.mem_cons_self
  have toEnd : η 0 = η 1 := equations _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [j_elabLeft, j_elabRight]
  obtain ⟨satFive, -⟩ := sat_tail _ _ sat
  have path : (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
      (.id (.var 4) (.var 3) (.var 0) : CTm Tower.Head 5) (η ∘ Fin.succ) := by
    show (∅ : ZFSet.{u}) ∈ truthCode (η 4 = η 1)
    rw [← toBase, ← toEnd]
    exact empty_mem_truthCode_eq _
  have satJ : Sat (objHeads h) (objectSetConsts h) (jTele (.sort Tower.zero))
      (extend (η ∘ Fin.succ) ∅) :=
    (sat_snoc _ _).mpr ⟨satFive, path⟩
  have key := jValue_apply satJ
  rw [← j_value h] at key
  exact key

/-! ## The definitions by one equation -/

theorem definition_value {f : DeclName} {tag : ObjConst} (named : objConst f = tag) {k : Nat}
    {Θ : Tower.Ctx k} {rhs : Tower.Tm k}
    (raw : tag.setRaw (objHeads h) (objectSetConsts h) =
      defSetRaw (objHeads h) (objectSetConsts h) f Θ rhs) :
    objectSetConsts h f = telescopeGraph (objHeads h) (objectSetConsts h) (liftCtx Θ)
      fun η => ev (objHeads h) (objectSetConsts h)
        (elabRight objectDecls (applyClosed Θ Presentation.ids (.const f)) rhs) η := by
  rw [objectSetConsts_of h named, raw, defSetRaw_eq]

theorem SetTower.eqAt_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed eqAtTele Presentation.ids (.const eqAtName)) eqAtRhs :=
  definition_valid (liftCtx eqAtTele) (by decide)
    (definition_value h (show objConst eqAtName = .eqAt by decide) rfl)

theorem SetTower.sucMove_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed eqAtTelescope Presentation.ids (.const sucMoveName)) sucMoveRhs :=
  definition_valid (liftCtx eqAtTelescope) (by decide)
    (definition_value h (show objConst sucMoveName = .sucMove by decide) rfl)

theorem SetTower.keep_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed keepTele Presentation.ids (.const keepName)) keepRhs :=
  definition_valid (liftCtx keepTele) (by decide)
    (definition_value h (show objConst keepName = .keep by decide) rfl)

theorem SetTower.transport_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed transportTelescope Presentation.ids (.const transportName)) transportRhs :=
  definition_valid (liftCtx transportTelescope) (by decide)
    (definition_value h (show objConst transportName = .transport by decide) rfl)

theorem SetTower.compose_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed composeTelescope Presentation.ids (.const composeName)) composeRhs :=
  definition_valid (liftCtx composeTelescope) (by decide)
    (definition_value h (show objConst composeName = .compose by decide) rfl)

theorem SetTower.returnIter_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed returnIterTele Presentation.ids (.const returnIterName)) returnIterRhs :=
  definition_valid (liftCtx returnIterTele) (by decide)
    (definition_value h (show objConst returnIterName = .returnIter by decide) rfl)

theorem SetTower.sucStep_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls
      (applyClosed eqAtTelescope Presentation.ids (.const sucStepName)) sucStepRhs :=
  definition_valid (liftCtx eqAtTelescope) (by decide)
    (definition_value h (show objConst sucStepName = .sucStep by decide) rfl)

end Steps

/-! ## The decoding of the codes -/

section Decoders

variable (h : CofinalInaccessibles.{u})

/-- **The decoding of an implication is valid at typed instances**: the trace functions from
the truth value of `p` to that of `q` form the truth value of the implication. -/
theorem SetTower.imp_valid :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls impLeft impRight := by
  intro η typed
  have sat := typed.sat imp_knowledge
  have hp : η 1 ∈ objectSetConsts h propN := sat 1
  have hq : η 0 ∈ objectSetConsts h propN := sat 0
  rw [setConst_prop h] at hp hq
  rw [elabLeft_firstOrder objectDecls rfl, imp_elabRight]
  show traceApp (objectSetConsts h holdsN) (traceApp (traceApp (objectSetConsts h impN) (η 1)) (η 0)) =
    tracePiSet (traceApp (objectSetConsts h holdsN) (η 1)) fun _ =>
      traceApp (objectSetConsts h holdsN) (η 0)
  rw [imp_apply h hp hq, holds_apply h (Square.truthCode_mem_omega _), holds_apply h hp,
    holds_apply h hq, tracePiSet_truth_values hp hq]

/-- **The decoding of a quantifier is valid at typed instances, at every simple type**: the
trace product over the type's set of the truth values of the instances is the truth value of
the quantification. -/
theorem SetTower.all_valid (type : HOL.Ty SetProfile.SetBase) :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls (allLeft type) (allRight type) := by
  intro η typed
  have sat := typed.sat (all_knowledge type)
  have member := sat 0
  rw [liftCtx_lookup, Ctx.lookup_snoc_zero, typeAt_rename, ev_objTypeAt h] at member
  rw [elabLeft_firstOrder objectDecls rfl, all_elabRight]
  have domain : ev (objHeads h) (objectSetConsts h)
      (liftTm (liftClosed (typeAt SetProfile.types 0 type) : Tower.Tm 1)) η = simpleSet type := by
    rw [liftClosed_typeAt]
    exact ev_objTypeAt h type η
  show traceApp (objectSetConsts h holdsN)
      (traceApp (objectSetConsts h (SetProfile.allName type)) (η 0)) =
    tracePiSet (ev (objHeads h) (objectSetConsts h)
      (liftTm (liftClosed (typeAt SetProfile.types 0 type) : Tower.Tm 1)) η) fun x =>
        traceApp (objectSetConsts h holdsN) (traceApp (η 0) x)
  rw [domain, all_apply h type member, holds_apply h (Square.truthCode_mem_omega _)]
  have fibres : (tracePiSet (simpleSet type) fun x =>
      traceApp (objectSetConsts h holdsN) (traceApp (η 0) x)) =
      tracePiSet (simpleSet type) fun x => truthCode ((∅ : ZFSet.{u}) ∈ traceApp (η 0) x) := by
    apply tracePiSet_congr
    intro x hx
    have value : traceApp (η 0) x ∈ Square.omega := traceApp_mem_fibre member hx
    rw [holds_apply h value, Square.truthCode_empty_mem (ZFSet.mem_powerset.mp value)]
  rw [fibres, Controls.tracePiSet_truthCode]

/-- **The decoding of an equation is valid at typed instances, at every simple type**: the
equation code and the identity type have one truth value. -/
theorem SetTower.eq_valid (type : HOL.Ty SetProfile.SetBase) :
    SchemaValid (objHeads h) (objectSetConsts h) objectDecls (eqLeft type) (eqRight type) := by
  intro η typed
  have sat := typed.sat (eq_knowledge type)
  have hx := sat 1
  have hy := sat 0
  rw [liftCtx_lookup] at hx hy
  change η 1 ∈ ev (objHeads h) (objectSetConsts h)
    (liftTm (Presentation.rename wk (Presentation.rename wk (typeAt SetProfile.types 0 type)))) η
    at hx
  change η 0 ∈ ev (objHeads h) (objectSetConsts h)
    (liftTm (Presentation.rename wk (typeAt SetProfile.types 1 type))) η at hy
  rw [typeAt_rename, typeAt_rename, ev_objTypeAt h] at hx
  rw [typeAt_rename, ev_objTypeAt h] at hy
  rw [elabLeft_firstOrder objectDecls rfl, eq_elabRight]
  show traceApp (objectSetConsts h holdsN)
      (traceApp (traceApp (objectSetConsts h (SetProfile.eqName type)) (η 1)) (η 0)) =
    truthCode (η 1 = η 0)
  rw [eq_apply h type hx hy, holds_apply h (Square.truthCode_mem_omega _)]

end Decoders

/-! ## The package -/

section Package

variable (h : CofinalInaccessibles.{u})

/-- **Every rewrite schema of the object package is valid at its typed instances** in the
seeded tower, relative to `CofinalInaccessibles`. -/
theorem SetTower.objectSchemas_valid :
    FamilyValid (objHeads h) (objectSetConsts h) objectDecls objectSchemas := by
  intro k L R rule
  rcases rule with rule | rule
  · obtain ⟨p, mem, rule⟩ := DeclaredComputation.mem_of_schemaUnionAll rule
    simp only [computationSpecs, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨i, k', fields, hi, rule⟩ := rule
      rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact SetTower.numRecZero_valid h
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact SetTower.numRecSuc_valid h
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hi
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact SetTower.addZero_valid h
      · exact SetTower.addSuc_valid h
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact SetTower.powZero_valid h
      · exact SetTower.powSuc_valid h
    · cases rule
      exact SetTower.j_valid h
    · cases rule
      exact SetTower.eqAt_valid h
    · cases rule
      exact SetTower.sucMove_valid h
    · cases rule
      exact SetTower.keep_valid h
    · cases rule
      exact SetTower.transport_valid h
    · cases rule
      exact SetTower.compose_valid h
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule
      · exact SetTower.iterZero_valid h
      · exact SetTower.iterSuc_valid h
    · cases rule
      exact SetTower.returnIter_valid h
    · cases rule
      exact SetTower.sucStep_valid h
  · rcases rule with rule | ⟨a, A, carrier, rule⟩ | ⟨e, A, carrier, rule⟩
    · cases rule
      exact SetTower.imp_valid h
    · change (SetProfile.allInstance? a).map typeTerm = some A at carrier
      cases found : SetProfile.allInstance? a with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.allInstance?_eq_some found
          cases rule
          exact SetTower.all_valid h type
    · change (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A
        at carrier
      rw [if_pos rfl] at carrier
      cases found : SetProfile.eqInstance? e with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.eqInstance?_eq_some found
          cases rule
          exact SetTower.eq_valid h type

/-- **Every root step of the object package's annotation is valid at its typed instances**:
it is an instance of a schema of the package by a substitution, and at every environment at
which the values of the substituted terms form a typed instance of the schema's left side, its
two sides have one value. -/
theorem objectChurch_step_valid {n : Nat} {l r : CTm Tower.Head n}
    (step : objectChurch.computation.step l r) :
    ∃ (k : Nat) (L R : Tm Tower.Head k) (σ : CSub Tower.Head k n), objectSchemas L R ∧
      l = (elabLeft objectDecls L).subst σ ∧ r = (elabRight objectDecls L R).subst σ ∧
        ∀ ρ : Env.{u} n,
          TypedInstance (objHeads h) (objectSetConsts h) objectDecls L
            (fun i => ev (objHeads h) (objectSetConsts h) (σ i) ρ) →
          ev (objHeads h) (objectSetConsts h) l ρ = ev (objHeads h) (objectSetConsts h) r ρ := by
  change CSchemaStep (elaborateFamily objectDecls objectSchemas) l r at step
  cases step with
  | instantiate rule σ =>
      obtain ⟨L, R, hS, rfl, rfl⟩ := rule
      exact ⟨_, L, R, σ, hS, rfl, rfl, fun ρ typed =>
        (SetTower.objectSchemas_valid h hS).instantiate σ ρ typed⟩

/-- **The object package has a set model in the seeded tower**, relative to
`CofinalInaccessibles`: the universe rules hold, every declared constant's value lies in the
value of its declared type, and every root step has one value on both sides wherever its
premises hold, the typings of the instances of its metavariables and the equations of its
reflexivity positions. -/
theorem objectSetModel : SetModel (objHeads h) (objectSetConsts h) objectChurch :=
  SetModel.ofSchemas
    { (towerModel h ZFSet.omega ∅ (fun _ => 0) (empty_mem_level h 0) (fun _ => ∅)).universes
      with }
    (towerModel h ZFSet.omega ∅ (fun _ => 0) (empty_mem_level h 0) (fun _ => ∅)).headEq
    (fun declared => objectSetConsts_typed h declared) (SetTower.objectSchemas_valid h)

/-- **Soundness of the object package in the seeded tower.** Relative to
`CofinalInaccessibles`, every derivable annotated statement of the object package holds in
the tower: a typed term's value lies in its type's value, and equal terms have one value. -/
theorem objectChurch_sound_tower {s : CStatement Tower.Head}
    (derivation : CDerivable objectChurch s) : Holds (objHeads h) (objectSetConsts h) s :=
  CDerivable.sound (objectSetModel h) derivation

end Package

/-! ## The model at every assignment that agrees on the names of the package

An extension of the object package by further constants gives those constants values of its
own. The object package keeps its model there: its declared types and the templates of its
schemas mention only names it declares. -/

section Agreement

open Presentation.TypedEquality.Impredicative.Domain (termConsts)

/-- Whether the object package declares a name. -/
def objectDeclared (c : DeclName) : Bool := (objectRules.constantType c).isSome

theorem objectDeclared_of_declared {c : DeclName} {T : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some T) : objectDeclared c = true := by
  rw [objectChurch_constantType] at declared
  unfold elabDeclarations at declared
  unfold objectDeclared
  cases found : objectRules.constantType c with
  | none =>
    rw [found] at declared
    exact nomatch declared
  | some _ => rfl

theorem objectDeclared_allName (type : HOL.Ty SetProfile.SetBase) :
    objectDeclared (SetProfile.allName type) = true := by
  unfold objectDeclared
  rw [declared_allName type]
  rfl

theorem objectDeclared_eqName (type : HOL.Ty SetProfile.SetBase) :
    objectDeclared (SetProfile.eqName type) = true := by
  unfold objectDeclared
  rw [declared_eqName type]
  rfl

/-- The translation of a simple type mentions only declared names. -/
theorem closedTerm_typeAt (type : HOL.Ty SetProfile.SetBase) {n : Nat} :
    closedTerm objectDeclared
      (liftTm (typeAt SetProfile.types n type) : CTm Tower.Head n) = true :=
  closedTerm_iff.mpr fun c mem => by
    rcases termConsts_typeAt type mem with rfl | rfl | rfl <;> decide

/-- **The declared type of every constant mentions only declared names.** -/
theorem ObjConst.declType_closed : ∀ tag : ObjConst, closedTerm objectDeclared tag.declType = true
  | .all type => closedTerm_typeAt (.arr (.arr type .prop) .prop)
  | .eq type => closedTerm_typeAt (.arr type (.arr type .prop))
  | .num => by decide
  | .set => by decide
  | .prop => by decide
  | .other => by decide
  | .zero => by decide
  | .suc => by decide
  | .add => by decide
  | .power => by decide
  | .pow => by decide
  | .numRec => by decide
  | .j => by decide
  | .eqAt => by decide
  | .sucMove => by decide
  | .keep => by decide
  | .transport => by decide
  | .compose => by decide
  | .iter => by decide
  | .returnIter => by decide
  | .sucStep => by decide
  | .holds => by decide
  | .imp => by decide

theorem all_equations (type : HOL.Ty SetProfile.SetBase) :
    patternEquations objectDecls none (allLeft type) = [] := by
  simp [patternEquations]

theorem eqLeft_equations (type : HOL.Ty SetProfile.SetBase) :
    patternEquations objectDecls none (eqLeft type) = [] := by
  simp [patternEquations]

/-- The decoding of a quantifier mentions only declared names, at every simple type. -/
theorem all_closed (type : HOL.Ty SetProfile.SetBase) :
    SchemaClosed objectDecls objectDeclared (allLeft type) (allRight type) where
  left := by
    rw [elabLeft_firstOrder objectDecls rfl]
    refine closedTerm_iff.mpr fun c mem => ?_
    change c ∈ [holdsN, SetProfile.allName type] at mem
    rcases List.mem_cons.mp mem with rfl | mem
    · decide
    · obtain rfl := List.mem_singleton.mp mem
      exact objectDeclared_allName type
  right := by
    rw [all_elabRight]
    refine closedTerm_iff.mpr fun c mem => ?_
    change c ∈ termConsts (liftTm (liftClosed (typeAt SetProfile.types 0 type) : Tower.Tm 1)) ++
      [holdsN] at mem
    rcases List.mem_append.mp mem with mem | mem
    · rw [liftClosed_typeAt] at mem
      exact closedTerm_iff.mp (closedTerm_typeAt type) c mem
    · obtain rfl := List.mem_singleton.mp mem
      decide
  types := by
    intro i T known
    rw [all_knowledge type i] at known
    obtain rfl := Option.some.inj known
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [liftCtx_lookup, Ctx.lookup_snoc_zero, typeAt_rename]
    exact closedTerm_typeAt _
  equations := by
    intro e mem
    rw [all_equations type] at mem
    exact nomatch mem

/-- The decoding of an equation mentions only declared names, at every simple type. -/
theorem eq_closed (type : HOL.Ty SetProfile.SetBase) :
    SchemaClosed objectDecls objectDeclared (eqLeft type) (eqRight type) where
  left := by
    rw [elabLeft_firstOrder objectDecls rfl]
    refine closedTerm_iff.mpr fun c mem => ?_
    change c ∈ [holdsN, SetProfile.eqName type] at mem
    rcases List.mem_cons.mp mem with rfl | mem
    · decide
    · obtain rfl := List.mem_singleton.mp mem
      exact objectDeclared_eqName type
  right := by
    rw [eq_elabRight]
    refine closedTerm_iff.mpr fun c mem => ?_
    change c ∈ termConsts (liftTm (liftClosed (typeAt SetProfile.types 0 type) : Tower.Tm 2)) ++
      [] at mem
    rw [List.append_nil, liftClosed_typeAt] at mem
    exact closedTerm_iff.mp (closedTerm_typeAt type) c mem
  types := by
    intro i T known
    rw [eq_knowledge type i] at known
    obtain rfl := Option.some.inj known
    rw [liftCtx_lookup]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Ctx.lookup_snoc_zero, typeAt_rename]
      exact closedTerm_typeAt _
    · obtain rfl : j = 0 := Subsingleton.elim j 0
      change closedTerm objectDeclared (liftTm (Presentation.rename wk (Presentation.rename wk
        (typeAt SetProfile.types 0 type)))) = true
      rw [typeAt_rename, typeAt_rename]
      exact closedTerm_typeAt _
  equations := by
    intro e mem
    rw [eqLeft_equations type] at mem
    exact nomatch mem

/-- **Every rewrite schema of the object package mentions only names the package declares.** -/
theorem objectSchemas_closed {k : Nat} {L R : Tm Tower.Head k} (rule : objectSchemas L R) :
    SchemaClosed objectDecls objectDeclared L R := by
  rcases rule with rule | rule
  · obtain ⟨p, mem, rule⟩ := DeclaredComputation.mem_of_schemaUnionAll rule
    simp only [computationSpecs, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨i, k', fields, hi, rule⟩ := rule
      rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact SchemaClosed.of_test (by decide)
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        cases rule
        exact SchemaClosed.of_test (by decide)
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hi
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule <;>
        exact SchemaClosed.of_test (by decide)
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule <;>
        exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · obtain ⟨k', fields, mem, rule⟩ := rule
      simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases rule <;>
        exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · cases rule
      exact SchemaClosed.of_test (by decide)
  · rcases rule with rule | ⟨a, A, carrier, rule⟩ | ⟨e, A, carrier, rule⟩
    · cases rule
      exact SchemaClosed.of_test (by decide)
    · change (SetProfile.allInstance? a).map typeTerm = some A at carrier
      cases found : SetProfile.allInstance? a with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.allInstance?_eq_some found
          cases rule
          exact all_closed type
    · change (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A
        at carrier
      rw [if_pos rfl] at carrier
      cases found : SetProfile.eqInstance? e with
      | none => rw [found] at carrier; cases carrier
      | some type =>
          rw [found] at carrier
          cases carrier
          obtain rfl := SetProfile.eqInstance?_eq_some found
          cases rule
          exact eq_closed type

variable (h : CofinalInaccessibles.{u})

/-- **The object package has a set model at every assignment of sets to names that agrees
with its own on the names it declares**, relative to `CofinalInaccessibles`. The values of
all other names are free: an extension of the package by new constants gives them. -/
theorem objectSetModel_agreeing {consts' : DeclName → ZFSet.{u}}
    (same : ∀ c, objectDeclared c = true → objectSetConsts h c = consts' c) :
    SetModel (objHeads h) consts' objectChurch :=
  SetModel.ofSchemas_agreeing
    { (towerModel h ZFSet.omega ∅ (fun _ => 0) (empty_mem_level h 0) (fun _ => ∅)).universes
      with }
    (towerModel h ZFSet.omega ∅ (fun _ => 0) (empty_mem_level h 0) (fun _ => ∅)).headEq
    objectDeclared
    (fun {c T} declared => ⟨objectDeclared_of_declared declared, by
      rw [declType_of_declared declared]
      exact ObjConst.declType_closed _⟩)
    (fun rule => objectSchemas_closed rule)
    (fun declared => objectSetConsts_typed h declared) (SetTower.objectSchemas_valid h) same

/-- **Soundness at every such assignment**: every derivable annotated statement of the object
package holds there. -/
theorem objectChurch_sound_agreeing {consts' : DeclName → ZFSet.{u}}
    (same : ∀ c, objectDeclared c = true → objectSetConsts h c = consts' c)
    {s : CStatement Tower.Head} (derivation : CDerivable objectChurch s) :
    Holds (objHeads h) consts' s :=
  CDerivable.sound (objectSetModel_agreeing h same) derivation

end Agreement

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
