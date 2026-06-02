import Mettapedia.GSLT.Meredith.InteractiveGSLT
import Mettapedia.GSLT.Synthesis.MainConservation

namespace Mettapedia.GSLT.Meredith.RhoExample

open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The rho trace/account bridge keeps amplitudes inert while focusing on the
intrinsic cost coordinates. -/
def rhoBridgeWeightMap : WeightMap rhoGSLT Complex where
  weight := fun _ => 1

/-- Shared rewrite-path trace for the intrinsic rho cost map. -/
noncomputable def rhoIntrinsicRewritePathTrace
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    QuantumTrace rhoGSLT Nat 2 :=
  rewritePathTrace (S := rhoGSLT) (A := Nat) (k := 2)
    rhoBridgeWeightMap
    rhoIntrinsicCostMap
    path

@[simp] theorem rhoIntrinsicRewritePathTrace_eq_rewritePathTrace
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoIntrinsicRewritePathTrace path =
      rewritePathTrace (S := rhoGSLT) (A := Nat) (k := 2)
        rhoBridgeWeightMap
        rhoIntrinsicCostMap
        path := by
  rfl

theorem rhoIntrinsicRewritePathTraceAccount_eq_totalCost
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicRewritePathTrace path) =
        totalCost rhoIntrinsicCostMap path := by
  simpa [rhoIntrinsicRewritePathTrace] using
    (traceAccount_rewritePathTrace (S := rhoGSLT) (A := Nat) (k := 2)
      rhoBridgeWeightMap
      rhoIntrinsicCostMap
      path)

theorem rhoIntrinsicTotalCost_ticks_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    totalCost rhoIntrinsicCostMap path 1 = path.length := by
  exact totalCost_coord_eq_length_of_step_unit_cost
    (S := rhoGSLT) (cm := rhoIntrinsicCostMap) (i := 1)
    (by
      intro a b h
      exact rhoIntrinsicStepCost_apply_one h)
    path

theorem rhoIntrinsicRewritePathTrace_ticks_eq_length
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicRewritePathTrace path) 1 = path.length := by
  rw [rhoIntrinsicRewritePathTrace, traceAccount_rewritePathTrace]
  exact rhoIntrinsicTotalCost_ticks_eq_length path

theorem rhoIntrinsicLedgerTotalAction_shadow_eq_traceAccount
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction path) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        (rhoIntrinsicRewritePathTrace path) := by
  calc
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction path) =
        totalCost rhoIntrinsicCostMap path := by
          exact rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost path
    _ =
        traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
          (rhoIntrinsicRewritePathTrace path) := by
            symm
            exact rhoIntrinsicRewritePathTraceAccount_eq_totalCost path

theorem rhoIntrinsicTemporalSemanticBridge
    {t u : Pattern} (path : rhoGSLT.RewritePath t u) :
    (totalAction rhoIntrinsicLedgerAction path).temporalList.length = path.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          path.length ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        path.length ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        (rhoIntrinsicRewritePathTrace path) 1 = path.length := by
  constructor
  · exact rhoIntrinsicLedgerTotalAction_temporalLength_eq_length path
  · constructor
    · exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_length path
    · constructor
      · exact rhoIntrinsicDirectSpentTrace_ticks_eq_length path
      · exact rhoIntrinsicRewritePathTrace_ticks_eq_length path

@[simp] theorem rhoRewritePathOfReducesN_cast
    {n m : Nat} {p q : Pattern} (hEq : n = m) (h : ReducesN n p q) :
    rhoRewritePathOfReducesN (cast (by cases hEq; rfl) h) =
      rhoRewritePathOfReducesN h := by
  cases hEq
  rfl

theorem reducesN_cast_proof_irrel
    {n m : Nat} {p q : Pattern} (hEq1 hEq2 : n = m) (h : ReducesN n p q) :
    cast (by cases hEq1; rfl) h = cast (by cases hEq2; rfl) h := by
  apply eq_of_heq
  exact HEq.trans
    (cast_heq (by cases hEq1; rfl) h)
    (HEq.symm (cast_heq (by cases hEq2; rfl) h))

theorem rhoRewritePathOfReducesN_cast_proof_irrel
    {n m : Nat} {p q : Pattern} (hEq1 hEq2 : n = m) (h : ReducesN n p q) :
    rhoRewritePathOfReducesN (cast (by cases hEq1; rfl) h) =
      rhoRewritePathOfReducesN (cast (by cases hEq2; rfl) h) := by
  exact congrArg rhoRewritePathOfReducesN
    (reducesN_cast_proof_irrel hEq1 hEq2 h)

theorem cast_type_proof_irrel
    {α β : Sort _} (e1 e2 : α = β) (x : α) :
    cast e1 x = cast e2 x := by
  apply eq_of_heq
  exact HEq.trans (cast_heq e1 x) (HEq.symm (cast_heq e2 x))

theorem rhoRewritePathOfReducesN_cast_type_proof_irrel
    {n m : Nat} {p q : Pattern}
    (e1 e2 : ReducesN n p q = ReducesN m p q) (h : ReducesN n p q) :
    rhoRewritePathOfReducesN (cast e1 h) =
      rhoRewritePathOfReducesN (cast e2 h) := by
  exact congrArg rhoRewritePathOfReducesN (cast_type_proof_irrel e1 e2 h)

@[simp] theorem rhoRewritePathOfReducesN_cast_congrArg
    {n m : Nat} {p q : Pattern}
    (hEq : n = m) (h : ReducesN n p q) :
    rhoRewritePathOfReducesN
      (cast (congrArg (fun k => ReducesN k p q) hEq) h) =
      rhoRewritePathOfReducesN h := by
  cases hEq
  rfl

theorem rhoRewritePathOfReducesN_cast_succ
    {n m : Nat} {p q r : Pattern}
    (hEq : n + 1 = m) (step : Reduces p q) (rest : ReducesN n q r) :
    rhoRewritePathOfReducesN
      (cast (by cases hEq; rfl) (ReducesN.succ step rest)) =
        GSLT.RewritePath.cons (S := rhoGSLT) ⟨step⟩
          (rhoRewritePathOfReducesN rest) := by
  rw [rhoRewritePathOfReducesN_cast (hEq := hEq)]
  rfl

theorem rhoRewritePathOfReducesN_cast_concat_zero
    {m : Nat} {p q : Pattern} (h : ReducesN m p q) :
    rhoRewritePathOfReducesN
      (cast (Eq.symm (Mettapedia.Languages.ProcessCalculi.RhoCalculus.reducesN_concat._proof_1 p)) h) =
        rhoRewritePathOfReducesN h := by
  let e2 : ReducesN m p q = ReducesN (0 + m) p q :=
    congrArg (fun k => ReducesN k p q) (Nat.zero_add m).symm
  trans rhoRewritePathOfReducesN (cast e2 h)
  · exact rhoRewritePathOfReducesN_cast_type_proof_irrel
      (e1 := Eq.symm (Mettapedia.Languages.ProcessCalculi.RhoCalculus.reducesN_concat._proof_1 p))
      (e2 := e2)
      h
  · exact rhoRewritePathOfReducesN_cast_congrArg (hEq := (Nat.zero_add m).symm) (h := h)

theorem rhoRewritePathOfReducesN_cast_concat_succ
    {n m : Nat} {p q r s : Pattern}
    (step : Reduces p q) (rest : ReducesN n q r) (h2 : ReducesN m r s) :
    rhoRewritePathOfReducesN
      (cast (Eq.symm
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.reducesN_concat._proof_2 (m := m) (k := n)))
        (ReducesN.succ step (reducesN_concat rest h2))) =
          GSLT.RewritePath.cons (S := rhoGSLT) ⟨step⟩
            (rhoRewritePathOfReducesN (reducesN_concat rest h2)) := by
  let hEq : (n + m) + 1 = (n + 1) + m := (Nat.add_right_comm n 1 m).symm
  let e2 : ReducesN ((n + m) + 1) p s = ReducesN ((n + 1) + m) p s :=
    congrArg (fun k => ReducesN k p s) hEq
  trans rhoRewritePathOfReducesN
      (cast e2 (ReducesN.succ step (reducesN_concat rest h2)))
  · exact rhoRewritePathOfReducesN_cast_type_proof_irrel
      (e1 := Eq.symm
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.reducesN_concat._proof_2 (m := m) (k := n)))
      (e2 := e2)
      (ReducesN.succ step (reducesN_concat rest h2))
  · trans rhoRewritePathOfReducesN (ReducesN.succ step (reducesN_concat rest h2))
    · exact rhoRewritePathOfReducesN_cast_congrArg (hEq := hEq) (h := ReducesN.succ step (reducesN_concat rest h2))
    · rfl

theorem rhoRewritePathOfReducesN_concat
    {n m : Nat} {p q r : Pattern} (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    rhoRewritePathOfReducesN (reducesN_concat h1 h2) =
      rewritePathAppend (rhoRewritePathOfReducesN h1) (rhoRewritePathOfReducesN h2) := by
  induction h1 generalizing r with
  | zero p =>
      rw [reducesN_concat_zero]
      rw [rhoRewritePathOfReducesN_cast_concat_zero]
      simp [rewritePathAppend, rhoRewritePathOfReducesN]
  | succ step rest ih =>
      rw [reducesN_concat_succ]
      rw [rhoRewritePathOfReducesN_cast_concat_succ]
      simpa [rewritePathAppend, rhoRewritePathOfReducesN] using
        congrArg (fun path => GSLT.RewritePath.cons (S := rhoGSLT) ⟨step⟩ path) (ih h2)

theorem rhoIntrinsicLedgerTotalAction_publicSpentSyntax_no_leak_reducesN_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
              rhoSpentSyntaxWidth
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h1))) +
              rhoSpentSyntaxWidth
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h2))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
              rhoSpentSyntaxTicks
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h1))) +
              rhoSpentSyntaxTicks
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h2))) := by
  rw [rhoRewritePathOfReducesN_concat]
  exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_no_leak_rewritePathAppend
    (rhoRewritePathOfReducesN h1)
    (rhoRewritePathOfReducesN h2)

theorem rhoIntrinsicLedgerPublicSpentSyntax_semantics_reducesN_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
              rhoSpentSyntaxWidth
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h1))) +
              rhoSpentSyntaxWidth
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h2))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
              rhoSpentSyntaxTicks
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h1))) +
              rhoSpentSyntaxTicks
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rhoRewritePathOfReducesN h2))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
              n + m ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) := by
  rcases rhoIntrinsicLedgerTotalAction_publicSpentSyntax_no_leak_reducesN_concat h1 h2 with
    ⟨hacc, hwidth, hticks⟩
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics_reducesN (reducesN_concat h1 h2) with
    ⟨_, _, _, hticksLen, hcoh⟩
  constructor
  · exact hacc
  · constructor
    · exact hwidth
    · constructor
      · exact hticks
      · constructor
        · exact hticksLen
        · exact hcoh

theorem rhoIntrinsicDirectSpentTrace_no_leak_reducesN_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h1)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h2)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
            rhoSpentSyntaxWidth
              (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h1)).toPattern +
            rhoSpentSyntaxWidth
              (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h2)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
            rhoSpentSyntaxTicks
              (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h1)).toPattern +
            rhoSpentSyntaxTicks
              (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h2)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger) := by
  rw [rhoRewritePathOfReducesN_concat]
  exact rhoIntrinsicDirectSpentTrace_no_leak_rewritePathAppend
    (rhoRewritePathOfReducesN h1)
    (rhoRewritePathOfReducesN h2)

theorem rhoIntrinsicDirectSpentTrace_semantics_reducesN_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger =
          totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPublicPattern =
          rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
            rhoSpentSyntaxAccount
              (rhoIntrinsicDirectSpentTrace
                (rhoRewritePathOfReducesN h1)).toPattern +
            rhoSpentSyntaxAccount
              (rhoIntrinsicDirectSpentTrace
                (rhoRewritePathOfReducesN h2)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
            rhoSpentSyntaxWidth
              (rhoIntrinsicDirectSpentTrace
                (rhoRewritePathOfReducesN h1)).toPattern +
            rhoSpentSyntaxWidth
              (rhoIntrinsicDirectSpentTrace
                (rhoRewritePathOfReducesN h2)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
            rhoSpentSyntaxTicks
              (rhoIntrinsicDirectSpentTrace
                (rhoRewritePathOfReducesN h1)).toPattern +
            rhoSpentSyntaxTicks
              (rhoIntrinsicDirectSpentTrace
                (rhoRewritePathOfReducesN h2)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
            n + m := by
  rcases rhoIntrinsicDirectSpentTrace_semantics_reducesN (reducesN_concat h1 h2) with
    ⟨hsurf, hledger, hpublic, hcoh, _, _, _, _, _, _, hticksLen⟩
  rcases rhoIntrinsicDirectSpentTrace_no_leak_reducesN_concat h1 h2 with
    ⟨hacc, hwidth, hticks, _⟩
  constructor
  · exact hsurf
  · constructor
    · exact hledger
    · constructor
      · exact hpublic
      · constructor
        · exact hcoh
        · constructor
          · exact hacc
          · constructor
            · exact hwidth
            · constructor
              · exact hticks
              · exact hticksLen

noncomputable def rhoIntrinsicReducesNTrace
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    QuantumTrace rhoGSLT Nat 2 :=
  rhoIntrinsicRewritePathTrace (rhoRewritePathOfReducesN h)

theorem rhoIntrinsicReducesNTraceAccount_eq_totalCost
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicReducesNTrace h) =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) := by
  exact rhoIntrinsicRewritePathTraceAccount_eq_totalCost
    (rhoRewritePathOfReducesN h)

theorem rhoIntrinsicLedgerTotalAction_shadow_eq_traceAccount_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) =
        traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
          (rhoIntrinsicReducesNTrace h) := by
  exact rhoIntrinsicLedgerTotalAction_shadow_eq_traceAccount
    (rhoRewritePathOfReducesN h)

theorem rhoIntrinsicTraceAccountBridge_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicReducesNTrace h) =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) =
        traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
          (rhoIntrinsicReducesNTrace h) := by
  constructor
  · exact rhoIntrinsicReducesNTraceAccount_eq_totalCost h
  · constructor
    · exact rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost
        (rhoRewritePathOfReducesN h)
    · exact rhoIntrinsicLedgerTotalAction_shadow_eq_traceAccount_reducesN h

theorem rhoIntrinsicSemanticBridge_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicReducesNTrace h) =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)).spatial.card ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
          (rhoRewritePathOfReducesN h).length ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 0 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
          totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 1 ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) =
        traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
          (rhoIntrinsicReducesNTrace h) ∧
    (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toLedger =
      totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h) ∧
    (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 0 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) 1 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
        (rhoRewritePathOfReducesN h).length := by
  rcases rhoIntrinsicTraceAccountBridge_reducesN h with
    ⟨htrace, hshadowCost, hshadowTrace⟩
  have hPublicAcc :
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            totalCost rhoIntrinsicCostMap (rhoRewritePathOfReducesN h) := by
    exact (rhoIntrinsicLedgerPublicSpentSyntax_semantics_reducesN h).1
  have hPublicWidthSpatial :
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h)).spatial.card := by
    exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_spatialCard
      (rhoRewritePathOfReducesN h)
  have hPublicTicksLen :
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction (rhoRewritePathOfReducesN h))) =
            (rhoRewritePathOfReducesN h).length := by
    exact rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_length
      (rhoRewritePathOfReducesN h)
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics_reducesN h with
    ⟨_, hPublicWidthCost, hPublicTicksCost, _, _⟩
  rcases rhoIntrinsicDirectSpentTrace_semantics_reducesN h with
    ⟨hSurf, hLedger, hPublicPattern, hCoherent, hDirectAccPublic, hDirectAccCost,
      hDirectWidthPublic, hDirectWidthCost, hDirectTicksPublic, hDirectTicksCost, _⟩
  have hDirectTicksLen :
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace (rhoRewritePathOfReducesN h)).toPattern =
          (rhoRewritePathOfReducesN h).length := by
    exact rhoIntrinsicDirectSpentTrace_ticks_eq_length (rhoRewritePathOfReducesN h)
  constructor
  · exact htrace
  · constructor
    · exact hshadowCost
    · constructor
      · exact hPublicAcc
      · constructor
        · exact hPublicWidthSpatial
        · constructor
          · exact hPublicTicksLen
          · constructor
            · exact hPublicWidthCost
            · constructor
              · exact hPublicTicksCost
              · constructor
                · exact hshadowTrace
                · constructor
                  · exact hSurf
                  · constructor
                    · exact hLedger
                    · constructor
                      · exact hPublicPattern
                      · constructor
                        · exact hCoherent
                        · constructor
                          · exact hDirectAccPublic
                          · constructor
                            · exact hDirectAccCost
                            · constructor
                              · exact hDirectWidthPublic
                              · constructor
                                · exact hDirectWidthCost
                                · constructor
                                  · exact hDirectTicksPublic
                                  · constructor
                                    · exact hDirectTicksCost
                                    · exact hDirectTicksLen

theorem rhoIntrinsicSemanticBridge_reducesN_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicReducesNTrace (reducesN_concat h1 h2)) =
        totalCost rhoIntrinsicCostMap
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) =
          totalCost rhoIntrinsicCostMap
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) =
          traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
            (rhoIntrinsicReducesNTrace (reducesN_concat h1 h2)) ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            n + m ∧
    RhoLedger.TraceCoherent
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger =
        totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h1)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h2)).toPattern ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h1)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h2)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h1)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h2)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          n + m := by
  rcases rhoIntrinsicSemanticBridge_reducesN (reducesN_concat h1 h2) with
    ⟨htrace, hshadowCost, _, _, _, _, _, hshadowTrace, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics_reducesN_concat h1 h2 with
    ⟨hPublicAcc, hPublicWidth, hPublicTicks, hPublicLen, hPublicCoh⟩
  rcases rhoIntrinsicDirectSpentTrace_semantics_reducesN_concat h1 h2 with
    ⟨hSurf, hLedger, hPublicPattern, hCoherent, hDirectAcc, hDirectWidth, hDirectTicks,
      hDirectLen⟩
  constructor
  · exact htrace
  · constructor
    · exact hshadowCost
    · constructor
      · exact hshadowTrace
      · constructor
        · exact hPublicAcc
        · constructor
          · exact hPublicWidth
          · constructor
            · exact hPublicTicks
            · constructor
              · exact hPublicLen
              · constructor
                · exact hPublicCoh
                · constructor
                  · exact hSurf
                  · constructor
                    · exact hLedger
                    · constructor
                      · exact hPublicPattern
                      · constructor
                        · exact hCoherent
                        · constructor
                          · exact hDirectAcc
                          · constructor
                            · exact hDirectWidth
                            · constructor
                              · exact hDirectTicks
                              · exact hDirectLen

theorem rhoIntrinsicSemanticBridge_reducesN_full_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    (traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicReducesNTrace (reducesN_concat h1 h2)) =
        totalCost rhoIntrinsicCostMap
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) =
          totalCost rhoIntrinsicCostMap
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            (totalAction rhoIntrinsicLedgerAction
              (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).spatial.card ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)).length ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) 0 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) 1 ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) =
          traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
            (rhoIntrinsicReducesNTrace (reducesN_concat h1 h2)) ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger =
        totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          totalCost rhoIntrinsicCostMap
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          totalCost rhoIntrinsicCostMap
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) 0 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          totalCost rhoIntrinsicCostMap
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) 1 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)).length) ∧
    (traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (rhoIntrinsicReducesNTrace (reducesN_concat h1 h2)) =
        totalCost rhoIntrinsicCostMap
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) =
          totalCost rhoIntrinsicCostMap
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) =
          traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
            (rhoIntrinsicReducesNTrace (reducesN_concat h1 h2)) ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h1))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN h2))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)))) =
            n + m ∧
    RhoLedger.TraceCoherent
      (totalAction rhoIntrinsicLedgerAction
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger =
        totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN (reducesN_concat h1 h2))) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h1)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h2)).toPattern ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h1)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h2)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h1)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (rhoRewritePathOfReducesN h2)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).toPattern =
          n + m) := by
  exact ⟨rhoIntrinsicSemanticBridge_reducesN (reducesN_concat h1 h2),
    rhoIntrinsicSemanticBridge_reducesN_concat h1 h2⟩

theorem rhoIntrinsicTemporalSemanticBridge_rewritePathAppend_steps
    {t u v : Pattern}
    (left : rhoGSLT.Step t u)
    (right : rhoGSLT.Step u v) :
    let path :=
      rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)
    (totalAction rhoIntrinsicLedgerAction path).temporalList.length =
        path.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          path.length ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        path.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) = 2 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        (rhoIntrinsicRewritePathTrace path) 1 = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        (rhoIntrinsicRewritePathTrace path) 1 = path.length := by
  dsimp
  rcases rhoIntrinsicTemporalSemanticBridge
      (rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)) with
    ⟨htemporal, hpublicTicksLen, hdirectTicksLen, htraceTicksLen⟩
  have hLenTwo :
      (rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)).length = 2 := by
    simp [rewritePathAppend, oneStepPath, GSLT.RewritePath.length]
  constructor
  · exact htemporal
  · constructor
    · exact hpublicTicksLen
    · constructor
      · exact hdirectTicksLen
      · constructor
        · calc
            rhoSpentSyntaxTicks
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (rewritePathAppend
                      (oneStepPath (S := rhoGSLT) left)
                      (oneStepPath (S := rhoGSLT) right)))) =
                (rewritePathAppend
                  (oneStepPath (S := rhoGSLT) left)
                  (oneStepPath (S := rhoGSLT) right)).length := by
                    exact hpublicTicksLen
            _ = 2 := hLenTwo
        · constructor
          · calc
              rhoSpentSyntaxTicks
                  (rhoIntrinsicDirectSpentTrace
                    (rewritePathAppend
                      (oneStepPath (S := rhoGSLT) left)
                      (oneStepPath (S := rhoGSLT) right))).toPattern =
                  (rewritePathAppend
                    (oneStepPath (S := rhoGSLT) left)
                    (oneStepPath (S := rhoGSLT) right)).length := by
                      exact hdirectTicksLen
              _ = 2 := hLenTwo
          · constructor
            · calc
                traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
                    (rhoIntrinsicRewritePathTrace
                      (rewritePathAppend
                          (oneStepPath (S := rhoGSLT) left)
                          (oneStepPath (S := rhoGSLT) right))) 1 =
                      (rewritePathAppend
                    (oneStepPath (S := rhoGSLT) left)
                    (oneStepPath (S := rhoGSLT) right)).length := by
                      exact htraceTicksLen
                _ = 2 := hLenTwo
            · exact htraceTicksLen

theorem rhoIntrinsicSemanticBridge_rewritePathAppend_steps_full
    {t u v : Pattern}
    (left : rhoGSLT.Step t u)
    (right : rhoGSLT.Step u v) :
    (let path :=
      rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)
    let stack := rhoIntrinsicDirectSpentStack path
    stack.toLedger = totalAction rhoIntrinsicLedgerAction path ∧
      rhoLedgerShadow stack.toLedger = totalCost rhoIntrinsicCostMap path ∧
      stack.depth = path.length ∧
      rhoSpentSyntaxAccount stack.toPattern = totalCost rhoIntrinsicCostMap path ∧
      rhoSpentSyntaxTicks stack.toPattern = path.length ∧
      stack =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) left))
          (rhoIntrinsicDirectSpentStack (oneStepPath (S := rhoGSLT) right)) ∧
      stack =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent left)
          (rhoIntrinsicDirectStepSpent right) ∧
      rhoIntrinsicDirectSpentTrace path =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent left)
          (rhoIntrinsicDirectStepSpent right) ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) left))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) right))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) left))) +
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) right))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) left))) +
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) right))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace path).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) left)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) right)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace path).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) left)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) right)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace path).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) left)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) right)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace path).toLedger)) ∧
    (let path :=
      rewritePathAppend
        (oneStepPath (S := rhoGSLT) left)
        (oneStepPath (S := rhoGSLT) right)
    (totalAction rhoIntrinsicLedgerAction path).temporalList.length =
        path.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) =
          path.length ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern =
        path.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction path)) = 2 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace path).toPattern = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        (rhoIntrinsicRewritePathTrace path) 1 = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        (rhoIntrinsicRewritePathTrace path) 1 = path.length) := by
  constructor
  · exact rhoIntrinsicSemanticBridge_rewritePathAppend_steps left right
  · exact rhoIntrinsicTemporalSemanticBridge_rewritePathAppend_steps left right

end Mettapedia.GSLT.Meredith.RhoExample
