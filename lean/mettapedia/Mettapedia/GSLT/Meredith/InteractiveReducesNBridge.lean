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
  exact (congrArg (fun cost => cost 1)
    (rhoIntrinsicRewritePathTraceAccount_eq_totalCost path)).trans
    (rhoIntrinsicTotalCost_ticks_eq_length path)

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

/-- Transporting an indexed reduction along any proof of the same index
equality does not change its rewrite path. -/
theorem rhoRewritePathOfReducesN_cast_type_eq
    {n m : Nat} {p q : Pattern} (hEq : n = m)
    (typeEq : ReducesN n p q = ReducesN m p q) (h : ReducesN n p q) :
    rhoRewritePathOfReducesN (cast typeEq h) =
      rhoRewritePathOfReducesN h := by
  let canonicalEq : ReducesN n p q = ReducesN m p q :=
    congrArg (fun k => ReducesN k p q) hEq
  trans rhoRewritePathOfReducesN (cast canonicalEq h)
  · exact rhoRewritePathOfReducesN_cast_type_proof_irrel typeEq canonicalEq h
  · exact rhoRewritePathOfReducesN_cast_congrArg hEq h

theorem rhoRewritePathOfReducesN_concat
    {n m : Nat} {p q r : Pattern} (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    rhoRewritePathOfReducesN (reducesN_concat h1 h2) =
      rewritePathAppend (rhoRewritePathOfReducesN h1) (rhoRewritePathOfReducesN h2) := by
  induction h1 generalizing r with
  | zero p =>
      rw [reducesN_concat_zero]
      rw [rhoRewritePathOfReducesN_cast_type_eq (hEq := (Nat.zero_add m).symm)]
      simp [rewritePathAppend, rhoRewritePathOfReducesN]
  | succ step rest ih =>
      rw [reducesN_concat_succ]
      rw [rhoRewritePathOfReducesN_cast_type_eq
        (hEq := (Nat.add_right_comm _ 1 m).symm)]
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
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2))).CanonicalShape ∧
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

/-- Observations of a typed rho path. The ordered direct trace still carries
its ledger and public presentation, and both presentations read the same
spatial and temporal account. -/
abbrev RhoPathSemantics {p q : Pattern} (path : rhoGSLT.RewritePath p q) : Prop :=
  let trace := rhoIntrinsicRewritePathTrace path
  let ledger := totalAction rhoIntrinsicLedgerAction path
  let publicSpent := rhoLedgerToSpentSyntax ledger
  let direct := rhoIntrinsicDirectSpentTrace path
  let cost := totalCost rhoIntrinsicCostMap path
  traceAccount trace = cost ∧
    rhoLedgerShadow ledger = cost ∧
    rhoSpentSyntaxAccount publicSpent = cost ∧
    rhoSpentSyntaxWidth publicSpent = ledger.spatial.card ∧
    rhoSpentSyntaxTicks publicSpent = path.length ∧
    rhoSpentSyntaxWidth publicSpent = cost 0 ∧
    rhoSpentSyntaxTicks publicSpent = cost 1 ∧
    rhoLedgerShadow ledger = traceAccount trace ∧
    direct.CanonicalShape ∧
    direct.toLedger = ledger ∧
    direct.toPublicPattern = publicSpent ∧
    RhoLedger.TraceCoherent direct.toLedger ∧
    rhoSpentSyntaxAccount direct.toPattern = rhoSpentSyntaxAccount publicSpent ∧
    rhoSpentSyntaxAccount direct.toPattern = cost ∧
    rhoSpentSyntaxWidth direct.toPattern = rhoSpentSyntaxWidth publicSpent ∧
    rhoSpentSyntaxWidth direct.toPattern = cost 0 ∧
    rhoSpentSyntaxTicks direct.toPattern = rhoSpentSyntaxTicks publicSpent ∧
    rhoSpentSyntaxTicks direct.toPattern = cost 1 ∧
    rhoSpentSyntaxTicks direct.toPattern = path.length

theorem rhoIntrinsicPathSemantics {p q : Pattern} (path : rhoGSLT.RewritePath p q) :
    RhoPathSemantics path :=
  ⟨rhoIntrinsicRewritePathTraceAccount_eq_totalCost path,
    rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost path,
    rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost path,
    rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_spatialCard path,
    rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_length path,
    rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_totalCost_zero path,
    rhoIntrinsicLedgerTotalAction_publicSpentSyntax_ticks_eq_totalCost_one path,
    rhoIntrinsicLedgerTotalAction_shadow_eq_traceAccount path,
    rhoIntrinsicDirectSpentTrace_semantics path⟩

theorem rhoIntrinsicSemanticBridge_reducesN
    {n : Nat} {p q : Pattern} (h : ReducesN n p q) :
    RhoPathSemantics (rhoRewritePathOfReducesN h) :=
  rhoIntrinsicPathSemantics (rhoRewritePathOfReducesN h)

/-- Observations of an ordered composition. The component and composed paths
stay typed by their endpoints. The presentations preserve their readouts under
addition, and the composed direct trace still identifies its ledger. -/
abbrev RhoPathConcatSemantics {p q r : Pattern}
    (left : rhoGSLT.RewritePath p q) (right : rhoGSLT.RewritePath q r)
    (joined : rhoGSLT.RewritePath p r) (ticks : Nat) : Prop :=
  let trace := rhoIntrinsicRewritePathTrace joined
  let ledger := totalAction rhoIntrinsicLedgerAction joined
  let cost := totalCost rhoIntrinsicCostMap joined
  let publicSpent := rhoLedgerToSpentSyntax ledger
  let publicLeft := rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction left)
  let publicRight := rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction right)
  let direct := rhoIntrinsicDirectSpentTrace joined
  let directLeft := (rhoIntrinsicDirectSpentTrace left).toPattern
  let directRight := (rhoIntrinsicDirectSpentTrace right).toPattern
  traceAccount trace = cost ∧
    rhoLedgerShadow ledger = cost ∧
    rhoLedgerShadow ledger = traceAccount trace ∧
    rhoSpentSyntaxAccount publicSpent = rhoSpentSyntaxAccount publicLeft +
      rhoSpentSyntaxAccount publicRight ∧
    rhoSpentSyntaxWidth publicSpent = rhoSpentSyntaxWidth publicLeft +
      rhoSpentSyntaxWidth publicRight ∧
    rhoSpentSyntaxTicks publicSpent = rhoSpentSyntaxTicks publicLeft +
      rhoSpentSyntaxTicks publicRight ∧
    rhoSpentSyntaxTicks publicSpent = ticks ∧
    RhoLedger.TraceCoherent ledger ∧
    direct.CanonicalShape ∧
    direct.toLedger = ledger ∧
    direct.toPublicPattern = publicSpent ∧
    RhoLedger.TraceCoherent direct.toLedger ∧
    rhoSpentSyntaxAccount direct.toPattern = rhoSpentSyntaxAccount directLeft +
      rhoSpentSyntaxAccount directRight ∧
    rhoSpentSyntaxWidth direct.toPattern = rhoSpentSyntaxWidth directLeft +
      rhoSpentSyntaxWidth directRight ∧
    rhoSpentSyntaxTicks direct.toPattern = rhoSpentSyntaxTicks directLeft +
      rhoSpentSyntaxTicks directRight ∧
    rhoSpentSyntaxTicks direct.toPattern = ticks

theorem rhoIntrinsicPathConcatSemantics {p q r : Pattern}
    (left : rhoGSLT.RewritePath p q) (right : rhoGSLT.RewritePath q r) :
    RhoPathConcatSemantics left right (rewritePathAppend left right)
      (rewritePathAppend left right).length := by
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics_rewritePathAppend left right with
    ⟨account, width, ticks, length, coherent⟩
  exact ⟨rhoIntrinsicRewritePathTraceAccount_eq_totalCost _,
    rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost _,
    rhoIntrinsicLedgerTotalAction_shadow_eq_traceAccount _, account, width, ticks, length,
    coherent, rhoIntrinsicDirectSpentTrace_semantics_rewritePathAppend left right⟩

theorem rhoIntrinsicSemanticBridge_reducesN_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    RhoPathConcatSemantics (rhoRewritePathOfReducesN h1) (rhoRewritePathOfReducesN h2)
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) (n + m) := by
  have joined := rhoIntrinsicPathConcatSemantics (rhoRewritePathOfReducesN h1)
    (rhoRewritePathOfReducesN h2)
  rw [← rhoRewritePathOfReducesN_concat h1 h2] at joined
  simpa only [rhoRewritePathOfReducesN_length] using joined

theorem rhoIntrinsicSemanticBridge_reducesN_full_concat
    {n m : Nat} {p q r : Pattern}
    (h1 : ReducesN n p q) (h2 : ReducesN m q r) :
    RhoPathSemantics (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) ∧
    RhoPathConcatSemantics (rhoRewritePathOfReducesN h1) (rhoRewritePathOfReducesN h2)
      (rhoRewritePathOfReducesN (reducesN_concat h1 h2)) (n + m) :=
  ⟨rhoIntrinsicSemanticBridge_reducesN (reducesN_concat h1 h2),
    rhoIntrinsicSemanticBridge_reducesN_concat h1 h2⟩

/-- The ordered ledger, public syntax, direct syntax, and trace all record
exactly one temporal entry for each of the two reductions. -/
abbrev RhoTwoStepTemporalSemantics {p q r : Pattern}
    (left : rhoGSLT.Step p q) (right : rhoGSLT.Step q r) : Prop :=
  let path := rewritePathAppend (oneStepPath (S := rhoGSLT) left)
    (oneStepPath (S := rhoGSLT) right)
  let ledger := totalAction rhoIntrinsicLedgerAction path
  let publicSpent := rhoLedgerToSpentSyntax ledger
  let directSpent := (rhoIntrinsicDirectSpentTrace path).toPattern
  let trace := rhoIntrinsicRewritePathTrace path
  ledger.temporalList.length = path.length ∧
    rhoSpentSyntaxTicks publicSpent = path.length ∧
    rhoSpentSyntaxTicks directSpent = path.length ∧
    rhoSpentSyntaxTicks publicSpent = 2 ∧
    rhoSpentSyntaxTicks directSpent = 2 ∧
    traceAccount trace 1 = 2 ∧
    traceAccount trace 1 = path.length

theorem rhoIntrinsicTemporalSemanticBridge_rewritePathAppend_steps
    {t u v : Pattern} (left : rhoGSLT.Step t u) (right : rhoGSLT.Step u v) :
    RhoTwoStepTemporalSemantics left right := by
  let path := rewritePathAppend (oneStepPath (S := rhoGSLT) left)
    (oneStepPath (S := rhoGSLT) right)
  obtain ⟨ledger, publicTicks, directTicks, traceTicks⟩ := rhoIntrinsicTemporalSemanticBridge path
  have length : path.length = 2 := rfl
  exact ⟨ledger, publicTicks, directTicks, publicTicks.trans length, directTicks.trans length,
    traceTicks.trans length, traceTicks⟩

theorem rhoIntrinsicSemanticBridge_rewritePathAppend_steps_full
    {t u v : Pattern} (left : rhoGSLT.Step t u) (right : rhoGSLT.Step u v) :
    RhoStepAppendSemantics left right ∧ RhoTwoStepTemporalSemantics left right :=
  ⟨rhoIntrinsicSemanticBridge_rewritePathAppend_steps left right,
    rhoIntrinsicTemporalSemanticBridge_rewritePathAppend_steps left right⟩

end Mettapedia.GSLT.Meredith.RhoExample
