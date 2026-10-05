import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolConcurrency

/-!
# Forward execution and the unary image of tuple lowering

The syntax remains the shared intrinsic signature; `Unary` identifies its
unary subset. The lowering preserves the stated structural equations and
selected actual executions through parallel components and private scopes.
This forward interpretation does not impose an unproved discipline on
arbitrary target contexts or on different source arities sharing one name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

/-- A subset of the shared presentation, containing no binary input or output. -/
inductive Unary : {Γ : Ctx sig} → Proc Γ → Prop where
  | var {Γ : Ctx sig} (name : Var Γ Srt.pr) : Unary (.var name)
  | nil {Γ} : Unary (nil : Proc Γ)
  | par {Γ} {p q : Proc Γ} : Unary p → Unary q → Unary (par p q)
  | inp1 {Γ} (channel : Name Γ) {body : Proc (.nm :: Γ)} :
      Unary body → Unary (inp1 channel body)
  | out1 {Γ} (channel datum : Name Γ) : Unary (out1 channel datum)
  | nu {Γ} {body : Proc (.nm :: Γ)} : Unary body → Unary (nu body)
  | rep {Γ} {body : Proc Γ} : Unary body → Unary (rep body)

theorem Unary.rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    {process : Proc Γ} (unary : Unary process) : Unary (rename ρ process) := by
  induction unary generalizing Δ with
  | var name => exact .var _
  | nil => exact .nil
  | par _ _ firstIH secondIH => exact .par (firstIH ρ) (secondIH ρ)
  | inp1 channel _ ih => exact .inp1 _ (ih (liftRen ρ [.nm]))
  | out1 channel datum => exact .out1 _ _
  | nu _ ih => exact .nu (ih (liftRen ρ [.nm]))
  | rep _ ih => exact .rep (ih ρ)

theorem sendPair_unary {Γ : Ctx sig} (channel first second : Name Γ) :
    Unary (sendPair channel first second) :=
  .nu (.par (.out1 _ _) (.inp1 _ (.par (.out1 _ _) (.out1 _ _))))

theorem receivePair_unary {Γ : Ctx sig} (channel : Name Γ)
    {body : Proc (.nm :: .nm :: Γ)} (unary : Unary body) :
    Unary (receivePair channel body) :=
  .inp1 _ (.nu (.par (.out1 _ _) (.inp1 _ (.inp1 _ (unary.rename receiveBodyRen)))))

/-- The candidate really lands in unary processes for every source term. -/
theorem lower_unary : ∀ {Γ : Ctx sig} (process : Proc Γ), Unary (lower process)
  | _, .var name => by rw [lower]; exact .var _
  | _, .op .nil .nil => by rw [lower]; exact .nil
  | _, .op .par (.cons first (.cons second .nil)) => by
      rw [lower]
      exact .par (lower_unary first) (lower_unary second)
  | _, .op .inp1 (.cons channel (.cons body .nil)) => by
      rw [lower]
      exact .inp1 _ (lower_unary body)
  | _, .op .inp2 (.cons channel (.cons body .nil)) => by
      rw [lower]
      exact receivePair_unary _ (lower_unary body)
  | _, .op .out1 (.cons channel (.cons datum .nil)) => by rw [lower]; exact .out1 _ _
  | _, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      rw [lower]
      exact sendPair_unary _ _ _
  | _, .op .nu (.cons body .nil) => by rw [lower]; exact .nu (lower_unary body)
  | _, .op .rep (.cons body .nil) => by rw [lower]; exact .rep (lower_unary body)
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem lower_weaken {Γ : Ctx sig} (process : Proc Γ) :
    lower (weaken (t := Srt.nm) process) = weaken (t := Srt.nm) (lower process) :=
  (lower_rename (fun _ name => .succ name) process).symm

theorem receivePair_structural {Γ : Ctx sig} (channel : Name Γ)
    {first second : Proc (.nm :: .nm :: Γ)} (equal : StructuralEq first second) :
    StructuralEq (receivePair channel first) (receivePair channel second) :=
  .inp1 _ (.nu (.par (.refl _) (.inp1 _ (.inp1 _ (equal.rename receiveBodyRen)))))

/-- Lowering respects the existing source equations, including scope
extrusion, exchange, and persistent-server unfolding. -/
theorem lower_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : StructuralEq (lower first) (lower second) := by
  induction equal with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ firstIH secondIH => exact .trans firstIH secondIH
  | parComm => simp only [lower_par]; exact .parComm _ _
  | parAssoc => simp only [lower_par]; exact .parAssoc _ _ _
  | parUnit => simp only [lower_par, lower_nil]; exact .parUnit _
  | nuUnused => simp only [lower_nu, lower_weaken]; exact .nuUnused _
  | nuPar => simp only [lower_par, lower_nu, lower_weaken]; exact .nuPar _ _
  | nuSwap =>
      simp only [lower_nu, ← lower_rename]
      exact .nuSwap _
  | repUnfold => simp only [lower_rep, lower_par]; exact .repUnfold _
  | par _ _ firstIH secondIH => simp only [lower_par]; exact .par firstIH secondIH
  | nu _ ih => simp only [lower_nu]; exact .nu ih
  | inp1 channel _ ih => simp only [lower_inp1]; exact .inp1 _ ih
  | inp2 channel _ ih => simp only [lower_inp2]; exact receivePair_structural _ ih
  | rep _ ih => simp only [lower_rep]; exact .rep ih

theorem modulo_add_parallel_right {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) (frame : Proc Γ) :
    StepModulo (par frame source) (par frame target) := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact ⟨_, _, .par (.refl _) before, .parR _ firing, .par (.refl _) after⟩

def rightParallelPath {Γ : Ctx sig} {source target : Proc Γ}
    (path : (operationalTheory Γ).RewritePath source target) (frame : Proc Γ) :
    (operationalTheory Γ).RewritePath (par frame source) (par frame target) :=
  match path with
  | .nil _ => .nil _
  | .cons first rest => .cons (modulo_add_parallel_right first frame) (rightParallelPath rest frame)

theorem rightParallelPath_length : ∀ {Γ : Ctx sig} {source target : Proc Γ}
    (path : (operationalTheory Γ).RewritePath source target) (frame : Proc Γ),
    (rightParallelPath path frame).length = path.length
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons _ rest, frame => by
      simp only [rightParallelPath, Mettapedia.GSLT.GSLT.RewritePath.length]
      rw [rightParallelPath_length rest frame]
termination_by _ _ _ path _ => path.length
decreasing_by simp only [Mettapedia.GSLT.GSLT.RewritePath.length]; omega

theorem modulo_add_private {Γ : Ctx sig} {source target : Proc (.nm :: Γ)}
    (step : StepModulo source target) : StepModulo (nu source) (nu target) := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact ⟨_, _, .nu before, .nu firing, .nu after⟩

def privatePath {Γ : Ctx sig} {source target : Proc (.nm :: Γ)}
    (path : (operationalTheory (.nm :: Γ)).RewritePath source target) :
    (operationalTheory Γ).RewritePath (nu source) (nu target) :=
  match path with
  | .nil _ => .nil _
  | .cons first rest => .cons (modulo_add_private first) (privatePath rest)

theorem privatePath_length : ∀ {Γ : Ctx sig} {source target : Proc (.nm :: Γ)}
    (path : (operationalTheory (.nm :: Γ)).RewritePath source target),
    (privatePath path).length = path.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ rest => by
      simp only [privatePath, Mettapedia.GSLT.GSLT.RewritePath.length]
      rw [privatePath_length rest]
termination_by _ _ _ path => path.length
decreasing_by simp only [Mettapedia.GSLT.GSLT.RewritePath.length]; omega

/-- Every source primitive has a real nonempty target block. A unary
communication has one event; a binary communication has four. Active
parallel/restriction contexts add no communication to that block. -/
theorem step_lower_path {Γ : Ctx sig} {source target : Proc Γ}
    (step : Step source target) :
    ∃ path : (operationalTheory Γ).RewritePath (lower source) (lower target),
      path.length = 1 ∨ path.length = 4 := by
  induction step with
  | comm1 channel datum body =>
      exact ⟨.cons (lower_unary_fires channel datum body) (.nil _), Or.inl rfl⟩
  | comm2 channel first second body =>
      exact ⟨lowerCallPath channel first second body, Or.inr (lowerCallPath_length _ _ _ _)⟩
  | parL frame _ ih =>
      obtain ⟨path, length⟩ := ih
      rw [lower_par, lower_par]
      refine ⟨parallelPath path (lower frame), ?_⟩
      rw [parallelPath_length]
      exact length
  | parR frame _ ih =>
      obtain ⟨path, length⟩ := ih
      rw [lower_par, lower_par]
      refine ⟨rightParallelPath path (lower frame), ?_⟩
      rw [rightParallelPath_length]
      exact length
  | nu _ ih =>
      obtain ⟨path, length⟩ := ih
      rw [lower_nu, lower_nu]
      refine ⟨privatePath path, ?_⟩
      rw [privatePath_length]
      exact length

/-- Changing the representative of the source of a nonempty block changes
its first actual firing, with no new event and no altered endpoint. -/
def pathSourceEquation {Γ : Ctx sig} {source source' target : Proc Γ}
    (equal : StructuralEq source' source)
    (path : (operationalTheory Γ).RewritePath source target) (positive : 0 < path.length) :
    (operationalTheory Γ).RewritePath source' target :=
  match path with
  | .nil _ => False.elim (Nat.lt_irrefl 0 positive)
  | .cons first rest => .cons (modulo_source_equation equal first) rest

theorem pathSourceEquation_length : ∀ {Γ : Ctx sig} {source source' target : Proc Γ}
    (equal : StructuralEq source' source)
    (path : (operationalTheory Γ).RewritePath source target) (positive : 0 < path.length),
    (pathSourceEquation equal path positive).length = path.length
  | _, _, _, _, _, .nil _, positive => False.elim (Nat.lt_irrefl 0 positive)
  | _, _, _, _, _, .cons _ _, _ => rfl

/-- Changing the representative of a supplied nonempty block's endpoint
updates its last actual firing. It neither finds another successful outcome
nor inserts an equation as a paid event. -/
def pathTargetEquation {Γ : Ctx sig} {source target target' : Proc Γ}
    (equal : StructuralEq target target')
    (path : (operationalTheory Γ).RewritePath source target) (positive : 0 < path.length) :
    (operationalTheory Γ).RewritePath source target' :=
  match path with
  | .nil _ => False.elim (Nat.lt_irrefl 0 positive)
  | .cons first (.nil _) => .cons (modulo_target_equation first equal) (.nil _)
  | .cons first (.cons second rest) =>
      .cons first (pathTargetEquation equal (.cons second rest)
        (by simp only [Mettapedia.GSLT.GSLT.RewritePath.length]; omega))

theorem pathTargetEquation_length : ∀ {Γ : Ctx sig} {source target target' : Proc Γ}
    (equal : StructuralEq target target')
    (path : (operationalTheory Γ).RewritePath source target) (positive : 0 < path.length),
    (pathTargetEquation equal path positive).length = path.length
  | _, _, _, _, _, .nil _, positive => False.elim (Nat.lt_irrefl 0 positive)
  | _, _, _, _, _, .cons _ (.nil _), _ => rfl
  | _, _, _, _, equal, .cons first (.cons second tail), positive => by
          simp only [pathTargetEquation, Mettapedia.GSLT.GSLT.RewritePath.length]
          exact congrArg (fun count => 1 + count)
            (pathTargetEquation_length equal (.cons second tail)
              (by simp only [Mettapedia.GSLT.GSLT.RewritePath.length]; omega))
termination_by _ _ _ _ _ path _ => path.length
decreasing_by simp only [Mettapedia.GSLT.GSLT.RewritePath.length]; omega

/-- Each actual source step modulo its equations has a supplied compiled
endpoint and a one-to-four communication block. The existential is in Prop;
selecting a particular Type-valued block requires choice or source evidence. -/
theorem stepModulo_lower_path {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) :
    ∃ path : (operationalTheory Γ).RewritePath (lower source) (lower target),
      path.length = 1 ∨ path.length = 4 := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  obtain ⟨path, length⟩ := step_lower_path firing
  have positive : 0 < path.length := by rcases length with one | four <;> omega
  let withEndpoint := pathTargetEquation (lower_structural after) path positive
  have positiveEndpoint : 0 < withEndpoint.length := by
    rw [pathTargetEquation_length]
    exact positive
  refine ⟨pathSourceEquation (lower_structural before) withEndpoint positiveEndpoint, ?_⟩
  rw [pathSourceEquation_length, pathTargetEquation_length]
  exact length

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
