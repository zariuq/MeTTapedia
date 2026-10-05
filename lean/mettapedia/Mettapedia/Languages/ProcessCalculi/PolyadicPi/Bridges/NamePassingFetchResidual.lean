import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchSelected
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure

/-!
# Exact ordinary-fetch residuals, including unrelated persistent declarations

The compiler's active replicated bodies are unary input guards. Source
addresses give each carrier and lookup one occurrence; no carrier origin is
inside a server. Origin-selective erasure therefore recovers the actual
untouched frame of a supplied one-shot fetch even when other listeners share
its channel or are structurally equal to it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchResidual

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingActiveOrigins ActiveMarking ActiveHeaderInvariant
open ActiveOriginErasure ScopedCommunicationInversion

def one (origin : Origin) : Origin → Bool := fun selected => decide (selected = origin)

def pair (input output : Origin) : Origin → Bool :=
  fun selected => decide (selected = input ∨ selected = output)

theorem compiler_singleBodies {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    SingleBodies (compile source environment result) := by
  induction source generalizing Δ with
  | var => simp only [compile, out1, SingleBodies]
  | lam => simp only [compile, inp2, SingleBodies]
  | app function argument ih =>
      simp only [compile, nu, par, out2, SingleBodies, and_true]
      exact ih _ _
  | defn value body valueIH bodyIH =>
      simp only [compile, nu, par, rep, inp1, SingleBodies, NoActiveRep, width, and_true]
      exact bodyIH _ _
  | carrier name value body valueIH bodyIH =>
      simp only [compile, par, inp1, SingleBodies, and_true]
      exact bodyIH _ _

private theorem deeper_different (origin : Origin) (address : List Edge)
    (deeper : origin.address.length < address.length) (kind : Kind) :
    Origin.mk kind address ≠ origin := by
  intro equal
  have lengths := congrArg (fun selected : Origin => selected.address.length) equal
  simp only at lengths
  omega

theorem count_deeper {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (origin : Origin) (deeper : origin.address.length < address.length) :
    originCount (one origin) (mark source address) = 0 := by
  induction source generalizing address with
  | var => simp only [mark, originCount, one]; simp [deeper_different origin address deeper]
  | lam => simp only [mark, originCount, one]; simp [deeper_different origin address deeper]
  | app function argument ih =>
      simp only [mark, originCount]
      rw [ih (.function :: address) (by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper)]
      simp [one, deeper_different origin address deeper]
  | defn value body valueIH bodyIH =>
      simp only [mark, originCount]
      rw [bodyIH (.definitionBody :: address) (by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper)]
      simp [one, deeper_different origin address deeper]
  | carrier name value body valueIH bodyIH =>
      simp only [mark, originCount]
      rw [bodyIH (.carrierBody :: address) (by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper)]
      simp [one, deeper_different origin address deeper]

theorem origin_unique {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (origin : Origin) : originCount (one origin) (mark source address) ≤ 1 := by
  induction source generalizing address with
  | var =>
      by_cases same : Origin.mk .lookup address = origin <;> simp [mark, originCount, one, same]
  | lam =>
      by_cases same : Origin.mk .lambda address = origin <;> simp [mark, originCount, one, same]
  | app function argument ih =>
      by_cases same : Origin.mk .application address = origin
      · simp only [mark, originCount]
        rw [count_deeper function (.function :: address) origin (by
          rw [← same]
          simp only [List.length_cons]
          omega)]
        simp [one, same]
      · simpa only [mark, originCount, one, same, decide_false, Bool.false_eq_true, ite_false,
          Nat.add_zero] using ih (.function :: address)
  | defn value body valueIH bodyIH =>
      by_cases same : Origin.mk .definition address = origin
      · simp only [mark, originCount]
        rw [count_deeper body (.definitionBody :: address) origin (by
          rw [← same]
          simp only [List.length_cons]
          omega)]
        simp [one, same]
      · simpa only [mark, originCount, one, same, decide_false, Bool.false_eq_true, ite_false,
          Nat.add_zero] using bodyIH (.definitionBody :: address)
  | carrier name value body valueIH bodyIH =>
      by_cases same : Origin.mk .carrier address = origin
      · simp only [mark, originCount]
        rw [count_deeper body (.carrierBody :: address) origin (by
          rw [← same]
          simp only [List.length_cons]
          omega)]
        simp [one, same]
      · simpa only [mark, originCount, one, same, decide_false, Bool.false_eq_true, ite_false,
          Nat.add_zero] using bodyIH (.carrierBody :: address)

theorem selected_positive {header : Header} {origin : Origin} {marked : ActiveMarking.Tree Origin}
    (selected : Selection header origin marked) : 1 ≤ originCount (one origin) marked := by
  induction selected with
  | inp1 | inp2 | out1 | out2 => simp [originCount, one]
  | left _ _ ih => simp only [originCount]; omega
  | right _ _ ih => simp only [originCount]; omega
  | nu _ _ ih | rep _ ih => exact ih

theorem pair_count (input output : Origin) (different : input ≠ output)
    (marked : ActiveMarking.Tree Origin) :
    originCount (pair input output) marked =
      originCount (one input) marked + originCount (one output) marked := by
  induction marked with
  | var | nil => rfl
  | par left right leftIH rightIH => simp only [originCount, leftIH, rightIH]; omega
  | inp1 origin | inp2 origin | out1 origin | out2 origin =>
      simp only [originCount, pair, one]
      by_cases first : origin = input
      · subst origin
        simp [different]
      · by_cases second : origin = output <;> simp [first, second, Ne.symm different]
  | nu _ _ ih | rep _ ih => exact ih

theorem ordinary_repFree {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (input output : Origin) (carrier : input.kind = .carrier) (lookup : output.kind = .lookup) :
    RepFree (pair input output) (mark source address) := by
  have notDefinition : ∀ location, Origin.mk .definition location ≠ input ∧
      Origin.mk .definition location ≠ output := by
    intro location
    constructor
    · intro equal
      have impossible := congrArg Origin.kind equal
      rw [carrier] at impossible
      cases impossible
    · intro equal
      have impossible := congrArg Origin.kind equal
      rw [lookup] at impossible
      cases impossible
  induction source generalizing address with
  | var | lam => trivial
  | app function argument ih => exact ⟨ih (.function :: address), trivial⟩
  | defn value body valueIH bodyIH =>
      refine ⟨bodyIH (.definitionBody :: address), ?_⟩
      simp only [RepFree, originCount, pair]
      simp [(notDefinition address).1, (notDefinition address).2]
  | carrier name value body valueIH bodyIH => exact ⟨bodyIH (.carrierBody :: address), trivial⟩

/-- Selected one-shot and lookup origins determine the exact supplied
residual. This allows shared channels and unrelated replicated servers. -/
theorem ordinary_frame {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {target : Proc Δ}
    (actual : Exposure (compile source environment result) target)
    (traced : TracedExposure (mark source []) actual)
    (carrier : traced.continuation.inputOrigin.kind = .carrier)
    (lookup : traced.continuation.outputOrigin.kind = .lookup) :
    StructuralEq
      (erase (pair traced.continuation.inputOrigin traced.continuation.outputOrigin)
        (mark source []) (compile source environment result)) (actual.scope.close actual.frame) := by
  let input := traced.continuation.inputOrigin
  let output := traced.continuation.outputOrigin
  have different : input ≠ output := by
    intro same
    have impossible := congrArg Origin.kind same
    rw [carrier, lookup] at impossible
    cases impossible
  have inputOne : originCount (one input) (mark source []) = 1 := by
    have lower := selected_positive traced.originalInput
    have upper := origin_unique source [] input
    change originCount (one input) (mark source []) ≥ 1 at lower
    omega
  have outputOne : originCount (one output) (mark source []) = 1 := by
    have lower := selected_positive traced.originalOutput
    have upper := origin_unique source [] output
    change originCount (one output) (mark source []) ≥ 1 at lower
    omega
  have two : originCount (pair input output) (mark source []) = 2 := by
    rw [pair_count input output different, inputOne, outputOne]
  exact (ordinary_exposure_residual (pair input output) (mark_fits source [] environment result)
    (compiler_singleBodies source environment result) traced
    (ordinary_repFree source [] input output carrier lookup) two
    (by simp [pair, input]) (by simp [pair, output])).2

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchResidual
