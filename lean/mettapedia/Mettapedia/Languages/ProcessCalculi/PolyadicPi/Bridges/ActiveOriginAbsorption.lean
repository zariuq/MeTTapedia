import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveGuardedBodies
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

/-!
# Observed copies of an existing guarded server

A selected active observation retains its subject and suspended body modulo
the authored equations. On a frontier whose active private scopes are unused,
those observations identify actual copies of the supplied receiver. The
existing server can therefore absorb the copies without changing its own
multiplicity. Unused scopes are strengthened with their exact physical body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginAbsorption

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveOriginErasure ActiveGuardedBodies ScopedActiveFrontier

universe u

/-- The observation equality retains the actual receiver modulo its authored
body equations, rather than identifying receivers only by their subject. -/
theorem input_guard_equal {Label : Type u} {Γ : Ctx sig} {origin : Label}
    {channel otherChannel : Name Γ} {body otherBody : Proc (.nm :: Γ)}
    (same : input1 origin channel body (fun _ name => name) =
      input1 origin otherChannel otherBody (fun _ name => name)) :
    StructuralEq (inp1 channel body) (inp1 otherChannel otherBody) := by
  have names := congrArg (fun observation => observation.header.channel) same
  have sameChannel : channel = otherChannel := by
    cases channel with
    | op operator _ => cases operator
    | var channel =>
      cases otherChannel with
      | op operator _ => cases operator
      | var otherChannel => exact congrArg Term.var names
  subst otherChannel
  have bodies : bodyQ (fun _ name => name) [.nm] body =
      bodyQ (fun _ name => name) [.nm] otherBody :=
    Option.some.inj (congrArg Observation.unaryBody same)
  have identity : liftRen (fun _ name => name : Ren sig Γ Γ) [Srt.nm] =
      (fun _ name => name : Ren sig (Srt.nm :: Γ) (Srt.nm :: Γ)) := by
    funext sort name
    cases name <;> rfl
  have normalized (process : Proc (Srt.nm :: Γ)) :
      bodyQ (fun _ name => name) [Srt.nm] process =
        (Quotient.mk _ process : TermQ equations (Srt.nm :: Γ) Srt.pr) := by
    have terms : rename (liftRen (fun _ name => name : Ren sig Γ Γ) [Srt.nm]) process = process :=
      (congrArg (fun environment : Ren sig (Srt.nm :: Γ) (Srt.nm :: Γ) =>
        rename environment process) identity).trans (rename_id process)
    exact congrArg (fun value : Proc (Srt.nm :: Γ) =>
      (Quotient.mk _ value : TermQ equations (Srt.nm :: Γ) Srt.pr)) terms
  have clean : (Quotient.mk _ body : TermQ equations (Srt.nm :: Γ) Srt.pr) =
      Quotient.mk _ otherBody := (normalized body).symm.trans (bodies.trans (normalized otherBody))
  have bodyEqual : StructuralEq body otherBody := eqClosure_sound (Quotient.exact clean)
  exact .inp1 channel bodyEqual

/-- Reindexing transports the actual copy equation, including the weakened
server used beneath an extruded private scope. -/
theorem absorbable_rename {Label : Type u} (selected : Label → Bool) :
    ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (marked : ActiveMarking.Tree Label)
      (process receiver : Proc Γ),
      Absorbable selected marked process receiver →
        Absorbable selected marked (rename environment process) (rename environment receiver)
  | _, _, _, _, .var _, _, _ => by simp only [rename, Absorbable]
  | _, _, _, _, .op .nil .nil, _, _ => by simp only [rename, renameArgs, Absorbable]
  | _, _, environment, marked, .op .par (.cons first (.cons second .nil)), receiver, copied => by
      cases marked <;> simp only [rename, renameArgs, liftRen, Absorbable] at copied ⊢
      rename_i left right
      exact ⟨absorbable_rename selected environment left first receiver copied.1,
        absorbable_rename selected environment right second receiver copied.2⟩
  | _, _, environment, marked, .op .inp1 (.cons channel (.cons body .nil)), receiver, copied => by
      cases marked <;> simp only [rename, renameArgs, Absorbable] at copied ⊢
      intro active
      exact (copied active).rename environment
  | _, _, environment, marked, .op .inp2 (.cons channel (.cons body .nil)), receiver, copied => by
      cases marked <;> simp only [rename, renameArgs, Absorbable] at copied ⊢
      intro active
      exact (copied active).rename environment
  | _, _, environment, marked, .op .out1 (.cons channel (.cons datum .nil)), receiver, copied => by
      cases marked <;> simp only [rename, renameArgs, Absorbable] at copied ⊢
      intro active
      exact (copied active).rename environment
  | _, _, environment, marked, .op .out2 (.cons channel (.cons first (.cons second .nil))), receiver, copied => by
      cases marked <;> simp only [rename, renameArgs, Absorbable] at copied ⊢
      intro active
      exact (copied active).rename environment
  | _, _, environment, marked, .op .nu (.cons body .nil), receiver, copied => by
      cases marked <;> simp only [rename, renameArgs, Absorbable] at copied ⊢
      rename_i origin inner
      rw [← rename_weaken environment receiver]
      exact absorbable_rename selected (liftRen environment [.nm]) inner body (weaken receiver) copied
  | _, _, _, _, .op .rep (.cons _ .nil), _, _ => by simp only [rename, renameArgs, Absorbable]
termination_by _ _ _ _ process _ _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- A selected observation is the same actual unary receiver, with the body
read in its equation quotient. No condition is imposed on unselected leaves. -/
def CopiesObserved {Label : Type u} {Γ : Ctx sig} (selected : Label → Bool)
    (binderName : Label → Var Γ .nm) (marked : ActiveMarking.Tree Label)
    (process : Proc Γ) (channel : Name Γ) (body : Proc (.nm :: Γ)) : Prop :=
  ∀ observation ∈ observe binderName marked process (fun _ name => name),
    selected observation.header.origin = true →
      observation = input1 observation.header.origin channel body (fun _ name => name)

/-- Temporary unused private scopes cannot disguise a different copy.
Strengthening removes the scope before reading its actual receiver body. -/
theorem absorbable_of_observations {Label : Type u} (selected : Label → Bool) :
    ∀ {Γ : Ctx sig} (binderName : Label → Var Γ .nm) (marked : ActiveMarking.Tree Label)
      (process : Proc Γ) (channel : Name Γ) (body : Proc (.nm :: Γ)),
      Fits marked process → ScopedOpening.Vacuous process →
      CopiesObserved selected binderName marked process channel body →
        Absorbable selected marked process (inp1 channel body)
  | _, _, _, .var _, _, _, _, _, _ => by simp only [Absorbable]
  | _, _, _, .op .nil .nil, _, _, _, _, _ => by simp only [Absorbable]
  | _, binderName, marked, .op .par (.cons first (.cons second .nil)), channel, body, fitted, unused, seen => by
      cases fitted with
      | par firstFits secondFits =>
        simp only [ScopedOpening.Vacuous] at unused
        simp only [Absorbable]
        refine ⟨absorbable_of_observations selected binderName _ first channel body firstFits unused.1 ?_,
          absorbable_of_observations selected binderName _ second channel body secondFits unused.2 ?_⟩
        · intro observation member active
          exact seen observation (by simpa only [observe, Set.mem_union] using Or.inl member) active
        · intro observation member active
          exact seen observation (by simpa only [observe, Set.mem_union] using Or.inr member) active
  | _, binderName, marked, .op .inp1 (.cons actualChannel (.cons actualBody .nil)), channel, body, fitted, _, seen => by
      cases fitted with
      | inp1 origin actualChannel bodyFits =>
        simp only [inp1, Absorbable]
        intro active
        apply input_guard_equal
        exact seen (input1 origin actualChannel actualBody (fun _ name => name))
          (by simp only [observe, Set.mem_singleton_iff]; rfl) active
  | _, binderName, marked, .op .inp2 (.cons actualChannel (.cons actualBody .nil)), channel, body, fitted, _, seen => by
      cases fitted with
      | inp2 origin actualChannel bodyFits =>
        simp only [inp2, Absorbable]
        intro active
        have same := seen (input2 origin actualChannel actualBody (fun _ name => name))
          (by simp only [observe, Set.mem_singleton_iff]; rfl) active
        have impossible := congrArg (fun observation => observation.header.header) same
        cases impossible
  | _, binderName, marked, .op .out1 (.cons actualChannel (.cons datum .nil)), channel, body, fitted, _, seen => by
      cases fitted with
      | out1 origin actualChannel datum =>
        simp only [out1, Absorbable]
        intro active
        have same := seen (output1 origin actualChannel datum (fun _ name => name))
          (by simp only [observe, Set.mem_singleton_iff]; rfl) active
        have impossible := congrArg (fun observation => observation.header.header) same
        cases impossible
  | _, binderName, marked, .op .out2 (.cons actualChannel (.cons first (.cons second .nil))), channel, body, fitted, _, seen => by
      cases fitted with
      | out2 origin actualChannel first second =>
        simp only [out2, Absorbable]
        intro active
        have same := seen (output2 origin actualChannel first second (fun _ name => name))
          (by simp only [observe, Set.mem_singleton_iff]; rfl) active
        have impossible := congrArg (fun observation => observation.header.header) same
        cases impossible
  | Γ, binderName, marked, .op .nu (.cons process .nil), channel, body, fitted, unused, seen => by
      cases fitted with
      | @nu _ origin _ inner insideFits =>
        obtain ⟨original, actualImage, originalUnused, _⟩ :=
          ScopedOpening.vacuous_scope_strengthening (.bind .nil) process unused
        have originalFits := Fits.ofRename (fun _ name => (Var.succ name : Var (.nm :: Γ) _)) original _ (by
          simpa only [Scope.inclusion] using actualImage ▸ insideFits)
        have view : observe binderName inner process (prependRen (binderName origin) (fun _ name => name)) =
            observe binderName inner original (fun _ name => name) := by
          rw [actualImage]
          rw [observe_rename]
          rfl
        have originalSeen : CopiesObserved selected binderName inner original channel body := by
          intro observation member active
          apply seen observation _ active
          simp only [observe]
          exact (congrArg (fun observed => observation ∈ observed) view).mpr member
        have copied := absorbable_of_observations selected binderName inner original channel body
          originalFits originalUnused originalSeen
        simp only [Absorbable]
        rw [actualImage]
        exact absorbable_rename selected (fun _ name => (Var.succ name : Var (.nm :: Γ) _)) _
          original (inp1 channel body) copied
  | _, _, _, .op .rep (.cons _ .nil), _, _, _, _, _ => by simp only [Absorbable]
termination_by _ _ _ process _ _ _ _ _ => termSize process
decreasing_by
  all_goals simp only [termSize, argsSize]
  all_goals first | omega | (rw [actualImage, termSize_rename]; omega)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginAbsorption
