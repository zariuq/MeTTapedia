import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.AccessibleRecursionProp
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Confluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Divergence

/-!
# Controls for the accessibility package over the tower

For the package of `Instances.AccessibleRecursionProp` (the tower with the
identity eliminator `J` at `U₀`, the codes over `prop`, motives in `U₀`):

**Transport along the unfolding** (`transport_control`). In the guarded
package, from `h : holds (Q (rec P R F a q))`, transport along
`unfold P R F a q` proves `holds (Q (F a (λ y r. rec P R F y (inv R a q y r))))`.

**Church–Rosser** (`churchRosser`). The package's computation, linear `J` at
reflexivity and the decoders, is a definition by constructor patterns, so its
conversion is Church–Rosser; the recursor and its unfolding add no equation.

**Separation** (`control_not_conv`, `hypothesis_not_conv_goal`). In the
transport control's context, conversion does not identify `rec P R F a q` with
its unfolding, nor the hypothesis's type with the goal: only the propositional
unfolding, used as the path of the transport, takes one to the other. They are
propositionally equal (`control_equal`), and in the strong variant they are
convertible in one step (`strong_identifies`).

**Divergence** (`loop_typed`, `loop_no_normal_form`, `loop_incomplete`). The
loop `rec P R (λ x z. z x (ρ x)) a q` over a reflexive relation is typed in the
strong variant and has no normal form. The weak-head checker with the
package's own root steps (`strongOracle`) is incomplete at every budget on it,
while the same checker without the unfolding (`inertOracle`) establishes its
weak-head normal form at budget one (`loop_established`). In the propositional
variant the loop is not convertible to its unfolding (`loop_inert_not_conv`); in
the strong variant it is, in one step (`loop_strong_conv`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
namespace PropInstance

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization
open Presentation.ConversionCoherence (ChurchRosser)
open Presentation.ConstructorSystem (ConstructorPresentation spineHead)
open Mettapedia.TypeTheory.AuthorityTheory (Outcome)
open Mettapedia.TypeTheory.UniverseLevel

/-! ## Transport along the unfolding -/

theorem rules_constantType_j : signature.rules.constantType jN = some (elimType U0 U0) := rfl

/-- The identity eliminator of the guarded package. -/
theorem eliminator : Eliminator signature.rules jN U0 U0 where
  declared := rules_constantType_j
  formed := by
    obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
    refine ⟨w, hw, Normalization.Derivable.mono ?_ typed⟩
    exact
      { headTyping := id
        isUniverse := id
        join := id
        cumulative := id
        headEq := id
        constantType := fun declared => nomatch declared
        computation := fun step => step.elim }
  carrier_universe := .sort _
  motive_universe := .sort _
  above := ⟨U1, .sort _, .sort _, .sort (.max Tower.zero (.succ Tower.zero)), .sorts _ _,
    fun _ => by simp [LevelExpr.eval, LevelTower.zero]⟩

/-- **Transport along the unfolding proves the goal about the unfolded call.** -/
theorem transport_control :
    Typed signature.rules signature.transportContext (signature.transportProof jN)
      signature.transportGoal :=
  signature.transport_goal laws eliminator

/-- The two calls are propositionally equal: `unfold P R F a q` is a path between
them. -/
theorem control_equal :
    Typed signature.rules signature.transportContext
      (signature.unfoldSpine (.var 6) (.var 5) (.var 4) (.var 3) (.var 2))
      (.id (.app (.var 6) (.var 3)) signature.controlCall signature.controlUnfolding) := by
  have U : signature.Universes signature.accBase := laws.universes.mono laws.base_accBase
  obtain ⟨hP, hR, hF, ha, hq, -, -⟩ := signature.transportContext_vars (B := signature.accBase)
  exact U.unfold_apply (Signature.rules_constantType_recursor laws)
    (Signature.rules_constantType_unfold laws) hP hR hF ha hq

/-! ## Church–Rosser -/

theorem computesJ {n : Nat} {l r : Tm Tower.Head n} :
    signature.base.computation.step l r ↔ Confluence.JStep jN l r := Iff.rfl

theorem names : Confluence.Names jN codes where
  j_ne_holds := by decide
  imp_ne_j := by decide
  imp_ne_holds := by decide
  all_ne := fun {a A} found => by
    rcases codes_quantifiers found with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨by decide, by decide⟩
  eq_ne := fun found => by cases found

theorem headEq_symmetric : Std.Symm signature.base.headEq := by
  constructor
  intro left right equality
  change Tower.HeadEq left right at equality
  change Tower.HeadEq right left
  cases left <;> cases right <;> simp only [LevelTower.HeadEq] at equality ⊢
  intro valuation
  exact (equality valuation).symm

/-- The package as a definition by constructor patterns. -/
def presentation : ConstructorPresentation signature.rules :=
  signature.presentation computesJ names headEq_symmetric

/-- **The conversion of the accessibility package is Church–Rosser.** -/
theorem churchRosser : ChurchRosser signature.rules := presentation.churchRosser

/-- The base with the codes, the candidate before the extension, is Church–Rosser
too: its computation is the same. -/
theorem churchRosser_base : ChurchRosser signature.baseRules := fun conversion =>
  churchRosser conversion

theorem recursor_not_defined : ¬ presentation.system.defined recN :=
  show ¬ Confluence.Defined jN codes recN from
    Confluence.not_defined_of_ne (J := jN) (K := codes) (by decide) (by decide)

/-! ## Separation -/

/-- **Conversion does not identify the recursor with its unfolding** at a
variable step function. -/
theorem separation {n : Nat} (P R a q : Tm Tower.Head n) (i : Fin n) :
    ¬ Conv signature.rules.headEq (signature.recSpine P R (.var i) a q)
      (signature.unfolding P R (.var i) a q) signature.rules.computation :=
  Signature.separation presentation recursor_not_defined P R a q i

/-- **Separation at a constant step function** `λ x g. d`, whose unfolding
computes to the constant `d` in two β-steps. -/
theorem separation_constant_step {d : DeclName} (hdrec : d ≠ recN) (hdj : d ≠ jN)
    (hdholds : d ≠ holdsN) {n : Nat} (P R a q : Tm Tower.Head n) :
    ¬ Conv signature.rules.headEq (signature.recSpine P R (.lam (.lam (.const d))) a q)
      (signature.unfolding P R (.lam (.lam (.const d))) a q) signature.rules.computation :=
  Signature.separation_of_reduct presentation recursor_not_defined
    (show ¬ Confluence.Defined jN codes d from Confluence.not_defined_of_ne hdj hdholds)
    (Ne.symm hdrec)
    (.tail (.tail .refl (.congAppFun (.betaPi _ _))) (.betaPi _ _)) rfl

/-- **With the constant step, too, conversion cannot replace the unfolding**:
for a variable predicate `Q`, `holds (Q (rec P R (λ x g. d) a q))` is not
convertible to `holds (Q d)`, the statement about the unfolded call. -/
theorem hypothesis_not_conv_goal_constant_step {d : DeclName} (hdrec : d ≠ recN) (hdj : d ≠ jN)
    (hdholds : d ≠ holdsN) {n : Nat} (P R a q : Tm Tower.Head n) (j : Fin n) :
    ¬ Conv signature.rules.headEq
      (codes.holdsOf (.app (.var j) (signature.recSpine P R (.lam (.lam (.const d))) a q)))
      (codes.holdsOf (.app (.var j) (.const d))) signature.rules.computation := by
  intro conversion
  exact Confluence.not_conv_spineHead_spineHead presentation recursor_not_defined
    (show ¬ Confluence.Defined jN codes d from Confluence.not_defined_of_ne hdj hdholds)
    (Ne.symm hdrec) (k := 5) (k' := 0) rfl rfl
    (Confluence.conv_of_conv_holds_var (base := signature.accBase) computesJ names
      headEq_symmetric conversion)

/-- In the transport control's context, the call and the unfolded call are not
convertible. -/
theorem control_not_conv :
    ¬ Conv signature.rules.headEq signature.controlCall signature.controlUnfolding
      signature.rules.computation :=
  separation (.var 6) (.var 5) (.var 3) (.var 2) 4

/-- **The conversion rule cannot replace the unfolding in the transport
control**: the hypothesis's type is not convertible to the goal. -/
theorem hypothesis_not_conv_goal :
    ¬ Conv signature.rules.headEq (codes.holdsOf (.app (.var 1) signature.controlCall))
      signature.transportGoal signature.rules.computation :=
  Signature.holds_separation computesJ names headEq_symmetric ⟨by decide, by decide⟩
    (.var 6) (.var 5) (.var 3) (.var 2) 4 1

/-- **In the strong variant the same pair is convertible**, by one unfolding
step: the separation is the inertness of the recursor, not a feature of the
terms. -/
theorem strong_identifies :
    Conv signature.strongRules.headEq signature.controlCall signature.controlUnfolding
      signature.strongRules.computation :=
  .rel _ _ (.root (signature.strongRules_step _ _ _ _ _))

/-! ## Divergence of the strong variant -/

theorem baseSpines : signature.BaseSpines := by
  intro n l r step
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, -⟩ := step
  exact ⟨jN, 6, by decide, rfl⟩

/-- **The loop is typed** in the strong variant. -/
theorem loop_typed :
    Typed signature.strongRules signature.loopTelescope signature.loopTerm (.app (.var 4) (.var 1)) :=
  signature.loop_typed laws

/-- **The loop has no normal form** in the strong variant. -/
theorem loop_no_normal_form {u : Tm Tower.Head 5}
    (steps : Relation.ReflTransGen signature.StrongStep signature.loopTerm u) :
    ∃ v, signature.StrongStep u v :=
  Signature.loop_no_normal_form laws baseSpines Signature.loopStep_loops steps

/-! ### The package's root steps, as an oracle -/

theorem appSpine_headArgs {n : Nat} : ∀ (t : Tm Tower.Head n), appSpine (headArgs t).1 (headArgs t).2 = t
  | .app f a => by
      simp only [headArgs]
      rw [appSpine_concat, appSpine_headArgs f]
  | .var _ => rfl
  | .const _ => rfl
  | .head _ => rfl
  | .pi _ _ => rfl
  | .sigma _ _ => rfl
  | .id _ _ _ => rfl
  | .lam _ => rfl
  | .pair _ _ => rfl
  | .fst _ => rfl
  | .snd _ => rfl
  | .refl _ => rfl

/-- The identity eliminator at reflexivity. -/
def jRoot? {n : Nat} (t : Tm Tower.Head n) : Option (Tm Tower.Head n) :=
  match headArgs t with
  | (.const c, [_a₀, _a₁, _a₂, a₃, _a₄, .refl _a₅]) => if c = jN then some a₃ else none
  | _ => none

/-- The decoder at a code. -/
def decode? {n : Nat} (x : Tm Tower.Head n) : Option (Tm Tower.Head n) :=
  match headArgs x with
  | (.const c, [p, q]) =>
      if c = impN then some (.pi (codes.holdsOf p) (codes.holdsOf (rename wk q))) else none
  | (.const c, [f]) =>
      if c = allPropN then
        some (.pi (liftClosed (.const propN)) (codes.holdsOf (.app (rename wk f) (.var 0))))
      else if c = allPredN then
        some (.pi (liftClosed (.pi (.const propN) (.const propN)))
          (codes.holdsOf (.app (rename wk f) (.var 0))))
      else none
  | _ => none

/-- The decoder's root step. -/
def decodeRoot? {n : Nat} (t : Tm Tower.Head n) : Option (Tm Tower.Head n) :=
  match headArgs t with
  | (.const c, [x]) => if c = holdsN then decode? x else none
  | _ => none

/-- The recursor's definitional unfolding. -/
def recRoot? {n : Nat} (t : Tm Tower.Head n) : Option (Tm Tower.Head n) :=
  match headArgs t with
  | (.const c, [P, R, F, a, q]) => if c = recN then some (signature.unfolding P R F a q) else none
  | _ => none

/-- The root steps of the propositional variant: `J` and the decoder. -/
def inertOracle : RootOracle Tower.Head := fun t => (jRoot? t).orElse fun _ => decodeRoot? t

/-- The root steps of the strong variant: also the unfolding. -/
def strongOracle : RootOracle Tower.Head := fun t => (inertOracle t).orElse fun _ => recRoot? t

theorem jRoot?_sound {n : Nat} {t u : Tm Tower.Head n} (h : jRoot? t = some u) :
    signature.base.computation.step t u := by
  unfold jRoot? at h
  split at h
  · rename_i _ c a₀ a₁ a₂ a₃ a₄ a₅ same
    split at h
    · rename_i hc
      cases h
      subst hc
      refine ⟨a₀, a₁, a₂, _, a₄, a₅, ?_, rfl⟩
      rw [← appSpine_headArgs t, same]
    · cases h
  · cases h

theorem decode?_sound {n : Nat} {x u : Tm Tower.Head n} (h : decode? x = some u) :
    DecoderStep codes.decoders (codes.holdsOf x) u := by
  unfold decode? at h
  split at h
  · rename_i c p q same
    split at h
    · rename_i hc
      cases h
      subst hc
      have e : x = codes.impOf p q := by rw [← appSpine_headArgs x, same]; rfl
      rw [e]
      exact .imp p q
    · cases h
  · rename_i c f same
    have e : x = .app (.const c) f := by rw [← appSpine_headArgs x, same]; rfl
    split at h
    · rename_i hc
      cases h
      subst hc
      rw [e]
      exact .all (A := .const propN) rfl f
    · split at h
      · rename_i _ hc
        cases h
        subst hc
        rw [e]
        exact .all (A := .pi (.const propN) (.const propN)) rfl f
      · cases h
  · cases h

theorem decodeRoot?_sound {n : Nat} {t u : Tm Tower.Head n} (h : decodeRoot? t = some u) :
    DecoderStep codes.decoders t u := by
  unfold decodeRoot? at h
  split at h
  · rename_i c x same
    split at h
    · rename_i hc
      subst hc
      have e : t = codes.holdsOf x := by rw [← appSpine_headArgs t, same]; rfl
      rw [e]
      exact decode?_sound h
    · cases h
  · cases h

theorem recRoot?_sound {n : Nat} {t u : Tm Tower.Head n} (h : recRoot? t = some u) :
    signature.unfoldComputation.step t u := by
  unfold recRoot? at h
  split at h
  · rename_i c P R F a q same
    split at h
    · rename_i hc
      cases h
      subst hc
      have e : t = signature.recSpine P R F a q := by rw [← appSpine_headArgs t, same]; rfl
      rw [e]
      exact signature.unfoldComputation_of P R F a q
    · cases h
  · cases h

/-- The inert oracle proposes only root steps of the propositional variant. -/
theorem inertOracle_sound : inertOracle.Sound signature.rules := by
  intro n t u h
  simp only [inertOracle, Option.orElse] at h
  cases hj : jRoot? t with
  | some u' =>
      rw [hj] at h
      cases h
      exact .inl (jRoot?_sound hj)
  | none =>
      rw [hj] at h
      exact .inr (decodeRoot?_sound h)

/-- The strong oracle proposes only root steps of the strong variant. -/
theorem strongOracle_sound : strongOracle.Sound signature.strongRules := by
  intro n t u h
  simp only [strongOracle, Option.orElse] at h
  cases hi : inertOracle t with
  | some u' =>
      rw [hi] at h
      cases h
      rcases inertOracle_sound hi with base | decoder
      · exact .inl (.inl base)
      · exact .inr decoder
  | none =>
      rw [hi] at h
      exact .inl (.inr (recRoot?_sound h))

/-- The strong oracle unfolds the recursor at every full application. -/
theorem strongOracle_unfolds : signature.UnfoldsRecursor strongOracle := by
  intro n P R F a q
  rfl

/-- **The strong checker is incomplete at every budget** on the loop, and never
establishes a weak-head normal form. -/
theorem loop_incomplete (k : Nat) : ∃ s, whCheck strongOracle k signature.loopTerm = .incomplete s :=
  Signature.loop_whCheck_incomplete laws baseSpines strongOracle_sound strongOracle_unfolds k

theorem loop_not_established (k : Nat) (u : Tm Tower.Head 5) :
    whCheck strongOracle k signature.loopTerm ≠ .established u :=
  Signature.loop_whCheck_ne_established laws baseSpines strongOracle_sound strongOracle_unfolds k u

/-- **The inert checker establishes the loop's weak-head normal form** at budget
one: without the definitional unfolding, the recursor is stuck. -/
theorem loop_established (k : Nat) :
    whCheck inertOracle (k + 1) signature.loopTerm = .established signature.loopTerm :=
  Signature.loop_whCheck_established laws baseSpines inertOracle_sound k

/-- **In the propositional variant the loop's conversion problem is decided
negatively**: the loop is not convertible to its unfolding, whose recursive call
carries the inverted accessibility proof. -/
theorem loop_inert_not_conv :
    ¬ Conv signature.rules.headEq signature.loopTerm
      (signature.unfolding (.var 4) (.var 3) Signature.loopStep (.var 1) (.var 0))
      signature.rules.computation :=
  Signature.loop_inert_not_conv presentation recursor_not_defined

/-- In the strong variant the same pair is convertible, by one unfolding step. -/
theorem loop_strong_conv :
    Conv signature.strongRules.headEq signature.loopTerm
      (signature.unfolding (.var 4) (.var 3) Signature.loopStep (.var 1) (.var 0))
      signature.strongRules.computation :=
  .rel _ _ (.root (signature.strongRules_step _ _ _ _ _))

end PropInstance
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
