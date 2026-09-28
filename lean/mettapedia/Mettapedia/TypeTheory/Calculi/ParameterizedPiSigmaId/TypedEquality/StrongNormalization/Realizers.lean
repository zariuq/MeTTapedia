import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Kripke

/-!
# Realizers of numbers, of identity proofs and of codes

A spine of a constant that does not compute at the spine's length, such as a
constructor applied to arguments, reduces only in its arguments, so it is
strongly normalizing when its arguments are.

Numbers have three shapes: zero, a successor of a shape, and the shape of a
term that never becomes a numeral. A realizer of a number of a given shape is
a strongly normalizing term that reduces to `zero` only at shape zero, and to
`suc u` only at a successor shape, with `u` a realizer of the predecessor's
shape. A realizer of the third shape never reduces to a numeral. The numerals
realize their own shapes.

A realizer of an identity proof is a strongly normalizing term that reduces
to reflexivity only if the endpoints are related. Identity candidates of
equivalent relations are equal, and when the endpoints are related the
realizers are all strongly normalizing terms.

A realizer of a code is a term whose decoding is strongly normalizing. Codes
decode to function types and identity types whose parts are decodings of the
code's parts: implication of realizers of codes is a realizer of codes; a
quantifier applied to a family is a realizer of codes when the family,
applied to a fresh variable, is; and an equation between strongly normalizing
terms is a realizer of codes.

Strong normalization of a code does not suffice for strong normalization of
its decoding. A quantifier's family is decoded applied to a fresh variable,
and a strongly normalizing family may be a partial application of a defined
constant whose unfolding, once the variable completes its arguments, does not
terminate. The realizers of codes are therefore those whose decoding is
strongly normalizing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace StrongNormalization

open Normalization

variable {Head : Type} {R : Rules Head} {roles : Roles Head}

/-! ## Canonical forms and first steps -/

/-- An inert term is not a canonical form. -/
theorem Inert.not_canonical {n : Nat} {t : Tm Head n} (inert : Inert roles t) :
    ¬ Canonical roles t := by
  rintro (⟨x, rfl⟩ | ⟨k, arity, args, role, rfl⟩)
  · exact inert.2.2.1 x rfl
  · exact inert.2.2.2.1 k arity args role rfl

/-- A reduction between different terms starts with a step. -/
theorem ReducesStar.first_step {n : Nat} {t v : Tm Head n} (steps : ReducesStar R t v)
    (ne : t ≠ v) : ∃ t', Reduces R t t' ∧ ReducesStar R t' v := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd rfl ne
  | head step rest _ => exact ⟨_, step, rest⟩

section Renaming

variable (reflects : RootReflectsRename R.computation) {n m : Nat} {ρ : Ren n m}
  {t : Tm Head n}
include reflects

theorem ReducesStar.rename_const {c : DeclName}
    (steps : ReducesStar R (Presentation.rename ρ t) (.const c)) :
    ReducesStar R t (.const c) := by
  obtain ⟨t', steps', e⟩ := ReducesStar.rename_inv reflects steps
  rw [rename_eq_const e.symm] at steps'
  exact steps'

theorem ReducesStar.rename_constApp {c : DeclName} {u : Tm Head m}
    (steps : ReducesStar R (Presentation.rename ρ t) (.app (.const c) u)) :
    ∃ u', ReducesStar R t (.app (.const c) u') ∧ Presentation.rename ρ u' = u := by
  obtain ⟨t', steps', e⟩ := ReducesStar.rename_inv reflects steps
  obtain ⟨f, u', rfl, hf, rfl⟩ := rename_eq_app e.symm
  rw [rename_eq_const hf] at steps'
  exact ⟨u', steps', rfl⟩

theorem ReducesStar.rename_refl {u : Tm Head m}
    (steps : ReducesStar R (Presentation.rename ρ t) (.refl u)) :
    ∃ u', ReducesStar R t (.refl u') ∧ Presentation.rename ρ u' = u := by
  obtain ⟨t', steps', e⟩ := ReducesStar.rename_inv reflects steps
  obtain ⟨u', rfl, rfl⟩ := rename_eq_refl e.symm
  exact ⟨u', steps', rfl⟩

end Renaming

/-! ## Spines of constants that do not compute -/

section Spines

variable (shape : RootShape R roles)
include shape

/-- The reducts of a spine of a constant that does not compute at the spine's
length or below reduce one argument. -/
theorem constSpine_reduct {n : Nat} {c : DeclName} :
    ∀ {args : List (Tm Head n)},
      (∀ arity scrutinee, roles c = .computes arity scrutinee → args.length < arity) →
      ∀ {v : Tm Head n}, Reduces R (appSpine (.const c) args) v →
        ∃ pre a a' post, args = pre ++ a :: post ∧ Reduces R a a' ∧
          v = appSpine (.const c) (pre ++ a' :: post) := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
      intro stuck v step
      change Reduces R (.const c) v at step
      cases step with
      | root r =>
          obtain ⟨c', arity, scrutinee, args', role, e, length, _⟩ := shape.spine r
          obtain ⟨rfl, rfl⟩ := appSpine_const_injective (show appSpine (.const c) [] = _ from e)
          have short := stuck arity scrutinee role
          rw [← length] at short
          exact absurd short (Nat.lt_irrefl _)
  | append_singleton init last ih =>
      intro stuck v step
      rw [appSpine_concat] at step
      generalize hf : appSpine (.const c) init = f at step
      cases step with
      | betaPi body a => exact absurd hf appSpine_const_ne_lam'
      | root r =>
          obtain ⟨c', arity, scrutinee, args', role, e, length, _⟩ := shape.spine r
          rw [← hf, ← appSpine_concat] at e
          obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
          have short := stuck arity scrutinee role
          rw [← length] at short
          exact absurd short (Nat.lt_irrefl _)
      | congAppFun s =>
          subst hf
          have stuck' : ∀ arity scrutinee, roles c = .computes arity scrutinee →
              init.length < arity := by
            intro arity scrutinee role
            have short := stuck arity scrutinee role
            rw [List.length_append, List.length_singleton] at short
            exact Nat.lt_of_succ_lt short
          obtain ⟨pre, a, a', post, rfl, s', rfl⟩ := ih stuck' s
          exact ⟨pre, a, a', post ++ [last], by simp, s', by rw [← appSpine_concat]; simp⟩
      | congAppArg s =>
          subst hf
          exact ⟨init, last, _, [], rfl, s, (appSpine_concat _ _ _).symm⟩

/-- A constant that does not compute without arguments takes no step. -/
theorem const_normal {c : DeclName}
    (stuck : ∀ arity scrutinee, roles c = .computes arity scrutinee → 0 < arity) {n : Nat}
    (v : Tm Head n) : ¬ Reduces R (.const c) v := by
  intro step
  obtain ⟨pre, a, a', post, e, -, -⟩ := constSpine_reduct shape (args := []) stuck step
  simp at e

/-- The reducts of a constant applied to one argument, when it does not compute
with one argument or fewer, reduce the argument. -/
theorem constApp_reduct {c : DeclName}
    (stuck : ∀ arity scrutinee, roles c = .computes arity scrutinee → 1 < arity) {n : Nat}
    {a v : Tm Head n} (step : Reduces R (.app (.const c) a) v) :
    ∃ a', Reduces R a a' ∧ v = .app (.const c) a' := by
  obtain ⟨pre, x, x', post, e, s, rfl⟩ := constSpine_reduct shape (args := [a]) stuck step
  rcases pre with _ | ⟨y, pre⟩
  · simp only [List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨x', s, rfl⟩
  · simp at e

/-- The reducts of a constant applied to two arguments, when it does not
compute with two arguments or fewer, reduce one of the arguments. -/
theorem constApp₂_reduct {c : DeclName}
    (stuck : ∀ arity scrutinee, roles c = .computes arity scrutinee → 2 < arity) {n : Nat}
    {a b v : Tm Head n} (step : Reduces R (.app (.app (.const c) a) b) v) :
    (∃ a', Reduces R a a' ∧ v = .app (.app (.const c) a') b) ∨
      ∃ b', Reduces R b b' ∧ v = .app (.app (.const c) a) b' := by
  obtain ⟨pre, x, x', post, e, s, rfl⟩ := constSpine_reduct shape (args := [a, b]) stuck step
  rcases pre with _ | ⟨y, _ | ⟨z, pre⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact .inl ⟨x', s, rfl⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact .inr ⟨x', s, rfl⟩
  · simp at e

/-- A spine of a constant that does not compute at the spine's length is
strongly normalizing when its arguments are. -/
theorem SN.constSpine {n : Nat} {c : DeclName} :
    ∀ {args : List (Tm Head n)},
      (∀ arity scrutinee, roles c = .computes arity scrutinee → args.length < arity) →
      (∀ a ∈ args, SN R a) → SN R (appSpine (.const c) args) := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
      intro stuck _
      exact SN.intro fun v step => absurd step (const_normal shape stuck v)
  | append_singleton init last ih =>
      intro stuck sns
      have stuck' : ∀ arity scrutinee, roles c = .computes arity scrutinee →
          init.length < arity := by
        intro arity scrutinee role
        have short := stuck arity scrutinee role
        rw [List.length_append, List.length_singleton] at short
        exact Nat.lt_of_succ_lt short
      have key : ∀ f, SN R f → ∀ init' : List (Tm Head n), f = appSpine (.const c) init' →
          init'.length = init.length → ∀ a, SN R a → SN R (.app f a) := by
        intro f sf
        induction sf with
        | intro f _ ihf =>
            intro init' hf hlen a sa
            induction sa with
            | intro a ha iha =>
                refine SN.intro fun v step => ?_
                cases step with
                | betaPi body x => exact absurd hf.symm appSpine_const_ne_lam'
                | root r =>
                    obtain ⟨c', arity, scrutinee, args', role, e, length, _⟩ := shape.spine r
                    rw [hf, ← appSpine_concat] at e
                    obtain ⟨rfl, rfl⟩ := appSpine_const_injective e
                    have short := stuck arity scrutinee role
                    rw [← length] at short
                    simp [hlen] at short
                | congAppFun s =>
                    subst hf
                    have stuckInit : ∀ arity scrutinee, roles c = .computes arity scrutinee →
                        init'.length < arity := by
                      intro arity scrutinee role
                      rw [hlen]
                      exact stuck' arity scrutinee role
                    obtain ⟨pre, x, x', post, rfl, _, rfl⟩ :=
                      constSpine_reduct shape stuckInit s
                    exact ihf _ s _ rfl (by simpa using hlen) a (SN.intro ha)
                | congAppArg s => exact iha _ s
      rw [appSpine_concat]
      exact key _ (ih stuck' fun a ha => sns a (List.mem_append_left _ ha)) init rfl rfl last
        (sns last (List.mem_append_right _ (List.mem_singleton_self _)))

end Spines

/-! ## Numbers -/

/-- The shape of a number: zero, a successor, or the shape of a term that
never becomes a numeral. -/
inductive NumShape where
  | zero
  | suc (s : NumShape)
  | star
  deriving DecidableEq

/-- The numerals are constructors: `zero` without fields and `suc` with one. -/
structure NumeralRoles (roles : Roles Head) (zero suc : DeclName) : Prop where
  zero : roles zero = .constructor 0
  suc : roles suc = .constructor 1

section Numbers

variable (reflects : RootReflectsRename R.computation) {zero suc : DeclName}
  (numerals : NumeralRoles roles zero suc)

/-- The realizers of the numbers of each shape: strongly normalizing terms that
reduce to `zero` only at shape zero, and to `suc u` only at a successor shape,
with `u` a realizer of the predecessor shape. A realizer of the shape `star`
never reduces to a numeral. -/
def NumReal : NumShape → KCand R roles
  | .zero =>
    { mem := fun t => SN R t ∧ ∀ u, ¬ ReducesStar R t (.app (.const suc) u)
      rename := fun {_ _} ρ {_} h => ⟨SN.rename reflects ρ h.1, fun _ steps => by
        obtain ⟨u', steps', -⟩ := ReducesStar.rename_constApp reflects steps
        exact h.2 u' steps'⟩
      sn := fun h => h.1
      reduct := fun h step => ⟨h.1.reduct step, fun u steps => h.2 u (.head step steps)⟩
      inert := fun hi h => ⟨SN.intro fun u step => (h u step).1, fun u steps => by
        obtain ⟨t', step, rest⟩ := steps.first_step (hi.2.2.2.1 suc 1 [u] numerals.suc)
        exact (h t' step).2 u rest⟩ }
  | .suc s =>
    { mem := fun t => SN R t ∧ ¬ ReducesStar R t (.const zero) ∧
        ∀ u, ReducesStar R t (.app (.const suc) u) → (NumReal s).mem u
      rename := fun {_ _} ρ {_} h => ⟨SN.rename reflects ρ h.1,
        fun steps => h.2.1 (ReducesStar.rename_const reflects steps),
        fun _ steps => by
          obtain ⟨u', steps', rfl⟩ := ReducesStar.rename_constApp reflects steps
          exact (NumReal s).rename ρ (h.2.2 u' steps')⟩
      sn := fun h => h.1
      reduct := fun h step => ⟨h.1.reduct step, fun steps => h.2.1 (.head step steps),
        fun u steps => h.2.2 u (.head step steps)⟩
      inert := fun hi h => ⟨SN.intro fun u step => (h u step).1,
        fun steps => by
          obtain ⟨t', step, rest⟩ := steps.first_step (hi.2.2.2.1 zero 0 [] numerals.zero)
          exact (h t' step).2.1 rest,
        fun u steps => by
          obtain ⟨t', step, rest⟩ := steps.first_step (hi.2.2.2.1 suc 1 [u] numerals.suc)
          exact (h t' step).2.2 u rest⟩ }
  | .star =>
    { mem := fun t => SN R t ∧ ¬ ReducesStar R t (.const zero) ∧
        ∀ u, ¬ ReducesStar R t (.app (.const suc) u)
      rename := fun {_ _} ρ {_} h => ⟨SN.rename reflects ρ h.1,
        fun steps => h.2.1 (ReducesStar.rename_const reflects steps),
        fun _ steps => by
          obtain ⟨u', steps', -⟩ := ReducesStar.rename_constApp reflects steps
          exact h.2.2 u' steps'⟩
      sn := fun h => h.1
      reduct := fun h step => ⟨h.1.reduct step, fun steps => h.2.1 (.head step steps),
        fun u steps => h.2.2 u (.head step steps)⟩
      inert := fun hi h => ⟨SN.intro fun u step => (h u step).1,
        fun steps => by
          obtain ⟨t', step, rest⟩ := steps.first_step (hi.2.2.2.1 zero 0 [] numerals.zero)
          exact (h t' step).2.1 rest,
        fun u steps => by
          obtain ⟨t', step, rest⟩ := steps.first_step (hi.2.2.2.1 suc 1 [u] numerals.suc)
          exact (h t' step).2.2 u rest⟩ }

theorem mem_numReal_zero {n : Nat} {t : Tm Head n} :
    (NumReal reflects numerals .zero).mem t ↔
      SN R t ∧ ∀ u, ¬ ReducesStar R t (.app (.const suc) u) :=
  Iff.rfl

theorem mem_numReal_suc {s : NumShape} {n : Nat} {t : Tm Head n} :
    (NumReal reflects numerals (.suc s)).mem t ↔
      SN R t ∧ ¬ ReducesStar R t (.const zero) ∧
        ∀ u, ReducesStar R t (.app (.const suc) u) → (NumReal reflects numerals s).mem u :=
  Iff.rfl

theorem mem_numReal_star {n : Nat} {t : Tm Head n} :
    (NumReal reflects numerals .star).mem t ↔
      SN R t ∧ ¬ ReducesStar R t (.const zero) ∧
        ∀ u, ¬ ReducesStar R t (.app (.const suc) u) :=
  Iff.rfl

variable (shape : RootShape R roles)
include shape

/-- `zero` realizes the shape zero. -/
theorem NumReal.zero_mem {n : Nat} :
    (NumReal reflects numerals .zero).mem (.const zero : Tm Head n) := by
  have stuck : ∀ arity scrutinee, roles zero = .computes arity scrutinee →
      ([] : List (Tm Head n)).length < arity := by
    intro arity scrutinee role
    rw [numerals.zero] at role
    cases role
  refine ⟨SN.constSpine shape stuck (by simp), fun u steps => ?_⟩
  obtain ⟨v, step, -⟩ := steps.first_step (by simp)
  exact const_normal shape stuck v step

/-- `suc u` realizes the successor of the shape `u` realizes. -/
theorem NumReal.suc_mem {s : NumShape} {n : Nat} {u : Tm Head n}
    (hu : (NumReal reflects numerals s).mem u) :
    (NumReal reflects numerals (.suc s)).mem (.app (.const suc) u) := by
  have stuck : ∀ arity scrutinee, roles suc = .computes arity scrutinee → 1 < arity := by
    intro arity scrutinee role
    rw [numerals.suc] at role
    cases role
  have steps_suc : ∀ v, ReducesStar R (.app (.const suc) u) v →
      ∃ w, ReducesStar R u w ∧ v = .app (.const suc) w := by
    intro v steps
    induction steps with
    | refl => exact ⟨u, .refl, rfl⟩
    | tail _ step ih =>
        obtain ⟨w, hw, rfl⟩ := ih
        obtain ⟨w', s', rfl⟩ := constApp_reduct shape stuck step
        exact ⟨w', hw.tail s', rfl⟩
  have su := (NumReal reflects numerals s).sn hu
  refine ⟨SN.constSpine shape (args := [u]) stuck (by simpa using su),
    fun steps => ?_, fun w steps => ?_⟩
  · obtain ⟨w, _, e⟩ := steps_suc _ steps
    cases e
  · obtain ⟨w', hw', e⟩ := steps_suc _ steps
    cases e
    exact (NumReal reflects numerals s).reducts hu hw'

end Numbers

/-! ## Identity proofs -/

section Identity

variable (reflects : RootReflectsRename R.computation)

/-- The realizers of an identity proof whose endpoints are related exactly when
`P` holds: strongly normalizing terms that reduce to reflexivity only if `P`. -/
def IdCand (P : Prop) : KCand R roles where
  mem := fun t => SN R t ∧ ∀ u, ReducesStar R t (.refl u) → P
  rename := fun {_ _} ρ {_} h => ⟨SN.rename reflects ρ h.1, fun _ steps => by
    obtain ⟨u', steps', -⟩ := ReducesStar.rename_refl reflects steps
    exact h.2 u' steps'⟩
  sn := fun h => h.1
  reduct := fun h step => ⟨h.1.reduct step, fun u steps => h.2 u (.head step steps)⟩
  inert := fun hi h => ⟨SN.intro fun u step => (h u step).1, fun u steps => by
    obtain ⟨t', step, rest⟩ := steps.first_step (hi.2.2.1 u)
    exact (h t' step).2 u rest⟩

theorem mem_idCand {P : Prop} {n : Nat} {t : Tm Head n} :
    (IdCand (roles := roles) reflects P).mem t ↔
      SN R t ∧ ∀ u, ReducesStar R t (.refl u) → P :=
  Iff.rfl

/-- Identity candidates of equivalent propositions are equal. -/
theorem IdCand.congr {P Q : Prop} (same : P ↔ Q) :
    IdCand (roles := roles) reflects P = IdCand reflects Q :=
  KCand.ext fun _ =>
    ⟨fun h => ⟨h.1, fun u steps => same.mp (h.2 u steps)⟩,
      fun h => ⟨h.1, fun u steps => same.mpr (h.2 u steps)⟩⟩

/-- When the endpoints are related, the realizers of an identity proof are the
strongly normalizing terms. -/
theorem IdCand.of_holds {P : Prop} (holds : P) :
    IdCand (roles := roles) reflects P = KCand.sn' reflects :=
  KCand.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, fun _ _ => holds⟩⟩

/-- Reflexivity realizes an identity proof whose endpoints are related. -/
theorem IdCand.refl_mem (shape : RootShape R roles) {P : Prop} (holds : P) {n : Nat}
    {a : Tm Head n} (sa : SN R a) : (IdCand (roles := roles) reflects P).mem (.refl a) :=
  ⟨SN.refl (RootShape.spineHeaded shape) sa, fun _ _ => holds⟩

end Identity

/-! ## Codes -/

section Codes

variable (shape : RootShape R roles) (reflects : RootReflectsRename R.computation)
  {D : Decoders Head} (decoderRoles : DecoderRoles roles D)
include shape decoderRoles

/-- The decoder takes no step unapplied. -/
theorem holds_normal {n : Nat} (v : Tm Head n) : ¬ Reduces R (.const D.holds) v :=
  const_normal shape (fun arity scrutinee role => by
    rw [decoderRoles.holds] at role
    injection role with same
    rw [← same]
    exact Nat.zero_lt_one) v

/-- The realizers of codes: terms whose decoding is strongly normalizing. -/
def CodeReal : KCand R roles where
  mem := fun c => SN R (.app (.const D.holds) c)
  rename := fun {_ _} ρ {_} h => SN.rename reflects ρ h
  sn := fun h => SN.app_right h
  reduct := fun h step => h.reduct (.congAppArg step)
  inert := fun {_} {c} hi h => SN.intro fun v step => by
    cases step with
    | root r =>
        obtain ⟨c', arity, scrutinee, args, role, e, _, accepts⟩ := shape.spine r
        obtain ⟨rfl, rfl⟩ :=
          appSpine_const_injective (show appSpine (.const D.holds) [c] = _ from e)
        rw [decoderRoles.holds] at role
        injection role with _ same
        subst same
        obtain ⟨a, ha, ca⟩ := InspectTree.accepts_single.mp accepts
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
        subst ha
        exact absurd ca (Inert.not_canonical hi)
    | congAppFun s => exact absurd s (holds_normal shape decoderRoles _)
    | congAppArg s => exact h _ s

theorem mem_codeReal {n : Nat} {c : Tm Head n} :
    (CodeReal shape reflects decoderRoles).mem c ↔ SN R (.app (.const D.holds) c) :=
  Iff.rfl

variable (decodes : ∀ {n : Nat} {l r : Tm Head n}, DecoderStep D l r → R.computation.step l r)
include decodes

/-- Implication of two realizers of codes is a realizer of codes. -/
theorem CodeReal.imp_mem {n : Nat} {p q : Tm Head n}
    (hp : (CodeReal shape reflects decoderRoles).mem p)
    (hq : (CodeReal shape reflects decoderRoles).mem q) :
    (CodeReal shape reflects decoderRoles).mem (.app (.app (.const D.imp) p) q) := by
  have stuck : ∀ arity scrutinee, roles D.imp = .computes arity scrutinee → 2 < arity := by
    intro arity scrutinee role
    rw [decoderRoles.imp] at role
    cases role
  have key : ∀ p : Tm Head n, SN R p → ∀ q : Tm Head n, SN R q →
      SN R (.app (.const D.holds) p) →
      SN R (.app (.const D.holds) q) →
      SN R (.app (.const D.holds) (.app (.app (.const D.imp) p) q)) := by
    intro p sp
    induction sp with
    | intro p _ ihp =>
        intro q sq
        induction sq with
        | intro q hq ihq =>
            intro decodedP decodedQ
            refine SN.intro fun v step => ?_
            cases step with
            | root r =>
                rw [shape.deterministic r (decodes (DecoderStep.imp p q))]
                exact SN.pi (RootShape.spineHeaded shape) decodedP
                  (SN.rename reflects wk decodedQ)
            | congAppFun s => exact absurd s (holds_normal shape decoderRoles _)
            | congAppArg s =>
                rcases constApp₂_reduct shape stuck s with ⟨p', s', rfl⟩ | ⟨q', s', rfl⟩
                · exact ihp p' s' q (SN.intro hq) (decodedP.reduct (.congAppArg s')) decodedQ
                · exact ihq q' s' decodedP (decodedQ.reduct (.congAppArg s'))
  exact key p (SN.app_right hp) q (SN.app_right hq) hp hq

/-- A quantifier applied to a family is a realizer of codes when the family
applied to a fresh variable is, and the quantifier's carrier is strongly
normalizing. -/
theorem CodeReal.all_mem {a : DeclName} {A : Tm Head 0} (carrier : D.allCarrier a = some A)
    (carrierSN : SN R A) {n : Nat} {f : Tm Head n}
    (body : (CodeReal shape reflects decoderRoles).mem
      (.app (Presentation.rename wk f) (.var 0))) :
    (CodeReal shape reflects decoderRoles).mem (.app (.const a) f) := by
  have stuck : ∀ arity scrutinee, roles a = .computes arity scrutinee → 1 < arity := by
    intro arity scrutinee role
    rw [decoderRoles.all carrier] at role
    cases role
  have sA : SN R (liftClosed A : Tm Head n) := SN.rename reflects Fin.elim0 carrierSN
  have key : ∀ f : Tm Head n, SN R f →
      SN R (.app (.const D.holds) (.app (Presentation.rename wk f) (.var 0))) →
      SN R (.app (.const D.holds) (.app (.const a) f)) := by
    intro f sf
    induction sf with
    | intro f _ ihf =>
        intro decodedBody
        refine SN.intro fun v step => ?_
        cases step with
        | root r =>
            rw [shape.deterministic r (decodes (DecoderStep.all carrier f))]
            exact SN.pi (RootShape.spineHeaded shape) sA decodedBody
        | congAppFun s => exact absurd s (holds_normal shape decoderRoles _)
        | congAppArg s =>
            obtain ⟨f', s', rfl⟩ := constApp_reduct shape stuck s
            exact ihf f' s'
              (decodedBody.reduct (.congAppArg (.congAppFun (StepCore.renameTerms s' wk))))
  exact key f (SN.of_rename wk (SN.app_left (SN.app_right body))) body

/-- A quantifier applied to a member of a Kripke function space into the
realizers of codes is a realizer of codes. -/
theorem CodeReal.all_mem_of_arrow {a : DeclName} {A : Tm Head 0}
    (carrier : D.allCarrier a = some A) (carrierSN : SN R A) (X : KCand R roles) {n : Nat}
    {f : Tm Head n}
    (family : (KCand.arrow shape reflects X (CodeReal shape reflects decoderRoles)).mem f) :
    (CodeReal shape reflects decoderRoles).mem (.app (.const a) f) :=
  CodeReal.all_mem shape reflects decoderRoles decodes carrier carrierSN
    (family wk (.var 0) (X.var_mem (RootShape.spineHeaded shape) 0))

/-- A quantifier applied to a member of a Kripke dependent function space into
the realizers of codes is a realizer of codes. -/
theorem CodeReal.all_mem_of_pi {a : DeclName} {A : Tm Head 0}
    (carrier : D.allCarrier a = some A) (carrierSN : SN R A) {I : Sort _} (point : I)
    (dom : I → KCand R roles) {n : Nat} {f : Tm Head n}
    (family : (KCand.pi shape reflects point dom
      (fun _ => CodeReal shape reflects decoderRoles)).mem f) :
    (CodeReal shape reflects decoderRoles).mem (.app (.const a) f) :=
  CodeReal.all_mem shape reflects decoderRoles decodes carrier carrierSN
    (family point wk (.var 0) ((dom point).var_mem (RootShape.spineHeaded shape) 0))

/-- An equation between strongly normalizing terms is a realizer of codes when
the equation's carrier is strongly normalizing. -/
theorem CodeReal.eq_mem {e : DeclName} {A : Tm Head 0} (carrier : D.eqCarrier e = some A)
    (carrierSN : SN R A) {n : Nat} {x y : Tm Head n} (sx : SN R x) (sy : SN R y) :
    (CodeReal shape reflects decoderRoles).mem (.app (.app (.const e) x) y) := by
  have stuck : ∀ arity scrutinee, roles e = .computes arity scrutinee → 2 < arity := by
    intro arity scrutinee role
    rw [decoderRoles.eq carrier] at role
    cases role
  have sA : SN R (liftClosed A : Tm Head n) := SN.rename reflects Fin.elim0 carrierSN
  induction sx generalizing y with
  | intro x hx ihx =>
      induction sy with
      | intro y hy ihy =>
          refine SN.intro fun v step => ?_
          cases step with
          | root r =>
              rw [shape.deterministic r (decodes (DecoderStep.eq carrier x y))]
              exact SN.id (RootShape.spineHeaded shape) sA (SN.intro hx) (SN.intro hy)
          | congAppFun s => exact absurd s (holds_normal shape decoderRoles _)
          | congAppArg s =>
              rcases constApp₂_reduct shape stuck s with ⟨x', s', rfl⟩ | ⟨y', s', rfl⟩
              · exact ihx x' s' (SN.intro hy)
              · exact ihy y' s'

end Codes

end StrongNormalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
