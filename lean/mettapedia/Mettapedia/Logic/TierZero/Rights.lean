import Mettapedia.Logic.TierZero.Kernel

/-!
# Only kernel steps make theorems: the rights the kernel's spaces need

The MeTTa kernel keeps two kinds of atoms of its own: **obligations** (a conclusion and the
premises still to discharge) and **theorems**. Its steps make an obligation from a rule instance,
discharge a premise by a theorem or a side condition, and turn an obligation with nothing left
into a theorem. This file states what makes that safe.

* `Honest`: every obligation's conclusion is derivable once its remaining judgment premises are,
  and every theorem is derivable.
* `kernel_honest`: kernel steps, together with clients that may only submit (rule name, arguments)
  pairs, keep the store honest. Every theorem reached from the empty store is derivable
  (`reachable_theorem_derivable`). This is the situation of the MeTTa kernel, whose obligations
  sit in a private space: clients hold only the right to send submissions.
* `forgery_of_writable_obligations`: if clients may also add obligations (the first version of
  the MeTTa kernel kept them in the clients' mailbox), a client can make any judgment a theorem,
  so every presentation with an underivable judgment is broken. `tests/k02_forgery.metta` in the
  kernel's scratch folder is the same attack, run.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero

universe u

variable {P : Presentation.{u}}

/-- The kernel's own atoms. -/
structure KStore (P : Presentation.{u}) where
  obs : List (P.J × List P.J)
  thms : List P.J

/-- Kernel steps. -/
inductive KStep : KStore P → KStore P → Prop
  | «open» {s : KStore P} {r a ps c} : P.inst r a = some (ps, c) →
      KStep s ⟨(c, ps) :: s.obs, s.thms⟩
  | dischargeTheorem {s : KStore P} {c p ps rest} : s.obs = (c, p :: ps) :: rest → p ∈ s.thms →
      KStep s ⟨(c, ps) :: rest, s.thms⟩
  | dischargeSide {s : KStore P} {c p ps rest} : s.obs = (c, p :: ps) :: rest → P.side p = true →
      KStep s ⟨(c, ps) :: rest, s.thms⟩
  | close {s : KStore P} {c rest} : s.obs = (c, []) :: rest → KStep s ⟨rest, c :: s.thms⟩
  /-- Obligations are worked on in any order: rotate the list. -/
  | rotate {s : KStore P} {o rest} : s.obs = o :: rest → KStep s ⟨rest ++ [o], s.thms⟩

/-- The store is honest. -/
def Honest (s : KStore P) : Prop :=
  (∀ o ∈ s.obs, (∀ p ∈ o.2, P.side p = false → Derivable P [] p) → Derivable P [] o.1) ∧
    ∀ j ∈ s.thms, Derivable P [] j

theorem kernel_honest {s t : KStore P} (step : KStep s t) (h : Honest s) : Honest t := by
  obtain ⟨hobs, hthms⟩ := h
  cases step with
  | «open» hi =>
      refine ⟨?_, hthms⟩
      intro o mem
      rcases List.mem_cons.mp mem with rfl | mem'
      · exact fun prem => Derivable.rule hi prem
      · exact hobs o mem'
  | @dischargeTheorem c p ps rest hs hp =>
      have hold := hobs (c, p :: ps) (by rw [hs]; exact List.mem_cons_self)
      refine ⟨?_, hthms⟩
      intro o mem
      rcases List.mem_cons.mp mem with rfl | mem'
      · intro prem
        refine hold fun q hq notSide => ?_
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hthms _ hp
        · exact prem q hq' notSide
      · exact hobs o (by rw [hs]; exact List.mem_cons_of_mem _ mem')
  | @dischargeSide c p ps rest hs sp =>
      have hold := hobs (c, p :: ps) (by rw [hs]; exact List.mem_cons_self)
      refine ⟨?_, hthms⟩
      intro o mem
      rcases List.mem_cons.mp mem with rfl | mem'
      · intro prem
        refine hold fun q hq notSide => ?_
        rcases List.mem_cons.mp hq with rfl | hq'
        · rw [sp] at notSide; cases notSide
        · exact prem q hq' notSide
      · exact hobs o (by rw [hs]; exact List.mem_cons_of_mem _ mem')
  | close hs =>
      refine ⟨fun o mem => hobs o (by rw [hs]; exact List.mem_cons_of_mem _ mem), ?_⟩
      intro j mem
      rcases List.mem_cons.mp mem with rfl | mem'
      · exact hobs _ (by rw [hs]; exact List.mem_cons_self) (by simp)
      · exact hthms j mem'
  | rotate hs =>
      refine ⟨?_, hthms⟩
      intro o mem
      rcases List.mem_append.mp mem with mem' | mem'
      · exact hobs o (by rw [hs]; exact List.mem_cons_of_mem _ mem')
      · rw [List.mem_singleton.mp mem']
        exact hobs _ (by rw [hs]; exact List.mem_cons_self)

theorem honest_empty : Honest (⟨[], []⟩ : KStore P) := ⟨by simp, by simp⟩

/-- **Only kernel steps make theorems**: from the empty store, every theorem is derivable. Client
submissions enter only through `open`, which reads the rule instance; so this covers any
interleaving of kernel steps and client submissions. -/
theorem reachable_theorem_derivable {t : KStore P}
    (reach : Relation.ReflTransGen KStep ⟨[], []⟩ t) : ∀ j ∈ t.thms, Derivable P [] j := by
  have : Honest t := by
    induction reach with
    | refl => exact honest_empty
    | tail _ step ih => exact kernel_honest step ih
  exact this.2

/-- Steps when clients may also add obligations. -/
inductive OpenStep : KStore P → KStore P → Prop
  | kernel {s t : KStore P} : KStep s t → OpenStep s t
  | clientObligation {s : KStore P} (o : P.J × List P.J) : OpenStep s ⟨o :: s.obs, s.thms⟩

/-- **The forgery**: with client-writable obligations, every judgment becomes a theorem. -/
theorem forgery_of_writable_obligations (j : P.J) :
    ∃ t : KStore P, Relation.ReflTransGen OpenStep ⟨[], []⟩ t ∧ j ∈ t.thms := by
  refine ⟨⟨[], [j]⟩, ?_, by simp⟩
  have first : OpenStep (⟨[], []⟩ : KStore P) ⟨[(j, [])], []⟩ := OpenStep.clientObligation (j, [])
  have second : OpenStep (⟨[(j, [])], []⟩ : KStore P) ⟨[], [j]⟩ :=
    OpenStep.kernel (KStep.close (c := j) (rest := []) rfl)
  exact Relation.ReflTransGen.head first (Relation.ReflTransGen.single second)

/-- So client-writable obligations break every presentation that has an underivable judgment. -/
theorem not_honest_of_writable_obligations {j : P.J} (under : ¬ Derivable P [] j) :
    ¬ ∀ t : KStore P, Relation.ReflTransGen OpenStep ⟨[], []⟩ t → ∀ k ∈ t.thms, Derivable P [] k := by
  intro safe
  obtain ⟨t, reach, mem⟩ := forgery_of_writable_obligations (P := P) j
  exact under (safe t reach j mem)

namespace Controls

open Mettapedia.Logic.TierZero.Controls

/-- A property closed under the rules and true of the hypotheses holds of every derivable judgment
(this presentation has no side conditions). -/
theorem derivable_closed {Q : pres.J → Prop} {hyps : List pres.J}
    (rules : ∀ r a ps c, pres.inst r a = some (ps, c) → (∀ p ∈ ps, Q p) → Q c)
    (hypsQ : ∀ j ∈ hyps, Q j) {j : pres.J} (h : Derivable pres hyps j) : Q j := by
  induction h with
  | hyp mem => exact hypsQ _ mem
  | rule hi _ ih => exact rules _ _ _ _ hi fun p mem => ih p mem rfl

/-- Truth with every atom false. -/
def falseEval : F → Bool
  | .atom _ => false
  | .imp a b => !falseEval a || falseEval b

/-- In the two-rule presentation, the atom `p` is underivable from no hypotheses: both rules keep
truth under the valuation making every atom false, and `p` is false there. -/
theorem p_underivable : ¬ Derivable pres [] (F.atom 0 : pres.J) := by
  intro h
  have := derivable_closed (Q := fun j : pres.J => falseEval j = true)
    (by
      intro r a ps c hi prem
      obtain ⟨x, y⟩ := a
      cases r
      · simp only [pres, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨-, rfl⟩ := hi
        cases hx : falseEval x <;> simp [falseEval, hx]
      · simp only [pres, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        have himp := prem (F.imp x y) (by simp)
        have hx := prem x (by simp)
        simp only [falseEval] at himp
        rw [hx] at himp
        simpa using himp)
    (by simp) h
  simp [falseEval] at this

/-- Hence the kernel with client-writable obligations is unsound for it. -/
theorem two_rule_forgery :
    ¬ ∀ t : KStore pres, Relation.ReflTransGen OpenStep ⟨[], []⟩ t →
      ∀ k ∈ t.thms, Derivable pres [] k :=
  not_honest_of_writable_obligations p_underivable

end Controls

end Mettapedia.Logic.TierZero
