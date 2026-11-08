import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramAdequacy

/-!
# Ground calls: two-way unification against a ground call is matching

For a ground call, the two-way unification of `EqStep` is one-way matching: a most general unifier
of a left-hand side, renamed apart, with an embedded row binds exactly the pattern's variables, to
the parts of the row (`ProgramRows.match_at`). On a single ground thread, a reference step of a
range-restricted program (every right-hand-side variable occurs on the left) is therefore a ground
rewrite at the root (`GRewrite`), and conversely (`eqStep_ground_iff`, `eqRuns_ground_iff`).

`GRewrite` is the semantics of a program on ground S-expressions: an equation whose left-hand side
matches the expression replaces it by its right-hand side under the match.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-- Every variable of the right-hand side occurs on the left. -/
def RangeRestricted (e : ProgramEquations.Equation) : Prop := ∀ x ∈ e.rhs.vars, x ∈ e.lhs.vars

/-- **Ground rewriting at the root**: an equation of the program matches the expression, which is
replaced by the right-hand side under the match. -/
def GRewrite (prog : Program) (s s' : Sx) : Prop :=
  ∃ e ∈ prog, ∃ θ : ℕ → Sx, e.lhs.inst θ = s ∧ s' = e.rhs.inst θ

/-- A ground thread. -/
def gthread (s : Sx) : Tm := thread (embed s)

theorem gthread_inj {s s' : Sx} (h : gthread s = gthread s') : s = s' :=
  embed_injective (tagged_inj.mp h).2

/-- **On a single ground thread, a reference step is a ground rewrite.** -/
theorem eqStep_ground_iff {prog : Program} (restricted : ∀ e ∈ prog, RangeRestricted e) (s : Sx)
    (n : ℕ) (s' : Multiset Tm × ℕ) :
    EqStep prog (gthread s ::ₘ 0, n) s' ↔ ∃ a, GRewrite prog s a ∧ s' = (gthread a ::ₘ 0, n + 1) := by
  constructor
  · intro step
    generalize hs : (gthread s ::ₘ (0 : Multiset Tm), n) = start at step
    cases step with
    | call j t F n' θ mgu =>
        obtain ⟨hW, rfl⟩ := Prod.mk.inj hs
        rw [Multiset.cons_zero] at hW
        obtain ⟨same, rfl⟩ := (Multiset.singleton_eq_cons_iff _).mp hW
        have ht : t = embed s := ((tagged_inj.mp same).2).symm
        subst ht
        have solved : θ.applyTerm ((prog.get j).lhs.at n) = embed s := by
          have := mgu.unifies _ (List.mem_singleton_self _)
          rw [this, apply_embed]
        obtain ⟨matched, values⟩ := match_at _ solved
        refine ⟨(prog.get j).rhs.inst (fun x => decode (θ (n, x))),
          ⟨prog.get j, List.get_mem prog j, _, matched, rfl⟩, ?_⟩
        rw [Multiset.map_zero]
        congr 2
        rw [gthread, thread, ← apply_at _ fun x hx =>
          values x (restricted _ (List.get_mem prog j) x hx)]
        rfl
  · rintro ⟨a, ⟨e, member, θ, matched, rfl⟩, rfl⟩
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp member
    let δ : Subst rows := fun v => if v.1 = n then embed (θ v.2) else .var v
    have unifies : Unifies δ [((prog.get j).lhs.at n, embed s)] := by
      rw [unifies_single, apply_embed, ← matched]
      exact apply_at _ fun x _ => if_pos rfl
    obtain ⟨μ, mgu⟩ := exists_isMGU ⟨δ, unifies⟩
    have step := EqStep.call j (embed s) 0 n μ mgu
    have solved : μ.applyTerm ((prog.get j).lhs.at n) = embed ((prog.get j).lhs.inst θ) := by
      rw [matched]
      have := mgu.unifies _ (List.mem_singleton_self _)
      rw [this, apply_embed]
    have values := agree_of_apply _ solved
    have answer : μ.applyTerm ((prog.get j).rhs.at n) = embed ((prog.get j).rhs.inst θ) :=
      apply_at _ fun x hx => values x (restricted _ (List.get_mem prog j) x hx)
    rw [answer, Multiset.map_zero] at step
    exact step

/-- **Reference runs of a single ground thread are ground rewriting runs**, one scope per step. -/
theorem eqRuns_ground {prog : Program} (restricted : ∀ e ∈ prog, RangeRestricted e) (s : Sx) (n : ℕ) :
    (∀ q, Relation.ReflTransGen (EqStep prog) (gthread s ::ₘ 0, n) q →
      ∃ b k, q = (gthread b ::ₘ 0, n + k) ∧ Relation.ReflTransGen (GRewrite prog) s b) ∧
    (∀ a, Relation.ReflTransGen (GRewrite prog) s a →
      ∃ k, Relation.ReflTransGen (EqStep prog) (gthread s ::ₘ 0, n) (gthread a ::ₘ 0, n + k)) := by
  refine ⟨fun q run => ?_, fun a run => ?_⟩
  · induction run with
    | refl => exact ⟨s, 0, rfl, .refl⟩
    | tail _ step ih =>
        obtain ⟨b, k, rfl, run⟩ := ih
        obtain ⟨c, rewrite, rfl⟩ := (eqStep_ground_iff restricted b (n + k) _).mp step
        exact ⟨c, k + 1, rfl, run.tail rewrite⟩
  · induction run with
    | refl => exact ⟨0, .refl⟩
    | @tail b c _ rewrite ih =>
        obtain ⟨k, path⟩ := ih
        exact ⟨k + 1, path.tail ((eqStep_ground_iff restricted b (n + k) _).mpr ⟨c, rewrite, rfl⟩)⟩

#print axioms eqStep_ground_iff
#print axioms eqRuns_ground

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled
