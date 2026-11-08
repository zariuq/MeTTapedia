import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramCompiledGround

/-!
# The join with the first-order equation core

First-order rows embed into the λ-terms of the binder-bearing core.
- **Rows:** a cell is an application, and the symbol `k` is the closed term `λ x₀ … x_k. x_k`
  (`k + 1` binders, the innermost variable), so distinct symbols stay distinct.
- **Patterns:** a pattern variable is a hole with no parameters. Every translated equation is a
  Miller pattern on both sides.

**Theorems.**
- `translate_answers`: on embedded ground rows, the branch of a translated equation has exactly the
  embedded answers of first-order matching. No range restriction is needed.
- `rewrites_iff`: one rewrite of the translated program is a ground rewrite of the first-order
  program (`ProgramCompiled.GRewrite`).
- `runs_iff`, for range-restricted programs: runs agree, since every answer of an embedded call is
  embedded.
- `step_join` and `execution_join`: with `eqStep_ground_iff` and `eqRuns_ground`, the binder-bearing
  core on the contextual step agrees with the first-order equation core (`EqStep`) on ground threads.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.FirstOrder

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open ProgramRows (Sx Pat)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Controls
  (lamT_inj appT_inj)

/-! ## Rows as λ-terms -/

/-- The symbol `k`: `k + 1` binders over the innermost variable. -/
def symTerm : ℕ → {Δ : Ctx sig} → Term sig Δ .term
  | 0, _ => lamT (.var .zero)
  | k + 1, _ => lamT (symTerm k)

theorem symTerm_ne_app {Δ : Ctx sig} (k : ℕ) (first second : Term sig Δ .term) :
    symTerm k ≠ appT first second := by
  cases k <;> intro same <;> cases same

theorem symTerm_inj : ∀ {Δ : Ctx sig} (k m : ℕ), symTerm (Δ := Δ) k = symTerm m → k = m
  | _, 0, 0, _ => rfl
  | _, 0, m + 1, same => by
      have inner := lamT_inj same
      cases m <;> cases inner
  | _, k + 1, 0, same => by
      have inner := lamT_inj same
      cases k <;> cases inner
  | _, k + 1, m + 1, same => congrArg (· + 1) (symTerm_inj k m (lamT_inj same))

def encSx : Sx → Term sig [] .term
  | .sym k => symTerm k
  | .cell head tail => appT (encSx head) (encSx tail)

theorem encSx_injective : ∀ first second : Sx, encSx first = encSx second → first = second
  | .sym k, .sym m, same => congrArg Sx.sym (symTerm_inj k m same)
  | .sym k, .cell _ _, same => absurd same (symTerm_ne_app k _ _)
  | .cell _ _, .sym m, same => absurd same.symm (symTerm_ne_app m _ _)
  | .cell a b, .cell c d, same => by
      have parts := appT_inj same
      rw [encSx_injective a c parts.1, encSx_injective b d parts.2]

/-! ## Patterns as Miller patterns -/

/-- First-order holes: one per pattern variable, with no parameters. -/
abbrev fo : ℕ → MetaArity sig := holeArity fun _ => []

def encPat : Pat → Term (signature sig fo) [] .term
  | .var x => generator fo x
  | .sym k => Rigid.includeTerm fo (symTerm k)
  | .cell head tail => app fo (encPat head) (encPat tail)

theorem encPat_pattern : ∀ p : Pat, ContextualPatternFragment.Pattern sig fo (encPat p)
  | .var x => ContextualPatternFragment.generator_pattern x
  | .sym k => ContextualPatternFragment.rigid_inclusion_pattern fo (symTerm k)
  | .cell head tail => .rigid (S := sig) LambdaContextualRung.Op.app _
      (.cons _ _ (encPat_pattern head) (.cons _ _ (encPat_pattern tail) .nil))

/-- The translation of a first-order equation. -/
def translate (e : ProgramEquations.Equation) : Equation sig [] .term :=
  ⟨ℕ, inferInstance, fo, encPat e.lhs, encPat e.rhs⟩

theorem translate_patterns (e : ProgramEquations.Equation) :
    ContextualPatternFragment.Pattern sig (translate e).arity (translate e).lhs ∧
      ContextualPatternFragment.Pattern sig (translate e).arity (translate e).rhs :=
  ⟨encPat_pattern e.lhs, encPat_pattern e.rhs⟩

theorem instantiate_encPat {W : Type} {target : W → MetaArity sig} (change : Assignment fo target)
    (θ : ℕ → Sx) : ∀ (p : Pat), (∀ x ∈ p.vars, change x = Rigid.includeTerm target (encSx (θ x))) →
      instantiate change (encPat p) = Rigid.includeTerm target (encSx (p.inst θ))
  | .var x, agree => by
      change instantiate change (generator fo x) = _
      rw [instantiate_generator]
      exact agree x (by simp [Pat.vars])
  | .sym k, _ => Rigid.instantiate_include change (symTerm k)
  | .cell head tail, agree => by
      change app target (instantiate change (encPat head)) (instantiate change (encPat tail)) = _
      rw [instantiate_encPat change θ head (fun x member => agree x (by simp [Pat.vars, member])),
        instantiate_encPat change θ tail (fun x member => agree x (by simp [Pat.vars, member]))]
      rfl

/-- **Inversion.** A solution reading a pattern as an embedded row reads each of its variables as an
embedded row. -/
theorem encPat_inversion {W : Type} {target : W → MetaArity sig} (change : Assignment fo target) :
    ∀ (p : Pat) (s : Sx), instantiate change (encPat p) = Rigid.includeTerm target (encSx s) →
      ∃ θ : ℕ → Sx, (∀ x ∈ p.vars, change x = Rigid.includeTerm target (encSx (θ x))) ∧ p.inst θ = s
  | .var x, s, same => by
      refine ⟨fun _ => s, ?_, rfl⟩
      intro y member
      simp only [Pat.vars, List.mem_singleton] at member
      subst member
      change instantiate change (generator fo y) = _ at same
      rwa [instantiate_generator] at same
  | .sym k, s, same => by
      have rows := Rigid.include_injective target (symTerm k) (encSx s) ((Rigid.instantiate_include change (symTerm k)).symm.trans same)
      refine ⟨fun _ => .sym 0, fun x member => by simp [Pat.vars] at member, ?_⟩
      cases s with
      | sym m => exact congrArg Sx.sym (symTerm_inj k m rows)
      | cell _ _ => exact absurd rows (symTerm_ne_app k _ _)
  | .cell head tail, s, same => by
      cases s with
      | sym m =>
          change app target (instantiate change (encPat head)) (instantiate change (encPat tail)) =
            Rigid.includeTerm target (symTerm m) at same
          cases m <;> cases (Term.op.inj same).1
      | cell first second =>
          change app target (instantiate change (encPat head)) (instantiate change (encPat tail)) =
            app target (Rigid.includeTerm target (encSx first)) (Rigid.includeTerm target (encSx second)) at same
          obtain ⟨θhead, agreeHead, readHead⟩ := encPat_inversion change head first (app_inj same).1
          obtain ⟨θtail, agreeTail, readTail⟩ := encPat_inversion change tail second (app_inj same).2
          let θ : ℕ → Sx := fun x => if x ∈ head.vars then θhead x else θtail x
          have shared : ∀ x ∈ tail.vars, θ x = θtail x := by
            intro x member
            by_cases inHead : x ∈ head.vars
            · simp only [θ, if_pos inHead]
              exact encSx_injective _ _ (Rigid.include_injective _ _ _
                ((agreeHead x inHead).symm.trans (agreeTail x member)))
            · simp only [θ, if_neg inHead]
          refine ⟨θ, ?_, ?_⟩
          · intro x member
            simp only [Pat.vars, List.mem_append] at member
            by_cases inHead : x ∈ head.vars
            · rw [agreeHead x inHead]
              simp only [θ, if_pos inHead]
            · rw [shared x (member.resolve_left inHead)]
              exact agreeTail x (member.resolve_left inHead)
          · change Sx.cell (head.inst θ) (tail.inst θ) = _
            rw [Pat.inst_congr head (fun x member => by simp only [θ, if_pos member]) |>.trans readHead,
              (Pat.inst_congr tail shared).trans readTail]

/-! ## Equations -/

/-- **One equation.** On embedded ground rows, the branch of the translated equation answers exactly
the embeddings of the first-order matches. -/
theorem translate_answers (e : ProgramEquations.Equation) (s a : Sx) :
    Answers (translate e) (encSx s) (encSx a) ↔ ∃ θ : ℕ → Sx, e.lhs.inst θ = s ∧ e.rhs.inst θ = a := by
  constructor
  · rintro ⟨solution, matched, answered⟩
    obtain ⟨θlhs, agreeLhs, readLhs⟩ := encPat_inversion _ e.lhs s matched
    obtain ⟨θrhs, agreeRhs, readRhs⟩ := encPat_inversion _ e.rhs a answered
    let θ : ℕ → Sx := fun x => if x ∈ e.lhs.vars then θlhs x else θrhs x
    refine ⟨θ, (Pat.inst_congr e.lhs (fun x member => by simp only [θ, if_pos member])).trans readLhs, ?_⟩
    refine (Pat.inst_congr e.rhs (fun x member => ?_)).trans readRhs
    by_cases inLhs : x ∈ e.lhs.vars
    · simp only [θ, if_pos inLhs]
      exact encSx_injective _ _ (Rigid.include_injective _ _ _ ((agreeLhs x inLhs).symm.trans (agreeRhs x member)))
    · simp only [θ, if_neg inLhs]
  · rintro ⟨θ, matched, answered⟩
    refine ⟨fun x => encSx (θ x), ?_, ?_⟩
    · have read := instantiate_encPat ((translate e).assign (fun x => encSx (θ x)) (ground sig)) θ e.lhs
        (fun _ _ => rfl)
      rw [matched] at read
      exact read
    · have read := instantiate_encPat ((translate e).assign (fun x => encSx (θ x)) (ground sig)) θ e.rhs
        (fun _ _ => rfl)
      rw [answered] at read
      exact read

/-- For a range-restricted equation, every answer of an embedded call is embedded. -/
theorem restricted_answer (e : ProgramEquations.Equation) (restricted : ProgramCompiled.RangeRestricted e)
    (s : Sx) (answer : Term sig [] .term) (answered : Answers (translate e) (encSx s) answer) :
    ∃ a, answer = encSx a ∧ ∃ θ : ℕ → Sx, e.lhs.inst θ = s ∧ e.rhs.inst θ = a := by
  obtain ⟨solution, matched, read⟩ := answered
  obtain ⟨θ, agree, readLhs⟩ := encPat_inversion _ e.lhs s matched
  have opened := instantiate_encPat ((translate e).assign solution (ground sig)) θ e.rhs
    (fun x member => agree x (restricted x member))
  change instantiate ((translate e).assign solution (ground sig)) (encPat e.rhs) = Rigid.includeTerm (ground sig) answer at read
  rw [read] at opened
  exact ⟨e.rhs.inst θ, Rigid.include_injective _ _ _ opened, θ, readLhs, rfl⟩

/-! ## Programs -/

/-- The translated program, one equation per first-order equation, in program order. -/
def foProgram (prog : ProgramEquations.Program) : Fin prog.length → Equation sig [] .term :=
  fun index => translate (prog.get index)

/-- **One rewrite.** -/
theorem rewrites_iff (prog : ProgramEquations.Program) (s a : Sx) :
    Rewrites (foProgram prog) (encSx s) (encSx a) ↔ ProgramCompiled.GRewrite prog s a := by
  constructor
  · rintro ⟨index, answered⟩
    obtain ⟨θ, readLhs, readRhs⟩ := (translate_answers _ s a).mp answered
    exact ⟨prog.get index, List.mem_iff_get.mpr ⟨index, rfl⟩, θ, readLhs, readRhs.symm⟩
  · rintro ⟨e, member, θ, readLhs, readRhs⟩
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact ⟨index, (translate_answers _ s a).mpr ⟨θ, readLhs, readRhs.symm⟩⟩

/-- **Runs**, for range-restricted programs. -/
theorem runs_iff (prog : ProgramEquations.Program)
    (restricted : ∀ e ∈ prog, ProgramCompiled.RangeRestricted e) (s a : Sx) :
    Relation.ReflTransGen (Rewrites (foProgram prog)) (encSx s) (encSx a) ↔
      Relation.ReflTransGen (ProgramCompiled.GRewrite prog) s a := by
  constructor
  · intro runs
    have embedded : ∀ {answer}, Relation.ReflTransGen (Rewrites (foProgram prog)) (encSx s) answer →
        ∃ b, answer = encSx b ∧ Relation.ReflTransGen (ProgramCompiled.GRewrite prog) s b := by
      intro answer path
      induction path with
      | refl => exact ⟨s, rfl, .refl⟩
      | tail _ rewriting ih =>
          obtain ⟨b, rfl, earlier⟩ := ih
          obtain ⟨index, answered⟩ := rewriting
          obtain ⟨c, rfl, θ, readLhs, readRhs⟩ :=
            restricted_answer _ (restricted _ (List.mem_iff_get.mpr ⟨index, rfl⟩)) b _ answered
          exact ⟨c, rfl, earlier.tail ⟨prog.get index, List.mem_iff_get.mpr ⟨index, rfl⟩, θ, readLhs,
            readRhs.symm⟩⟩
    obtain ⟨b, same, path⟩ := embedded runs
    rw [encSx_injective _ _ same]
    exact path
  · intro runs
    induction runs with
    | refl => exact .refl
    | tail _ rewriting ih => exact ih.tail ((rewrites_iff prog _ _).mpr rewriting)

/-- **The step join.** For a range-restricted program, one rewrite of the binder-bearing core on
embedded rows is one reference step of the first-order equation core on a ground thread. -/
theorem step_join (prog : ProgramEquations.Program)
    (restricted : ∀ e ∈ prog, ProgramCompiled.RangeRestricted e) (s a : Sx) (n : ℕ) :
    Rewrites (foProgram prog) (encSx s) (encSx a) ↔
      ProgramEquations.EqStep prog (ProgramCompiled.gthread s ::ₘ 0, n)
        (ProgramCompiled.gthread a ::ₘ 0, n + 1) := by
  rw [rewrites_iff, ProgramCompiled.eqStep_ground_iff restricted s n]
  constructor
  · intro rewriting
    exact ⟨a, rewriting, rfl⟩
  · rintro ⟨b, rewriting, same⟩
    have threads : ProgramCompiled.gthread a = ProgramCompiled.gthread b := by
      have rows := (Prod.mk.inj same).1
      simpa only [Multiset.cons_zero, Multiset.singleton_inj] using rows
    rw [ProgramCompiled.gthread_inj threads]
    exact rewriting

/-- **The execution join.** For a range-restricted program, the runs of the binder-bearing core on
the contextual step from an embedded call read an embedded row exactly when the first-order equation
core reaches its ground thread. -/
theorem execution_join (prog : ProgramEquations.Program)
    (restricted : ∀ e ∈ prog, ProgramCompiled.RangeRestricted e) (s a : Sx) (n : ℕ) :
    (∃ after, Relation.ReflTransGen (Transition (foProgram prog)) (initial (encSx s)) after ∧
        Reads (foProgram prog) after (encSx a)) ↔
      ∃ k, Relation.ReflTransGen (ProgramEquations.EqStep prog) (ProgramCompiled.gthread s ::ₘ 0, n)
        (ProgramCompiled.gthread a ::ₘ 0, n + k) := by
  rw [← execution_iff, runs_iff prog restricted]
  constructor
  · exact (ProgramCompiled.eqRuns_ground restricted s n).2 a
  · rintro ⟨k, path⟩
    obtain ⟨b, j, same, runs⟩ := (ProgramCompiled.eqRuns_ground restricted s n).1 _ path
    have threads : ProgramCompiled.gthread a = ProgramCompiled.gthread b := by
      have rows := (Prod.mk.inj same).1
      simpa only [Multiset.cons_zero, Multiset.singleton_inj] using rows
    rw [ProgramCompiled.gthread_inj threads]
    exact runs

#print axioms encSx_injective
#print axioms translate_patterns
#print axioms encPat_inversion
#print axioms translate_answers
#print axioms restricted_answer
#print axioms rewrites_iff
#print axioms runs_iff
#print axioms step_join
#print axioms execution_join

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.FirstOrder
