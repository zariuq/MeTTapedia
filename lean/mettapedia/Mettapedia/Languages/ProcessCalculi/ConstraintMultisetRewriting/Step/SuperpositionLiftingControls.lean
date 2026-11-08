import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLiftingOverlap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLiftingRedundancy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLiftingInterpretation

/-!
# Controls for the lifting of superposition

The signature has the constants `⊤`, `a`, `b`, `nil`, the unary symbols `p`, `q`, and the clause
formers `lit⁺`, `lit⁻`, `cons` (`code`). Ground terms are ordered by the pairing interpretation
(`interpOrder`), a ground simplification ordering; the non-ground ordering is the strict subterm
ordering (`subtermOrder`), which is linked to every ground simplification ordering.

* **A refutation through lifting** (`lifting_unsatisfiable`, `ground_superposition`, `lift1`,
  `lifted_firing_admitted`, `lifting_refutation`): the ground instances of `{p(x₀) ≈ x₀, p(b) ≉ b}`
  are unsatisfiable, and their refutation starts with a superposition into the root of `p(b)`, a
  non-variable position. Its lift (`lift1`: the copy `p(x₁) ≈ x₁`, the unifier `x₁ ↦ b`) is an
  admitted firing of the shared store; an equality resolution on the derived clause, whose variable
  the knowledge binds, completes the refutation (`unifyFiring_admits_of_consistent`).
* **The variable-overlap case** (`overlap_inference`, `overlap_is_redundant`, `no_unifier`): the
  ground superposition of `a ≈ ⊤` into `q(a) ≉ ⊤`, the instance of `q(x₀) ≉ ⊤` under `x₀ ↦ a`, rewrites
  inside the instance of the variable. No non-ground superposition lifts it (`a` and `q(x₀)` do not
  unify); it is redundant.
* **A co-stable side condition fails at an instance; the closure guard admits it**
  (`condition_at_mgu`, `condition_fails_at_instance`, `bare_guard_refused`,
  `closure_guard_entailed`, `guarded_superposition_admitted`): superposing `p(x₁) ≈ x₂` into
  `p(b) ≉ b`, the condition `x₂ ⋡ p(x₁)` holds at the unifier `x₁ ↦ b` and fails at its instance
  `x₂ ↦ q(p(b))`.
* **`p(x) ∨ q(x)`, `¬p(a)`, `¬q(a)` is refuted on the shared step** (`refutation_run`): four firings
  (superposition, equality resolution, superposition, equality resolution) make the empty clause.
  This is a run of the step, not the output of a given-clause loop.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition.LiftingControls

open Mettapedia.Logic.LP
open Resolution (A)

/-! ## The signature, its orderings and the clause former -/

/-- The unary symbols and the clause formers. -/
inductive Fn where
  | p
  | q
  | lit (negative : Bool)
  | cons
  deriving DecidableEq

/-- The signature: constants `⊤ = 0`, `a = 1`, `b = 2`, `nil = 3`. -/
abbrev csig : LPSignature where
  constants := Fin 4
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Fn
  functionArity
    | .p => 1
    | .q => 1
    | .lit _ => 2
    | .cons => 2

def fnCode : Fn → ℕ
  | .p => 0
  | .q => 1
  | .lit false => 2
  | .lit true => 3
  | .cons => 4

theorem fnCode_injective : Function.Injective fnCode := by
  rintro (_ | _ | ⟨_ | _⟩ | _) (_ | _ | ⟨_ | _⟩ | _) same <;> first | rfl | exact absurd same (by decide)

def codes : SymbolCodes csig := ⟨fun c => c.val, Fin.val_injective, fnCode, fnCode_injective⟩

instance : LinearOrder (GroundTerm csig) := interpOrder codes
instance : WellFoundedLT (GroundTerm csig) := interpOrder_wellFounded codes
instance : GroundSimplification csig := interpOrder_simplification codes

/-- The non-ground ordering: strict subterms. -/
abbrev ord : GroundedOrder csig := subtermOrder

def top : Term csig := .const 0
def a : Term csig := .const 1
def b : Term csig := .const 2
def nil : Term csig := .const 3
def p (t : Term csig) : Term csig := .app Fn.p fun _ => t
def q (t : Term csig) : Term csig := .app Fn.q fun _ => t
def x (n : ℕ) : Term csig := .var n

def gtop : GroundTerm csig := .const 0
def ga : GroundTerm csig := .const 1
def gb : GroundTerm csig := .const 2
def gp (t : GroundTerm csig) : GroundTerm csig := .app Fn.p fun _ => t
def gq (t : GroundTerm csig) : GroundTerm csig := .app Fn.q fun _ => t

def encodeLit (L : NLit csig) : Term csig := .app (Fn.lit L.negative) ![L.lhs, L.rhs]

def encode : NClause csig → Term csig
  | [] => nil
  | L :: C => .app Fn.cons ![encodeLit L, encode C]

theorem encodeLit_subst (τ : Subst csig) (L : NLit csig) :
    τ.applyTerm (encodeLit L) = encodeLit (L.subst τ) := by
  show Term.app (Fn.lit L.negative) (fun i => τ.applyTerm (![L.lhs, L.rhs] i)) =
    Term.app (Fn.lit L.negative) ![τ.applyTerm L.lhs, τ.applyTerm L.rhs]
  congr 1
  funext i
  rcases i with ⟨_ | _ | n, h⟩
  · rfl
  · rfl
  · exact absurd h (by simp)

theorem encode_subst (τ : Subst csig) : ∀ C : NClause csig, τ.applyTerm (encode C) = encode (C.subst τ)
  | [] => rfl
  | L :: C => by
      show Term.app Fn.cons (fun i => τ.applyTerm (![encodeLit L, encode C] i)) =
        Term.app Fn.cons ![encodeLit (L.subst τ), encode (NClause.subst τ C)]
      congr 1
      funext i
      rcases i with ⟨_ | _ | n, h⟩
      · exact encodeLit_subst τ L
      · exact encode_subst τ C
      · exact absurd h (by simp)

/-- **The clause former.** -/
def code : ClauseCode csig := ⟨encode, encode_subst⟩

/-! ## Strict subterms, unifiers and fixed clauses -/

theorem strictSubterm_exists_arg {s t : Term csig} (below : StrictSubterm s t) :
    ∃ (f : Fn) (ts : Fin (csig.functionArity f) → Term csig) (i : Fin (csig.functionArity f)),
      s = .app f ts ∧ (t = ts i ∨ StrictSubterm (ts i) t) := by
  induction below with
  | arg f ts i => exact ⟨f, ts, i, rfl, Or.inl rfl⟩
  | trans _ two ih _ =>
      obtain ⟨f, ts, i, rfl, here | deeper⟩ := ih
      · subst here
        exact ⟨f, ts, i, rfl, Or.inr two⟩
      · exact ⟨f, ts, i, rfl, Or.inr (.trans deeper two)⟩

theorem not_strictSubterm_const (c : Fin 4) (t : Term csig) : ¬ StrictSubterm (.const c) t := by
  intro below
  obtain ⟨_, _, _, same, -⟩ := strictSubterm_exists_arg below
  cases same

theorem not_strictSubterm_var (v : ℕ) (t : Term csig) : ¬ StrictSubterm (.var v) t := by
  intro below
  obtain ⟨_, _, _, same, -⟩ := strictSubterm_exists_arg below
  cases same

/-- The strict subterms of a unary application are its argument and the argument's. -/
theorem strictSubterm_unary {g : Fn} {t u : Term csig} (below : StrictSubterm (Term.app g fun _ => t) u) :
    u = t ∨ StrictSubterm t u := by
  obtain ⟨f, ts, i, same, rest⟩ := strictSubterm_exists_arg below
  obtain ⟨rfl, hargs⟩ := Term.app.inj same
  have args := eq_of_heq hargs
  rw [← args] at rest
  exact rest

theorem not_ge_const (c : Fin 4) {t : Term csig} (ne : Term.const c ≠ t) :
    ¬ ord.toStableOrder.ge (.const c) t :=
  fun ge => ge.elim (not_strictSubterm_const c t) ne

theorem not_ge_var (v : ℕ) {t : Term csig} (ne : Term.var v ≠ t) : ¬ ord.toStableOrder.ge (.var v) t :=
  fun ge => ge.elim (not_strictSubterm_var v t) ne

theorem reorient_refl (X : NClause csig) : Reorient X X :=
  ⟨X, List.Perm.refl X, List.forall₂_same.mpr fun _ _ => Or.inl rfl⟩

theorem fixes_id (C : NClause csig) : FixesClause (Subst.id csig) C :=
  fun L _ => ⟨Subst.applyTerm_id L.lhs, Subst.applyTerm_id L.rhs⟩

/-- The most general unifier of `g(xᵥ)` and `g(k)` for a unary `g`: `xᵥ ↦ k`. -/
theorem unary_principal (g : Fn) (i : Fin (csig.functionArity g)) (v : ℕ) (k : Fin 4) :
    (A csig).Principal [(Term.app g fun _ => x v, Term.app g fun _ => .const k)]
      (Subst.single (σ := csig) v (.const k)) := by
  refine ⟨fun e member => ?_, fun δ solved => ⟨δ, fun t => ?_⟩⟩
  · rw [List.mem_singleton.mp member]
    show Term.app g (fun _ => Subst.single (σ := csig) v (.const k) v) = Term.app g fun _ => .const k
    rw [Subst.single_eq (σ := csig)]
  · have unifies : δ.applyTerm (Term.app g fun _ => x v) = δ.applyTerm (Term.app g fun _ => .const k) :=
      solved _ List.mem_cons_self
    have atV : δ v = .const k := by
      have shapes : Term.app g (fun _ => δ v) = Term.app g (fun _ => .const k) := unifies
      exact congrFun (eq_of_heq (Term.app.inj shapes).2) i
    have same : δ ∘ₛ Subst.single (σ := csig) v (.const k) = δ := by
      funext w
      by_cases h : w = v
      · show δ.applyTerm (Subst.single (σ := csig) v (.const k) w) = δ w
        rw [h, Subst.single_eq (σ := csig), atV]
        rfl
      · show δ.applyTerm (Subst.single (σ := csig) v (.const k) w) = δ w
        rw [Subst.single_ne (σ := csig) _ h]
        rfl
    show δ.applyTerm t = (δ ∘ₛ Subst.single (σ := csig) v (.const k)).applyTerm t
    rw [same]

/-- The most general unifier of `xᵥ` and `k`: `xᵥ ↦ k`. -/
theorem var_principal (v : ℕ) (k : Fin 4) :
    (A csig).Principal [(x v, .const k)] (Subst.single (σ := csig) v (.const k)) := by
  refine ⟨fun e member => ?_, fun δ solved => ⟨δ, fun t => ?_⟩⟩
  · rw [List.mem_singleton.mp member]
    show Subst.single (σ := csig) v (.const k) v = .const k
    rw [Subst.single_eq (σ := csig)]
  · have atV : δ v = .const k := solved _ List.mem_cons_self
    have same : δ ∘ₛ Subst.single (σ := csig) v (.const k) = δ := by
      funext w
      by_cases h : w = v
      · show δ.applyTerm (Subst.single (σ := csig) v (.const k) w) = δ w
        rw [h, Subst.single_eq (σ := csig), atV]
        rfl
      · show δ.applyTerm (Subst.single (σ := csig) v (.const k) w) = δ w
        rw [Subst.single_ne (σ := csig) _ h]
        rfl
    show δ.applyTerm t = (δ ∘ₛ Subst.single (σ := csig) v (.const k)).applyTerm t
    rw [same]

theorem id_principal (t : Term csig) : (A csig).Principal [(t, t)] (Subst.id csig) :=
  ⟨(fun e member => by rw [List.mem_singleton.mp member]; rfl), fun δ _ => ⟨δ, fun s => by
    show δ.applyTerm s = (δ ∘ₛ Subst.id csig).applyTerm s
    rw [Subst.comp_id_right]⟩⟩

/-- A solution of the knowledge that solves the told equation solves the result's knowledge. -/
theorem models_result {label : ℕ → Term csig} {C : Configuration (Term csig) ℕ}
    {reads : List (ℕ × Term csig)} (stored : ∀ p ∈ reads, label p.1 = p.2) {l u : Term csig} {made : ℕ}
    {concl : Term csig} {G : Subst csig → Prop} {σ : Subst csig} (before : (A csig).Models σ C.equations)
    (told : σ.applyTerm l = σ.applyTerm u) :
    (A csig).Models σ ((unifyFiring reads l u made concl G).firing.result label C).equations :=
  (unifyFiring_models_iff label C stored l u made concl G σ).mpr ⟨before, told⟩

theorem start_principal (present : Finset ℕ) :
    (A csig).Principal (⟨[], present⟩ : Configuration (Term csig) ℕ).equations (Subst.id csig) :=
  ⟨(fun _ member => by cases member), fun δ _ => ⟨δ, fun t => by
    show δ.applyTerm t = (δ ∘ₛ Subst.id csig).applyTerm t
    rw [Subst.comp_id_right]⟩⟩

/-! ## Control 1: a refutation through lifting -/

/-- `p(x₀) ≈ x₀`. -/
def pxx : NClause csig := [⟨false, p (x 0), x 0⟩]
/-- `p(b) ≉ b`. -/
def pbNeB : NClause csig := [⟨true, p b, b⟩]
/-- The copy renamed apart: `p(x₁) ≈ x₁`. -/
def pxxCopy : NClause csig := [⟨false, p (x 1), x 1⟩]

def θb : Grounding csig := fun _ => gb

theorem gb_lt_gpgb : gb < gp gb := GroundSimplification.subterm (sig := csig) Fn.p (fun _ => gb) 0

/-- **The ground instances are unsatisfiable**: the instance `x₀ ↦ b` is `p(b) ≈ b`. -/
theorem lifting_unsatisfiable :
    ¬ ∃ I : Congruence csig, ∀ C ∈ [pxx, pbNeB], ∀ θ : Grounding csig, Models I.rel (NClause.ground θ C) := by
  rintro ⟨I, holds⟩
  have symm : ∀ s t, I.rel s t → I.rel t s := fun _ _ h => I.equivalence.symm h
  have rel : I.rel (gp gb) gb := by
    have one : Models I.rel (Lit.make false (gp gb) gb ::ₘ 0) := holds pxx List.mem_cons_self θb
    rcases models_cons.mp one with h | h
    · simpa using (Lit.holds_make symm false (gp gb) gb).mp h
    · exact absurd h (not_models_zero _)
  have two : Models I.rel (Lit.make true (gp gb) gb ::ₘ 0) :=
    holds pbNeB (List.mem_cons_of_mem _ List.mem_cons_self) θb
  rcases models_cons.mp two with h | h
  · exact (by simpa using (Lit.holds_make symm true (gp gb) gb).mp h : ¬ I.rel (gp gb) gb) rel
  · exact not_models_zero _ h

/-- **The ground refutation starts with a superposition into the root of `p(b)`**: `p(b) ≈ b` into
`p(b) ≉ b`, giving `b ≉ b`. -/
theorem ground_superposition :
    Inference (some (NClause.ground θb pxxCopy)) (NClause.ground θb pbNeB)
      (NClause.ground θb [⟨true, x 1, b⟩]) := by
  have le := gb_lt_gpgb.le
  have side : NClause.ground θb pxxCopy = Lit.pos (gp gb) gb le ::ₘ 0 := by
    show Lit.make false (gp gb) gb ::ₘ 0 = _
    rw [Lit.make_false_eq_pos le]
  have mainLhs : (Lit.make true (gp gb) gb).lhs = gp gb := max_eq_left le
  have mainRhs : (Lit.make true (gp gb) gb).rhs = gb := min_eq_right le
  have inference := Inference.negSup (l := gp gb) (r := gb) 0 0 (Lit.make true (gp gb) gb) Ctx.hole
    gb_lt_gpgb (fun M member => absurd member (Multiset.notMem_zero M)) rfl mainLhs
    (by rw [mainLhs, mainRhs]; exact gb_lt_gpgb) (fun M member => absurd member (Multiset.notMem_zero M))
  rw [mainRhs, add_zero] at inference
  rw [side]
  exact inference

def mu1 : Subst csig := Subst.single 1 b

theorem mu1_principal : (A csig).Principal [(p (x 1), p b)] mu1 := unary_principal Fn.p 0 1 2

theorem conditions1 : supConditions ord.toStableOrder (p b) (p (x 1)) (x 1) [] ⟨true, p b, b⟩ [] mu1 :=
  ⟨(fun v h => by cases h),
    show ¬ ord.toStableOrder.ge b (p b) from not_ge_const 2 (by intro h; cases h),
    show ¬ ord.toStableOrder.ge b (p b) from not_ge_const 2 (by intro h; cases h),
    (fun M member => by cases member),
    (fun _ M member => by cases member),
    fun positive => absurd positive (by decide)⟩

theorem factors1 : groundAfter θb mu1 = θb := by
  funext v
  show θb.groundTerm (Subst.single 1 b v) = gb
  by_cases h : v = 1
  · rw [h, Subst.single_eq (σ := csig)]
    rfl
  · rw [Subst.single_ne (σ := csig) _ h]
    rfl

/-- **The lifted superposition**: the copy `p(x₁) ≈ x₁`, told `p(x₁) = p(b)`, unifier `x₁ ↦ b`. -/
def lift1 : SupLift ord.toStableOrder θb pxxCopy pbNeB (NClause.ground θb [⟨true, x 1, b⟩]) where
  D' := []
  C' := []
  L := ⟨true, p b, b⟩
  c := .hole
  u := p b
  l := p (x 1)
  r := x 1
  μ := mu1
  ν := θb
  side_reorient := reorient_refl _
  main_reorient := reorient_refl _
  at_position := rfl
  principal := mu1_principal
  conditions := conditions1
  factors := factors1
  conclusion := rfl

def label1 : ℕ → Term csig
  | 0 => code.encode pxx
  | 1 => code.encode pbNeB
  | 2 => code.encode (supConclusion .hole (x 1) [] ⟨true, p b, b⟩ [])
  | _ => code.encode []

def start1 : Configuration (Term csig) ℕ := ⟨[], {0, 1}⟩

/-- **The lifted superposition is an admitted firing of the shared store**, and its made clause read at
the result's principal answer has the ground conclusion `b ≉ b` as an instance. -/
theorem lifted_firing_admitted :
    (guarded (A csig) label1).Admits (s := start1)
        (supFiring ord.toStableOrder code (0, label1 0) (1, label1 1) 2 lift1.c lift1.u lift1.l lift1.r
          lift1.D' lift1.L lift1.C') ∧
      (A csig).Principal ((supFiring ord.toStableOrder code (0, label1 0) (1, label1 1) 2 lift1.c lift1.u
        lift1.l lift1.r lift1.D' lift1.L lift1.C').firing.result label1 start1).equations
        (mu1 ∘ₛ Subst.id csig) ∧
      (mu1 ∘ₛ Subst.id csig).applyTerm (label1 2) =
        code.encode ((supConclusion lift1.c lift1.r lift1.D' lift1.L lift1.C').subst mu1) ∧
      NClause.ground θb ((supConclusion lift1.c lift1.r lift1.D' lift1.L lift1.C').subst mu1) =
        NClause.ground θb [⟨true, x 1, b⟩] :=
  lift1.admitted label1 code (start_principal _) ⟨rfl, rfl⟩ ⟨by decide, by decide⟩
    ⟨fixes_id _, fixes_id _⟩ (by decide) rfl

def fire1 : GuardedFiring (Term csig) (Subst csig) ℕ :=
  supFiring ord.toStableOrder code (0, label1 0) (1, label1 1) 2 .hole (p b) (p (x 1)) (x 1) [] ⟨true, p b, b⟩ []

def after1 : Configuration (Term csig) ℕ := fire1.firing.result label1 start1

/-- **Equality resolution on the derived clause** `x₁ ≉ b`, whose variable the knowledge binds. -/
def resolve1 : GuardedFiring (Term csig) (Subst csig) ℕ :=
  eqResFiring ord.toStableOrder code (2, label1 2) 3 ⟨true, x 1, b⟩ []

theorem resolve1_admitted : (guarded (A csig) label1).Admits (s := after1) resolve1 :=
  unifyFiring_admits_of_consistent label1 (by simp [label1]) (by intro r member; simp at member; rcases member with rfl; decide)
    (by decide) rfl
    (models_result (by simp [label1]) (fun _ member => by cases member) rfl)
    (show mu1.applyTerm (x 1) = mu1.applyTerm b from rfl) (var_principal 1 2)
    ⟨rfl, (fun _ member => by cases member)⟩

/-- **The refutation**: two firings of the guarded step make the empty clause. -/
theorem lifting_refutation :
    ∃ r : (guarded (A csig) label1).Run start1, 3 ∈ r.last.present ∧ label1 3 = code.encode [] :=
  ⟨.cons fire1 lifted_firing_admitted.1 (.cons resolve1 resolve1_admitted (.nil _)), by decide, rfl⟩

/-! ## Control 2: the variable-overlap case -/

/-- `a ≈ ⊤`. -/
def aTop : NClause csig := [⟨false, a, top⟩]
/-- `q(x₀) ≉ ⊤`. -/
def qxNeTop : NClause csig := [⟨true, q (x 0), top⟩]

def θa : Grounding csig := fun _ => ga

/-- The context `q(□)` of the variable `x₀` in `q(x₀)`. -/
def cq : FirstOrderRewriting.Context csig := .app Fn.q (fun _ => x 0) 0 .hole

theorem gtop_lt_ga : gtop < ga := by
  show interp codes gtop < interp codes ga
  decide

theorem ga_lt_gqga : ga < gq ga := GroundSimplification.subterm (sig := csig) Fn.q (fun _ => ga) 0

/-- The conclusion `q(⊤) ≉ ⊤`. -/
def E2 : Clause (GroundTerm csig) :=
  Lit.make true ((groundCtx θa cq).fill (Ctx.hole.fill gtop)) (θa.groundTerm top) ::ₘ
    (0 + NClause.ground θa ([] ++ []))

theorem gqga_fill : (groundCtx θa cq).fill ga = gq ga := by
  show GroundTerm.app Fn.q (Function.update (fun _ => ga) 0 ga) = GroundTerm.app Fn.q fun _ => ga
  rw [Function.update_eq_self]

/-- **The ground superposition at a variable position**: `a ≈ ⊤` into `q(a) ≉ ⊤`, at the argument of
`q`, which is the instance of the variable `x₀`. -/
theorem overlap_inference :
    Inference (some (NClause.ground θa aTop)) (NClause.ground θa qxNeTop) E2 := by
  have le := gtop_lt_ga.le
  have side : NClause.ground θa aTop = Lit.pos ga gtop le ::ₘ 0 := by
    show Lit.make false ga gtop ::ₘ 0 = _
    rw [Lit.make_false_eq_pos le]
  have lt : gtop < gq ga := gtop_lt_ga.trans ga_lt_gqga
  have mainLhs : (Lit.make true (gq ga) gtop).lhs = gq ga := max_eq_left lt.le
  have mainRhs : (Lit.make true (gq ga) gtop).rhs = gtop := min_eq_right lt.le
  have inference := Inference.negSup (l := ga) (r := gtop) 0 0 (Lit.make true (gq ga) gtop)
    (groundCtx θa cq) gtop_lt_ga (fun M member => absurd member (Multiset.notMem_zero M)) rfl
    (by rw [mainLhs, gqga_fill]) (by rw [mainLhs, mainRhs]; exact lt)
    (fun M member => absurd member (Multiset.notMem_zero M))
  rw [mainRhs] at inference
  rw [side]
  exact inference

/-- **The variable-overlap superposition is redundant** with respect to the ground instances of
`{a ≈ ⊤, q(x₀) ≉ ⊤}`: its conclusion follows from `a ≈ ⊤` and the smaller instance `q(⊤) ≉ ⊤`. -/
theorem overlap_is_redundant :
    RedundantInference (groundInstances {aTop, qxNeTop}) (NClause.ground θa qxNeTop) E2 := by
  refine overlap_redundant (Dc := aTop) ⟨ga, gtop, 0, [], [], ⟨true, q (x 0), top⟩, ⟨true, q (x 0), top⟩,
    cq, 0, .hole, gtop_lt_ga, rfl, rfl, Or.inl rfl, ?_, ?_, rfl, rfl⟩
    (ground_mem_groundInstances (Or.inl rfl) θa)
    (fun θ' => ground_mem_groundInstances (Or.inr rfl) θ')
  · intro K member
    rw [show NClause.ground θa aTop = Lit.make false ga gtop ::ₘ 0 from rfl, Multiset.mem_cons] at member
    rcases member with rfl | none
    · apply Lit.lt_of_lhs_lt
      show max ga gtop < max (gq ga) gtop
      rw [max_eq_left gtop_lt_ga.le, max_eq_left (gtop_lt_ga.trans ga_lt_gqga).le]
      exact ga_lt_gqga
    · exact absurd none (Multiset.notMem_zero K)
  · show Term.app Fn.q (fun _ => x 0) = Term.app Fn.q (Function.update (fun _ => x 0) 0 (Term.var 0))
    congr 1
    funext i
    by_cases h : i = 0
    · rw [h, Function.update_self]
      rfl
    · rw [Function.update_of_ne h]

/-- **No non-ground superposition lifts it**: the rewritten term `a` does not unify with `q(x₀)`, the only
non-variable subterm of the instantiated side. -/
theorem no_unifier (σ : Subst csig) : σ.applyTerm a ≠ σ.applyTerm (q (x 0)) := by
  intro same
  cases same

/-! ## Control 3: a co-stable side condition fails at an instance; the closure guard admits it -/

/-- The side conditions of superposing `p(x₁) ≈ x₂` into `p(b) ≉ b` at the root. -/
def guard3 : Subst csig → Prop :=
  supConditions ord.toStableOrder (p b) (p (x 1)) (x 2) [] ⟨true, p b, b⟩ []

/-- **They hold at the most general unifier `x₁ ↦ b`.** -/
theorem condition_at_mgu : guard3 mu1 :=
  ⟨(fun v h => by cases h),
    show ¬ ord.toStableOrder.ge (x 2) (p b) from not_ge_var 2 (by intro h; cases h),
    show ¬ ord.toStableOrder.ge b (p b) from not_ge_const 2 (by intro h; cases h),
    (fun M member => by cases member),
    (fun _ M member => by cases member),
    fun positive => absurd positive (by decide)⟩

/-- The instance `x₁ ↦ b`, `x₂ ↦ q(p(b))`. -/
def bump : Subst csig := fun v => if v = 1 then b else if v = 2 then q (p b) else .var v

theorem bump_solves : (A csig).Models bump [(p (x 1), p b)] := by
  intro e member
  rw [List.mem_singleton.mp member]
  rfl

/-- **They fail at the instance `x₂ ↦ q(p(b))`**: there `x₂` lies above `p(x₁)`. -/
theorem condition_fails_at_instance : ¬ guard3 bump := by
  rintro ⟨-, notAbove, -⟩
  exact notAbove (Or.inl (show StrictSubterm (q (p b)) (p b) from StrictSubterm.arg (sig := csig) Fn.q (fun _ => p b) 0))

/-- **Asked at every solution, the bare condition is refused.** -/
theorem bare_guard_refused : ¬ (A csig).Entails [(p (x 1), p b)] guard3 :=
  fun asked => condition_fails_at_instance (asked bump bump_solves)

/-- **Its closure, asked at every solution, is entailed.** -/
theorem closure_guard_entailed : (A csig).Entails [(p (x 1), p b)] (Closure (A csig) [(p (x 1), p b)] guard3) :=
  (entails_closure_iff mu1_principal (respects_firstOrder _) (supConditions_coStable _ _ _ _ _ _ _)).mpr
    condition_at_mgu

def label3 : ℕ → Term csig
  | 0 => code.encode [⟨false, p (x 1), x 2⟩]
  | 1 => code.encode pbNeB
  | 2 => code.encode (supConclusion .hole (x 2) [] ⟨true, p b, b⟩ [])
  | _ => code.encode []

/-- **The firing guarded by the closure is admitted.** -/
theorem guarded_superposition_admitted :
    (guarded (A csig) label3).Admits (s := ⟨[], {0, 1}⟩)
      (supFiring ord.toStableOrder code (0, label3 0) (1, label3 1) 2 .hole (p b) (p (x 1)) (x 2) []
        ⟨true, p b, b⟩ []) :=
  (sup_admits_iff ord.toStableOrder label3 code (start_principal _) ⟨rfl, rfl⟩
    ⟨Subst.applyTerm_id _, Subst.applyTerm_id _⟩ 2 .hole [] ⟨true, p b, b⟩ []).mpr
    ⟨by decide, by decide, by decide, rfl, mu1, mu1_principal, condition_at_mgu⟩

/-! ## Control 4: `p(x) ∨ q(x)`, `¬p(a)`, `¬q(a)` on the shared step -/

def label4 : ℕ → Term csig
  | 0 => code.encode [⟨false, p (x 0), top⟩, ⟨false, q (x 0), top⟩]
  | 1 => code.encode [⟨true, p a, top⟩]
  | 2 => code.encode [⟨true, q a, top⟩]
  | 3 => code.encode (supConclusion .hole top [⟨false, q (x 1), top⟩] ⟨true, p a, top⟩ [])
  | 4 => code.encode [⟨false, q (x 1), top⟩]
  | 5 => code.encode (supConclusion .hole top [] ⟨true, q a, top⟩ [])
  | _ => code.encode []

def start4 : Configuration (Term csig) ℕ := ⟨[], {0, 1, 2}⟩

def mu4 : Subst csig := Subst.single 1 a

/-- Superposition of the copy `p(x₁) ≈ ⊤ ∨ q(x₁) ≈ ⊤` into `p(a) ≉ ⊤`. -/
def step1 : GuardedFiring (Term csig) (Subst csig) ℕ :=
  supFiring ord.toStableOrder code (0, label4 0) (1, label4 1) 3 .hole (p a) (p (x 1)) top
    [⟨false, q (x 1), top⟩] ⟨true, p a, top⟩ []

theorem step1_admitted : (guarded (A csig) label4).Admits (s := start4) step1 := by
  refine (sup_admits_iff ord.toStableOrder label4 code (start_principal _) ⟨rfl, rfl⟩
    ⟨Subst.applyTerm_id _, Subst.applyTerm_id _⟩ 3 .hole [⟨false, q (x 1), top⟩] ⟨true, p a, top⟩ []).mpr
    ⟨by decide, by decide, by decide, rfl, mu4, unary_principal Fn.p 0 1 1, (fun v h => by cases h),
      show ¬ ord.toStableOrder.ge top (p a) from not_ge_const 0 (by intro h; cases h),
      show ¬ ord.toStableOrder.ge top (p a) from not_ge_const 0 (by intro h; cases h), ?_,
      (fun _ M member => by cases member), fun positive => absurd positive (by decide)⟩
  intro M member
  rw [List.mem_singleton.mp member]
  show ¬ (SidesBelow StrictSubterm ⟨false, q a, top⟩ ⟨false, p a, top⟩ ∨
    (⟨false, q a, top⟩ : NLit csig) = ⟨false, p a, top⟩)
  rintro (⟨first | first, -⟩ | same)
  · rcases strictSubterm_unary first with h | h
    · cases h
    · exact not_strictSubterm_const 1 _ h
  · exact not_strictSubterm_const 0 _ first
  · cases same

def after4a : Configuration (Term csig) ℕ := step1.firing.result label4 start4

/-- Equality resolution on `⊤ ≉ ⊤ ∨ q(x₁) ≈ ⊤`. -/
def step2 : GuardedFiring (Term csig) (Subst csig) ℕ :=
  eqResFiring ord.toStableOrder code (3, label4 3) 4 ⟨true, top, top⟩ [⟨false, q (x 1), top⟩]

theorem knowledge4a : (A csig).Models mu4 after4a.equations :=
  models_result (by simp [label4]) (fun _ member => by cases member)
    (show mu4.applyTerm (p (x 1)) = mu4.applyTerm (p a) from rfl)

theorem step2_admitted : (guarded (A csig) label4).Admits (s := after4a) step2 := by
  refine unifyFiring_admits_of_consistent label4 (by simp [label4]) (by intro r member; simp at member; rcases member with rfl; decide)
    (by decide) rfl knowledge4a rfl (id_principal top) ⟨rfl, ?_⟩
  intro M member
  rw [List.mem_singleton.mp member]
  show ¬ SidesBelow StrictSubterm ⟨false, q (x 1), top⟩ ⟨true, top, top⟩
  rintro ⟨first | first, -⟩
  · rcases strictSubterm_unary first with h | h
    · cases h
    · exact not_strictSubterm_var 1 _ h
  · exact not_strictSubterm_const 0 _ first

def after4b : Configuration (Term csig) ℕ := step2.firing.result label4 after4a

/-- Superposition of `q(x₁) ≈ ⊤` (with `x₁ = a` in the knowledge) into `q(a) ≉ ⊤`. -/
def step3 : GuardedFiring (Term csig) (Subst csig) ℕ :=
  supFiring ord.toStableOrder code (4, label4 4) (2, label4 2) 5 .hole (q a) (q (x 1)) top [] ⟨true, q a, top⟩ []

theorem knowledge4b : (A csig).Models mu4 after4b.equations :=
  models_result (by simp [label4]) knowledge4a rfl

theorem step3_admitted : (guarded (A csig) label4).Admits (s := after4b) step3 :=
  unifyFiring_admits_of_consistent label4 (by simp [label4]) (by intro r member; simp at member; rcases member with rfl | rfl <;> decide)
    (by decide) rfl knowledge4b (show mu4.applyTerm (q (x 1)) = mu4.applyTerm (q a) from rfl)
    (unary_principal Fn.q 0 1 1)
    ⟨(fun v h => by cases h),
      show ¬ ord.toStableOrder.ge top (q a) from not_ge_const 0 (by intro h; cases h),
      show ¬ ord.toStableOrder.ge top (q a) from not_ge_const 0 (by intro h; cases h),
      (fun M member => by cases member),
      (fun _ M member => by cases member),
      fun positive => absurd positive (by decide)⟩

def after4c : Configuration (Term csig) ℕ := step3.firing.result label4 after4b

/-- Equality resolution on `⊤ ≉ ⊤`. -/
def step4 : GuardedFiring (Term csig) (Subst csig) ℕ :=
  eqResFiring ord.toStableOrder code (5, label4 5) 6 ⟨true, top, top⟩ []

theorem knowledge4c : (A csig).Models mu4 after4c.equations :=
  models_result (by simp [label4]) knowledge4b rfl

theorem step4_admitted : (guarded (A csig) label4).Admits (s := after4c) step4 :=
  unifyFiring_admits_of_consistent label4 (by simp [label4])
    (by intro r member; simp at member; rcases member with rfl; decide) (by decide) rfl knowledge4c rfl
    (id_principal top) ⟨rfl, (fun _ member => by cases member)⟩

/-- **`p(x) ∨ q(x)`, `¬p(a)`, `¬q(a)` is refuted**: four firings of the guarded step make the empty
clause. -/
theorem refutation_run :
    ∃ r : (guarded (A csig) label4).Run start4, 6 ∈ r.last.present ∧ label4 6 = code.encode [] :=
  ⟨.cons step1 step1_admitted (.cons step2 step2_admitted (.cons step3 step3_admitted
    (.cons step4 step4_admitted (.nil _)))), by decide, rfl⟩

#print axioms fnCode_injective
#print axioms encode_subst
#print axioms strictSubterm_exists_arg
#print axioms strictSubterm_unary
#print axioms unary_principal
#print axioms var_principal
#print axioms lifting_unsatisfiable
#print axioms ground_superposition
#print axioms lifted_firing_admitted
#print axioms resolve1_admitted
#print axioms lifting_refutation
#print axioms overlap_inference
#print axioms overlap_is_redundant
#print axioms no_unifier
#print axioms condition_at_mgu
#print axioms condition_fails_at_instance
#print axioms bare_guard_refused
#print axioms closure_guard_entailed
#print axioms guarded_superposition_admitted
#print axioms step1_admitted
#print axioms step2_admitted
#print axioms step3_admitted
#print axioms step4_admitted
#print axioms refutation_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition.LiftingControls
