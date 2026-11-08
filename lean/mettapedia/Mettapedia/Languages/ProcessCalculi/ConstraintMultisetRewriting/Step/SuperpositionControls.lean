import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionGenerator
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionSaturation

/-!
# Controls for ground superposition

The signature has one unary function `p` and three constants `⊤ < a < b`. Its ground terms are
`pⁿ(k)`, ordered by depth and then by the constant (`key`): a linear, well-founded order compatible
with `p` and containing the subterm relation, so a ground simplification ordering.

* **An ordering side condition blocks an inference** (`blocked`, `blocked_firing`): in
  `a ≉ a ∨ b ≈ ⊤` the literal `a ≉ a` is not maximal, so equality resolution on it is refused, and no
  inference at all has this clause as its only premise. Alone, `a ≉ a` resolves to the empty clause
  (`unblocked`).
* **Demodulation takes the rewritten clause** (`demodulation_admitted`, `demodulation_takes`): the unit
  `a ≈ ⊤` rewrites `p(a) ≈ ⊤` to `p(⊤) ≈ ⊤`; the firing takes `p(a) ≈ ⊤`, which is redundant with
  respect to what remains.
* **A tautology is deleted** (`tautology_admitted`, `tautology_takes`): the firing takes `a ≈ a`.
* **A fair loop refutes what a starving one never refutes** (`fair_refutes`, `starving_never_refutes`):
  from `a ≈ ⊤` and `a ≉ ⊤`, the first-in first-out loop derives the empty clause; a policy that always
  prefers another clause and so never selects `a ≈ ⊤` never derives it (`starved`: a run that never
  selects a clause whose removal leaves a satisfiable set never derives the empty clause).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

/-! ## Starving policies -/

section Starvation

variable {sig : LPSignature} [LinearOrder (GroundTerm sig)]

/-- A step of the loop whose given clause a policy chooses. -/
def Loop.stepPick (generate : Generator sig)
    (pick : Loop sig → Option (Clause (GroundTerm sig) × List (Clause (GroundTerm sig)))) (s : Loop sig) :
    Loop sig :=
  match pick s with
  | none => s
  | some (given, rest) => ⟨given :: s.active, rest ++ generate given s.active⟩

def Loop.runPick (generate : Generator sig)
    (pick : Loop sig → Option (Clause (GroundTerm sig) × List (Clause (GroundTerm sig)))) (s : Loop sig) :
    ℕ → Loop sig
  | 0 => s
  | i + 1 => Loop.stepPick generate pick (Loop.runPick generate pick s i)

/-- A policy picks a passive clause and keeps only passive clauses in the queue. -/
def Picks (pick : Loop sig → Option (Clause (GroundTerm sig) × List (Clause (GroundTerm sig)))) : Prop :=
  ∀ s given rest, pick s = some (given, rest) → given ∈ s.passive ∧ ∀ C ∈ rest, C ∈ s.passive

theorem Entails.trans {S S' : Set (Clause (GroundTerm sig))} {C : Clause (GroundTerm sig)}
    (each : ∀ D ∈ S', Entails S D) (entails : Entails S' C) : Entails S C :=
  fun I holds => entails I fun D member => each D member I holds

/-- **A starved clause**: a run that never selects `A` derives only consequences of the other initial
clauses, so it never derives the empty clause when they are satisfiable. -/
theorem starved (generate : Generator sig) (sound : Generator.Sound generate)
    (pick : Loop sig → Option (Clause (GroundTerm sig) × List (Clause (GroundTerm sig)))) (picks : Picks pick)
    (initial : List (Clause (GroundTerm sig))) (A : Clause (GroundTerm sig))
    (never : ∀ i given rest, pick (Loop.runPick generate pick ⟨[], initial⟩ i) = some (given, rest) → given ≠ A)
    (others : ∃ I : Congruence sig, ∀ C ∈ initial, C ≠ A → Models I.rel C) (notEmpty : A ≠ 0) :
    ∀ i, (0 : Clause (GroundTerm sig)) ∉ Loop.clauses (Loop.runPick generate pick ⟨[], initial⟩ i) := by
  let S : Set (Clause (GroundTerm sig)) := {C | C ∈ initial ∧ C ≠ A}
  have invariant : ∀ i, (∀ C ∈ (Loop.runPick generate pick ⟨[], initial⟩ i).active, Entails S C) ∧
      ∀ C ∈ (Loop.runPick generate pick ⟨[], initial⟩ i).passive, C = A ∨ Entails S C := by
    intro i
    induction i with
    | zero =>
        refine ⟨fun C member => absurd member (by simp [Loop.runPick]), fun C member => ?_⟩
        by_cases same : C = A
        · exact Or.inl same
        · exact Or.inr (Entails.of_mem ⟨member, same⟩)
    | succ i ih =>
        obtain ⟨active, passive⟩ := ih
        show (∀ C ∈ (Loop.stepPick generate pick _).active, Entails S C) ∧
          ∀ C ∈ (Loop.stepPick generate pick _).passive, C = A ∨ Entails S C
        unfold Loop.stepPick
        split
        · exact ⟨active, passive⟩
        · next given rest chosen =>
          obtain ⟨inPassive, restIn⟩ := picks _ given rest chosen
          have givenEntailed : Entails S given := by
            rcases passive given inPassive with same | entailed
            · exact absurd same (never i given rest chosen)
            · exact entailed
          refine ⟨fun C member => ?_, fun C member => ?_⟩
          · rcases List.mem_cons.mp member with rfl | old
            · exact givenEntailed
            · exact active C old
          · rcases List.mem_append.mp member with kept | generated
            · exact passive C (restIn C kept)
            · refine Or.inr (Entails.trans (fun D member => ?_) (sound given _ C generated))
              rcases member with rfl | old
              · exact givenEntailed
              · exact active D old
  intro i empty
  obtain ⟨I, holds⟩ := others
  have model : ∀ D ∈ S, Models I.rel D := fun D ⟨member, ne⟩ => holds D member ne
  rcases empty with inActive | inPassive
  · exact not_models_zero I.rel ((invariant i).1 0 inActive I model)
  · rcases (invariant i).2 0 inPassive with same | entailed
    · exact notEmpty same.symm
    · exact not_models_zero I.rel (entailed I model)

end Starvation

namespace Controls

/-! ## The signature and its ordering -/

/-- One unary function `p` and the constants `⊤ = 0`, `a = 1`, `b = 2`. -/
abbrev sig : LPSignature where
  constants := Fin 3
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity _ := 1

/-- The depth of a ground term and its constant. -/
def key : GroundTerm sig → ℕ ×ₗ Fin 3
  | .const c => toLex (0, c)
  | .app _ args => toLex ((ofLex (key (args 0))).1 + 1, (ofLex (key (args 0))).2)

theorem key_injective : Function.Injective key := by
  intro s t same
  induction s generalizing t with
  | const c =>
      cases t with
      | const d =>
          simp only [key, toLex_inj] at same
          exact congrArg GroundTerm.const (congrArg Prod.snd same)
      | app f args =>
          simp only [key, toLex_inj] at same
          have depth := congrArg Prod.fst same
          simp only at depth
          omega
  | app f args ih =>
      cases t with
      | const d =>
          simp only [key, toLex_inj] at same
          have depth := congrArg Prod.fst same
          simp only at depth
          omega
      | app g args' =>
          cases f
          cases g
          simp only [key, toLex_inj] at same
          have depth := congrArg Prod.fst same
          have base := congrArg Prod.snd same
          simp only at depth base
          have keys : key (args 0) = key (args' 0) := ofLex_inj.mp (Prod.ext (by omega) base)
          have first := ih 0 keys
          congr 1
          funext i
          rw [Subsingleton.elim i 0]
          exact first

instance : LinearOrder (GroundTerm sig) := LinearOrder.lift' key key_injective

instance : WellFoundedLT (GroundTerm sig) := ⟨InvImage.wf key wellFounded_lt⟩

theorem lt_iff_key {s t : GroundTerm sig} : s < t ↔ key s < key t := Iff.rfl

instance : GroundSimplification sig where
  monotone f args i a lt := by
    cases f
    rw [Subsingleton.elim i 0] at lt ⊢
    rw [lt_iff_key] at lt ⊢
    show toLex ((ofLex (key ((Function.update args 0 a) 0))).1 + 1, (ofLex (key ((Function.update args 0 a) 0))).2) <
      toLex ((ofLex (key (args 0))).1 + 1, (ofLex (key (args 0))).2)
    rw [Function.update_self]
    rcases Prod.Lex.lt_iff.mp lt with depth | ⟨depth, base⟩
    · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp only; omega))
    · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨by simp only [depth], base⟩)
  subterm f args i := by
    cases f
    rw [Subsingleton.elim i 0, lt_iff_key]
    show toLex (ofLex (key (args 0))) < toLex ((ofLex (key (args 0))).1 + 1, (ofLex (key (args 0))).2)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp only; omega))

/-- `⊤`, `a`, `b` and `p`. -/
def top : GroundTerm sig := .const (0 : Fin 3)
def a : GroundTerm sig := .const (1 : Fin 3)
def b : GroundTerm sig := .const (2 : Fin 3)
def p (t : GroundTerm sig) : GroundTerm sig := .app () fun _ => t

theorem top_lt_a : top < a := Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by decide⟩)
theorem a_lt_b : a < b := Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by decide⟩)
theorem lt_p (t : GroundTerm sig) : t < p t := GroundSimplification.subterm () (fun _ => t) 0
theorem a_ne_top : a ≠ top := ne_of_gt top_lt_a

/-! ## An ordering side condition blocks an inference -/

/-- `a ≉ a`. -/
def aNeA : Lit (GroundTerm sig) := ⟨a, true, a, le_rfl⟩
/-- `b ≈ ⊤`. -/
def bEqTop : Lit (GroundTerm sig) := Lit.pos b top (top_lt_a.trans a_lt_b).le

theorem aNeA_ne_bEqTop : aNeA ≠ bEqTop := fun same => by
  have := congrArg Lit.negative same
  simp [aNeA, bEqTop, Lit.pos] at this

/-- **Blocked**: no inference has `a ≉ a ∨ b ≈ ⊤` as its only premise. Equality resolution on `a ≉ a`
is refused because `a ≉ a` is not maximal: `b ≈ ⊤` is larger. -/
theorem blocked (E : Clause (GroundTerm sig)) : ¬ Inference none (aNeA ::ₘ {bEqTop}) E := by
  intro inference
  have listed := mem_unary_of_inference inference
  simp only [unaryConclusions, List.mem_flatMap, Multiset.mem_toList, List.mem_append] at listed
  obtain ⟨L, member, resolved | ⟨L', inRest, factored⟩⟩ := listed
  · split_ifs at resolved with conditions
    · rcases Multiset.mem_cons.mp member with rfl | inRest
      · have bigger := conditions.2.2 bEqTop (by
          rw [Multiset.erase_cons_head]
          exact Multiset.mem_singleton_self _)
        exact absurd (Lit.lhs_le_of_le bigger) (not_le.mpr a_lt_b)
      · rw [Multiset.mem_singleton.mp inRest] at conditions
        exact absurd conditions.1 (by simp [bEqTop, Lit.pos])
    · simp at resolved
  · split_ifs at factored with conditions
    · rcases Multiset.mem_cons.mp member with rfl | inRest'
      · exact absurd conditions.1 (by simp [aNeA])
      · rw [Multiset.mem_singleton.mp inRest'] at inRest conditions
        rw [Multiset.erase_cons_tail _ aNeA_ne_bEqTop, Multiset.erase_singleton] at inRest
        rw [Multiset.mem_singleton.mp inRest] at conditions
        exact absurd conditions.2.1 (by simp [aNeA])
    · simp at factored

/-- **Unblocked**: alone, `a ≉ a` resolves to the empty clause. -/
theorem unblocked : Inference none (aNeA ::ₘ 0) 0 :=
  Inference.eqRes 0 aNeA rfl rfl fun M member => absurd member (Multiset.notMem_zero M)

/-! ## Clauses as occurrences -/

/-- `a ≈ ⊤`. -/
def unitA : Clause (GroundTerm sig) := {Lit.pos a top top_lt_a.le}
/-- `p(a) ≈ ⊤`. -/
def pa : Lit (GroundTerm sig) := Lit.pos (p a) top (top_lt_a.trans (lt_p a)).le
/-- The position of `a` in `p(a)`. -/
def ctxP : Ctx sig := .app () (fun _ => a) 0 .hole
/-- `p(⊤) ≈ ⊤`, made by demodulation. -/
def rewritten : Clause (GroundTerm sig) := Lit.make false (ctxP.fill top) top ::ₘ 0
/-- `a ≈ a`. -/
def aEqA : Lit (GroundTerm sig) := ⟨a, false, a, le_rfl⟩

/-- The labels of the occurrences. -/
def label : ℕ → Clause (GroundTerm sig)
  | 0 => aNeA ::ₘ {bEqTop}
  | 1 => unitA
  | 2 => pa ::ₘ 0
  | 3 => rewritten
  | 4 => aEqA ::ₘ 0
  | _ => 0

/-- **The blocked inference as a firing is refused.** -/
theorem blocked_firing (E : Clause (GroundTerm sig)) :
    ¬ (guarded (syntactic _) label).Admits (s := (⟨[], {0}⟩ : Configuration (Clause (GroundTerm sig)) ℕ))
      (inferFiring none (0, aNeA ::ₘ {bEqTop}) 1 E) :=
  fun admitted => blocked E ((inferFiring_admits_iff label _ none _ 1 E).mp admitted).2.2.2.2

/-! ## Demodulation takes the rewritten clause -/

theorem pa_lhs : pa.lhs = ctxP.fill a := by
  show p a = GroundTerm.app () (Function.update (fun _ => a) 0 (Ctx.fill .hole a))
  unfold p
  congr 1
  funext i
  rw [Subsingleton.elim i 0, Function.update_self]
  rfl

theorem unit_smaller : ClauseLT {Lit.pos a top top_lt_a.le} (pa ::ₘ 0) :=
  dm_of_all_below _ _ Multiset.cons_ne_zero fun y member =>
    ⟨pa, Multiset.mem_cons_self _ _, by
      rw [Multiset.mem_singleton.mp member]
      exact Lit.lt_of_lhs_lt (lt_p a)⟩

/-- The demodulation of `p(a) ≈ ⊤` by `a ≈ ⊤`. -/
def demodulate : GuardedFiring (Clause (GroundTerm sig)) Unit ℕ :=
  simplifyFiring (2, pa ::ₘ 0) [(1, unitA)] [(3, rewritten)]

/-- **The demodulation firing is admitted.** -/
theorem demodulation_admitted :
    (guarded (syntactic _) label).Admits (s := (⟨[], {1, 2}⟩ : Configuration (Clause (GroundTerm sig)) ℕ))
      demodulate := by
  refine (clauseFiring_admits_iff label _ [(2, pa ::ₘ 0)] [(1, unitA)] [(3, rewritten)] _).mpr
    ⟨List.nodup_singleton _, List.nodup_singleton _, fun q member => ?_, by simp, fun q member => ?_,
      (fun e member => by cases member), ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩
  · rw [List.mem_singleton] at member
    subst member
    exact ⟨by decide, rfl⟩
  · exact Simplification.demodulation 0 pa ctxP top_lt_a top (Or.inl ⟨pa_lhs, rfl⟩) unit_smaller

/-- **Demodulation takes `p(a) ≈ ⊤`**, which is redundant with respect to the clauses that remain. -/
theorem demodulation_takes :
    2 ∉ (demodulate.firing.result label ⟨[], {1, 2}⟩).present ∧
      Redundant (clauses label (demodulate.firing.result label ⟨[], {1, 2}⟩)) (pa ::ₘ 0) :=
  simplify_takes_redundant label demodulation_admitted

/-! ## A tautology is deleted -/

def deleteTautology : GuardedFiring (Clause (GroundTerm sig)) Unit ℕ := simplifyFiring (4, aEqA ::ₘ 0) [] []

theorem tautology_admitted :
    (guarded (syntactic _) label).Admits (s := (⟨[], {4}⟩ : Configuration (Clause (GroundTerm sig)) ℕ))
      deleteTautology := by
  refine (clauseFiring_admits_iff label _ [(4, aEqA ::ₘ 0)] [] [] _).mpr
    ⟨List.nodup_singleton _, List.nodup_nil, fun q member => ?_, by simp, by simp,
      (fun e member => by cases member), ?_⟩
  · simp only [List.append_nil, List.mem_singleton] at member
    subst member
    exact ⟨by decide, rfl⟩
  · exact Simplification.tautology (aEqA ::ₘ 0) aEqA (Multiset.mem_cons_self _ _) rfl rfl

/-- **The tautology `a ≈ a` is taken**, redundant with respect to what remains. -/
theorem tautology_takes :
    4 ∉ (deleteTautology.firing.result label ⟨[], {4}⟩).present ∧
      Redundant (clauses label (deleteTautology.firing.result label ⟨[], {4}⟩)) (aEqA ::ₘ 0) :=
  simplify_takes_redundant label tautology_admitted

/-! ## A fair loop refutes what a starving one never refutes -/

/-- `a ≉ ⊤`. -/
def notA : Clause (GroundTerm sig) := {⟨a, true, top, top_lt_a.le⟩}

/-- **`a ≈ ⊤` and `a ≉ ⊤` are unsatisfiable.** -/
theorem unsatisfiable : ¬ ∃ I : Congruence sig, ∀ C ∈ [unitA, notA], Models I.rel C := by
  rintro ⟨I, holds⟩
  obtain ⟨L, inA, holdsA⟩ := holds unitA List.mem_cons_self
  obtain ⟨M, inB, holdsB⟩ := holds notA (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [Multiset.mem_singleton.mp inA, Lit.holds_of_positive rfl] at holdsA
  rw [Multiset.mem_singleton.mp inB, Lit.holds_of_negative rfl] at holdsB
  exact holdsB holdsA

/-- Equality of ground terms is an equality interpretation. -/
def equality : Congruence sig := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩, fun c _ _ same => congrArg c.fill same⟩

/-- Without `a ≈ ⊤` the rest is satisfiable. -/
theorem others_satisfiable : ∃ I : Congruence sig, ∀ C ∈ [unitA, notA], C ≠ unitA → Models I.rel C := by
  refine ⟨equality, fun C member ne => ?_⟩
  rcases List.mem_cons.mp member with rfl | rest
  · exact absurd rfl ne
  · rw [List.mem_singleton.mp rest]
    exact ⟨_, Multiset.mem_singleton_self _, (Lit.holds_of_negative rfl).mpr a_ne_top⟩

/-- **The fair loop refutes**: first-in first-out selection derives the empty clause. -/
theorem fair_refutes :
    ∃ i, (0 : Clause (GroundTerm sig)) ∈ Loop.clauses (Loop.run generator ⟨[], [unitA, notA]⟩ i) :=
  givenClause_complete [unitA, notA] unsatisfiable

open Classical in
/-- **A starving policy**: it selects the most recent clause other than `a ≈ ⊤`. -/
noncomputable def starve (s : Loop sig) : Option (Clause (GroundTerm sig) × List (Clause (GroundTerm sig))) :=
  match (s.passive.filter fun C => decide (C ≠ unitA)).getLast? with
  | none => none
  | some g => some (g, s.passive.erase g)

theorem starve_spec {s : Loop sig} {given : Clause (GroundTerm sig)} {rest : List (Clause (GroundTerm sig))}
    (chosen : starve s = some (given, rest)) :
    given ∈ s.passive ∧ given ≠ unitA ∧ ∀ C ∈ rest, C ∈ s.passive := by
  classical
  unfold starve at chosen
  split at chosen
  · cases chosen
  · next g found =>
    simp only [Option.some.injEq, Prod.mk.injEq] at chosen
    obtain ⟨rfl, rfl⟩ := chosen
    have member := List.mem_filter.mp (List.mem_of_getLast? found)
    exact ⟨member.1, of_decide_eq_true member.2, fun C inRest => List.mem_of_mem_erase inRest⟩

theorem starve_picks : Picks starve := fun _ _ _ chosen =>
  ⟨(starve_spec chosen).1, (starve_spec chosen).2.2⟩

/-- **The starving loop never refutes** the same unsatisfiable set. -/
theorem starving_never_refutes :
    ∀ i, (0 : Clause (GroundTerm sig)) ∉ Loop.clauses (Loop.runPick generator starve ⟨[], [unitA, notA]⟩ i) :=
  starved generator generator_sound starve starve_picks [unitA, notA] unitA
    (fun _ _ _ chosen => (starve_spec chosen).2.1) others_satisfiable (Multiset.singleton_ne_zero _)

end Controls

#print axioms starved
#print axioms Controls.key_injective
#print axioms Controls.blocked
#print axioms Controls.unblocked
#print axioms Controls.blocked_firing
#print axioms Controls.demodulation_admitted
#print axioms Controls.demodulation_takes
#print axioms Controls.tautology_admitted
#print axioms Controls.tautology_takes
#print axioms Controls.unsatisfiable
#print axioms Controls.fair_refutes
#print axioms Controls.starving_never_refutes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
