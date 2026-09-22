import Mettapedia.Logic.HOL.Syntax.DecidableEq
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.UniversalAlgebra.Certificate
import Mettapedia.Logic.FinitaryRuleSystem.Tree

/-!
# A qualified ground unary-equational chart of HOL

A chart registers finitely many frozen HOL expressions at one declared type,
and finitely many unary HOL operator expressions at that type. Recognition
accepts outer equality between registered atoms and registered unary application
spines, up to an explicit depth budget. Frozen expressions may themselves be
higher-order; the chart neither interprets their interiors nor erases them.

The backend is the existing universal-algebra equational certificate checker.
Accepted certificates reconstruct actual `ExtDerivation` proofs from the exact
recognized assumptions. Outer quantifiers and arbitrary HOL conversion are
outside this grammar. Node counts measure replay trees, not runtime or total HOL
proof size; witness functions are Lean data, not a serialized wire format.

False eligibility or acceptance, including exhausted depth, is chart
non-admission, never a refutation of the HOL formula.
-/

namespace Mettapedia.Logic.HOL.GroundUnaryEquationalChart

universe u v

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {τ : Ty Base}

structure Chart (Const : Ty Base → Type v) (Γ : Ctx Base) (τ : Ty Base) where
  atomCount : Nat
  unaryCount : Nat
  atoms : Fin atomCount → Term Const Γ τ
  unary : Fin unaryCount → Term Const Γ (τ ⇒ τ)

abbrev Chart.signature (c : Chart Const Γ τ) : UniversalAlgebra.Signature where
  Operation := Fin c.atomCount ⊕ Fin c.unaryCount
  arity | .inl _ => 0 | .inr _ => 1

abbrev Expr (c : Chart Const Γ τ) := UniversalAlgebra.Term c.signature
abbrev Equation (c : Chart Const Γ τ) := UniversalAlgebra.Equation c.signature

def atom (c : Chart Const Γ τ) (i : Fin c.atomCount) : Expr c :=
  .op (.inl i) Fin.elim0

def unary (c : Chart Const Γ τ) (i : Fin c.unaryCount) (t : Expr c) : Expr c :=
  .op (.inr i) (fun _ => t)

def Chart.syntaxModel (c : Chart Const Γ τ) : UniversalAlgebra.Model c.signature (Term Const Γ τ) where
  interpret | .inl i, _ => c.atoms i | .inr i, args => .app (c.unary i) (args 0)

def translate (c : Chart Const Γ τ) (ν : Nat → Term Const Γ τ) (t : Expr c) :=
  t.evaluate c.syntaxModel ν

def formula (c : Chart Const Γ τ) (ν : Nat → Term Const Γ τ) (e : Equation c) :
    Formula Const Γ := .eq (translate c ν e.1) (translate c ν e.2)

@[simp] theorem translate_atom (c : Chart Const Γ τ) (ν) (i) :
    translate c ν (atom c i) = c.atoms i := rfl

@[simp] theorem translate_unary (c : Chart Const Γ τ) (ν) (i) (t) :
    translate c ν (unary c i t) = .app (c.unary i) (translate c ν t) := rfl

/-- Rule-by-rule reconstruction, including arbitrary backend substitutions.
The premise obligation concerns only the supplied equation system. -/
theorem consequence_reconstruction (c : Chart Const Γ τ)
    (system : UniversalAlgebra.EquationSystem c.signature) {Δ : List (Formula Const Γ)}
    (licensed : ∀ e ∈ system, ∀ ν, ExtDerivation Const Δ (formula c ν e))
    {e : Equation c} (h : UniversalAlgebra.EquationalConsequence system e) :
    ∀ ν, ExtDerivation Const Δ (formula c ν e) := by
  refine Derives.least (fun e => ∀ ν, ExtDerivation Const Δ (formula c ν e)) ?_ h
  intro premises conclusion rule ih ν
  cases rule with
  | systemInstance member substitution =>
      simpa only [formula, translate, UniversalAlgebra.Term.evaluate_subst] using
        licensed _ member (fun n => translate c ν (substitution n))
  | refl t => exact .eqRefl _
  | symm left right => exact .eqSymm (ih (left, right) (by simp) ν)
  | trans left middle right =>
      exact .eqTrans (ih (left, middle) (by simp) ν) (ih (middle, right) (by simp) ν)
  | congruence operation left right =>
      cases operation with
      | inl i => exact .eqRefl _
      | inr i =>
          exact .eqAppArg (c.unary i) (ih _ (List.mem_ofFn.mpr ⟨0, rfl⟩) ν)

/-- The declared grammar, independent of recognition: registered atoms have
depth one, and a registered unary application adds one to its body's depth.
Different witnesses may describe the same HOL term, including an entire
application also registered as an atom. No uniqueness is required. -/
inductive SupportedSpine (c : Chart Const Γ τ) : Nat → Term Const Γ τ → Prop where
  | atom (i : Fin c.atomCount) : SupportedSpine c 1 (c.atoms i)
  | unary (i : Fin c.unaryCount) {depth : Nat} {body : Term Const Γ τ}
      (supported : SupportedSpine c depth body) :
      SupportedSpine c (depth + 1) (.app (c.unary i) body)

structure ReifiedTerm (c : Chart Const Γ τ) (source : Term Const Γ τ) where
  term : Expr c
  roundtrip : ∀ ν, translate c ν term = source

structure ReifiedEquation (c : Chart Const Γ τ) (source : Formula Const Γ) where
  equation : Equation c
  roundtrip : ∀ ν, formula c ν equation = source

variable [DecidableEq Base] [∀ σ, DecidableEq (Const σ)]

/-- Atoms take priority over application decomposition. A zero budget rejects
even an atom; a successor budget permits one registered node. -/
def reifyTerm (c : Chart Const Γ τ) : (fuel : Nat) → (t : Term Const Γ τ) →
    Option (ReifiedTerm c t)
  | 0, _ => none
  | fuel + 1, t =>
      match (List.finRange c.atomCount).findSome? (fun i =>
        if h : c.atoms i = t then some ⟨atom c i, fun _ => h⟩ else none) with
      | some result => some result
      | none =>
          match t with
          | @Term.app _ _ _ σ _ f x =>
              if h : σ = τ then by
                subst σ
                exact (List.finRange c.unaryCount).findSome? (fun i =>
                  if head : c.unary i = f then
                    (reifyTerm c fuel x).map (fun result =>
                      ⟨unary c i result.term, fun ν => by
                        simp only [translate_unary, result.roundtrip, head]⟩)
                  else none)
              else none
          | _ => none

/-- Every spine in the declared grammar is recognized at any sufficient
depth budget. Duplicate registrations and atom-priority shortcuts are allowed;
the result is not required to use the witness's particular inventory indices. -/
theorem reifyTerm_complete (c : Chart Const Γ τ) {depth fuel : Nat}
    {t : Term Const Γ τ} (supported : SupportedSpine c depth t)
    (adequate : depth ≤ fuel) : (reifyTerm c fuel t).isSome = true := by
  induction supported generalizing fuel with
  | atom i =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          unfold reifyTerm
          split
          · rfl
          · rename_i missing
            have absent := List.findSome?_eq_none_iff.mp missing i (List.mem_finRange i)
            simp at absent
  | @unary i depth body supported ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have child := ih (Nat.le_of_succ_le_succ adequate)
          unfold reifyTerm
          split
          · rfl
          · simp only [dite_true]
            apply List.findSome?_isSome_iff.mpr
            refine ⟨i, List.mem_finRange i, ?_⟩
            simpa using child

def reifyEquation (c : Chart Const Γ τ) (fuel : Nat) (φ : Formula Const Γ) :
    Option (ReifiedEquation c φ) :=
  match φ with
  | @Term.eq _ _ _ σ left right =>
      if h : σ = τ then by
        subst σ
        exact do
          let l ← reifyTerm c fuel left
          let r ← reifyTerm c fuel right
          pure ⟨(l.term, r.term), fun ν => by
            simp only [formula, l.roundtrip, r.roundtrip]⟩
      else none
  | _ => none

def eligible (c : Chart Const Γ τ) (fuel : Nat) (φ : Formula Const Γ) : Bool :=
  (reifyEquation c fuel φ).isSome

/-- Equality between any two supported spines is eligible once both depth
witnesses fit the budget. This is grammar completeness, not proof-search
completeness or a claim about arbitrary first-order/HOL syntax. -/
theorem eligible_complete (c : Chart Const Γ τ) {left right : Term Const Γ τ}
    {leftDepth rightDepth fuel : Nat}
    (leftSupported : SupportedSpine c leftDepth left)
    (rightSupported : SupportedSpine c rightDepth right)
    (leftAdequate : leftDepth ≤ fuel) (rightAdequate : rightDepth ≤ fuel) :
    eligible c fuel (.eq left right) = true := by
  have hl := reifyTerm_complete c leftSupported leftAdequate
  have hr := reifyTerm_complete c rightSupported rightAdequate
  cases el : reifyTerm c fuel left <;> simp only [el, Option.isSome_none,
    Bool.false_eq_true] at hl
  cases er : reifyTerm c fuel right <;> simp only [er, Option.isSome_none,
    Bool.false_eq_true] at hr
  simp [eligible, reifyEquation, el, er]

structure ReifiedAssumptions (c : Chart Const Γ τ) (Δ : List (Formula Const Γ)) where
  system : UniversalAlgebra.EquationSystem c.signature
  source : ∀ e ∈ system, ∀ ν, formula c ν e ∈ Δ

def reifyAssumptions (c : Chart Const Γ τ) (fuel : Nat) :
    (Δ : List (Formula Const Γ)) → Option (ReifiedAssumptions c Δ)
  | [] => some ⟨⟨[]⟩, by intro e h; cases h⟩
  | φ :: Δ => do
      let h ← reifyEquation c fuel φ
      let hs ← reifyAssumptions c fuel Δ
      pure ⟨⟨h.equation :: hs.system.equations⟩, by
        intro e member ν
        change e ∈ h.equation :: hs.system.equations at member
        rcases List.mem_cons.mp member with rfl | member
        · rw [h.roundtrip]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs.source _ member ν)⟩

abbrev Certificate (c : Chart Const Γ τ) (system : UniversalAlgebra.EquationSystem c.signature) :=
  Mettapedia.Logic.Derivation (Equation c) (UniversalAlgebra.EquationalRuleWitness system)

/-- Replay is bound to the complete ordered assumption list and the requested
goal, not merely to an equation certificate accepted in some other environment. -/
def accepts (c : Chart Const Γ τ) (fuel : Nat) (Δ : List (Formula Const Γ))
    (φ : Formula Const Γ) (system : UniversalAlgebra.EquationSystem c.signature)
    (certificate : Certificate c system) : Bool :=
  match reifyAssumptions c fuel Δ, reifyEquation c fuel φ with
  | some hs, some goal =>
      decide (hs.system.equations = system.equations) &&
      decide (goal.equation = certificate.concl) &&
      certificate.valid (UniversalAlgebra.equationalRuleInterface system)
  | _, _ => false

/-- Acceptance reconstructs a proof in the original object HOL syntax from
proofs of the declared source assumptions. Reconstruction of the conclusion
is proved below, not supplied as part of the chart. -/
theorem accepts_reconstruct_licensed (c : Chart Const Γ τ) (fuel : Nat)
    (assumptions : List (Formula Const Γ)) (φ : Formula Const Γ)
    (system : UniversalAlgebra.EquationSystem c.signature) (certificate : Certificate c system)
    (accepted : accepts c fuel assumptions φ system certificate = true)
    {Δ : List (Formula Const Γ)}
    (sourceProofs : ∀ ψ ∈ assumptions, ExtDerivation Const Δ ψ)
    (ν : Nat → Term Const Γ τ) : ExtDerivation Const Δ φ := by
  unfold accepts at accepted
  split at accepted <;> try contradiction
  rename_i hs goal _ _
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨systemEq, goalEq⟩, valid⟩ := accepted
  have licensed : ∀ e ∈ system, ∀ ν, ExtDerivation Const Δ (formula c ν e) := by
    intro e member ν
    apply sourceProofs
    apply hs.source e
    change e ∈ hs.system.equations
    rw [systemEq]
    exact member
  have proof := consequence_reconstruction c system licensed
    (certificate.valid_sound (UniversalAlgebra.equationalRuleInterface system) valid) ν
  have hform : formula c ν certificate.concl = φ :=
    (congrArg (formula c ν) goalEq.symm).trans (goal.roundtrip ν)
  exact hform ▸ proof

theorem accepts_reconstruct (c : Chart Const Γ τ) (fuel : Nat)
    (Δ : List (Formula Const Γ)) (φ : Formula Const Γ)
    (system : UniversalAlgebra.EquationSystem c.signature) (certificate : Certificate c system)
    (accepted : accepts c fuel Δ φ system certificate = true)
    (ν : Nat → Term Const Γ τ) : ExtDerivation Const Δ φ :=
  accepts_reconstruct_licensed c fuel Δ φ system certificate accepted
    (fun _ h => .hyp h) ν

/-- The finite artifact metric is independent of HOL syntax retention. -/
def certificateNodes (c : Chart Const Γ τ) {system : UniversalAlgebra.EquationSystem c.signature}
    (certificate : Certificate c system) : Nat := certificate.nodeCount

omit [DecidableEq Base] [∀ σ, DecidableEq (Const σ)] in
theorem certificateNodes_pos (c : Chart Const Γ τ)
    {system : UniversalAlgebra.EquationSystem c.signature} (certificate : Certificate c system) :
    0 < certificateNodes c certificate := certificate.nodeCount_pos

end Mettapedia.Logic.HOL.GroundUnaryEquationalChart
