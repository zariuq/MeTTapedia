import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Groundable

/-!
# Groundable up to bisimilarity: every finite program

A program that makes fresh identities has infinitely many successors on the nose, finitely many up
to bisimilarity (`ProgramAdequacy.program_imageFiniteBisimilar`). Groundability transfers through
the bisimulation quotient.

* **The quotient** (`bisimSetoid`, `quotientLTS`): classes of bisimilar states step when
  representatives do. The class map is a zigzag map (`class_isZigzag`): a step of a class is matched
  by a step of every representative, because bisimilarity is a bisimulation. A system with finite
  covers of successors up to bisimilarity has an image-finite quotient (`quotient_imageFinite`).
* **Stages pull back** (`lower_pull`, `upper_pull`): for an environment closed under bisimilarity
  (`EnvClosed`), such as the atoms of a system (`atomEnv_closed`), every unfolding of a plain body on
  the system is the preimage of the same unfolding on the quotient (`FixpointTypes.satisfies_pull`).
* **Groundable up to bisimilarity** (`satisfies_mu_iff_exists_stage_upTo`,
  `satisfies_nu_iff_forall_stage_upTo`): on every system with finite covers up to bisimilarity, a
  least fixed point of a plain body is found at a finite unfolding and a greatest one refuted at one.
* **Every finite program on the first-order step** (`program_mu_groundable`,
  `program_nu_refutable`): under the hypotheses of `ProgramAdequacy.program_adequacy` (fresh
  identities for every label, a finite rule set, observations invariant under label-keeping
  renaming).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.GroundableUpTo

open Set
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean (bodyOrderHom)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary (fixedPointsPositive)
open Mettapedia.GSLT
open FixpointTypes Groundable

universe uG uA uL

section Plain

variable {Act : Type*}

theorem fixedPointsPositive_of_plain : ∀ {n : ℕ} (φ : Formula Act n), plain φ = true →
    fixedPointsPositive φ = true
  | _, .tt, _ => rfl
  | _, .ff, _ => rfl
  | _, .var _, _ => rfl
  | _, .conj a b, p => by
      simp only [plain, Bool.and_eq_true] at p
      show (fixedPointsPositive a && fixedPointsPositive b) = true
      rw [fixedPointsPositive_of_plain a p.1, fixedPointsPositive_of_plain b p.2]
      rfl
  | _, .disj a b, p => by
      simp only [plain, Bool.and_eq_true] at p
      show (fixedPointsPositive a && fixedPointsPositive b) = true
      rw [fixedPointsPositive_of_plain a p.1, fixedPointsPositive_of_plain b p.2]
      rfl
  | _, .diamond _ a, p => fixedPointsPositive_of_plain a p
  | _, .box _ a, p => fixedPointsPositive_of_plain a p
  | _, .neg _, p => by simp [plain] at p
  | _, .mu _, p => by simp [plain] at p
  | _, .nu _, p => by simp [plain] at p

theorem mu_positive_of_plain {n : ℕ} (body : Formula Act (n + 1)) (p : plain body = true) :
    fixedPointsPositive (.mu body) = true := by
  show (body.isPositive && fixedPointsPositive body) = true
  rw [show body.isPositive = true from isPositiveIn_of_plain body p 0, fixedPointsPositive_of_plain body p]
  rfl

theorem nu_positive_of_plain {n : ℕ} (body : Formula Act (n + 1)) (p : plain body = true) :
    fixedPointsPositive (.nu body) = true := by
  show (body.isPositive && fixedPointsPositive body) = true
  rw [show body.isPositive = true from isPositiveIn_of_plain body p 0, fixedPointsPositive_of_plain body p]
  rfl

end Plain

variable {G : GSLT.{uG}} (M : HennessyMilner.System.{uA, uL} G)

/-! ## The bisimulation quotient -/

/-- Bisimilarity as a setoid. -/
def bisimSetoid : Setoid G.Term where
  r := M.Bisimilar
  iseqv := ⟨M.bisimilar_refl, M.bisimilar_symm, M.bisimilar_trans⟩

/-- **The bisimulation quotient**: classes step when representatives do. -/
def quotientLTS : LTS (Quotient (bisimSetoid M)) M.Label where
  trans a l b := ∃ s t, Quotient.mk _ s = a ∧ Quotient.mk _ t = b ∧ M.act l s t

/-- **The class map is a zigzag map.** -/
theorem class_isZigzag : IsZigzag (ltsOf M) (quotientLTS M) (Quotient.mk (bisimSetoid M)) where
  forth s _ t step := ⟨s, t, rfl, rfl, step⟩
  back s l _ := by
    rintro ⟨s', t', same, rfl, step⟩
    obtain ⟨R, bisimulation, related⟩ := M.bisimilar_symm (Quotient.exact same)
    obtain ⟨t, step', related'⟩ := bisimulation.2.1 related l step
    exact ⟨t, step', Quotient.sound ⟨R, bisimulation, related'⟩⟩

/-- **Finite covers up to bisimilarity make the quotient image-finite.** -/
theorem quotient_imageFinite (finite : M.ImageFiniteBisimilar) : ImageFinite (quotientLTS M) := by
  intro a l
  refine Quotient.inductionOn a fun s => ?_
  obtain ⟨reps, repsFinite, covers⟩ := finite l s
  refine (repsFinite.image (Quotient.mk (bisimSetoid M))).subset ?_
  intro b step
  obtain ⟨t, step', rfl⟩ := (class_isZigzag M).back s l b step
  obtain ⟨r, member, bisimilar⟩ := covers step'
  exact ⟨r, member, (Quotient.sound bisimilar).symm⟩

/-! ## Environments closed under bisimilarity -/

/-- An environment whose sets are closed under bisimilarity. -/
def EnvClosed {n : ℕ} (ρ : Env G.Term n) : Prop := ∀ i s t, M.Bisimilar s t → s ∈ ρ i → t ∈ ρ i

/-- Its sets, read on classes. -/
def quotientEnv {n : ℕ} (ρ : Env G.Term n) : Env (Quotient (bisimSetoid M)) n :=
  fun i => {a | ∃ s ∈ ρ i, Quotient.mk _ s = a}

variable {M}

theorem mem_pull_quotientEnv {n : ℕ} {ρ : Env G.Term n} (closed : EnvClosed M ρ) (i : Fin n)
    (s : G.Term) : s ∈ pullEnv (Quotient.mk (bisimSetoid M)) (quotientEnv M ρ) i ↔ s ∈ ρ i := by
  constructor
  · rintro ⟨s', inside, same⟩
    exact closed i s' s (Quotient.exact same) inside
  · intro inside
    exact ⟨s, inside, rfl⟩

/-- **The atoms of a system are closed under bisimilarity.** -/
theorem atomEnv_closed {n : ℕ} (atoms : Fin n → M.Atom) : EnvClosed M (atomEnv M atoms) := by
  rintro i s t ⟨R, bisimulation, related⟩ inside
  exact (bisimulation.2.2 related (atoms i)).mp inside

/-! ## Stages pull back -/

section Stages

variable {n : ℕ} {ρ : Env G.Term n}

theorem body_pull (closed : EnvClosed M ρ) (body : Formula M.Label (n + 1)) (p : plain body = true)
    (L : Set (Quotient (bisimSetoid M))) (s : G.Term) :
    satisfies (ltsOf M) (ρ.extend (Quotient.mk (bisimSetoid M) ⁻¹' L)) body s ↔
      satisfies (quotientLTS M) ((quotientEnv M ρ).extend L) body (Quotient.mk _ s) := by
  refine (satisfies_congr (fun _ _ _ => Iff.rfl) (fun i t => ?_) body s).trans
    (satisfies_pull (class_isZigzag M) body (fixedPointsPositive_of_plain body p) _ s)
  exact (Env.extend_congr (fun j t' => (mem_pull_quotientEnv closed j t').symm) _ i t).trans
    (mem_pullEnv_extend _ (quotientEnv M ρ) L i t).symm

/-- **Every lower stage on the system is the preimage of the same stage on the quotient.** -/
theorem lower_pull (closed : EnvClosed M ρ) (body : Formula M.Label (n + 1)) (p : plain body = true) :
    ∀ k, lower (bodyOrderHom (ltsOf M) ρ body (isPositiveIn_of_plain body p 0)) k =
      Quotient.mk (bisimSetoid M) ⁻¹'
        lower (bodyOrderHom (quotientLTS M) (quotientEnv M ρ) body (isPositiveIn_of_plain body p 0)) k
  | 0 => rfl
  | k + 1 => by
      rw [lower_succ, lower_succ, lower_pull closed body p k]
      ext s
      exact body_pull closed body p _ s

/-- **Every upper stage on the system is the preimage of the same stage on the quotient.** -/
theorem upper_pull (closed : EnvClosed M ρ) (body : Formula M.Label (n + 1)) (p : plain body = true) :
    ∀ k, upper (bodyOrderHom (ltsOf M) ρ body (isPositiveIn_of_plain body p 0)) k =
      Quotient.mk (bisimSetoid M) ⁻¹'
        upper (bodyOrderHom (quotientLTS M) (quotientEnv M ρ) body (isPositiveIn_of_plain body p 0)) k
  | 0 => rfl
  | k + 1 => by
      rw [upper_succ, upper_succ, upper_pull closed body p k]
      ext s
      exact body_pull closed body p _ s

theorem satisfies_quotient (closed : EnvClosed M ρ) (formula : Formula M.Label n)
    (positive : fixedPointsPositive formula = true) (s : G.Term) :
    satisfies (ltsOf M) ρ formula s ↔
      satisfies (quotientLTS M) (quotientEnv M ρ) formula (Quotient.mk (bisimSetoid M) s) :=
  (satisfies_congr (fun _ _ _ => Iff.rfl) (fun i t => (mem_pull_quotientEnv closed i t).symm)
    formula s).trans (satisfies_pull (class_isZigzag M) formula positive _ s)

/-- **Groundable up to bisimilarity**: with finite covers of successors up to bisimilarity, a state
satisfies a least fixed point of a plain body exactly when a finite unfolding finds it. -/
theorem satisfies_mu_iff_exists_stage_upTo (finite : M.ImageFiniteBisimilar) (closed : EnvClosed M ρ)
    (body : Formula M.Label (n + 1)) (p : plain body = true) (s : G.Term) :
    satisfies (ltsOf M) ρ (.mu body) s ↔
      ∃ k, s ∈ lower (bodyOrderHom (ltsOf M) ρ body (isPositiveIn_of_plain body p 0)) k := by
  rw [satisfies_quotient closed _ (mu_positive_of_plain body p),
    satisfies_mu_iff_exists_stage (quotient_imageFinite M finite) (quotientEnv M ρ) body p]
  simp only [lower_pull closed body p, Set.mem_preimage]

/-- **Refutable up to bisimilarity**: with finite covers of successors up to bisimilarity, a state
fails a greatest fixed point of a plain body exactly when a finite unfolding excludes it. -/
theorem satisfies_nu_iff_forall_stage_upTo (finite : M.ImageFiniteBisimilar) (closed : EnvClosed M ρ)
    (body : Formula M.Label (n + 1)) (p : plain body = true) (s : G.Term) :
    satisfies (ltsOf M) ρ (.nu body) s ↔
      ∀ k, s ∈ upper (bodyOrderHom (ltsOf M) ρ body (isPositiveIn_of_plain body p 0)) k := by
  rw [satisfies_quotient closed _ (nu_positive_of_plain body p),
    satisfies_nu_iff_forall_stage (quotient_imageFinite M finite) (quotientEnv M ρ) body p]
  simp only [upper_pull closed body p, Set.mem_preimage]

end Stages

/-! ## Every finite program on the first-order step -/

section Programs

open ProgramAdequacy StepSpan

variable {T : Type} {S : Type} {O : Type} [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)

/-- **On the first-order step under every finite program, least fixed points of plain bodies over
the atoms are groundable.** -/
theorem program_mu_groundable (supply : Supply label) {R : Set (RuleInstance T)} (finite : R.Finite)
    {Atom : Type} (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C))
    {n : ℕ} (atoms : Fin n → Atom) (body : Formula Unit (n + 1)) (p : plain body = true)
    (C : Configuration T O) :
    satisfies (ltsOf (stepSystem (program A label R) observes))
        (atomEnv (stepSystem (program A label R) observes) atoms) (.mu body) C ↔
      ∃ k, C ∈ lower (bodyOrderHom (ltsOf (stepSystem (program A label R) observes))
        (atomEnv (stepSystem (program A label R) observes) atoms) body (isPositiveIn_of_plain body p 0)) k :=
  satisfies_mu_iff_exists_stage_upTo
    (program_imageFiniteBisimilar A label supply finite observes invariant) (atomEnv_closed atoms) body p C

/-- **And greatest fixed points of plain bodies are refutable.** -/
theorem program_nu_refutable (supply : Supply label) {R : Set (RuleInstance T)} (finite : R.Finite)
    {Atom : Type} (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C))
    {n : ℕ} (atoms : Fin n → Atom) (body : Formula Unit (n + 1)) (p : plain body = true)
    (C : Configuration T O) :
    satisfies (ltsOf (stepSystem (program A label R) observes))
        (atomEnv (stepSystem (program A label R) observes) atoms) (.nu body) C ↔
      ∀ k, C ∈ upper (bodyOrderHom (ltsOf (stepSystem (program A label R) observes))
        (atomEnv (stepSystem (program A label R) observes) atoms) body (isPositiveIn_of_plain body p 0)) k :=
  satisfies_nu_iff_forall_stage_upTo
    (program_imageFiniteBisimilar A label supply finite observes invariant) (atomEnv_closed atoms) body p C

section Instance

open Distinctions.ParityBoundary NamesOnTheStep NamesOnTheStep.IssuingControls ProgramAdequacy

/-- **An instance of the hypotheses**: the program "take one `T`", observing the knowledge. -/
theorem countDown_mu_groundable {n : ℕ} (atoms : Fin n → EquationStore Expr) (body : Formula Unit (n + 1))
    (p : plain body = true) (C : Conf) :
    satisfies (ltsOf countingKnowledge) (atomEnv countingKnowledge atoms) (.mu body) C ↔
      ∃ k, C ∈ lower (bodyOrderHom (ltsOf countingKnowledge) (atomEnv countingKnowledge atoms) body
        (isPositiveIn_of_plain body p 0)) k :=
  program_mu_groundable ground Prod.fst occSupply (Set.finite_singleton takesT) knowledgeView
    (fun _ _ _ _ => Iff.rfl) atoms body p C

end Instance

end Programs

#print axioms countDown_mu_groundable
#print axioms class_isZigzag
#print axioms quotient_imageFinite
#print axioms atomEnv_closed
#print axioms lower_pull
#print axioms upper_pull
#print axioms satisfies_quotient
#print axioms satisfies_mu_iff_exists_stage_upTo
#print axioms satisfies_nu_iff_forall_stage_upTo
#print axioms program_mu_groundable
#print axioms program_nu_refutable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.GroundableUpTo
