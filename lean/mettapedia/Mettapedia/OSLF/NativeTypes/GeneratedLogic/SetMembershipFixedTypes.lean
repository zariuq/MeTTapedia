import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointTransport
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPlainTypeProofs

/-!
# Types of fixed-point bodies, proved in the logic of the sets

A body with fixed points is read through the tree of its subformula occurrences, each with closed formulas for its
free variables (a **node** `(φ, u)`, standing for the closed formula `φ[u]`); a fixed point's child is its body with
the fixed point itself put back for its variable, as in the guarded closure. A term's **type**, said of a set
(`fixTypeAt`), is the conjunction over the tree of each node's native formula or its negation, as the counted
evaluation of `φ[u]` at the term says (`nodeVal`).

The calculus of the package proves, with no excluded middle:

- **Native formulas move along same members** (`transferFix`).
- **Empty sets** (`emptyTree`) have the empty set's type, and **adjunction** (`adjoinTree`): a set adjoining `b` to
  `a` has the type of the term adjoining `b`'s type to `a`'s.

Each is built in two phases. A node's own literal (`adjoinHead`, `emptyHead`) is derived from the literals it depends
on: a step's from the sets' own node literals, a fixed point's from its unfolding by folding and unfolding
(`foldMu`, `unfoldMu`). A guarded body never needs its own variable there, since every occurrence lies under a step
and so at a member. The whole tree (`adjoinTree`, `emptyTree`) then reads each variable node by the literal of the
fixed point above it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member)
open Mettapedia.Logic.HOL.Term (isCore isCore_rename)

/-! ## Node values -/

/-- **The value of a node** `(φ, u)` at a term: the counted evaluation of the closed formula `φ[u]`. -/
def nodeVal {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (term : Pattern) : Bool :=
  evalCounted (formula.subst u) term

theorem nodeVal_possibly_insert {n : ℕ} (label : StepLabel) (inner : Formula n) (u : Fin n → Formula 0)
    (term whole : Pattern) :
    nodeVal (.possibly label inner) u (insertTerm term whole) =
      ((decide (memberLabel label) && nodeVal inner u term) || nodeVal (.possibly label inner) u whole) := by
  simp only [nodeVal, evalCounted, Formula.subst, evalCountedWith, insertTerm, set, membersOf, List.any_cons]
  cases decide (memberLabel label) <;> simp

theorem nodeVal_necessarily_insert {n : ℕ} (label : StepLabel) (inner : Formula n) (u : Fin n → Formula 0)
    (term whole : Pattern) :
    nodeVal (.necessarily label inner) u (insertTerm term whole) =
      ((!decide (memberLabel label) || nodeVal inner u term) && nodeVal (.necessarily label inner) u whole) := by
  simp only [nodeVal, evalCounted, Formula.subst, evalCountedWith, insertTerm, set, membersOf, List.all_cons]
  cases decide (memberLabel label) <;> simp

theorem nodeVal_possibly_empty {n : ℕ} (label : StepLabel) (inner : Formula n) (u : Fin n → Formula 0) :
    nodeVal (.possibly label inner) u (set []) = false := by
  simp [nodeVal, evalCounted, Formula.subst, evalCountedWith, set, membersOf]

theorem nodeVal_necessarily_empty {n : ℕ} (label : StepLabel) (inner : Formula n) (u : Fin n → Formula 0) :
    nodeVal (.necessarily label inner) u (set []) = true := by
  simp [nodeVal, evalCounted, Formula.subst, evalCountedWith, set, membersOf]

theorem nodeVal_mu {n : ℕ} (inner : Formula (n + 1)) (u : Fin n → Formula 0)
    (okFixed : ((Formula.mu inner).subst u).countGuarded = true)
    (okUnfolded : (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)).countGuarded = true) {term : Pattern}
    (holds : IsHF term) :
    nodeVal (.mu inner) u term = nodeVal inner (unfoldWith ((Formula.mu inner).subst u) u) term :=
  Bool.eq_iff_iff.mpr ((evalCounted_iff okFixed holds).trans ((sat_subst_mu inner u _).trans
    (evalCounted_iff okUnfolded holds).symm))

theorem nodeVal_nu {n : ℕ} (inner : Formula (n + 1)) (u : Fin n → Formula 0)
    (okFixed : ((Formula.nu inner).subst u).countGuarded = true)
    (okUnfolded : (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)).countGuarded = true) {term : Pattern}
    (holds : IsHF term) :
    nodeVal (.nu inner) u term = nodeVal inner (unfoldWith ((Formula.nu inner).subst u) u) term :=
  Bool.eq_iff_iff.mpr ((evalCounted_iff okFixed holds).trans ((sat_subst_nu inner u _).trans
    (evalCounted_iff okUnfolded holds).symm))

/-! ## Native formulas of closed formulas -/

section Closed

variable {Γ Γ' : Ctx Unit}

/-- **The native formula of a closed formula** about a set term. -/
def closedAt (formula : Formula 0) (w : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  nativeFormula formula w Fin.elim0

theorem closedAt_possibly {label : StepLabel} (labelled : memberLabel label) (inner : Formula 0)
    (w : Term Symbol Γ setTy) :
    closedAt (.possibly label inner) w =
      existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken w)) (closedAt inner (.var .vz))) := by
  simp only [closedAt, nativeFormula, if_pos labelled, native_env_irrelevant]

theorem closedAt_possibly_unlabelled {label : StepLabel} (unlabelled : ¬ memberLabel label) (inner : Formula 0)
    (w : Term Symbol Γ setTy) : closedAt (.possibly label inner) w = falsity := by
  simp only [closedAt, nativeFormula, if_neg unlabelled]

theorem closedAt_necessarily {label : StepLabel} (labelled : memberLabel label) (inner : Formula 0)
    (w : Term Symbol Γ setTy) :
    closedAt (.necessarily label inner) w =
      .all (σ := setTy) (.imp (member (.var .vz) (weaken w)) (closedAt inner (.var .vz))) := by
  simp only [closedAt, nativeFormula, if_pos labelled, native_env_irrelevant]

theorem closedAt_necessarily_unlabelled {label : StepLabel} (unlabelled : ¬ memberLabel label) (inner : Formula 0)
    (w : Term Symbol Γ setTy) : closedAt (.necessarily label inner) w = truth := by
  simp only [closedAt, nativeFormula, if_neg unlabelled]

theorem subst_closedAt (θ : Subst Symbol Γ Γ') {formula : Formula 0} (regional : formula.regional = true)
    (w : Term Symbol Γ setTy) : subst θ (closedAt formula w) = closedAt formula (subst θ w) := by
  unfold closedAt
  rw [subst_nativeFormula_regional _ formula regional, native_env_irrelevant]

theorem weaken_closedAt {σ : Ty Unit} {formula : Formula 0} (regional : formula.regional = true)
    (w : Term Symbol Γ setTy) : weaken (σ := σ) (closedAt formula w) = closedAt formula (weaken w) := by
  rw [weaken_eq_subst, subst_closedAt _ regional, ← weaken_eq_subst]

theorem instantiate_closedBody {formula : Formula 0} (regional : formula.regional = true) (t x : Term Symbol Γ setTy) :
    instantiate t (conjunctionFormula (member (.var .vz) (weaken x)) (closedAt formula (.var .vz))) =
      conjunctionFormula (member t x) (closedAt formula t) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_closedAt _ regional]
  change conjunctionFormula (member t (instantiate t (weaken x))) (closedAt formula t) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_closedAllBody {formula : Formula 0} (regional : formula.regional = true) (t x : Term Symbol Γ setTy) :
    instantiate t (.imp (member (.var .vz) (weaken x)) (closedAt formula (.var .vz))) =
      .imp (member t x) (closedAt formula t) := by
  change Term.imp (member t (instantiate t (weaken x))) (subst (Subst.single t) (closedAt formula (.var .vz))) = _
  rw [subst_closedAt _ regional, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

end Closed

/-! ## The tree of a body -/

section Tree

variable {Γ : Ctx Unit}

/-- **A node's literal**: its native formula or its negation, as its value at the term says. -/
def nodeLit {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (term : Pattern) (w : Term Symbol Γ setTy) :
    Term Symbol Γ .prop :=
  literal (nodeVal formula u term) (closedAt (formula.subst u) w)

/-- **A term's type, said of a set**: the literal of every node of the tree. -/
def fixTypeAt : {n : ℕ} → Formula n → (Fin n → Formula 0) → Pattern → Term Symbol Γ setTy → Term Symbol Γ .prop
  | _, .and left right, u, t, w =>
    conjunctionFormula (nodeLit (.and left right) u t w) (conjunctionFormula (fixTypeAt left u t w) (fixTypeAt right u t w))
  | _, .or left right, u, t, w =>
    conjunctionFormula (nodeLit (.or left right) u t w) (conjunctionFormula (fixTypeAt left u t w) (fixTypeAt right u t w))
  | _, .possibly label inner, u, t, w =>
    conjunctionFormula (nodeLit (.possibly label inner) u t w) (fixTypeAt inner u t w)
  | _, .necessarily label inner, u, t, w =>
    conjunctionFormula (nodeLit (.necessarily label inner) u t w) (fixTypeAt inner u t w)
  | _, .mu inner, u, t, w =>
    conjunctionFormula (nodeLit (.mu inner) u t w) (fixTypeAt inner (unfoldWith ((Formula.mu inner).subst u) u) t w)
  | _, .nu inner, u, t, w =>
    conjunctionFormula (nodeLit (.nu inner) u t w) (fixTypeAt inner (unfoldWith ((Formula.nu inner).subst u) u) t w)
  | _, formula, u, t, w => conjunctionFormula (nodeLit formula u t w) truth

/-- The children of a node. -/
def fixChildren : {n : ℕ} → Formula n → (Fin n → Formula 0) → Pattern → Term Symbol Γ setTy → Term Symbol Γ .prop
  | _, .and left right, u, t, w | _, .or left right, u, t, w =>
    conjunctionFormula (fixTypeAt left u t w) (fixTypeAt right u t w)
  | _, .possibly _ inner, u, t, w | _, .necessarily _ inner, u, t, w => fixTypeAt inner u t w
  | _, .mu inner, u, t, w => fixTypeAt inner (unfoldWith ((Formula.mu inner).subst u) u) t w
  | _, .nu inner, u, t, w => fixTypeAt inner (unfoldWith ((Formula.nu inner).subst u) u) t w
  | _, _, _, _, _ => truth

theorem fixTypeAt_head {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (t : Pattern) (w : Term Symbol Γ setTy) :
    fixTypeAt formula u t w = conjunctionFormula (nodeLit formula u t w) (fixChildren formula u t w) := by
  cases formula <;> rfl

variable {Δ : List (Term Symbol Γ .prop)}

/-- **The literal at a tree's root.** -/
def rootLit {n : ℕ} {formula : Formula n} {u : Fin n → Formula 0} {t : Pattern} {w : Term Symbol Γ setTy}
    (tree : Proof Δ (fixTypeAt formula u t w)) : Proof Δ (nodeLit formula u t w) :=
  conjunctionLeft (Proof.cast (fixTypeAt_head formula u t w) tree)

theorem fixTypeAt_congr : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) {t t' : Pattern},
    (∀ c ∈ closureWith u formula, evalCounted c t = evalCounted c t') →
    ∀ w : Term Symbol Γ setTy, fixTypeAt formula u t w = fixTypeAt formula u t' w := by
  intro n formula u t t' same w
  have head : nodeVal formula u t = nodeVal formula u t' := same _ (subst_mem_closureWith u formula)
  cases formula
  case and left right =>
    simp only [fixTypeAt, nodeLit, head,
      fixTypeAt_congr left u (fun c inside => same c (List.mem_cons_of_mem _ (List.mem_append_left _ inside))) w,
      fixTypeAt_congr right u (fun c inside => same c (List.mem_cons_of_mem _ (List.mem_append_right _ inside))) w]
  case or left right =>
    simp only [fixTypeAt, nodeLit, head,
      fixTypeAt_congr left u (fun c inside => same c (List.mem_cons_of_mem _ (List.mem_append_left _ inside))) w,
      fixTypeAt_congr right u (fun c inside => same c (List.mem_cons_of_mem _ (List.mem_append_right _ inside))) w]
  case possibly label inner =>
    simp only [fixTypeAt, nodeLit, head, fixTypeAt_congr inner u (fun c inside => same c (List.mem_cons_of_mem _ inside)) w]
  case necessarily label inner =>
    simp only [fixTypeAt, nodeLit, head, fixTypeAt_congr inner u (fun c inside => same c (List.mem_cons_of_mem _ inside)) w]
  case mu inner =>
    simp only [fixTypeAt, nodeLit, head, fixTypeAt_congr inner _ (fun c inside => same c (List.mem_cons_of_mem _ inside)) w]
  case nu inner =>
    simp only [fixTypeAt, nodeLit, head, fixTypeAt_congr inner _ (fun c inside => same c (List.mem_cons_of_mem _ inside)) w]
  all_goals simp only [fixTypeAt, nodeLit, head]

theorem isCore_fixTypeAt : ∀ {n : ℕ} (formula : Formula n), formula.fixBody = true → ∀ (u : Fin n → Formula 0),
    (∀ i, (u i).fixBody = true) → ∀ (t : Pattern) {w : Term Symbol Γ setTy}, w.isCore = true →
      (fixTypeAt formula u t w).isCore = true := by
  intro n formula body u bodies t w coreW
  have node : (nodeLit formula u t w).isCore = true :=
    isCore_literal _ (isCore_native _ (fixBody_subst formula u body bodies) coreW fun i => i.elim0)
  cases formula
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact isCore_conjunctionFormula node (isCore_conjunctionFormula (isCore_fixTypeAt left body.1 u bodies t coreW)
      (isCore_fixTypeAt right body.2 u bodies t coreW))
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact isCore_conjunctionFormula node (isCore_fixTypeAt inner body.2 u bodies t coreW)
  case mu inner =>
    simp only [Formula.fixBody] at body
    exact isCore_conjunctionFormula node (isCore_fixTypeAt inner body _
      (unfoldWith_bodies (fixBody_subst (.mu inner) u body bodies) bodies) t coreW)
  case nu inner =>
    simp only [Formula.fixBody] at body
    exact isCore_conjunctionFormula node (isCore_fixTypeAt inner body _
      (unfoldWith_bodies (fixBody_subst (.nu inner) u body bodies) bodies) t coreW)
  all_goals exact isCore_conjunctionFormula node rfl

theorem subst_fixTypeAt {Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') : ∀ {n : ℕ} (formula : Formula n),
    formula.fixBody = true → ∀ (u : Fin n → Formula 0), (∀ i, (u i).fixBody = true) → ∀ (t : Pattern)
      (w : Term Symbol Γ setTy), subst θ (fixTypeAt formula u t w) = fixTypeAt formula u t (subst θ w) := by
  intro n formula body u bodies t w
  have node : subst θ (nodeLit formula u t w) = nodeLit formula u t (subst θ w) := by
    unfold nodeLit
    rw [subst_literal, subst_closedAt _ (regional_of_fixBody _ (fixBody_subst formula u body bodies))]
  cases formula
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [fixTypeAt, subst_conjunctionFormula, node, subst_fixTypeAt θ left body.1 u bodies,
      subst_fixTypeAt θ right body.2 u bodies]
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [fixTypeAt, subst_conjunctionFormula, node, subst_fixTypeAt θ inner body.2 u bodies]
  case mu inner =>
    simp only [Formula.fixBody] at body
    simp only [fixTypeAt, subst_conjunctionFormula, node, subst_fixTypeAt θ inner body _
      (unfoldWith_bodies (fixBody_subst (.mu inner) u body bodies) bodies)]
  case nu inner =>
    simp only [Formula.fixBody] at body
    simp only [fixTypeAt, subst_conjunctionFormula, node, subst_fixTypeAt θ inner body _
      (unfoldWith_bodies (fixBody_subst (.nu inner) u body bodies) bodies)]
  all_goals simp only [fixTypeAt, subst_conjunctionFormula, node]; rfl

end Tree

/-! ## Native formulas move along same members -/

section Transfer

/-- **Transfer of a closed formula** along same members, in every context. -/
abbrev TransferOf (formula : Formula 0) : Type :=
  ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {m b : Term Symbol Γ setTy}, m.isCore = true → b.isCore = true →
    Proof Δ (sameMembers m b) → Proof Δ (closedAt formula m) → Proof Δ (closedAt formula b)

theorem guarded_parts_and {n : ℕ} {now later : Fin n → Bool} {left right : Formula n}
    (guarded : (Formula.and left right).guardedIn now later = true) :
    left.guardedIn now later = true ∧ right.guardedIn now later = true := by
  simpa [Formula.guardedIn] using guarded

theorem guarded_parts_or {n : ℕ} {now later : Fin n → Bool} {left right : Formula n}
    (guarded : (Formula.or left right).guardedIn now later = true) :
    left.guardedIn now later = true ∧ right.guardedIn now later = true := by
  simpa [Formula.guardedIn] using guarded

/-- **A closed fixed-point body moves along same members**: a step looks at the set only through its members; a fixed
point unfolds, moves, and folds back. The variables that occur unguarded move by the transfers given. -/
def transferFix : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (now later : Fin n → Bool),
    formula.fixBody = true → formula.guardedIn now later = true → (∀ i, (u i).fixBody = true) →
    (∀ i, now i = true → TransferOf (u i)) → TransferOf (formula.subst u) := by
  intro n formula u now later body guarded bodies varT Γ Δ m b coreM coreB same proof
  cases formula
  case top => exact proof
  case bot => exact Proof.absurd proof
  case and left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_and guarded
    exact conjunctionIntro (transferFix left u now later body.1 parts.1 bodies varT coreM coreB same
      (conjunctionLeft proof)) (transferFix right u now later body.2 parts.2 bodies varT coreM coreB same
      (conjunctionRight proof))
  case or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_or guarded
    exact disjunctionElim proof
      (disjunctionLeft (transferFix left u now later body.1 parts.1 bodies varT coreM coreB (same.prepend _)
        (Proof.newest _)))
      (disjunctionRight (transferFix right u now later body.2 parts.2 bodies varT coreM coreB (same.prepend _)
        (Proof.newest _)))
  case var index => exact varT index guarded coreM coreB same proof
  case possibly label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have regional := regional_of_fixBody _ (fixBody_subst inner u body.2 bodies)
    change Proof Δ (closedAt (.possibly label (inner.subst u)) m) at proof
    change Proof Δ (closedAt (.possibly label (inner.subst u)) b)
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [closedAt_possibly labelled] at proof
      refine existentialElim proof ?_
      rw [weaken_closedAt (by simp only [Formula.regional, regional, body.1, Bool.and_self]), closedAt_possibly labelled]
      refine existentialIntro (.var .vz) (Proof.cast (instantiate_closedBody regional _ _).symm ?_)
      have same' : Proof (conjunctionFormula (member (.var .vz) (weaken m)) (closedAt (inner.subst u) (.var .vz)) ::
          weakenHyps (σ := setTy) Δ) (sameMembers (weaken m) (weaken b)) :=
        Proof.cast (weaken_sameMembers m b) (under _ same)
      exact conjunctionIntro ((sameAt same' (.var .vz)).iffForward (conjunctionLeft (Proof.newest _)))
        (conjunctionRight (Proof.newest _))
    · rw [closedAt_possibly_unlabelled labelled] at proof
      exact Proof.absurd proof
  case necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have regional := regional_of_fixBody _ (fixBody_subst inner u body.2 bodies)
    change Proof Δ (closedAt (.necessarily label (inner.subst u)) m) at proof
    change Proof Δ (closedAt (.necessarily label (inner.subst u)) b)
    have regionalBox : (Formula.necessarily label (inner.subst u)).regional = true := by
      simp only [Formula.regional, regional, body.1, Bool.and_self]
    refine if labelled : memberLabel label then ?_ else ?_
    · have every := Proof.cast (instantiate_closedAllBody regional (.var .vz) (weaken m))
        (.allE (.var .vz) (Proof.cast ((weaken_closedAt (σ := setTy) regionalBox m).trans
          (closedAt_necessarily labelled _ _)) proof.lift))
      rw [closedAt_necessarily labelled]
      refine .allI (.impI ?_)
      have same' : Proof (member (.var .vz) (weaken b) :: weakenHyps (σ := setTy) Δ)
          (sameMembers (weaken m) (weaken b)) :=
        Proof.cast (weaken_sameMembers m b) (under _ same)
      exact .impE (every.prepend _) ((sameAt same' (.var .vz)).iffBackward (Proof.newest _))
    · rw [closedAt_necessarily_unlabelled labelled]
      exact truthIntro
  case mu inner =>
    simp only [Formula.fixBody] at body
    have fixedBody := fixBody_subst (.mu inner) u body bodies
    exact foldMu inner body u bodies coreB (transferFix inner (unfoldWith ((Formula.mu inner).subst u) u)
      (Fin.cons false now) (Fin.cons true later) body guarded (unfoldWith_bodies fixedBody bodies)
      (fun i => Fin.cases (fun absent => absurd absent Bool.false_ne_true) (fun j present => varT j present) i)
      coreM coreB same (unfoldMu inner body u bodies coreM proof))
  case nu inner =>
    simp only [Formula.fixBody] at body
    have fixedBody := fixBody_subst (.nu inner) u body bodies
    exact foldNu inner body u bodies coreB (transferFix inner (unfoldWith ((Formula.nu inner).subst u) u)
      (Fin.cons false now) (Fin.cons true later) body guarded (unfoldWith_bodies fixedBody bodies)
      (fun i => Fin.cases (fun absent => absurd absent Bool.false_ne_true) (fun j present => varT j present) i)
      coreM coreB same (unfoldNu inner body u bodies coreM proof))
  all_goals exact absurd body (by simp [Formula.fixBody])

end Transfer

/-! ## Variables read under a fixed point -/

section Variables

/-- The masked variables under a fixed point: its own is never needed unguarded. -/
def maskedCons {n : ℕ} {now : Fin n → Bool} {motive : Fin (n + 1) → Type}
    (rest : ∀ i : Fin n, now i = true → motive i.succ) : ∀ i : Fin (n + 1), (Fin.cons false now : Fin (n + 1) → Bool) i = true →
      motive i :=
  fun i => Fin.cases (fun absent => absurd absent Bool.false_ne_true) (fun j present => rest j present) i

/-- The variables under a fixed point: its own first. -/
def fullCons {n : ℕ} {motive : Fin (n + 1) → Type} (first : motive 0) (rest : ∀ i : Fin n, motive i.succ) :
    ∀ i : Fin (n + 1), motive i :=
  fun i => Fin.cases first rest i

end Variables

/-! ## Adjunction -/

section Adjunction

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem closure_head_mu {n : ℕ} {inner : Formula (n + 1)} {u : Fin n → Formula 0}
    (ok : ∀ c ∈ closureWith u (.mu inner), c.countGuarded = true) :
    ((Formula.mu inner).subst u).countGuarded = true ∧
      (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)).countGuarded = true ∧
      ∀ c ∈ closureWith (unfoldWith ((Formula.mu inner).subst u) u) inner, c.countGuarded = true :=
  ⟨ok _ List.mem_cons_self, ok _ (List.mem_cons_of_mem _ (subst_mem_closureWith _ inner)),
    fun c inside => ok c (List.mem_cons_of_mem _ inside)⟩

theorem closure_head_nu {n : ℕ} {inner : Formula (n + 1)} {u : Fin n → Formula 0}
    (ok : ∀ c ∈ closureWith u (.nu inner), c.countGuarded = true) :
    ((Formula.nu inner).subst u).countGuarded = true ∧
      (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)).countGuarded = true ∧
      ∀ c ∈ closureWith (unfoldWith ((Formula.nu inner).subst u) u) inner, c.countGuarded = true :=
  ⟨ok _ List.mem_cons_self, ok _ (List.mem_cons_of_mem _ (subst_mem_closureWith _ inner)),
    fun c inside => ok c (List.mem_cons_of_mem _ inside)⟩

/-- A least fixed point's literal from its unfolding's. -/
def muLiteral {n : ℕ} (inner : Formula (n + 1)) (body : inner.fixBody = true) (u : Fin n → Formula 0)
    (bodies : ∀ i, (u i).fixBody = true) {z : Term Symbol Γ setTy} (coreZ : z.isCore = true) {value : Bool}
    (unfolded : Proof Δ (literal value (closedAt (inner.subst (unfoldWith ((Formula.mu inner).subst u) u)) z))) :
    Proof Δ (literal value (closedAt ((Formula.mu inner).subst u) z)) := by
  cases value
  · exact .impI (.impE (unfolded.prepend _) (unfoldMu inner body u bodies coreZ (Proof.newest _)))
  · exact foldMu inner body u bodies coreZ unfolded

/-- A greatest fixed point's literal from its unfolding's. -/
def nuLiteral {n : ℕ} (inner : Formula (n + 1)) (body : inner.fixBody = true) (u : Fin n → Formula 0)
    (bodies : ∀ i, (u i).fixBody = true) {z : Term Symbol Γ setTy} (coreZ : z.isCore = true) {value : Bool}
    (unfolded : Proof Δ (literal value (closedAt (inner.subst (unfoldWith ((Formula.nu inner).subst u) u)) z))) :
    Proof Δ (literal value (closedAt ((Formula.nu inner).subst u) z)) := by
  cases value
  · exact .impI (.impE (unfolded.prepend _) (unfoldNu inner body u bodies coreZ (Proof.newest _)))
  · exact foldNu inner body u bodies coreZ unfolded

/-- **A node's literal at an adjunction**, from the literals it depends on: the sets' node literals at a step, the
unfolding's at a fixed point. A variable that occurs unguarded is read by the literal given for it. -/
def adjoinHead : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (now later : Fin n → Bool),
    formula.fixBody = true → formula.guardedIn now later = true → (∀ i, (u i).fixBody = true) →
    (∀ c ∈ closureWith u formula, c.countGuarded = true) →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {a b z : Term Symbol Γ setTy} {whole term : Pattern},
    IsHF whole → IsHF term → a.isCore = true → b.isCore = true → z.isCore = true →
    Proof Δ (fixTypeAt formula u whole a) → Proof Δ (fixTypeAt formula u term b) → Proof Δ (adjoins z a b) →
    (∀ i, now i = true → Proof Δ (literal (evalCounted (u i) (insertTerm term whole)) (closedAt (u i) z))) →
    (∀ i, TransferOf (u i)) → Proof Δ (nodeLit formula u (insertTerm term whole) z) := by
  intro n formula u now later body guarded bodies ok Γ Δ a b z whole term holdsWhole holdsTerm coreA coreB coreZ
    treeA treeB adjoined varL varT
  have insertHolds := insertTerm_hf holdsTerm holdsWhole
  cases formula
  case top => exact truthIntro
  case bot => exact .impI (Proof.newest _)
  case and left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_and guarded
    exact andLiteral
      (adjoinHead left u now later body.1 parts.1 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ inside))) holdsWhole holdsTerm coreA coreB coreZ (conjunctionLeft (conjunctionRight treeA))
        (conjunctionLeft (conjunctionRight treeB)) adjoined varL varT)
      (adjoinHead right u now later body.2 parts.2 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ inside))) holdsWhole holdsTerm coreA coreB coreZ
        (conjunctionRight (conjunctionRight treeA)) (conjunctionRight (conjunctionRight treeB)) adjoined varL varT)
  case or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_or guarded
    exact orLiteral
      (adjoinHead left u now later body.1 parts.1 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ inside))) holdsWhole holdsTerm coreA coreB coreZ (conjunctionLeft (conjunctionRight treeA))
        (conjunctionLeft (conjunctionRight treeB)) adjoined varL varT)
      (adjoinHead right u now later body.2 parts.2 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ inside))) holdsWhole holdsTerm coreA coreB coreZ
        (conjunctionRight (conjunctionRight treeA)) (conjunctionRight (conjunctionRight treeB)) adjoined varL varT)
  case var index => exact varL index guarded
  case possibly label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have regional := regional_of_fixBody _ (fixBody_subst inner u body.2 bodies)
    have nodeA : Proof Δ (literal (nodeVal (.possibly label inner) u whole) (closedAt (.possibly label (inner.subst u)) a)) :=
      rootLit treeA
    have nodeB : Proof Δ (literal (nodeVal inner u term) (closedAt (inner.subst u) b)) := rootLit (conjunctionRight treeB)
    have moves : TransferOf (inner.subst u) :=
      transferFix inner u later later body.2 guarded bodies (fun i _ => varT i)
    change Proof Δ (literal (nodeVal (.possibly label inner) u (insertTerm term whole))
      (closedAt (.possibly label (inner.subst u)) z))
    rw [nodeVal_possibly_insert]
    refine if labelled : memberLabel label then ?_ else ?_
    · refine if holdsB : nodeVal inner u term = true then ?_ else ?_
      · refine asTrue (by simp [labelled, holdsB]) (Proof.cast (closedAt_possibly labelled _ z).symm ?_)
        exact existentialIntro b (Proof.cast (instantiate_closedBody regional b z).symm
          (conjunctionIntro (adjoinedMember adjoined) (literalTrue holdsB nodeB)))
      · have failsB : nodeVal inner u term = false := Bool.eq_false_iff.mpr holdsB
        refine if holdsA : nodeVal (.possibly label inner) u whole = true then ?_ else ?_
        · refine asTrue (by simp [holdsA]) ?_
          refine existentialElim (Proof.cast (closedAt_possibly labelled _ a) (literalTrue holdsA nodeA)) ?_
          rw [weaken_closedAt (by simp only [Formula.regional, regional, body.1, Bool.and_self]), closedAt_possibly labelled]
          refine existentialIntro (.var .vz) (Proof.cast (instantiate_closedBody regional _ _).symm ?_)
          have adjoined' := Proof.cast (weaken_adjoins z a b) (under (conjunctionFormula (member (.var .vz) (weaken a))
            (closedAt (inner.subst u) (.var .vz))) adjoined)
          exact conjunctionIntro (keptMember adjoined' (conjunctionLeft (Proof.newest _)))
            (conjunctionRight (Proof.newest _))
        · have failsA : nodeVal (.possibly label inner) u whole = false := Bool.eq_false_iff.mpr holdsA
          refine asFalse (by simp [failsA, failsB]) ?_
          refine .impI (existentialElim (Proof.cast (closedAt_possibly labelled _ z) (Proof.newest _)) ?_)
          let found := conjunctionFormula (member (.var .vz) (weaken z)) (closedAt (inner.subst u) (.var .vz))
          have adjoined' := Proof.cast (weaken_adjoins z a b)
            (under found (adjoined.prepend (closedAt (.possibly label (inner.subst u)) z)))
          refine disjunctionElim ((adjoinsAt adjoined' (.var .vz)).iffForward (conjunctionLeft (Proof.newest _))) ?_ ?_
          · have notA := Proof.cast ((weaken_negCore _).trans (congrArg negCore
              (weaken_closedAt (by simp only [Formula.regional, regional, body.1, Bool.and_self]) _)))
              (under found ((literalFalse failsA nodeA).prepend (closedAt (.possibly label (inner.subst u)) z)))
            refine .impE (Proof.cast (congrArg negCore (closedAt_possibly labelled _ (weaken a))) (notA.prepend _)) ?_
            refine existentialIntro (.var .vz) (Proof.cast (instantiate_closedBody regional _ _).symm ?_)
            exact conjunctionIntro (Proof.newest _) (conjunctionRight ((Proof.newest _).prepend _))
          · have notB := Proof.cast ((weaken_negCore _).trans (congrArg negCore (weaken_closedAt regional _)))
              (under found ((literalFalse failsB nodeB).prepend (closedAt (.possibly label (inner.subst u)) z)))
            exact .impE (notB.prepend _) (moves rfl (coreWeaken coreB) (Proof.newest _)
              (conjunctionRight ((Proof.newest _).prepend _)))
    · rw [closedAt_possibly_unlabelled labelled]
      exact asFalse (by simp [nodeVal, evalCounted, Formula.subst, evalCountedWith, labelled]) (.impI (Proof.newest _))
  case necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have regional := regional_of_fixBody _ (fixBody_subst inner u body.2 bodies)
    have regionalBox : (Formula.necessarily label (inner.subst u)).regional = true := by
      simp only [Formula.regional, regional, body.1, Bool.and_self]
    have nodeA : Proof Δ (literal (nodeVal (.necessarily label inner) u whole)
        (closedAt (.necessarily label (inner.subst u)) a)) := rootLit treeA
    have nodeB : Proof Δ (literal (nodeVal inner u term) (closedAt (inner.subst u) b)) := rootLit (conjunctionRight treeB)
    have moves : TransferOf (inner.subst u) :=
      transferFix inner u later later body.2 guarded bodies (fun i _ => varT i)
    change Proof Δ (literal (nodeVal (.necessarily label inner) u (insertTerm term whole))
      (closedAt (.necessarily label (inner.subst u)) z))
    rw [nodeVal_necessarily_insert]
    refine if labelled : memberLabel label then ?_ else ?_
    · refine if holdsB : nodeVal inner u term = true then ?_ else ?_
      · refine if holdsA : nodeVal (.necessarily label inner) u whole = true then ?_ else ?_
        · refine asTrue (by simp [holdsA, holdsB]) (Proof.cast (closedAt_necessarily labelled _ z).symm (.allI (.impI ?_)))
          have adjoined' := Proof.cast (weaken_adjoins z a b) (under (member (.var .vz) (weaken z)) adjoined)
          refine disjunctionElim ((adjoinsAt adjoined' (.var .vz)).iffForward (Proof.newest _)) ?_ ?_
          · have every := Proof.cast (instantiate_closedAllBody regional (.var .vz) (weaken a))
              (.allE (.var .vz) (Proof.cast ((weaken_closedAt (σ := setTy) regionalBox a).trans
                (closedAt_necessarily labelled _ _)) (literalTrue holdsA nodeA).lift))
            exact .impE ((every.prepend _).prepend _) (Proof.newest _)
          · have innerB := Proof.cast (weaken_closedAt regional b)
              (under (member (.var .vz) (weaken z)) (literalTrue holdsB nodeB))
            exact moves (coreWeaken coreB) rfl (sameSymm (Proof.newest _)) (innerB.prepend _)
        · have failsA : nodeVal (.necessarily label inner) u whole = false := Bool.eq_false_iff.mpr holdsA
          refine asFalse (by simp [failsA]) (.impI ?_)
          refine .impE (Proof.cast (congrArg negCore (closedAt_necessarily labelled _ a))
            ((literalFalse failsA nodeA).prepend _)) ?_
          refine .allI (.impI ?_)
          have every := Proof.cast (instantiate_closedAllBody regional (.var .vz) (weaken z))
            (.allE (.var .vz) (Proof.cast ((weaken_closedAt (σ := setTy) regionalBox z).trans
              (closedAt_necessarily labelled _ _))
                (Proof.newest (Δ := Δ) (closedAt (.necessarily label (inner.subst u)) z)).lift))
          have adjoined' := Proof.cast (weaken_adjoins z a b) (under (member (.var .vz) (weaken a))
            (adjoined.prepend (closedAt (.necessarily label (inner.subst u)) z)))
          exact .impE (every.prepend _) (keptMember adjoined' (Proof.newest _))
      · have failsB : nodeVal inner u term = false := Bool.eq_false_iff.mpr holdsB
        refine asFalse (by simp [labelled, failsB]) (.impI ?_)
        let everyZ : Term Symbol Γ .prop :=
          .all (σ := setTy) (.imp (member (.var .vz) (weaken z)) (closedAt (inner.subst u) (.var .vz)))
        have atB := Proof.cast (instantiate_closedAllBody regional b z)
          (.allE b (Proof.cast (closedAt_necessarily labelled _ z) (Proof.newest (Δ := Δ)
            (closedAt (.necessarily label (inner.subst u)) z))))
        exact .impE ((literalFalse failsB nodeB).prepend _) (.impE atB (adjoinedMember (adjoined.prepend _)))
    · rw [closedAt_necessarily_unlabelled labelled]
      exact asTrue (by simp [nodeVal, evalCounted, Formula.subst, evalCountedWith, labelled]) truthIntro
  case mu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨okFixed, okUnfolded, okInner⟩ := closure_head_mu ok
    have fixedBody := fixBody_subst (.mu inner) u body bodies
    have unfolded := adjoinHead inner (unfoldWith ((Formula.mu inner).subst u) u) (Fin.cons false now) (Fin.cons true later)
      body guarded (unfoldWith_bodies fixedBody bodies) okInner holdsWhole holdsTerm coreA coreB coreZ
      (conjunctionRight treeA) (conjunctionRight treeB) adjoined
      (maskedCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.mu inner).subst u) u i)
        (insertTerm term whole)) (closedAt (unfoldWith ((Formula.mu inner).subst u) u i) z))) varL)
      (fullCons (motive := fun i => TransferOf (unfoldWith ((Formula.mu inner).subst u) u i))
        (transferFix (.mu inner) u now later body guarded bodies fun i _ => varT i) varT)
    change Proof Δ (literal (nodeVal (.mu inner) u (insertTerm term whole)) (closedAt ((Formula.mu inner).subst u) z))
    rw [nodeVal_mu inner u okFixed okUnfolded insertHolds]
    exact muLiteral inner body u bodies coreZ unfolded
  case nu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨okFixed, okUnfolded, okInner⟩ := closure_head_nu ok
    have fixedBody := fixBody_subst (.nu inner) u body bodies
    have unfolded := adjoinHead inner (unfoldWith ((Formula.nu inner).subst u) u) (Fin.cons false now) (Fin.cons true later)
      body guarded (unfoldWith_bodies fixedBody bodies) okInner holdsWhole holdsTerm coreA coreB coreZ
      (conjunctionRight treeA) (conjunctionRight treeB) adjoined
      (maskedCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.nu inner).subst u) u i)
        (insertTerm term whole)) (closedAt (unfoldWith ((Formula.nu inner).subst u) u i) z))) varL)
      (fullCons (motive := fun i => TransferOf (unfoldWith ((Formula.nu inner).subst u) u i))
        (transferFix (.nu inner) u now later body guarded bodies fun i _ => varT i) varT)
    change Proof Δ (literal (nodeVal (.nu inner) u (insertTerm term whole)) (closedAt ((Formula.nu inner).subst u) z))
    rw [nodeVal_nu inner u okFixed okUnfolded insertHolds]
    exact nuLiteral inner body u bodies coreZ unfolded
  all_goals exact absurd body (by simp [Formula.fixBody])

/-- **Adjunction**: a set adjoining `b` to `a` has the type of the term adjoining `b`'s type to `a`'s, the whole tree;
each variable node is read by the literal of the fixed point above it. -/
def adjoinTree : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (now later : Fin n → Bool),
    formula.fixBody = true → formula.guardedIn now later = true → (∀ i, (u i).fixBody = true) →
    (∀ c ∈ closureWith u formula, c.countGuarded = true) →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {a b z : Term Symbol Γ setTy} {whole term : Pattern},
    IsHF whole → IsHF term → a.isCore = true → b.isCore = true → z.isCore = true →
    Proof Δ (fixTypeAt formula u whole a) → Proof Δ (fixTypeAt formula u term b) → Proof Δ (adjoins z a b) →
    (∀ i, Proof Δ (literal (evalCounted (u i) (insertTerm term whole)) (closedAt (u i) z))) →
    (∀ i, TransferOf (u i)) → Proof Δ (fixTypeAt formula u (insertTerm term whole) z) := by
  intro n formula u now later body guarded bodies ok Γ Δ a b z whole term holdsWhole holdsTerm coreA coreB coreZ
    treeA treeB adjoined varL varT
  have node := adjoinHead formula u now later body guarded bodies ok holdsWhole holdsTerm coreA coreB coreZ treeA treeB
    adjoined (fun i _ => varL i) varT
  cases formula
  case and left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_and guarded
    exact conjunctionIntro node (conjunctionIntro
      (adjoinTree left u now later body.1 parts.1 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ inside))) holdsWhole holdsTerm coreA coreB coreZ (conjunctionLeft (conjunctionRight treeA))
        (conjunctionLeft (conjunctionRight treeB)) adjoined varL varT)
      (adjoinTree right u now later body.2 parts.2 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ inside))) holdsWhole holdsTerm coreA coreB coreZ
        (conjunctionRight (conjunctionRight treeA)) (conjunctionRight (conjunctionRight treeB)) adjoined varL varT))
  case or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_or guarded
    exact conjunctionIntro node (conjunctionIntro
      (adjoinTree left u now later body.1 parts.1 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ inside))) holdsWhole holdsTerm coreA coreB coreZ (conjunctionLeft (conjunctionRight treeA))
        (conjunctionLeft (conjunctionRight treeB)) adjoined varL varT)
      (adjoinTree right u now later body.2 parts.2 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ inside))) holdsWhole holdsTerm coreA coreB coreZ
        (conjunctionRight (conjunctionRight treeA)) (conjunctionRight (conjunctionRight treeB)) adjoined varL varT))
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact conjunctionIntro node (adjoinTree inner u later later body.2 guarded bodies
      (fun c inside => ok c (List.mem_cons_of_mem _ inside)) holdsWhole holdsTerm coreA coreB coreZ
      (conjunctionRight treeA) (conjunctionRight treeB) adjoined varL varT)
  case mu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨_, _, okInner⟩ := closure_head_mu ok
    have fixedBody := fixBody_subst (.mu inner) u body bodies
    exact conjunctionIntro node (adjoinTree inner (unfoldWith ((Formula.mu inner).subst u) u) (Fin.cons false now)
      (Fin.cons true later) body guarded (unfoldWith_bodies fixedBody bodies) okInner holdsWhole holdsTerm coreA coreB
      coreZ (conjunctionRight treeA) (conjunctionRight treeB) adjoined
      (fullCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.mu inner).subst u) u i)
        (insertTerm term whole)) (closedAt (unfoldWith ((Formula.mu inner).subst u) u i) z))) node varL)
      (fullCons (motive := fun i => TransferOf (unfoldWith ((Formula.mu inner).subst u) u i))
        (transferFix (.mu inner) u now later body guarded bodies fun i _ => varT i) varT))
  case nu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨_, _, okInner⟩ := closure_head_nu ok
    have fixedBody := fixBody_subst (.nu inner) u body bodies
    exact conjunctionIntro node (adjoinTree inner (unfoldWith ((Formula.nu inner).subst u) u) (Fin.cons false now)
      (Fin.cons true later) body guarded (unfoldWith_bodies fixedBody bodies) okInner holdsWhole holdsTerm coreA coreB
      coreZ (conjunctionRight treeA) (conjunctionRight treeB) adjoined
      (fullCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.nu inner).subst u) u i)
        (insertTerm term whole)) (closedAt (unfoldWith ((Formula.nu inner).subst u) u i) z))) node varL)
      (fullCons (motive := fun i => TransferOf (unfoldWith ((Formula.nu inner).subst u) u i))
        (transferFix (.nu inner) u now later body guarded bodies fun i _ => varT i) varT))
  all_goals exact conjunctionIntro node truthIntro

/-! ## The empty sets -/

/-- **A node's literal at an empty set.** -/
def emptyHead : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (now later : Fin n → Bool),
    formula.fixBody = true → formula.guardedIn now later = true → (∀ i, (u i).fixBody = true) →
    (∀ c ∈ closureWith u formula, c.countGuarded = true) →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {z : Term Symbol Γ setTy}, z.isCore = true →
    Proof Δ (emptyCore z) → (∀ i, now i = true → Proof Δ (literal (evalCounted (u i) (set [])) (closedAt (u i) z))) →
    Proof Δ (nodeLit formula u (set []) z) := by
  intro n formula u now later body guarded bodies ok Γ Δ z coreZ empty varL
  have emptyHolds : IsHF (set []) := set_hf fun _ found => nomatch found
  cases formula
  case top => exact truthIntro
  case bot => exact .impI (Proof.newest _)
  case and left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_and guarded
    exact andLiteral
      (emptyHead left u now later body.1 parts.1 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ inside))) coreZ empty varL)
      (emptyHead right u now later body.2 parts.2 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ inside))) coreZ empty varL)
  case or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts := guarded_parts_or guarded
    exact orLiteral
      (emptyHead left u now later body.1 parts.1 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ inside))) coreZ empty varL)
      (emptyHead right u now later body.2 parts.2 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ inside))) coreZ empty varL)
  case var index => exact varL index guarded
  case possibly label inner =>
    change Proof Δ (literal (nodeVal (.possibly label inner) u (set [])) (closedAt (.possibly label (inner.subst u)) z))
    refine asFalse (nodeVal_possibly_empty label inner u) ?_
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [closedAt_possibly labelled]
      refine .impI (existentialElim (Proof.newest _) ?_)
      have none := Proof.cast (weaken_emptyCore z) (under (conjunctionFormula (member (.var .vz) (weaken z))
        (closedAt (inner.subst u) (.var .vz))) (empty.prepend (existentialInline (σ := setTy)
          (conjunctionFormula (member (.var .vz) (weaken z)) (closedAt (inner.subst u) (.var .vz))))))
      exact .impE (noMemberAt none (.var .vz)) (conjunctionLeft (Proof.newest _))
    · rw [closedAt_possibly_unlabelled labelled]
      exact .impI (Proof.newest _)
  case necessarily label inner =>
    change Proof Δ (literal (nodeVal (.necessarily label inner) u (set []))
      (closedAt (.necessarily label (inner.subst u)) z))
    refine asTrue (nodeVal_necessarily_empty label inner u) ?_
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [closedAt_necessarily labelled]
      refine .allI (.impI (Proof.absurd ?_))
      have none := Proof.cast (weaken_emptyCore z) (under (member (.var .vz) (weaken z)) empty)
      exact .impE (noMemberAt none (.var .vz)) (Proof.newest _)
    · rw [closedAt_necessarily_unlabelled labelled]
      exact truthIntro
  case mu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨okFixed, okUnfolded, okInner⟩ := closure_head_mu ok
    have fixedBody := fixBody_subst (.mu inner) u body bodies
    have unfolded := emptyHead inner (unfoldWith ((Formula.mu inner).subst u) u) (Fin.cons false now) (Fin.cons true later)
      body guarded (unfoldWith_bodies fixedBody bodies) okInner coreZ empty
      (maskedCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.mu inner).subst u) u i)
        (set [])) (closedAt (unfoldWith ((Formula.mu inner).subst u) u i) z))) varL)
    change Proof Δ (literal (nodeVal (.mu inner) u (set [])) (closedAt ((Formula.mu inner).subst u) z))
    rw [nodeVal_mu inner u okFixed okUnfolded emptyHolds]
    exact muLiteral inner body u bodies coreZ unfolded
  case nu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨okFixed, okUnfolded, okInner⟩ := closure_head_nu ok
    have fixedBody := fixBody_subst (.nu inner) u body bodies
    have unfolded := emptyHead inner (unfoldWith ((Formula.nu inner).subst u) u) (Fin.cons false now) (Fin.cons true later)
      body guarded (unfoldWith_bodies fixedBody bodies) okInner coreZ empty
      (maskedCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.nu inner).subst u) u i)
        (set [])) (closedAt (unfoldWith ((Formula.nu inner).subst u) u i) z))) varL)
    change Proof Δ (literal (nodeVal (.nu inner) u (set [])) (closedAt ((Formula.nu inner).subst u) z))
    rw [nodeVal_nu inner u okFixed okUnfolded emptyHolds]
    exact nuLiteral inner body u bodies coreZ unfolded
  all_goals exact absurd body (by simp [Formula.fixBody])

/-- **The empty sets have the empty set's type**, the whole tree. -/
def emptyTree : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (now later : Fin n → Bool),
    formula.fixBody = true → formula.guardedIn now later = true → (∀ i, (u i).fixBody = true) →
    (∀ c ∈ closureWith u formula, c.countGuarded = true) →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {z : Term Symbol Γ setTy}, z.isCore = true →
    Proof Δ (emptyCore z) → (∀ i, Proof Δ (literal (evalCounted (u i) (set [])) (closedAt (u i) z))) →
    Proof Δ (fixTypeAt formula u (set []) z) := by
  intro n formula u now later body guarded bodies ok Γ Δ z coreZ empty varL
  have node := emptyHead formula u now later body guarded bodies ok coreZ empty (fun i _ => varL i)
  cases formula
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts : left.guardedIn now later = true ∧ right.guardedIn now later = true := by
      simpa [Formula.guardedIn] using guarded
    exact conjunctionIntro node (conjunctionIntro
      (emptyTree left u now later body.1 parts.1 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ inside))) coreZ empty varL)
      (emptyTree right u now later body.2 parts.2 bodies (fun c inside => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ inside))) coreZ empty varL))
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    exact conjunctionIntro node (emptyTree inner u later later body.2 guarded bodies
      (fun c inside => ok c (List.mem_cons_of_mem _ inside)) coreZ empty varL)
  case mu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨_, _, okInner⟩ := closure_head_mu ok
    have fixedBody := fixBody_subst (.mu inner) u body bodies
    exact conjunctionIntro node (emptyTree inner (unfoldWith ((Formula.mu inner).subst u) u) (Fin.cons false now)
      (Fin.cons true later) body guarded (unfoldWith_bodies fixedBody bodies) okInner coreZ empty
      (fullCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.mu inner).subst u) u i)
        (set [])) (closedAt (unfoldWith ((Formula.mu inner).subst u) u i) z))) node varL))
  case nu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨_, _, okInner⟩ := closure_head_nu ok
    have fixedBody := fixBody_subst (.nu inner) u body bodies
    exact conjunctionIntro node (emptyTree inner (unfoldWith ((Formula.nu inner).subst u) u) (Fin.cons false now)
      (Fin.cons true later) body guarded (unfoldWith_bodies fixedBody bodies) okInner coreZ empty
      (fullCons (motive := fun i => Proof Δ (literal (evalCounted (unfoldWith ((Formula.nu inner).subst u) u i)
        (set [])) (closedAt (unfoldWith ((Formula.nu inner).subst u) u i) z))) node varL))
  all_goals exact conjunctionIntro node truthIntro

end Adjunction

/-! ## Classification -/

section Classification

variable {Γ Γ' : Ctx Unit}

/-- **Some representative's type holds** of a set, for a fixed-point body. -/
def fixSomeType (body : Formula 0) (reps : List Pattern) (w : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  anyFormula (reps.map fun r => fixTypeAt body Fin.elim0 r w)

theorem subst_fixSomeType (θ : Subst Symbol Γ Γ') {body : Formula 0} (isBody : body.fixBody = true) :
    ∀ (reps : List Pattern) (w : Term Symbol Γ setTy), subst θ (fixSomeType body reps w) = fixSomeType body reps (subst θ w)
  | [], _ => rfl
  | r :: reps, w => by
    change subst θ (disjunctionFormula (fixTypeAt body Fin.elim0 r w) (fixSomeType body reps w)) =
      disjunctionFormula (fixTypeAt body Fin.elim0 r (subst θ w)) (fixSomeType body reps (subst θ w))
    rw [subst_disjunctionFormula, subst_fixTypeAt θ body isBody Fin.elim0 (fun i => i.elim0),
      subst_fixSomeType θ isBody reps]

theorem isCore_fixSomeType {body : Formula 0} (isBody : body.fixBody = true) :
    ∀ (reps : List Pattern) {w : Term Symbol Γ setTy}, w.isCore = true → (fixSomeType body reps w).isCore = true
  | [], _, _ => rfl
  | r :: reps, _, coreW => isCore_disjunctionFormula (isCore_fixTypeAt body isBody Fin.elim0 (fun i => i.elim0) r coreW)
    (isCore_fixSomeType isBody reps coreW)

/-- **The predicate `some representative's type holds`.** -/
def fixSomeTypePred (body : Formula 0) (reps : List Pattern) : Term Symbol Γ predTy :=
  .lam (fixSomeType body reps (.var .vz))

theorem weaken_fixSomeTypePred {σ : Ty Unit} {body : Formula 0} (isBody : body.fixBody = true) (reps : List Pattern) :
    weaken (σ := σ) (fixSomeTypePred (Γ := Γ) body reps) = fixSomeTypePred body reps := by
  change Term.lam (rename (Rename.lift Rename.weaken) (fixSomeType body reps (.var .vz))) = _
  rw [rename_eq_subst, subst_fixSomeType _ isBody]
  rfl

variable {Δ : List (Term Symbol Γ .prop)}

/-- Some representative's type, from one of them. -/
def fixSomeIntro {body : Formula 0} {w : Term Symbol Γ setTy} : ∀ (reps : List Pattern) (index : Fin reps.length),
    Proof Δ (fixTypeAt body Fin.elim0 (reps.get index) w) → Proof Δ (fixSomeType body reps w)
  | _ :: _, ⟨0, _⟩, proof => disjunctionLeft proof
  | _ :: reps, ⟨index + 1, bound⟩, proof =>
    disjunctionRight (fixSomeIntro reps ⟨index, Nat.lt_of_succ_lt_succ bound⟩ proof)

/-- **Case analysis over the representatives** whose type may hold. -/
def fixSomeCases {body : Formula 0} {w : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop} :
    ∀ {Δ : List (Term Symbol Γ .prop)} (reps : List Pattern), Proof Δ (fixSomeType body reps w) →
      (∀ index : Fin reps.length, Proof (fixTypeAt body Fin.elim0 (reps.get index) w :: Δ) goal) → Proof Δ goal
  | _, [], cases, _ => Proof.absurd cases
  | Δ, _ :: reps, cases, branch =>
    disjunctionElim cases (branch ⟨0, Nat.succ_pos _⟩)
      (fixSomeCases (Δ := fixSomeType body reps w :: Δ) reps (Proof.newest _) fun index =>
        Proof.insertSecond _ (branch index.succ))

def fixSomeTypeExpand {body : Formula 0} (isBody : body.fixBody = true) {reps : List Pattern}
    {w : Term Symbol Γ setTy} (coreW : w.isCore = true) (proof : Proof Δ (fixSomeType body reps w)) :
    Proof Δ (.app (fixSomeTypePred body reps) w) :=
  Proof.betaExpand (isCore_fixSomeType isBody reps rfl) coreW
    (Proof.cast (by unfold instantiate; rw [subst_fixSomeType _ isBody]; rfl) proof)

def fixSomeTypeReduce {body : Formula 0} (isBody : body.fixBody = true) {reps : List Pattern}
    {w : Term Symbol Γ setTy} (coreW : w.isCore = true) (proof : Proof Δ (.app (fixSomeTypePred body reps) w)) :
    Proof Δ (fixSomeType body reps w) :=
  Proof.cast (by unfold instantiate; rw [subst_fixSomeType _ isBody]; rfl)
    (Proof.betaReduce (isCore_fixSomeType isBody reps rfl) coreW proof)

theorem found_vec {closure : List (Formula 0)} {reps : List Pattern} {target : Pattern}
    (found : ∃ r ∈ reps, closureVec closure r = closureVec closure target) :
    ∃ r ∈ reps, (closureVec closure r == closureVec closure target) = true := by
  obtain ⟨r, inside, same⟩ := found
  exact ⟨r, inside, beq_iff_eq.mpr same⟩

/-- A type moves to a representative with the same values on the closure. -/
def fixToRep {body : Formula 0} {reps : List Pattern} {target : Pattern} {w : Term Symbol Γ setTy}
    (found : ∃ r ∈ reps, closureVec (guardedClosure body) r = closureVec (guardedClosure body) target)
    (proof : Proof Δ (fixTypeAt body Fin.elim0 target w)) : Proof Δ (fixSomeType body reps w) :=
  match chooseIndex reps (fun r => closureVec (guardedClosure body) r == closureVec (guardedClosure body) target)
      (found_vec found) with
  | ⟨index, test⟩ => fixSomeIntro reps index (Proof.cast (fixTypeAt_congr body Fin.elim0
      (fun c inside => (List.map_inj_left.mp (beq_iff_eq.mp test) c inside).symm) w) proof)

/-- **Classification**: a hereditarily finite set has the type of one of the representatives, for a guarded
fixed-point body, when the representatives hold the empty set's values on the closure and every adjunction's. -/
def fixClassify (body : Formula 0) (isBody : body.fixBody = true) (guarded : body.guarded = true)
    (ok : ∀ c ∈ guardedClosure body, c.countGuarded = true) (reps : List Pattern) (repsHF : ∀ r ∈ reps, IsHF r)
    (base : ∃ r ∈ reps, closureVec (guardedClosure body) r = closureVec (guardedClosure body) (set []))
    (adjoin : ∀ whole ∈ reps, ∀ term ∈ reps,
      ∃ r ∈ reps, closureVec (guardedClosure body) r = closureVec (guardedClosure body) (insertTerm term whole))
    {y : Term Symbol Γ setTy} (coreY : y.isCore = true) (finite : Proof Δ (hfFormula y)) :
    Proof Δ (fixSomeType body reps y) := by
  have instance' : Proof Δ (.imp (buildClosed (fixSomeTypePred body reps)) (.app (fixSomeTypePred body reps) y)) :=
    Proof.cast (instantiate_hfBody _ y)
      (.allE (φ := .imp (buildClosed (.var .vz)) (.app (.var .vz) (weaken y))) (fixSomeTypePred body reps) finite)
  refine fixSomeTypeReduce isBody coreY (.impE instance' (conjunctionIntro ?_ ?_))
  · rw [weaken_fixSomeTypePred isBody]
    exact .allI (.impI (fixSomeTypeExpand isBody rfl (fixToRep base (emptyTree body Fin.elim0 Fin.elim0 Fin.elim0 isBody
      guarded (fun i => i.elim0) ok rfl (Proof.newest _) fun i => i.elim0))))
  · simp only [weaken_fixSomeTypePred isBody]
    refine .allI (.allI (.allI (.impI (.impI (.impI (.impI ?_))))))
    refine fixSomeTypeExpand isBody rfl ?_
    refine fixSomeCases reps (fixSomeTypeReduce isBody rfl (.hyp ⟨3, by simp⟩)) fun first => ?_
    refine fixSomeCases reps (fixSomeTypeReduce isBody rfl (.hyp ⟨3, by simp⟩)) fun second => ?_
    exact fixToRep (adjoin _ (List.get_mem _ _) _ (List.get_mem _ _))
      (adjoinTree body Fin.elim0 Fin.elim0 Fin.elim0 isBody guarded (fun i => i.elim0) ok
        (repsHF _ (List.get_mem _ _)) (repsHF _ (List.get_mem _ _)) rfl rfl rfl (Proof.prepend _ (Proof.newest _))
        (Proof.newest _) (.hyp ⟨2, by simp⟩) (fun i => i.elim0) fun i => i.elim0)

end Classification

/-! ## The practical stage's representatives serve -/

section Representatives

variable {body : Formula 0}

theorem practicalOK_of (guarded : body.guarded = true) (ok : ∀ c ∈ guardedClosure body, c.countGuarded = true) :
    practicalOK body = true := by
  rw [practicalOK_eq]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, ok⟩
  have masks : (fun _ : Fin 0 => false) = (Fin.elim0 : Fin 0 → Bool) := funext fun i => i.elim0
  rw [masks]
  exact guarded

theorem fixReps_covers (guarded : body.guarded = true) (ok : ∀ c ∈ guardedClosure body, c.countGuarded = true)
    {term : Pattern} (holds : IsHF term) :
    ∃ r ∈ bodyReps body, closureVec (guardedClosure body) r = closureVec (guardedClosure body) term := by
  obtain ⟨_, _, closed⟩ := practicalOK_parts (practicalOK_of guarded ok)
  obtain ⟨r, inside, same⟩ := closed.covers (guardedClosure_isLocal guarded) holds
  exact ⟨r, inside, (closureVec_eq_iff ok (closed.hf r inside) holds).mpr same⟩

theorem fixReps_hf (guarded : body.guarded = true) (ok : ∀ c ∈ guardedClosure body, c.countGuarded = true) :
    ∀ r ∈ bodyReps body, IsHF r :=
  (practicalOK_parts (practicalOK_of guarded ok)).2.2.hf

theorem fixReps_base (guarded : body.guarded = true) (ok : ∀ c ∈ guardedClosure body, c.countGuarded = true) :
    ∃ r ∈ bodyReps body, closureVec (guardedClosure body) r = closureVec (guardedClosure body) (set []) :=
  fixReps_covers guarded ok (set_hf fun _ found => nomatch found)

theorem fixReps_adjoin (guarded : body.guarded = true) (ok : ∀ c ∈ guardedClosure body, c.countGuarded = true) :
    ∀ whole ∈ bodyReps body, ∀ term ∈ bodyReps body, ∃ r ∈ bodyReps body,
      closureVec (guardedClosure body) r = closureVec (guardedClosure body) (insertTerm term whole) :=
  fun _ wholeIn _ termIn => fixReps_covers guarded ok
    (insertTerm_hf (fixReps_hf guarded ok _ termIn) (fixReps_hf guarded ok _ wholeIn))

end Representatives

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
