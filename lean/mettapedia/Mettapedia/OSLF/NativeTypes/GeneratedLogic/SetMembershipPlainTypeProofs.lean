import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPlainTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipHFSentence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofs

/-!
# Types of plain bodies, proved in the logic of the sets

A term's type for a plain formula becomes a core sentence about a set (`typeAt`): at every node, the node's native
formula or its negation, as the term's value of the node says. The calculus of the package proves, with no excluded
middle:

- **Native formulas move along same members** (`transfer`): a plain formula looks at a set only through its members.
- **The empty sets have the empty set's type** (`emptyType`).
- **Adjunction** (`adjoinType`): a set adjoining `b` to `a` has the type of the term adjoining the type of `b` to the
  type of `a`. Each step's literal is proved from the two node literals it depends on.
- **Classification** (`classify`): every hereditarily finite set has the type of one of a list of representatives that
  holds the empty set's vector and every adjunction's. The proof instantiates the impredicative definition of hereditary
  finiteness with the predicate `some representative's type holds` (`someTypePred`) and proves it closed under
  building.
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

/-! ## The sentences of building -/

section Building

variable {Γ Γ' : Ctx Unit}

theorem subst_emptyCore (θ : Subst Symbol Γ Γ') (z : Term Symbol Γ setTy) :
    subst θ (emptyCore z) = emptyCore (subst θ z) := by
  simp only [emptyCore, subst, subst_negCore, member, Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem subst_adjoins (θ : Subst Symbol Γ Γ') (z a b : Term Symbol Γ setTy) :
    subst θ (adjoins z a b) = adjoins (subst θ z) (subst θ a) (subst θ b) := by
  simp only [adjoins, subst, subst_iffCore, subst_disjunctionFormula, subst_sameMembers, member,
    Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem subst_buildStep (θ : Subst Symbol Γ Γ') (p : Term Symbol Γ predTy) (a b z : Term Symbol Γ setTy) :
    subst θ (buildStep p a b z) = buildStep (subst θ p) (subst θ a) (subst θ b) (subst θ z) := by
  simp only [buildStep, subst, subst_adjoins, subst_negCore, member]

theorem subst_buildClosed (θ : Subst Symbol Γ Γ') (p : Term Symbol Γ predTy) :
    subst θ (buildClosed p) = buildClosed (subst θ p) := by
  simp only [buildClosed, subst_conjunctionFormula, subst, subst_emptyCore, subst_buildStep,
    Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem weaken_adjoins {σ : Ty Unit} (z a b : Term Symbol Γ setTy) :
    weaken (σ := σ) (adjoins z a b) = adjoins (weaken z) (weaken a) (weaken b) := by
  rw [weaken_eq_subst, subst_adjoins, ← weaken_eq_subst, ← weaken_eq_subst, ← weaken_eq_subst]

theorem weaken_emptyCore {σ : Ty Unit} (z : Term Symbol Γ setTy) :
    weaken (σ := σ) (emptyCore z) = emptyCore (weaken z) := by
  rw [weaken_eq_subst, subst_emptyCore, ← weaken_eq_subst]

theorem instantiate_hfBody (p : Term Symbol Γ predTy) (y : Term Symbol Γ setTy) :
    instantiate p (.imp (buildClosed (.var .vz)) (.app (.var .vz) (weaken y))) = .imp (buildClosed p) (.app p y) := by
  change Term.imp (subst (Subst.single p) (buildClosed (.var .vz))) (.app p (instantiate p (weaken y))) = _
  rw [subst_buildClosed, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_adjoinsBody (m z a b : Term Symbol Γ setTy) :
    instantiate m (iffCore (member (.var .vz) (weaken z))
        (disjunctionFormula (member (.var .vz) (weaken a)) (sameMembers (.var .vz) (weaken b)))) =
      iffCore (member m z) (disjunctionFormula (member m a) (sameMembers m b)) := by
  unfold instantiate
  rw [subst_iffCore, subst_disjunctionFormula, subst_sameMembers]
  change iffCore (member m (instantiate m (weaken z))) (disjunctionFormula (member m (instantiate m (weaken a)))
    (sameMembers m (instantiate m (weaken b)))) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken,
    Mettapedia.Logic.HOL.instantiate_weaken]

end Building

/-! ## Native formulas of plain formulas -/

section Formulas

variable {Γ Γ' : Ctx Unit}

/-- **The native formula of a plain formula**, about a set term. -/
def plainAt (formula : PlainFormula) (w : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  nativeFormula formula.toFormula w Fin.elim0

theorem native_env_irrelevant {formula : Formula 0} {w : Term Symbol Γ setTy} (env : Fin 0 → Term Symbol Γ predTy) :
    nativeFormula formula w env = nativeFormula formula w Fin.elim0 :=
  congrArg (nativeFormula formula w) (Subsingleton.elim _ _)

theorem plainAt_possibly {label : StepLabel} (labelled : memberLabel label) (inner : PlainFormula)
    (w : Term Symbol Γ setTy) :
    plainAt (.possibly label inner) w =
      existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken w)) (plainAt inner (.var .vz))) := by
  simp only [plainAt, PlainFormula.toFormula, nativeFormula, if_pos labelled, native_env_irrelevant]

theorem plainAt_possibly_unlabelled {label : StepLabel} (unlabelled : ¬ memberLabel label) (inner : PlainFormula)
    (w : Term Symbol Γ setTy) : plainAt (.possibly label inner) w = falsity := by
  simp only [plainAt, PlainFormula.toFormula, nativeFormula, if_neg unlabelled]

theorem plainAt_necessarily {label : StepLabel} (labelled : memberLabel label) (inner : PlainFormula)
    (w : Term Symbol Γ setTy) :
    plainAt (.necessarily label inner) w =
      .all (σ := setTy) (.imp (member (.var .vz) (weaken w)) (plainAt inner (.var .vz))) := by
  simp only [plainAt, PlainFormula.toFormula, nativeFormula, if_pos labelled, native_env_irrelevant]

theorem plainAt_necessarily_unlabelled {label : StepLabel} (unlabelled : ¬ memberLabel label) (inner : PlainFormula)
    (w : Term Symbol Γ setTy) : plainAt (.necessarily label inner) w = truth := by
  simp only [plainAt, PlainFormula.toFormula, nativeFormula, if_neg unlabelled]

theorem subst_plainAt : ∀ {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (formula : PlainFormula)
    (w : Term Symbol Γ setTy), subst θ (plainAt formula w) = plainAt formula (subst θ w)
  | _, _, _, .top, _ => rfl
  | _, _, _, .bot, _ => rfl
  | _, _, θ, .and left right, w => by
    change subst θ (conjunctionFormula (plainAt left w) (plainAt right w)) =
      conjunctionFormula (plainAt left (subst θ w)) (plainAt right (subst θ w))
    rw [subst_conjunctionFormula, subst_plainAt θ left, subst_plainAt θ right]
  | _, _, θ, .or left right, w => by
    change subst θ (disjunctionFormula (plainAt left w) (plainAt right w)) =
      disjunctionFormula (plainAt left (subst θ w)) (plainAt right (subst θ w))
    rw [subst_disjunctionFormula, subst_plainAt θ left, subst_plainAt θ right]
  | _, _, θ, .possibly label inner, w => by
    by_cases labelled : memberLabel label
    · rw [plainAt_possibly labelled, plainAt_possibly labelled, subst_existentialInline, subst_conjunctionFormula]
      congr 2
      · exact congrArg (member (.var .vz)) (Mettapedia.Logic.HOL.subst_weaken θ w)
      · exact subst_plainAt (Subst.lift θ) inner (.var .vz)
    · rw [plainAt_possibly_unlabelled labelled, plainAt_possibly_unlabelled labelled]
      rfl
  | _, _, θ, .necessarily label inner, w => by
    by_cases labelled : memberLabel label
    · rw [plainAt_necessarily labelled, plainAt_necessarily labelled]
      change Term.all (.imp (member (.var .vz) (subst (Subst.lift θ) (weaken w)))
        (subst (Subst.lift θ) (plainAt inner (.var .vz)))) = _
      congr 2
      · exact congrArg (member (.var .vz)) (Mettapedia.Logic.HOL.subst_weaken θ w)
      · exact subst_plainAt (Subst.lift θ) inner (.var .vz)
    · rw [plainAt_necessarily_unlabelled labelled, plainAt_necessarily_unlabelled labelled]
      rfl

theorem weaken_plainAt {σ : Ty Unit} (formula : PlainFormula) (w : Term Symbol Γ setTy) :
    weaken (σ := σ) (plainAt formula w) = plainAt formula (weaken w) := by
  rw [weaken_eq_subst, subst_plainAt, ← weaken_eq_subst]

theorem instantiate_plainBody (t x : Term Symbol Γ setTy) (inner : PlainFormula) :
    instantiate t (conjunctionFormula (member (.var .vz) (weaken x)) (plainAt inner (.var .vz))) =
      conjunctionFormula (member t x) (plainAt inner t) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_plainAt]
  change conjunctionFormula (member t (instantiate t (weaken x))) (plainAt inner t) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_plainAllBody (t x : Term Symbol Γ setTy) (inner : PlainFormula) :
    instantiate t (.imp (member (.var .vz) (weaken x)) (plainAt inner (.var .vz))) =
      .imp (member t x) (plainAt inner t) := by
  change Term.imp (member t (instantiate t (weaken x))) (subst (Subst.single t) (plainAt inner (.var .vz))) = _
  rw [subst_plainAt, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem isCore_plainAt : ∀ (formula : PlainFormula) {Γ : Ctx Unit} {w : Term Symbol Γ setTy}, w.isCore = true →
    (plainAt formula w).isCore = true
  | .top, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .and left right, _, _, coreW =>
    isCore_conjunctionFormula (isCore_plainAt left coreW) (isCore_plainAt right coreW)
  | .or left right, _, _, coreW =>
    isCore_disjunctionFormula (isCore_plainAt left coreW) (isCore_plainAt right coreW)
  | .possibly label inner, _, w, coreW => by
    by_cases labelled : memberLabel label
    · rw [plainAt_possibly labelled]
      simp only [existentialInline, isCore, isCore_rename, Bool.and_true]
      exact isCore_conjunctionFormula (isCore_member rfl (by simp only [weaken, isCore_rename, coreW]))
        (isCore_plainAt inner rfl)
    · rw [plainAt_possibly_unlabelled labelled]
      rfl
  | .necessarily label inner, _, w, coreW => by
    by_cases labelled : memberLabel label
    · rw [plainAt_necessarily labelled]
      simp only [isCore, Bool.and_eq_true]
      exact ⟨isCore_member rfl (by simp only [weaken, isCore_rename, coreW]), isCore_plainAt inner rfl⟩
    · rw [plainAt_necessarily_unlabelled labelled]
      rfl

/-- **A literal**: the formula when the value is true, its negation when false. -/
def literal : Bool → Term Symbol Γ .prop → Term Symbol Γ .prop
  | true, p => p
  | false, p => negCore p

theorem subst_literal (θ : Subst Symbol Γ Γ') : ∀ (value : Bool) (p : Term Symbol Γ .prop),
    subst θ (literal value p) = literal value (subst θ p)
  | true, _ => rfl
  | false, _ => rfl

theorem isCore_literal : ∀ (value : Bool) {p : Term Symbol Γ .prop}, p.isCore = true → (literal value p).isCore = true
  | true, _, core => core
  | false, _, core => by simp only [literal, negCore, isCore, core, isCore_falsity, Bool.and_self]

/-- **A term's type, said of a set**: at every node, the node's native formula or its negation, as the term's value
of the node says. -/
def typeAt : PlainFormula → Pattern → Term Symbol Γ setTy → Term Symbol Γ .prop
  | .top, t, w => conjunctionFormula (literal (PlainFormula.top.eval t) (plainAt .top w)) truth
  | .bot, t, w => conjunctionFormula (literal (PlainFormula.bot.eval t) (plainAt .bot w)) truth
  | .and left right, t, w => conjunctionFormula (literal ((PlainFormula.and left right).eval t)
      (plainAt (.and left right) w)) (conjunctionFormula (typeAt left t w) (typeAt right t w))
  | .or left right, t, w => conjunctionFormula (literal ((PlainFormula.or left right).eval t)
      (plainAt (.or left right) w)) (conjunctionFormula (typeAt left t w) (typeAt right t w))
  | .possibly label inner, t, w => conjunctionFormula (literal ((PlainFormula.possibly label inner).eval t)
      (plainAt (.possibly label inner) w)) (typeAt inner t w)
  | .necessarily label inner, t, w => conjunctionFormula (literal ((PlainFormula.necessarily label inner).eval t)
      (plainAt (.necessarily label inner) w)) (typeAt inner t w)

theorem subst_typeAt (θ : Subst Symbol Γ Γ') :
    ∀ (formula : PlainFormula) (t : Pattern) (w : Term Symbol Γ setTy), subst θ (typeAt formula t w) = typeAt formula t (subst θ w)
  | .top, _, _ | .bot, _, _ => by
    simp only [typeAt, subst_conjunctionFormula, subst_literal, subst_plainAt]
    rfl
  | .and left right, t, w | .or left right, t, w => by
    simp only [typeAt, subst_conjunctionFormula, subst_literal, subst_plainAt, subst_typeAt θ left, subst_typeAt θ right]
  | .possibly label inner, t, w | .necessarily label inner, t, w => by
    simp only [typeAt, subst_conjunctionFormula, subst_literal, subst_plainAt, subst_typeAt θ inner]

theorem isCore_typeAt : ∀ (formula : PlainFormula) (t : Pattern) {w : Term Symbol Γ setTy}, w.isCore = true →
    (typeAt formula t w).isCore = true
  | .top, _, _, coreW | .bot, _, _, coreW =>
    isCore_conjunctionFormula (isCore_literal _ (isCore_plainAt _ coreW)) rfl
  | .and left right, t, _, coreW | .or left right, t, _, coreW =>
    isCore_conjunctionFormula (isCore_literal _ (isCore_plainAt _ coreW))
      (isCore_conjunctionFormula (isCore_typeAt left t coreW) (isCore_typeAt right t coreW))
  | .possibly _ inner, t, _, coreW | .necessarily _ inner, t, _, coreW =>
    isCore_conjunctionFormula (isCore_literal _ (isCore_plainAt _ coreW)) (isCore_typeAt inner t coreW)

/-- **A type reads only the node values.** -/
theorem typeAt_congr : ∀ (formula : PlainFormula) {t t' : Pattern},
    (∀ node ∈ formula.nodes, node.eval t = node.eval t') → ∀ w : Term Symbol Γ setTy, typeAt formula t w = typeAt formula t' w
  | .top, _, _, same, _ | .bot, _, _, same, _ => by
    simp only [typeAt, same _ List.mem_cons_self]
  | .and left right, _, _, same, w | .or left right, _, _, same, w => by
    simp only [typeAt, same _ List.mem_cons_self,
      typeAt_congr left (fun node found => same node (List.mem_cons_of_mem _ (List.mem_append_left _ found))) w,
      typeAt_congr right (fun node found => same node (List.mem_cons_of_mem _ (List.mem_append_right _ found))) w]
  | .possibly _ inner, _, _, same, w | .necessarily _ inner, _, _, same, w => by
    simp only [typeAt, same _ List.mem_cons_self,
      typeAt_congr inner (fun node found => same node (List.mem_cons_of_mem _ found)) w]

/-- Some formula of a list holds. -/
def anyFormula : List (Term Symbol Γ .prop) → Term Symbol Γ .prop
  | [] => falsity
  | φ :: φs => disjunctionFormula φ (anyFormula φs)

/-- **Some representative's type holds** of a set. -/
def someType (formula : PlainFormula) (reps : List Pattern) (w : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  anyFormula (reps.map fun r => typeAt formula r w)

theorem subst_someType (θ : Subst Symbol Γ Γ') (formula : PlainFormula) :
    ∀ (reps : List Pattern) (w : Term Symbol Γ setTy), subst θ (someType formula reps w) = someType formula reps (subst θ w)
  | [], _ => rfl
  | r :: reps, w => by
    change subst θ (disjunctionFormula (typeAt formula r w) (someType formula reps w)) =
      disjunctionFormula (typeAt formula r (subst θ w)) (someType formula reps (subst θ w))
    rw [subst_disjunctionFormula, subst_typeAt, subst_someType θ formula reps]

theorem isCore_someType (formula : PlainFormula) :
    ∀ (reps : List Pattern) {w : Term Symbol Γ setTy}, w.isCore = true → (someType formula reps w).isCore = true
  | [], _, _ => rfl
  | r :: reps, _, coreW =>
    isCore_disjunctionFormula (isCore_typeAt formula r coreW) (isCore_someType formula reps coreW)

/-- **The predicate `some representative's type holds`.** -/
def someTypePred (formula : PlainFormula) (reps : List Pattern) : Term Symbol Γ predTy :=
  .lam (someType formula reps (.var .vz))

theorem weaken_someTypePred {σ : Ty Unit} (formula : PlainFormula) (reps : List Pattern) :
    weaken (σ := σ) (someTypePred (Γ := Γ) formula reps) = someTypePred formula reps := by
  change Term.lam (rename (Rename.lift Rename.weaken) (someType formula reps (.var .vz))) = _
  rw [rename_eq_subst, subst_someType]
  rfl

end Formulas

/-! ## Proofs -/

section Proofs

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- A literal whose value is true. -/
def literalTrue {value : Bool} {p : Term Symbol Γ .prop} (holds : value = true) (proof : Proof Δ (literal value p)) :
    Proof Δ p :=
  Proof.cast (by rw [holds]; rfl) proof

/-- A literal whose value is false. -/
def literalFalse {value : Bool} {p : Term Symbol Γ .prop} (fails : value = false) (proof : Proof Δ (literal value p)) :
    Proof Δ (negCore p) :=
  Proof.cast (by rw [fails]; rfl) proof

/-- A proof as a literal whose value is true. -/
def asTrue {value : Bool} {p : Term Symbol Γ .prop} (holds : value = true) (proof : Proof Δ p) :
    Proof Δ (literal value p) :=
  Proof.cast (by rw [holds]; rfl) proof

/-- A refutation as a literal whose value is false. -/
def asFalse {value : Bool} {p : Term Symbol Γ .prop} (fails : value = false) (proof : Proof Δ (negCore p)) :
    Proof Δ (literal value p) :=
  Proof.cast (by rw [fails]; rfl) proof

/-- The literal of a conjunction, from its two literals. -/
def andLiteral {p q : Term Symbol Γ .prop} : ∀ {first second : Bool}, Proof Δ (literal first p) →
    Proof Δ (literal second q) → Proof Δ (literal (first && second) (conjunctionFormula p q))
  | true, true, left, right => conjunctionIntro left right
  | true, false, _, right => .impI (.impE (right.prepend _) (conjunctionRight (Proof.newest _)))
  | false, _, left, _ => .impI (.impE (left.prepend _) (conjunctionLeft (Proof.newest _)))

/-- The literal of a disjunction, from its two literals. -/
def orLiteral {p q : Term Symbol Γ .prop} : ∀ {first second : Bool}, Proof Δ (literal first p) →
    Proof Δ (literal second q) → Proof Δ (literal (first || second) (disjunctionFormula p q))
  | true, _, left, _ => disjunctionLeft left
  | false, true, _, right => disjunctionRight right
  | false, false, left, right => .impI (disjunctionElim (Proof.newest _)
      (.impE ((left.prepend _).prepend _) (Proof.newest _)) (.impE ((right.prepend _).prepend _) (Proof.newest _)))

/-- **The node literal of a type.** -/
def nodeLiteral {t : Pattern} {w : Term Symbol Γ setTy} : ∀ {formula : PlainFormula},
    Proof Δ (typeAt formula t w) → Proof Δ (literal (formula.eval t) (plainAt formula w))
  | .top, proof | .bot, proof | .and _ _, proof | .or _ _, proof | .possibly _ _, proof | .necessarily _ _, proof =>
    conjunctionLeft proof

/-- Same members, both ways round. -/
def sameRefl (b : Term Symbol Γ setTy) : Proof Δ (sameMembers b b) :=
  .allI (Proof.iffIntro (Proof.newest _) (Proof.newest _))

def sameSymm {m b : Term Symbol Γ setTy} (same : Proof Δ (sameMembers m b)) : Proof Δ (sameMembers b m) := by
  refine .allI ?_
  have both := sameAt (Proof.cast (weaken_sameMembers m b) same.lift) (.var .vz)
  exact conjunctionIntro (conjunctionRight both) (conjunctionLeft both)

/-- The members of a set adjoining `b` to `a`. -/
def adjoinsAt {z a b : Term Symbol Γ setTy} (adjoined : Proof Δ (adjoins z a b)) (m : Term Symbol Γ setTy) :
    Proof Δ (iffCore (member m z) (disjunctionFormula (member m a) (sameMembers m b))) :=
  Proof.cast (instantiate_adjoinsBody m z a b)
    (.allE (φ := iffCore (member (.var .vz) (weaken z))
      (disjunctionFormula (member (.var .vz) (weaken a)) (sameMembers (.var .vz) (weaken b)))) m adjoined)

/-- The adjoined set is a member. -/
def adjoinedMember {z a b : Term Symbol Γ setTy} (adjoined : Proof Δ (adjoins z a b)) : Proof Δ (member b z) :=
  (adjoinsAt adjoined b).iffBackward (disjunctionRight (sameRefl b))

/-- A member of `a` is a member of the set adjoining to it. -/
def keptMember {z a b m : Term Symbol Γ setTy} (adjoined : Proof Δ (adjoins z a b)) (inside : Proof Δ (member m a)) :
    Proof Δ (member m z) :=
  (adjoinsAt adjoined m).iffBackward (disjunctionLeft inside)

/-- A hypothesis about the outer context, read under a new set variable and a new hypothesis. -/
def under {φ : Term Symbol Γ .prop} (ψ : Term Symbol (setTy :: Γ) .prop) (proof : Proof Δ φ) :
    Proof (ψ :: weakenHyps (σ := setTy) Δ) (weaken φ) :=
  proof.lift.prepend ψ

/-- **A plain formula moves along same members.** -/
def transfer : ∀ (formula : PlainFormula) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {m b : Term Symbol Γ setTy},
    Proof Δ (sameMembers m b) → Proof Δ (plainAt formula m) → Proof Δ (plainAt formula b)
  | .top, _, _, _, _, _, _ => truthIntro
  | .bot, _, _, _, _, _, proof => Proof.absurd proof
  | .and left right, _, _, _, _, same, proof =>
    conjunctionIntro (transfer left same (conjunctionLeft proof)) (transfer right same (conjunctionRight proof))
  | .or left right, _, _, _, _, same, proof =>
    disjunctionElim proof (disjunctionLeft (transfer left (same.prepend _) (Proof.newest _)))
      (disjunctionRight (transfer right (same.prepend _) (Proof.newest _)))
  | .possibly label inner, _, Δ, m, b, same, proof => by
    refine if labelled : memberLabel label then ?_ else ?_
    · refine existentialElim (Proof.cast (plainAt_possibly labelled inner m) proof) ?_
      rw [weaken_plainAt, plainAt_possibly labelled]
      refine existentialIntro (.var .vz) (Proof.cast (instantiate_plainBody _ _ _).symm ?_)
      have same' : Proof (conjunctionFormula (member (.var .vz) (weaken m)) (plainAt inner (.var .vz)) ::
          weakenHyps (σ := setTy) Δ) (sameMembers (weaken m) (weaken b)) :=
        Proof.cast (weaken_sameMembers m b) (under _ same)
      exact conjunctionIntro ((sameAt same' (.var .vz)).iffForward (conjunctionLeft (Proof.newest _)))
        (conjunctionRight (Proof.newest _))
    · exact Proof.absurd (Proof.cast (plainAt_possibly_unlabelled labelled inner m) proof)
  | .necessarily label inner, _, Δ, m, b, same, proof => by
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [plainAt_necessarily labelled]
      refine .allI (.impI ?_)
      have every := Proof.cast (instantiate_plainAllBody (.var .vz) (weaken m) inner)
        (.allE (.var .vz) (Proof.cast ((weaken_plainAt _ _).trans (plainAt_necessarily labelled inner _)) proof.lift))
      have same' : Proof (member (.var .vz) (weaken b) :: weakenHyps (σ := setTy) Δ)
          (sameMembers (weaken m) (weaken b)) :=
        Proof.cast (weaken_sameMembers m b) (under _ same)
      exact .impE (every.prepend _) ((sameAt same' (.var .vz)).iffBackward (Proof.newest _))
    · exact Proof.cast (plainAt_necessarily_unlabelled labelled inner b).symm truthIntro

theorem eval_possibly_empty (label : StepLabel) (inner : PlainFormula) :
    (PlainFormula.possibly label inner).eval (set []) = false := by
  simp [PlainFormula.eval, set, membersOf]

theorem eval_necessarily_empty (label : StepLabel) (inner : PlainFormula) :
    (PlainFormula.necessarily label inner).eval (set []) = true := by
  simp [PlainFormula.eval, set, membersOf]

/-- **The empty sets have the empty set's type.** -/
def emptyType : ∀ (formula : PlainFormula) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {z : Term Symbol Γ setTy},
    Proof Δ (emptyCore z) → Proof Δ (typeAt formula (set []) z)
  | .top, _, _, _, _ => conjunctionIntro truthIntro truthIntro
  | .bot, _, _, _, _ => conjunctionIntro (.impI (Proof.newest _)) truthIntro
  | .and left right, _, _, _, empty =>
    conjunctionIntro (andLiteral (nodeLiteral (emptyType left empty)) (nodeLiteral (emptyType right empty)))
      (conjunctionIntro (emptyType left empty) (emptyType right empty))
  | .or left right, _, _, _, empty =>
    conjunctionIntro (orLiteral (nodeLiteral (emptyType left empty)) (nodeLiteral (emptyType right empty)))
      (conjunctionIntro (emptyType left empty) (emptyType right empty))
  | .possibly label inner, _, _, z, empty => by
    refine conjunctionIntro (asFalse (eval_possibly_empty label inner) ?_) (emptyType inner empty)
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [plainAt_possibly labelled]
      refine .impI (existentialElim (Proof.newest _) ?_)
      have none := Proof.cast (weaken_emptyCore z) (under (conjunctionFormula (member (.var .vz) (weaken z))
        (plainAt inner (.var .vz))) (empty.prepend (existentialInline (σ := setTy)
          (conjunctionFormula (member (.var .vz) (weaken z)) (plainAt inner (.var .vz))))))
      exact .impE (noMemberAt none (.var .vz)) (conjunctionLeft (Proof.newest _))
    · rw [plainAt_possibly_unlabelled labelled]
      exact .impI (Proof.newest _)
  | .necessarily label inner, _, _, z, empty => by
    refine conjunctionIntro (asTrue (eval_necessarily_empty label inner) ?_) (emptyType inner empty)
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [plainAt_necessarily labelled]
      refine .allI (.impI (Proof.absurd ?_))
      have none := Proof.cast (weaken_emptyCore z) (under (member (.var .vz) (weaken z)) empty)
      exact .impE (noMemberAt none (.var .vz)) (Proof.newest _)
    · rw [plainAt_necessarily_unlabelled labelled]
      exact truthIntro

/-- **Adjunction**: a set adjoining `b` to `a` has the type of the term adjoining `b`'s type to `a`'s. -/
def adjoinType : ∀ (formula : PlainFormula) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}
    {a b z : Term Symbol Γ setTy} {whole term : Pattern},
    Proof Δ (typeAt formula whole a) → Proof Δ (typeAt formula term b) → Proof Δ (adjoins z a b) →
      Proof Δ (typeAt formula (insertTerm term whole) z)
  | .top, _, _, _, _, _, _, _, _, _, _ => conjunctionIntro truthIntro truthIntro
  | .bot, _, _, _, _, _, _, _, _, _, _ => conjunctionIntro (.impI (Proof.newest _)) truthIntro
  | .and left right, _, _, _, _, _, _, _, typeA, typeB, adjoined =>
    have first := adjoinType left (conjunctionLeft (conjunctionRight typeA)) (conjunctionLeft (conjunctionRight typeB))
      adjoined
    have second := adjoinType right (conjunctionRight (conjunctionRight typeA))
      (conjunctionRight (conjunctionRight typeB)) adjoined
    conjunctionIntro (andLiteral (nodeLiteral first) (nodeLiteral second)) (conjunctionIntro first second)
  | .or left right, _, _, _, _, _, _, _, typeA, typeB, adjoined =>
    have first := adjoinType left (conjunctionLeft (conjunctionRight typeA)) (conjunctionLeft (conjunctionRight typeB))
      adjoined
    have second := adjoinType right (conjunctionRight (conjunctionRight typeA))
      (conjunctionRight (conjunctionRight typeB)) adjoined
    conjunctionIntro (orLiteral (nodeLiteral first) (nodeLiteral second)) (conjunctionIntro first second)
  | .possibly label inner, _, Δ, a, b, z, whole, term, typeA, typeB, adjoined => by
    refine conjunctionIntro ?_ (adjoinType inner (conjunctionRight typeA) (conjunctionRight typeB) adjoined)
    have nodeA : Proof Δ (literal ((PlainFormula.possibly label inner).eval whole) (plainAt (.possibly label inner) a)) :=
      nodeLiteral typeA
    have nodeB : Proof Δ (literal (inner.eval term) (plainAt inner b)) := nodeLiteral (conjunctionRight typeB)
    rw [PlainFormula.eval_insert_possibly]
    refine if labelled : memberLabel label then ?_ else ?_
    · refine if holdsB : inner.eval term = true then ?_ else ?_
      · refine asTrue (by simp [labelled, holdsB]) (Proof.cast (plainAt_possibly labelled inner z).symm ?_)
        exact existentialIntro b (Proof.cast (instantiate_plainBody b z inner).symm
          (conjunctionIntro (adjoinedMember adjoined) (literalTrue holdsB nodeB)))
      · have failsB : inner.eval term = false := Bool.eq_false_iff.mpr holdsB
        refine if holdsA : (PlainFormula.possibly label inner).eval whole = true then ?_ else ?_
        · refine asTrue (by simp [holdsA]) ?_
          refine existentialElim (Proof.cast (plainAt_possibly labelled inner a) (literalTrue holdsA nodeA)) ?_
          rw [weaken_plainAt, plainAt_possibly labelled]
          refine existentialIntro (.var .vz) (Proof.cast (instantiate_plainBody _ _ _).symm ?_)
          have adjoined' := Proof.cast (weaken_adjoins z a b) (under (conjunctionFormula (member (.var .vz) (weaken a))
            (plainAt inner (.var .vz))) adjoined)
          exact conjunctionIntro (keptMember adjoined' (conjunctionLeft (Proof.newest _)))
            (conjunctionRight (Proof.newest _))
        · have failsA : (PlainFormula.possibly label inner).eval whole = false := Bool.eq_false_iff.mpr holdsA
          refine asFalse (by simp [failsA, failsB]) ?_
          refine .impI (existentialElim (Proof.cast (plainAt_possibly labelled inner z) (Proof.newest _)) ?_)
          let body := conjunctionFormula (member (.var .vz) (weaken z)) (plainAt inner (.var .vz))
          have adjoined' := Proof.cast (weaken_adjoins z a b)
            (under body (adjoined.prepend (plainAt (.possibly label inner) z)))
          refine disjunctionElim ((adjoinsAt adjoined' (.var .vz)).iffForward (conjunctionLeft (Proof.newest _))) ?_ ?_
          · have notA := Proof.cast ((weaken_negCore _).trans (congrArg negCore (weaken_plainAt _ _)))
              (under body ((literalFalse failsA nodeA).prepend (plainAt (.possibly label inner) z)))
            refine .impE (Proof.cast (congrArg negCore (plainAt_possibly labelled inner (weaken a))) (notA.prepend _)) ?_
            refine existentialIntro (.var .vz) (Proof.cast (instantiate_plainBody _ _ _).symm ?_)
            exact conjunctionIntro (Proof.newest _) (conjunctionRight ((Proof.newest _).prepend _))
          · have notB := Proof.cast ((weaken_negCore _).trans (congrArg negCore (weaken_plainAt _ _)))
              (under body ((literalFalse failsB nodeB).prepend (plainAt (.possibly label inner) z)))
            exact .impE (notB.prepend _) (transfer inner (Proof.newest _) (conjunctionRight ((Proof.newest _).prepend _)))
    · rw [plainAt_possibly_unlabelled labelled]
      exact asFalse (by simp [PlainFormula.eval, labelled]) (.impI (Proof.newest _))
  | .necessarily label inner, _, Δ, a, b, z, whole, term, typeA, typeB, adjoined => by
    refine conjunctionIntro ?_ (adjoinType inner (conjunctionRight typeA) (conjunctionRight typeB) adjoined)
    have nodeA : Proof Δ (literal ((PlainFormula.necessarily label inner).eval whole)
        (plainAt (.necessarily label inner) a)) :=
      nodeLiteral typeA
    have nodeB : Proof Δ (literal (inner.eval term) (plainAt inner b)) := nodeLiteral (conjunctionRight typeB)
    rw [PlainFormula.eval_insert_necessarily]
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [plainAt_necessarily labelled]
      refine if holdsB : inner.eval term = true then ?_ else ?_
      · refine if holdsA : (PlainFormula.necessarily label inner).eval whole = true then ?_ else ?_
        · refine asTrue (by simp [holdsA, holdsB]) (.allI (.impI ?_))
          have adjoined' := Proof.cast (weaken_adjoins z a b) (under (member (.var .vz) (weaken z)) adjoined)
          refine disjunctionElim ((adjoinsAt adjoined' (.var .vz)).iffForward (Proof.newest _)) ?_ ?_
          · have every := Proof.cast (instantiate_plainAllBody (.var .vz) (weaken a) inner)
              (.allE (.var .vz) (Proof.cast ((weaken_plainAt _ _).trans (plainAt_necessarily labelled inner _))
                (literalTrue holdsA nodeA).lift))
            exact .impE ((every.prepend _).prepend _) (Proof.newest _)
          · have innerB := Proof.cast (weaken_plainAt inner b)
              (under (member (.var .vz) (weaken z)) (literalTrue holdsB nodeB))
            exact transfer inner (sameSymm (Proof.newest _)) (innerB.prepend _)
        · have failsA : (PlainFormula.necessarily label inner).eval whole = false := Bool.eq_false_iff.mpr holdsA
          refine asFalse (by simp [failsA]) (.impI ?_)
          refine .impE (Proof.cast (congrArg negCore (plainAt_necessarily labelled inner a))
            ((literalFalse failsA nodeA).prepend _)) ?_
          refine .allI (.impI ?_)
          let everyZ := Term.all (σ := setTy) (.imp (member (.var .vz) (weaken z)) (plainAt inner (.var .vz)))
          have every := Proof.cast (instantiate_plainAllBody (.var .vz) (weaken z) inner)
            (.allE (.var .vz) (Proof.cast ((congrArg weaken (plainAt_necessarily labelled inner z).symm).trans
              ((weaken_plainAt _ _).trans (plainAt_necessarily labelled inner _))) (Proof.newest (Δ := Δ) everyZ).lift))
          have adjoined' := Proof.cast (weaken_adjoins z a b) (under (member (.var .vz) (weaken a))
            (adjoined.prepend everyZ))
          exact .impE (every.prepend _) (keptMember adjoined' (Proof.newest _))
      · have failsB : inner.eval term = false := Bool.eq_false_iff.mpr holdsB
        refine asFalse (by simp [labelled, failsB]) (.impI ?_)
        let everyZ := Term.all (σ := setTy) (.imp (member (.var .vz) (weaken z)) (plainAt inner (.var .vz)))
        have atB := Proof.cast (instantiate_plainAllBody b z inner) (.allE b (Proof.newest (Δ := Δ) everyZ))
        exact .impE ((literalFalse failsB nodeB).prepend _) (.impE atB (adjoinedMember (adjoined.prepend _)))
    · rw [plainAt_necessarily_unlabelled labelled]
      exact asTrue (by simp [PlainFormula.eval, labelled]) truthIntro

/-- Some representative's type, from one of them. -/
def someIntro {formula : PlainFormula} {w : Term Symbol Γ setTy} : ∀ (reps : List Pattern) (index : Fin reps.length),
    Proof Δ (typeAt formula (reps.get index) w) → Proof Δ (someType formula reps w)
  | _ :: _, ⟨0, _⟩, proof => disjunctionLeft proof
  | _ :: reps, ⟨index + 1, bound⟩, proof => disjunctionRight (someIntro reps ⟨index, Nat.lt_of_succ_lt_succ bound⟩ proof)

/-- **Case analysis over the representatives** whose type may hold. -/
def someCases {formula : PlainFormula} {w : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop} :
    ∀ {Δ : List (Term Symbol Γ .prop)} (reps : List Pattern), Proof Δ (someType formula reps w) →
      (∀ index : Fin reps.length, Proof (typeAt formula (reps.get index) w :: Δ) goal) → Proof Δ goal
  | _, [], cases, _ => Proof.absurd cases
  | Δ, _ :: reps, cases, branch =>
    disjunctionElim cases (branch ⟨0, Nat.succ_pos _⟩)
      (someCases (Δ := someType formula reps w :: Δ) reps (Proof.newest _) fun index =>
        Proof.insertSecond _ (branch index.succ))

/-- The predicate applied, from the type. -/
def someTypeExpand {formula : PlainFormula} {reps : List Pattern} {w : Term Symbol Γ setTy} (coreW : w.isCore = true)
    (proof : Proof Δ (someType formula reps w)) : Proof Δ (.app (someTypePred formula reps) w) :=
  Proof.betaExpand (isCore_someType formula reps rfl) coreW
    (Proof.cast (by unfold instantiate; rw [subst_someType]; rfl) proof)

/-- The type, from the predicate applied. -/
def someTypeReduce {formula : PlainFormula} {reps : List Pattern} {w : Term Symbol Γ setTy} (coreW : w.isCore = true)
    (proof : Proof Δ (.app (someTypePred formula reps) w)) : Proof Δ (someType formula reps w) :=
  Proof.cast (by unfold instantiate; rw [subst_someType]; rfl)
    (Proof.betaReduce (isCore_someType formula reps rfl) coreW proof)

theorem found_beq {formula : PlainFormula} {reps : List Pattern} {target : Pattern}
    (found : ∃ r ∈ reps, formula.vec r = formula.vec target) :
    ∃ r ∈ reps, (formula.vec r == formula.vec target) = true := by
  obtain ⟨r, inside, same⟩ := found
  exact ⟨r, inside, beq_iff_eq.mpr same⟩

/-- The position of a representative with a given vector. -/
def repIndex (formula : PlainFormula) (reps : List Pattern) (target : Pattern)
    (found : ∃ r ∈ reps, formula.vec r = formula.vec target) :
    {index : Fin reps.length // formula.vec (reps.get index) = formula.vec target} :=
  match chooseIndex reps (fun r => formula.vec r == formula.vec target) (found_beq found) with
  | ⟨index, test⟩ => ⟨index, beq_iff_eq.mp test⟩

/-- A type moves to a representative with the same vector. -/
def toRep {formula : PlainFormula} {reps : List Pattern} {target : Pattern} {w : Term Symbol Γ setTy}
    (found : ∃ r ∈ reps, formula.vec r = formula.vec target) (proof : Proof Δ (typeAt formula target w)) :
    Proof Δ (someType formula reps w) :=
  let chosen := repIndex formula reps target found
  someIntro reps chosen.1
    (Proof.cast (typeAt_congr formula (PlainFormula.eval_of_vec chosen.2.symm) w) proof)

/-- **Classification**: a hereditarily finite set has the type of one of the representatives, when they hold the empty
set's vector and every adjunction's. -/
def classify (formula : PlainFormula) (reps : List Pattern)
    (base : ∃ r ∈ reps, formula.vec r = formula.vec (set []))
    (adjoin : ∀ whole ∈ reps, ∀ term ∈ reps, ∃ r ∈ reps, formula.vec r = formula.vec (insertTerm term whole))
    {y : Term Symbol Γ setTy} (coreY : y.isCore = true) (finite : Proof Δ (hfFormula y)) :
    Proof Δ (someType formula reps y) := by
  have instance' : Proof Δ (.imp (buildClosed (someTypePred formula reps)) (.app (someTypePred formula reps) y)) :=
    Proof.cast (instantiate_hfBody _ y)
      (.allE (φ := .imp (buildClosed (.var .vz)) (.app (.var .vz) (weaken y))) (someTypePred formula reps) finite)
  refine someTypeReduce coreY (.impE instance' (conjunctionIntro ?_ ?_))
  · rw [weaken_someTypePred]
    exact .allI (.impI (someTypeExpand rfl (toRep base (emptyType formula (Proof.newest _)))))
  · simp only [weaken_someTypePred]
    refine .allI (.allI (.allI (.impI (.impI (.impI (.impI ?_))))))
    refine someTypeExpand rfl ?_
    refine someCases reps (someTypeReduce rfl (.hyp ⟨3, by simp⟩)) fun first => ?_
    refine someCases reps (someTypeReduce rfl (.hyp ⟨3, by simp⟩)) fun second => ?_
    exact toRep (adjoin _ (List.get_mem _ _) _ (List.get_mem _ _))
      (adjoinType formula (Proof.prepend _ (Proof.newest _)) (Proof.newest _) (.hyp ⟨2, by simp⟩))

end Proofs

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
