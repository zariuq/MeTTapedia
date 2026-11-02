import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastVerdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofTerms

/-!
# Proof terms for past modalities and quantifiers over a type

For a past modality or a quantifier over a type with a plain modal body, at a hereditary term, the calculus of the
package proves the sentence (`pastSentence`) or its negation from the laws of the empty set, the power set and
separation, with no excluded middle. The verdict on the representatives (`pastVerdict`) chooses every branch and
witness.

- **Witness sets are hereditarily finite** (`hfWitness`): the set term of a hereditary term is built from the empty set
  by adjoining its members one at a time, each new (`buildList`). Repeated members are dropped before the step, so the
  step is fresh (`freshWitness`) and adjoins exactly the members (`adjoinsWitness`).
- **Witness search**: a past modality that holds is proved at the term adjoined to a representative without a conflict
  (`beforeProof`), a quantifier over a type at a representative (`someProof`); the native type there is proved by the
  package's prover (`proveNative`).
- **Induction along membership**: a refutation instantiates hereditary finiteness with the predicate `some
  representative's type holds` (`classify`) and refutes each representative: by the body's literal, or by a conflict
  with the term (`conflictRefutes`), whose literal contradicts the term's membership.
- **The compiler** (`compilePastSentence`) proves exactly the sentences that hold (`compilePastSentence_isLeft_iff`),
  and in the package each derivation is a closed proof term (`compilePastVerdict`). So such a type holds exactly when
  its proposition has a closed proof term in the package (`sat_iff_pastProofTerm`), relative to the cardinals that give
  the package its set model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member separate)
open Mettapedia.Logic.HOL.Term (isCore isCore_rename)

/-! ## Substitutions -/

section Substitutions

variable {Γ Γ' : Ctx Unit}

theorem subst_powerIter (θ : Subst Symbol Γ Γ') : ∀ k : ℕ, subst θ (powerIter k) = powerIter k
  | 0 => rfl
  | k + 1 => by
    change Term.app (.const .power) (subst θ (powerIter k)) = _
    rw [subst_powerIter θ k]
    rfl

theorem subst_witness (θ : Subst Symbol Γ Γ') (term : Pattern) : subst θ (witness term) = witness term := by
  change Term.app (.app (.const .separate) (subst θ (powerIter (height term))))
    (.lam (subst (Subst.lift θ) (describesOne (membersOf term) (.var .vz)))) = _
  rw [subst_powerIter, subst_describesOne]
  rfl

theorem weaken_witness {σ : Ty Unit} (term : Pattern) :
    weaken (σ := σ) (witness term : Term Symbol Γ setTy) = witness term := by
  rw [weaken_eq_subst, subst_witness]

theorem subst_hfFormula (θ : Subst Symbol Γ Γ') (y : Term Symbol Γ setTy) :
    subst θ (hfFormula y) = hfFormula (subst θ y) := by
  change Term.all (.imp (subst (Subst.lift θ) (buildClosed (.var .vz))) (.app (.var .vz) (subst (Subst.lift θ) (weaken y))))
    = _
  rw [subst_buildClosed, Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem subst_pastFormula (θ : Subst Symbol Γ Γ') : ∀ (formula : Formula 0), formula.pastPlain = true →
    ∀ x : Term Symbol Γ setTy, subst θ (pastFormula formula x) = pastFormula formula (subst θ x) := by
  intro formula past x
  have native : ∀ {inner : Formula 0}, inner.plainModal = true →
      subst (Subst.lift θ) (nativeFormula inner (.var .vz) Fin.elim0) = nativeFormula inner (.var .vz) Fin.elim0 :=
    fun plain => (subst_nativeFormula_regional _ _ (Formula.regional_of_plainModal _ plain) _ _).trans
      (native_env_irrelevant _)
  cases formula
  case sometimeBefore label inner =>
    by_cases labelled : memberLabel label
    · simp only [pastFormula, if_pos labelled, subst_existentialInline, subst_conjunctionFormula, subst_hfFormula,
        native past]
      congr 3
      exact congrArg (fun t => member t (.var .vz)) (Mettapedia.Logic.HOL.subst_weaken θ x)
    · simp only [pastFormula, if_neg labelled]
      rfl
  case alwaysBefore label inner =>
    by_cases labelled : memberLabel label
    · simp only [pastFormula, if_pos labelled]
      change Term.all (.imp (subst (Subst.lift θ) (hfFormula (.var .vz)))
        (.imp (member (subst (Subst.lift θ) (weaken x)) (.var .vz))
          (subst (Subst.lift θ) (nativeFormula inner (.var .vz) Fin.elim0)))) = _
      rw [subst_hfFormula, native past, Mettapedia.Logic.HOL.subst_weaken]
      rfl
    · simp only [pastFormula, if_neg labelled]
      rfl
  case someOf type inner =>
    simp only [pastFormula, subst_existentialInline, subst_conjunctionFormula, subst_hfFormula, subst_typedFormula,
      native past]
    rfl
  case everyOf type inner =>
    simp only [pastFormula]
    change Term.all (.imp (subst (Subst.lift θ) (hfFormula (.var .vz)))
      (.imp (subst (Subst.lift θ) (typedFormula type (.var .vz)))
        (subst (Subst.lift θ) (nativeFormula inner (.var .vz) Fin.elim0)))) = _
    rw [subst_hfFormula, subst_typedFormula, native past]
    rfl
  all_goals simp [Formula.pastPlain] at past

theorem instantiate_pastBody {formula : Formula 0} (past : formula.pastPlain = true) (term : Pattern)
    (t : Term Symbol Γ setTy) :
    instantiate t (conjunctionFormula (describes term (.var .vz)) (pastFormula formula (.var .vz))) =
      conjunctionFormula (describes term t) (pastFormula formula t) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_describes, subst_pastFormula _ formula past]
  rfl

end Substitutions

/-! ## Building witness sets -/

section Building

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem instantiate_buildEmpty (p : Term Symbol Γ predTy) (z : Term Symbol Γ setTy) :
    instantiate z (.imp (emptyCore (.var .vz)) (.app (weaken p) (.var .vz))) = .imp (emptyCore z) (.app p z) := by
  change Term.imp (subst (Subst.single z) (emptyCore (.var .vz))) (.app (instantiate z (weaken p)) z) = _
  rw [subst_emptyCore, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_buildFirst (p : Term Symbol Γ predTy) (a : Term Symbol Γ setTy) :
    instantiate a (Term.all (σ := setTy) (.all (σ := setTy) (buildStep (weaken (weaken (weaken p)))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))) =
    .all (.all (buildStep (weaken (weaken p)) (weaken (weaken a)) (.var (.vs .vz)) (.var .vz))) := by
  change Term.all (.all (subst (Subst.lift (Subst.lift (Subst.single a))) (buildStep (weaken (weaken (weaken p)))
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))) = _
  rw [subst_buildStep]
  congr 3
  rw [Mettapedia.Logic.HOL.subst_weaken, Mettapedia.Logic.HOL.subst_weaken]
  exact congrArg (fun t => weaken (weaken t)) (Mettapedia.Logic.HOL.instantiate_weaken a p)

theorem instantiate_buildSecond (p : Term Symbol Γ predTy) (a b : Term Symbol Γ setTy) :
    instantiate b (Term.all (σ := setTy) (buildStep (weaken (weaken p)) (weaken (weaken a)) (.var (.vs .vz))
      (.var .vz))) = .all (buildStep (weaken p) (weaken a) (weaken b) (.var .vz)) := by
  change Term.all (subst (Subst.lift (Subst.single b)) (buildStep (weaken (weaken p)) (weaken (weaken a))
    (.var (.vs .vz)) (.var .vz))) = _
  rw [subst_buildStep, Mettapedia.Logic.HOL.subst_weaken, Mettapedia.Logic.HOL.subst_weaken]
  change Term.all (buildStep (weaken (instantiate b (weaken p))) (weaken (instantiate b (weaken a))) _ _) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_buildThird (p : Term Symbol Γ predTy) (a b z : Term Symbol Γ setTy) :
    instantiate z (buildStep (weaken p) (weaken a) (weaken b) (.var .vz)) = buildStep p a b z := by
  unfold instantiate
  rw [subst_buildStep]
  change buildStep (instantiate z (weaken p)) (instantiate z (weaken a)) (instantiate z (weaken b)) z = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken,
    Mettapedia.Logic.HOL.instantiate_weaken]

/-- The empty step of building, at a set. -/
def buildEmptyAt {p : Term Symbol Γ predTy} (closed : Proof Δ (buildClosed p)) (z : Term Symbol Γ setTy) :
    Proof Δ (.imp (emptyCore z) (.app p z)) :=
  Proof.cast (instantiate_buildEmpty p z) (.allE z (conjunctionLeft closed))

/-- The adjunction step of building, at three sets. -/
def buildAt {p : Term Symbol Γ predTy} (closed : Proof Δ (buildClosed p)) (a b z : Term Symbol Γ setTy) :
    Proof Δ (buildStep p a b z) :=
  Proof.cast (instantiate_buildThird p a b z) (.allE z (Proof.cast (instantiate_buildSecond p a b)
    (.allE b (Proof.cast (instantiate_buildFirst p a) (.allE a (conjunctionRight closed))))))

/-- **The set term of the empty term is empty.** -/
def emptyWitness (laws : HasLaws Δ) : Proof Δ (emptyCore (witness (set []))) := by
  change Proof Δ (.all (negCore (member (.var .vz) (weaken (witness (set []))))))
  rw [weaken_witness]
  exact .allI (.impI (describesForward (describedWitness ((laws.lift setTy).prepend _) (set [])
    (set_hf fun _ found => nomatch found)) (Proof.newest _)))

/-- The members a list keeps once those of the set of `v` are dropped. -/
def apartFromSet (v : Pattern) (values : List Pattern) : List Pattern := values.filter fun u => !sameSet v u

/-- **Adjoining a new member**: the set term of `v` is not a member of the set term of the members apart from it. -/
def freshWitness (laws : HasLaws Δ) {v : Pattern} (vHolds : IsHF v) {values : List Pattern}
    (all : ∀ u ∈ values, IsHF u) : Proof Δ (negCore (member (witness v) (witness (set (apartFromSet v values))))) := by
  have apartHolds : ∀ u ∈ apartFromSet v values, IsHF u := fun u inside => all u (List.mem_filter.mp inside).1
  refine .impI (oneCases (apartFromSet v values) (describesForward (describedWitness (laws.prepend _) _
    (set_hf apartHolds)) (Proof.newest _)) fun index => ?_)
  have uIn := List.get_mem (apartFromSet v values) index
  have differ : zfOf v ≠ zfOf ((apartFromSet v values).get index) := fun same => by
    have apart := (List.mem_filter.mp uIn).2
    rw [(sameSet_iff v vHolds _ (apartHolds _ uIn)).mpr same] at apart
    exact Bool.false_ne_true apart
  have laws' := (laws.prepend (member (witness v) (witness (set (apartFromSet v values))))).prepend
    (describes ((apartFromSet v values).get index) (witness v))
  exact describesDistinct laws' v _ vHolds (apartHolds _ uIn) differ (witness v) (describedWitness laws' v vHolds)
    (Proof.newest _)

/-- **The set term of `v` and its members is the set term of the members apart from `v` with `v` adjoined.** -/
def adjoinsWitness (laws : HasLaws Δ) {v : Pattern} (vHolds : IsHF v) {values : List Pattern}
    (all : ∀ u ∈ values, IsHF u) :
    Proof Δ (adjoins (witness (set (v :: values))) (witness (set (apartFromSet v values))) (witness v)) := by
  have apartHolds : ∀ u ∈ apartFromSet v values, IsHF u := fun u inside => all u (List.mem_filter.mp inside).1
  have wholeHolds : IsHF (set (v :: values)) := set_hf fun u found => by
    rcases List.mem_cons.mp found with rfl | found
    · exact vHolds
    · exact all u found
  change Proof Δ (.all (iffCore (member (.var .vz) (weaken (witness (set (v :: values)))))
    (disjunctionFormula (member (.var .vz) (weaken (witness (set (apartFromSet v values)))))
      (sameMembers (.var .vz) (weaken (witness v))))))
  rw [weaken_witness, weaken_witness, weaken_witness]
  refine .allI (Proof.iffIntro ?_ ?_)
  · refine disjunctionElim (describesForward (describedWitness ((laws.lift setTy).prepend _) _ wholeHolds)
      (Proof.newest _)) ?_ ?_
    · exact disjunctionRight (sameOfDescribes vHolds vHolds rfl (Proof.newest _)
        (describedWitness (((laws.lift setTy).prepend _).prepend _) v vHolds))
    · refine oneCases values (Proof.newest _) fun index => ?_
      have uIn := List.get_mem values index
      refine if same : sameSet v (values.get index) = true then ?_ else ?_
      · exact disjunctionRight (sameOfDescribes (all _ uIn) vHolds
          ((sameSet_iff v vHolds _ (all _ uIn)).mp same).symm (Proof.newest _)
          (describedWitness ((((laws.lift setTy).prepend _).prepend _).prepend _) v vHolds))
      · exact disjunctionLeft (describesBackward (describedWitness ((((laws.lift setTy).prepend _).prepend _).prepend _)
          _ (set_hf apartHolds)) (oneIntroOfMem (Proof.newest _) _
            (List.mem_filter.mpr ⟨uIn, by simpa using same⟩)))
  · refine disjunctionElim (Proof.newest _) ?_ ?_
    · refine oneCases (apartFromSet v values) (describesForward (describedWitness
        (((laws.lift setTy).prepend _).prepend _) _ (set_hf apartHolds)) (Proof.newest _)) fun index => ?_
      exact describesBackward (describedWitness ((((laws.lift setTy).prepend _).prepend _).prepend _) _ wholeHolds)
        (disjunctionRight (oneIntroOfMem (Proof.newest _) values
          (List.mem_filter.mp (List.get_mem _ index)).1))
    · exact describesBackward (describedWitness (((laws.lift setTy).prepend _).prepend _) _ wholeHolds)
        (disjunctionLeft (describesAlong vHolds (describedWitness (((laws.lift setTy).prepend _).prepend _) v vHolds)
          (sameSymm (Proof.newest _))))

variable {p : Term Symbol Γ predTy}

/-- **Building the set of a list of members**, each of height at most `k`, given building for each member. -/
def buildList (laws : HasLaws Δ) (closed : Proof Δ (buildClosed p)) (k : ℕ)
    (built : ∀ v : Pattern, IsHF v → height v ≤ k → Proof Δ (.app p (witness v))) :
    ∀ (n : ℕ) (values : List Pattern), values.length ≤ n → (∀ v ∈ values, IsHF v ∧ height v ≤ k) →
      Proof Δ (.app p (witness (set values)))
  | _, [], _, _ => .impE (buildEmptyAt closed _) (emptyWitness laws)
  | 0, _ :: _, short, _ => absurd short (by simp)
  | n + 1, v :: values, short, all =>
    have vHolds := (all v List.mem_cons_self).1
    have valuesHold : ∀ u ∈ values, IsHF u := fun u found => (all u (List.mem_cons_of_mem _ found)).1
    have rest := buildList laws closed k built n (apartFromSet v values)
      (le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ short))
      fun u inside => all u (List.mem_cons_of_mem _ (List.mem_filter.mp inside).1)
    .impE (.impE (.impE (.impE (buildAt closed _ _ _) rest) (built v vHolds (all v List.mem_cons_self).2))
      (freshWitness laws vHolds valuesHold)) (adjoinsWitness laws vHolds valuesHold)

/-- **Building the set term of a hereditary term** of height at most `k`. -/
def buildTerm (laws : HasLaws Δ) (closed : Proof Δ (buildClosed p)) :
    ∀ (k : ℕ) (term : Pattern), IsHF term → height term ≤ k → Proof Δ (.app p (witness term))
  | 0, _, holds, bound => absurd (hf_height_pos holds) (by omega)
  | k + 1, term, holds, bound =>
    Proof.cast (congrArg (fun t => Term.app p (witness t)) (hf_eq_set holds).symm)
      (buildList laws closed k (buildTerm laws closed k) _ (membersOf term) le_rfl fun u inside =>
        ⟨hf_members holds u inside, by have := height_lt_of_mem inside; omega⟩)

/-- **The set term of a hereditary term is hereditarily finite.** -/
def hfWitness (laws : HasLaws Δ) (term : Pattern) (holds : IsHF term) : Proof Δ (hfFormula (witness term)) := by
  change Proof Δ (.all (σ := predTy) (.imp (buildClosed (.var .vz)) (.app (.var .vz) (weaken (witness term)))))
  rw [weaken_witness]
  exact .allI (.impI (buildTerm ((laws.lift predTy).prepend _) (Proof.newest _) (height term) term holds le_rfl))

/-- A member of a set term with a term adjoined. -/
def memberOfAdjoined (laws : HasLaws Δ) {term r : Pattern} (holds : IsHF term) (rHolds : IsHF r)
    {x : Term Symbol Γ setTy} (described : Proof Δ (describes term x)) :
    Proof Δ (member x (witness (insertTerm term r))) :=
  describesBackward (describedWitness laws (insertTerm term r) (insertTerm_hf holds rHolds)) (disjunctionLeft described)

end Building

/-! ## Plain native types at described sets -/

section Native

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- **A plain native type that holds, at the set a hereditary term describes.** -/
def provePlain (laws : HasLaws Δ) {body : PlainFormula} (plain : body.toFormula.plainModal = true) {term : Pattern}
    (holds : IsHF term) (holdsAt : body.eval term = true) {x : Term Symbol Γ setTy} (coreX : x.isCore = true)
    (described : Proof Δ (describes term x)) : Proof Δ (plainAt body x) :=
  proveNative (Region.withParts term holds) (withParts_partsClosed holds) false body.toFormula
    (Formula.regionalWith_of_modal _ (body.modal_of_plain plain)) laws.core Fin.elim0 Env.closed Fin.elim0
    (agrees_closed _) (fun index => index.elim0) term holds (self_mem_zfParts term)
    ((body.eval_iff Env.closed holds).mp holdsAt) x coreX (describesSomeOfTerm laws holds described)

/-- **A plain native type that fails, refuted at the set a hereditary term describes.** -/
def refutePlain (laws : HasLaws Δ) {body : PlainFormula} (plain : body.toFormula.plainModal = true) {term : Pattern}
    (holds : IsHF term) (failsAt : body.eval term = false) {x : Term Symbol Γ setTy} (coreX : x.isCore = true)
    (described : Proof Δ (describes term x)) : Proof Δ (negCore (plainAt body x)) :=
  refuteNative (Region.withParts term holds) (withParts_partsClosed holds) body.toFormula
    (Formula.regional_of_plainModal _ plain) laws Fin.elim0 Env.closed Fin.elim0 (agrees_closed _)
    (fun index => index.elim0) term holds (self_mem_zfParts term)
    (fun holdsAt => by
      rw [← body.eval_iff Env.closed holds, failsAt] at holdsAt
      exact Bool.false_ne_true holdsAt) x coreX (describesSomeOfTerm laws holds described)

/-- **A conflict refutes a container**: a set of the representative's type with the term's set as a member. -/
def conflictRefutes (laws : HasLaws Δ) : ∀ (body : PlainFormula), body.toFormula.plainModal = true →
    ∀ {r term : Pattern}, IsHF term → body.conflict r term = true → ∀ {x y : Term Symbol Γ setTy}, x.isCore = true →
      Proof Δ (describes term x) → Proof Δ (typeAt body r y) → Proof Δ (member x y) → Proof Δ falsity
  | .top, _, _, _, _, conflicting, _, _, _, _, _, _ => absurd conflicting Bool.false_ne_true
  | .bot, _, _, _, _, conflicting, _, _, _, _, _, _ => absurd conflicting Bool.false_ne_true
  | .and left right, plain, r, term, holds, conflicting, _, _, coreX, described, typed, inside =>
    if first : left.conflict r term = true then
      conflictRefutes laws left (PlainFormula.plain_parts_and plain).1 holds first coreX described
        (conjunctionLeft (conjunctionRight typed)) inside
    else
      conflictRefutes laws right (PlainFormula.plain_parts_and plain).2 holds
        (by simpa [PlainFormula.conflict, first] using conflicting) coreX described
        (conjunctionRight (conjunctionRight typed)) inside
  | .or left right, plain, r, term, holds, conflicting, _, _, coreX, described, typed, inside =>
    if first : left.conflict r term = true then
      conflictRefutes laws left (PlainFormula.plain_parts_or plain).1 holds first coreX described
        (conjunctionLeft (conjunctionRight typed)) inside
    else
      conflictRefutes laws right (PlainFormula.plain_parts_or plain).2 holds
        (by simpa [PlainFormula.conflict, first] using conflicting) coreX described
        (conjunctionRight (conjunctionRight typed)) inside
  | .possibly label inner, plain, r, term, holds, conflicting, x, y, coreX, described, typed, inside =>
    if here : (decide (memberLabel label) && !(PlainFormula.possibly label inner).eval r && inner.eval term) = true then
      have labelled : memberLabel label := by simp only [Bool.and_eq_true, decide_eq_true_eq] at here; exact here.1.1
      have refuted : (PlainFormula.possibly label inner).eval r = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at here; exact here.1.2
      have holdsAt : inner.eval term = true := by simp only [Bool.and_eq_true] at here; exact here.2
      .impE (Proof.cast (congrArg negCore (plainAt_possibly labelled inner y)) (literalFalse refuted (nodeLiteral typed)))
        (existentialIntro x (Proof.cast (instantiate_plainBody x y inner).symm (conjunctionIntro inside
          (provePlain laws (PlainFormula.plain_inner_possibly plain) holds holdsAt coreX described))))
    else
      conflictRefutes laws inner (PlainFormula.plain_inner_possibly plain) holds
        (by simpa [PlainFormula.conflict, here] using conflicting) coreX described (conjunctionRight typed) inside
  | .necessarily label inner, plain, r, term, holds, conflicting, x, y, coreX, described, typed, inside =>
    if here : (decide (memberLabel label) && (PlainFormula.necessarily label inner).eval r && !inner.eval term) = true
    then
      have labelled : memberLabel label := by simp only [Bool.and_eq_true, decide_eq_true_eq] at here; exact here.1.1
      have proved : (PlainFormula.necessarily label inner).eval r = true := by
        simp only [Bool.and_eq_true] at here; exact here.1.2
      have failsAt : inner.eval term = false := by simp only [Bool.and_eq_true, Bool.not_eq_true'] at here; exact here.2
      have atX := Proof.cast (instantiate_plainAllBody x y inner)
        (.allE x (Proof.cast (plainAt_necessarily labelled inner y) (literalTrue proved (nodeLiteral typed))))
      .impE (refutePlain laws (PlainFormula.plain_inner_necessarily plain) holds failsAt coreX described)
        (.impE atX inside)
    else
      conflictRefutes laws inner (PlainFormula.plain_inner_necessarily plain) holds
        (by simpa [PlainFormula.conflict, here] using conflicting) coreX described (conjunctionRight typed) inside

end Native

/-! ## The four forms at a described set -/

section Forms

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem instantiate_beforeBody (t x : Term Symbol Γ setTy) (body : PlainFormula) :
    instantiate t (conjunctionFormula (hfFormula (.var .vz)) (conjunctionFormula (member (weaken x) (.var .vz))
      (plainAt body (.var .vz)))) = conjunctionFormula (hfFormula t) (conjunctionFormula (member x t) (plainAt body t)) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_conjunctionFormula, subst_hfFormula, subst_plainAt]
  change conjunctionFormula (hfFormula t) (conjunctionFormula (member (instantiate t (weaken x)) t) (plainAt body t)) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_alwaysBody (t x : Term Symbol Γ setTy) (body : PlainFormula) :
    instantiate t (.imp (hfFormula (.var .vz)) (.imp (member (weaken x) (.var .vz)) (plainAt body (.var .vz)))) =
      .imp (hfFormula t) (.imp (member x t) (plainAt body t)) := by
  change Term.imp (subst (Subst.single t) (hfFormula (.var .vz))) (.imp (member (instantiate t (weaken x)) t)
    (subst (Subst.single t) (plainAt body (.var .vz)))) = _
  rw [subst_hfFormula, subst_plainAt, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_someBody (t : Term Symbol Γ setTy) (type : TypeExpr) (body : PlainFormula) :
    instantiate t (conjunctionFormula (hfFormula (.var .vz)) (conjunctionFormula (typedFormula type (.var .vz))
      (plainAt body (.var .vz)))) =
      conjunctionFormula (hfFormula t) (conjunctionFormula (typedFormula type t) (plainAt body t)) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_conjunctionFormula, subst_hfFormula, subst_typedFormula, subst_plainAt]
  rfl

theorem instantiate_everyBody (t : Term Symbol Γ setTy) (type : TypeExpr) (body : PlainFormula) :
    instantiate t (.imp (hfFormula (.var .vz)) (.imp (typedFormula type (.var .vz)) (plainAt body (.var .vz)))) =
      .imp (hfFormula t) (.imp (typedFormula type t) (plainAt body t)) := by
  change Term.imp (subst (Subst.single t) (hfFormula (.var .vz))) (.imp (subst (Subst.single t)
    (typedFormula type (.var .vz))) (subst (Subst.single t) (plainAt body (.var .vz)))) = _
  rw [subst_hfFormula, subst_typedFormula, subst_plainAt]
  rfl

theorem pastFormula_before {label : StepLabel} (labelled : memberLabel label) (body : PlainFormula)
    (x : Term Symbol Γ setTy) :
    pastFormula (.sometimeBefore label body.toFormula) x = existentialInline (σ := setTy) (conjunctionFormula
      (hfFormula (.var .vz)) (conjunctionFormula (member (weaken x) (.var .vz)) (plainAt body (.var .vz)))) := by
  simp only [pastFormula, if_pos labelled]
  rfl

theorem pastFormula_always {label : StepLabel} (labelled : memberLabel label) (body : PlainFormula)
    (x : Term Symbol Γ setTy) :
    pastFormula (.alwaysBefore label body.toFormula) x = .all (σ := setTy) (.imp (hfFormula (.var .vz))
      (.imp (member (weaken x) (.var .vz)) (plainAt body (.var .vz)))) := by
  simp only [pastFormula, if_pos labelled]
  rfl

theorem pastFormula_some (type : TypeExpr) (body : PlainFormula) (x : Term Symbol Γ setTy) :
    pastFormula (.someOf type body.toFormula) x = existentialInline (σ := setTy) (conjunctionFormula
      (hfFormula (.var .vz)) (conjunctionFormula (typedFormula type (.var .vz)) (plainAt body (.var .vz)))) := rfl

theorem pastFormula_every (type : TypeExpr) (body : PlainFormula) (x : Term Symbol Γ setTy) :
    pastFormula (.everyOf type body.toFormula) x = .all (σ := setTy) (.imp (hfFormula (.var .vz))
      (.imp (typedFormula type (.var .vz)) (plainAt body (.var .vz)))) := rfl

/-- A hereditarily finite set has some representative's type. -/
def classifyReps (body : PlainFormula) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {y : Term Symbol Γ setTy}
    (coreY : y.isCore = true) (finite : Proof Δ (hfFormula y)) : Proof Δ (someType body (plainReps body) y) :=
  classify body (plainReps body) (plainReps_base body)
    (fun _ wholeIn _ termIn => plainReps_adjoin body wholeIn termIn) coreY finite

theorem isCore_weakened {σ : Ty Unit} {x : Term Symbol Γ setTy} (coreX : x.isCore = true) :
    (weaken (σ := σ) x).isCore = true := by
  simp only [weaken, isCore_rename, coreX]

/-- **`⧫ψ` proved**: the term adjoined to a representative without a conflict, which has `ψ`. -/
def beforeProof (laws : HasLaws Δ) {label : StepLabel} (labelled : memberLabel label) {body : PlainFormula}
    (plain : body.toFormula.plainModal = true) {term r : Pattern} (holds : IsHF term) (rIn : r ∈ plainReps body)
    (free : body.conflict r term = false) (holdsAt : body.eval r = true) {x : Term Symbol Γ setTy}
    (described : Proof Δ (describes term x)) : Proof Δ (pastFormula (.sometimeBefore label body.toFormula) x) := by
  have rHolds := plainReps_hf body r rIn
  have containerHolds := insertTerm_hf holds rHolds
  rw [pastFormula_before labelled]
  refine existentialIntro (witness (insertTerm term r)) (Proof.cast (instantiate_beforeBody _ _ _).symm ?_)
  refine conjunctionIntro (hfWitness laws _ containerHolds)
    (conjunctionIntro (memberOfAdjoined laws holds rHolds described) ?_)
  exact provePlain laws plain containerHolds (by rw [body.eval_insert_of_conflict free body body.self_mem_nodes]; exact holdsAt)
    (isCore_witness _) (describedWitness laws _ containerHolds)

/-- **`⧫ψ` refuted**: by induction along membership, each representative is refuted by `ψ`'s literal or by a
conflict with the term. -/
def beforeRefutation (laws : HasLaws Δ) {label : StepLabel} {body : PlainFormula}
    (plain : body.toFormula.plainModal = true) {term : Pattern} (holds : IsHF term)
    (every : memberLabel label → ∀ r ∈ plainReps body, body.conflict r term = true ∨ body.eval r = false)
    {x : Term Symbol Γ setTy} (coreX : x.isCore = true) (described : Proof Δ (describes term x)) :
    Proof Δ (negCore (pastFormula (.sometimeBefore label body.toFormula) x)) := by
  refine if labelled : memberLabel label then ?_ else ?_
  · rw [pastFormula_before labelled]
    refine .impI (existentialElim (Proof.newest _) ?_)
    let found := conjunctionFormula (hfFormula (.var .vz)) (conjunctionFormula (member (weaken x) (.var .vz))
      (plainAt body (.var .vz)))
    have laws' : HasLaws (found :: weakenHyps (σ := setTy) (existentialInline (σ := setTy) found :: Δ)) :=
      ((laws.prepend _).lift setTy).prepend _
    have described' := Proof.cast (weaken_describes term x)
      (under found (described.prepend (existentialInline (σ := setTy) found)))
    refine someCases (plainReps body) (classifyReps body rfl (conjunctionLeft (Proof.newest _))) fun index => ?_
    have rIn := List.get_mem (plainReps body) index
    refine if holdsAt : body.eval ((plainReps body).get index) = true then ?_ else ?_
    · have conflicting := ((every labelled _ rIn).resolve_right (by rw [holdsAt]; decide))
      exact conflictRefutes (laws'.prepend _) body plain holds conflicting (isCore_weakened coreX) (described'.prepend _)
        (Proof.newest _) (conjunctionLeft (conjunctionRight ((Proof.newest _).prepend _)))
    · exact .impE (literalFalse (Bool.eq_false_iff.mpr holdsAt) (nodeLiteral (Proof.newest _)))
        (conjunctionRight (conjunctionRight ((Proof.newest _).prepend _)))
  · rw [show pastFormula (.sometimeBefore label body.toFormula) x = falsity by simp only [pastFormula, if_neg labelled]]
    exact .impI (Proof.newest _)

/-- **`■ψ` proved**: by induction along membership, each representative has `ψ` or a conflict with the term. -/
def alwaysProof (laws : HasLaws Δ) {label : StepLabel} {body : PlainFormula}
    (plain : body.toFormula.plainModal = true) {term : Pattern} (holds : IsHF term)
    (every : memberLabel label → ∀ r ∈ plainReps body, body.conflict r term = true ∨ body.eval r = true)
    {x : Term Symbol Γ setTy} (coreX : x.isCore = true) (described : Proof Δ (describes term x)) :
    Proof Δ (pastFormula (.alwaysBefore label body.toFormula) x) := by
  refine if labelled : memberLabel label then ?_ else ?_
  · rw [pastFormula_always labelled]
    refine .allI (.impI (.impI ?_))
    have laws' := (((laws.lift setTy).prepend (hfFormula (.var .vz))).prepend (member (weaken x) (.var .vz)))
    have described' := Proof.cast (weaken_describes term x)
      ((under (hfFormula (.var .vz)) described).prepend (member (weaken x) (.var .vz)))
    refine someCases (plainReps body) (classifyReps body rfl (Proof.prepend _ (Proof.newest _))) fun index => ?_
    have rIn := List.get_mem (plainReps body) index
    refine if holdsAt : body.eval ((plainReps body).get index) = true then ?_ else ?_
    · exact literalTrue holdsAt (nodeLiteral (Proof.newest _))
    · exact Proof.absurd (conflictRefutes (laws'.prepend _) body plain holds
        ((every labelled _ rIn).resolve_right holdsAt) (isCore_weakened coreX) (described'.prepend _) (Proof.newest _)
        ((Proof.newest _).prepend _))
  · rw [show pastFormula (.alwaysBefore label body.toFormula) x = truth by simp only [pastFormula, if_neg labelled]]
    exact truthIntro

/-- **`■ψ` refuted**: the term adjoined to a representative without a conflict, which lacks `ψ`. -/
def alwaysRefutation (laws : HasLaws Δ) {label : StepLabel} (labelled : memberLabel label) {body : PlainFormula}
    (plain : body.toFormula.plainModal = true) {term r : Pattern} (holds : IsHF term) (rIn : r ∈ plainReps body)
    (free : body.conflict r term = false) (failsAt : body.eval r = false) {x : Term Symbol Γ setTy}
    (described : Proof Δ (describes term x)) :
    Proof Δ (negCore (pastFormula (.alwaysBefore label body.toFormula) x)) := by
  have rHolds := plainReps_hf body r rIn
  have containerHolds := insertTerm_hf holds rHolds
  rw [pastFormula_always labelled]
  refine .impI ?_
  let every := Term.all (σ := setTy) (.imp (hfFormula (.var .vz)) (.imp (member (weaken x) (.var .vz))
    (plainAt body (.var .vz))))
  have atW := Proof.cast (instantiate_alwaysBody (witness (insertTerm term r)) x body)
    (.allE (witness (insertTerm term r)) (Proof.newest (Δ := Δ) every))
  exact .impE (refutePlain (laws.prepend _) plain containerHolds
      (by rw [body.eval_insert_of_conflict free body body.self_mem_nodes]; exact failsAt) (isCore_witness _)
      (describedWitness (laws.prepend _) _ containerHolds))
    (.impE (.impE atW (hfWitness (laws.prepend _) _ containerHolds))
      (memberOfAdjoined (laws.prepend _) holds rHolds (described.prepend _)))

/-- **`∃ T. ψ` proved**: a representative with the type and `ψ`. -/
def someProof (laws : HasLaws Δ) {type : TypeExpr} {body : PlainFormula} (plain : body.toFormula.plainModal = true)
    {r : Pattern} (rIn : r ∈ plainReps (typedBody type body)) (holdsAt : (typedBody type body).eval r = true)
    {x : Term Symbol Γ setTy} : Proof Δ (pastFormula (.someOf type body.toFormula) x) := by
  have rHolds := plainReps_hf _ r rIn
  have both : (typePlain type).eval r = true ∧ body.eval r = true := by
    simpa [typedBody, PlainFormula.eval] using holdsAt
  rw [pastFormula_some]
  refine existentialIntro (witness r) (Proof.cast (instantiate_someBody _ _ _).symm ?_)
  refine conjunctionIntro (hfWitness laws r rHolds) (conjunctionIntro ?_ ?_)
  · exact Proof.cast (typedFormula_eq type _).symm (provePlain laws (typePlain_plain type) rHolds both.1
      (isCore_witness r) (describedWitness laws r rHolds))
  · exact provePlain laws plain rHolds both.2 (isCore_witness r) (describedWitness laws r rHolds)

/-- **`∃ T. ψ` refuted**: by induction along membership, no representative has the type and `ψ`. -/
def someRefutation {type : TypeExpr} {body : PlainFormula}
    (none' : ∀ r ∈ plainReps (typedBody type body), (typedBody type body).eval r = false)
    {x : Term Symbol Γ setTy} : Proof Δ (negCore (pastFormula (.someOf type body.toFormula) x)) := by
  rw [pastFormula_some]
  refine .impI (existentialElim (Proof.newest _) ?_)
  refine someCases _ (classifyReps (typedBody type body) rfl (conjunctionLeft (Proof.newest _))) fun index => ?_
  exact .impE (literalFalse (none' _ (List.get_mem _ index)) (nodeLiteral (Proof.newest _)))
    (conjunctionIntro (Proof.cast (typedFormula_eq type _) (conjunctionLeft (conjunctionRight ((Proof.newest _).prepend _))))
      (conjunctionRight (conjunctionRight ((Proof.newest _).prepend _))))

/-- **`∀ T. ψ` proved**: by induction along membership, every representative with the type has `ψ`. -/
def everyProof {type : TypeExpr} {body : PlainFormula}
    (every : ∀ r ∈ plainReps (typedBody type body), (typePlain type).eval r = false ∨ body.eval r = true)
    {x : Term Symbol Γ setTy} : Proof Δ (pastFormula (.everyOf type body.toFormula) x) := by
  rw [pastFormula_every]
  refine .allI (.impI (.impI ?_))
  refine someCases _ (classifyReps (typedBody type body) rfl (Proof.prepend _ (Proof.newest _))) fun index => ?_
  have rIn := List.get_mem _ index
  refine if holdsAt : body.eval ((plainReps (typedBody type body)).get index) = true then ?_ else ?_
  · exact literalTrue holdsAt (nodeLiteral (conjunctionRight (conjunctionRight (Proof.newest _))))
  · exact Proof.absurd (.impE (literalFalse ((every _ rIn).resolve_right holdsAt)
      (nodeLiteral (conjunctionLeft (conjunctionRight (Proof.newest _)))))
      (Proof.cast (typedFormula_eq type _) ((Proof.newest _).prepend _)))

/-- **`∀ T. ψ` refuted**: a representative with the type that lacks `ψ`. -/
def everyRefutation (laws : HasLaws Δ) {type : TypeExpr} {body : PlainFormula}
    (plain : body.toFormula.plainModal = true) {r : Pattern} (rIn : r ∈ plainReps (typedBody type body))
    (typed : (typePlain type).eval r = true) (failsAt : body.eval r = false) {x : Term Symbol Γ setTy} :
    Proof Δ (negCore (pastFormula (.everyOf type body.toFormula) x)) := by
  have rHolds := plainReps_hf _ r rIn
  rw [pastFormula_every]
  refine .impI ?_
  let every : Term Symbol Γ .prop := Term.all (σ := setTy) (.imp (hfFormula (.var .vz))
    (.imp (typedFormula type (.var .vz)) (plainAt body (.var .vz))))
  have atW := Proof.cast (instantiate_everyBody (witness r) type body) (.allE (witness r) (Proof.newest (Δ := Δ) every))
  exact .impE (refutePlain (laws.prepend _) plain rHolds failsAt (isCore_witness r)
      (describedWitness (laws.prepend _) r rHolds))
    (.impE (.impE atW (hfWitness (laws.prepend _) r rHolds))
      (Proof.cast (typedFormula_eq type _).symm (provePlain (laws.prepend _) (typePlain_plain type) rHolds typed
        (isCore_witness r) (describedWitness (laws.prepend _) r rHolds))))

end Forms

/-! ## The verdict and the compiler -/

theorem plain?_toFormula : ∀ (body : PlainFormula), body.toFormula.plainModal = true → body.toFormula.plain? = some body
  | .top, _ | .bot, _ => rfl
  | .and left right, plain => by
    simp only [PlainFormula.toFormula, Formula.plain?, plain?_toFormula left (PlainFormula.plain_parts_and plain).1,
      plain?_toFormula right (PlainFormula.plain_parts_and plain).2]
    rfl
  | .or left right, plain => by
    simp only [PlainFormula.toFormula, Formula.plain?, plain?_toFormula left (PlainFormula.plain_parts_or plain).1,
      plain?_toFormula right (PlainFormula.plain_parts_or plain).2]
    rfl
  | .possibly label inner, plain => by
    have own : label.isContext = false := by
      simp only [PlainFormula.toFormula, Formula.plainModal, Bool.and_eq_true, Bool.not_eq_true'] at plain
      exact plain.1
    simp only [PlainFormula.toFormula, Formula.plain?, own, plain?_toFormula inner (PlainFormula.plain_inner_possibly plain)]
    rfl
  | .necessarily label inner, plain => by
    have own : label.isContext = false := by
      simp only [PlainFormula.toFormula, Formula.plainModal, Bool.and_eq_true, Bool.not_eq_true'] at plain
      exact plain.1
    simp only [PlainFormula.toFormula, Formula.plain?, own,
      plain?_toFormula inner (PlainFormula.plain_inner_necessarily plain)]
    rfl

/-- **A plain body as a plain formula.** -/
def plainOf (inner : Formula 0) (plain : inner.plainModal = true) :
    {body : PlainFormula // body.toFormula = inner ∧ body.toFormula.plainModal = true} :=
  match found : inner.plain? with
  | some body => ⟨body, (toFormula_plain? found).1, (toFormula_plain? found).1 ▸ (toFormula_plain? found).2⟩
  | none => False.elim (by
      obtain ⟨body, found'⟩ := plain?_isSome plain
      rw [found] at found'
      cases found')

/-- **The verdict on a past modality or a quantifier over a type with a plain body**, read on the representatives. -/
def pastVerdict : Formula 0 → Pattern → Bool
  | .sometimeBefore label inner, term => match inner.plain? with
    | some body => beforeVerdict label body term
    | none => false
  | .alwaysBefore label inner, term => match inner.plain? with
    | some body => alwaysVerdict label body term
    | none => false
  | .someOf type inner, _ => match inner.plain? with
    | some body => someVerdict type body
    | none => false
  | .everyOf type inner, _ => match inner.plain? with
    | some body => everyVerdict type body
    | none => false
  | _, _ => false

/-- **The verdict is exact.** -/
theorem pastVerdict_iff {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern} (holds : IsHF term) :
    pastVerdict formula term = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  cases formula
  case sometimeBefore label inner =>
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain]
    exact beforeVerdict_iff plain label holds
  case alwaysBefore label inner =>
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain]
    exact alwaysVerdict_iff plain label holds
  case someOf type inner =>
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain]
    exact someVerdict_iff plain type _
  case everyOf type inner =>
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain]
    exact everyVerdict_iff plain type _
  all_goals simp [Formula.pastPlain] at past

section Compiler

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- **A past type that holds, proved at the set a hereditary term describes**, with the witness the verdict found. -/
def provePast (laws : HasLaws Δ) : ∀ (formula : Formula 0), formula.pastPlain = true → ∀ {term : Pattern}, IsHF term →
    pastVerdict formula term = true → ∀ {x : Term Symbol Γ setTy}, x.isCore = true → Proof Δ (describes term x) →
      Proof Δ (pastFormula formula x)
  | .sometimeBefore label inner, past, term, holds, verdict, x, _, described => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    have labelled : memberLabel label := by
      simp only [beforeVerdict, Bool.and_eq_true, decide_eq_true_eq] at verdict; exact verdict.1
    have found : ∃ r ∈ plainReps body, (!body.conflict r term && body.eval r) = true := by
      simp only [beforeVerdict, Bool.and_eq_true, List.any_eq_true] at verdict
      obtain ⟨r, inside, test⟩ := verdict.2
      exact ⟨r, inside, by simpa using test⟩
    let chosen := chooseIndex (plainReps body) (fun r => !body.conflict r term && body.eval r) found
    have test : (!body.conflict ((plainReps body).get chosen.1) term && body.eval ((plainReps body).get chosen.1)) = true :=
      chosen.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at test
    exact beforeProof laws labelled plain holds (List.get_mem _ _) test.1 test.2 described
  | .alwaysBefore label inner, past, term, holds, verdict, x, coreX, described => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    refine alwaysProof laws plain holds (fun labelled r inside => ?_) coreX described
    simp only [alwaysVerdict, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true] at verdict
    exact (verdict.resolve_left (not_not.mpr labelled)) r inside
  | .someOf type inner, past, term, _, verdict, x, _, _ => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    have found : ∃ r ∈ plainReps (typedBody type body), (typedBody type body).eval r = true := by
      simpa [someVerdict, List.any_eq_true] using verdict
    let chosen := chooseIndex (plainReps (typedBody type body)) (typedBody type body).eval found
    exact someProof laws plain (List.get_mem _ chosen.1) chosen.2
  | .everyOf type inner, past, term, _, verdict, x, _, _ => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    refine everyProof fun r inside => ?_
    simp only [everyVerdict, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at verdict
    exact verdict r inside
  | .top, past, _, _, _, _, _, _ | .bot, past, _, _, _, _, _, _ | .and _ _, past, _, _, _, _, _, _
  | .or _ _, past, _, _, _, _, _, _ | .var _, past, _, _, _, _, _, _ | .mu _, past, _, _, _, _, _, _
  | .nu _, past, _, _, _, _, _, _ | .possibly _ _, past, _, _, _, _, _, _
  | .necessarily _ _, past, _, _, _, _, _, _ | .atLeast _ _ _ _, past, _, _, _, _, _, _
  | .allButFewer _ _ _ _, past, _, _, _, _, _, _ | .built _ _, past, _, _, _, _, _, _
  | .everyBuilt _ _, past, _, _, _, _, _, _ | .split _ _ _, past, _, _, _, _, _, _
  | .everySplit _ _ _, past, _, _, _, _, _, _ | .empty _, past, _, _, _, _, _, _
  | .nonEmpty _, past, _, _, _, _, _, _ | .single _ _, past, _, _, _, _, _, _
  | .everySingle _ _, past, _, _, _, _, _, _ | .body _, past, _, _, _, _, _, _
  | .everyBody _, past, _, _, _, _, _, _ | .multiBody _ _, past, _, _, _, _, _, _
  | .everyMultiBody _ _, past, _, _, _, _, _, _ | .bound _, past, _, _, _, _, _, _
  | .notBound _, past, _, _, _, _, _, _ | .typed _, past, _, _, _, _, _, _ | .untyped _, past, _, _, _, _, _, _
  | .is _, past, _, _, _, _, _, _ | .isNot _, past, _, _, _, _, _, _ | .mapsAll _ _, past, _, _, _, _, _, _
  | .mapsSome _ _, past, _, _, _, _, _, _ | .inRelation _, past, _, _, _, _, _, _
  | .notInRelation _, past, _, _, _, _, _, _ => absurd past Bool.false_ne_true

/-- **A past type that fails, refuted at the set a hereditary term describes.** -/
def refutePast (laws : HasLaws Δ) : ∀ (formula : Formula 0), formula.pastPlain = true → ∀ {term : Pattern}, IsHF term →
    pastVerdict formula term = false → ∀ {x : Term Symbol Γ setTy}, x.isCore = true → Proof Δ (describes term x) →
      Proof Δ (negCore (pastFormula formula x))
  | .sometimeBefore label inner, past, term, holds, verdict, x, coreX, described => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    refine beforeRefutation laws plain holds (fun labelled r inside => ?_) coreX described
    simp only [beforeVerdict, Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false] at verdict
    have rejected := (verdict.resolve_left (not_not.mpr labelled)) r inside
    cases conflicting : body.conflict r term
    · exact Or.inr (by simpa [conflicting] using rejected)
    · exact Or.inl rfl
  | .alwaysBefore label inner, past, term, holds, verdict, x, _, described => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    have labelled : memberLabel label := by
      simp only [alwaysVerdict, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at verdict
      exact verdict.1
    have found : ∃ r ∈ plainReps body, (!body.conflict r term && !body.eval r) = true := by
      simp only [alwaysVerdict, Bool.or_eq_false_iff, List.all_eq_false] at verdict
      obtain ⟨r, inside, test⟩ := verdict.2
      exact ⟨r, inside, by simpa using test⟩
    let chosen := chooseIndex (plainReps body) (fun r => !body.conflict r term && !body.eval r) found
    have test : (!body.conflict ((plainReps body).get chosen.1) term && !body.eval ((plainReps body).get chosen.1)) = true :=
      chosen.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at test
    exact alwaysRefutation laws labelled plain holds (List.get_mem _ _) test.1 test.2 described
  | .someOf type inner, past, term, _, verdict, x, _, _ => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    refine someRefutation fun r inside => ?_
    simp only [someVerdict, List.any_eq_false] at verdict
    simpa using verdict r inside
  | .everyOf type inner, past, term, _, verdict, x, _, _ => by
    obtain ⟨body, rfl, plain⟩ := plainOf inner past
    simp only [pastVerdict, plain?_toFormula body plain] at verdict
    have found : ∃ r ∈ plainReps (typedBody type body), ((typePlain type).eval r && !body.eval r) = true := by
      simp only [everyVerdict, List.all_eq_false] at verdict
      obtain ⟨r, inside, test⟩ := verdict
      exact ⟨r, inside, by simpa using test⟩
    let chosen := chooseIndex (plainReps (typedBody type body)) (fun r => (typePlain type).eval r && !body.eval r) found
    have test : ((typePlain type).eval ((plainReps (typedBody type body)).get chosen.1) &&
        !body.eval ((plainReps (typedBody type body)).get chosen.1)) = true := chosen.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at test
    exact everyRefutation laws plain (List.get_mem _ _) test.1 test.2
  | .top, past, _, _, _, _, _, _ | .bot, past, _, _, _, _, _, _ | .and _ _, past, _, _, _, _, _, _
  | .or _ _, past, _, _, _, _, _, _ | .var _, past, _, _, _, _, _, _ | .mu _, past, _, _, _, _, _, _
  | .nu _, past, _, _, _, _, _, _ | .possibly _ _, past, _, _, _, _, _, _
  | .necessarily _ _, past, _, _, _, _, _, _ | .atLeast _ _ _ _, past, _, _, _, _, _, _
  | .allButFewer _ _ _ _, past, _, _, _, _, _, _ | .built _ _, past, _, _, _, _, _, _
  | .everyBuilt _ _, past, _, _, _, _, _, _ | .split _ _ _, past, _, _, _, _, _, _
  | .everySplit _ _ _, past, _, _, _, _, _, _ | .empty _, past, _, _, _, _, _, _
  | .nonEmpty _, past, _, _, _, _, _, _ | .single _ _, past, _, _, _, _, _, _
  | .everySingle _ _, past, _, _, _, _, _, _ | .body _, past, _, _, _, _, _, _
  | .everyBody _, past, _, _, _, _, _, _ | .multiBody _ _, past, _, _, _, _, _, _
  | .everyMultiBody _ _, past, _, _, _, _, _, _ | .bound _, past, _, _, _, _, _, _
  | .notBound _, past, _, _, _, _, _, _ | .typed _, past, _, _, _, _, _, _ | .untyped _, past, _, _, _, _, _, _
  | .is _, past, _, _, _, _, _, _ | .isNot _, past, _, _, _, _, _, _ | .mapsAll _ _, past, _, _, _, _, _, _
  | .mapsSome _ _, past, _, _, _, _, _, _ | .inRelation _, past, _, _, _, _, _, _
  | .notInRelation _, past, _, _, _, _, _, _ => absurd past Bool.false_ne_true

end Compiler

/-- **The sentence of a past type that holds, proved from the three laws.** -/
def pastSentenceProof {Δ : List (Term Symbol [] .prop)} (laws : HasLaws Δ) {formula : Formula 0}
    (past : formula.pastPlain = true) {term : Pattern} (holds : IsHF term) (verdict : pastVerdict formula term = true) :
    Proof Δ (pastSentence formula term) :=
  existentialIntro (witness term) (Proof.cast (instantiate_pastBody past term (witness term)).symm
    (conjunctionIntro (describedWitness laws term holds)
      (provePast laws formula past holds verdict (isCore_witness term) (describedWitness laws term holds))))

/-- **The negation of the sentence of a past type that fails, proved from the three laws.** -/
def pastSentenceRefutation {Δ : List (Term Symbol [] .prop)} (laws : HasLaws Δ) {formula : Formula 0}
    (past : formula.pastPlain = true) {term : Pattern} (holds : IsHF term) (verdict : pastVerdict formula term = false) :
    Proof Δ (negCore (pastSentence formula term)) :=
  .impI (existentialElim (Proof.newest _)
    (.impE (refutePast (((laws.prepend _).lift setTy).prepend _) formula past holds verdict rfl
      (conjunctionLeft (Proof.newest _))) (conjunctionRight (Proof.newest _))))

/-- **The certificate compiler for past types**: the sentence of a past modality or a quantifier over a type with a
plain body, at a hereditary term, proved or refuted from the three laws. The verdict chooses every branch and
witness. -/
def compilePastSentence {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern} (holds : IsHF term) :
    Proof lawList (pastSentence formula term) ⊕ Proof lawList (negCore (pastSentence formula term)) :=
  if verdict : pastVerdict formula term = true then .inl (pastSentenceProof lawsOfList past holds verdict)
  else .inr (pastSentenceRefutation lawsOfList past holds (Bool.eq_false_iff.mpr verdict))

/-- **The compiler proves exactly the past types that hold.** -/
theorem compilePastSentence_isLeft_iff {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern}
    (holds : IsHF term) :
    (compilePastSentence past holds).isLeft = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  rw [← pastVerdict_iff past holds]
  unfold compilePastSentence
  split <;> simp_all

/-! ## In the package -/

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed)
open ZFSetUniverseClosure (CofinalInaccessibles)

variable {L : Type} [LevelOrder L]

/-- **The verdict compiler for past types into the package**: a closed term of the type of the proofs of the
proposition, or of its negation. -/
def compilePastVerdict {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern} (holds : IsHF term) :
    {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term))))} ⊕
      {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (pastSentence formula term)))))} :=
  match compilePastSentence past holds with
  | .inl proof => .inl ⟨packageTerm proof, packageTerm_typed proof⟩
  | .inr proof => .inr ⟨packageTerm proof, packageTerm_typed proof⟩

/-- **Every past type with a plain body at a hereditary term is decided in the package**, by a computed closed proof
term of its proposition or of the negation. -/
theorem pastProofTerm_decides {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern}
    (holds : IsHF term) :
    (∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term))))) ∨
      ∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (pastSentence formula term))))) :=
  match compilePastVerdict (L := L) past holds with
  | .inl found => .inl ⟨found.1, found.2⟩
  | .inr found => .inr ⟨found.1, found.2⟩

variable (small : CofinalInaccessibles.{0}) (large : CofinalInaccessibles.{1})

include small large in
/-- **A past type with a plain body holds at a hereditary term exactly when its proposition has a closed proof term
in the package with the laws**, relative to cofinally many inaccessible cardinals in two universes. -/
theorem sat_iff_pastProofTerm {formula : Formula 0} (past : formula.pastPlain = true) {term : Pattern}
    (holds : IsHF term) :
    HFSets.sat Env.closed formula (hfOf holds) ↔
      ∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term)))) := by
  constructor
  · intro holdsAt
    have verdict := (pastVerdict_iff past holds).mpr holdsAt
    exact ⟨packageTerm (pastSentenceProof lawsOfList past holds verdict), packageTerm_typed _⟩
  · intro proved
    have true' := models_of_hasProof (L := L) small large proved
    rw [ZFSetUniverseInterpretation.models_embed] at true'
    exact (denote_pastSentence past holds _).mp true'

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
