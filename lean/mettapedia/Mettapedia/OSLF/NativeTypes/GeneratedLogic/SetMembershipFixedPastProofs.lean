import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedVerdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastProofs

/-!
# Proof terms for past modalities and quantifiers over a type, with fixed-point bodies

For a past modality or a quantifier over a type whose body is a guarded fixed-point body with a count-guarded closure
(`Formula.pastFixed`), at a hereditary term, the calculus of the package proves the sentence (`pastSentence`) or its
negation from the laws of the empty set, the power set and separation, with no excluded middle; the verdict on the
practical stage's representatives (`pastFixedVerdict`) chooses every branch and witness.

- **Witness search**: a past modality that holds is proved at the term adjoined to a representative without a
  conflict (`fixBeforeProof`), a quantifier over a type at a representative (`fixSomeProof`); the body is proved
  there by the package's prover (`proveClosed`).
- **Induction along membership**: a refutation classifies the container by the type of a representative
  (`fixClassify`) and refutes each: by the body's literal at the tree's root, or by a conflict with the term
  anywhere in the tree (`fixConflictRefutes`).
- **The compiler** (`compilePastFixedSentence`) proves exactly the past types that hold, and in the package each
  derivation is a closed proof term (`compilePastFixedVerdict`); such a type holds exactly when its proposition has a
  closed proof term (`sat_iff_pastFixedProofTerm`). Plain bodies are fixed-point bodies, so this compiler covers them.
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

/-! ## Closed bodies at described sets -/

section Native

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem extensional_of_counted {c : Formula 0} (isBody : c.fixBody = true) (ok : c.countGuarded = true) {term : Pattern}
    (holds : IsHF term) : evalCounted c term = true ↔ extensional.sat Env.closed c (zfOf term) :=
  (evalCounted_iff ok holds).trans (hfSets_sat_iff_regional (regional_of_fixBody c isBody) (hfOf holds))

/-- **A closed fixed-point body that holds, at the set a hereditary term describes.** -/
def proveClosed (laws : HasLaws Δ) {c : Formula 0} (isBody : c.fixBody = true) (ok : c.countGuarded = true)
    {term : Pattern} (holds : IsHF term) (holdsAt : evalCounted c term = true) {x : Term Symbol Γ setTy}
    (coreX : x.isCore = true) (described : Proof Δ (describes term x)) : Proof Δ (closedAt c x) :=
  proveNative (Region.withParts term holds) (withParts_partsClosed holds) false c
    (Formula.regionalWith_of_modal _ (modal_of_fixBody c isBody)) laws.core Fin.elim0 Env.closed Fin.elim0
    (agrees_closed _) (fun index => index.elim0) term holds (self_mem_zfParts term)
    ((extensional_of_counted isBody ok holds).mp holdsAt) x coreX (describesSomeOfTerm laws holds described)

/-- **A closed fixed-point body that fails, refuted at the set a hereditary term describes.** -/
def refuteClosed (laws : HasLaws Δ) {c : Formula 0} (isBody : c.fixBody = true) (ok : c.countGuarded = true)
    {term : Pattern} (holds : IsHF term) (failsAt : evalCounted c term = false) {x : Term Symbol Γ setTy}
    (coreX : x.isCore = true) (described : Proof Δ (describes term x)) : Proof Δ (negCore (closedAt c x)) :=
  refuteNative (Region.withParts term holds) (withParts_partsClosed holds) c (regional_of_fixBody c isBody) laws
    Fin.elim0 Env.closed Fin.elim0 (agrees_closed _) (fun index => index.elim0) term holds (self_mem_zfParts term)
    (fun holdsAt => by
      rw [← extensional_of_counted isBody ok holds, failsAt] at holdsAt
      exact Bool.false_ne_true holdsAt) x coreX (describesSomeOfTerm laws holds described)

/-- **A conflict anywhere in the tree refutes a container** of the term's set. -/
def fixConflictRefutes (laws : HasLaws Δ) : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0),
    formula.fixBody = true → (∀ i, (u i).fixBody = true) → (∀ c ∈ closureWith u formula, c.countGuarded = true) →
    ∀ {r term : Pattern}, IsHF term → fixConflict formula u r term = true → ∀ {x y : Term Symbol Γ setTy},
      x.isCore = true → Proof Δ (describes term x) → Proof Δ (fixTypeAt formula u r y) → Proof Δ (member x y) →
      Proof Δ falsity := by
  intro n formula u body bodies ok r term holds conflicting x y coreX described typed inside
  cases formula
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    refine if first : fixConflict left u r term = true then ?_ else ?_
    · exact fixConflictRefutes laws left u body.1 bodies (fun c found => ok c (List.mem_cons_of_mem _
        (List.mem_append_left _ found))) holds first coreX described (conjunctionLeft (conjunctionRight typed)) inside
    · exact fixConflictRefutes laws right u body.2 bodies (fun c found => ok c (List.mem_cons_of_mem _
        (List.mem_append_right _ found))) holds (by simpa [fixConflict, first] using conflicting) coreX described
        (conjunctionRight (conjunctionRight typed)) inside
  case possibly label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have innerBody := fixBody_subst inner u body.2 bodies
    have innerOk : (inner.subst u).countGuarded = true := ok _ (List.mem_cons_of_mem _ (subst_mem_closureWith u inner))
    refine if here : (decide (memberLabel label) && !nodeVal (.possibly label inner) u r && nodeVal inner u term) = true
      then ?_ else ?_
    · have labelled : memberLabel label := by simp only [Bool.and_eq_true, decide_eq_true_eq] at here; exact here.1.1
      have refuted : nodeVal (.possibly label inner) u r = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at here; exact here.1.2
      have holdsAt : nodeVal inner u term = true := by simp only [Bool.and_eq_true] at here; exact here.2
      have notHere : Proof Δ (negCore (closedAt (.possibly label (inner.subst u)) y)) :=
        literalFalse refuted (rootLit typed)
      exact .impE (Proof.cast (congrArg negCore (closedAt_possibly labelled _ y)) notHere)
        (existentialIntro x (Proof.cast (instantiate_closedBody (regional_of_fixBody _ innerBody) x y).symm
          (conjunctionIntro inside (proveClosed laws innerBody innerOk holds holdsAt coreX described))))
    · exact fixConflictRefutes laws inner u body.2 bodies (fun c found => ok c (List.mem_cons_of_mem _ found)) holds
        (by simpa [fixConflict, here] using conflicting) coreX described (conjunctionRight typed) inside
  case necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have innerBody := fixBody_subst inner u body.2 bodies
    have innerOk : (inner.subst u).countGuarded = true := ok _ (List.mem_cons_of_mem _ (subst_mem_closureWith u inner))
    refine if here : (decide (memberLabel label) && nodeVal (.necessarily label inner) u r && !nodeVal inner u term) = true
      then ?_ else ?_
    · have labelled : memberLabel label := by simp only [Bool.and_eq_true, decide_eq_true_eq] at here; exact here.1.1
      have proved : nodeVal (.necessarily label inner) u r = true := by
        simp only [Bool.and_eq_true] at here; exact here.1.2
      have failsAt : nodeVal inner u term = false := by simp only [Bool.and_eq_true, Bool.not_eq_true'] at here; exact here.2
      have every : Proof Δ (closedAt (.necessarily label (inner.subst u)) y) := literalTrue proved (rootLit typed)
      have atX := Proof.cast (instantiate_closedAllBody (regional_of_fixBody _ innerBody) x y)
        (.allE x (Proof.cast (closedAt_necessarily labelled _ y) every))
      exact .impE (refuteClosed laws innerBody innerOk holds failsAt coreX described) (.impE atX inside)
    · exact fixConflictRefutes laws inner u body.2 bodies (fun c found => ok c (List.mem_cons_of_mem _ found)) holds
        (by simpa [fixConflict, here] using conflicting) coreX described (conjunctionRight typed) inside
  case mu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨_, _, okInner⟩ := closure_head_mu ok
    exact fixConflictRefutes laws inner _ body (unfoldWith_bodies (fixBody_subst (.mu inner) u body bodies) bodies)
      okInner holds conflicting coreX described (conjunctionRight typed) inside
  case nu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨_, _, okInner⟩ := closure_head_nu ok
    exact fixConflictRefutes laws inner _ body (unfoldWith_bodies (fixBody_subst (.nu inner) u body bodies) bodies)
      okInner holds conflicting coreX described (conjunctionRight typed) inside
  all_goals exact absurd conflicting (by simp [fixConflict])

/-- The body's literal at the root of a tree. -/
def rootBody {body : Formula 0} (isBody : body.fixBody = true) {r : Pattern} {y : Term Symbol Γ setTy}
    (tree : Proof Δ (fixTypeAt body Fin.elim0 r y)) : Proof Δ (literal (evalCounted body r) (closedAt body y)) :=
  Proof.cast (by unfold nodeLit; rw [nodeVal_root isBody, subst_elim0_fixBody isBody]) (rootLit tree)

end Native

/-! ## The four forms at a described set -/

section Forms

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem instantiate_beforeClosed (t x : Term Symbol Γ setTy) {body : Formula 0} (regional : body.regional = true) :
    instantiate t (conjunctionFormula (hfFormula (.var .vz)) (conjunctionFormula (member (weaken x) (.var .vz))
      (closedAt body (.var .vz)))) = conjunctionFormula (hfFormula t) (conjunctionFormula (member x t) (closedAt body t)) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_conjunctionFormula, subst_hfFormula, subst_closedAt _ regional]
  change conjunctionFormula (hfFormula t) (conjunctionFormula (member (instantiate t (weaken x)) t) (closedAt body t)) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_alwaysClosed (t x : Term Symbol Γ setTy) {body : Formula 0} (regional : body.regional = true) :
    instantiate t (.imp (hfFormula (.var .vz)) (.imp (member (weaken x) (.var .vz)) (closedAt body (.var .vz)))) =
      .imp (hfFormula t) (.imp (member x t) (closedAt body t)) := by
  change Term.imp (subst (Subst.single t) (hfFormula (.var .vz))) (.imp (member (instantiate t (weaken x)) t)
    (subst (Subst.single t) (closedAt body (.var .vz)))) = _
  rw [subst_hfFormula, subst_closedAt _ regional, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_someClosed (t : Term Symbol Γ setTy) (type : TypeExpr) {body : Formula 0}
    (regional : body.regional = true) :
    instantiate t (conjunctionFormula (hfFormula (.var .vz)) (conjunctionFormula (typedFormula type (.var .vz))
      (closedAt body (.var .vz)))) =
      conjunctionFormula (hfFormula t) (conjunctionFormula (typedFormula type t) (closedAt body t)) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_conjunctionFormula, subst_hfFormula, subst_typedFormula, subst_closedAt _ regional]
  rfl

theorem instantiate_everyClosed (t : Term Symbol Γ setTy) (type : TypeExpr) {body : Formula 0}
    (regional : body.regional = true) :
    instantiate t (.imp (hfFormula (.var .vz)) (.imp (typedFormula type (.var .vz)) (closedAt body (.var .vz)))) =
      .imp (hfFormula t) (.imp (typedFormula type t) (closedAt body t)) := by
  change Term.imp (subst (Subst.single t) (hfFormula (.var .vz))) (.imp (subst (Subst.single t)
    (typedFormula type (.var .vz))) (subst (Subst.single t) (closedAt body (.var .vz)))) = _
  rw [subst_hfFormula, subst_typedFormula, subst_closedAt _ regional]
  rfl

theorem pastFormula_beforeClosed {label : StepLabel} (labelled : memberLabel label) (body : Formula 0)
    (x : Term Symbol Γ setTy) :
    pastFormula (.sometimeBefore label body) x = existentialInline (σ := setTy) (conjunctionFormula
      (hfFormula (.var .vz)) (conjunctionFormula (member (weaken x) (.var .vz)) (closedAt body (.var .vz)))) := by
  simp only [pastFormula, if_pos labelled]
  rfl

theorem pastFormula_alwaysClosed {label : StepLabel} (labelled : memberLabel label) (body : Formula 0)
    (x : Term Symbol Γ setTy) :
    pastFormula (.alwaysBefore label body) x = .all (σ := setTy) (.imp (hfFormula (.var .vz))
      (.imp (member (weaken x) (.var .vz)) (closedAt body (.var .vz)))) := by
  simp only [pastFormula, if_pos labelled]
  rfl

theorem typedFormula_closed (type : TypeExpr) (w : Term Symbol Γ setTy) :
    typedFormula type w = closedAt (typePlain type).toFormula w :=
  typedFormula_eq type w

theorem fixBody_of_plain : ∀ (formula : PlainFormula), formula.toFormula.plainModal = true →
    formula.toFormula.fixBody = true
  | .top, _ | .bot, _ => rfl
  | .and left right, plain | .or left right, plain => by
    simp only [PlainFormula.toFormula, Formula.plainModal, Bool.and_eq_true] at plain
    simp only [PlainFormula.toFormula, Formula.fixBody, fixBody_of_plain left plain.1, fixBody_of_plain right plain.2,
      Bool.and_self]
  | .possibly _ inner, plain | .necessarily _ inner, plain => by
    simp only [PlainFormula.toFormula, Formula.plainModal, Bool.and_eq_true] at plain
    simp only [PlainFormula.toFormula, Formula.fixBody, plain.1, fixBody_of_plain inner plain.2, Bool.and_self]

/-- A fixed-point body's classification by the practical stage's representatives. -/
def fixClassifyReps {body : Formula 0} (admitted : FixAdmitted body) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}
    {y : Term Symbol Γ setTy} (coreY : y.isCore = true) (finite : Proof Δ (hfFormula y)) :
    Proof Δ (fixSomeType body (bodyReps body) y) :=
  fixClassify body admitted.isBody admitted.guarded admitted.ok (bodyReps body) (fixReps_hf admitted.guarded admitted.ok)
    (fixReps_base admitted.guarded admitted.ok) (fixReps_adjoin admitted.guarded admitted.ok) coreY finite

/-- **`⧫ψ` proved**: the term adjoined to a representative without a conflict, which has `ψ`. -/
def fixBeforeProof (laws : HasLaws Δ) {label : StepLabel} (labelled : memberLabel label) {body : Formula 0}
    (admitted : FixAdmitted body) {term r : Pattern} (holds : IsHF term) (rIn : r ∈ bodyReps body)
    (free : fixConflict body Fin.elim0 r term = false) (holdsAt : evalCounted body r = true) {x : Term Symbol Γ setTy}
    (described : Proof Δ (describes term x)) : Proof Δ (pastFormula (.sometimeBefore label body) x) := by
  have rHolds := fixReps_hf admitted.guarded admitted.ok r rIn
  have containerHolds := insertTerm_hf holds rHolds
  rw [pastFormula_beforeClosed labelled]
  refine existentialIntro (witness (insertTerm term r))
    (Proof.cast (instantiate_beforeClosed _ _ (regional_of_fixBody _ admitted.isBody)).symm ?_)
  refine conjunctionIntro (hfWitness laws _ containerHolds) (conjunctionIntro (memberOfAdjoined laws holds rHolds described) ?_)
  exact proveClosed laws admitted.isBody (countGuarded_body admitted) containerHolds
    (by rw [fixKeeps_root admitted rHolds holds free]; exact holdsAt) (isCore_witness _)
    (describedWitness laws _ containerHolds)

/-- **`⧫ψ` refuted**: by induction along membership, each representative is refuted by `ψ`'s literal or by a
conflict with the term. -/
def fixBeforeRefutation (laws : HasLaws Δ) {label : StepLabel} {body : Formula 0} (admitted : FixAdmitted body)
    {term : Pattern} (holds : IsHF term)
    (every : memberLabel label → ∀ r ∈ bodyReps body, fixConflict body Fin.elim0 r term = true ∨ evalCounted body r = false)
    {x : Term Symbol Γ setTy} (coreX : x.isCore = true) (described : Proof Δ (describes term x)) :
    Proof Δ (negCore (pastFormula (.sometimeBefore label body) x)) := by
  refine if labelled : memberLabel label then ?_ else ?_
  · rw [pastFormula_beforeClosed labelled]
    refine .impI (existentialElim (Proof.newest _) ?_)
    let found := conjunctionFormula (hfFormula (.var .vz)) (conjunctionFormula (member (weaken x) (.var .vz))
      (closedAt body (.var .vz)))
    have laws' : HasLaws (found :: weakenHyps (σ := setTy) (existentialInline (σ := setTy) found :: Δ)) :=
      ((laws.prepend _).lift setTy).prepend _
    have described' := Proof.cast (weaken_describes term x)
      (under found (described.prepend (existentialInline (σ := setTy) found)))
    refine fixSomeCases (bodyReps body) (fixClassifyReps admitted rfl (conjunctionLeft (Proof.newest _))) fun index => ?_
    have rIn := List.get_mem (bodyReps body) index
    refine if holdsAt : evalCounted body ((bodyReps body).get index) = true then ?_ else ?_
    · have conflicting := ((every labelled _ rIn).resolve_right (by rw [holdsAt]; decide))
      exact fixConflictRefutes (laws'.prepend _) body Fin.elim0 admitted.isBody (fun i => i.elim0) admitted.ok holds
        conflicting (isCore_weakened coreX) (described'.prepend _) (Proof.newest _)
        (conjunctionLeft (conjunctionRight ((Proof.newest _).prepend _)))
    · exact .impE (literalFalse (Bool.eq_false_iff.mpr holdsAt) (rootBody admitted.isBody (Proof.newest _)))
        (conjunctionRight (conjunctionRight ((Proof.newest _).prepend _)))
  · rw [show pastFormula (.sometimeBefore label body) x = falsity by simp only [pastFormula, if_neg labelled]]
    exact .impI (Proof.newest _)

/-- **`■ψ` proved**: by induction along membership, each representative has `ψ` or a conflict with the term. -/
def fixAlwaysProof (laws : HasLaws Δ) {label : StepLabel} {body : Formula 0} (admitted : FixAdmitted body)
    {term : Pattern} (holds : IsHF term)
    (every : memberLabel label → ∀ r ∈ bodyReps body, fixConflict body Fin.elim0 r term = true ∨ evalCounted body r = true)
    {x : Term Symbol Γ setTy} (coreX : x.isCore = true) (described : Proof Δ (describes term x)) :
    Proof Δ (pastFormula (.alwaysBefore label body) x) := by
  refine if labelled : memberLabel label then ?_ else ?_
  · rw [pastFormula_alwaysClosed labelled]
    refine .allI (.impI (.impI ?_))
    have laws' := (((laws.lift setTy).prepend (hfFormula (.var .vz))).prepend (member (weaken x) (.var .vz)))
    have described' := Proof.cast (weaken_describes term x)
      ((under (hfFormula (.var .vz)) described).prepend (member (weaken x) (.var .vz)))
    refine fixSomeCases (bodyReps body) (fixClassifyReps admitted rfl (Proof.prepend _ (Proof.newest _))) fun index => ?_
    have rIn := List.get_mem (bodyReps body) index
    refine if holdsAt : evalCounted body ((bodyReps body).get index) = true then ?_ else ?_
    · exact literalTrue holdsAt (rootBody admitted.isBody (Proof.newest _))
    · exact Proof.absurd (fixConflictRefutes (laws'.prepend _) body Fin.elim0 admitted.isBody (fun i => i.elim0)
        admitted.ok holds ((every labelled _ rIn).resolve_right holdsAt) (isCore_weakened coreX) (described'.prepend _)
        (Proof.newest _) ((Proof.newest _).prepend _))
  · rw [show pastFormula (.alwaysBefore label body) x = truth by simp only [pastFormula, if_neg labelled]]
    exact truthIntro

/-- **`■ψ` refuted**: the term adjoined to a representative without a conflict, which lacks `ψ`. -/
def fixAlwaysRefutation (laws : HasLaws Δ) {label : StepLabel} (labelled : memberLabel label) {body : Formula 0}
    (admitted : FixAdmitted body) {term r : Pattern} (holds : IsHF term) (rIn : r ∈ bodyReps body)
    (free : fixConflict body Fin.elim0 r term = false) (failsAt : evalCounted body r = false) {x : Term Symbol Γ setTy}
    (described : Proof Δ (describes term x)) : Proof Δ (negCore (pastFormula (.alwaysBefore label body) x)) := by
  have rHolds := fixReps_hf admitted.guarded admitted.ok r rIn
  have containerHolds := insertTerm_hf holds rHolds
  rw [pastFormula_alwaysClosed labelled]
  refine .impI ?_
  let every := Term.all (σ := setTy) (.imp (hfFormula (.var .vz)) (.imp (member (weaken x) (.var .vz))
    (closedAt body (.var .vz))))
  have atW := Proof.cast (instantiate_alwaysClosed (witness (insertTerm term r)) x (regional_of_fixBody _ admitted.isBody))
    (.allE (witness (insertTerm term r)) (Proof.newest (Δ := Δ) every))
  exact .impE (refuteClosed (laws.prepend _) admitted.isBody (countGuarded_body admitted) containerHolds
      (by rw [fixKeeps_root admitted rHolds holds free]; exact failsAt) (isCore_witness _)
      (describedWitness (laws.prepend _) _ containerHolds))
    (.impE (.impE atW (hfWitness (laws.prepend _) _ containerHolds))
      (memberOfAdjoined (laws.prepend _) holds rHolds (described.prepend _)))

theorem typePlain_fixBody (type : TypeExpr) : (typePlain type).toFormula.fixBody = true :=
  fixBody_of_plain _ (typePlain_plain type)

/-- **`∃ T. ψ` proved**: a representative with the type and `ψ`. -/
def fixSomeProof (laws : HasLaws Δ) {type : TypeExpr} {body : Formula 0} (admitted : FixAdmitted (fixTypedBody type body))
    {r : Pattern} (rIn : r ∈ bodyReps (fixTypedBody type body)) (holdsAt : evalCounted (fixTypedBody type body) r = true)
    {x : Term Symbol Γ setTy} : Proof Δ (pastFormula (.someOf type body) x) := by
  have rHolds := fixReps_hf admitted.guarded admitted.ok r rIn
  obtain ⟨isBody, ok⟩ := body_of_typed admitted
  have both : evalCounted (typePlain type).toFormula r = true ∧ evalCounted body r = true := by
    rw [typed_parts, Bool.and_eq_true] at holdsAt
    exact holdsAt
  change Proof Δ (existentialInline (σ := setTy) (conjunctionFormula (hfFormula (.var .vz))
    (conjunctionFormula (typedFormula type (.var .vz)) (closedAt body (.var .vz)))))
  refine existentialIntro (witness r) (Proof.cast (instantiate_someClosed _ _ (regional_of_fixBody _ isBody)).symm ?_)
  refine conjunctionIntro (hfWitness laws r rHolds) (conjunctionIntro ?_ ?_)
  · exact Proof.cast (typedFormula_closed type _).symm (proveClosed laws (typePlain_fixBody type)
      (admitted.ok _ (typePlain_mem admitted)) rHolds both.1 (isCore_witness r) (describedWitness laws r rHolds))
  · exact proveClosed laws isBody ok rHolds both.2 (isCore_witness r) (describedWitness laws r rHolds)

/-- **`∃ T. ψ` refuted**: by induction along membership, no representative has the type and `ψ`. -/
def fixSomeRefutation {type : TypeExpr} {body : Formula 0} (admitted : FixAdmitted (fixTypedBody type body))
    (none' : ∀ r ∈ bodyReps (fixTypedBody type body), evalCounted (fixTypedBody type body) r = false)
    {x : Term Symbol Γ setTy} : Proof Δ (negCore (pastFormula (.someOf type body) x)) := by
  change Proof Δ (negCore (existentialInline (σ := setTy) (conjunctionFormula (hfFormula (.var .vz))
    (conjunctionFormula (typedFormula type (.var .vz)) (closedAt body (.var .vz))))))
  refine .impI (existentialElim (Proof.newest _) ?_)
  refine fixSomeCases _ (fixClassifyReps admitted rfl (conjunctionLeft (Proof.newest _))) fun index => ?_
  exact .impE (literalFalse (none' _ (List.get_mem _ index)) (rootBody admitted.isBody (Proof.newest _)))
    (conjunctionIntro (Proof.cast (typedFormula_closed type _) (conjunctionLeft (conjunctionRight ((Proof.newest _).prepend _))))
      (conjunctionRight (conjunctionRight ((Proof.newest _).prepend _))))

/-- **`∀ T. ψ` proved**: by induction along membership, every representative with the type has `ψ`. -/
def fixEveryProof {type : TypeExpr} {body : Formula 0} (admitted : FixAdmitted (fixTypedBody type body))
    (every : ∀ r ∈ bodyReps (fixTypedBody type body),
      evalCounted (typePlain type).toFormula r = false ∨ evalCounted body r = true)
    {x : Term Symbol Γ setTy} : Proof Δ (pastFormula (.everyOf type body) x) := by
  obtain ⟨isBody, _⟩ := body_of_typed admitted
  change Proof Δ (.all (σ := setTy) (.imp (hfFormula (.var .vz)) (.imp (typedFormula type (.var .vz))
    (closedAt body (.var .vz)))))
  refine .allI (.impI (.impI ?_))
  refine fixSomeCases _ (fixClassifyReps admitted rfl (Proof.prepend _ (Proof.newest _))) fun index => ?_
  have rIn := List.get_mem _ index
  have tree := Proof.cast (fixTypeAt_head _ _ _ _) (Proof.newest (Δ := typedFormula type (.var .vz) ::
    hfFormula (.var .vz) :: weakenHyps (σ := setTy) Δ)
    (fixTypeAt (fixTypedBody type body) Fin.elim0 ((bodyReps (fixTypedBody type body)).get index) (.var .vz)))
  refine if holdsAt : evalCounted body ((bodyReps (fixTypedBody type body)).get index) = true then ?_ else ?_
  · exact literalTrue holdsAt (rootBody isBody (conjunctionRight (conjunctionRight tree)))
  · exact Proof.absurd (.impE (literalFalse ((every _ rIn).resolve_right holdsAt)
      (rootBody (typePlain_fixBody type) (conjunctionLeft (conjunctionRight tree))))
      (Proof.cast (typedFormula_closed type _) ((Proof.newest _).prepend _)))

/-- **`∀ T. ψ` refuted**: a representative with the type that lacks `ψ`. -/
def fixEveryRefutation (laws : HasLaws Δ) {type : TypeExpr} {body : Formula 0}
    (admitted : FixAdmitted (fixTypedBody type body)) {r : Pattern} (rIn : r ∈ bodyReps (fixTypedBody type body))
    (typed : evalCounted (typePlain type).toFormula r = true) (failsAt : evalCounted body r = false)
    {x : Term Symbol Γ setTy} : Proof Δ (negCore (pastFormula (.everyOf type body) x)) := by
  have rHolds := fixReps_hf admitted.guarded admitted.ok r rIn
  obtain ⟨isBody, ok⟩ := body_of_typed admitted
  change Proof Δ (negCore (.all (σ := setTy) (.imp (hfFormula (.var .vz)) (.imp (typedFormula type (.var .vz))
    (closedAt body (.var .vz))))))
  refine .impI ?_
  let every : Term Symbol Γ .prop := Term.all (σ := setTy) (.imp (hfFormula (.var .vz))
    (.imp (typedFormula type (.var .vz)) (closedAt body (.var .vz))))
  have atW := Proof.cast (instantiate_everyClosed (witness r) type (regional_of_fixBody _ isBody))
    (.allE (witness r) (Proof.newest (Δ := Δ) every))
  exact .impE (refuteClosed (laws.prepend _) isBody ok rHolds failsAt (isCore_witness r)
      (describedWitness (laws.prepend _) r rHolds))
    (.impE (.impE atW (hfWitness (laws.prepend _) r rHolds))
      (Proof.cast (typedFormula_closed type _).symm (proveClosed (laws.prepend _) (typePlain_fixBody type)
        (admitted.ok _ (typePlain_mem admitted)) rHolds typed (isCore_witness r) (describedWitness (laws.prepend _) r rHolds))))

end Forms

/-! ## The verdict and the compiler -/

/-- **Past modalities and quantifiers over a type whose bodies are admitted fixed-point bodies.** -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.pastFixed : Formula 0 → Bool
  | .sometimeBefore _ inner | .alwaysBefore _ inner => inner.fixAdmitted
  | .someOf type inner | .everyOf type inner => (fixTypedBody type inner).fixAdmitted
  | _ => false

/-- **The verdict on a past type with an admitted fixed-point body**, read on the representatives. -/
def pastFixedVerdict : Formula 0 → Pattern → Bool
  | .sometimeBefore label inner, term => fixBeforeVerdict label inner term
  | .alwaysBefore label inner, term => fixAlwaysVerdict label inner term
  | .someOf type inner, _ => fixSomeVerdict type inner
  | .everyOf type inner, _ => fixEveryVerdict type inner
  | _, _ => false

theorem pastRegional_of_pastFixed : ∀ {formula : Formula 0}, formula.pastFixed = true → formula.pastRegional = true := by
  intro formula past
  cases formula
  case sometimeBefore _ inner | alwaysBefore _ inner =>
    exact regional_of_fixBody _ (fixAdmitted_parts past).isBody
  case someOf type inner | everyOf type inner =>
    exact regional_of_fixBody _ (body_of_typed (fixAdmitted_parts past)).1
  all_goals simp [Formula.pastFixed] at past

/-- **The verdict is exact.** -/
theorem pastFixedVerdict_iff {formula : Formula 0} (past : formula.pastFixed = true) {term : Pattern} (holds : IsHF term) :
    pastFixedVerdict formula term = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  cases formula
  case sometimeBefore label inner => exact fixBeforeVerdict_iff (fixAdmitted_parts past) label holds
  case alwaysBefore label inner => exact fixAlwaysVerdict_iff (fixAdmitted_parts past) label holds
  case someOf type inner => exact fixSomeVerdict_iff (fixAdmitted_parts past) _
  case everyOf type inner => exact fixEveryVerdict_iff (fixAdmitted_parts past) _
  all_goals simp [Formula.pastFixed] at past

section Compiler

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- **A past type that holds, proved at the set a hereditary term describes**, with the witness the verdict found. -/
def provePastFixed (laws : HasLaws Δ) (formula : Formula 0) (past : formula.pastFixed = true) {term : Pattern}
    (holds : IsHF term) (verdict : pastFixedVerdict formula term = true) {x : Term Symbol Γ setTy}
    (coreX : x.isCore = true) (described : Proof Δ (describes term x)) : Proof Δ (pastFormula formula x) := by
  cases formula
  case sometimeBefore label inner =>
    have admitted := fixAdmitted_parts past
    have labelled : memberLabel label := by
      simp only [pastFixedVerdict, fixBeforeVerdict, Bool.and_eq_true, decide_eq_true_eq] at verdict; exact verdict.1
    have found : ∃ r ∈ bodyReps inner, (!fixConflict inner Fin.elim0 r term && evalCounted inner r) = true := by
      simp only [pastFixedVerdict, fixBeforeVerdict, Bool.and_eq_true, List.any_eq_true] at verdict
      obtain ⟨r, inside, test⟩ := verdict.2
      exact ⟨r, inside, by simpa using test⟩
    let chosen := chooseIndex (bodyReps inner) (fun r => !fixConflict inner Fin.elim0 r term && evalCounted inner r) found
    have test : (!fixConflict inner Fin.elim0 ((bodyReps inner).get chosen.1) term &&
        evalCounted inner ((bodyReps inner).get chosen.1)) = true := chosen.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at test
    exact fixBeforeProof laws labelled admitted holds (List.get_mem _ _) test.1 test.2 described
  case alwaysBefore label inner =>
    have admitted := fixAdmitted_parts past
    refine fixAlwaysProof laws admitted holds (fun labelled r inside => ?_) coreX described
    simp only [pastFixedVerdict, fixAlwaysVerdict, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.all_eq_true] at verdict
    exact (verdict.resolve_left (not_not.mpr labelled)) r inside
  case someOf type inner =>
    have admitted := fixAdmitted_parts past
    have found : ∃ r ∈ bodyReps (fixTypedBody type inner), evalCounted (fixTypedBody type inner) r = true := by
      simpa [pastFixedVerdict, fixSomeVerdict, List.any_eq_true] using verdict
    let chosen := chooseIndex (bodyReps (fixTypedBody type inner)) (evalCounted (fixTypedBody type inner)) found
    exact fixSomeProof laws admitted (List.get_mem _ chosen.1) chosen.2
  case everyOf type inner =>
    have admitted := fixAdmitted_parts past
    refine fixEveryProof admitted fun r inside => ?_
    simp only [pastFixedVerdict, fixEveryVerdict, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at verdict
    exact verdict r inside
  all_goals exact absurd past (by simp [Formula.pastFixed])

/-- **A past type that fails, refuted at the set a hereditary term describes.** -/
def refutePastFixed (laws : HasLaws Δ) (formula : Formula 0) (past : formula.pastFixed = true) {term : Pattern}
    (holds : IsHF term) (verdict : pastFixedVerdict formula term = false) {x : Term Symbol Γ setTy}
    (coreX : x.isCore = true) (described : Proof Δ (describes term x)) : Proof Δ (negCore (pastFormula formula x)) := by
  cases formula
  case sometimeBefore label inner =>
    have admitted := fixAdmitted_parts past
    refine fixBeforeRefutation laws admitted holds (fun labelled r inside => ?_) coreX described
    simp only [pastFixedVerdict, fixBeforeVerdict, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      List.any_eq_false] at verdict
    have rejected := (verdict.resolve_left (not_not.mpr labelled)) r inside
    cases conflicting : fixConflict inner Fin.elim0 r term
    · exact Or.inr (by simpa [conflicting] using rejected)
    · exact Or.inl rfl
  case alwaysBefore label inner =>
    have admitted := fixAdmitted_parts past
    have labelled : memberLabel label := by
      simp only [pastFixedVerdict, fixAlwaysVerdict, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at verdict
      exact verdict.1
    have found : ∃ r ∈ bodyReps inner, (!fixConflict inner Fin.elim0 r term && !evalCounted inner r) = true := by
      simp only [pastFixedVerdict, fixAlwaysVerdict, Bool.or_eq_false_iff, List.all_eq_false] at verdict
      obtain ⟨r, inside, test⟩ := verdict.2
      exact ⟨r, inside, by simpa using test⟩
    let chosen := chooseIndex (bodyReps inner) (fun r => !fixConflict inner Fin.elim0 r term && !evalCounted inner r) found
    have test : (!fixConflict inner Fin.elim0 ((bodyReps inner).get chosen.1) term &&
        !evalCounted inner ((bodyReps inner).get chosen.1)) = true := chosen.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at test
    exact fixAlwaysRefutation laws labelled admitted holds (List.get_mem _ _) test.1 test.2 described
  case someOf type inner =>
    have admitted := fixAdmitted_parts past
    refine fixSomeRefutation admitted fun r inside => ?_
    simp only [pastFixedVerdict, fixSomeVerdict, List.any_eq_false] at verdict
    simpa using verdict r inside
  case everyOf type inner =>
    have admitted := fixAdmitted_parts past
    have found : ∃ r ∈ bodyReps (fixTypedBody type inner),
        (evalCounted (typePlain type).toFormula r && !evalCounted inner r) = true := by
      simp only [pastFixedVerdict, fixEveryVerdict, List.all_eq_false] at verdict
      obtain ⟨r, inside, test⟩ := verdict
      exact ⟨r, inside, by simpa using test⟩
    let chosen := chooseIndex (bodyReps (fixTypedBody type inner))
      (fun r => evalCounted (typePlain type).toFormula r && !evalCounted inner r) found
    have test : (evalCounted (typePlain type).toFormula ((bodyReps (fixTypedBody type inner)).get chosen.1) &&
        !evalCounted inner ((bodyReps (fixTypedBody type inner)).get chosen.1)) = true := chosen.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at test
    exact fixEveryRefutation laws admitted (List.get_mem _ _) test.1 test.2
  all_goals exact absurd past (by simp [Formula.pastFixed])

end Compiler

theorem subst_pastFormula_regional {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') : ∀ (formula : Formula 0),
    formula.pastRegional = true → ∀ x : Term Symbol Γ setTy, subst θ (pastFormula formula x) = pastFormula formula (subst θ x) := by
  intro formula past x
  have native : ∀ {inner : Formula 0}, inner.regional = true →
      subst (Subst.lift θ) (nativeFormula inner (.var .vz) Fin.elim0) = nativeFormula inner (.var .vz) Fin.elim0 :=
    fun regional => (subst_nativeFormula_regional _ _ regional _ _).trans (native_env_irrelevant _)
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
  all_goals simp [Formula.pastRegional] at past

theorem instantiate_pastRegionalBody {Γ : Ctx Unit} {formula : Formula 0} (past : formula.pastRegional = true)
    (term : Pattern) (t : Term Symbol Γ setTy) :
    instantiate t (conjunctionFormula (describes term (.var .vz)) (pastFormula formula (.var .vz))) =
      conjunctionFormula (describes term t) (pastFormula formula t) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_describes, subst_pastFormula_regional _ formula past]
  rfl

/-- **The sentence of a past type that holds, proved from the three laws.** -/
def pastFixedSentenceProof {Δ : List (Term Symbol [] .prop)} (laws : HasLaws Δ) {formula : Formula 0}
    (past : formula.pastFixed = true) {term : Pattern} (holds : IsHF term)
    (verdict : pastFixedVerdict formula term = true) : Proof Δ (pastSentence formula term) :=
  existentialIntro (witness term) (Proof.cast (instantiate_pastRegionalBody (pastRegional_of_pastFixed past) term
    (witness term)).symm (conjunctionIntro (describedWitness laws term holds)
      (provePastFixed laws formula past holds verdict (isCore_witness term) (describedWitness laws term holds))))

/-- **The negation of the sentence of a past type that fails, proved from the three laws.** -/
def pastFixedSentenceRefutation {Δ : List (Term Symbol [] .prop)} (laws : HasLaws Δ) {formula : Formula 0}
    (past : formula.pastFixed = true) {term : Pattern} (holds : IsHF term)
    (verdict : pastFixedVerdict formula term = false) : Proof Δ (negCore (pastSentence formula term)) :=
  .impI (existentialElim (Proof.newest _)
    (.impE (refutePastFixed (((laws.prepend _).lift setTy).prepend _) formula past holds verdict rfl
      (conjunctionLeft (Proof.newest _))) (conjunctionRight (Proof.newest _))))

/-- **The certificate compiler for past types with fixed-point bodies.** -/
def compilePastFixedSentence {formula : Formula 0} (past : formula.pastFixed = true) {term : Pattern}
    (holds : IsHF term) :
    Proof lawList (pastSentence formula term) ⊕ Proof lawList (negCore (pastSentence formula term)) :=
  if verdict : pastFixedVerdict formula term = true then .inl (pastFixedSentenceProof lawsOfList past holds verdict)
  else .inr (pastFixedSentenceRefutation lawsOfList past holds (Bool.eq_false_iff.mpr verdict))

/-- **The compiler proves exactly the past types that hold.** -/
theorem compilePastFixedSentence_isLeft_iff {formula : Formula 0} (past : formula.pastFixed = true) {term : Pattern}
    (holds : IsHF term) :
    (compilePastFixedSentence past holds).isLeft = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  rw [← pastFixedVerdict_iff past holds]
  unfold compilePastFixedSentence
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

/-- **The verdict compiler for past types with fixed-point bodies into the package.** -/
def compilePastFixedVerdict {formula : Formula 0} (past : formula.pastFixed = true) {term : Pattern} (holds : IsHF term) :
    {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term))))} ⊕
      {proofTerm : CTm (Head L) 0 //
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (pastSentence formula term)))))} :=
  match compilePastFixedSentence past holds with
  | .inl proof => .inl ⟨packageTerm proof, packageTerm_typed proof⟩
  | .inr proof => .inr ⟨packageTerm proof, packageTerm_typed proof⟩

theorem compilePastFixedVerdict_isLeft {formula : Formula 0} (past : formula.pastFixed = true) {term : Pattern}
    (holds : IsHF term) :
    (compilePastFixedVerdict (L := L) past holds).isLeft = (compilePastFixedSentence past holds).isLeft := by
  unfold compilePastFixedVerdict
  cases compilePastFixedSentence past holds <;> rfl

/-- **Every past type with an admitted fixed-point body at a hereditary term is decided in the package.** -/
theorem pastFixedProofTerm_decides {formula : Formula 0} (past : formula.pastFixed = true) {term : Pattern}
    (holds : IsHF term) :
    (∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term))))) ∨
      ∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (negCore (pastSentence formula term))))) :=
  match compilePastFixedVerdict (L := L) past holds with
  | .inl found => .inl ⟨found.1, found.2⟩
  | .inr found => .inr ⟨found.1, found.2⟩

variable (small : CofinalInaccessibles.{0}) (large : CofinalInaccessibles.{1})

include small large in
/-- **A past type with an admitted fixed-point body holds at a hereditary term exactly when its proposition has a
closed proof term in the package with the laws**, relative to cofinally many inaccessible cardinals in two universes. -/
theorem sat_iff_pastFixedProofTerm {formula : Formula 0} (past : formula.pastFixed = true) {term : Pattern}
    (holds : IsHF term) :
    HFSets.sat Env.closed formula (hfOf holds) ↔
      ∃ proofTerm : CTm (Head L) 0,
        CTyped (setLaws L) .nil proofTerm (cHolds (trTerm (embed (pastSentence formula term)))) := by
  constructor
  · intro holdsAt
    exact ⟨packageTerm (pastFixedSentenceProof lawsOfList past holds ((pastFixedVerdict_iff past holds).mpr holdsAt)),
      packageTerm_typed _⟩
  · intro proved
    have true' := models_of_hasProof (L := L) small large proved
    rw [ZFSetUniverseInterpretation.models_embed] at true'
    exact (denote_pastSentence_regional (pastRegional_of_pastFixed past) holds _).mp true'

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
