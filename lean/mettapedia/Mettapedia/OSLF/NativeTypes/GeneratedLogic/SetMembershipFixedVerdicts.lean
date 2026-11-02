import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastSentences

/-!
# Verdicts on past modalities and quantifiers over a type, for fixed-point bodies

For a guarded fixed-point body whose closure is count-guarded (`Formula.fixAdmitted`), the practical stage's
representatives carry every type of a hereditarily finite set. The verdicts read them through the tree of the body:

- **A conflict** (`fixConflict`) of a representative with a member `x`: a node `◇ψ` the representative refutes while
  `ψ` holds at `x`, or a node `□ψ` it proves while `ψ` fails at `x`, anywhere in the tree. A set of the
  representative's type containing `x` has no conflict with it (`fixConflict_false_of_member`); without a conflict,
  adjoining `x` keeps every value of the closure (`fixKeeps`).
- **The four verdicts** (`fixBeforeVerdict`, `fixAlwaysVerdict`, `fixSomeVerdict`, `fixEveryVerdict`) are exact among
  the hereditarily finite sets (`fixBeforeVerdict_iff` and the others).
- **Substituting nothing** changes no fixed-point body (`subst_elim0_fixBody`), so the root of the tree is the body.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Substituting nothing -/

theorem liftSubstitution_var {n : ℕ} : liftSubstitution (Formula.var : Fin n → Formula n) = Formula.var :=
  funext fun i => Fin.cases rfl (fun _ => rfl) i

theorem subst_var_fixBody : ∀ {n : ℕ} (formula : Formula n), formula.fixBody = true → formula.subst Formula.var = formula := by
  intro n formula body
  cases formula
  case top | bot | var => rfl
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.subst, subst_var_fixBody left body.1, subst_var_fixBody right body.2]
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [Formula.subst, subst_var_fixBody inner body.2]
  case mu inner | nu inner =>
    simp only [Formula.fixBody] at body
    simp only [Formula.subst, liftSubstitution_var, subst_var_fixBody inner body]
  all_goals simp [Formula.fixBody] at body

theorem subst_elim0_fixBody {formula : Formula 0} (body : formula.fixBody = true) :
    formula.subst (Fin.elim0 : Fin 0 → Formula 0) = formula := by
  rw [show (Fin.elim0 : Fin 0 → Formula 0) = Formula.var from funext fun i => i.elim0]
  exact subst_var_fixBody formula body

/-! ## Admitted bodies -/

/-- **Admitted fixed-point bodies**: guarded, with a count-guarded closure. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.fixAdmitted (formula : Formula 0) : Bool :=
  formula.fixBody && formula.guarded && (guardedClosure formula).all Formula.countGuarded

structure FixAdmitted (body : Formula 0) : Prop where
  isBody : body.fixBody = true
  guarded : body.guarded = true
  ok : ∀ c ∈ guardedClosure body, c.countGuarded = true

theorem fixAdmitted_parts {body : Formula 0} (admitted : body.fixAdmitted = true) : FixAdmitted body := by
  simp only [Formula.fixAdmitted, Bool.and_eq_true, List.all_eq_true] at admitted
  exact ⟨admitted.1.1, admitted.1.2, admitted.2⟩

theorem countGuarded_body {body : Formula 0} (admitted : FixAdmitted body) : body.countGuarded = true := by
  have := admitted.ok _ (subst_mem_closureWith Fin.elim0 body)
  rwa [subst_elim0_fixBody admitted.isBody] at this

/-- The body's value at a term is its root node's. -/
theorem nodeVal_root {body : Formula 0} (isBody : body.fixBody = true) (term : Pattern) :
    nodeVal body Fin.elim0 term = evalCounted body term := by
  rw [nodeVal, subst_elim0_fixBody isBody]

/-- Counted evaluation reads the set a hereditary term denotes. -/
theorem evalCounted_congr {formula : Formula 0} (ok : formula.countGuarded = true) {first second : Pattern}
    (firstHolds : IsHF first) (secondHolds : IsHF second) (same : zfOf first = zfOf second) :
    evalCounted formula first = evalCounted formula second := by
  apply Bool.eq_iff_iff.mpr
  rw [evalCounted_iff ok firstHolds, evalCounted_iff ok secondHolds]
  have : hfOf firstHolds = hfOf secondHolds := Subtype.ext same
  rw [this]

/-! ## Conflicts -/

/-- **A conflict of a representative `r` with a member `x`**, anywhere in the tree of a body. -/
def fixConflict : {n : ℕ} → Formula n → (Fin n → Formula 0) → Pattern → Pattern → Bool
  | _, .and left right, u, r, x | _, .or left right, u, r, x => fixConflict left u r x || fixConflict right u r x
  | _, .possibly label inner, u, r, x =>
    (decide (memberLabel label) && !nodeVal (.possibly label inner) u r && nodeVal inner u x) || fixConflict inner u r x
  | _, .necessarily label inner, u, r, x =>
    (decide (memberLabel label) && nodeVal (.necessarily label inner) u r && !nodeVal inner u x) || fixConflict inner u r x
  | _, .mu inner, u, r, x => fixConflict inner (unfoldWith ((Formula.mu inner).subst u) u) r x
  | _, .nu inner, u, r, x => fixConflict inner (unfoldWith ((Formula.nu inner).subst u) u) r x
  | _, _, _, _, _ => false

/-- **Without a conflict, adjoining the member keeps a node's value**, its variables read as kept. -/
theorem fixKeepsHead : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (now later : Fin n → Bool),
    formula.fixBody = true → formula.guardedIn now later = true → (∀ c ∈ closureWith u formula, c.countGuarded = true) →
    ∀ {r x : Pattern}, IsHF r → IsHF x → fixConflict formula u r x = false →
    (∀ i, now i = true → evalCounted (u i) (insertTerm x r) = evalCounted (u i) r) →
    nodeVal formula u (insertTerm x r) = nodeVal formula u r := by
  intro n formula u now later body guarded ok r x holdsR holdsX free varEq
  have insertHolds := insertTerm_hf holdsX holdsR
  cases formula
  case top | bot => rfl
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts : left.guardedIn now later = true ∧ right.guardedIn now later = true := by
      simpa [Formula.guardedIn] using guarded
    simp only [fixConflict, Bool.or_eq_false_iff] at free
    have first := fixKeepsHead left u now later body.1 parts.1 (fun c inside => ok c (List.mem_cons_of_mem _
      (List.mem_append_left _ inside))) holdsR holdsX free.1 varEq
    have second := fixKeepsHead right u now later body.2 parts.2 (fun c inside => ok c (List.mem_cons_of_mem _
      (List.mem_append_right _ inside))) holdsR holdsX free.2 varEq
    simp only [nodeVal, evalCounted, Formula.subst, evalCountedWith] at first second ⊢
    rw [first, second]
  case var index => exact varEq index guarded
  case possibly label inner =>
    simp only [fixConflict, Bool.or_eq_false_iff] at free
    rw [nodeVal_possibly_insert]
    have head := free.1
    revert head
    cases decide (memberLabel label) <;> cases nodeVal (.possibly label inner) u r <;>
      cases nodeVal inner u x <;> simp
  case necessarily label inner =>
    simp only [fixConflict, Bool.or_eq_false_iff] at free
    rw [nodeVal_necessarily_insert]
    have head := free.1
    revert head
    cases decide (memberLabel label) <;> cases nodeVal (.necessarily label inner) u r <;>
      cases nodeVal inner u x <;> simp
  case mu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨okFixed, okUnfolded, okInner⟩ := closure_head_mu ok
    rw [nodeVal_mu inner u okFixed okUnfolded insertHolds, nodeVal_mu inner u okFixed okUnfolded holdsR]
    exact fixKeepsHead inner _ (Fin.cons false now) (Fin.cons true later) body guarded okInner holdsR holdsX free
      fun i => Fin.cases (fun absent => absurd absent Bool.false_ne_true) (fun j present => varEq j present) i
  case nu inner =>
    simp only [Formula.fixBody] at body
    obtain ⟨okFixed, okUnfolded, okInner⟩ := closure_head_nu ok
    rw [nodeVal_nu inner u okFixed okUnfolded insertHolds, nodeVal_nu inner u okFixed okUnfolded holdsR]
    exact fixKeepsHead inner _ (Fin.cons false now) (Fin.cons true later) body guarded okInner holdsR holdsX free
      fun i => Fin.cases (fun absent => absurd absent Bool.false_ne_true) (fun j present => varEq j present) i
  all_goals simp [Formula.fixBody] at body

/-- **Without a conflict, adjoining the member keeps every value of the closure.** -/
theorem fixKeeps : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0) (now later : Fin n → Bool),
    formula.fixBody = true → formula.guardedIn now later = true → (∀ c ∈ closureWith u formula, c.countGuarded = true) →
    ∀ {r x : Pattern}, IsHF r → IsHF x → fixConflict formula u r x = false →
    (∀ i, evalCounted (u i) (insertTerm x r) = evalCounted (u i) r) →
    ∀ c ∈ closureWith u formula, evalCounted c (insertTerm x r) = evalCounted c r := by
  intro n formula u now later body guarded ok r x holdsR holdsX free varEq
  have head := fixKeepsHead formula u now later body guarded ok holdsR holdsX free (fun i _ => varEq i)
  cases formula
  case and left right | or left right =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    have parts : left.guardedIn now later = true ∧ right.guardedIn now later = true := by
      simpa [Formula.guardedIn] using guarded
    simp only [fixConflict, Bool.or_eq_false_iff] at free
    intro c inside
    rcases List.mem_cons.mp inside with rfl | found
    · exact head
    · rcases List.mem_append.mp found with found | found
      · exact fixKeeps left u now later body.1 parts.1 (fun c inside => ok c (List.mem_cons_of_mem _
          (List.mem_append_left _ inside))) holdsR holdsX free.1 varEq c found
      · exact fixKeeps right u now later body.2 parts.2 (fun c inside => ok c (List.mem_cons_of_mem _
          (List.mem_append_right _ inside))) holdsR holdsX free.2 varEq c found
  case possibly label inner | necessarily label inner =>
    simp only [Formula.fixBody, Bool.and_eq_true] at body
    simp only [fixConflict, Bool.or_eq_false_iff] at free
    intro c inside
    rcases List.mem_cons.mp inside with rfl | found
    · exact head
    · exact fixKeeps inner u later later body.2 guarded (fun c inside => ok c (List.mem_cons_of_mem _ inside)) holdsR
        holdsX free.2 varEq c found
  case mu inner | nu inner =>
    simp only [Formula.fixBody] at body
    intro c inside
    rcases List.mem_cons.mp inside with rfl | found
    · exact head
    · exact fixKeeps inner _ (Fin.cons false now) (Fin.cons true later) body guarded
        (fun c inside => ok c (List.mem_cons_of_mem _ inside)) holdsR holdsX free
        (fun i => Fin.cases head (fun j => varEq j) i) c found
  case var index =>
    intro c inside
    rw [List.mem_singleton.mp inside]
    exact varEq index
  case top | bot =>
    intro c inside
    rw [List.mem_singleton.mp inside]
    exact head
  all_goals exact absurd body (by simp [Formula.fixBody])

/-- **A set of a representative's type containing the member has no conflict with it.** -/
theorem fixConflict_false_of_member : ∀ {n : ℕ} (formula : Formula n) (u : Fin n → Formula 0),
    (∀ c ∈ closureWith u formula, c.countGuarded = true) → ∀ {r x whole : Pattern}, IsHF x → IsHF whole →
    zfOf x ∈ zfOf whole → (∀ c ∈ closureWith u formula, evalCounted c r = evalCounted c whole) →
    fixConflict formula u r x = false := by
  intro n formula u ok r x whole holdsX holdsWhole inside same
  cases formula
  case and left right | or left right =>
    simp only [fixConflict, Bool.or_eq_false_iff]
    exact ⟨fixConflict_false_of_member left u (fun c found => ok c (List.mem_cons_of_mem _ (List.mem_append_left _ found)))
        holdsX holdsWhole inside fun c found => same c (List.mem_cons_of_mem _ (List.mem_append_left _ found)),
      fixConflict_false_of_member right u (fun c found => ok c (List.mem_cons_of_mem _ (List.mem_append_right _ found)))
        holdsX holdsWhole inside fun c found => same c (List.mem_cons_of_mem _ (List.mem_append_right _ found))⟩
  case possibly label inner =>
    simp only [fixConflict, Bool.or_eq_false_iff]
    refine ⟨?_, fixConflict_false_of_member inner u (fun c found => ok c (List.mem_cons_of_mem _ found)) holdsX
      holdsWhole inside fun c found => same c (List.mem_cons_of_mem _ found)⟩
    obtain ⟨value, valueMember, valueEq⟩ := (mem_zfOf_hf holdsWhole).mp inside
    have innerOk : (inner.subst u).countGuarded = true :=
      ok _ (List.mem_cons_of_mem _ (subst_mem_closureWith u inner))
    have valueSame : nodeVal inner u value = nodeVal inner u x :=
      evalCounted_congr innerOk (hf_members holdsWhole value valueMember) holdsX valueEq
    have rootSame : nodeVal (.possibly label inner) u r = nodeVal (.possibly label inner) u whole :=
      same _ List.mem_cons_self
    rw [rootSame]
    cases labelled : decide (memberLabel label)
    · rfl
    · cases holdsAt : nodeVal inner u x
      · simp
      · have present : nodeVal (.possibly label inner) u whole = true := by
          simp only [nodeVal, evalCounted, Formula.subst, evalCountedWith, labelled, Bool.true_and, List.any_eq_true]
          exact ⟨value, valueMember, valueSame.trans holdsAt⟩
        simp [present]
  case necessarily label inner =>
    simp only [fixConflict, Bool.or_eq_false_iff]
    refine ⟨?_, fixConflict_false_of_member inner u (fun c found => ok c (List.mem_cons_of_mem _ found)) holdsX
      holdsWhole inside fun c found => same c (List.mem_cons_of_mem _ found)⟩
    obtain ⟨value, valueMember, valueEq⟩ := (mem_zfOf_hf holdsWhole).mp inside
    have innerOk : (inner.subst u).countGuarded = true :=
      ok _ (List.mem_cons_of_mem _ (subst_mem_closureWith u inner))
    have valueSame : nodeVal inner u value = nodeVal inner u x :=
      evalCounted_congr innerOk (hf_members holdsWhole value valueMember) holdsX valueEq
    have rootSame : nodeVal (.necessarily label inner) u r = nodeVal (.necessarily label inner) u whole :=
      same _ List.mem_cons_self
    rw [rootSame]
    cases labelled : decide (memberLabel label)
    · rfl
    · cases holdsAt : nodeVal inner u x
      · have absent : nodeVal (.necessarily label inner) u whole = false := by
          simp only [nodeVal, evalCounted, Formula.subst, evalCountedWith, labelled, Bool.not_true, Bool.false_or,
            List.all_eq_false]
          exact ⟨value, valueMember, by
            change ¬ nodeVal inner u value = true
            rw [valueSame, holdsAt]
            exact Bool.false_ne_true⟩
        simp [absent]
      · simp
  case mu inner | nu inner =>
    exact fixConflict_false_of_member inner _ (fun c found => ok c (List.mem_cons_of_mem _ found)) holdsX holdsWhole
      inside fun c found => same c (List.mem_cons_of_mem _ found)
  all_goals rfl

/-! ## The verdicts -/

variable {body : Formula 0}

/-- **`⧫ψ` at a term**: some representative has `ψ` and no conflict with the term. -/
def fixBeforeVerdict (label : StepLabel) (body : Formula 0) (term : Pattern) : Bool :=
  decide (memberLabel label) && (bodyReps body).any fun r => !fixConflict body Fin.elim0 r term && evalCounted body r

/-- **`■ψ` at a term**: every representative without a conflict with the term has `ψ`. -/
def fixAlwaysVerdict (label : StepLabel) (body : Formula 0) (term : Pattern) : Bool :=
  !decide (memberLabel label) || (bodyReps body).all fun r => fixConflict body Fin.elim0 r term || evalCounted body r

/-- The body a quantifier over a type classifies by: the type and the body. -/
abbrev fixTypedBody (type : TypeExpr) (body : Formula 0) : Formula 0 := .and (typePlain type).toFormula body

/-- **`∃ T. ψ`**: some representative has the type and `ψ`. -/
def fixSomeVerdict (type : TypeExpr) (body : Formula 0) : Bool :=
  (bodyReps (fixTypedBody type body)).any (evalCounted (fixTypedBody type body))

/-- **`∀ T. ψ`**: every representative with the type has `ψ`. -/
def fixEveryVerdict (type : TypeExpr) (body : Formula 0) : Bool :=
  (bodyReps (fixTypedBody type body)).all fun r => !evalCounted (typePlain type).toFormula r || evalCounted body r

theorem sat_iff_counted (ok : body.countGuarded = true) {term : Pattern} (holds : IsHF term) :
    HFSets.sat Env.closed body (hfOf holds) ↔ evalCounted body term = true :=
  (evalCounted_iff ok holds).symm

theorem root_vec_eq {first second : Pattern}
    (same : closureVec (guardedClosure body) first = closureVec (guardedClosure body) second) :
    ∀ c ∈ guardedClosure body, evalCounted c first = evalCounted c second :=
  fun c inside => List.map_inj_left.mp same c inside

theorem body_mem_closure (isBody : body.fixBody = true) : body ∈ guardedClosure body := by
  have := subst_mem_closureWith Fin.elim0 body
  rwa [subst_elim0_fixBody isBody] at this

theorem mem_insertTerm' {term whole : Pattern} (wholeHolds : IsHF whole) : zfOf term ∈ zfOf (insertTerm term whole) := by
  rw [zfOf_insertTerm term wholeHolds]
  exact ZFSet.mem_insert _ _

/-- Adjoining a conflict-free member keeps the body's value. -/
theorem fixKeeps_root (admitted : FixAdmitted body) {r x : Pattern} (holdsR : IsHF r) (holdsX : IsHF x)
    (free : fixConflict body Fin.elim0 r x = false) : evalCounted body (insertTerm x r) = evalCounted body r :=
  fixKeeps body Fin.elim0 Fin.elim0 Fin.elim0 admitted.isBody admitted.guarded admitted.ok holdsR holdsX free
    (fun i => i.elim0) body (body_mem_closure admitted.isBody)

/-- **`⧫ψ` is exact.** -/
theorem fixBeforeVerdict_iff (admitted : FixAdmitted body) (label : StepLabel) {term : Pattern} (holds : IsHF term) :
    fixBeforeVerdict label body term = true ↔ HFSets.sat Env.closed (.sometimeBefore label body) (hfOf holds) := by
  have ok := countGuarded_body admitted
  simp only [fixBeforeVerdict, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨labelled, r, inside, free, holdsAt⟩
    have rHolds := fixReps_hf admitted.guarded admitted.ok r inside
    have containerHolds := insertTerm_hf holds rHolds
    refine ⟨hfOf containerHolds, ⟨labelled, mem_insertTerm' rHolds⟩, ?_⟩
    rw [sat_iff_counted ok containerHolds, fixKeeps_root admitted rHolds holds free]
    exact holdsAt
  · rintro ⟨previous, ⟨labelled, inside⟩, holdsAt⟩
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term previous
    obtain ⟨r, rIn, same⟩ := fixReps_covers admitted.guarded admitted.ok wholeHolds
    refine ⟨labelled, r, rIn, fixConflict_false_of_member body Fin.elim0 admitted.ok holds wholeHolds inside
      (root_vec_eq same), ?_⟩
    rw [root_vec_eq same body (body_mem_closure admitted.isBody)]
    exact (sat_iff_counted ok wholeHolds).mp holdsAt

/-- **`■ψ` is exact.** -/
theorem fixAlwaysVerdict_iff (admitted : FixAdmitted body) (label : StepLabel) {term : Pattern} (holds : IsHF term) :
    fixAlwaysVerdict label body term = true ↔ HFSets.sat Env.closed (.alwaysBefore label body) (hfOf holds) := by
  have ok := countGuarded_body admitted
  simp only [fixAlwaysVerdict, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
  constructor
  · intro verdict previous step
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term previous
    obtain ⟨r, rIn, same⟩ := fixReps_covers admitted.guarded admitted.ok wholeHolds
    rcases verdict with unlabelled | every
    · exact absurd step.1 unlabelled
    · have free := fixConflict_false_of_member body Fin.elim0 admitted.ok holds wholeHolds step.2
        (root_vec_eq same)
      rcases every r rIn with conflicting | holdsAt
      · rw [free] at conflicting
        exact absurd conflicting Bool.false_ne_true
      · rw [sat_iff_counted ok wholeHolds, ← root_vec_eq same body
          (body_mem_closure admitted.isBody)]
        exact holdsAt
  · intro every
    by_cases labelled : memberLabel label
    · refine Or.inr fun r inside => ?_
      have rHolds := fixReps_hf admitted.guarded admitted.ok r inside
      cases conflicting : fixConflict body Fin.elim0 r term
      · have containerHolds := insertTerm_hf holds rHolds
        have there := every (hfOf containerHolds) ⟨labelled, mem_insertTerm' rHolds⟩
        rw [sat_iff_counted ok containerHolds, fixKeeps_root admitted rHolds holds conflicting] at there
        exact Or.inr there
      · exact Or.inl rfl
    · exact Or.inl labelled

theorem typed_parts {type : TypeExpr} (term : Pattern) :
    evalCounted (fixTypedBody type body) term = (evalCounted (typePlain type).toFormula term && evalCounted body term) :=
  rfl

theorem typePlain_mem {type : TypeExpr} (admitted : FixAdmitted (fixTypedBody type body)) :
    (typePlain type).toFormula ∈ guardedClosure (fixTypedBody type body) := by
  have whole := admitted.isBody
  simp only [Formula.fixBody, Bool.and_eq_true] at whole
  have := List.mem_cons_of_mem ((fixTypedBody type body).subst Fin.elim0) (List.mem_append_left
    (closureWith Fin.elim0 body) (subst_mem_closureWith Fin.elim0 (typePlain type).toFormula))
  rwa [subst_elim0_fixBody whole.1] at this

theorem body_mem_typed {type : TypeExpr} (admitted : FixAdmitted (fixTypedBody type body)) :
    body ∈ guardedClosure (fixTypedBody type body) := by
  have whole := admitted.isBody
  simp only [Formula.fixBody, Bool.and_eq_true] at whole
  have := List.mem_cons_of_mem ((fixTypedBody type body).subst Fin.elim0) (List.mem_append_right
    (closureWith Fin.elim0 (typePlain type).toFormula) (subst_mem_closureWith Fin.elim0 body))
  rwa [subst_elim0_fixBody whole.2] at this

theorem body_of_typed {type : TypeExpr} (admitted : FixAdmitted (fixTypedBody type body)) :
    body.fixBody = true ∧ body.countGuarded = true := by
  have whole := admitted.isBody
  simp only [Formula.fixBody, Bool.and_eq_true] at whole
  exact ⟨whole.2, admitted.ok _ (body_mem_typed admitted)⟩

theorem typePlain_counted {type : TypeExpr} (admitted : FixAdmitted (fixTypedBody type body)) {term : Pattern}
    (holds : IsHF term) : evalCounted (typePlain type).toFormula term = (typePlain type).eval term :=
  Bool.eq_iff_iff.mpr ((evalCounted_iff (admitted.ok _ (typePlain_mem admitted)) holds).trans
    ((hfSets_sat_iff_regional (Formula.regional_of_plainModal _ (typePlain_plain type)) _).trans
      ((typePlain type).eval_iff Env.closed holds).symm))

/-- **`∃ T. ψ` is exact.** -/
theorem fixSomeVerdict_iff {type : TypeExpr} (admitted : FixAdmitted (fixTypedBody type body)) (x : HF) :
    fixSomeVerdict type body = true ↔ HFSets.sat Env.closed (.someOf type body) x := by
  have ok := admitted.ok _ (body_mem_typed admitted)
  simp only [fixSomeVerdict, List.any_eq_true]
  constructor
  · rintro ⟨r, inside, holdsAt⟩
    have rHolds := fixReps_hf admitted.guarded admitted.ok r inside
    rw [typed_parts, Bool.and_eq_true, typePlain_counted admitted rHolds] at holdsAt
    exact ⟨hfOf rHolds, (typePlain_eval_iff type rHolds).mp holdsAt.1, (sat_iff_counted ok rHolds).mpr holdsAt.2⟩
  · rintro ⟨witness, typed, holdsAt⟩
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term witness
    obtain ⟨r, rIn, same⟩ := fixReps_covers admitted.guarded admitted.ok wholeHolds
    have rHolds := fixReps_hf admitted.guarded admitted.ok r rIn
    refine ⟨r, rIn, ?_⟩
    rw [typed_parts, root_vec_eq same _ (typePlain_mem admitted),
      root_vec_eq same _ (body_mem_typed admitted), typePlain_counted admitted wholeHolds,
      (typePlain_eval_iff type wholeHolds).mpr typed, (sat_iff_counted ok wholeHolds).mp holdsAt]
    rfl

/-- **`∀ T. ψ` is exact.** -/
theorem fixEveryVerdict_iff {type : TypeExpr} (admitted : FixAdmitted (fixTypedBody type body)) (x : HF) :
    fixEveryVerdict type body = true ↔ HFSets.sat Env.closed (.everyOf type body) x := by
  have ok := admitted.ok _ (body_mem_typed admitted)
  simp only [fixEveryVerdict, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro every witness typed
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term witness
    obtain ⟨r, rIn, same⟩ := fixReps_covers admitted.guarded admitted.ok wholeHolds
    have typeSame := root_vec_eq same _ (typePlain_mem admitted)
    have bodySame := root_vec_eq same _ (body_mem_typed admitted)
    have typedThere := (typePlain_eval_iff type wholeHolds).mpr typed
    rw [← typePlain_counted admitted wholeHolds] at typedThere
    rcases every r rIn with untyped | holdsAt
    · rw [untyped, typedThere] at typeSame
      exact absurd typeSame Bool.false_ne_true
    · rw [sat_iff_counted ok wholeHolds, ← bodySame]
      exact holdsAt
  · intro every r inside
    have rHolds := fixReps_hf admitted.guarded admitted.ok r inside
    cases typed : evalCounted (typePlain type).toFormula r
    · exact Or.inl rfl
    · rw [typePlain_counted admitted rHolds] at typed
      exact Or.inr ((sat_iff_counted ok rHolds).mp (every (hfOf rHolds) ((typePlain_eval_iff type rHolds).mp typed)))

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
