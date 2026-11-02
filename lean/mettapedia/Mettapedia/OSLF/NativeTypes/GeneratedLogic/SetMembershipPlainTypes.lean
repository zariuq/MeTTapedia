import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastModalities
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPracticalStage

/-!
# Types of plain bodies, and representatives grown by adjunction

A plain modal formula (steps, their duals and the connectives) sees a set through the truth values of its subformulas
there, the set's **type**. Adjoining a member to a set gives a set whose type is fixed by the two types, so the types of
all hereditarily finite sets are reached from the empty set's by adjunctions.

- **Plain formulas as their own syntax** (`PlainFormula`), read back as formulas (`toFormula`) and read off every plain
  modal formula (`Formula.plain?`, `toFormula_plain?`).
- **Evaluation** (`PlainFormula.eval`) is structural over the formula, a step looking at the members of the term. It is
  the extensional truth at every hereditary term (`eval_iff`).
- **Nodes and vectors**: the subformula occurrences of a formula (`nodes`), and their values at a term (`vec`).
- **Adjunction is local** (`eval_insert_congr`): at a set with a member adjoined, the value of every node is fixed by
  the vectors of the set and of the new member.
- **Representatives grown by a candidate rule** (`growWith`): each round adds the candidates whose vectors are new. The
  vectors stay distinct, so a list of them has at most `2^m` entries for vectors of length `m`
  (`length_le_of_vectors`), and within `2^m + 1` rounds a round adds nothing (`growWith_closed`).
- **Grown by adjunction** (`plainReps`): the candidates are the empty set and every set adjoining a representative to a
  representative. The representatives hold the empty set's vector and every adjunction's (`plainReps_base`,
  `plainReps_adjoin`), and they cover every hereditary term (`plainReps_covers`).
- **The practical stage's representatives close too** (`bodyReps_check`): its growth over sublists is the same growth
  (`growReps_eq_growWith`), so its closedness check always passes (`practicalOK_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Plain formulas -/

/-- **Plain modal formulas**: the connectives, steps and their duals, with no fixed point, variable or atom. -/
inductive PlainFormula where
  | top
  | bot
  | and (left right : PlainFormula)
  | or (left right : PlainFormula)
  | possibly (label : StepLabel) (inner : PlainFormula)
  | necessarily (label : StepLabel) (inner : PlainFormula)
  deriving DecidableEq, Repr

namespace PlainFormula

/-- A plain formula as a formula. -/
def toFormula : PlainFormula → Formula 0
  | .top => .top
  | .bot => .bot
  | .and left right => .and left.toFormula right.toFormula
  | .or left right => .or left.toFormula right.toFormula
  | .possibly label inner => .possibly label inner.toFormula
  | .necessarily label inner => .necessarily label inner.toFormula

/-- **Evaluation at a term**: a step looks at the members of the term. -/
def eval : PlainFormula → Pattern → Bool
  | .top, _ => true
  | .bot, _ => false
  | .and left right, term => left.eval term && right.eval term
  | .or left right, term => left.eval term || right.eval term
  | .possibly label inner, term => decide (memberLabel label) && (membersOf term).any inner.eval
  | .necessarily label inner, term => !decide (memberLabel label) || (membersOf term).all inner.eval

/-- **The nodes**: the subformula occurrences, the formula first. -/
def nodes : PlainFormula → List PlainFormula
  | .top => [.top]
  | .bot => [.bot]
  | .and left right => .and left right :: (left.nodes ++ right.nodes)
  | .or left right => .or left right :: (left.nodes ++ right.nodes)
  | .possibly label inner => .possibly label inner :: inner.nodes
  | .necessarily label inner => .necessarily label inner :: inner.nodes

/-- **The vector of a term**: the values of the nodes there. -/
def vec (formula : PlainFormula) (term : Pattern) : List Bool := formula.nodes.map fun node => node.eval term

theorem self_mem_nodes : ∀ formula : PlainFormula, formula ∈ formula.nodes
  | .top | .bot | .and _ _ | .or _ _ | .possibly _ _ | .necessarily _ _ => List.mem_cons_self

theorem length_vec (formula : PlainFormula) (term : Pattern) : (formula.vec term).length = formula.nodes.length :=
  List.length_map _

theorem eval_of_vec {formula : PlainFormula} {first second : Pattern} (same : formula.vec first = formula.vec second) :
    ∀ node ∈ formula.nodes, node.eval first = node.eval second :=
  fun node inside => List.map_inj_left.mp same node inside

theorem vec_of_eval {formula : PlainFormula} {first second : Pattern}
    (same : ∀ node ∈ formula.nodes, node.eval first = node.eval second) : formula.vec first = formula.vec second :=
  List.map_congr_left same

end PlainFormula

/-- **Reading a plain formula off a formula**, when it is plain modal. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.plain? : {n : ℕ} → Formula n → Option PlainFormula
  | _, .top => some .top
  | _, .bot => some .bot
  | _, .and left right => do return .and (← left.plain?) (← right.plain?)
  | _, .or left right => do return .or (← left.plain?) (← right.plain?)
  | _, .possibly label inner => if label.isContext then none else do return .possibly label (← inner.plain?)
  | _, .necessarily label inner => if label.isContext then none else do return .necessarily label (← inner.plain?)
  | _, _ => none

example : (Formula.possibly .any (.and .top .bot) : Formula 0).plain? = some (.possibly .any (.and .top .bot)) := rfl

theorem toFormula_plain? : ∀ {formula : Formula 0} {plain : PlainFormula}, formula.plain? = some plain →
    plain.toFormula = formula ∧ formula.plainModal = true := by
  intro formula plain found
  cases formula
  case top => cases found; exact ⟨rfl, rfl⟩
  case bot => cases found; exact ⟨rfl, rfl⟩
  case and left right =>
    simp only [Formula.plain?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
    obtain ⟨l, foundL, r, foundR, rfl⟩ := found
    obtain ⟨eqL, plainL⟩ := toFormula_plain? foundL
    obtain ⟨eqR, plainR⟩ := toFormula_plain? foundR
    exact ⟨by rw [PlainFormula.toFormula, eqL, eqR], by simp only [Formula.plainModal, plainL, plainR, Bool.and_self]⟩
  case or left right =>
    simp only [Formula.plain?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
    obtain ⟨l, foundL, r, foundR, rfl⟩ := found
    obtain ⟨eqL, plainL⟩ := toFormula_plain? foundL
    obtain ⟨eqR, plainR⟩ := toFormula_plain? foundR
    exact ⟨by rw [PlainFormula.toFormula, eqL, eqR], by simp only [Formula.plainModal, plainL, plainR, Bool.and_self]⟩
  case possibly label inner =>
    simp only [Formula.plain?] at found
    split at found
    · cases found
    · rename_i own
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨i, foundI, rfl⟩ := found
      obtain ⟨eqI, plainI⟩ := toFormula_plain? foundI
      exact ⟨by rw [PlainFormula.toFormula, eqI], by simp only [Formula.plainModal, own, plainI]; rfl⟩
  case necessarily label inner =>
    simp only [Formula.plain?] at found
    split at found
    · cases found
    · rename_i own
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨i, foundI, rfl⟩ := found
      obtain ⟨eqI, plainI⟩ := toFormula_plain? foundI
      exact ⟨by rw [PlainFormula.toFormula, eqI], by simp only [Formula.plainModal, own, plainI]; rfl⟩
  all_goals simp [Formula.plain?] at found

theorem plain?_isSome : ∀ {formula : Formula 0}, formula.plainModal = true → ∃ plain, formula.plain? = some plain := by
  intro formula plain
  cases formula
  case top => exact ⟨_, rfl⟩
  case bot => exact ⟨_, rfl⟩
  case and left right =>
    simp only [Formula.plainModal, Bool.and_eq_true] at plain
    obtain ⟨l, foundL⟩ := plain?_isSome plain.1
    obtain ⟨r, foundR⟩ := plain?_isSome plain.2
    exact ⟨.and l r, by simp only [Formula.plain?, foundL, foundR]; rfl⟩
  case or left right =>
    simp only [Formula.plainModal, Bool.and_eq_true] at plain
    obtain ⟨l, foundL⟩ := plain?_isSome plain.1
    obtain ⟨r, foundR⟩ := plain?_isSome plain.2
    exact ⟨.or l r, by simp only [Formula.plain?, foundL, foundR]; rfl⟩
  case possibly label inner =>
    simp only [Formula.plainModal, Bool.and_eq_true, Bool.not_eq_true'] at plain
    obtain ⟨i, foundI⟩ := plain?_isSome plain.2
    exact ⟨.possibly label i, by simp only [Formula.plain?, plain.1, foundI]; rfl⟩
  case necessarily label inner =>
    simp only [Formula.plainModal, Bool.and_eq_true, Bool.not_eq_true'] at plain
    obtain ⟨i, foundI⟩ := plain?_isSome plain.2
    exact ⟨.necessarily label i, by simp only [Formula.plain?, plain.1, foundI]; rfl⟩
  all_goals simp [Formula.plainModal] at plain

namespace PlainFormula

/-! ## Evaluation is truth -/

/-- **Evaluation is the extensional truth** of the formula at every hereditary term. -/
theorem eval_iff : ∀ (formula : PlainFormula) (sets : Env ZFSet.{0} 0) {term : Pattern}, IsHF term →
    (formula.eval term = true ↔ extensional.sat sets formula.toFormula (zfOf term))
  | .top, _, _, _ => iff_of_true rfl trivial
  | .bot, _, _, _ => iff_of_false Bool.false_ne_true id
  | .and left right, sets, _, holds => by
    simp only [eval, Bool.and_eq_true, eval_iff left sets holds, eval_iff right sets holds]
    rfl
  | .or left right, sets, _, holds => by
    simp only [eval, Bool.or_eq_true, eval_iff left sets holds, eval_iff right sets holds]
    rfl
  | .possibly label inner, sets, term, holds => by
    simp only [eval, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    constructor
    · rintro ⟨labelled, value, member, holdsAt⟩
      exact ⟨zfOf value, ⟨labelled, (mem_zfOf_hf holds).mpr ⟨value, member, rfl⟩⟩,
        (eval_iff inner sets (hf_members holds value member)).mp holdsAt⟩
    · rintro ⟨next, ⟨labelled, member⟩, holdsAt⟩
      obtain ⟨value, valueMember, rfl⟩ := (mem_zfOf_hf holds).mp member
      exact ⟨labelled, value, valueMember, (eval_iff inner sets (hf_members holds value valueMember)).mpr holdsAt⟩
  | .necessarily label inner, sets, term, holds => by
    simp only [eval, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    constructor
    · rintro (unlabelled | every) next ⟨labelled, member⟩
      · exact absurd labelled unlabelled
      · obtain ⟨value, valueMember, rfl⟩ := (mem_zfOf_hf holds).mp member
        exact (eval_iff inner sets (hf_members holds value valueMember)).mp (every value valueMember)
    · intro every
      by_cases labelled : memberLabel label
      · exact Or.inr fun value member => (eval_iff inner sets (hf_members holds value member)).mpr
          (every _ ⟨labelled, (mem_zfOf_hf holds).mpr ⟨value, member, rfl⟩⟩)
      · exact Or.inl labelled

/-- Evaluation reads the set a hereditary term denotes. -/
theorem eval_congr (formula : PlainFormula) {first second : Pattern} (firstHolds : IsHF first)
    (secondHolds : IsHF second) (same : zfOf first = zfOf second) : formula.eval first = formula.eval second :=
  Bool.eq_iff_iff.mpr <| (eval_iff formula Env.closed firstHolds).trans <|
    same ▸ (eval_iff formula Env.closed secondHolds).symm

/-! ## Adjunction is local -/

theorem eval_insert_possibly (label : StepLabel) (inner : PlainFormula) (term whole : Pattern) :
    (PlainFormula.possibly label inner).eval (insertTerm term whole) =
      ((decide (memberLabel label) && inner.eval term) || (PlainFormula.possibly label inner).eval whole) := by
  simp only [eval, insertTerm, set, membersOf, List.any_cons]
  cases decide (memberLabel label) <;> simp

theorem eval_insert_necessarily (label : StepLabel) (inner : PlainFormula) (term whole : Pattern) :
    (PlainFormula.necessarily label inner).eval (insertTerm term whole) =
      ((!decide (memberLabel label) || inner.eval term) && (PlainFormula.necessarily label inner).eval whole) := by
  simp only [eval, insertTerm, set, membersOf, List.all_cons]
  cases decide (memberLabel label) <;> simp

/-- **At a set with a member adjoined, every node's value is fixed by the vectors** of the set and of the member. -/
theorem eval_insert_congr : ∀ (formula : PlainFormula) {whole whole' term term' : Pattern},
    (∀ node ∈ formula.nodes, node.eval whole = node.eval whole') →
    (∀ node ∈ formula.nodes, node.eval term = node.eval term') →
    ∀ node ∈ formula.nodes, node.eval (insertTerm term whole) = node.eval (insertTerm term' whole')
  | .top, _, _, _, _, _, _, node, inside => by
    rw [List.mem_singleton.mp inside]
    rfl
  | .bot, _, _, _, _, _, _, node, inside => by
    rw [List.mem_singleton.mp inside]
    rfl
  | .and left right, whole, whole', term, term', sameWhole, sameTerm, node, inside => by
    have leftCongr := eval_insert_congr left (fun node found => sameWhole node
      (List.mem_cons_of_mem _ (List.mem_append_left _ found))) (fun node found => sameTerm node
      (List.mem_cons_of_mem _ (List.mem_append_left _ found)))
    have rightCongr := eval_insert_congr right (fun node found => sameWhole node
      (List.mem_cons_of_mem _ (List.mem_append_right _ found))) (fun node found => sameTerm node
      (List.mem_cons_of_mem _ (List.mem_append_right _ found)))
    rcases List.mem_cons.mp inside with rfl | found
    · simp only [eval, leftCongr left (self_mem_nodes left), rightCongr right (self_mem_nodes right)]
    · rcases List.mem_append.mp found with found | found
      · exact leftCongr node found
      · exact rightCongr node found
  | .or left right, whole, whole', term, term', sameWhole, sameTerm, node, inside => by
    have leftCongr := eval_insert_congr left (fun node found => sameWhole node
      (List.mem_cons_of_mem _ (List.mem_append_left _ found))) (fun node found => sameTerm node
      (List.mem_cons_of_mem _ (List.mem_append_left _ found)))
    have rightCongr := eval_insert_congr right (fun node found => sameWhole node
      (List.mem_cons_of_mem _ (List.mem_append_right _ found))) (fun node found => sameTerm node
      (List.mem_cons_of_mem _ (List.mem_append_right _ found)))
    rcases List.mem_cons.mp inside with rfl | found
    · simp only [eval, leftCongr left (self_mem_nodes left), rightCongr right (self_mem_nodes right)]
    · rcases List.mem_append.mp found with found | found
      · exact leftCongr node found
      · exact rightCongr node found
  | .possibly label inner, whole, whole', term, term', sameWhole, sameTerm, node, inside => by
    have innerCongr := eval_insert_congr inner (fun node found => sameWhole node (List.mem_cons_of_mem _ found))
      (fun node found => sameTerm node (List.mem_cons_of_mem _ found))
    rcases List.mem_cons.mp inside with rfl | found
    · rw [eval_insert_possibly, eval_insert_possibly, sameWhole _ List.mem_cons_self,
        sameTerm inner (List.mem_cons_of_mem _ (self_mem_nodes inner))]
    · exact innerCongr node found
  | .necessarily label inner, whole, whole', term, term', sameWhole, sameTerm, node, inside => by
    have innerCongr := eval_insert_congr inner (fun node found => sameWhole node (List.mem_cons_of_mem _ found))
      (fun node found => sameTerm node (List.mem_cons_of_mem _ found))
    rcases List.mem_cons.mp inside with rfl | found
    · rw [eval_insert_necessarily, eval_insert_necessarily, sameWhole _ List.mem_cons_self,
        sameTerm inner (List.mem_cons_of_mem _ (self_mem_nodes inner))]
    · exact innerCongr node found

end PlainFormula

/-! ## Growing representatives by a candidate rule -/

/-- One round: add each candidate whose vector is new. -/
def stepWith (candidates : List Pattern → List Pattern) (vec : Pattern → List Bool) (reps : List Pattern) :
    List Pattern :=
  (candidates reps).foldl (addRep vec) reps

/-- **Rounds until one adds nothing**, within the fuel. -/
def growWith (candidates : List Pattern → List Pattern) (vec : Pattern → List Bool) :
    ℕ → List Pattern → List Pattern
  | 0, reps => reps
  | fuel + 1, reps =>
    if (stepWith candidates vec reps).length = reps.length then reps
    else growWith candidates vec fuel (stepWith candidates vec reps)

section Growth

variable {vec : Pattern → List Bool}

theorem length_addRep (reps : List Pattern) (candidate : Pattern) :
    (addRep vec reps candidate).length = reps.length ∨
      ((addRep vec reps candidate).length = reps.length + 1 ∧ ∀ r ∈ reps, vec r ≠ vec candidate) := by
  unfold addRep
  split
  · exact Or.inl rfl
  · rename_i fresh
    refine Or.inr ⟨by simp, fun r inside same => fresh ?_⟩
    exact List.any_eq_true.mpr ⟨r, inside, beq_iff_eq.mpr same⟩

theorem foldl_addRep_length_ge : ∀ (candidates reps : List Pattern),
    reps.length ≤ (candidates.foldl (addRep vec) reps).length
  | [], _ => le_rfl
  | candidate :: candidates, reps => by
    simp only [List.foldl_cons]
    refine le_trans ?_ (foldl_addRep_length_ge candidates (addRep vec reps candidate))
    rcases length_addRep (vec := vec) reps candidate with same | ⟨more, _⟩ <;> omega

/-- **A round adding nothing matched every candidate.** -/
theorem foldl_addRep_matched : ∀ (candidates reps : List Pattern),
    (candidates.foldl (addRep vec) reps).length = reps.length →
      ∀ candidate ∈ candidates, ∃ r ∈ reps, vec r = vec candidate
  | [], _, _ => fun _ inside => nomatch inside
  | candidate :: candidates, reps, same => by
    simp only [List.foldl_cons] at same
    have grown := foldl_addRep_length_ge (vec := vec) candidates (addRep vec reps candidate)
    by_cases matched : reps.any (fun r => vec r == vec candidate) = true
    · have unchanged : addRep vec reps candidate = reps := by
        unfold addRep
        rw [if_pos matched]
      rw [unchanged] at same
      intro other inside
      rcases List.mem_cons.mp inside with rfl | inside
      · obtain ⟨r, found, eq⟩ := List.any_eq_true.mp matched
        exact ⟨r, found, beq_iff_eq.mp eq⟩
      · exact foldl_addRep_matched candidates reps same other inside
    · have more : addRep vec reps candidate = reps ++ [candidate] := by
        unfold addRep
        rw [if_neg matched]
      rw [more] at grown same
      simp only [List.length_append, List.length_singleton] at grown
      omega

theorem nodup_addRep {reps : List Pattern} (distinct : (reps.map vec).Nodup) (candidate : Pattern) :
    ((addRep vec reps candidate).map vec).Nodup := by
  unfold addRep
  split
  · exact distinct
  · rename_i fresh
    rw [List.map_append, List.nodup_append]
    refine ⟨distinct, List.nodup_singleton _, ?_⟩
    intro first firstIn second secondIn same
    obtain ⟨r, inside, rfl⟩ := List.mem_map.mp firstIn
    rw [List.map_singleton, List.mem_singleton] at secondIn
    subst secondIn
    exact fresh (List.any_eq_true.mpr ⟨r, inside, beq_iff_eq.mpr same⟩)

theorem nodup_foldl_addRep : ∀ (candidates : List Pattern) {reps : List Pattern}, (reps.map vec).Nodup →
    ((candidates.foldl (addRep vec) reps).map vec).Nodup
  | [], _, distinct => distinct
  | candidate :: candidates, _, distinct => nodup_foldl_addRep candidates (nodup_addRep distinct candidate)

/-- **Distinct vectors of length `m` are at most `2^m`.** -/
theorem length_le_of_vectors {m : ℕ} (sized : ∀ term, (vec term).length = m) {reps : List Pattern}
    (distinct : (reps.map vec).Nodup) : reps.length ≤ 2 ^ m := by
  let asVector : Pattern → List.Vector Bool m := fun term => ⟨vec term, sized term⟩
  have values : (reps.map asVector).map List.Vector.toList = reps.map vec := by
    rw [List.map_map]
    rfl
  have nodupVectors : (reps.map asVector).Nodup := List.Nodup.of_map List.Vector.toList (values ▸ distinct)
  have bound := nodupVectors.length_le_card
  rw [List.length_map, card_vector, Fintype.card_bool] at bound
  exact bound

/-- **The growth closes within its fuel**: from distinct vectors of length `m`, `2^m + 1` rounds reach a round that
adds nothing, so every candidate of the result has the vector of a representative. -/
theorem growWith_closed (candidates : List Pattern → List Pattern) {m : ℕ} (sized : ∀ term, (vec term).length = m) :
    ∀ (fuel : ℕ) {reps : List Pattern}, (reps.map vec).Nodup → 2 ^ m < reps.length + fuel →
      ∀ candidate ∈ candidates (growWith candidates vec fuel reps),
        ∃ r ∈ growWith candidates vec fuel reps, vec r = vec candidate
  | 0, reps, distinct, enough => absurd (length_le_of_vectors sized distinct) (by omega)
  | fuel + 1, reps, distinct, enough => by
    simp only [growWith]
    split
    · rename_i same
      exact foldl_addRep_matched _ reps same
    · rename_i changed
      have grown := foldl_addRep_length_ge (vec := vec) (candidates reps) reps
      have more : reps.length + 1 ≤ (stepWith candidates vec reps).length := by
        unfold stepWith at changed ⊢
        omega
      exact growWith_closed candidates sized fuel (nodup_foldl_addRep _ distinct) (by omega)

theorem addRep_mem {reps : List Pattern} {candidate r : Pattern} (inside : r ∈ addRep vec reps candidate) :
    r ∈ reps ∨ r = candidate := by
  unfold addRep at inside
  split at inside
  · exact Or.inl inside
  · rcases List.mem_append.mp inside with found | found
    · exact Or.inl found
    · exact Or.inr (List.mem_singleton.mp found)

theorem foldl_addRep_mem : ∀ (candidates : List Pattern) {reps : List Pattern} {r : Pattern},
    r ∈ candidates.foldl (addRep vec) reps → r ∈ reps ∨ r ∈ candidates
  | [], _, _, inside => Or.inl inside
  | candidate :: candidates, _, _, inside => by
    simp only [List.foldl_cons] at inside
    rcases foldl_addRep_mem candidates inside with found | found
    · rcases addRep_mem found with found | rfl
      · exact Or.inl found
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ found)

/-- **Representatives stay hereditary** when the candidates of hereditary terms are. -/
theorem growWith_hf {candidates : List Pattern → List Pattern}
    (preserves : ∀ reps, (∀ r ∈ reps, IsHF r) → ∀ c ∈ candidates reps, IsHF c) :
    ∀ (fuel : ℕ) {reps : List Pattern}, (∀ r ∈ reps, IsHF r) → ∀ r ∈ growWith candidates vec fuel reps, IsHF r
  | 0, _, all => all
  | fuel + 1, reps, all => by
    simp only [growWith]
    split
    · exact all
    · refine growWith_hf preserves fuel fun r inside => ?_
      rcases foldl_addRep_mem _ inside with found | found
      · exact all r found
      · exact preserves reps all r found

end Growth

/-! ## Representatives of a plain formula, grown by adjunction -/

/-- **The candidates of adjunction**: the empty set, and every set adjoining a representative to a representative. -/
def adjunctions (reps : List Pattern) : List Pattern :=
  set [] :: reps.flatMap fun whole => reps.map fun term => insertTerm term whole

/-- **The representatives of a plain formula**: grown by adjunction from none, within `2^m + 1` rounds for `m`
nodes. -/
def plainReps (formula : PlainFormula) : List Pattern :=
  growWith adjunctions formula.vec (2 ^ formula.nodes.length + 1) []

theorem adjunctions_hf {reps : List Pattern} (all : ∀ r ∈ reps, IsHF r) : ∀ c ∈ adjunctions reps, IsHF c := by
  intro c inside
  rcases List.mem_cons.mp inside with rfl | found
  · exact set_hf fun _ found => nomatch found
  · obtain ⟨whole, wholeIn, found⟩ := List.mem_flatMap.mp found
    obtain ⟨term, termIn, rfl⟩ := List.mem_map.mp found
    exact insertTerm_hf (all term termIn) (all whole wholeIn)

theorem plainReps_hf (formula : PlainFormula) : ∀ r ∈ plainReps formula, IsHF r :=
  growWith_hf (fun _ => adjunctions_hf) _ fun _ inside => nomatch inside

theorem plainReps_closed (formula : PlainFormula) :
    ∀ c ∈ adjunctions (plainReps formula), ∃ r ∈ plainReps formula, formula.vec r = formula.vec c :=
  growWith_closed adjunctions (formula.length_vec) _ List.nodup_nil (by simp)

/-- **The empty set's vector is a representative's.** -/
theorem plainReps_base (formula : PlainFormula) : ∃ r ∈ plainReps formula, formula.vec r = formula.vec (set []) :=
  plainReps_closed formula _ List.mem_cons_self

/-- **Every adjunction's vector is a representative's.** -/
theorem plainReps_adjoin (formula : PlainFormula) {whole term : Pattern} (wholeIn : whole ∈ plainReps formula)
    (termIn : term ∈ plainReps formula) :
    ∃ r ∈ plainReps formula, formula.vec r = formula.vec (insertTerm term whole) :=
  plainReps_closed formula _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨whole, wholeIn,
    List.mem_map.mpr ⟨term, termIn, rfl⟩⟩))

/-- **The representatives cover every hereditary term**: some representative has its vector. -/
theorem plainReps_covers (formula : PlainFormula) :
    ∀ {term : Pattern}, IsHF term → ∃ r ∈ plainReps formula, formula.vec r = formula.vec term := by
  intro term holds
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values all ih =>
    induction values with
    | nil => exact plainReps_base formula
    | cons value values tailIh =>
      obtain ⟨whole, wholeIn, sameWhole⟩ := tailIh (fun other found => all other (List.mem_cons_of_mem _ found))
        (fun other found => ih other (List.mem_cons_of_mem _ found))
      obtain ⟨term, termIn, sameTerm⟩ := ih value List.mem_cons_self
      obtain ⟨r, rIn, sameR⟩ := plainReps_adjoin formula wholeIn termIn
      refine ⟨r, rIn, sameR.trans (PlainFormula.vec_of_eval ?_)⟩
      exact PlainFormula.eval_insert_congr formula (PlainFormula.eval_of_vec sameWhole)
        (PlainFormula.eval_of_vec sameTerm)

/-! ## The practical stage's representatives always close -/

/-- The practical stage's growth is growth by the rule of sets over sublists. -/
theorem growReps_eq_growWith (vec : Pattern → List Bool) :
    ∀ (fuel : ℕ) (reps : List Pattern), growReps vec fuel reps = growWith (fun reps => reps.sublists.map set) vec fuel reps
  | 0, _ => rfl
  | fuel + 1, reps => by
    have same : stepWith (fun reps => reps.sublists.map set) vec reps = growStep vec reps := rfl
    simp only [growReps, growWith, same, growReps_eq_growWith vec fuel]

/-- **A body's representatives are closed**: the practical stage's check never fails, so for a guarded, count-guarded
body the stage never falls back to the whole stage. -/
theorem bodyReps_check (inner : Formula 0) :
    repsCheck (closureVec (guardedClosure inner)) (bodyReps inner) = true := by
  have closed := growWith_closed (fun reps => reps.sublists.map set) (vec := closureVec (guardedClosure inner))
    (m := (guardedClosure inner).length) (fun _ => List.length_map _) (2 ^ (guardedClosure inner).length + 1)
    (reps := []) List.nodup_nil (by simp)
  rw [← growReps_eq_growWith] at closed
  simp only [repsCheck, List.all_eq_true, List.any_eq_true, beq_iff_eq]
  intro sub inside
  exact closed (set sub) (List.mem_map.mpr ⟨sub, inside, rfl⟩)

theorem practicalOK_eq (inner : Formula 0) :
    practicalOK inner = (inner.guardedIn (fun _ => false) (fun _ => false) &&
      (guardedClosure inner).all Formula.countGuarded) := by
  simp only [practicalOK, bodyReps_check, Bool.and_true]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
