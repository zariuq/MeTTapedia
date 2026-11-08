import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosureAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyFormers

/-!
# The stratified Miller class under decomposition

**Closed Miller codes.** A normal code with Miller occurrences when every free variable is read as a metavariable and
every binder as a rigid local (`miller (fun _ => true)`) has Miller normal forms at **every** opening depth
(`sides_of_closed`): opening applies it to distinct fresh locals, and hereditary substitution of variables keeps
Miller occurrences (`ContextualDependentHereditary.collapse_miller`). So on normal codes the side condition of the
Miller class is a syntactic check that does not depend on how deep an equation is opened
(`fragmentSidesMiller_of_closed`). This is why decomposition and answers cannot push a store out of the class by
opening it deeper, unlike the arity condition (`ContextualDependentShortClosure.Controls.twin_first_round`).

**Splicing.** Replacing an equation by pieces with exactly its solutions keeps the class, when the pieces have Miller
sides and stratified annotations among themselves (`StratifiedMiller.splice`, R99's `Stratified.splice` for the
corrected class).

**The pieces of formers under abstractions** (R99's `underParts`: Π, Σ, identity types and pairs, under any number of
abstractions) of normal closed Miller sides are normal closed Miller codes (`underParts_closed`), so they meet the side
condition of the splice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentShortClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure ContextualDependentHereditary
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Closed Miller codes open to Miller normal forms at every depth -/

section Raw

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

/-- **One more local**: a Miller normal form of an opened side gives one of the side opened once more. -/
theorem miller_step {n d : Nat} {code : Tm Head n}
    (found : ∃ opened, Star (R := R) (openCode d code) opened ∧ Normal R opened ∧
      miller (openedFlexible d) opened = true) :
    ∃ opened, Star (R := R) (openCode (d + 1) code) opened ∧ Normal R opened ∧
      miller (openedFlexible (d + 1)) opened = true := by
  obtain ⟨N, toN, normalN, millerN⟩ := found
  have respects : ∀ i : Fin (n + d),
      openedFlexible (d + 1) ((wk : Ren (n + d) (n + d + 1)) i) = openedFlexible d i := by
    intro i
    simp only [openedFlexible, wk, Fin.val_succ, Nat.add_le_add_iff_right]
  obtain ⟨t', steps, normal', miller'⟩ := collapse_miller empty [0] N (openedFlexible d) wk normalN millerN
    (Fin.succ_injective _) respects
    (fun y member => by
      rw [List.mem_singleton.mp member]
      simp [openedFlexible])
    (List.nodup_singleton _)
    (fun y member i same => by
      rw [List.mem_singleton.mp member] at same
      exact Fin.succ_ne_zero _ same)
  refine ⟨t', ?_, normal', miller'⟩
  change Star (R := R) (.app (Presentation.rename wk (openCode d code)) (.var 0)) t'
  exact (star_app (star_rename wk toN) .refl).trans steps

/-- **A normal closed Miller code has a Miller normal form at every opening depth.** -/
theorem sides_of_closed {n : Nat} {code : Tm Head n} (normal : Normal R code)
    (closed : miller (fun _ => true) code = true) :
    ∀ d : Nat, ∃ opened, Star (R := R) (openCode d code) opened ∧ Normal R opened ∧
      miller (openedFlexible d) opened = true
  | 0 => by
      refine ⟨code, .refl, normal, ?_⟩
      have marking : openedFlexible (n := n + 0) 0 = fun _ => true := funext fun i => by simp [openedFlexible]
      rw [marking]
      exact closed
  | d + 1 => miller_step empty (sides_of_closed normal closed d)

end Raw

section Equations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **An equation whose two side codes are normal closed Miller codes has Miller sides**, at its opening depth. -/
theorem fragmentSidesMiller_of_closed (empty : rules.computation = RootComputation.empty) {Θ : Context rules}
    {equation : Equation (TotalTerm Θ)} (normalLeft : Normal rules equation.1.2.code)
    (normalRight : Normal rules equation.2.2.code) (closedLeft : miller (fun _ => true) equation.1.2.code = true)
    (closedRight : miller (fun _ => true) equation.2.2.code = true) : FragmentSidesMiller equation :=
  ⟨all_miller_of_one empty (sides_of_closed empty normalLeft closedLeft _),
    all_miller_of_one empty (sides_of_closed empty normalRight closedRight _)⟩

/-- **Replacing one equation by pieces with exactly its solutions keeps the Miller class**, when the pieces have
Miller sides and stratified annotations among themselves, after the equations before them. -/
theorem StratifiedMiller.splice {Θ : Context rules} {before after pieces : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : StratifiedMiller levels (before ++ equation :: after))
    (exact : ∀ {Δ : Context rules} (σ : Δ ⟶ Θ),
      (frames levels).Models σ pieces ↔ (frames levels).Solves σ equation)
    (sides : ∀ piece ∈ pieces, FragmentSidesMiller piece)
    (internal : ∀ (first last : EquationStore (TotalTerm Θ)) (piece : Equation (TotalTerm Θ)),
      pieces = first ++ piece :: last → StratifiedAt levels (before ++ first) piece) :
    StratifiedMiller levels (before ++ (pieces ++ after)) := by
  have afterPart : ∀ (middle rest : EquationStore (TotalTerm Θ)) (later : Equation (TotalTerm Θ)),
      after = middle ++ later :: rest →
      FragmentSidesMiller later ∧ StratifiedAt levels (before ++ (pieces ++ middle)) later := by
    intro middle rest later split
    have whole := stratified (before ++ equation :: middle) rest later (by rw [split]; simp)
    refine ⟨whole.1, fun σ solved => whole.2 σ ?_⟩
    rw [models_append_iff, models_append_iff] at solved
    rw [models_append_iff]
    refine ⟨solved.1, ?_⟩
    intro e member
    rcases List.mem_cons.mp member with rfl | inside
    · exact (exact σ).mp solved.2.1
    · exact solved.2.2 e inside
  intro before' after' later split
  rcases List.append_eq_append_iff.mp split with ⟨cs, rfl, rest⟩ | ⟨bs, sameBefore, rest⟩
  · rcases List.append_eq_append_iff.mp rest with ⟨ds, rfl, inAfter⟩ | ⟨ds, inPieces, tail⟩
    · have := afterPart ds after' later inAfter
      simpa [List.append_assoc] using this
    · rcases ds with _ | ⟨first, ds⟩
      · simp only [List.append_nil] at inPieces
        subst inPieces
        have := afterPart [] after' later (by simpa using tail.symm)
        simpa using this
      · simp only [List.cons_append, List.cons.injEq] at tail
        obtain ⟨rfl, rfl⟩ := tail
        exact ⟨sides _ (by rw [inPieces]; exact List.mem_append_right _ List.mem_cons_self),
          internal cs ds later inPieces⟩
  · rcases List.cons_eq_append_iff.mp rest with ⟨rfl, inRest⟩ | ⟨bs', rfl, tail⟩
    · simp only [List.append_nil] at sameBefore
      subst sameBefore
      rcases List.append_eq_cons_iff.mp inRest with ⟨rfl, inAfter⟩ | ⟨ps, inPieces, tail⟩
      · have := afterPart [] after' later inAfter.symm.symm
        simpa using this
      · refine ⟨sides _ (by rw [inPieces]; exact List.mem_cons_self), ?_⟩
        have atPiece : StratifiedAt levels (before ++ []) later := internal [] ps later inPieces
        rwa [List.append_nil] at atPiece
    · have whole := stratified before' (bs' ++ equation :: after) later (by rw [sameBefore]; simp)
      exact whole

/-- **Mapping every equation to one with the same solutions keeps the Miller class**, when the map keeps Miller sides
and stratified annotations: R99's twin retyping and collapse, and every re-expression of a side with the same
solutions, are instances. -/
theorem StratifiedMiller.map {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (stratified : StratifiedMiller levels problem) (f : Equation (TotalTerm Θ) → Equation (TotalTerm Θ))
    (same : ∀ (equation : Equation (TotalTerm Θ)) {Δ : Context rules} (σ : Δ ⟶ Θ),
      (frames levels).Solves σ (f equation) ↔ (frames levels).Solves σ equation)
    (sides : ∀ equation ∈ problem, FragmentSidesMiller equation → FragmentSidesMiller (f equation))
    (annotations : ∀ equation ∈ problem, ∀ before : EquationStore (TotalTerm Θ),
      StratifiedAt levels before equation → StratifiedAt levels before (f equation)) :
    StratifiedMiller levels (problem.map f) := by
  intro before' after' later split
  obtain ⟨before, rest, rfl, rfl, mapped⟩ := List.map_eq_append_iff.mp split
  obtain ⟨equation, after, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
  have member : equation ∈ before ++ equation :: after := List.mem_append_right _ List.mem_cons_self
  obtain ⟨sides₀, at₀⟩ := stratified before after equation rfl
  refine ⟨sides equation member sides₀, fun σ solved => annotations equation member before at₀ σ ?_⟩
  intro e inside
  exact (same e σ).mp (solved (f e) (List.mem_map.mpr ⟨e, inside, rfl⟩))

/-- **The Miller class after a fixed prefix**: every equation has Miller sides and annotations equal under every
solution of the prefix and of the equations before it. -/
def StratifiedMillerFrom (levels : LevelModel rules L) {Θ : Context rules} (fixed problem : EquationStore (TotalTerm Θ)) :
    Prop :=
  ∀ (before after : EquationStore (TotalTerm Θ)) (equation : Equation (TotalTerm Θ)),
    problem = before ++ equation :: after → FragmentSidesMiller equation ∧ StratifiedAt levels (fixed ++ before) equation

theorem stratifiedMillerFrom_nil {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)} :
    StratifiedMillerFrom levels [] problem ↔ StratifiedMiller levels problem := by
  unfold StratifiedMillerFrom StratifiedMiller
  simp only [List.nil_append]

theorem StratifiedMillerFrom.nil {Θ : Context rules} (fixed : EquationStore (TotalTerm Θ)) :
    StratifiedMillerFrom levels fixed [] := by
  intro before after equation split
  cases before <;> cases split

theorem StratifiedMillerFrom.head {Θ : Context rules} {fixed rest : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : StratifiedMillerFrom levels fixed (equation :: rest)) :
    FragmentSidesMiller equation ∧ StratifiedAt levels fixed equation := by
  have := stratified [] rest equation rfl
  simpa using this

theorem StratifiedMillerFrom.tail {Θ : Context rules} {fixed rest : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : StratifiedMillerFrom levels fixed (equation :: rest)) :
    StratifiedMillerFrom levels (fixed ++ [equation]) rest := by
  intro before after later split
  have := stratified (equation :: before) after later (by rw [split]; rfl)
  simpa [List.append_assoc] using this

theorem StratifiedMillerFrom.cons {Θ : Context rules} {fixed rest : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (sides : FragmentSidesMiller equation)
    (atFixed : StratifiedAt levels fixed equation) (later : StratifiedMillerFrom levels (fixed ++ [equation]) rest) :
    StratifiedMillerFrom levels fixed (equation :: rest) := by
  intro before after other split
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      refine ⟨sides, ?_⟩
      rw [List.append_nil]
      exact atFixed
  | cons first before =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      have := later before after other rfl
      simpa [List.append_assoc] using this

/-- **Dropping equations that hold at every substitution keeps the Miller class after a prefix**, read through a
selection: `keep equation = false` only for equations that hold at every substitution. -/
theorem StratifiedMillerFrom.filter_valid {Θ : Context rules} (keep : Equation (TotalTerm Θ) → Bool)
    (valid : ∀ equation, keep equation = false → ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Solves σ equation) :
    ∀ {fixed fixed' : EquationStore (TotalTerm Θ)} (problem : EquationStore (TotalTerm Θ)),
      (∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Models σ fixed' → (frames levels).Models σ fixed) →
      StratifiedMillerFrom levels fixed problem → StratifiedMillerFrom levels fixed' (problem.filter keep)
  | _, fixed', [], _, _ => StratifiedMillerFrom.nil fixed'
  | fixed, fixed', equation :: rest, stronger, stratified => by
      obtain ⟨sides, atFixed⟩ := stratified.head
      by_cases kept : keep equation = true
      · rw [List.filter_cons_of_pos kept]
        refine StratifiedMillerFrom.cons sides (fun σ solved => atFixed σ (stronger σ solved)) ?_
        refine StratifiedMillerFrom.filter_valid keep valid rest (fixed := fixed ++ [equation]) (fun σ solved => ?_)
          stratified.tail
        rw [models_append_iff] at solved ⊢
        exact ⟨stronger σ solved.1, solved.2⟩
      · rw [List.filter_cons_of_neg kept]
        refine StratifiedMillerFrom.filter_valid keep valid rest (fixed := fixed ++ [equation]) (fun σ solved => ?_)
          stratified.tail
        rw [models_append_iff]
        refine ⟨stronger σ solved, ?_⟩
        intro other member
        rw [List.mem_singleton.mp member]
        exact valid equation (by simpa using kept) σ

/-- **The conversion scan keeps the Miller class**: dropping the equations that hold at every substitution. -/
theorem StratifiedMiller.filter_valid {Θ : Context rules} (keep : Equation (TotalTerm Θ) → Bool)
    (valid : ∀ equation, keep equation = false → ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Solves σ equation)
    {problem : EquationStore (TotalTerm Θ)} (stratified : StratifiedMiller levels problem) :
    StratifiedMiller levels (problem.filter keep) :=
  stratifiedMillerFrom_nil.mp (StratifiedMillerFrom.filter_valid keep valid problem (fun _ solved => solved)
    (stratifiedMillerFrom_nil.mpr stratified))

end Equations

/-! ## The pieces of formers under abstractions -/

section Pieces

open ContextualDependentSpinesMany

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (empty : S.R.computation = RootComputation.empty)
include empty

/-- Normal Miller codes, at one marking. -/
def NormalMiller {n : Nat} (mark : Fin n → Bool) (code : Tm Head n) : Prop :=
  Normal S.R code ∧ miller mark code = true

omit empty in
theorem NormalMiller.lam {n : Nat} {mark : Fin n → Bool} {body : Tm Head (n + 1)}
    (inner : NormalMiller (S := S) (liftFlexible mark) body) (empty : S.R.computation = RootComputation.empty) :
    NormalMiller (S := S) mark (.lam body) :=
  ⟨(normal_lam_iff empty).mpr inner.1, inner.2⟩

/-- **The pieces of a former equation at a universe** have normal Miller codes when the two formers do. -/
theorem baseParts_closed {n : Nat} {u : Head} (mark : Fin n → Bool) {left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : baseParts u left right = some pieces)
    (leftClosed : NormalMiller (S := S) mark left) (rightClosed : NormalMiller (S := S) mark right) :
    ∀ piece ∈ pieces, NormalMiller (S := S) mark piece.left ∧ NormalMiller (S := S) mark piece.right := by
  cases left with
  | pi B C =>
      cases right with
      | pi B' C' =>
          simp only [baseParts, Option.some.injEq] at found
          subst found
          obtain ⟨nB, nC⟩ := (normal_pi_iff empty).mp leftClosed.1
          obtain ⟨nB', nC'⟩ := (normal_pi_iff empty).mp rightClosed.1
          have mL := leftClosed.2
          have mR := rightClosed.2
          simp only [miller, Bool.and_eq_true] at mL mR
          intro piece member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨⟨nB, mL.1⟩, ⟨nB', mR.1⟩⟩
          · exact ⟨NormalMiller.lam ⟨nC, mL.2⟩ empty, NormalMiller.lam ⟨nC', mR.2⟩ empty⟩
      | _ => simp [baseParts] at found
  | sigma B C =>
      cases right with
      | sigma B' C' =>
          simp only [baseParts, Option.some.injEq] at found
          subst found
          obtain ⟨nB, nC⟩ := (normal_sigma_iff empty).mp leftClosed.1
          obtain ⟨nB', nC'⟩ := (normal_sigma_iff empty).mp rightClosed.1
          have mL := leftClosed.2
          have mR := rightClosed.2
          simp only [miller, Bool.and_eq_true] at mL mR
          intro piece member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨⟨nB, mL.1⟩, ⟨nB', mR.1⟩⟩
          · exact ⟨NormalMiller.lam ⟨nC, mL.2⟩ empty, NormalMiller.lam ⟨nC', mR.2⟩ empty⟩
      | _ => simp [baseParts] at found
  | id C a b =>
      cases right with
      | id C' a' b' =>
          simp only [baseParts, Option.some.injEq] at found
          subst found
          obtain ⟨nC, na, nb⟩ := (normal_id_iff empty).mp leftClosed.1
          obtain ⟨nC', na', nb'⟩ := (normal_id_iff empty).mp rightClosed.1
          have mL := leftClosed.2
          have mR := rightClosed.2
          simp only [miller, Bool.and_eq_true] at mL mR
          intro piece member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact ⟨⟨nC, mL.1.1⟩, ⟨nC', mR.1.1⟩⟩
          · exact ⟨⟨na, mL.1.2⟩, ⟨na', mR.1.2⟩⟩
          · exact ⟨⟨nb, mL.2⟩, ⟨nb', mR.2⟩⟩
      | _ => simp [baseParts] at found
  | _ => simp [baseParts] at found

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- **The pieces of formers under abstractions have normal Miller codes** when the two sides do, at every marking. -/
theorem underParts_closed : ∀ {n : Nat} (annotation left right : Tm Head n) {pieces : List (Piece Head n)}
    (mark : Fin n → Bool), underParts (S := S) annotation left right = some pieces →
    NormalMiller (S := S) mark left → NormalMiller (S := S) mark right →
    ∀ piece ∈ pieces, NormalMiller (S := S) mark piece.left ∧ NormalMiller (S := S) mark piece.right
  | _, .head u, left, right, pieces, mark, found, leftClosed, rightClosed => by
      obtain ⟨-, base⟩ := underParts_head found
      exact baseParts_closed empty mark base leftClosed rightClosed
  | _, .pi D T, left, right, pieces, mark, found, leftClosed, rightClosed => by
      obtain ⟨l, r, inner, rfl, rfl, computed, rfl⟩ := underParts_pi_cases found
      have lClosed : NormalMiller (S := S) (liftFlexible mark) l :=
        ⟨(normal_lam_iff empty).mp leftClosed.1, leftClosed.2⟩
      have rClosed : NormalMiller (S := S) (liftFlexible mark) r :=
        ⟨(normal_lam_iff empty).mp rightClosed.1, rightClosed.2⟩
      intro piece member
      obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
      obtain ⟨pl, pr⟩ := underParts_closed T l r (liftFlexible mark) computed lClosed rClosed original inInner
      exact ⟨NormalMiller.lam pl empty, NormalMiller.lam pr empty⟩
  | _, .sigma A B, left, right, pieces, mark, found, leftClosed, rightClosed => by
      obtain ⟨a, b, a', b', rfl, rfl, rfl⟩ := underParts_sigma_cases found
      obtain ⟨na, nb⟩ := (normal_pair_iff empty).mp leftClosed.1
      obtain ⟨na', nb'⟩ := (normal_pair_iff empty).mp rightClosed.1
      have mL := leftClosed.2
      have mR := rightClosed.2
      simp only [miller, Bool.and_eq_true] at mL mR
      intro piece member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨⟨na, mL.1⟩, ⟨na', mR.1⟩⟩
      · exact ⟨⟨nb, mL.2⟩, ⟨nb', mR.2⟩⟩
  | _, .var _, _, _, _, _, found, _, _ | _, .const _, _, _, _, _, found, _, _
  | _, .id _ _ _, _, _, _, _, found, _, _ | _, .lam _, _, _, _, _, found, _, _
  | _, .app _ _, _, _, _, _, found, _, _ | _, .pair _ _, _, _, _, _, found, _, _
  | _, .fst _, _, _, _, _, found, _, _ | _, .snd _, _, _, _, _, found, _, _
  | _, .refl _, _, _, _, _, found, _, _ => by simp [underParts] at found

end Pieces

/-! ## The pieces of formers are stratified among themselves -/

section Internal

open ContextualDependentSpinesMany ContextualDependentRigidFormers

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)
include facts algebra

/-- **Each piece of a former decomposition under abstractions has annotations that are equal types once the pieces
before it hold.** Under the abstractions every piece shares the left side's domains; at a universe, the family twin of
a Π or Σ type and the endpoints of an identity type are compared after the domain or carrier; at a Σ type, the second
components are compared after the first. This is the internal obligation of `StratifiedMiller.splice` (and of R99's
`Stratified.splice`) for the pieces of `underParts`, at every substitution into every formed context. -/
theorem underParts_internal : ∀ {n : Nat} (annotation left right : Tm Head n) {pieces : List (Piece Head n)},
    underParts (S := S) annotation left right = some pieces →
    ∀ {m : Nat} {Δ : Ctx Head m} (θ : Sub Head n m), CtxFormed S.R Δ → IsType S.R Δ (subst θ annotation) →
    ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
      (∀ q ∈ first, (q.subst θ).Holds S.R Δ) →
      TypeEq S.R Δ (subst θ piece.leftType) (subst θ piece.rightType)
  | _, .head u, left, right, pieces, found, _, Δ, θ, formed, _, first, last, piece, split, held => by
      obtain ⟨hu, base⟩ := underParts_head found
      have universal : TypeEq S.R Δ (.head u) (.head u) := ContextualDependentRank.universe_typeEq Δ hu
      have binderCase : ∀ {B B' : Tm Head _} {C C' : Tm Head (_ + 1)},
          pieces = [⟨.head u, B, .head u, B'⟩, ⟨.pi B (.head u), .lam C, .pi B' (.head u), .lam C'⟩] →
          TypeEq S.R Δ (subst θ piece.leftType) (subst θ piece.rightType) := by
        intro B B' C C' shape
        rw [shape] at split
        rcases first with _ | ⟨one, _ | ⟨two, rest⟩⟩
        · simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, -⟩ := split
          exact universal
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl, -⟩ := split
          have domains := (held _ List.mem_cons_self).2
          change Equal S.R Δ (subst θ B) (subst θ B') (.head u) at domains
          change TypeEq S.R Δ (.pi (subst θ B) (.head u)) (.pi (subst θ B') (.head u))
          exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr
            ⟨⟨u, hu, domains⟩, ContextualDependentRank.universe_typeEq _ hu⟩
        · simp at split
      cases left with
      | pi B C =>
          cases right with
          | pi B' C' =>
              simp only [baseParts, Option.some.injEq] at base
              exact binderCase base.symm
          | _ => simp [baseParts] at base
      | sigma B C =>
          cases right with
          | sigma B' C' =>
              simp only [baseParts, Option.some.injEq] at base
              exact binderCase base.symm
          | _ => simp [baseParts] at base
      | id C a b =>
          cases right with
          | id C' a' b' =>
              simp only [baseParts, Option.some.injEq] at base
              subst base
              rcases first with _ | ⟨one, rest⟩
              · simp only [List.nil_append, List.cons.injEq] at split
                obtain ⟨rfl, -⟩ := split
                exact universal
              · simp only [List.cons_append, List.cons.injEq] at split
                obtain ⟨rfl, split⟩ := split
                have carriers := (held _ List.mem_cons_self).2
                change Equal S.R Δ (subst θ C) (subst θ C') (.head u) at carriers
                have carriersEq : TypeEq S.R Δ (subst θ C) (subst θ C') := ⟨u, hu, carriers⟩
                rcases rest with _ | ⟨two, _ | ⟨three, rest⟩⟩
                · simp only [List.nil_append, List.cons.injEq] at split
                  obtain ⟨rfl, -⟩ := split
                  exact carriersEq
                · simp only [List.cons_append, List.nil_append, List.cons.injEq] at split
                  obtain ⟨rfl, rfl, -⟩ := split
                  exact carriersEq
                · simp at split
          | _ => simp [baseParts] at base
      | _ => simp [baseParts] at base
  | _, .pi D T, left, right, pieces, found, _, Δ, θ, formed, isType, first, last, piece, split, held => by
      obtain ⟨l, r, inner, rfl, rfl, computed, rfl⟩ := underParts_pi_cases found
      obtain ⟨u, hu, typed⟩ := isType
      change TypedEquality.Typed S.R Δ (binder true (subst θ D) (subst (liftSub θ) T)) (.head u) at typed
      obtain ⟨tD, tT⟩ := binder_typed facts algebra true formed typed
      obtain ⟨first', rest', innerSplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
      obtain ⟨piece', last', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
      have held' : ∀ q ∈ first', (q.subst (liftSub θ)).Holds S.R (.snoc Δ (subst θ D)) := by
        intro q member
        obtain ⟨types, terms⟩ := held (q.under D) (List.mem_map.mpr ⟨q, member, rfl⟩)
        change TypeEq S.R Δ (.pi (subst θ D) (subst (liftSub θ) q.leftType))
          (.pi (subst θ D) (subst (liftSub θ) q.rightType)) at types
        change Equal S.R Δ (.lam (subst (liftSub θ) q.left)) (.lam (subst (liftSub θ) q.right))
          (.pi (subst θ D) (subst (liftSub θ) q.leftType)) at terms
        exact ⟨((ContextualDependentRigid.typeEq_pi_iff facts formed).mp types).2,
          ContextualDependentOccursFull.lam_equal_inv facts formed terms⟩
      have below := underParts_internal T l r computed (liftSub θ) (formed.snoc ⟨u, hu, tD⟩) ⟨u, hu, tT⟩
        first' last' piece' innerSplit held'
      change TypeEq S.R Δ (.pi (subst θ D) (subst (liftSub θ) piece'.leftType))
        (.pi (subst θ D) (subst (liftSub θ) piece'.rightType))
      exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr
        ⟨IsType.refl ⟨u, hu, tD⟩, below⟩
  | _, .sigma A B, left, right, pieces, found, _, Δ, θ, formed, isType, first, last, piece, split, held => by
      obtain ⟨a, b, a', b', rfl, rfl, rfl⟩ := underParts_sigma_cases found
      obtain ⟨u, hu, typed⟩ := isType
      change TypedEquality.Typed S.R Δ (binder false (subst θ A) (subst (liftSub θ) B)) (.head u) at typed
      obtain ⟨tA, tB⟩ := binder_typed facts algebra false formed typed
      rcases first with _ | ⟨one, rest⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, -⟩ := split
        exact IsType.refl ⟨u, hu, tA⟩
      · simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, split⟩ := split
        rcases rest with _ | ⟨two, rest⟩
        · simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, -⟩ := split
          have firsts := (held _ List.mem_cons_self).2
          change Equal S.R Δ (subst θ a) (subst θ a') (subst θ A) at firsts
          change TypeEq S.R Δ (subst θ (inst0 a B)) (subst θ (inst0 a' B))
          rw [subst_inst0, subst_inst0]
          exact TypeEq.of_instantiateEq tB hu (Equal.typed (S := S) firsts formed).1 firsts
        · simp at split
  | _, .var _, _, _, _, found, _, _, _, _, _, _, _, _, _, _ | _, .const _, _, _, _, found, _, _, _, _, _, _, _, _, _, _
  | _, .id _ _ _, _, _, _, found, _, _, _, _, _, _, _, _, _, _
  | _, .lam _, _, _, _, found, _, _, _, _, _, _, _, _, _, _ | _, .app _ _, _, _, _, found, _, _, _, _, _, _, _, _, _, _
  | _, .pair _ _, _, _, _, found, _, _, _, _, _, _, _, _, _, _
  | _, .fst _, _, _, _, found, _, _, _, _, _, _, _, _, _, _ | _, .snd _, _, _, _, found, _, _, _, _, _, _, _, _, _, _
  | _, .refl _, _, _, _, found, _, _, _, _, _, _, _, _, _, _ => by simp [underParts] at found

end Internal

end ContextualDependentShortClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
