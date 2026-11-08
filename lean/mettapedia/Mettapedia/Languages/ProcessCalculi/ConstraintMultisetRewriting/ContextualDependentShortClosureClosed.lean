import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosurePieces

/-!
# Miller sides are a syntactic, depth-free condition on normal codes

For a normal code `c`, the Miller condition on the normal forms of `c` opened at some depth holds **exactly when**
`c` itself has Miller occurrences with every free variable read as a metavariable and every binder as a rigid local
(`miller (fun _ => true) c`):

* `ContextualDependentShortClosure.sides_of_closed` (one direction): a closed Miller code opens to Miller normal forms
  at every depth;
* `closed_of_sides` (the other): if the normal form of `c` opened at depth `d` is Miller, so is `c`. Opening applies
  `c`, weakened, to distinct fresh locals (`openCode_eq_appsFwd`); contracting the leading abstractions is a renaming,
  and Miller occurrences are reflected by injective renamings that respect the marking (`miller_rename_reflect`) and
  by spine prefixes (`miller_of_app_var`), so they are reflected by the contraction (`collapse_reflect`).

So on stores whose side codes are normal, the side condition of the stratified Miller class does not depend on the
opening depth (`fragmentSidesMiller_iff_closed`): it is the decidable check `miller (fun _ => true)` on the two codes.
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

section Raw

variable {Head : Type}

/-! ## Reflection of Miller occurrences -/

theorem millerSpine_rename_reflect {n m : Nat} {ρ : Ren n m}
    {flexible : Fin n → Bool} {flexible' : Fin m → Bool} (respects : ∀ i, flexible' (ρ i) = flexible i)
    {t : Tm Head n} (spine : millerSpine flexible' (Presentation.rename ρ t) = true) : millerSpine flexible t = true := by
  unfold millerSpine at spine ⊢
  rw [readSpine_rename] at spine
  cases read : readSpine t with
  | none => rw [read] at spine; cases spine
  | some found =>
      obtain ⟨head, arguments⟩ := found
      rw [read] at spine
      simp only [Option.map_some, Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at spine
      obtain ⟨⟨flexibleHead, rigid⟩, distinct⟩ := spine
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
      refine ⟨⟨by rw [← respects]; exact flexibleHead, fun argument member => ?_⟩, distinct.of_map ρ⟩
      rw [← respects]
      exact rigid argument member

/-- **Miller occurrences are reflected by every injective renaming that respects the marking.** -/
theorem miller_rename_reflect : ∀ {n m : Nat} (t : Tm Head n) {ρ : Ren n m} (_ : Function.Injective ρ)
    {flexible : Fin n → Bool} {flexible' : Fin m → Bool} (_ : ∀ i, flexible' (ρ i) = flexible i),
    miller flexible' (Presentation.rename ρ t) = true → miller flexible t = true
  | _, _, .var _, _, _, _, _, _, _ => rfl
  | _, _, .const _, _, _, _, _, _, _ => rfl
  | _, _, .head _, _, _, _, _, _, _ => rfl
  | _, _, .pi A B, _, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨miller_rename_reflect A injective respects holds.1,
        miller_rename_reflect B (ContextualDependentPruning.liftRen_injective injective)
          (liftFlexible_respects respects) holds.2⟩
  | _, _, .sigma A B, _, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨miller_rename_reflect A injective respects holds.1,
        miller_rename_reflect B (ContextualDependentPruning.liftRen_injective injective)
          (liftFlexible_respects respects) holds.2⟩
  | _, _, .id A a b, _, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨⟨miller_rename_reflect A injective respects holds.1.1, miller_rename_reflect a injective respects holds.1.2⟩,
        miller_rename_reflect b injective respects holds.2⟩
  | _, _, .lam body, _, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller] at holds ⊢
      exact miller_rename_reflect body (ContextualDependentPruning.liftRen_injective injective)
        (liftFlexible_respects respects) holds
  | _, _, .app f a, ρ, injective, flexible, flexible', respects, holds => by
      simp only [Presentation.rename, miller, spineHead_rename, flexHead_rename ρ respects] at holds
      simp only [miller]
      split
      · rename_i flexibleSpine
        rw [if_pos flexibleSpine] at holds
        exact millerSpine_rename_reflect respects (t := .app f a) holds
      · rename_i rigidSpine
        rw [if_neg rigidSpine] at holds
        simp only [Bool.and_eq_true] at holds ⊢
        exact ⟨miller_rename_reflect f injective respects holds.1, miller_rename_reflect a injective respects holds.2⟩
  | _, _, .pair a b, _, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨miller_rename_reflect a injective respects holds.1, miller_rename_reflect b injective respects holds.2⟩
  | _, _, .fst p, ρ, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller, Bool.and_eq_true, spineHead_rename, flexHead_rename ρ respects] at holds
      simp only [miller, Bool.and_eq_true]
      exact ⟨holds.1, miller_rename_reflect p injective respects holds.2⟩
  | _, _, .snd p, ρ, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller, Bool.and_eq_true, spineHead_rename, flexHead_rename ρ respects] at holds
      simp only [miller, Bool.and_eq_true]
      exact ⟨holds.1, miller_rename_reflect p injective respects holds.2⟩
  | _, _, .refl a, _, injective, _, _, respects, holds => by
      simp only [Presentation.rename, miller] at holds ⊢
      exact miller_rename_reflect a injective respects holds

/-- **A spine prefix keeps Miller occurrences**: dropping the last variable argument. -/
theorem miller_of_app_var {n : Nat} {flexible : Fin n → Bool} {t : Tm Head n} {y : Fin n}
    (holds : miller flexible (.app t (.var y)) = true) : miller flexible t = true := by
  by_cases flexibleSpine : flexHead flexible (spineHead t) = true
  · simp only [miller, flexibleSpine, if_true] at holds
    unfold millerSpine at holds
    have unfolded : readSpine (Tm.app t (.var y)) = (readSpine t).map fun read => (read.1, y :: read.2) := rfl
    rw [unfolded] at holds
    cases read : readSpine t with
    | none => rw [read] at holds; cases holds
    | some found =>
        obtain ⟨head, arguments⟩ := found
        rw [read] at holds
        simp only [Option.map_some, Bool.and_eq_true, List.all_eq_true, List.mem_cons, forall_eq_or_imp,
          Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at holds
        obtain ⟨⟨flexibleHead, -, rigid⟩, distinct⟩ := holds
        rw [readSpine_spec read]
        exact miller_appsVar flexibleHead arguments rigid (List.nodup_cons.mp distinct).2
  · have rigidSpine : flexHead flexible (spineHead t) = false := by
      cases h : flexHead flexible (spineHead t)
      · rfl
      · exact absurd h flexibleSpine
    simp only [miller, rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true] at holds
    exact holds.1

theorem miller_of_appsFwd {n : Nat} {flexible : Fin n → Bool} :
    ∀ (more : List (Fin n)) {t : Tm Head n}, miller flexible (appsFwd t more) = true → miller flexible t = true
  | [], _, holds => holds
  | _ :: rest, _, holds => miller_of_app_var (miller_of_appsFwd rest holds)

/-! ## Opening as application to fresh locals -/

/-- Weakening past `count` locals. -/
def wkK {n : Nat} : (count : Nat) → Ren n (n + count)
  | 0 => fun i => i
  | count + 1 => fun i => (wkK count i).succ

/-- The `count` fresh locals of an opening, in application order. -/
def localsFwd {n : Nat} : (count : Nat) → List (Fin (n + count))
  | 0 => []
  | count + 1 => (localsFwd count).map Fin.succ ++ [0]

theorem wkK_val {n : Nat} : ∀ (count : Nat) (i : Fin n), (wkK count i).val = i.val + count
  | 0, _ => rfl
  | count + 1, i => by
      change (wkK count i).val + 1 = i.val + (count + 1)
      rw [wkK_val count i]
      omega

theorem wkK_injective {n : Nat} (count : Nat) : Function.Injective (wkK (n := n) count) := by
  intro i j same
  have := congrArg Fin.val same
  rw [wkK_val, wkK_val] at this
  exact Fin.ext (by omega)

theorem localsFwd_lt {n : Nat} : ∀ (count : Nat), ∀ y ∈ localsFwd (n := n) count, y.val < count
  | 0, _, member => absurd member List.not_mem_nil
  | count + 1, y, member => by
      rcases List.mem_append.mp member with early | late
      · obtain ⟨prior, inPrior, rfl⟩ := List.mem_map.mp early
        have := localsFwd_lt count prior inPrior
        simp only [Fin.val_succ]
        omega
      · rw [List.mem_singleton.mp late]
        simp

theorem localsFwd_nodup {n : Nat} : ∀ (count : Nat), (localsFwd (n := n) count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      refine List.nodup_append.mpr ⟨(localsFwd_nodup count).map (Fin.succ_injective _), List.nodup_singleton _, ?_⟩
      intro first early second late same
      rw [List.mem_singleton.mp late] at same
      obtain ⟨prior, _, rfl⟩ := List.mem_map.mp early
      exact Fin.succ_ne_zero _ same

theorem rename_appsFwd {n m : Nat} (ρ : Ren n m) :
    ∀ (more : List (Fin n)) (head : Tm Head n),
      Presentation.rename ρ (appsFwd head more) = appsFwd (Presentation.rename ρ head) (more.map ρ)
  | [], _ => rfl
  | argument :: rest, head => rename_appsFwd ρ rest (.app head (.var argument))

/-- **Opening is application to fresh locals.** -/
theorem openCode_eq_appsFwd {n : Nat} (code : Tm Head n) :
    ∀ count : Nat, openCode count code = appsFwd (Presentation.rename (wkK count) code) (localsFwd count)
  | 0 => (rename_id code).symm
  | count + 1 => by
      change Tm.app (Presentation.rename wk (openCode count code)) (.var 0) = _
      rw [openCode_eq_appsFwd code count, rename_appsFwd, rename_comp]
      change _ = appsFwd (Presentation.rename (wkK (count + 1)) code) ((localsFwd count).map Fin.succ ++ [0])
      rw [appsFwd_append_single]
      rfl

variable {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

/-- From a reduct to a normal form, every other reduct still reaches that normal form. -/
theorem star_to_normal {n : Nat} {x y N : Tm Head n} (toN : Star (R := R) x N) (normalN : Normal R N)
    (toY : Star (R := R) x y) : Star (R := R) y N := by
  obtain ⟨common, fromN, fromY⟩ := confluent empty toN toY
  rw [normalN.star_eq fromN] at fromY
  exact fromY

/-- **Miller occurrences are reflected by contraction against fresh variables.** -/
theorem collapse_reflect {m : Nat} {flexible' : Fin m → Bool} :
    ∀ (more : List (Fin m)) {o : Nat} (v : Tm Head o) (mark : Fin o → Bool) (ρ : Ren o m),
      Normal R v → Function.Injective ρ → (∀ i, flexible' (ρ i) = mark i) →
      (∀ y ∈ more, flexible' y = false) → more.Nodup → (∀ y ∈ more, ∀ i, ρ i ≠ y) →
      ∀ N, Star (R := R) (appsFwd (Presentation.rename ρ v) more) N → Normal R N → miller flexible' N = true →
        miller mark v = true
  | [], _, v, _, ρ, normal, injective, respects, _, _, _, N, toN, _, millerN => by
      have same : N = Presentation.rename ρ v :=
        ((ContextualDependentNormalizing.normal_rename_iff empty ρ v).mpr normal).star_eq toN
      rw [same] at millerN
      exact miller_rename_reflect v injective respects millerN
  | y :: rest, o, v, mark, ρ, normal, injective, respects, rigid, distinct, avoids, N, toN, normalN, millerN => by
      by_cases abstraction : ∃ body, v = .lam body
      · obtain ⟨body, rfl⟩ := abstraction
        have fresh : ∀ i, ρ i ≠ y := avoids y List.mem_cons_self
        have restRigid : ∀ other ∈ rest, flexible' other = false :=
          fun other member => rigid other (List.mem_cons_of_mem _ member)
        have restDistinct := (List.nodup_cons.mp distinct).2
        have restAvoids : ∀ other ∈ rest, ∀ i, (Fin.cases y ρ : Fin (o + 1) → Fin m) i ≠ other := by
          intro other member i
          refine Fin.cases ?_ (fun prior => ?_) i
          · intro same
            change y = other at same
            exact (List.nodup_cons.mp distinct).1 (by rw [same]; exact member)
          · exact avoids other (List.mem_cons_of_mem _ member) prior
        have consRespects : ∀ i, flexible' ((Fin.cases y ρ : Fin (o + 1) → Fin m) i) = liftFlexible mark i := by
          intro i
          refine Fin.cases ?_ (fun prior => ?_) i
          · exact rigid y List.mem_cons_self
          · exact respects prior
        have contracted : Star (R := R) (.app (.lam (Presentation.rename (liftRen ρ) body)) (.var y))
            (Presentation.rename (Fin.cases y ρ) body) := by
          rw [← inst0_var_rename_liftRen]
          exact Relation.ReflTransGen.single (.betaPi _ _)
        have reaches := star_to_normal empty toN normalN (star_appsFwd rest contracted)
        have inner := collapse_reflect rest body (liftFlexible mark) (Fin.cases y ρ) ((normal_lam_iff empty).mp normal)
          (cons_injective injective fresh) consRespects restRigid restDistinct restAvoids N reaches normalN millerN
        simp only [miller]
        exact inner
      · have notLam : isLam v = false := by
          cases v with
          | lam body => exact absurd ⟨body, rfl⟩ abstraction
          | var _ | const _ | head _ | pi _ _ | sigma _ _ | id _ _ _ | app _ _ | pair _ _ | fst _ | snd _
          | refl _ => rfl
        have normalSpine := normal_appsFwd empty (y :: rest)
          ((ContextualDependentNormalizing.normal_rename_iff empty ρ v).mpr normal) (by rw [isLam_rename]; exact notLam)
        have same : N = appsFwd (Presentation.rename ρ v) (y :: rest) := (normalSpine.star_eq toN)
        rw [same] at millerN
        exact miller_rename_reflect v injective respects (miller_of_appsFwd (y :: rest) millerN)

/-- Contracting a normal term against variables reaches a normal form. -/
theorem collapse_normal {m : Nat} :
    ∀ (more : List (Fin m)) {o : Nat} (v : Tm Head o) (ρ : Ren o m), Normal R v →
      ∃ t', Star (R := R) (appsFwd (Presentation.rename ρ v) more) t' ∧ Normal R t'
  | [], _, v, ρ, normal =>
      ⟨Presentation.rename ρ v, .refl, (ContextualDependentNormalizing.normal_rename_iff empty ρ v).mpr normal⟩
  | y :: rest, o, v, ρ, normal => by
      by_cases abstraction : ∃ body, v = .lam body
      · obtain ⟨body, rfl⟩ := abstraction
        obtain ⟨t', steps, normal'⟩ := collapse_normal rest body (Fin.cases y ρ) ((normal_lam_iff empty).mp normal)
        refine ⟨t', ?_, normal'⟩
        have contracted : Star (R := R) (.app (.lam (Presentation.rename (liftRen ρ) body)) (.var y))
            (Presentation.rename (Fin.cases y ρ) body) := by
          rw [← inst0_var_rename_liftRen]
          exact Relation.ReflTransGen.single (.betaPi _ _)
        exact (star_appsFwd rest contracted).trans steps
      · have notLam : isLam v = false := by
          cases v with
          | lam body => exact absurd ⟨body, rfl⟩ abstraction
          | var _ | const _ | head _ | pi _ _ | sigma _ _ | id _ _ _ | app _ _ | pair _ _ | fst _ | snd _
          | refl _ => rfl
        exact ⟨_, .refl, normal_appsFwd empty (y :: rest)
          ((ContextualDependentNormalizing.normal_rename_iff empty ρ v).mpr normal) (by rw [isLam_rename]; exact notLam)⟩

/-- **A normal code opens to a normal form at every depth.** -/
theorem opens_normal {n : Nat} {code : Tm Head n} (normal : Normal R code) (count : Nat) :
    ∃ N, Star (R := R) (openCode count code) N ∧ Normal R N := by
  rw [openCode_eq_appsFwd]
  exact collapse_normal empty (localsFwd count) code (wkK count) normal

/-- **A normal code whose opening has a Miller normal form is a closed Miller code.** -/
theorem closed_of_sides {n : Nat} {code : Tm Head n} (normal : Normal R code) (count : Nat) {N : Tm Head (n + count)}
    (toN : Star (R := R) (openCode count code) N) (normalN : Normal R N)
    (millerN : miller (openedFlexible count) N = true) : miller (fun _ => true) code = true := by
  rw [openCode_eq_appsFwd] at toN
  exact collapse_reflect empty (localsFwd count) code (fun _ => true) (wkK count) normal (wkK_injective count)
    (fun i => by simp [openedFlexible, wkK_val])
    (fun y member => by
      have := localsFwd_lt count y member
      simp [openedFlexible]
      omega)
    (localsFwd_nodup count)
    (fun y member i same => by
      have small := localsFwd_lt count y member
      rw [← same, wkK_val] at small
      omega)
    N toN normalN millerN

end Raw

section Equations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

/-- **On normal codes, Miller sides are the closed Miller check on the two codes**, whatever the opening depth. -/
theorem fragmentSidesMiller_iff_closed (empty : rules.computation = RootComputation.empty) {Θ : Context rules}
    {equation : Equation (TotalTerm Θ)} (normalLeft : Normal rules equation.1.2.code)
    (normalRight : Normal rules equation.2.2.code) :
    FragmentSidesMiller equation ↔
      miller (fun _ => true) equation.1.2.code = true ∧ miller (fun _ => true) equation.2.2.code = true := by
  constructor
  · intro sides
    obtain ⟨N, toN, normalN⟩ := opens_normal empty normalLeft (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
    obtain ⟨M, toM, normalM⟩ := opens_normal empty normalRight (ContextualDependentPatternSolver.lamDepth equation.1.2.code)
    exact ⟨closed_of_sides empty normalLeft _ toN normalN (sides.1 N toN normalN),
      closed_of_sides empty normalRight _ toM normalM (sides.2 M toM normalM)⟩
  · rintro ⟨closedLeft, closedRight⟩
    exact fragmentSidesMiller_of_closed empty normalLeft normalRight closedLeft closedRight

end Equations

/-! ## Decomposition of formers under abstractions keeps the Miller class -/

section Splice

open ContextualDependentSpinesMany ContextualDependentRigidFormers

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [∀ head, Decidable (S.R.isUniverse head)]

/-- The four codes of an equation, as a piece. -/
def codePiece {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Piece Head Θ.arity :=
  ⟨equation.1.1.code, equation.1.2.code, equation.2.1.code, equation.2.2.code⟩

/-- **Replacing a normal equation between formers under abstractions by its pieces keeps the Miller class**: any
store of equations whose codes are the pieces of `underParts` and whose solutions are the equation's. The pieces have
Miller sides because the equation's codes are closed Miller codes (`fragmentSidesMiller_iff_closed`,
`underParts_closed`), and they are stratified among themselves (`underParts_internal`). -/
theorem StratifiedMiller.splice_underParts (empty : S.R.computation = RootComputation.empty)
    (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R) {Θ : Context S.R}
    {before after : EquationStore (TotalTerm Θ)} {equation : Equation (TotalTerm Θ)}
    (stratified : StratifiedMiller S.levels (before ++ equation :: after)) {pieces : List (Piece Head Θ.arity)}
    (found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (normalLeft : Normal S.R equation.1.2.code) (normalRight : Normal S.R equation.2.2.code)
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    StratifiedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have sidesEquation := (stratified before after equation rfl).1
  have closed := (fragmentSidesMiller_iff_closed empty normalLeft normalRight).mp sidesEquation
  have closedPieces := underParts_closed empty _ _ _ (fun _ => true) found ⟨normalLeft, closed.1⟩
    ⟨normalRight, closed.2⟩
  refine StratifiedMiller.splice stratified exact ?_ ?_
  · intro piece member
    have inPieces : codePiece piece ∈ pieces := by
      rw [← codes]
      exact List.mem_map_of_mem member
    obtain ⟨closedLeft, closedRight⟩ := closedPieces _ inPieces
    exact fragmentSidesMiller_of_closed empty closedLeft.1 closedRight.1 closedLeft.2 closedRight.2
  · intro first last piece split Δ σ solved
    rw [models_append_iff] at solved
    have pieceSplit : pieces = first.map codePiece ++ codePiece piece :: last.map codePiece := by
      rw [← codes, split]
      simp
    exact underParts_internal facts algebra _ _ _ found σ.substitution Δ.formed (equation.1.1.reindex σ).isType
      (first.map codePiece) (last.map codePiece) (codePiece piece) pieceSplit (fun q member => by
        obtain ⟨original, inFirst, rfl⟩ := List.mem_map.mp member
        exact (solves_raw σ original).mp (solved.2 original inFirst))

end Splice

end ContextualDependentShortClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
