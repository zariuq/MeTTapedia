import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureAny

/-!
# Closure of the cumulative round: decomposition between spines of one local

R99's decomposition between spines of one local (`spineWeighed`) reads `λ z̄. x ā ≐ λ z̄. x b̄` for a local `x` of the
abstractions (`dependentUnder`) and replaces the equation by the argument pieces `λ z̄. aᵢ ≐ λ z̄. bᵢ`, each at the
domain of `x`'s type instantiated at the arguments before it, on its own side (`argParts`).

* **Reducts.** A reduct of a spine of a variable is a spine of that variable with reducts of the arguments, and a
  normal Miller spine of a rigid variable has normal Miller arguments, so the pieces have Miller normal reducts when the
  sides do (`MarkedReduct.of_spine`, `dependentUnder_reducts`), the locals being rigid.
* **Stratification.** Once the pieces before it hold, a piece's two domains are equal types: the two telescopes start
  from the one type of `x`, and equal arguments instantiate equal codomains to equal types (`argParts_internal`,
  `dependentUnder_internal`), at every substitution into every formed context (`dependentUnder_subst`).

So the decomposition keeps the permuted class (`spineWeighed_keeps`), and with R94's former decomposition and the
decomposition under abstractions so does R99's committed decomposition (`decomposeAny_keeps_permuted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentSpinesMany ContextualDependentRigidFormers
open ContextualDependentClosure
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Reducts of rigid spines -/

section Reducts

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)

omit empty in
theorem elim_appSpine {n : Nat} : ∀ (as : List (Tm Head n)) {f : Tm Head n}, Elim f → Elim (appSpine f as)
  | [], _, rigid => rigid
  | _ :: as, _, rigid => elim_appSpine as (Elim.app rigid)

omit empty in
theorem spineHead_appSpine {n : Nat} (h : Fin n) :
    ∀ (as : List (Tm Head n)) {f : Tm Head n}, spineHead f = .var h → spineHead (appSpine f as) = .var h
  | [], _, head => head
  | a :: as, f, head => spineHead_appSpine h as (f := .app f a) head

include empty

/-- **A step keeps the head of a spine of a variable.** -/
theorem spineHead_step {n : Nat} {h : Fin n} :
    ∀ {f f' : Tm Head n}, spineHead f = .var h → StrongNormalization.Reduces R f f' → spineHead f' = .var h
  | .var _, _, _, step => by
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
  | .app g b, _, head, step => by
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | betaPi body _ => cases head
      | congAppFun inner =>
          have inside := spineHead_step (f := g) head inner
          exact inside
      | congAppArg _ => exact head
  | .const _, _, head, _ | .head _, _, head, _ | .pi _ _, _, head, _ | .sigma _ _, _, head, _
  | .id _ _ _, _, head, _ | .lam _, _, head, _ | .pair _ _, _, head, _ | .fst _, _, head, _
  | .snd _, _, head, _ | .refl _, _, head, _ => by cases head

theorem spineHead_star {n : Nat} {h : Fin n} {f f' : Tm Head n} (head : spineHead f = .var h)
    (steps : Star (R := R) f f') : spineHead f' = .var h := by
  induction steps with
  | refl => exact head
  | tail _ step ih => exact spineHead_step empty ih step

/-- **The arguments of a spine of a rigid variable have Miller normal reducts** when the spine does. -/
theorem MarkedReduct.of_spine {n : Nat} {mark : Fin n → Bool} (h : Fin n) (rigidHead : mark h = false) :
    ∀ as : List (Tm Head n), MarkedReduct R mark (appSpine (.var h) as) → ∀ a ∈ as, MarkedReduct R mark a := by
  intro as
  induction as using List.reverseRecOn with
  | nil => intro _ a member; cases member
  | append_singleton as a ih =>
      intro outer b member
      rw [appSpine_concat] at outer
      obtain ⟨X, toX, normalX, millerX⟩ := outer
      obtain ⟨f', a', rfl, toF, toA, _⟩ := star_app_inv empty (elim_appSpine as (Elim.var h)) toX
      obtain ⟨_, normalF, normalA⟩ := (normal_app_iff empty).mp normalX
      have headF : spineHead f' = .var h := spineHead_star empty (spineHead_appSpine h as rfl) toF
      have rigidF : flexHead mark (spineHead f') = false := by
        rw [headF]
        exact rigidHead
      obtain ⟨millerF, millerA⟩ := decompose_app rigidF millerX
      rcases List.mem_append.mp member with inner | last
      · exact ih ⟨f', toF, normalF, millerF⟩ b inner
      · rw [List.mem_singleton.mp last]
        exact ⟨a', toA, normalA, millerA⟩

end Reducts

section Pieces

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The pieces of spines of one local have Miller normal reducts** when the two sides do, the locals rigid. -/
theorem dependentUnder_reducts (empty : S.R.computation = RootComputation.empty) :
    ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n) {pieces : List (Piece Head n)}
      (mark : Fin n → Bool), (∀ j : Fin n, j.val < locals.length → mark j = false) →
      dependentUnder locals annotation left right = some pieces →
      MarkedReduct S.R mark left → MarkedReduct S.R mark right →
      ∀ piece ∈ pieces, MarkedReduct S.R mark piece.left ∧ MarkedReduct S.R mark piece.right := by
  intro n locals annotation left right pieces mark localsRigid found leftReduct rightReduct
  rcases dependentUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · have lifted : ∀ j : Fin (n + 1),
        j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
          liftFlexible mark j = false := by
      intro j
      refine Fin.cases (motive := fun j : Fin (n + 1) =>
        j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
          liftFlexible mark j = false) ?_ (fun j small => ?_) j
      · intro _
        rfl
      · change mark j = false
        simp only [List.length_cons, List.length_map, Fin.val_succ] at small
        exact localsRigid j (by omega)
    intro piece member
    obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
    obtain ⟨pl, pr⟩ := dependentUnder_reducts empty _ T l r (liftFlexible mark) lifted computed
      (MarkedReduct.of_lam empty leftReduct) (MarkedReduct.of_lam empty rightReduct) original inInner
    exact ⟨MarkedReduct.lam empty pl, MarkedReduct.lam empty pr⟩
  · obtain ⟨h, as, bs, T, _, rfl, rfl, small, _, _, read⟩ := dependentBase_spec base
    obtain ⟨sameL, sameR⟩ := argParts_sides as bs read
    have rigidHead := localsRigid h small
    intro piece member
    refine ⟨MarkedReduct.of_spine empty h rigidHead as leftReduct _ ?_,
      MarkedReduct.of_spine empty h rigidHead bs rightReduct _ ?_⟩
    · rw [← sameL]
      exact List.mem_map_of_mem member
    · rw [← sameR]
      exact List.mem_map_of_mem member

variable (facts : FormFacts S.R S.roles)
include facts

/-- **Along two telescopes with equal types, the domains of a piece are equal types once the pieces before it
hold.** -/
theorem argParts_internal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (as bs : List (Tm Head n)) {TL TR : Tm Head n} {pieces : List (Piece Head n)},
      argParts TL TR as bs = some pieces → TypeEq S.R Γ TL TR → IsType S.R Γ TL → IsType S.R Γ TR →
      (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
        (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType
  | [], bs, _, _, pieces, found, _, _, _, _, first, last, piece, split, _ => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      exact absurd split.symm (by simp)
  | _ :: _, [], _, _, _, found, _, _, _, _, _, _, _, _, _ => (argParts_right_nil found).elim
  | a :: as, b :: bs, TL, TR, pieces, found, types, isL, isR, typed, first, last, piece, split, held => by
      obtain ⟨DL, EL, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      obtain ⟨domains, codomains⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp types
      rcases first with _ | ⟨one, first⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, -⟩ := split
        exact domains
      · simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, split⟩ := split
        obtain ⟨ta, tb⟩ := typed _ List.mem_cons_self
        have firsts : Equal S.R Γ a b DL := (held _ List.mem_cons_self).2
        obtain ⟨_, ⟨v, hv, tEL⟩⟩ := IsType.pi_parts isL
        obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts isR
        have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domains)
        have nextTypes : TypeEq S.R Γ (inst0 a EL) (inst0 b ER) :=
          TypeEq.trans S.levels (TypeEq.instantiate codomains ta) (TypeEq.of_instantiateEq tER' hv' ta firsts)
        have nextL : IsType S.R Γ (inst0 a EL) := ⟨v, hv, Typed.instantiate tEL ta⟩
        have nextR : IsType S.R Γ (inst0 b ER) := ⟨v', hv', Typed.instantiate tER tb⟩
        exact argParts_internal formed as bs computed nextTypes nextL nextR
          (fun other member => typed other (List.mem_cons_of_mem _ member)) first last piece split
          (fun q member => held q (List.mem_cons_of_mem _ member))

theorem dependentBase_internal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : dependentBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
      (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  have typed := dependentBase_typed facts formed types found tl tr
  obtain ⟨h, as, bs, T, _, rfl, rfl, _, _, looked, read⟩ := dependentBase_spec found
  have headType := types.head looked
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typedVar : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typedVar
  have isT := Typed.isType th formed
  exact argParts_internal facts formed as bs read isT.refl isT isT typed

/-- **The pieces of spines of one local under abstractions are stratified among themselves.** -/
theorem dependentUnder_internal : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    dependentUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
      (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  intro n locals annotation left right Γ pieces formed types found tl tr first last piece split held
  rcases dependentUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
    have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
    have formedD := formed.snoc isD
    have tl' := Typed.lam_inv facts tl formed
    have tr' := Typed.lam_inv facts tr formed
    have typed := dependentUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
    obtain ⟨first', rest', innerSplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
    obtain ⟨piece', last', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
    have held' : ∀ q ∈ first', q.Holds S.R (.snoc Γ D) := fun q member =>
      (Piece.holds_under facts formed isD (typed q (by rw [innerSplit]; exact List.mem_append_left _ member))).mp
        (held (q.under D) (List.mem_map.mpr ⟨q, member, rfl⟩))
    have below := dependentUnder_internal _ T l r formedD (types.under D) computed tl' tr' first' last' piece'
      innerSplit held'
    exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr ⟨isD.refl, below⟩
  · exact dependentBase_internal facts formed types base tl tr first last piece split held

end Pieces

/-! ## Replacing an equation by the pieces of spines of one local -/

section Splice

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Replacing an equation between spines of one local by its pieces keeps the Miller class** on a strongly
normalizing package, at any position. -/
theorem StratifiedMiller.splice_spine (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (facts : FormFacts S.R S.roles)
    {Θ : Context S.R} {before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : StratifiedMiller S.levels (before ++ equation :: after))
    (same : equation.2.1.code = equation.1.1.code) {pieces : List (Piece Head Θ.arity)}
    (found : dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    StratifiedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have empty := computation_empty rigid
  obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (stratified before after equation rfl).1
  have reducts := dependentUnder_reducts empty [] _ _ _ (fun _ => true)
    (fun _ small => absurd small (Nat.not_lt_zero _)) found leftReduct rightReduct
  refine StratifiedMiller.splice stratified exact ?_ ?_
  · intro piece member
    have inPieces : codePiece piece ∈ pieces := by
      rw [← codes]
      exact List.mem_map_of_mem member
    obtain ⟨pieceLeft, pieceRight⟩ := reducts _ inPieces
    exact sides_of_reducts empty pieceLeft pieceRight
  · intro first last piece split Δ σ solved
    rw [models_append_iff] at solved
    have pieceSplit : pieces = first.map codePiece ++ codePiece piece :: last.map codePiece := by
      rw [← codes, split]
      simp
    have tl := equation.1.2.typed.substitute σ.typed
    have tr := equation.2.2.typed.substitute σ.typed
    rw [same] at tr
    have read := dependentUnder_subst [] _ _ _ found σ.substitution
      (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
    rw [List.map_nil] at read
    exact dependentUnder_internal facts [] _ _ _ Δ.formed (LocalTypes.nil _) read tl tr
      ((first.map codePiece).map (Piece.subst σ.substitution))
      ((last.map codePiece).map (Piece.subst σ.substitution)) ((codePiece piece).subst σ.substitution)
      (by rw [pieceSplit]; simp)
      (fun q member => by
        obtain ⟨q', inFirst, rfl⟩ := List.mem_map.mp member
        obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inFirst
        exact (solves_raw σ original).mp (solved.2 original inOriginal))

/-- **Replacing an equation between spines of one local by its pieces keeps the permuted class** at every
position. -/
theorem PermutedMiller.splice_spine (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (facts : FormFacts S.R S.roles)
    {Θ : Context S.R} {before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (permuted : PermutedMiller S.levels (before ++ equation :: after))
    (same : equation.2.1.code = equation.1.1.code) {pieces : List (Piece Head Θ.arity)}
    (found : dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    PermutedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have front : PermutedMiller S.levels (equation :: (before ++ after)) := permuted.perm List.perm_middle
  have spliced := front.splice_of (pieces := pieceEquations) fun _ _ stratified =>
    StratifiedMiller.splice_spine rigid sn facts stratified same found pieceEquations codes exact
  exact spliced.perm (by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right after)

end Splice

/-! ## The decomposition between spines of one local -/

section Rule

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **The decomposition between spines of one local has one annotation and the codes of `dependentUnder`.** -/
theorem spineWeighed_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : spineWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code =
        some (weighed.val.val.map codePiece) := by
  unfold spineWeighed at found
  split at found
  · rename_i same
    split at found
    · rename_i pieces computed
      obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp found
      refine ⟨same, computed.trans ?_⟩
      exact congrArg some (formPieces_codes facts roots heads algebra rigid complete declared choices reducer fuel
        pieces _ formed).symm
    · cases found
  · cases found

/-- **R99's decomposition between spines of one local keeps the class** on a strongly normalizing package. -/
theorem spineWeighed_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (spineWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, codes⟩ := spineWeighed_codes facts roots heads algebra rigid complete declared choices reducer fuel
    found
  exact PermutedMiller.splice_spine rigid sn facts permuted same codes weighed.val.val rfl
    fun σ => (weighed.val.property σ).symm

/-- **R99's committed decomposition keeps the permuted class** on a strongly normalizing package. -/
theorem decomposeAny_keeps_permuted (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem) :
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (ContextualDependentSpinesMany.decomposeAny facts roots heads algebra rigid complete declared choices reducer
        fuel problem) :=
  decomposeAny_keeps_of_spine facts roots heads algebra rigid complete declared choices reducer sn fuel
    (fun equation => spineWeighed_keeps facts roots heads algebra rigid complete declared choices reducer sn fuel
      equation)
    problem permuted

end Rule

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
