import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbDecided
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrows

/-!
# One rank for the rules of the Miller solver and of the solver of arrow codes

**The rank** (`commonRank`): the weight of a store (the arities, plus one, of the unknowns occurring in its sides),
then its size (the nodes of its sides). It is a pair of numbers, ordered lexicographically: the rank type of the tree's
driver.

* **Every Miller round lowers it**, on every store (`millerGlbRound_commonRank`). A deletion removes an equation, hence
  nodes, and keeps the occurring unknowns among the earlier ones. Every other step re-reads the whole store, so the
  number of equations stays the same, and the Miller rank (weight, equations) then forces the weight down.
* **Every round of the solver of arrow codes lowers it on that solver's fragment** (`arrowCodRound_commonRank`). There
  every occurring unknown is declared at a universe, a family of no parameters, so the weight is the number of
  occurring unknowns (`weight_eq_count`), and that solver's rank (unknowns, size) is this rank.
* **Permutations keep it** (`commonRank_perm`) and keep the solutions (`equivalent_perm`).
* **Rounds carried between ranks** (`retarget`): a round whose every progress lowers a second rank is a round of the
  second rank; **rounds carried along an equivalence of stores of one rank** (`transport`).

The Miller rank counts equations, which a decomposition of arrow codes raises, so it is not a rank of the arrow
solver. The rank here is not a sum indexed by the solver: it is one occurrence count with one size, and both solvers
lower it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentOccursCheck (nodes)

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## The rank -/

section Rank

variable {S : Setting Head L}

/-- **The common rank**: the weight (the occurring unknowns, each counted with its arity plus one), then the size. -/
def commonRank {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Nat × Nat :=
  (Miller.weight problem, storeSize problem)

/-- **Removing the first equation lowers the rank.** -/
theorem commonRank_drop {Γ : Context S.R} (e : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ)) :
    Below (commonRank rest) (commonRank (e :: rest)) := by
  refine below_of_le_lt (Finset.sum_le_sum_of_subset fun v h => Finset.mem_union_right _ h) ?_
  have := nodes_pos e.1.2.code
  simp only [storeSize]
  omega

/-- **A store with as many equations and a lower Miller rank has a lower rank.** -/
theorem commonRank_of_millerRank {Γ Γ' : Context S.R} {P : EquationStore (TotalTerm Γ)}
    {Q : EquationStore (TotalTerm Γ')} (smaller : Below (Miller.millerRank Q) (Miller.millerRank P))
    (same : Q.length = P.length) : Below (commonRank Q) (commonRank P) := by
  unfold ContextualDependentWorklist.Below Miller.millerRank at smaller
  rcases Prod.lex_def.mp smaller with lt | ⟨_, lt⟩
  · exact Prod.Lex.left _ _ lt
  · exact absurd lt (by simp only [same]; exact Nat.lt_irrefl _)

/-- Permuting a store keeps the unknowns occurring in it. -/
theorem occ_perm {Γ : Context S.R} {P Q : EquationStore (TotalTerm Γ)} (perm : P.Perm Q) :
    Miller.occ P = Miller.occ Q := by
  ext v
  rw [Miller.mem_occ, Miller.mem_occ]
  exact ⟨fun ⟨e, m, h⟩ => ⟨e, perm.mem_iff.mp m, h⟩, fun ⟨e, m, h⟩ => ⟨e, perm.mem_iff.mpr m, h⟩⟩

theorem storeSize_perm {Γ : Context S.R} {P Q : EquationStore (TotalTerm Γ)} (perm : P.Perm Q) :
    storeSize P = storeSize Q := by
  induction perm with
  | nil => rfl
  | cons x _ ih => simp only [storeSize, ih]
  | swap x y l => simp only [storeSize]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Permutations keep the rank.** -/
theorem commonRank_perm {Γ : Context S.R} {P Q : EquationStore (TotalTerm Γ)} (perm : P.Perm Q) :
    commonRank P = commonRank Q := by
  unfold commonRank Miller.weight
  rw [occ_perm perm, storeSize_perm perm]

/-- Transport keeps the number of equations. -/
theorem applyStore_length {Γ Δ : Context S.R} (f : Δ ⟶ Γ) (problem : EquationStore (TotalTerm Γ)) :
    ((frames S.levels).applyStore f problem).length = problem.length :=
  List.length_map ..

/-- **Permutations keep the solutions.** -/
theorem equivalent_perm {Γ : Context S.R} {P Q : EquationStore (TotalTerm Γ)} (perm : P.Perm Q) :
    (frames S.levels).Equivalent P Q :=
  fun _ _ => ⟨fun solved e member => solved e (perm.mem_iff.mpr member),
    fun solved e member => solved e (perm.mem_iff.mp member)⟩

end Rank

/-! ## Every Miller round lowers the rank -/

namespace Miller

section MillerRounds

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- Re-reading keeps the number of equations. -/
theorem rereadStore_length {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ)
    (problem : EquationStore (TotalTerm Θ)) : (rereadStore A problem).length = problem.length :=
  List.length_map ..

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem stepLocals_commonRank {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {v : EqView (S := S) e} {l m : Fin v.qs.length} {sl : e.1.2.code = localSide v.qs l}
    {bl : S.R.cumulative (v.qs.get l) v.d} {sm : e.2.2.code = localSide v.qs m}
    {bm : S.R.cumulative (v.qs.get m) v.d}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (progressed : stepLocals rigid complete rest v l m sl bl sm bm = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank (e :: rest)) := by
  unfold stepLocals at progressed
  split at progressed
  · cases progressed
    exact commonRank_drop e rest
  · cases progressed

theorem stepFlexLocal_commonRank {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {qs : List Head} {d : Head} {universes : AllUniverses S.R qs} {hd : S.R.isUniverse d}
    {X : Fin Θ.arity} {ps : List Head} {c : Head} {img : Fin ps.length → Fin qs.length}
    {declared : Ctx.lookup Θ.raw X = famCode ps c} {injective : Function.Injective img}
    {domains : ∀ j, ps.get j = qs.get (img j)} {below : S.R.cumulative c d} {l : Fin qs.length}
    {occurs : X ∈ occ (e :: rest)}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (progressed : stepFlexLocal facts roots heads algebra rigid complete inh rest families universes hd img declared
      injective domains below l occurs opens = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank (e :: rest)) := by
  unfold stepFlexLocal at progressed
  split at progressed
  · split at progressed
    · cases progressed
      exact commonRank_of_millerRank smaller (List.length_map ..)
    · cases progressed
  · cases progressed

theorem solveRound_commonRank {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {qs : List Head} {d : Head} {universes : AllUniverses S.R qs} {hd : S.R.isUniverse d}
    {X Y : Fin Θ.arity} {psX psY : List Head} {cX cY : Head} {imgX : Fin psX.length → Fin qs.length}
    {imgY : Fin psY.length → Fin qs.length} {declX : Ctx.lookup Θ.raw X = famCode psX cX}
    {declY : Ctx.lookup Θ.raw Y = famCode psY cY} {injX : Function.Injective imgX}
    {injY : Function.Injective imgY}
    {domX : ∀ j, psX.get j = qs.get (imgX j)} {domY : ∀ j, psY.get j = qs.get (imgY j)}
    {belowX : S.R.cumulative cX d} {ne : Y ≠ X} {cover : ∀ i, ∃ j, imgX j = imgY i}
    {codomains : S.R.cumulative cY cX} {occX : X ∈ occ (e :: rest)} {occY : Y ∈ occ (e :: rest)}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psY imgY) (opened psY (f.substitution Y)))
        (Presentation.rename (sideRen qs psX imgX) (opened psX (f.substitution X))) (.head d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (progressed : solveRound facts roots heads algebra rigid complete inh rest families universes hd imgX imgY declX
      declY injX injY domX domY belowX ne cover codomains occX occY opens = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank (e :: rest)) := by
  unfold solveRound at progressed
  cases progressed
  exact commonRank_of_millerRank smaller (List.length_map ..)

theorem stepFlexFlex_commonRank {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (progressed : stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂
      opens = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank (e :: rest)) := by
  unfold stepFlexFlex at progressed
  split_ifs at progressed with hcode hF hcov₁ hcov₂ hc hc'
  · cases progressed
    exact commonRank_drop e rest
  · unfold pruneRound at progressed
    cases progressed
    exact commonRank_of_millerRank smaller (List.length_map ..)
  · exact solveRound_commonRank facts roots heads algebra rigid complete inh progressed
  · exact solveRound_commonRank facts roots heads algebra rigid complete inh
      (opens := fun f solved => (opens f solved).symm) progressed
  · unfold pruneRound at progressed
    cases progressed
    exact commonRank_of_millerRank smaller (List.length_map ..)
  · unfold pruneRound at progressed
    cases progressed
    exact commonRank_of_millerRank smaller (List.length_map ..)

theorem stepView_commonRank {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (progressed : stepView facts roots heads algebra rigid complete normalizes inh rest families v =
      .progress update smaller) :
    Below (commonRank update.remaining) (commonRank (e :: rest)) := by
  unfold stepView at progressed
  split at progressed
  · exact stepLocals_commonRank rigid complete progressed
  · exact stepFlexLocal_commonRank facts roots heads algebra rigid complete inh progressed
  · exact stepFlexLocal_commonRank facts roots heads algebra rigid complete inh progressed
  · exact stepFlexFlex_commonRank facts roots heads algebra rigid complete normalizes inh progressed

theorem glbSolveRound_commonRank {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {hl : v.left = .flex D₁ b₁} {hr : v.right = .flex D₂ b₂} {g : Head} {isGlb : IsGlb S.R g D₁.c D₂.c}
    {ne : D₁.unknown ≠ D₂.unknown} {cover : ∀ i, ∃ j, D₂.img j = D₁.img i}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (progressed : glbSolveRound facts roots heads algebra rigid complete inh headTypingUnique rest families v D₁ b₁
      D₂ b₂ hl hr isGlb ne cover = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank (e :: rest)) := by
  unfold glbSolveRound at progressed
  obtain ⟨u, s, solved, rfl⟩ := roundAfter_progress _ _ progressed
  unfold solveRound at solved
  cases solved
  refine commonRank_of_millerRank smaller ((rereadStore_length _ _).trans ?_)
  simp only [List.length_cons, applyStore_length]

theorem stepViewGlb_commonRank {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (progressed : stepViewGlb facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec rest
      families v = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank (e :: rest)) := by
  unfold stepViewGlb at progressed
  split at progressed
  · split at progressed
    · split at progressed
      · exact glbSolveRound_commonRank facts roots heads algebra rigid complete inh headTypingUnique progressed
      · cases progressed
    · exact stepView_commonRank facts roots heads algebra rigid complete normalizes inh progressed
  · exact stepView_commonRank facts roots heads algebra rigid complete normalizes inh progressed

/-- **Every round of the Miller solver lowers the common rank**, on every store. -/
theorem millerGlbRound_commonRank {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem} {smaller : Below (millerRank update.remaining) (millerRank problem)}
    (progressed : millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
      problem = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank problem) := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [millerGlbRound] at progressed
      split at progressed
      · split at progressed
        · exact stepViewGlb_commonRank facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
            progressed
        · cases progressed
      · cases progressed

end MillerRounds

end Miller

/-! ## Every round of the solver of arrow codes lowers the rank on its fragment -/

section ArrowRounds

variable {S : Setting Head L}

/-- A universe is a family of no parameters. -/
theorem famArity_head {n : Nat} (w : Head) : Miller.famArity (Tm.head w : Tm Head n) = 0 := rfl

theorem occursCod_iff {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) (i : Fin Γ.arity) :
    occursCod problem i = true ↔ i ∈ Miller.occ problem := by
  rw [Miller.mem_occ]
  simp [occursCod, List.any_eq_true]

/-- **Where every occurring unknown is declared at a universe, the weight counts the occurring unknowns.** -/
theorem weight_eq_count {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (occurring : ∀ e ∈ problem, AtUniverses (S := S) Γ.raw e.1.2.code ∧ AtUniverses (S := S) Γ.raw e.2.2.code) :
    Miller.weight problem = ((List.finRange Γ.arity).filter (occursCod problem)).length := by
  have arities : ∀ i ∈ Miller.occ problem, Miller.famArity (Ctx.lookup Γ.raw i) + 1 = 1 := by
    intro i member
    obtain ⟨e, eMember, side⟩ := Miller.mem_occ.mp member
    obtain ⟨w, hw, _⟩ : ∃ w, Ctx.lookup Γ.raw i = .head w ∧ S.R.isUniverse w := by
      rcases side with h | h
      · exact (occurring e eMember).1 i h
      · exact (occurring e eMember).2 i h
    rw [hw, famArity_head]
  unfold Miller.weight
  rw [Finset.sum_congr rfl arities, Finset.sum_const, smul_eq_mul, mul_one]
  have nodup : ((List.finRange Γ.arity).filter (occursCod problem)).Nodup := (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup nodup]
  congr 1
  ext i
  simp [occursCod_iff]

/-- On the fragment of arrow codes the common rank is the arrow solver's rank. -/
theorem commonRank_eq_codRank {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (occurring : ∀ e ∈ problem, AtUniverses (S := S) Γ.raw e.1.2.code ∧ AtUniverses (S := S) Γ.raw e.2.2.code) :
    commonRank problem = codRank problem := by
  unfold commonRank codRank
  rw [weight_eq_count occurring]

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)

/-- **Every round of the solver of arrow codes lowers the common rank** on its fragment. -/
theorem arrowCodRound_commonRank {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : Below (codRank update.remaining) (codRank problem)}
    (inside : InArrowsCod choices problem)
    (progressed : arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening problem = .progress update smaller) :
    Below (commonRank update.remaining) (commonRank problem) := by
  have after := arrowCodRound_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique
    declared strengthening inside progressed
  rw [commonRank_eq_codRank inside.occurring, commonRank_eq_codRank after.occurring]
  exact smaller

end ArrowRounds

/-! ## Rounds between ranks, and along equivalences -/

section Rounds

variable {S : Setting Head L}

/-- **A round read in a second rank**, when every progress it makes lowers that rank. -/
def retarget {rank rank' : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat} {Γ : Context S.R}
    {problem : EquationStore (TotalTerm Γ)} (r : Round S.levels rank problem)
    (lowers : ∀ (update : Update S.levels problem) (smaller : Below (rank update.remaining) (rank problem)),
      r = .progress update smaller → Below (rank' update.remaining) (rank' problem)) :
    Round S.levels rank' problem :=
  match r with
  | .progress update smaller => .progress update (lowers update smaller rfl)
  | .refuted absent => .refuted absent
  | .stuck => .stuck

theorem retarget_progress {rank rank' : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat}
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {r : Round S.levels rank problem}
    {lowers : ∀ (update : Update S.levels problem) (smaller : Below (rank update.remaining) (rank problem)),
      r = .progress update smaller → Below (rank' update.remaining) (rank' problem)}
    {update : Update S.levels problem} {smaller' : Below (rank' update.remaining) (rank' problem)}
    (progressed : retarget r lowers = .progress update smaller') :
    ∃ smaller, r = .progress update smaller := by
  cases r with
  | progress u s =>
      simp only [retarget] at progressed
      cases progressed
      exact ⟨s, rfl⟩
  | refuted _ => simp only [retarget] at progressed; cases progressed
  | stuck => simp only [retarget] at progressed; cases progressed

theorem retarget_ne_stuck {rank rank' : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat}
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {r : Round S.levels rank problem}
    {lowers : ∀ (update : Update S.levels problem) (smaller : Below (rank update.remaining) (rank problem)),
      r = .progress update smaller → Below (rank' update.remaining) (rank' problem)}
    (moving : r ≠ .stuck) : retarget r lowers ≠ .stuck := by
  cases r with
  | progress u s => simp only [retarget]; intro h; cases h
  | refuted _ => simp only [retarget]; intro h; cases h
  | stuck => exact absurd rfl moving

/-- **A round carried along an equivalence of stores of the same common rank.** -/
def transport {Γ : Context S.R} {P Q : EquationStore (TotalTerm Γ)} (same : (frames S.levels).Equivalent P Q)
    (ranks : commonRank Q = commonRank P) : Round S.levels commonRank Q → Round S.levels commonRank P
  | .progress update smaller => .progress (update.rephrase same) (by rw [← ranks]; exact smaller)
  | .refuted absent => .refuted fun ⟨Δ, f, solved⟩ => absent ⟨Δ, f, (same Δ f).mp solved⟩
  | .stuck => .stuck

theorem transport_progress {Γ : Context S.R} {P Q : EquationStore (TotalTerm Γ)}
    {same : (frames S.levels).Equivalent P Q} {ranks : commonRank Q = commonRank P}
    {r : Round S.levels commonRank Q} {update : Update S.levels P}
    {smaller : Below (commonRank update.remaining) (commonRank P)}
    (progressed : transport same ranks r = .progress update smaller) :
    ∃ inner smaller', r = .progress inner smaller' ∧ update = inner.rephrase same := by
  cases r with
  | progress inner s =>
      cases progressed
      exact ⟨inner, s, rfl, rfl⟩
  | refuted _ => cases progressed
  | stuck => cases progressed

theorem transport_ne_stuck {Γ : Context S.R} {P Q : EquationStore (TotalTerm Γ)}
    {same : (frames S.levels).Equivalent P Q} {ranks : commonRank Q = commonRank P}
    {r : Round S.levels commonRank Q} (moving : r ≠ .stuck) : transport same ranks r ≠ .stuck := by
  cases r with
  | progress _ _ => intro h; cases h
  | refuted _ => intro h; cases h
  | stuck => exact absurd rfl moving

end Rounds

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
