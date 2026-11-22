import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PatternInitiality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbDecided

/-!
# Initial solutions for Miller patterns, pruning in place included

Every solved run of the Miller solver (without the chain of codomains, `millerGlbSolver`) ends with an answer whose
trimming is the initial solution (`millerGlb_solved_initial`, `millerGlb_initial`).

* **The run invariant** (`MillerInv`): every unknown the answer mentions, and every unknown of the remaining store, is
  pattern-covered by the answer (`PatternCovered`). It holds at the start (`MillerInv.pending`).
* **Fixing and lowering keep it** (`PatternCovered.transport`, `MillerInv.lowering`): an unknown sent to itself, at the
  same domains and a codomain no higher, keeps its pattern.
* **Pruning keeps it** (`PatternCovered.pruned`): `X := λ x̄. X x_K` turns the pattern `λ ȳ. X y_L` of the answer into
  `λ ȳ. X y_{L ∘ K}` by one β-step (`reread_equal`), still a pattern because `L ∘ K` is injective.
* **A value step keeps it** (`MillerInv.answerStep`): the unknowns of the value are covered already, since they occur
  in the remaining store.
* **Every round keeps it** (`millerGlbRound_inv`), so **the driver keeps it** (`drive_inv`), and at a solved state the
  trimming theorem for patterns (`initial_of_patternTrimmed`) applies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## The invariant and its steps -/

section Invariant

variable {S : Setting Head L}

/-- **The run invariant**: every unknown the answer mentions, and every unknown of the remaining store, is
pattern-covered by the answer. -/
structure MillerInv {Γ Θ : Context S.R} (σ : Θ ⟶ Γ) (remaining : EquationStore (TotalTerm Θ)) : Prop where
  covered : ∀ j, (∃ i, j ∈ (σ.substitution i).support) → PatternCovered σ j
  occurs : ∀ j ∈ occ remaining, PatternCovered σ j

/-- **At the start**, the identity covers every unknown by its η-expansion. -/
theorem MillerInv.pending {Γ : Context S.R} (families : Families Γ) (problem : EquationStore (TotalTerm Γ)) :
    MillerInv (𝟙 Γ) problem := by
  have all : ∀ j, PatternCovered (𝟙 Γ) j := fun j => by
    obtain ⟨ps, c, dj, ups, uc⟩ := families j
    exact fixed_patternCovered (𝟙 Γ) rfl dj dj ups uc uc (S.levels.cumulative_refl uc)
  exact ⟨fun j _ => all j, fun j _ => all j⟩

/-- **An unknown sent to an unknown keeps its pattern**, when the new declaration has its domains and a codomain no
higher. -/
theorem PatternCovered.transport {Γ Θ Θ' : Context S.R} {σ : Θ ⟶ Γ}
    (trans : ∀ {u v w : Head}, S.R.cumulative u v → S.R.cumulative v w → S.R.cumulative u w)
    (τ : Θ' ⟶ Θ) {k : Fin Θ.arity} {k' : Fin Θ'.arity} (cov : PatternCovered σ k)
    (fixed : τ.substitution k = .var k')
    (decl : ∀ (ps : List Head) (c : Head), Ctx.lookup Θ.raw k = famCode ps c →
      ∃ c₀, Ctx.lookup Θ'.raw k' = famCode ps c₀ ∧ S.R.isUniverse c₀ ∧ S.R.cumulative c₀ c) :
    PatternCovered (τ ≫ σ) k' := by
  obtain ⟨i, ps, qs, c, c', K, dk, di, ups, uqs, uc, uc', below, injective, domains, eq⟩ := cov
  obtain ⟨c₀, dk', uc₀, low⟩ := decl ps c dk
  refine ⟨i, ps, qs, c₀, c', K, dk', di, ups, uqs, uc₀, uc', trans low below, injective, domains, ?_⟩
  have moved := eq.substitute τ.typed
  rw [famCode_subst, subst_flexSide, fixed] at moved
  exact moved

/-- The occurring unknowns of a tail. -/
theorem occ_tail {Θ : Context S.R} (e : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ))
    {j : Fin Θ.arity} (h : j ∈ occ rest) : j ∈ occ (e :: rest) := by
  show j ∈ e.1.2.code.support ∪ e.2.2.code.support ∪ occ rest
  exact Finset.mem_union_right _ h

/-- **Deleting the first equation keeps the invariant.** -/
theorem MillerInv.delete {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inv : MillerInv σ (e :: rest)) : MillerInv (𝟙 Θ ≫ σ) rest := by
  rw [Category.id_comp]
  exact ⟨inv.covered, fun j hj => inv.occurs j (occ_tail e rest hj)⟩

/-- **A codomain lowering keeps the invariant.** -/
theorem MillerInv.lowering {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)}
    (algebra : CumulativeAlgebra S.R) (inv : MillerInv σ R) (ℓ : CodomainLowering Θ) :
    MillerInv (ℓ.hom ≫ σ) ((frames S.levels).applyStore ℓ.hom R) := by
  have keep : ∀ k, PatternCovered σ k → PatternCovered (ℓ.hom ≫ σ) k := by
    intro k cov
    refine PatternCovered.transport algebra.trans ℓ.hom cov rfl fun ps c dk => ?_
    by_cases hk : k = ℓ.index
    · have same : Ctx.lookup Θ.raw ℓ.index = famCode ps c := hk ▸ dk
      obtain ⟨hps, hc⟩ := famCode_inj (ℓ.declared.symm.trans same)
      refine ⟨ℓ.lower, ?_, ℓ.universe_lower, by rw [← hc]; exact ℓ.below⟩
      rw [hk, ℓ.lookup_self, hps]
    · obtain ⟨_, uc⟩ := (show AllUniverses S.R ps ∧ S.R.isUniverse c from by
        obtain ⟨i, ps', qs, c₁, c', K, dk', _, ups, _, uc₁, _⟩ := cov
        obtain ⟨hps, hc⟩ := famCode_inj (dk'.symm.trans dk)
        exact ⟨hps ▸ ups, hc ▸ uc₁⟩)
      exact ⟨c, (ℓ.lookup_ne hk).trans dk, uc, S.levels.cumulative_refl uc⟩
  refine ⟨fun j ⟨i, hj⟩ => keep j (inv.covered j ⟨i, ?_⟩), fun j hj => keep j (inv.occurs j ?_)⟩
  · have hj' : j ∈ (Presentation.subst ids (σ.substitution i)).support := hj
    rw [subst_ids] at hj'
    exact hj'
  · rw [occ_lowered] at hj
    exact hj

/-- **A step that answers one unknown keeps the invariant**, when the unknowns of the value are covered after it. -/
theorem MillerInv.answerStep {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)}
    (algebra : CumulativeAlgebra S.R) (inv : MillerInv σ R) {families : Families Θ} {X : Fin Θ.arity}
    {ps' : List Head} {c' : Head} {universes' : AllUniverses S.R ps'} {hc' : S.R.isUniverse c'}
    (τ : redecl Θ families X ps' c' universes' hc' ⟶ Θ) {psX : List Head} {val : Tm Head (arity Θ.arity psX)}
    (hsub : ∀ k, τ.substitution k = answerSub X psX val k)
    (valCovered : ∀ j ∈ (lams psX val).support, PatternCovered (τ ≫ σ) j)
    (R' : EquationStore (TotalTerm (redecl Θ families X ps' c' universes' hc')))
    (occR : occ R' ⊆ (occ R).erase X ∪ (lams psX val).support) :
    MillerInv (τ ≫ σ) R' := by
  have keep : ∀ k, k ≠ X → PatternCovered σ k → PatternCovered (τ ≫ σ) k := by
    intro k ne cov
    refine PatternCovered.transport algebra.trans τ cov (by rw [hsub, answerSub_ne X psX val ne]) fun ps c dk => ?_
    obtain ⟨_, ps₁, _, c₁, _, _, dk', _, _, _, uc₁, _⟩ := cov
    obtain ⟨_, hc⟩ := famCode_inj (dk'.symm.trans dk)
    refine ⟨c, ?_, hc ▸ uc₁, S.levels.cumulative_refl (hc ▸ uc₁)⟩
    exact (lookup_setFamAt_ne Θ.raw X k ps' c' ne).trans dk
  constructor
  · rintro j ⟨i, hj⟩
    change j ∈ (Presentation.subst τ.substitution (σ.substitution i)).support at hj
    obtain ⟨k, hk, hjk⟩ := support_subst_sub _ τ.substitution hj
    by_cases hkX : k = X
    · subst hkX
      rw [hsub, answerSub_self] at hjk
      exact valCovered j hjk
    · rw [hsub, answerSub_ne X psX val hkX] at hjk
      have jk : j = k := by simpa [Tm.support] using hjk
      subst jk
      exact keep j hkX (inv.covered j ⟨i, hk⟩)
  · intro j hj
    rcases Finset.mem_union.mp (occR hj) with h | h
    · obtain ⟨ne, hR⟩ := Finset.mem_erase.mp h
      exact keep j ne (inv.occurs j hR)
    · exact valCovered j h

/-- **Pruning in place keeps a pattern**: one β-step composes the two injective maps of locals. -/
theorem PatternCovered.pruned {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} [DecidableEq Head] {families : Families Θ}
    {X : Fin Θ.arity} {psX : List Head} {cX : Head} (declX : Ctx.lookup Θ.raw X = famCode psX cX)
    (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX) (Kl : List (Fin psX.length)) (nodup : Kl.Nodup)
    (cov : PatternCovered σ X) :
    PatternCovered (pruneHom families X declX universesX hcX Kl ≫ σ) X := by
  obtain ⟨i, ps, qs, c, c', K, dX, di, _, uqs, _, uc', below, injective, domains, eq⟩ := cov
  obtain ⟨hps, hc⟩ := famCode_inj (dX.symm.trans declX)
  subst hps
  subst hc
  have moved := eq.substitute (pruneHom families X declX universesX hcX Kl).typed
  rw [famCode_subst] at moved
  have reread := reread_equal (pruneHom families X declX universesX hcX Kl) X
    (flexBody ps (keptDomains ps Kl) X (keptPos ps Kl)) (answerSub_self X ps _)
    (pruneData families X declX universesX hcX Kl).typed universesX qs K uqs uc' domains below hcX
  rw [rename_flexBody] at reread
  refine ⟨i, keptDomains ps Kl, qs, c, c', fun k => K (keptPos ps Kl k),
    redecl_self Θ families X _ c (keptDomains_universes Kl universesX) hcX, di,
    keptDomains_universes Kl universesX, uqs, hcX, uc', below, injective.comp (keptPos_injective nodup),
    fun k => by rw [keptPos_domains, domains], moved.trans reread⟩

/-- The invariant depends on the answer only through its substitution. -/
theorem MillerInv.of_eq {Γ Θ : Context S.R} {σ σ' : Θ ⟶ Γ} {R : EquationStore (TotalTerm Θ)}
    (same : ∀ i, σ.substitution i = σ'.substitution i) (inv : MillerInv σ R) : MillerInv σ' R := by
  have equal : σ = σ' := Hom.ext (funext same)
  subst equal
  exact inv

end Invariant

/-! ## The rounds keep the invariant -/

section Rounds

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

include algebra in
theorem solveRound_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
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
    (inv : MillerInv σ (e :: rest))
    (progressed : solveRound facts roots heads algebra rigid complete inh rest families universes hd imgX imgY declX
      declY injX injY domX domY belowX ne cover codomains occX occY opens = .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  unfold solveRound at progressed
  cases progressed
  refine MillerInv.answerStep algebra inv _ (fun _ => rfl) ?_ _
    (occ_reread (valueHom families X declX _ _ _ _) (valueData families X declX _ _ _ _) (fun _ => rfl) (e :: rest))
  intro j hj
  change j ∈ (flexSide psX psY Y (solveMap imgX imgY cover)).support at hj
  rw [support_flexSide, Finset.mem_singleton] at hj
  subst hj
  refine PatternCovered.transport algebra.trans _ (inv.occurs j occY)
    (answerSub_ne X psX _ ne) fun ps c dk => ?_
  obtain ⟨_, hc⟩ := famCode_inj (declY.symm.trans dk)
  subst hc
  exact ⟨cY, (lookup_setFamAt_ne Θ.raw X j psX cX ne).trans dk, (famFacts families declY).2,
    S.levels.cumulative_refl (famFacts families declY).2⟩

include algebra in
/-- **A pruning keeps the invariant.** -/
theorem pruneStep_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (inv : MillerInv σ (e :: rest)) (families : Families Θ) (X : Fin Θ.arity)
    {psX : List Head} {cX : Head} (declX : Ctx.lookup Θ.raw X = famCode psX cX) (Kl : List (Fin psX.length))
    (nodup : Kl.Nodup) (occX : X ∈ occ (e :: rest)) :
    MillerInv (pruneHom families X declX (famFacts families declX).1 (famFacts families declX).2 Kl ≫ σ)
      (rereadStore (pruneData families X declX (famFacts families declX).1 (famFacts families declX).2 Kl)
        (e :: rest)) := by
  refine MillerInv.answerStep algebra inv _ (fun _ => rfl) ?_ _
    (occ_reread (pruneHom families X declX _ _ _) (pruneData families X declX _ _ _) (fun _ => rfl) (e :: rest))
  intro j hj
  change j ∈ (flexSide psX _ X _).support at hj
  rw [support_flexSide, Finset.mem_singleton] at hj
  subst hj
  exact PatternCovered.pruned declX (famFacts families declX).1 (famFacts families declX).2 Kl nodup
    (inv.occurs j occX)

include algebra in
theorem stepFlexLocal_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {qs : List Head} {d : Head} {universes : AllUniverses S.R qs} {hd : S.R.isUniverse d}
    {X : Fin Θ.arity} {ps : List Head} {c : Head} {img : Fin ps.length → Fin qs.length}
    {declared : Ctx.lookup Θ.raw X = famCode ps c} {injective : Function.Injective img}
    {domains : ∀ j, ps.get j = qs.get (img j)} {below : S.R.cumulative c d} {l : Fin qs.length}
    {occurs : X ∈ occ (e :: rest)}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inv : MillerInv σ (e :: rest))
    (progressed : stepFlexLocal facts roots heads algebra rigid complete inh rest families universes hd img declared
      injective domains below l occurs opens = .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  unfold stepFlexLocal at progressed
  split at progressed
  · split at progressed
    · cases progressed
      refine MillerInv.answerStep algebra inv _ (fun _ => rfl) ?_ _
        (occ_reread (valueHom families X declared _ _ _ _) (valueData families X declared _ _ _ _) (fun _ => rfl)
          (e :: rest))
      intro j hj
      change j ∈ (localSide ps _ : Tm Head Θ.arity).support at hj
      rw [support_localSide] at hj
      exact absurd hj (Finset.notMem_empty j)
    · cases progressed
  · cases progressed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem stepLocals_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    {v : EqView (S := S) e} {l m : Fin v.qs.length} {sl : e.1.2.code = localSide v.qs l}
    {bl : S.R.cumulative (v.qs.get l) v.d} {sm : e.2.2.code = localSide v.qs m}
    {bm : S.R.cumulative (v.qs.get m) v.d}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inv : MillerInv σ (e :: rest))
    (progressed : stepLocals rigid complete rest v l m sl bl sm bm = .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  unfold stepLocals at progressed
  split at progressed
  · cases progressed
    exact inv.delete
  · cases progressed

include algebra in
theorem stepFlexFlex_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inv : MillerInv σ (e :: rest))
    (progressed : stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂
      opens = .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  unfold stepFlexFlex at progressed
  split_ifs at progressed with hcode hF hcov₁ hcov₂ hc hc'
  · cases progressed
    exact inv.delete
  · unfold pruneRound at progressed
    cases progressed
    exact pruneStep_inv algebra inv families D₁.unknown D₁.declared _ ((List.nodup_finRange _).filter _)
      (occurs_side D₁ (.inl rfl))
  · exact solveRound_inv facts roots heads algebra rigid complete inh inv progressed
  · exact solveRound_inv facts roots heads algebra rigid complete inh
      (opens := fun f solved => (opens f solved).symm) inv progressed
  · unfold pruneRound at progressed
    cases progressed
    exact pruneStep_inv algebra inv families D₂.unknown D₂.declared _ ((List.nodup_finRange _).filter _)
      (occurs_side D₂ (.inr rfl))
  · unfold pruneRound at progressed
    cases progressed
    exact pruneStep_inv algebra inv families D₁.unknown D₁.declared _ ((List.nodup_finRange _).filter _)
      (occurs_side D₁ (.inl rfl))

include algebra in
theorem stepView_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inv : MillerInv σ (e :: rest))
    (progressed : stepView facts roots heads algebra rigid complete normalizes inh rest families v =
      .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  unfold stepView at progressed
  split at progressed
  · exact stepLocals_inv rigid complete inv progressed
  · exact stepFlexLocal_inv facts roots heads algebra rigid complete inh inv progressed
  · exact stepFlexLocal_inv facts roots heads algebra rigid complete inh inv progressed
  · exact stepFlexFlex_inv facts roots heads algebra rigid complete normalizes inh inv progressed

theorem glbSolveRound_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {hl : v.left = .flex D₁ b₁} {hr : v.right = .flex D₂ b₂} {g : Head} {isGlb : IsGlb S.R g D₁.c D₂.c}
    {ne : D₁.unknown ≠ D₂.unknown} {cover : ∀ i, ∃ j, D₂.img j = D₁.img i}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inv : MillerInv σ (e :: rest))
    (progressed : glbSolveRound facts roots heads algebra rigid complete inh headTypingUnique rest families v D₁ b₁
      D₂ b₂ hl hr isGlb ne cover = .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  unfold glbSolveRound at progressed
  obtain ⟨u, s, solved, rfl⟩ := roundAfter_progress _ _ progressed
  have first := MillerInv.lowering algebra inv (millerLowerF families v D₁ D₂.c isGlb)
  have second := MillerInv.lowering algebra first (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm))
  have third := solveRound_inv facts roots heads algebra rigid complete inh
    (opens := lowered_opens rest families v D₁ b₁ D₂ b₂ hl hr isGlb ne) second solved
  refine MillerInv.of_eq (fun i => ?_) third
  show Presentation.subst u.answer.substitution
      (Presentation.subst ids (Presentation.subst ids (σ.substitution i))) =
    Presentation.subst u.answer.substitution (σ.substitution i)
  exact congrArg (Presentation.subst u.answer.substitution) ((subst_ids _).trans (subst_ids _))

include facts roots heads algebra rigid complete normalizes inh headTypingUnique spec in
theorem stepViewGlb_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {e : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inv : MillerInv σ (e :: rest))
    (progressed : stepViewGlb facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec rest
      families v = .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  unfold stepViewGlb at progressed
  split at progressed
  · split at progressed
    · split at progressed
      · exact glbSolveRound_inv facts roots heads algebra rigid complete inh headTypingUnique inv progressed
      · cases progressed
    · exact stepView_inv facts roots heads algebra rigid complete normalizes inh inv progressed
  · exact stepView_inv facts roots heads algebra rigid complete normalizes inh inv progressed

/-- **Every round keeps the invariant.** -/
theorem millerGlbRound_inv {Γ Θ : Context S.R} {σ : Θ ⟶ Γ} {problem : EquationStore (TotalTerm Θ)}
    {update : Update S.levels problem} {smaller : Below (millerRank update.remaining) (millerRank problem)}
    (inside : InMillerGlb (S := S) problem) (inv : MillerInv σ problem)
    (progressed : millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
      problem = .progress update smaller) :
    MillerInv (update.answer ≫ σ) update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [millerGlbRound] at progressed
      rw [dif_pos inside.families] at progressed
      split at progressed
      · exact stepViewGlb_inv facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec inv
          progressed
      · cases progressed

/-! ## The driver keeps the invariant; solved runs are initial -/

/-- **The driver keeps the invariant and the fragment.** -/
theorem drive_inv {Γ : Context S.R} {original : EquationStore (TotalTerm Γ)} (fuel : Nat) :
    ∀ (state : Update S.levels original), MillerInv state.answer state.remaining →
      InMillerGlb (S := S) state.remaining → ∀ (final : Update S.levels original) (finished : final.remaining = []),
        drive (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec)
            fuel state = .solved final finished →
          MillerInv final.answer final.remaining ∧ InMillerGlb (S := S) final.remaining := by
  induction fuel with
  | zero =>
      intro state _ _ final finished h
      cases h
  | succ fuel ih =>
      intro state inv inside final finished h
      rw [drive] at h
      cases ha : advance (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb
        spec) state with
      | done outcome =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
            cases h
            exact ⟨inv, inside⟩
          · split at ha
            · cases ha
            · cases ha
              cases h
            · cases ha
              cases h
      | next next =>
          simp only [ha] at h
          unfold advance at ha
          split at ha
          · cases ha
          · split at ha
            · rename_i update smaller hround
              cases ha
              have inv' := millerGlbRound_inv facts roots heads algebra rigid complete normalizes inh headTypingUnique
                glb spec inside inv hround
              have inside' := millerGlbRound_stable facts roots heads algebra rigid complete normalizes inh
                headTypingUnique glb spec inside hround
              exact ih (state.then update) inv' inside' final finished h
            · cases ha
            · cases ha

include facts roots heads algebra rigid complete normalizes inh headTypingUnique spec in
/-- **Every solved run of the Miller solver ends with an answer whose trimming is the initial solution**, pruning in
place included. -/
theorem millerGlb_solved_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := S) original) {fuel : Nat} {state : Update S.levels original}
    {finished : state.remaining = []}
    (solved : run (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec)
      original fuel = .solved state finished) :
    ∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer := by
  obtain ⟨inv, insideFinal⟩ := drive_inv facts roots heads algebra rigid complete normalizes inh headTypingUnique glb
    spec fuel (Update.pending S.levels original) (MillerInv.pending inside.families original) inside state finished
    solved
  choose ps c hd hu huc using insideFinal.families
  exact ⟨_, _, initial_of_patternTrimmed facts roots heads algebra rigid complete inh (state.completed finished)
    (fun j => (ps j, c j)) hd (fun j => ⟨hu j, huc j⟩) inv.covered⟩

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include facts roots heads algebra rigid complete normalizes inh headTypingUnique spec total in
/-- **Every solvable Miller store, codomains in any order, has an initial solution.** -/
theorem millerGlb_initial {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := S) original) :
    (∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), InitialSolution (frames S.levels) original answer) ∨
      ¬ (frames S.levels).Solvable original := by
  obtain ⟨fuel, decided⟩ :=
    millerGlb_decided facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec total inside
  rcases (decided fuel le_rfl).2 with ⟨state, finished, solved, _⟩ | ⟨absent, _⟩
  · exact .inl (millerGlb_solved_initial facts roots heads algebra rigid complete normalizes inh headTypingUnique glb
      spec inside solved)
  · exact .inr absent

end Rounds

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
