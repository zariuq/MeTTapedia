import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbRound

/-!
# Miller patterns decided without the chain of codomains

**The fragment** (`InMillerGlb`): a telescope of universe families, and every equation a Miller equation
(`EqView`). The declared codomains need not form a chain. It contains the fragment of the Miller solver
(`inMillerGlb_of_inMiller`).

* **The Miller solver is stuck only on one shape** (`stepView_stuck`): two flex sides of different unknowns covering
  each other, with incomparable codomains (`GlbShape`). Without the chain this is a lemma about the round, not a
  contradiction.
* **Every step keeps the fragment** (`millerGlbRound_stable`): the Miller steps (`stepView_stableGlb`, read without
  the chain) and the round that lowers both unknowns to the greatest lower bound, then solves
  (`glbSolveRound_stable`).
* **Progress by shape** (`millerGlbRound_ne_stuck`), for a greatest lower bound defined on every pair of universes
  (`total`).
* **Decided** (`millerGlb_decided`): from some budget on, the run is fixed and ends with a principal answer or a
  certified refutation; every store of the fragment has a principal answer or no solution
  (`principal_or_unsolvable_glb`).
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

/-! ## The fragment -/

section Fragment

variable {S : Setting Head L}

/-- **The fragment of Miller stores without the chain of codomains.** -/
structure InMillerGlb {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Prop where
  families : Families Γ
  views : ∀ e ∈ problem, Nonempty (EqView (S := S) e)

/-- It contains the fragment of the Miller solver. -/
theorem inMillerGlb_of_inMiller {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InMiller (S := S) problem) : InMillerGlb (S := S) problem :=
  ⟨inside.families, inside.views⟩

end Fragment

section Decided

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

/-! ## Stability of the Miller steps, without the chain -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem inMillerGlb_tail {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := S) (e :: rest)) : InMillerGlb (S := S) rest :=
  ⟨inside.families, fun e' member => inside.views e' (List.mem_cons_of_mem _ member)⟩

theorem inMillerGlb_value {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := S) (e :: rest)) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declX : Ctx.lookup Θ.raw X = famCode psX cX) (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) val (.head cX))
    (shape : ValueShape (redecl Θ inside.families X psX cX (famFacts inside.families declX).1
      (famFacts inside.families declX).2) psX cX val) :
    InMillerGlb (S := S) (rereadStore (valueData inside.families X declX (famFacts inside.families declX).1
      (famFacts inside.families declX).2 val typed) (e :: rest)) :=
  ⟨redecl_families Θ inside.families X psX cX (famFacts inside.families declX).1 (famFacts inside.families declX).2,
    views_reread (valueHom inside.families X declX (famFacts inside.families declX).1
        (famFacts inside.families declX).2 val typed)
      (valueData inside.families X declX (famFacts inside.families declX).1 (famFacts inside.families declX).2
        val typed)
      rfl (fun _ => rfl) shape (e :: rest) inside.views⟩

include algebra in
theorem inMillerGlb_prune {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := S) (e :: rest)) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declX : Ctx.lookup Θ.raw X = famCode psX cX) (K : List (Fin psX.length)) (nodup : K.Nodup) :
    InMillerGlb (S := S) (rereadStore (pruneData inside.families X declX (famFacts inside.families declX).1
      (famFacts inside.families declX).2 K) (e :: rest)) := by
  have uK := keptDomains_universes K (famFacts inside.families declX).1
  have hcX := (famFacts inside.families declX).2
  refine ⟨redecl_families Θ inside.families X (keptDomains psX K) cX uK hcX,
    views_reread (pruneHom inside.families X declX (famFacts inside.families declX).1 hcX K)
      (pruneData inside.families X declX (famFacts inside.families declX).1 hcX K) rfl
      (fun _ => rfl) ?_ (e :: rest) inside.views⟩
  have declX' : Ctx.lookup (setFamAt Θ.raw X (keptDomains psX K) cX) X = famCode (keptDomains psX K) cX :=
    lookup_setFamAt_self Θ.raw X _ cX
  exact flex_shape algebra (redecl Θ inside.families X (keptDomains psX K) cX uK hcX) psX cX X (keptPos psX K)
    declX' (keptPos_injective nodup) (keptPos_domains psX K) (S.levels.cumulative_refl hcX)

theorem solveRound_stableGlb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
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
    (inside : InMillerGlb (S := S) (e :: rest))
    (progressed : solveRound facts roots heads algebra rigid complete inh rest families universes hd imgX imgY declX
      declY injX injY domX domY belowX ne cover codomains occX occY opens = .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  unfold solveRound at progressed
  cases progressed
  have domσ : ∀ i, psY.get i = psX.get (solveMap imgX imgY cover i) := fun i => by
    rw [domX (solveMap imgX imgY cover i), solveMap_spec imgX imgY cover i, domY i]
  have injσ : Function.Injective (solveMap imgX imgY cover) := by
    intro a b same
    apply injY
    rw [← solveMap_spec imgX imgY cover a, ← solveMap_spec imgX imgY cover b, same]
  have declY' : Ctx.lookup (setFamAt Θ.raw X psX cX) Y = famCode psY cY := by
    rw [lookup_setFamAt_ne Θ.raw X Y psX cX ne, declY]
  exact inMillerGlb_value inside X declX _ _
    (flex_shape algebra (redecl Θ inside.families X psX cX (famFacts inside.families declX).1
      (famFacts inside.families declX).2) psX cX Y (solveMap imgX imgY cover) declY' injσ domσ codomains)

theorem stepFlexLocal_stableGlb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {qs : List Head} {d : Head} {universes : AllUniverses S.R qs} {hd : S.R.isUniverse d}
    {X : Fin Θ.arity} {ps : List Head} {c : Head} {img : Fin ps.length → Fin qs.length}
    {declared : Ctx.lookup Θ.raw X = famCode ps c} {injective : Function.Injective img}
    {domains : ∀ j, ps.get j = qs.get (img j)} {below : S.R.cumulative c d} {l : Fin qs.length}
    {occurs : X ∈ occ (e :: rest)}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMillerGlb (S := S) (e :: rest))
    (progressed : stepFlexLocal facts roots heads algebra rigid complete inh rest families universes hd img declared
      injective domains below l occurs opens = .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  unfold stepFlexLocal at progressed
  split at progressed
  · rename_i j _
    split at progressed
    · rename_i hfit
      cases progressed
      exact inMillerGlb_value inside X declared _ _
        (project_shape algebra (redecl Θ inside.families X ps c (famFacts inside.families declared).1
          (famFacts inside.families declared).2) ps c j hfit)
    · cases progressed
  · cases progressed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem stepLocals_stableGlb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {v : EqView (S := S) e} {l m : Fin v.qs.length} {sl : e.1.2.code = localSide v.qs l}
    {bl : S.R.cumulative (v.qs.get l) v.d} {sm : e.2.2.code = localSide v.qs m}
    {bm : S.R.cumulative (v.qs.get m) v.d}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMillerGlb (S := S) (e :: rest))
    (progressed : stepLocals rigid complete rest v l m sl bl sm bm = .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  unfold stepLocals at progressed
  split at progressed
  · cases progressed
    exact inMillerGlb_tail inside
  · cases progressed

theorem stepFlexFlex_stableGlb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMillerGlb (S := S) (e :: rest))
    (progressed : stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂
      opens = .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  unfold stepFlexFlex at progressed
  split_ifs at progressed with hcode hF hcov₁ hcov₂ hc hc'
  · cases progressed
    exact inMillerGlb_tail inside
  · unfold pruneRound at progressed
    cases progressed
    exact inMillerGlb_prune algebra inside _ _ _ ((List.nodup_finRange _).filter _)
  · exact solveRound_stableGlb facts roots heads algebra rigid complete inh inside progressed
  · exact solveRound_stableGlb facts roots heads algebra rigid complete inh
      (opens := fun f solved => (opens f solved).symm) inside progressed
  · unfold pruneRound at progressed
    cases progressed
    exact inMillerGlb_prune algebra inside _ _ _ ((List.nodup_finRange _).filter _)
  · unfold pruneRound at progressed
    cases progressed
    exact inMillerGlb_prune algebra inside _ _ _ ((List.nodup_finRange _).filter _)

theorem stepView_stableGlb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMillerGlb (S := S) (e :: rest))
    (progressed : stepView facts roots heads algebra rigid complete normalizes inh rest families v =
      .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  unfold stepView at progressed
  split at progressed
  · exact stepLocals_stableGlb rigid complete inside progressed
  · exact stepFlexLocal_stableGlb facts roots heads algebra rigid complete inh inside progressed
  · exact stepFlexLocal_stableGlb facts roots heads algebra rigid complete inh inside progressed
  · exact stepFlexFlex_stableGlb facts roots heads algebra rigid complete normalizes inh inside progressed

/-! ## Stability of the lowering round -/

theorem solveRound_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
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
        (Presentation.rename (sideRen qs psX imgX) (opened psX (f.substitution X))) (.head d)} :
    solveRound facts roots heads algebra rigid complete inh rest families universes hd imgX imgY declX declY injX injY
      domX domY belowX ne cover codomains occX occY opens ≠ .stuck := by
  unfold solveRound
  intro h
  cases h

theorem glbSolveRound_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {hl : v.left = .flex D₁ b₁} {hr : v.right = .flex D₂ b₂} {g : Head} {isGlb : IsGlb S.R g D₁.c D₂.c}
    {ne : D₁.unknown ≠ D₂.unknown} {cover : ∀ i, ∃ j, D₂.img j = D₁.img i}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMillerGlb (S := S) (e :: rest))
    (progressed : glbSolveRound facts roots heads algebra rigid complete inh headTypingUnique rest families v D₁ b₁
      D₂ b₂ hl hr isGlb ne cover = .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  unfold glbSolveRound at progressed
  obtain ⟨u, s, solved, rfl⟩ := roundAfter_progress _ _ progressed
  have lowered : InMillerGlb (S := S)
      ((frames S.levels).applyStore (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
        ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom (e :: rest))) :=
    ⟨lowering_families _ (lowering_families _ families),
      lowering_views algebra _ _ (lowering_views algebra _ _ inside.views)⟩
  have kept := solveRound_stableGlb facts roots heads algebra rigid complete inh
    (opens := lowered_opens rest families v D₁ b₁ D₂ b₂ hl hr isGlb ne) lowered solved
  exact kept

/-! ## The stuck shape, and progress -/

theorem stepFlexFlex_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (families : Families Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d))
    (stuck : stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂ opens =
      .stuck) :
    GlbShape (S := S) D₁ D₂ := by
  by_contra noShape
  revert stuck
  unfold stepFlexFlex
  split_ifs with hcode hF hcov₁ hcov₂ hc hc'
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro _
    exact noShape ⟨hF, hcov₁, hcov₂, hc, hc'⟩
  · intro h; cases h
  · intro h; cases h

/-- **The Miller step is stuck only on the shape of incomparable codomains.** -/
theorem stepView_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (families : Families Θ) (v : EqView (S := S) e)
    (stuck : stepView facts roots heads algebra rigid complete normalizes inh rest families v = .stuck) :
    ∃ D₁ b₁ D₂ b₂, v.left = .flex D₁ b₁ ∧ v.right = .flex D₂ b₂ ∧ GlbShape (S := S) D₁ D₂ := by
  unfold stepView at stuck
  split at stuck
  · exact absurd stuck (stepLocals_ne_stuck rigid complete _ _ _ _ _ _ _)
  · exact absurd stuck (stepFlexLocal_ne_stuck facts roots heads algebra rigid complete inh families _ _ _ _ _ _ _ _
      _ _)
  · exact absurd stuck (stepFlexLocal_ne_stuck facts roots heads algebra rigid complete inh families _ _ _ _ _ _ _ _
      _ _)
  · rename_i D₁ b₁ D₂ b₂ hl hr
    exact ⟨D₁, b₁, D₂, b₂, hl, hr,
      stepFlexFlex_stuck facts roots heads algebra rigid complete normalizes inh families v D₁ b₁ D₂ b₂ _ stuck⟩

include facts roots heads algebra rigid complete normalizes inh headTypingUnique spec in
/-- **The rules keep the fragment.** -/
theorem stepViewGlb_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMillerGlb (S := S) (e :: rest))
    (progressed : stepViewGlb facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec rest
      families v = .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  unfold stepViewGlb at progressed
  split at progressed
  · split at progressed
    · split at progressed
      · exact glbSolveRound_stable facts roots heads algebra rigid complete inh headTypingUnique inside progressed
      · cases progressed
    · exact stepView_stableGlb facts roots heads algebra rigid complete normalizes inh inside progressed
  · exact stepView_stableGlb facts roots heads algebra rigid complete normalizes inh inside progressed

theorem millerGlbRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem} {smaller : Below (millerRank update.remaining) (millerRank problem)}
    (inside : InMillerGlb (S := S) problem)
    (progressed : millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
      problem = .progress update smaller) :
    InMillerGlb (S := S) update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [millerGlbRound] at progressed
      rw [dif_pos inside.families] at progressed
      split at progressed
      · exact stepViewGlb_stable facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
          inside progressed
      · cases progressed

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include total in
theorem stepViewGlb_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (families : Families Θ) (v : EqView (S := S) e) :
    stepViewGlb facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec rest families v ≠
      .stuck := by
  unfold stepViewGlb
  split
  · rename_i D₁ b₁ D₂ b₂ hl hr
    split
    · rename_i shape
      split
      · unfold glbSolveRound
        apply roundAfter_ne_stuck
        exact solveRound_ne_stuck facts roots heads algebra rigid complete inh
      · rename_i none
        obtain ⟨g, found⟩ := total (famFacts families D₁.declared).2 (famFacts families D₂.declared).2
        rw [found] at none
        cases none
    · rename_i noShape
      intro stuck
      obtain ⟨D₁', b₁', D₂', b₂', hl', hr', shape'⟩ :=
        stepView_stuck facts roots heads algebra rigid complete normalizes inh families v stuck
      rw [hl] at hl'
      rw [hr] at hr'
      cases hl'
      cases hr'
      exact noShape shape'
  · rename_i notBoth
    intro stuck
    obtain ⟨D₁, b₁, D₂, b₂, hl, hr, _⟩ :=
      stepView_stuck facts roots heads algebra rigid complete normalizes inh families v stuck
    exact notBoth D₁ b₁ D₂ b₂ hl hr

include total in
/-- **Progress by shape**: on the fragment, a nonempty store is never stuck. -/
theorem millerGlbRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InMillerGlb (S := S) problem) (nonempty : problem ≠ []) :
    millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec problem ≠
      .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨w⟩ := inside.views e List.mem_cons_self
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (readEq_isSome_of_view w)
      simp only [millerGlbRound]
      rw [dif_pos inside.families]
      split
      · exact stepViewGlb_ne_stuck facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
          total inside.families _
      · rename_i hnone
        rw [hv] at hnone
        cases hnone

/-! ## Decision -/

/-- **The fragment of the Miller solver without the chain.** -/
def millerGlbFragment : ContextualDependentWorklist.Fragment
    (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec) where
  holds := InMillerGlb (S := S)
  stable := fun inside progressed =>
    millerGlbRound_stable facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec inside
      progressed
  decisive := fun inside nonempty =>
    millerGlbRound_ne_stuck facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec total
      inside nonempty

include total in
/-- **Miller patterns decided without the chain of codomains, by the tree's own driver.** On the fragment, the run
reaches, at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem millerGlb_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := S) original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec)
          original larger =
        run (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec)
          original fuel ∧
        ((∃ state finished,
              run (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec)
                  original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (millerGlbSolver facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec)
              original larger = .refuted absent)) :=
  (millerGlbFragment facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec total).decided
    inside

include facts roots heads algebra rigid complete normalizes inh headTypingUnique spec total in
/-- **Every Miller store, codomains in any order, has a principal answer or no solution.** -/
theorem principal_or_unsolvable_glb {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := S) original) :
    (∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer) ∨
      ¬ (frames S.levels).Solvable original := by
  obtain ⟨fuel, decided⟩ :=
    millerGlb_decided facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec total inside
  rcases (decided fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, _⟩
  · exact .inl ⟨_, _, principal⟩
  · exact .inr absent

end Decided

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
