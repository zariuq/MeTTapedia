import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDecision

/-!
# Progress, stability and decision for the Miller solver

* `millerRound_ne_stuck`: on the fragment, a nonempty store is never stuck;
* `millerRound_stable`: every step keeps the fragment;
* `miller_decided`: the tree's driver decides the fragment; every store of the fragment has a principal answer or
  no solution (`principal_or_unsolvable`).
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

/-! ## Stability of each kind of step -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem inMiller_tail {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMiller (S := S) (e :: rest)) : InMiller (S := S) rest :=
  ⟨inside.families, inside.chain, fun e' member => inside.views e' (List.mem_cons_of_mem _ member)⟩

theorem inMiller_value {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMiller (S := S) (e :: rest)) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declX : Ctx.lookup Θ.raw X = famCode psX cX) (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) val (.head cX))
    (shape : ValueShape (redecl Θ inside.families X psX cX (famFacts inside.families declX).1
      (famFacts inside.families declX).2) psX cX val) :
    InMiller (S := S) (rereadStore (valueData inside.families X declX (famFacts inside.families declX).1
      (famFacts inside.families declX).2 val typed) (e :: rest)) :=
  ⟨redecl_families Θ inside.families X psX cX (famFacts inside.families declX).1 (famFacts inside.families declX).2,
    redecl_chain Θ inside.families X declX psX (famFacts inside.families declX).1 (famFacts inside.families declX).2
      inside.chain,
    views_reread (valueHom inside.families X declX (famFacts inside.families declX).1
        (famFacts inside.families declX).2 val typed)
      (valueData inside.families X declX (famFacts inside.families declX).1 (famFacts inside.families declX).2
        val typed)
      rfl (fun _ => rfl) shape (e :: rest) inside.views⟩

include algebra in
theorem inMiller_prune {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InMiller (S := S) (e :: rest)) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declX : Ctx.lookup Θ.raw X = famCode psX cX) (K : List (Fin psX.length)) (nodup : K.Nodup) :
    InMiller (S := S) (rereadStore (pruneData inside.families X declX (famFacts inside.families declX).1
      (famFacts inside.families declX).2 K) (e :: rest)) := by
  have uK := keptDomains_universes K (famFacts inside.families declX).1
  have hcX := (famFacts inside.families declX).2
  refine ⟨redecl_families Θ inside.families X (keptDomains psX K) cX uK hcX,
    redecl_chain Θ inside.families X declX (keptDomains psX K) uK hcX inside.chain,
    views_reread (pruneHom inside.families X declX (famFacts inside.families declX).1 hcX K)
      (pruneData inside.families X declX (famFacts inside.families declX).1 hcX K) rfl
      (fun _ => rfl) ?_ (e :: rest) inside.views⟩
  have declX' : Ctx.lookup (setFamAt Θ.raw X (keptDomains psX K) cX) X = famCode (keptDomains psX K) cX :=
    lookup_setFamAt_self Θ.raw X _ cX
  exact flex_shape algebra (redecl Θ inside.families X (keptDomains psX K) cX uK hcX) psX cX X (keptPos psX K)
    declX' (keptPos_injective nodup) (keptPos_domains psX K) (S.levels.cumulative_refl hcX)

theorem pruneRound_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {d : Head} {hd : S.R.isUniverse d} {X : Fin Θ.arity} {psX : List Head} {cX : Head}
    {declX : Ctx.lookup Θ.raw X = famCode psX cX} {belowX : S.R.cumulative cX d} {p : Fin psX.length → Bool}
    {dropped : ∃ i, p i = false} {occX : X ∈ occ (e :: rest)}
    {pruned : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Pruned inh Δ.raw psX ((List.finRange psX.length).filter p) d (f.substitution X)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMiller (S := S) (e :: rest))
    (progressed : pruneRound facts roots heads algebra rigid complete inh rest families hd declX belowX p dropped occX
      pruned = .progress update smaller) :
    InMiller (S := S) update.remaining := by
  unfold pruneRound at progressed
  cases progressed
  exact inMiller_prune algebra inside X declX _ ((List.nodup_finRange _).filter _)

theorem solveRound_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
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
    (inside : InMiller (S := S) (e :: rest))
    (progressed : solveRound facts roots heads algebra rigid complete inh rest families universes hd imgX imgY declX
      declY injX injY domX domY belowX ne cover codomains occX occY opens = .progress update smaller) :
    InMiller (S := S) update.remaining := by
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
  exact inMiller_value inside X declX _ _
    (flex_shape algebra (redecl Θ inside.families X psX cX (famFacts inside.families declX).1
      (famFacts inside.families declX).2) psX cX Y (solveMap imgX imgY cover) declY' injσ domσ codomains)

theorem stepFlexLocal_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {qs : List Head} {d : Head} {universes : AllUniverses S.R qs} {hd : S.R.isUniverse d}
    {X : Fin Θ.arity} {ps : List Head} {c : Head} {img : Fin ps.length → Fin qs.length}
    {declared : Ctx.lookup Θ.raw X = famCode ps c} {injective : Function.Injective img}
    {domains : ∀ j, ps.get j = qs.get (img j)} {below : S.R.cumulative c d} {l : Fin qs.length}
    {occurs : X ∈ occ (e :: rest)}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMiller (S := S) (e :: rest))
    (progressed : stepFlexLocal facts roots heads algebra rigid complete inh rest families universes hd img declared
      injective domains below l occurs opens = .progress update smaller) :
    InMiller (S := S) update.remaining := by
  unfold stepFlexLocal at progressed
  split at progressed
  · rename_i j _
    split at progressed
    · rename_i hfit
      cases progressed
      exact inMiller_value inside X declared _ _
        (project_shape algebra (redecl Θ inside.families X ps c (famFacts inside.families declared).1
          (famFacts inside.families declared).2) ps c j hfit)
    · cases progressed
  · cases progressed

/-! ## Stability of the round -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem stepLocals_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {v : EqView (S := S) e} {l m : Fin v.qs.length} {sl : e.1.2.code = localSide v.qs l}
    {bl : S.R.cumulative (v.qs.get l) v.d} {sm : e.2.2.code = localSide v.qs m}
    {bm : S.R.cumulative (v.qs.get m) v.d}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMiller (S := S) (e :: rest))
    (progressed : stepLocals rigid complete rest v l m sl bl sm bm = .progress update smaller) :
    InMiller (S := S) update.remaining := by
  unfold stepLocals at progressed
  split at progressed
  · cases progressed
    exact inMiller_tail inside
  · cases progressed

theorem stepFlexFlex_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMiller (S := S) (e :: rest))
    (progressed : stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂
      opens = .progress update smaller) :
    InMiller (S := S) update.remaining := by
  unfold stepFlexFlex at progressed
  split_ifs at progressed with hcode hF hcov₁ hcov₂ hc hc'
  · cases progressed
    exact inMiller_tail inside
  · unfold pruneRound at progressed
    cases progressed
    exact inMiller_prune algebra inside _ _ _ ((List.nodup_finRange _).filter _)
  · exact solveRound_stable facts roots heads algebra rigid complete inh inside progressed
  · exact solveRound_stable facts roots heads algebra rigid complete inh
      (opens := fun f solved => (opens f solved).symm) inside progressed
  · unfold pruneRound at progressed
    cases progressed
    exact inMiller_prune algebra inside _ _ _ ((List.nodup_finRange _).filter _)
  · unfold pruneRound at progressed
    cases progressed
    exact inMiller_prune algebra inside _ _ _ ((List.nodup_finRange _).filter _)

theorem stepView_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : InMiller (S := S) (e :: rest))
    (progressed : stepView facts roots heads algebra rigid complete normalizes inh rest families v =
      .progress update smaller) :
    InMiller (S := S) update.remaining := by
  unfold stepView at progressed
  split at progressed
  · exact stepLocals_stable rigid complete inside progressed
  · exact stepFlexLocal_stable facts roots heads algebra rigid complete inh inside progressed
  · exact stepFlexLocal_stable facts roots heads algebra rigid complete inh inside progressed
  · exact stepFlexFlex_stable facts roots heads algebra rigid complete normalizes inh inside progressed

/-- **The rules keep the fragment.** -/
theorem millerRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem} {smaller : Below (millerRank update.remaining) (millerRank problem)}
    (inside : InMiller (S := S) problem)
    (progressed : millerRound facts roots heads algebra rigid complete normalizes inh problem =
      .progress update smaller) :
    InMiller (S := S) update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [millerRound] at progressed
      rw [dif_pos inside.families] at progressed
      split at progressed
      · exact stepView_stable facts roots heads algebra rigid complete normalizes inh inside progressed
      · cases progressed

/-! ## Progress by shape -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem stepLocals_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : EqView (S := S) e) (l m : Fin v.qs.length) (sl : e.1.2.code = localSide v.qs l)
    (bl : S.R.cumulative (v.qs.get l) v.d) (sm : e.2.2.code = localSide v.qs m)
    (bm : S.R.cumulative (v.qs.get m) v.d) :
    stepLocals rigid complete rest v l m sl bl sm bm ≠ .stuck := by
  unfold stepLocals
  split <;> intro h <;> cases h

theorem stepFlexLocal_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (families : Families Θ) {qs : List Head} {d : Head} (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    {X : Fin Θ.arity} {ps : List Head} {c : Head} (img : Fin ps.length → Fin qs.length)
    (declared : Ctx.lookup Θ.raw X = famCode ps c) (injective : Function.Injective img)
    (domains : ∀ j, ps.get j = qs.get (img j)) (below : S.R.cumulative c d) (l : Fin qs.length)
    (occurs : X ∈ occ (e :: rest))
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)) :
    stepFlexLocal facts roots heads algebra rigid complete inh rest families universes hd img declared injective
      domains below l occurs opens ≠ .stuck := by
  unfold stepFlexLocal
  split
  · split <;> intro h <;> cases h
  · intro h
    cases h

theorem stepFlexFlex_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (families : Families Θ) (chain : Chain Θ) (v : EqView (S := S) e) (D₁ : FlexData Θ.raw v.qs e.1.2.code)
    (b₁ : S.R.cumulative D₁.c v.d) (D₂ : FlexData Θ.raw v.qs e.2.2.code) (b₂ : S.R.cumulative D₂.c v.d)
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d)) :
    stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂ opens ≠ .stuck := by
  unfold stepFlexFlex
  split_ifs with hcode hF hcov₁ hcov₂ hc hc'
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · exfalso
    rcases chain D₁.unknown D₂.unknown D₁.ps D₂.ps D₁.c D₂.c D₁.declared D₂.declared with h | h
    · exact hc h
    · exact hc' h
  · intro h; cases h
  · intro h; cases h

theorem stepView_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (families : Families Θ) (chain : Chain Θ) (v : EqView (S := S) e) :
    stepView facts roots heads algebra rigid complete normalizes inh rest families v ≠ .stuck := by
  unfold stepView
  split
  · exact stepLocals_ne_stuck rigid complete _ _ _ _ _ _ _
  · exact stepFlexLocal_ne_stuck facts roots heads algebra rigid complete inh families _ _ _ _ _ _ _ _ _ _
  · exact stepFlexLocal_ne_stuck facts roots heads algebra rigid complete inh families _ _ _ _ _ _ _ _ _ _
  · exact stepFlexFlex_ne_stuck facts roots heads algebra rigid complete normalizes inh families chain _ _ _ _ _ _

/-- **Progress by shape**: on the fragment, a nonempty store is never stuck. -/
theorem millerRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InMiller (S := S) problem) (nonempty : problem ≠ []) :
    millerRound facts roots heads algebra rigid complete normalizes inh problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨w⟩ := inside.views e List.mem_cons_self
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (readEq_isSome_of_view w)
      simp only [millerRound]
      rw [dif_pos inside.families]
      split
      · exact stepView_ne_stuck facts roots heads algebra rigid complete normalizes inh inside.families inside.chain _
      · rename_i hnone
        rw [hv] at hnone
        cases hnone

/-! ## Decision -/

/-- **The fragment of the Miller solver.** -/
def millerFragment :
    ContextualDependentWorklist.Fragment (millerSolver facts roots heads algebra rigid complete normalizes inh) where
  holds := InMiller (S := S)
  stable := fun inside progressed =>
    millerRound_stable facts roots heads algebra rigid complete normalizes inh inside progressed
  decisive := fun inside nonempty =>
    millerRound_ne_stuck facts roots heads algebra rigid complete normalizes inh inside nonempty

/-- **Miller patterns with arbitrary distinct locals, decided by the tree's own driver.** On the fragment, the run
reaches, at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem miller_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMiller (S := S) original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (millerSolver facts roots heads algebra rigid complete normalizes inh) original larger =
          run (millerSolver facts roots heads algebra rigid complete normalizes inh) original fuel ∧
        ((∃ state finished,
              run (millerSolver facts roots heads algebra rigid complete normalizes inh) original larger =
                .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (millerSolver facts roots heads algebra rigid complete normalizes inh) original larger =
              .refuted absent)) :=
  (millerFragment facts roots heads algebra rigid complete normalizes inh).decided inside

include facts roots heads algebra rigid complete normalizes inh in
/-- **Every Miller store has a principal answer or no solution.** -/
theorem principal_or_unsolvable {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMiller (S := S) original) :
    (∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal original answer) ∨
      ¬ (frames S.levels).Solvable original := by
  obtain ⟨fuel, decided⟩ := miller_decided facts roots heads algebra rigid complete normalizes inh inside
  rcases (decided fuel le_rfl).2 with ⟨state, _, _, principal⟩ | ⟨absent, _⟩
  · exact .inl ⟨_, _, principal⟩
  · exact .inr absent

end Decided

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
