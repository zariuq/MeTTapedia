import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRefutation

/-!
# Pruning and intersection forced in the tree's fibre

A value of a family is **pruned** to a list `K` of its binders (`Pruned`) when its opening equals its reading at the
binders of `K` with every other binder sent to an inhabitant, renamed back. Such a value factors through `λ x̄. H x_K`.

* **Intersection** (`intersect_forced`): from `λ ȳ. F y_a ≐ λ ȳ. F y_b`, every solution's value of `F` is pruned to
  the positions where `a` and `b` agree. Substitution alone cannot show this when `a` and `b` differ by a cycle
  (`F x y ≐ F y x`: a symmetric function satisfies it semantically), so the proof reads the normal form of the
  opened value: two renamings of one normal term are equal only when the renamings agree on its support (the tree's
  `equal_agreement`). The pruned body is then obtained by substitution at inhabitants, with no typing reflection.
* **Pruning** (`prune_forced`): from `λ ȳ. F y_a ≐ λ ȳ. G y_b`, every solution's value of `F` is pruned to the
  positions whose local is among `b`. This needs no normal form: the forcing by substitution
  (`flexFlex_forced`) already writes the value with only those positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Kept binders -/

section Kept

/-- The domains at the kept binders. -/
def keptDomains (ps : List Head) (K : List (Fin ps.length)) : List Head := K.map ps.get

/-- The binder of `ps` at the `j`-th kept position. -/
def keptPos (ps : List Head) (K : List (Fin ps.length)) (j : Fin (keptDomains ps K).length) : Fin ps.length :=
  K.get (Fin.cast (by simp [keptDomains]) j)

theorem keptPos_domains (ps : List Head) (K : List (Fin ps.length)) (j : Fin (keptDomains ps K).length) :
    (keptDomains ps K).get j = ps.get (keptPos ps K j) := by
  have h : j.1 < K.length := by simpa [keptDomains] using j.2
  show (K.map ps.get)[j.1]'(by simpa [keptDomains] using j.2) = ps.get (K[j.1]'h)
  rw [List.getElem_map]

theorem keptPos_injective {ps : List Head} {K : List (Fin ps.length)} (nodup : K.Nodup) :
    Function.Injective (keptPos ps K) := by
  intro a b same
  have inner := (List.Nodup.get_inj_iff nodup).mp same
  apply Fin.ext
  have := congrArg Fin.val inner
  simpa using this

theorem mem_keptPos {ps : List Head} {K : List (Fin ps.length)} {i : Fin ps.length} (member : i ∈ K) :
    ∃ j, keptPos ps K j = i := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp member
  refine ⟨Fin.cast (by simp [keptDomains]) n, ?_⟩
  rw [← hn]
  rfl

theorem keptDomains_universes {R : Rules Head} {ps : List Head} (K : List (Fin ps.length))
    (universes : AllUniverses R ps) : AllUniverses R (keptDomains ps K) := by
  intro p member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  exact universes _ (List.get_mem ps i)

/-- The positions where two argument maps agree. -/
def agreeing {k m : Nat} (imgA imgB : Fin k → Fin m) : List (Fin k) :=
  (List.finRange k).filter fun i => decide (imgA i = imgB i)

theorem agreeing_nodup {k m : Nat} (imgA imgB : Fin k → Fin m) : (agreeing imgA imgB).Nodup :=
  (List.nodup_finRange k).filter _

theorem mem_agreeing {k m : Nat} {imgA imgB : Fin k → Fin m} {i : Fin k} :
    i ∈ agreeing imgA imgB ↔ imgA i = imgB i := by
  simp [agreeing]

/-- The positions whose local is among the arguments of another side. -/
def covered {k k' m : Nat} (imgF : Fin k → Fin m) (imgG : Fin k' → Fin m) : List (Fin k) :=
  (List.finRange k).filter fun i => decide (∃ j, imgG j = imgF i)

theorem covered_nodup {k k' m : Nat} (imgF : Fin k → Fin m) (imgG : Fin k' → Fin m) : (covered imgF imgG).Nodup :=
  (List.nodup_finRange k).filter _

theorem mem_covered {k k' m : Nat} {imgF : Fin k → Fin m} {imgG : Fin k' → Fin m} {i : Fin k} :
    i ∈ covered imgF imgG ↔ ∃ j, imgG j = imgF i := by
  simp [covered]

end Kept

/-! ## Pruned values -/

section Pruned

variable {S : Setting Head L} (inh : Inhabitants S.R)

/-- **A value pruned to the binders `K`**: its opening equals its reading at `K`, the other binders at inhabitants,
renamed back. -/
def Pruned {n : Nat} (Γ : Ctx Head n) (ps : List Head) (K : List (Fin ps.length)) (e : Head) (t : Tm Head n) :
    Prop :=
  Equal S.R (ctx Γ ps) (opened ps t)
    (Presentation.rename (sideRen ps (keptDomains ps K) (keptPos ps K))
      (Presentation.subst (pullSub inh ps (keptDomains ps K) (keptPos ps K)) (opened ps t))) (.head e)

/-- The reading at the kept binders, renamed back, fixes every variable that is outer or kept. -/
theorem kept_fixed {n : Nat} (ps : List Head) (K : List (Fin ps.length)) (nodup : K.Nodup)
    (v : Fin (arity n ps)) (outerOrKept : (∃ w, v = shift ps w) ∨ ∃ i ∈ K, v = loc ps i) :
    Presentation.rename (sideRen ps (keptDomains ps K) (keptPos ps K))
      (pullSub inh ps (keptDomains ps K) (keptPos ps K) v) = .var v := by
  rcases outerOrKept with ⟨w, rfl⟩ | ⟨i, member, rfl⟩
  · rw [pullSub_shift]
    show Tm.var (spineRen _ _ _ (shift (keptDomains ps K) w)) = Tm.var (shift ps w)
    rw [spineRen_shift]
  · obtain ⟨j, rfl⟩ := mem_keptPos member
    rw [pullSub_loc, pullImg_img inh (keptPos_injective nodup) j]
    show Tm.var (spineRen _ _ _ (loc (keptDomains ps K) j)) = Tm.var (loc ps (keptPos ps K j))
    rw [spineRen_loc]

/-- The reading at the kept binders, renamed back, is a typed substitution. -/
theorem kept_substMor {n : Nat} (Γ : Ctx Head n) (ps : List Head) (K : List (Fin ps.length))
    (universes : AllUniverses S.R ps) :
    SubstMor S.R (ctx Γ ps) (ctx Γ ps) fun v =>
      Presentation.rename (sideRen ps (keptDomains ps K) (keptPos ps K))
        (pullSub inh ps (keptDomains ps K) (keptPos ps K) v) := by
  intro v
  have typed := pullSub_substMor inh Γ ps (keptDomains ps K) (keptPos ps K) universes (keptPos_domains ps K) v
  have renamed := typed.rename (sideRen_ctxRen Γ ps (keptDomains ps K) (keptPos ps K) (keptPos_domains ps K))
  rw [rename_subst] at renamed
  exact renamed

variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)

include rigid complete normalizes in
/-- **Intersection is forced.** From `λ ȳ. F y_a ≐ λ ȳ. F y_b`, every solution's value of `F` is pruned to any list
of binders containing the positions where `a` and `b` agree. -/
theorem intersect_forced {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {c d : Head} {F : Fin Θ.arity}
    {ps : List Head} (imgA imgB : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Θ.raw F = famCode ps c)
    (universes : AllUniverses S.R qs) (universesP : AllUniverses S.R ps) (hc : S.R.isUniverse c)
    (below : S.R.cumulative c d) (domainsA : ∀ j, ps.get j = qs.get (imgA j))
    (domainsB : ∀ j, ps.get j = qs.get (imgB j)) (K : List (Fin ps.length)) (nodup : K.Nodup)
    (covers : ∀ i, imgA i = imgB i → i ∈ K)
    (equal : Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps imgA) (opened ps (f.substitution F)))
      (Presentation.rename (sideRen qs ps imgB) (opened ps (f.substitution F))) (.head d)) :
    Pruned inh Δ.raw ps K d (f.substitution F) := by
  have tOpen := value_opened_typed f declared
  have formedP := ctx_formed ps Δ.formed universesP
  obtain ⟨u, hu, tc, _⟩ := S.levels.successor hc
  let C : Context S.R := ⟨_, ctx Δ.raw ps, formedP⟩
  let T : TypeOver C := ⟨.head c, u, hu, .headType tc⟩
  obtain ⟨N, normal, eN⟩ := normalizes (⟨opened ps (f.substitution F), tOpen⟩ : Term C T)
  change Equal S.R (ctx Δ.raw ps) (opened ps (f.substitution F)) N (.head c) at eN
  have eA := Derivable.cumulEq (eN.rename (sideRen_ctxRen Δ.raw qs ps imgA domainsA)) below
  have eB := Derivable.cumulEq (eN.rename (sideRen_ctxRen Δ.raw qs ps imgB domainsB)) below
  have same : Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps imgA) N)
      (Presentation.rename (sideRen qs ps imgB) N) (.head d) := eA.symm.trans (equal.trans eB)
  have agree := ContextualDependentNormalEqualizer.equal_agreement rigid complete (ctx_formed qs Δ.formed universes)
    N _ _ same normal
  have fixed : Presentation.rename (sideRen ps (keptDomains ps K) (keptPos ps K))
      (Presentation.subst (pullSub inh ps (keptDomains ps K) (keptPos ps K)) N) = N := by
    rw [rename_subst]
    conv_rhs => rw [← subst_ids N]
    apply ContextualDependentGeneralPattern.subst_eq_of_support
    intro v member
    apply kept_fixed inh ps K nodup v
    rcases index_cases ps v with ⟨w, rfl⟩ | ⟨j, rfl⟩
    · exact .inl ⟨w, rfl⟩
    · refine .inr ⟨j, covers j ?_, rfl⟩
      have hit := agree _ member
      change spineRen ps (shift qs) _ (loc ps j) = spineRen ps (shift qs) _ (loc ps j) at hit
      rw [spineRen_loc, spineRen_loc] at hit
      exact loc_injective qs hit
  have eM := eN.substitute (pullSub_substMor inh Δ.raw ps (keptDomains ps K) (keptPos ps K) universesP
    (keptPos_domains ps K))
  have eR := eM.rename (sideRen_ctxRen Δ.raw ps (keptDomains ps K) (keptPos ps K) (keptPos_domains ps K))
  rw [fixed] at eR
  exact Derivable.cumulEq (eN.trans eR.symm) below

include inh in
/-- **Pruning is forced.** From `λ ȳ. F y_a ≐ λ ȳ. G y_b`, every solution's value of `F` is pruned to any list of
binders containing the positions whose local is among `b`. -/
theorem prune_forced {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {d : Head} {F G : Fin Θ.arity}
    {psF psG : List Head} (imgF : Fin psF.length → Fin qs.length) (imgG : Fin psG.length → Fin qs.length)
    (universes : AllUniverses S.R qs) (universesF : AllUniverses S.R psF) (domainsF : ∀ j, psF.get j = qs.get (imgF j))
    (injectiveF : Function.Injective imgF) (K : List (Fin psF.length)) (nodup : K.Nodup)
    (covers : ∀ i, (∃ j, imgG j = imgF i) → i ∈ K)
    (equal : Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psF imgF) (opened psF (f.substitution F)))
      (Presentation.rename (sideRen qs psG imgG) (opened psG (f.substitution G))) (.head d)) :
    Pruned inh Δ.raw psF K d (f.substitution F) := by
  have forced := flexFlex_forced inh f qs imgG imgF universes domainsF injectiveF equal.symm
  have stays : Presentation.subst (fun v => Presentation.rename (sideRen psF (keptDomains psF K) (keptPos psF K))
      (pullSub inh psF (keptDomains psF K) (keptPos psF K) v))
      (apps (Presentation.rename (shift psF) (f.substitution G))
        ((List.finRange psG.length).map fun j => pullImg inh qs psF imgF (imgG j))) =
      apps (Presentation.rename (shift psF) (f.substitution G))
        ((List.finRange psG.length).map fun j => pullImg inh qs psF imgF (imgG j)) := by
    rw [subst_apps, List.map_map]
    congr 1
    · rw [subst_rename, ← subst_renSub]
      apply subst_ext
      intro w
      exact kept_fixed inh psF K nodup _ (.inl ⟨w, rfl⟩)
    · apply List.map_congr_left
      intro j _
      show Presentation.subst _ (pullImg inh qs psF imgF (imgG j)) = pullImg inh qs psF imgF (imgG j)
      unfold pullImg
      cases found : posOf imgF (imgG j) with
      | some i =>
          exact kept_fixed inh psF K nodup _ (.inr ⟨i, covers i ⟨j, (posOf_some found).symm⟩, rfl⟩)
      | none => rfl
  have moved := forced.substitute (kept_substMor inh Δ.raw psF K universesF)
  rw [stays] at moved
  unfold Pruned
  rw [rename_subst]
  exact forced.symm.trans moved

end Pruned

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
