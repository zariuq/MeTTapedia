import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedReduction

/-!
# Corrected COMM as one firing of the transform candidate step

`MeTTaOperationsComm.comm_adequacy` relates COMM to one firing of the
candidate step when the unifier is ground and principal and the continuations
mention only pattern variables. This module removes both restrictions.

* `comm_valid_principal`: the firing is valid for every principal unifier, not
  only a ground one, when the store's variables are apart from the patterns'.
* `firing_reads_uniform_dot`: every solution of the result store reads each
  produced continuation as the *uniform dot*: every pattern variable is quoted,
  then the unifier is applied. This holds for every principal unifier.
* `uniformDot_eq_applyDot`: when the unifier binds every pattern variable a
  continuation reads, the uniform dot is the manuscript's dot `P·σ̇`. When a
  read variable is left unbound, the manuscript's dot depends on which most
  general unifier is chosen (`manuscript_dot_depends_on_orientation`), and the
  uniform dot does not.
* `comm_adequacy_corrected`: the firing is valid, the corrected relational step
  relates the source to the manuscript's reduct, and every solution reads the
  outputs as that reduct.
* `step_toReflectionClosure`: the corrected relational step is contained in
  `ReflectionClosure.Step`, instantiated with principal unifiers and
  alpha-equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst pvars PSubst pcomp psubst_comp patternAction commRule commSelection comm_valid_iff
    comm_problem dotted quoteOn storePVars applyDot_eq lookup_eq_none_of_keys psubst_congr firstOrder)

/-! ## Inclusion into the existing relational rules -/

/-- The corrected relational step is an instance of `ReflectionClosure.Step`. -/
theorem step_toReflectionClosure {admit : Admission} {p q : Pattern} (step : Step admit p q) :
    ReflectionClosure.Step (fun t u bs => Principal t u bs) AlphaEq p q := by
  induction step with
  | comm t u x A B bs principal _ => exact .comm t u x A B bs principal
  | parallel surrounding _ ih => exact .parallel surrounding ih
  | congruence before _ after ih => exact .congruence before ih after
  | reflect x _ ih => exact .reflect x ih

/-! ## The uniform dot -/

/-- Quote every pattern variable `vs`, reading it through the unifier. -/
def uniformSubst (vs : List String) (bs : Bindings) : PSubst := fun v =>
  if v ∈ vs then some (nQuote (psubst bs.lookup (.fvar v))) else none

def uniformDot (vs : List String) (bs : Bindings) (P : Pattern) : Pattern := psubst (uniformSubst vs bs) P

/-- **Every solution reads the uniform dot.** For any principal unifier, every
solution of a store that equates the two patterns reads a dotted
continuation as its uniform dot. -/
theorem firing_reads_uniform_dot {t u : Pattern} {bs : Bindings} (principal : Principal t u bs)
    {σ : PSubst} (solved : psubst σ t = psubst σ u) (P : Pattern) :
    psubst σ (dotted (pvars t ++ pvars u) P) = psubst σ (uniformDot (pvars t ++ pvars u) bs P) := by
  unfold dotted uniformDot
  rw [psubst_comp, psubst_comp]
  apply psubst_getD_congr_on
  intro v _
  by_cases member : v ∈ pvars t ++ pvars u
  · simp only [pcomp, quoteOn, uniformSubst, if_pos member, Option.getD_some]
    show nQuote (psubst σ (.fvar v)) = nQuote (psubst σ (psubst bs.lookup (.fvar v)))
    rw [principal.general σ solved (.fvar v)]
  · simp only [pcomp, quoteOn, uniformSubst, if_neg member]

/-- When the unifier binds every pattern variable the continuation reads, the
uniform dot is the manuscript's dot. -/
theorem uniformDot_eq_applyDot {t u : Pattern} {bs : Bindings} (principal : Principal t u bs)
    (P : Pattern) (fo : firstOrder P = true)
    (bound : ∀ v ∈ pvars P, v ∈ pvars t ++ pvars u → ∃ w, bs.lookup v = some w) :
    uniformDot (pvars t ++ pvars u) bs P = applyDot bs P := by
  rw [applyDot_eq bs P fo]
  unfold uniformDot
  apply psubst_getD_congr_on
  intro v occurs
  by_cases member : v ∈ pvars t ++ pvars u
  · obtain ⟨w, found⟩ := bound v occurs member
    simp [uniformSubst, member, psubst, found]
  · simp [uniformSubst, member, lookup_eq_none_of_keys principal.keys member]

/-- **The uniform dot is the manuscript's dot of the completed list.** Dotting
with the principal list completed by identity entries quotes every pattern
variable as its unifier value. The executable COMM dots with this list. -/
theorem applyDot_completeBindings {t u : Pattern} {bs : Bindings} (principal : Principal t u bs)
    (P : Pattern) (fo : firstOrder P = true) :
    applyDot (completeBindings (pvars t ++ pvars u) bs) P = uniformDot (pvars t ++ pvars u) bs P := by
  rw [applyDot_eq _ P fo]
  unfold uniformDot
  apply psubst_getD_congr_on
  intro v _
  show (((completeBindings (pvars t ++ pvars u) bs).lookup v).map nQuote).getD (.fvar v) =
    (uniformSubst (pvars t ++ pvars u) bs v).getD (.fvar v)
  rw [lookup_completeBindings]
  unfold uniformSubst
  by_cases member : v ∈ pvars t ++ pvars u
  · cases h : bs.lookup v with
    | some w => simp [member, psubst, h]
    | none => simp [member, psubst, h]
  · rw [lookup_eq_none_of_keys principal.keys member]
    simp [member]

/-- The manuscript's dot depends on the orientation of a most general unifier
when a read variable stays unbound: `{X ↦ Y}` and `{Y ↦ X}` both unify `X` and
`Y`, and dot the continuation `X` to `@Y` and to `X`. The uniform dot reads
`@Y` and `@X`, which differ only by the choice of residual name. -/
theorem manuscript_dot_depends_on_orientation :
    Principal (.fvar "X") (.fvar "Y") [("X", .fvar "Y")] ∧
      Principal (.fvar "X") (.fvar "Y") [("Y", .fvar "X")] ∧
      applyDot [("X", .fvar "Y")] (.fvar "X") = nQuote (.fvar "Y") ∧
      applyDot [("Y", .fvar "X")] (.fvar "X") = .fvar "X" ∧
      uniformDot ["X", "Y"] [("X", .fvar "Y")] (.fvar "X") = nQuote (.fvar "Y") ∧
      uniformDot ["X", "Y"] [("Y", .fvar "X")] (.fvar "X") = nQuote (.fvar "X") := by
  refine ⟨⟨by decide +kernel, ?_, by decide +kernel⟩, ⟨by decide +kernel, ?_, by decide +kernel⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro τ solves p
    rw [psubst_comp]
    apply psubst_getD_congr_on
    intro v _
    by_cases h : v = "X"
    · subst h
      simp only [psubst] at solves
      simp [pcomp, Bindings.lookup, psubst, solves]
    · have h' : ("X" = v) = False := by simp [Ne.symm h]
      simp [pcomp, Bindings.lookup, h']
  · intro τ solves p
    rw [psubst_comp]
    apply psubst_getD_congr_on
    intro v _
    by_cases h : v = "Y"
    · subst h
      simp only [psubst] at solves
      simp [pcomp, Bindings.lookup, psubst, solves]
    · have h' : ("Y" = v) = False := by simp [Ne.symm h]
      simp [pcomp, Bindings.lookup, h']

/-! ## The firing is valid for every principal unifier -/

variable {O : Type*} [DecidableEq O]

theorem comm_valid_principal (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (principal : Principal t u bs)
    (before : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ before.present) (present₂ : second ∈ before.present)
    (fresh₁ : made₁ ∉ before.present) (fresh₂ : made₂ ∉ before.present)
    (out₁ : label made₁ = dotted (pvars t ++ pvars u) P)
    (out₂ : label made₂ = dotted (pvars t ++ pvars u) Q)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars before.equations)
    (base : patternAction.Consistent before.equations) :
    (commSelection first second made₁ made₂).Valid patternAction label (commRule t u channel P Q) before := by
  classical
  refine (comm_valid_iff label t u channel P Q before first second made₁ made₂).mpr
    ⟨distinct, madeDistinct, present₁, present₂, fresh₁, fresh₂, out₁, out₂, ?_⟩
  obtain ⟨σ₀, solved₀⟩ := base
  let glued : PSubst := fun x => if x ∈ pvars t ++ pvars u then bs.lookup x else σ₀ x
  have onPatterns : ∀ term : Pattern, (∀ x ∈ pvars term, x ∈ pvars t ++ pvars u) →
      psubst glued term = psubst bs.lookup term := by
    intro term inside
    apply psubst_congr
    intro x member
    show (if x ∈ pvars t ++ pvars u then bs.lookup x else σ₀ x) = bs.lookup x
    rw [if_pos (inside x member)]
  refine ⟨glued, ?_⟩
  intro e member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with old | rfl | rfl | rfl
  · have equation := solved₀ e old
    change psubst σ₀ e.1 = psubst σ₀ e.2 at equation
    change psubst glued e.1 = psubst glued e.2
    have outside : ∀ term, (∀ x ∈ pvars term, x ∈ storePVars before.equations) →
        psubst glued term = psubst σ₀ term := by
      intro term inside
      apply psubst_congr
      intro x member
      have notPattern : x ∉ pvars t ++ pvars u := fun inPattern => apart x inPattern (inside x member)
      show (if x ∈ pvars t ++ pvars u then bs.lookup x else σ₀ x) = σ₀ x
      rw [if_neg notPattern]
    rw [outside e.1 (fun x member => by
        simp only [storePVars, List.mem_flatMap, List.mem_append]; exact ⟨e, old, .inl member⟩),
      outside e.2 (fun x member => by
        simp only [storePVars, List.mem_flatMap, List.mem_append]; exact ⟨e, old, .inr member⟩)]
    exact equation
  · change psubst glued (pFor t channel P) = psubst glued (label first)
    rw [labelFirst]
  · change psubst glued (pFor u channel Q) = psubst glued (label second)
    rw [labelSecond]
  · change psubst glued t = psubst glued u
    rw [onPatterns t (fun x member => List.mem_append_left _ member),
      onPatterns u (fun x member => List.mem_append_right _ member)]
    exact principal.solves

/-- **COMM adequacy, corrected.** For a COMM redex under the variable
convention and any principal unifier: the firing is valid; the corrected
relational step relates the source to the manuscript's reduct; every solution
of the result store reads each output as the uniform dot; and where the
unifier binds every variable a continuation reads, that reading is the
manuscript's dotted continuation. -/
theorem comm_adequacy_corrected (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (principal : Principal t u bs) (convention : Apart t P u Q)
    (foP : firstOrder P = true) (foQ : firstOrder Q = true)
    (before : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ before.present) (present₂ : second ∈ before.present)
    (fresh₁ : made₁ ∉ before.present) (fresh₂ : made₂ ∉ before.present)
    (out₁ : label made₁ = dotted (pvars t ++ pvars u) P)
    (out₂ : label made₂ = dotted (pvars t ++ pvars u) Q)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars before.equations)
    (base : patternAction.Consistent before.equations) :
    (commSelection first second made₁ made₂).Valid patternAction label (commRule t u channel P Q) before ∧
      Step conventional (par (pFor t channel P) (pFor u channel Q))
        (par (applyDot bs P) (applyDot bs Q)) ∧
      (∀ σ : PSubst, patternAction.Models σ
          ((commSelection first second made₁ made₂).result label (commRule t u channel P Q) before).equations →
        psubst σ (label made₁) = psubst σ (uniformDot (pvars t ++ pvars u) bs P) ∧
          psubst σ (label made₂) = psubst σ (uniformDot (pvars t ++ pvars u) bs Q)) ∧
      ((∀ v ∈ pvars P ++ pvars Q, v ∈ pvars t ++ pvars u → ∃ w, bs.lookup v = some w) →
        ∀ σ : PSubst, patternAction.Models σ
            ((commSelection first second made₁ made₂).result label (commRule t u channel P Q) before).equations →
          psubst σ (label made₁) = psubst σ (applyDot bs P) ∧
            psubst σ (label made₂) = psubst σ (applyDot bs Q)) := by
  have valid := comm_valid_principal label t u channel P Q bs principal before first second made₁ made₂
    labelFirst labelSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ out₁ out₂ apart base
  have reads : ∀ σ : PSubst, patternAction.Models σ
      ((commSelection first second made₁ made₂).result label (commRule t u channel P Q) before).equations →
      psubst σ (label made₁) = psubst σ (uniformDot (pvars t ++ pvars u) bs P) ∧
        psubst σ (label made₂) = psubst σ (uniformDot (pvars t ++ pvars u) bs Q) := by
    intro σ solved
    have equation := solved (t, u) (by simp [Selection.result, comm_problem])
    change psubst σ t = psubst σ u at equation
    rw [out₁, out₂]
    exact ⟨firing_reads_uniform_dot principal equation P, firing_reads_uniform_dot principal equation Q⟩
  refine ⟨valid, .comm t u channel P Q bs principal convention, reads, ?_⟩
  intro bound σ solved
  obtain ⟨readP, readQ⟩ := reads σ solved
  rw [readP, readQ, uniformDot_eq_applyDot principal P foP
      (fun v occurs inPattern => bound v (List.mem_append_left _ occurs) inPattern),
    uniformDot_eq_applyDot principal Q foQ
      (fun v occurs inPattern => bound v (List.mem_append_right _ occurs) inPattern)]
  exact ⟨rfl, rfl⟩

/-! ## COMM at any path, modulo the bag laws -/

mutual
/-- The top-level parallel components: parallel bags are flattened at every
nesting and `0` is dropped. -/
def components : Pattern → List Pattern
  | .collection .hashBag elems none => componentsList elems
  | .apply "MZero" [] => []
  | p => [p]
def componentsList : List Pattern → List Pattern
  | [] => []
  | p :: ps => components p ++ componentsList ps
end

theorem components_par (p q : Pattern) : components (par p q) = components p ++ components q := by
  simp [par, pPar, components, componentsList]

theorem components_pZero : components pZero = [] := by simp [pZero, components]

/-- The bag laws do not change the components, up to order. -/
theorem components_par_comm (p q : Pattern) : (components (par p q)).Perm (components (par q p)) := by
  rw [components_par, components_par]; exact List.perm_append_comm

theorem components_par_assoc (p q r : Pattern) :
    components (par (par p q) r) = components (par p (par q r)) := by
  simp [components_par, List.append_assoc]

theorem components_par_zero (p : Pattern) : components (par p pZero) = components p := by
  simp [components_par, components_pZero]

theorem components_pFor (t x k : Pattern) : components (pFor t x k) = [pFor t x k] := by
  simp [pFor, components]

theorem mem_fire_labels {O : Type*} [DecidableEq O] (label : O → Pattern) (present : Finset O)
    (first second made₁ made₂ : O) (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ present) (present₂ : second ∈ present)
    (fresh₁ : made₁ ∉ present) (fresh₂ : made₂ ∉ present) :
    ((OccurrenceCommits.fire present
        ((commSelection first second made₁ made₂).commit (T := Pattern))).val.map label) =
      present.val.map label - {label first, label second} + {label made₁, label made₂} := by
  classical
  have takenSub : ({first, second} : Finset O) ⊆ present := by
    intro o member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  have disjoint : Disjoint (present \ {first, second}) ({made₁, made₂} : Finset O) := by
    rw [Finset.disjoint_left]
    intro o inLeft inRight
    simp only [Finset.mem_insert, Finset.mem_singleton] at inRight
    have inPresent := (Finset.mem_sdiff.mp inLeft).1
    rcases inRight with rfl | rfl
    · exact fresh₁ inPresent
    · exact fresh₂ inPresent
  have fireEq : OccurrenceCommits.fire present ((commSelection first second made₁ made₂).commit (T := Pattern)) =
      (present \ {first, second}) ∪ {made₁, made₂} := by
    simp [OccurrenceCommits.fire, Selection.commit, commSelection]
  rw [fireEq, ← Finset.disjUnion_eq_union _ _ disjoint, Finset.disjUnion_val, Multiset.map_add,
    Finset.sdiff_val]
  have pairVal : ({first, second} : Finset O).val = first ::ₘ {second} := by
    rw [Finset.insert_val, Multiset.ndinsert_of_notMem (by simpa using distinct)]; rfl
  have madeVal : ({made₁, made₂} : Finset O).val = made₁ ::ₘ {made₂} := by
    rw [Finset.insert_val, Multiset.ndinsert_of_notMem (by simpa using madeDistinct)]; rfl
  have le : ({first, second} : Finset O).val ≤ present.val := Finset.val_le_iff.mpr takenSub
  have split : present.val.map label =
      (present.val - ({first, second} : Finset O).val).map label +
        ({first, second} : Finset O).val.map label := by
    rw [← Multiset.map_add, Multiset.sub_add_cancel le]
  have removed : (present.val - ({first, second} : Finset O).val).map label =
      present.val.map label - {label first, label second} := by
    have pairMap : Multiset.map label (first ::ₘ {second}) = {label first, label second} := by simp
    rw [split, pairVal, pairMap, add_tsub_cancel_right]
  rw [removed, madeVal]
  rfl

/-- **COMM at any path, modulo the bag laws.** When the present occurrences
carry the components of a process, firing COMM on two of its input guards
leaves the components with those two guards replaced by the two dotted
continuations, wherever the guards sat in the process's parallel structure. -/
theorem comm_at_any_path {O : Type*} [DecidableEq O] (label : O → Pattern) (P : Pattern)
    (t u channel A B : Pattern) (before : Configuration Pattern O) (first second made₁ made₂ : O)
    (carries : before.present.val.map label = (components P : Multiset Pattern))
    (labelFirst : label first = pFor t channel A) (labelSecond : label second = pFor u channel B)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ before.present) (present₂ : second ∈ before.present)
    (fresh₁ : made₁ ∉ before.present) (fresh₂ : made₂ ∉ before.present)
    (out₁ : label made₁ = dotted (pvars t ++ pvars u) A)
    (out₂ : label made₂ = dotted (pvars t ++ pvars u) B) :
    ((commSelection first second made₁ made₂).result label (commRule t u channel A B) before).present.val.map label =
      (components P : Multiset Pattern) - {pFor t channel A, pFor u channel B} +
        {dotted (pvars t ++ pvars u) A, dotted (pvars t ++ pvars u) B} ∧
      pFor t channel A ∈ components P ∧ pFor u channel B ∈ components P := by
  have inComponents : ∀ o ∈ before.present, label o ∈ components P := by
    intro o member
    have : label o ∈ before.present.val.map label := Multiset.mem_map_of_mem label member
    rw [carries] at this
    exact Multiset.mem_coe.mp this
  refine ⟨?_, labelFirst ▸ inComponents first present₁, labelSecond ▸ inComponents second present₂⟩
  simp only [Selection.result]
  rw [mem_fire_labels label before.present first second made₁ made₂ distinct madeDistinct present₁ present₂
    fresh₁ fresh₂, carries, labelFirst, labelSecond, out₁, out₂]

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
